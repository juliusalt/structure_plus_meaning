#!/usr/bin/env python3
"""Validate a workspace using exact accepted proof contexts at their original paths.

Rebuild only theories changed since the accepted base and their dependents, export each module from its
actual provider, and execute every recipe whose complete execution boundary changed. A check stores no heap:
its rebuilt theories supply exports, not import contexts, so the base stays the one selected context. Only a
check that advances the base stores a heap and becomes the next base. Unchanged recipe manifests retain their
accepted verification.
A changed manifest whose exported module, subject contracts, execution tools, fixtures, expected
reports and native runtime all equal an accepted execution's boundary reuses that execution.
The original fixed base is used only when no newer context has been selected. Neither reuse nor
adoption rebuilds a parent heap, and a partial recipe check cannot replace the complete inventory.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import importlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
import uuid

import build
import check
import execution_support as investigate
import isabelle_places
import native_execution_runtime
import prove_context
import proof_contexts
import proved_code
import reconstruction_sources
from evidence_io import write_json

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
POLY = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
ENV = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'USER_HOME': str(isabelle_places.USER_HOME)}
# Every Isabelle/Poly/ML runtime file read by native executions, beyond the toolchain digests.
NATIVE_RUNTIME = (*native_execution_runtime.inputs(), Path('/opt/isabelle/src/Pure/ML/ml_statistics.ML'))


def theory_names(project):
    return re.findall(r'^    ([A-Za-z_][A-Za-z_0-9]*)\s*$', (project / 'ROOT').read_text(), re.M)


def session_declaration(project):
    """ROOT without its theory entries: session name, parent, options, sessions and directories."""
    return proof_contexts.session_declaration(project)


# A refusal made before anything is built names, in the text a session reads, what it found and where.
def stale_output_refusal(output) -> str:
    return 'Use a fresh output directory: ' + str(output) + ' already exists.'


def source_check_refusal(structure) -> str:
    return '\n  '.join(('The sources refuse this check:', *structure['refusals']))


def declaration_refusal(base, project, stored) -> str:
    return ('The project session declaration changed; a complete check is required.\n'
            '  ROOT now declares: ' + json.dumps(project) + '\n'
            '  the base ' + str(base) + ' was built with: ' + json.dumps(stored))


def stored_heap_refusal(base) -> str:
    return 'The base must store the heap that supplies its import contexts; ' + str(base) + ' stores none.'


def active_context_refusal(path, directory, receipt) -> str:
    return ('The active context ' + str(path) + ' selects ' + str(directory) + ', whose receipt '
            + str(receipt) + ' no longer has the digest recorded there.')


def repeated_recipe_refusal(names) -> str:
    repeated = sorted({name for name in names if names.count(name) > 1})
    return 'Two reconstruction scripts declare one recipe name: ' + ', '.join(repeated) + '.'


def unknown_recipe_refusal(selected, known) -> str:
    return ('Unknown recipe name: ' + ', '.join(sorted(set(selected) - set(known)))
            + '; this project declares ' + ', '.join(sorted(known)) + '.')


ACTIVE_CONTEXT = isabelle_places.ACTIVE_CONTEXT


def heap_identity(session):
    return proof_contexts.heap_identity(session)


def activate_context(directory, lineage=None):
    context = proof_contexts.load_parent(directory, None, *(lineage or proof_contexts.new_lineage()))
    assert context['project_declaration'] == session_declaration(ROOT), \
        declaration_refusal(directory, session_declaration(ROOT), context['project_declaration'])
    assert context['stored_heap'], stored_heap_refusal(directory)
    ACTIVE_CONTEXT.parent.mkdir(parents=True, exist_ok=True)
    temporary = ACTIVE_CONTEXT.with_suffix('.new.json')
    write_json(temporary, {'directory': str(Path(directory).resolve()),
                           'receipt_sha256': investigate.file_hash(Path(context['receipt']))})
    temporary.replace(ACTIVE_CONTEXT)
    return context


def selected_base(explicit, lineage=None):
    if explicit is not None:
        return explicit
    if ACTIVE_CONTEXT.is_file():
        selected = json.loads(ACTIVE_CONTEXT.read_text())
        context = proof_contexts.load_parent(selected['directory'], None, *(lineage or proof_contexts.new_lineage()))
        assert investigate.file_hash(Path(context['receipt'])) == selected['receipt_sha256'], \
            active_context_refusal(ACTIVE_CONTEXT, selected['directory'], context['receipt'])
        return Path(selected['directory'])
    return isabelle_places.FALLBACK_BASE


def recipes():
    rows = []
    sys.path.insert(0, str(TOOLS))
    for script in sorted(TOOLS.glob('reconstruct_*.py')):
        recipe = getattr(importlib.import_module(script.stem), 'RECIPE', None)
        if recipe is not None:
            theory, filename = recipe.export.split(':')
            rows.append({'script': script.name, 'name': recipe.name, 'roots': list(recipe.roots),
                         'theory': theory, 'filename': filename})
    assert len({row['name'] for row in rows}) == len(rows), \
        repeated_recipe_refusal([row['name'] for row in rows])
    return rows


def establish(base, threads, timeout):
    """Accept the current sources in the fixed base directory by a complete check run there.

    Isabelle's session digest pairs every source hash with its absolute path, so an accepted heap is
    current only for sources at the path where they were built. The base therefore keeps one fixed
    path; only changed files are replaced, and the complete check runs only when a base is established.
    """
    names = theory_names(ROOT)
    for directory in ('theories', 'tools', 'validation'):
        (base / directory).mkdir(parents=True, exist_ok=True)
    wanted = {'ROOT': ROOT / 'ROOT', 'tools/build.py': TOOLS / 'build.py', 'tools/check.py': TOOLS / 'check.py',
              'tools/isabelle_places.py': TOOLS / 'isabelle_places.py'}
    wanted |= {'theories/' + name + '.thy': ROOT / 'theories' / (name + '.thy') for name in names}
    for stale in (base / 'theories').glob('*.thy'):
        if 'theories/' + stale.name not in wanted:
            stale.unlink()
    for relative, source in wanted.items():
        target = base / relative
        if not target.is_file() or investigate.file_hash(target) != investigate.file_hash(source):
            shutil.copy2(source, target)
    started = time.monotonic()
    completed = subprocess.run([sys.executable, '-B', str(base / 'tools/check.py'), '--isabelle', 'isabelle',
                                '--threads', str(threads), '--timeout', str(timeout)],
                               cwd=base, env=ENV, capture_output=True, text=True)
    seconds = time.monotonic() - started
    session, sources, _ = prove_context.accepted_parent(base)
    assert completed.returncode == 0
    workspace = {name: investigate.file_hash(ROOT / 'theories' / (name + '.thy')) for name in names}
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    write_json(base / 'base.json', {'session': session, 'theories': len(sources), 'check_seconds': seconds,
        'stored': heap_identity(session),
        'workspace_head': head, 'snapshot_equals_workspace_sources': workspace == sources,
        'boundary': 'The complete check ran in this fixed directory; its receipts bind these exact sources.'})
    print(json.dumps({'base': str(base), 'session': session, 'theories': len(sources),
                      'check_seconds': round(seconds, 1)}))
    return 0


def run_logged(command, log, timeout):
    started = time.monotonic()
    with log.open('w') as stream:
        try:
            code = build.run_session(command, cwd=ROOT, env=ENV, stdout=stream, stderr=subprocess.STDOUT,
                                     timeout=timeout)
        except subprocess.TimeoutExpired:
            code = 'timeout'
    return code, time.monotonic() - started


def failing_tests(text, lines=8):
    """Every test unittest's report names as failing or erroring, with the last lines of its traceback.

The report prints each failure as a block: a line of '=', the outcome and the test's id, a line of
'-', then the traceback up to the next such separator line. Colour escapes, which unittest writes
when the environment forces colour, are removed first."""
    report = re.sub(r'\x1b\[[0-9;]*m', '', text).splitlines()
    rule = lambda line, mark: len(line) >= 20 and set(line) == {mark}
    found = []
    for index, line in enumerate(report):
        heading = re.match(r'(ERROR|FAIL): (.*)$', line)
        if not heading or index == 0 or not rule(report[index - 1], '='):
            continue
        body = []
        for following in report[index + 2:]:
            if rule(following, '=') or rule(following, '-'):
                break
            body.append(following)
        while body and not body[-1].strip():
            body.pop()
        found.append({'outcome': heading.group(1), 'test': heading.group(2), 'traceback': body[-lines:]})
    return found


def host_tests():
    """Run the tool and kernel test suites; return their counts from unittest's own summary."""
    suites = {'tools': (ROOT / 'tools', 'test_*.py'),
              'kernel': (ROOT / 'source-material/RRA/RRA_Kernel_Definition_1.0.0', 'test_*.py')}

    def run(item):
        name, (directory, pattern) = item
        start = 'tests' if name == 'kernel' else '.'
        completed = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', start, '-p', pattern],
                                   cwd=directory, env=ENV, capture_output=True, text=True, timeout=1800)
        text = completed.stderr + completed.stdout
        ran = re.search(r'^Ran (\d+) tests?', text, re.M)
        skipped = re.search(r'skipped=(\d+)', text)
        return name, {'exit_code': completed.returncode, 'ran': int(ran.group(1)) if ran else None,
                      'skipped': int(skipped.group(1)) if skipped else 0,
                      'tail': text.strip().splitlines()[-1:], 'failing': failing_tests(text)}

    with ThreadPoolExecutor(max_workers=2) as pool:
        return dict(pool.map(run, suites.items()))


def execution_boundary(row, manifest, proof_path):
    """Every input a recipe's executions read, with theory sources present only through their export.

    The accepted proof context establishes that the exported module and subject contracts belong to
    the current sources. An execution reads that export, its own Python closure, declared fixtures,
    the expected report boundaries and the native runtime; equal boundaries determine equal reports.
    """
    proof = json.loads(Path(proof_path).read_text())
    (export,) = proof['exports']
    script = TOOLS / row['script']
    name, _, fixtures, jobs = reconstruction_sources.recipe_inputs(script)
    assert name == row['name']
    closure = reconstruction_sources.local_python_closure(TOOLS, [script, *(TOOLS / job for job in jobs)])
    tools = {str(path.relative_to(ROOT)): sha for path, sha in sorted(closure.items())}
    files = manifest['files']
    assert all(files.get(path) == sha for path, sha in tools.items()), 'Execution tools differ from the manifest.'
    declared = (*fixtures, 'validation/reconstruction/' + name + '-reports.json')
    assert investigate.file_hash(Path(export['path'])) == export['sha256']
    return {'export': {'theory': proof['export_theory'], 'module_sha256': export['sha256'],
                       'subject_contracts': dict(sorted((Path(c['path']).name, c['sha256'])
                                                        for c in proof['subject_contracts'])),
                       'code_target': proof['code_target'],
                       'complete_artifact_transport': proof['complete_artifact_transport'],
                       'complete_term_transport': proof['complete_term_transport']},
            'tools': tools, 'declared_inputs': {path: files[path] for path in declared},
            'toolchain': manifest['toolchain'],
            'runtime': {str(path): investigate.file_hash(path) for path in NATIVE_RUNTIME}}


def reusable_execution(verified, boundary):
    """An accepted execution applies to every check whose complete execution boundary is equal."""
    # An exported module is byte-identical from any session over identical sources (task 134: 52 groups of
    # distinct sessions over one closure), so a receipt goes stale only when a code equation in its recipe's
    # closure changes, and reuse fires after a base move or a retention.
    return (verified.get('status') == 'accepted' and verified.get('reports_equal') is True
            and verified.get('execution_boundary') == boundary)


def verify_manifest_inputs(manifests):
    """Check each distinct input once, including tools and fixtures of unchanged recipes."""
    files = {}
    for manifest in manifests.values():
        for name, sha in manifest['files'].items():
            path = (ROOT / name).resolve()
            assert path.is_relative_to(ROOT) and path.is_file(), 'Missing recipe input: ' + name
            assert name not in files or files[name] == sha, 'Conflicting input versions: ' + name
            files[name] = sha
    assert all(investigate.file_hash(ROOT / name) == sha for name, sha in files.items()), \
        'Recipe inputs changed after validation.'


def validate(base, output, *, threads, jobs, selected, all_recipes, timeout, lineage=None, advance_base=False):
    started = time.monotonic()
    # One verified lineage (contexts and input digests) serves the base, adoption and activation.
    lineage = lineage or proof_contexts.new_lineage()
    base = base.resolve()
    output = output.resolve()
    assert not output.exists(), stale_output_refusal(output)
    output.mkdir(parents=True)
    summary = {'status': 'failed', 'base': str(base), 'phases': {}}
    phases = summary['phases']

    def phase(name, begin):
        phases[name] = round(time.monotonic() - begin, 2)

    proof = None
    try:
        summary['validation_inputs'] = {str(path.relative_to(ROOT)): investigate.file_hash(path)
            for path in (ROOT / 'ROOT', Path(__file__).resolve(), Path(check.__file__).resolve())}
        begin = time.monotonic()
        parent = proof_contexts.load_parent(base, None, *lineage)
        session, base_sources, base_inputs = parent['session'], parent['sources'], parent['inputs']
        assert session_declaration(ROOT) == parent['project_declaration'], \
            declaration_refusal(base, session_declaration(ROOT), parent['project_declaration'])
        assert parent['stored_heap'], stored_heap_refusal(base)
        summary['advance_base'] = advance_base
        structure = check.source_checks()
        summary['source_checks'] = structure
        if structure['refusals']:
            summary['source_check_refusals'] = structure['refusals']
        assert not structure['refusals'], source_check_refusal(structure)
        names = theory_names(ROOT)
        sources, parents = investigate.source_graph(ROOT, [], names)
        reused, rebuilt = proved_code.proved_context_partition(sources, parents, base_sources)
        summary.update(base_receipt_sha256=base_inputs[parent['receipt']],
                       base_theories=len(base_sources), base_context_receipt=parent['receipt'],
                       theories=len(sources), reused_theories=len(reused), rebuilt_theories=sorted(rebuilt))
        phase('base_and_impact', begin)

        proof = None
        if rebuilt:
            begin = time.monotonic()
            proof = output / 'proof'
            code, _ = run_logged([sys.executable, '-B', str(TOOLS / 'prove_context.py'), '--parent-project', str(base),
                                  '--project', str(ROOT), '--output', str(proof),
                                  '--session', 'Incremental_' + uuid.uuid4().hex[:8], '--threads', str(threads),
                                  '--timeout', str(timeout), *([] if advance_base else ['--without-heap']),
                                  *sorted(rebuilt)], output / 'proof.log', 7200)
            phase('proof', begin)
            summary['proof'] = str(proof / 'result.json')
            assert code == 0, 'Incremental proof failed; see ' + str(proof / 'build.log')
            proof_contexts.adopt_proof_context(proof, ROOT, *lineage)
        export_context = proof if proof is not None else base
        summary['accepted_proof_context'] = str(export_context)

        begin = time.monotonic()
        version = subprocess.run(['isabelle', 'version'], capture_output=True, text=True, check=True,
                                 env=ENV).stdout.strip()
        declared = recipes()
        rows = [row for row in declared if not selected or row['name'] in selected]
        assert not selected or {row['name'] for row in rows} == set(selected), \
            unknown_recipe_refusal(selected, [row['name'] for row in declared])

        modules = {}

        def impact(row):
            manifest = reconstruction_sources.collect(ROOT, TOOLS / row['script'], POLY, isabelle_version=version,
                                                      graph=(sources, parents), modules=modules)
            retained = ROOT / 'validation/reconstruction' / (row['name'] + '-sources.json')
            verified = ROOT / 'validation/reconstruction' / (row['name'] + '-verified.json')
            unchanged = (retained.is_file() and verified.is_file()
                         and json.loads(retained.read_text()) == manifest
                         and json.loads(verified.read_text()).get('status') == 'accepted')
            return row | {'manifest': manifest, 'affected': all_recipes or not unchanged}

        with ThreadPoolExecutor(max_workers=16) as pool:
            rows = list(pool.map(impact, rows))
        affected = [row for row in rows if row['affected']]
        phase('recipe_impact', begin)

        begin = time.monotonic()
        exports = {}
        if affected:
            directory = output / 'exports-context'
            modules = [item for row in affected for item in ('--module', row['theory'] + ':' + row['filename'])]
            code, _ = run_logged([sys.executable, '-B', str(TOOLS / 'export_proved_code.py'),
                '--context', str(export_context), '--project', str(ROOT), '--output', str(directory),
                '--module-roots', json.dumps({row['theory']: row['roots'] for row in affected}),
                *modules], output / 'export-context.log', 1800)
            assert code == 0, 'Export failed; see export-context.log.'
            exports = {r['name']: directory / r['filename'].replace('.ML', '.proof.json') for r in affected}
        phase('export', begin)

        begin = time.monotonic()
        boundaries = {row['name']: execution_boundary(row, row['manifest'], exports[row['name']]) for row in affected}
        write_json(output / 'boundaries.json', boundaries)
        results = {}
        for row in affected:
            verified = ROOT / 'validation/reconstruction' / (row['name'] + '-verified.json')
            previous = json.loads(verified.read_text()) if verified.is_file() else {}
            if not all_recipes and reusable_execution(previous, boundaries[row['name']]):
                results[row['name']] = {'status': 'reused', 'exit_code': 0, 'seconds': 0.0, 'receipt': str(verified)}
        executed = [row for row in affected if row['name'] not in results]
        phase('execution_impact', begin)

        begin = time.monotonic()

        def expected_seconds(row):
            path = ROOT / 'validation/reconstruction' / (row['name'] + '-verified.json')
            if not path.is_file():
                return float('inf')
            return sum(step.get('seconds', 0) for step in json.loads(path.read_text()).get('steps', []))

        lock = threading.Lock()

        def execute(row):
            directory = output / 'recipes' / row['name']
            directory.parent.mkdir(parents=True, exist_ok=True)
            code, seconds = run_logged([sys.executable, '-B', str(TOOLS / row['script']), '--proof',
                                        str(exports[row['name']]), '--poly', str(POLY), '--output', str(directory)],
                                       output / 'recipes' / (row['name'] + '.log'), 14400)
            receipt = directory / 'reconstruction.json'
            status = json.loads(receipt.read_text()) if receipt.is_file() else {}
            accepted = code == 0 and status.get('status') == 'accepted' and status.get('reports_equal') is True
            with lock:
                results[row['name']] = {'status': 'accepted' if accepted else 'failed', 'exit_code': code,
                                        'seconds': round(seconds, 2), 'receipt': str(receipt)}
                print(json.dumps({'recipe': row['name'], **results[row['name']]}), flush=True)

        ordered = sorted(executed, key=expected_seconds, reverse=True)
        with ThreadPoolExecutor(max_workers=1) as test_pool, ThreadPoolExecutor(max_workers=jobs) as pool:
            tests = test_pool.submit(host_tests)
            list(pool.map(execute, ordered))
            summary['host_tests'] = tests.result()
        phase('recipes_and_host_tests', begin)
        summary['recipes'] = {row['name']: results.get(row['name'], {'status': 'unchanged'}) for row in rows}
        write_json(output / 'manifests.json', {row['name']: row['manifest'] for row in rows})
        failed = sorted(name for name, result in results.items() if result['status'] not in ('accepted', 'reused'))
        summary['failed_recipes'] = failed
        assert not failed, 'Failed recipes: ' + ', '.join(failed)
        assert all(r['exit_code'] == 0 for r in summary['host_tests'].values()), 'Host tests failed.'
        stable = all(investigate.file_hash(Path(p)) == sha for p, sha in base_inputs.items())
        assert stable and investigate.current_sources(sources), 'Base or workspace sources changed during the check.'
        verify_manifest_inputs({row['name']: row['manifest'] for row in rows}
                               | {'validation': {'files': summary['validation_inputs']}})
        assert all(investigate.file_hash(Path(p)) == sha for boundary in boundaries.values()
                   for p, sha in boundary['runtime'].items()), 'Native runtime changed during the check.'
        summary['status'] = 'accepted'
    except Exception as error:
        summary['error'] = f'{type(error).__name__}: {error}'
    if summary['status'] == 'accepted' and not selected and (proof is None or advance_base):
        activate_context(export_context, lineage)
        summary['active_context'] = str(export_context)
    elif summary['status'] == 'accepted' and not selected:
        # The checked context exports without supplying import contexts; the base remains selected.
        summary['active_context'] = str(base)
    elif proof is not None:
        # Failed/partial checks do not advance the complete-workspace checkpoint.
        # Their accepted proof artifacts remain available for explicit reuse/review.
        summary['active_context'] = None
    summary['seconds'] = round(time.monotonic() - started, 2)
    write_json(output / 'incremental.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k not in ('rebuilt_theories', 'recipes', 'source_checks')}))
    return 0 if summary['status'] == 'accepted' else 1


def retain(output, host_tests=None):
    """Record an accepted check: executed recipes receive their current manifests and receipts."""
    output = output.resolve()
    summary = json.loads((output / 'incremental.json').read_text())
    assert summary['status'] == 'accepted'
    assert set(summary['recipes']) == {row['name'] for row in recipes()}, \
        'A partial recipe check cannot replace the complete inventory.'
    actual_tests = {name: {key: result[key] for key in ('ran', 'skipped')}
                    for name, result in summary['host_tests'].items()}
    assert all(result['exit_code'] == 0 and result['ran'] is not None
               for result in summary['host_tests'].values()), 'Host tests did not pass.'
    assert host_tests is None or host_tests == actual_tests, 'Supplied test counts differ from the actual run.'
    host_tests = actual_tests
    manifests = json.loads((output / 'manifests.json').read_text())
    assert set(manifests) == set(summary['recipes'])
    verify_manifest_inputs(manifests | {'validation': {'files': summary.get('validation_inputs', {})}})
    boundaries_path = output / 'boundaries.json'
    boundaries = json.loads(boundaries_path.read_text()) if boundaries_path.is_file() else {}
    assert {n for n, r in summary['recipes'].items() if r['status'] != 'unchanged'} <= boundaries.keys()
    assert all(investigate.file_hash(Path(p)) == sha for boundary in boundaries.values()
               for p, sha in boundary['runtime'].items()), 'Native runtime changed after validation.'
    target = ROOT / 'validation/reconstruction'
    base = Path(summary['base'])
    proof = summary.get('proof')
    context_receipt = Path(summary['accepted_proof_context']) / proof_contexts.CONTEXT_FILE
    entries = []
    for name, result in sorted(summary['recipes'].items()):
        sources_path = target / (name + '-sources.json')
        verified_path = target / (name + '-verified.json')
        if result['status'] == 'unchanged':
            assert json.loads(sources_path.read_text()) == manifests[name]
            previous = json.loads(verified_path.read_text())
            records = sum(b['records'] for b in previous['report_boundaries'].values())
        elif result['status'] == 'reused':
            previous = json.loads(verified_path.read_text())
            assert reusable_execution(previous, boundaries[name]), 'The retained execution no longer applies.'
            write_json(sources_path, manifests[name])
            records = sum(b['records'] for b in previous['report_boundaries'].values())
            previous.update(
                complete_recipe_source_manifest=sources_path.name,
                source_manifest_sha256=investigate.file_hash(sources_path),
                execution_reuse={'base_receipt_sha256': summary['base_receipt_sha256'],
                                 'proof_receipt_sha256': investigate.file_hash(Path(proof)) if proof else None,
                                 'proof_context_receipt_sha256': investigate.file_hash(context_receipt),
                                 'export_module_sha256': boundaries[name]['export']['module_sha256'],
                                 'boundary': 'The current accepted proof context exported an identical module and '
                                             'subject contracts; execution tools, fixtures, expected reports and '
                                             'native runtime are unchanged. The accepted execution determines '
                                             'these complete report boundaries without being repeated.'})
            write_json(verified_path, previous)
        else:
            assert result['status'] == 'accepted'
            receipt = json.loads(Path(result['receipt']).read_text())
            assert receipt['status'] == 'accepted' and receipt['reports_equal'] is True
            write_json(sources_path, manifests[name])
            records = sum(b['records'] for b in receipt['report_boundaries'].values())
            receipt.update(
                complete_recipe_source_manifest=sources_path.name,
                source_manifest_sha256=investigate.file_hash(sources_path),
                execution_boundary=boundaries[name],
                complete_review={'status': 'accepted', 'records': records, 'reports_equal': True,
                                 'base_receipt_sha256': summary['base_receipt_sha256'],
                                 'proof_receipt_sha256': investigate.file_hash(Path(proof)) if proof else None,
                                 'seconds': result['seconds']},
                retention='The accepted base proof and the incremental proof of every changed theory and '
                          'dependent supplied the exported module; every complete report boundary equals its '
                          'retained original. Generated result bulk is not a repository input.')
            write_json(verified_path, receipt)
        if result['status'] != 'unchanged':
            write_json(target / (name + '-materialization.json'), {
                'recipe_source_manifest': sources_path.name,
                'recipe_source_manifest_sha256': investigate.file_hash(sources_path),
                'recipe_files': len(manifests[name]['files']),
                'boundary': 'Validated against an accepted proof base and an incremental proof of its changed '
                            'theories; no separate source-only copy was materialized.'})
        files = manifests[name]['files']
        entries.append({'recipe': name, 'reports': records, 'source_files': len(files),
                        'theories': sum(f.endswith('.thy') for f in files),
                        'python_modules': sum(f.endswith('.py') for f in files),
                        'source_manifest_sha256': investigate.file_hash(sources_path),
                        'verification_sha256': investigate.file_hash(verified_path),
                        'validation': {'unchanged': 'unchanged complete manifest; retained verification applies',
                                       'reused': 'unchanged complete execution boundary; the accepted execution '
                                                 'applies to the current proof',
                                       'accepted': 'executed against the accepted base and incremental proof'}
                                      [result['status']]})
    base_theories = summary.get('base_theories')
    if base_theories is None:
        base_theories = len(proof_contexts.load_parent(base)['sources'])
    write_json(ROOT / 'validation/reconstruction/current-verified.json', {
        'status': 'accepted', 'host_tests': host_tests,
        'base_theories': base_theories, 'workspace_theories': summary['theories'],
        'incremental_proof_theories': len(summary['rebuilt_theories']),
        'base_receipt_sha256': summary['base_receipt_sha256'],
        'source_only_reconstructions': entries, 'complete_native_reports': sum(e['reports'] for e in entries),
        'executed_recipes': sum(r['status'] == 'accepted' for r in summary['recipes'].values()),
        'reused_recipes': sum(r['status'] == 'reused' for r in summary['recipes'].values()),
        'unchanged_recipes': sum(r['status'] == 'unchanged' for r in summary['recipes'].values()),
        'phase_seconds': summary['phases'], 'total_seconds': summary['seconds']})
    write_json(ROOT / 'validation/incremental-check.json', {
        key: summary[key] for key in ('status', 'base_receipt_sha256', 'theories', 'reused_theories',
                                      'rebuilt_theories', 'phases', 'seconds', 'source_checks', 'host_tests')}
        | {'validation_inputs': summary.get('validation_inputs', {}),
           'recipes': {n: {k: v for k, v in r.items() if k != 'receipt'} for n, r in summary['recipes'].items()}})
    print(json.dumps({'retained': len(entries), 'reports': sum(e['reports'] for e in entries)}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    base = commands.add_parser('establish', help='Accept the current sources in the fixed base directory.')
    base.add_argument('--base', type=Path, default=isabelle_places.FALLBACK_BASE)
    base.add_argument('--threads', type=int, default=16)
    base.add_argument('--timeout', type=int, default=1200)
    run = commands.add_parser('check', help='Validate the workspace against the current accepted base.')
    run.add_argument('--base', type=Path, help='Override the active accepted context.')
    run.add_argument('--output', type=Path, required=True)
    run.add_argument('--threads', type=int, default=16)
    run.add_argument('--jobs', type=int, default=8)
    run.add_argument('--timeout', type=int, default=1200)
    run.add_argument('--recipe', action='append', default=[])
    run.add_argument('--all-recipes', action='store_true')
    run.add_argument('--advance-base', action='store_true',
                     help='Store the heap of the rebuilt theories and select this check as the next base.')
    adopt = commands.add_parser('adopt', help='Reuse a successful immutable proof context without rebuilding it.')
    adopt.add_argument('--proof', type=Path, required=True)
    adopt.add_argument('--source-project', type=Path, default=ROOT)
    keep = commands.add_parser('retain', help='Record the evidence of an accepted check.')
    keep.add_argument('--output', type=Path, required=True)
    keep.add_argument('--host-tests', type=json.loads, help='Optional cross-check of recorded test counts.')
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Incremental validation requires Python assertions.')
    if args.command == 'adopt':
        directory = args.proof.resolve()
        if not (directory / proof_contexts.CONTEXT_FILE).is_file():
            proof_contexts.adopt_proof_context(directory, args.source_project)
        context = activate_context(directory)
        print(json.dumps({'active_context': str(directory), 'theories': len(context['sources'])}))
        return 0
    if args.command == 'retain':
        return retain(args.output, args.host_tests)
    if args.command == 'establish':
        args.base.mkdir(parents=True, exist_ok=True)
        return establish(args.base.resolve(), args.threads, args.timeout)
    lineage = proof_contexts.new_lineage()
    return validate(selected_base(args.base, lineage), args.output, threads=args.threads, jobs=args.jobs,
                    selected=args.recipe, all_recipes=args.all_recipes, timeout=args.timeout, lineage=lineage,
                    advance_base=args.advance_base)


if __name__ == '__main__':
    raise SystemExit(main())
