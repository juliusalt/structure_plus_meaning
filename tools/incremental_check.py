#!/usr/bin/env python3
"""Validate a changed workspace against an accepted proof base in one fixed directory.

Isabelle pairs every session source hash with its absolute path, so the accepted heap is current only
for the fixed base directory it was built in. A base is established rarely, by a complete check in
that directory. A check never rebuilds it: it refuses unless the base heap is the one recorded at
establishment, proves only changed theories and their dependents over that heap, executes every recipe
whose complete source manifest differs from its retained verification against exports of the proof
containing its roots, and keeps the retained verification of every recipe whose manifest is unchanged.
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

import check
import investigate
import prove_context
import proved_code
import reconstruction_sources
from evidence_io import write_json

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
POLY = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
ENV = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'USER_HOME': '/tmp/structural-isabelle'}


def theory_names(project):
    return re.findall(r'^    ([A-Za-z_][A-Za-z_0-9]*)\s*$', (project / 'ROOT').read_text(), re.M)


def session_declaration(project):
    """ROOT without its theory entries: session name, parent, options, sessions and directories."""
    return re.sub(r'^    [A-Za-z_][A-Za-z_0-9]*\s*\n', '', (project / 'ROOT').read_text(), flags=re.M)


def heap_identity(session):
    """The stored heap and build database of a session; a rebuild replaces both."""
    stored = sorted(Path(ENV['USER_HOME']).glob('.isabelle/*/heaps/*/' + session))
    databases = sorted(Path(ENV['USER_HOME']).glob('.isabelle/*/heaps/*/log/' + session + '.db'))
    assert len(stored) == 1 and len(databases) == 1, 'The accepted session heap is missing.'
    return {'heap': str(stored[0]), 'heap_sha256': investigate.file_hash(stored[0]),
            'database': str(databases[0]), 'database_sha256': investigate.file_hash(databases[0])}


def recipes():
    rows = []
    sys.path.insert(0, str(TOOLS))
    for script in sorted(TOOLS.glob('reconstruct_*.py')):
        recipe = getattr(importlib.import_module(script.stem), 'RECIPE', None)
        if recipe is not None:
            theory, filename = recipe.export.split(':')
            rows.append({'script': script.name, 'name': recipe.name, 'roots': list(recipe.roots),
                         'theory': theory, 'filename': filename})
    assert len({row['name'] for row in rows}) == len(rows)
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
    wanted = {'ROOT': ROOT / 'ROOT', 'tools/build.py': TOOLS / 'build.py', 'tools/check.py': TOOLS / 'check.py'}
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
            code = subprocess.run(command, cwd=ROOT, env=ENV, stdout=stream, stderr=subprocess.STDOUT,
                                  timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            code = 'timeout'
    return code, time.monotonic() - started


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
                      'tail': text.strip().splitlines()[-1:] }

    with ThreadPoolExecutor(max_workers=2) as pool:
        return dict(pool.map(run, suites.items()))


def validate(base, output, *, threads, jobs, selected, all_recipes, timeout):
    started = time.monotonic()
    base = base.resolve()
    output = output.resolve()
    assert not output.exists(), 'Use a fresh output directory.'
    output.mkdir(parents=True)
    summary = {'status': 'failed', 'base': str(base), 'phases': {}}
    phases = summary['phases']

    def phase(name, begin):
        phases[name] = round(time.monotonic() - begin, 2)

    try:
        begin = time.monotonic()
        session, base_sources, base_inputs = prove_context.accepted_parent(base)
        recorded = json.loads((base / 'base.json').read_text())
        assert recorded['session'] == session and recorded['stored'] == heap_identity(session), \
            'The accepted base heap changed since establishment; establish the base again.'
        assert session_declaration(ROOT) == session_declaration(base), \
            'The session declaration changed; a complete check is required.'
        structure = check.source_checks()
        summary['source_checks'] = structure
        assert not any(structure[k] for k in ('missing_theory_files', 'unlisted_theories', 'proof_escape_matches'))
        names = theory_names(ROOT)
        sources, parents = investigate.source_graph(ROOT, [], names)
        reused, rebuilt = proved_code.proved_context_partition(sources, parents, base_sources)
        summary.update(base_receipt_sha256=base_inputs[str(base / 'validation/build.json')],
                       theories=len(sources), reused_theories=len(reused), rebuilt_theories=sorted(rebuilt))
        phase('base_and_impact', begin)

        proof = None
        if rebuilt:
            begin = time.monotonic()
            proof = output / 'proof'
            code, _ = run_logged([sys.executable, '-B', str(TOOLS / 'prove_context.py'), '--parent-project', str(base),
                                  '--project', str(ROOT), '--output', str(proof),
                                  '--session', 'Incremental_' + uuid.uuid4().hex[:8], '--threads', str(threads),
                                  '--timeout', str(timeout), *sorted(rebuilt)], output / 'proof.log', 7200)
            phase('proof', begin)
            summary['proof'] = str(proof / 'result.json')
            assert code == 0, 'Incremental proof failed; see ' + str(proof / 'build.log')

        begin = time.monotonic()
        version = subprocess.run(['isabelle', 'version'], capture_output=True, text=True, check=True,
                                 env=ENV).stdout.strip()
        rows = [row for row in recipes() if not selected or row['name'] in selected]
        assert not selected or {row['name'] for row in rows} == set(selected), 'Unknown recipe name.'

        def impact(row):
            manifest = reconstruction_sources.collect(ROOT, TOOLS / row['script'], POLY, isabelle_version=version)
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
        groups = {'context': [r for r in affected if r['theory'] in rebuilt],
                  'base': [r for r in affected if r['theory'] not in rebuilt]}
        exports = {}

        def export(kind):
            members = groups[kind]
            if not members:
                return kind, 0
            directory = output / ('exports-' + kind)
            source = ['--proof', str(proof / 'result.json'), '--project', str(ROOT)] if kind == 'context' \
                else ['--main-project', str(base), '--project', str(ROOT)]
            modules = [item for r in members for item in ('--module', r['theory'] + ':' + r['filename'])]
            code, _ = run_logged([sys.executable, '-B', str(TOOLS / 'export_proved_code.py'), *source,
                                  '--output', str(directory), *modules], output / ('export-' + kind + '.log'), 1800)
            for r in members:
                exports[r['name']] = directory / r['filename'].replace('.ML', '.proof.json')
            return kind, code

        with ThreadPoolExecutor(max_workers=2) as pool:
            codes = dict(pool.map(export, groups))
        phase('export', begin)
        assert not any(codes.values()), 'Export failed: ' + json.dumps(codes)

        begin = time.monotonic()

        def expected_seconds(row):
            path = ROOT / 'validation/reconstruction' / (row['name'] + '-verified.json')
            if not path.is_file():
                return float('inf')
            return sum(step.get('seconds', 0) for step in json.loads(path.read_text()).get('steps', []))

        lock = threading.Lock()
        results = {}

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

        ordered = sorted(affected, key=expected_seconds, reverse=True)
        with ThreadPoolExecutor(max_workers=jobs + 1) as pool:
            tests = pool.submit(host_tests)
            list(pool.map(execute, ordered))
            summary['host_tests'] = tests.result()
        phase('recipes_and_host_tests', begin)
        summary['recipes'] = {row['name']: results.get(row['name'], {'status': 'unchanged'}) for row in rows}
        write_json(output / 'manifests.json', {row['name']: row['manifest'] for row in rows})
        failed = sorted(name for name, result in results.items() if result['status'] != 'accepted')
        summary['failed_recipes'] = failed
        assert not failed, 'Failed recipes: ' + ', '.join(failed)
        assert all(r['exit_code'] == 0 for r in summary['host_tests'].values()), 'Host tests failed.'
        stable = all(investigate.file_hash(Path(p)) == sha for p, sha in base_inputs.items())
        assert stable and investigate.current_sources(sources), 'Base or workspace sources changed during the check.'
        summary['status'] = 'accepted'
    except Exception as error:
        summary['error'] = f'{type(error).__name__}: {error}'
    if proof is not None and (proof / 'result.json').is_file():
        # Exports and receipts are retained as files; the child heap and database are not reused.
        child = json.loads((proof / 'result.json').read_text())['command'][-1]
        for stored in Path(ENV['USER_HOME']).glob('.isabelle/*/heaps/*/' + child) :
            stored.unlink()
        for stored in Path(ENV['USER_HOME']).glob('.isabelle/*/heaps/*/log/' + child + '.*'):
            stored.unlink()
    summary['seconds'] = round(time.monotonic() - started, 2)
    write_json(output / 'incremental.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k not in ('rebuilt_theories', 'recipes', 'source_checks')}))
    return 0 if summary['status'] == 'accepted' else 1


def retain(output, host_tests):
    """Record an accepted check: executed recipes receive their current manifests and receipts."""
    output = output.resolve()
    summary = json.loads((output / 'incremental.json').read_text())
    assert summary['status'] == 'accepted'
    manifests = json.loads((output / 'manifests.json').read_text())
    target = ROOT / 'validation/reconstruction'
    base = Path(summary['base'])
    proof = summary.get('proof')
    entries = []
    for name, result in sorted(summary['recipes'].items()):
        sources_path = target / (name + '-sources.json')
        verified_path = target / (name + '-verified.json')
        if result['status'] == 'unchanged':
            assert json.loads(sources_path.read_text()) == manifests[name]
            previous = json.loads(verified_path.read_text())
            records = sum(b['records'] for b in previous['report_boundaries'].values())
        else:
            assert result['status'] == 'accepted'
            receipt = json.loads(Path(result['receipt']).read_text())
            assert receipt['status'] == 'accepted' and receipt['reports_equal'] is True
            write_json(sources_path, manifests[name])
            records = sum(b['records'] for b in receipt['report_boundaries'].values())
            receipt.update(
                complete_recipe_source_manifest=sources_path.name,
                source_manifest_sha256=investigate.file_hash(sources_path),
                complete_review={'status': 'accepted', 'records': records, 'reports_equal': True,
                                 'base_receipt_sha256': summary['base_receipt_sha256'],
                                 'proof_receipt_sha256': investigate.file_hash(Path(proof)) if proof else None,
                                 'seconds': result['seconds']},
                retention='The accepted base proof and the incremental proof of every changed theory and '
                          'dependent supplied the exported module; every complete report boundary equals its '
                          'retained original. Generated result bulk is not a repository input.')
            write_json(verified_path, receipt)
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
                        'validation': 'unchanged complete manifest; retained verification applies'
                                      if result['status'] == 'unchanged' else
                                      'executed against the accepted base and incremental proof'})
    base_check = json.loads((base / 'validation/check.json').read_text())
    write_json(ROOT / 'validation/reconstruction/current-verified.json', {
        'status': 'accepted', 'host_tests': host_tests,
        'base_theories': base_check['theory_count'], 'workspace_theories': summary['theories'],
        'incremental_proof_theories': len(summary['rebuilt_theories']),
        'base_receipt_sha256': summary['base_receipt_sha256'],
        'source_only_reconstructions': entries, 'complete_native_reports': sum(e['reports'] for e in entries),
        'executed_recipes': sum(r['status'] == 'accepted' for r in summary['recipes'].values()),
        'unchanged_recipes': sum(r['status'] == 'unchanged' for r in summary['recipes'].values()),
        'phase_seconds': summary['phases'], 'total_seconds': summary['seconds']})
    write_json(ROOT / 'validation/incremental-check.json', {
        key: summary[key] for key in ('status', 'base_receipt_sha256', 'theories', 'reused_theories',
                                      'rebuilt_theories', 'phases', 'seconds', 'source_checks', 'host_tests')}
        | {'recipes': {n: {k: v for k, v in r.items() if k != 'receipt'} for n, r in summary['recipes'].items()}})
    print(json.dumps({'retained': len(entries), 'reports': sum(e['reports'] for e in entries)}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    base = commands.add_parser('establish', help='Accept the current sources in the fixed base directory.')
    base.add_argument('--base', type=Path, default=Path('/tmp/structural-accepted'))
    base.add_argument('--threads', type=int, default=16)
    base.add_argument('--timeout', type=int, default=1200)
    run = commands.add_parser('check', help='Validate the workspace against the current accepted base.')
    run.add_argument('--base', type=Path, default=Path('/tmp/structural-accepted'))
    run.add_argument('--output', type=Path, required=True)
    run.add_argument('--threads', type=int, default=16)
    run.add_argument('--jobs', type=int, default=8)
    run.add_argument('--timeout', type=int, default=1200)
    run.add_argument('--recipe', action='append', default=[])
    run.add_argument('--all-recipes', action='store_true')
    keep = commands.add_parser('retain', help='Record the evidence of an accepted check.')
    keep.add_argument('--output', type=Path, required=True)
    keep.add_argument('--host-tests', type=json.loads, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Incremental validation requires Python assertions.')
    if args.command == 'retain':
        return retain(args.output, args.host_tests)
    if args.command == 'establish':
        args.base.mkdir(parents=True, exist_ok=True)
        return establish(args.base.resolve(), args.threads, args.timeout)
    return validate(args.base, args.output, threads=args.threads, jobs=args.jobs, selected=args.recipe,
                    all_recipes=args.all_recipes, timeout=args.timeout)


if __name__ == '__main__':
    raise SystemExit(main())
