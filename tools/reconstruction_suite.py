"""Reconstruct related recipes through one fresh proof of their combined source dependencies."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import argparse
import json
import os
import runpy
import subprocess
import sys
import time
import traceback
import uuid

from build import run_session
import isabelle_places
from evidence_io import digest, write_json
from machine_reports import unique_object
from materialize_source_boundary import materialize
from proved_code import accepted_proof
from reconstruction import finish_reconstruction
from reconstruction_sources import collect, local_python_closure, recipe_inputs


def main(argv=None):
    if not __debug__:
        raise ValueError("Reconstruction checks require Python assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--poly', type=Path, required=True)
    parser.add_argument('--recipe', action='append', help='Recipe filename in tools; defaults to every reconstruct_*.py.')
    parser.add_argument('--session', default='Reconstruct_Related_Recipes')
    parser.add_argument('--threads', type=int, default=12)
    parser.add_argument('--timeout', type=int, default=1800)
    parser.add_argument('--workers', type=int, default=3)
    args = parser.parse_args(argv)
    assert min(args.threads, args.timeout, args.workers) > 0
    project, output, poly = (p.resolve() for p in (args.project, args.output, args.poly))
    assert not output.exists(), 'Use a fresh reconstruction directory.'
    output.mkdir(parents=True)
    (output / 'manifests').mkdir()
    summary = {'status': 'failed', 'invocation': str(uuid.uuid4()), 'source_project': str(project),
               'boundary': 'Every recipe retains its own complete source and report boundary. Their union is '
                           'materialized from source and proved once from HOL without a supplied project heap. '
                           'Each original execution consumes its own exported module and compares every report. '
                           'Sharing build work adds no subject semantics.'}
    write_json(output / 'suite.json', summary)
    environment = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'USER_HOME': str(isabelle_places.USER_HOME)}

    def run(name, command, timeout, log_directory, cwd):
        log = log_directory / (name + '.log')
        started = time.monotonic()
        with log.open('x') as stream:
            try:
                code = run_session(list(map(str, command)), cwd=cwd, env=environment,
                                   stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
            except subprocess.TimeoutExpired:
                code = 'timeout'
        result = {'name': name, 'command': list(map(str, command)), 'exit_code': code,
                  'seconds': time.monotonic() - started, 'log': str(log)}
        print(json.dumps(result), flush=True)
        return result

    try:
        directory = project / 'tools'
        scripts = ([directory / name for name in args.recipe] if args.recipe else
                   sorted(directory.glob('reconstruct_*.py')))
        assert scripts and len(set(p.resolve() for p in scripts)) == len(scripts)
        recipes, files, roots, exports, manifests = [], {}, set(), set(), {}
        toolchain = None
        for script in scripts:
            script = script.resolve()
            assert script.parent == directory and script.is_file()
            name, declared_roots, fixtures, jobs = recipe_inputs(script)
            recipe = runpy.run_path(str(script), run_name='reconstruction_recipe')['RECIPE']
            assert recipe.name == name and recipe.roots == declared_roots and recipe.fixtures == fixtures
            assert tuple(job.script for group in recipe.groups for job in group) == jobs
            assert all(recipe.groups) and len(recipe.executions) == len(set(recipe.executions))
            assert not set(recipe.executions) & {'proof', 'diagnostics', 'export'}
            assert name not in manifests
            spec = collect(project, script, poly)
            if toolchain is None:
                toolchain = spec['toolchain']
            assert spec['toolchain'] == toolchain
            for path, sha in spec['files'].items():
                assert path not in files or files[path] == sha
                files[path] = sha
            roots.update(declared_roots)
            exports.add(recipe.export)
            manifest = output / 'manifests' / (name + '-sources.json')
            write_json(manifest, spec)
            manifests[name] = manifest
            recipes.append((script.name, recipe, spec))
        filenames = [entry.split(':')[1] for entry in exports]
        assert len(filenames) == len(set(filenames)), 'Exported module filenames must be distinct.'
        suite_tools = local_python_closure(directory, [Path(__file__).resolve()])
        files.update({str(path.relative_to(project)): sha for path, sha in suite_tools.items()})
        union = {'version': 1, 'roots': sorted(roots), 'toolchain': toolchain,
                 'files': dict(sorted(files.items())), 'boundary': summary['boundary']}
        union_path = output / 'source-manifest.json'
        write_json(union_path, union)
        original_inputs = {str(project / path): sha for path, sha in files.items()}
        source = output / 'source'
        materialization = materialize(project, union_path, source)
        copied_inputs = {str(source / path): sha for path, sha in files.items()}
        tracked = original_inputs | copied_inputs
        tools = source / 'tools'
        summary.update(recipes=[recipe.name for _, recipe, _ in recipes],
                       source_manifest_sha256=digest(union_path), materialization=materialization,
                       execution_inputs=tracked)
        write_json(output / 'suite.json', summary)
        shared = [run('proof', [sys.executable, '-B', tools / 'prove_context.py', '--project', source,
            '--output', output / 'proof', '--session', args.session, '--threads', args.threads,
            '--timeout', args.timeout, *sorted(roots)], max(3600, args.timeout + 300), output, source)]
        databases = list((isabelle_places.USER_HOME / '.isabelle').glob(
            '*/heaps/*/log/' + args.session + '.db'))
        assert len(databases) == 1, databases
        shared.append(run('diagnostics', [sys.executable, '-B', tools / 'proof_diagnostics.py',
            '--database', databases[0], '--proof', output / 'proof/result.json',
            '--output', output / 'proof-diagnostics.json'], 180, output, source))
        assert all(step['exit_code'] == 0 for step in shared), 'See the combined proof and diagnostics.'
        proof, proved_sources = accepted_proof(output / 'proof/result.json', project=source,
                                              required_theories=sorted(roots))
        assert not proof.get('parent_theories_reused', 0), 'The combined project proof must rebuild from source.'
        assert all(path in copied_inputs and copied_inputs[path] == sha for path, sha in proved_sources.items())
        command = [sys.executable, '-B', tools / 'export_proved_code.py', '--proof', output / 'proof/result.json',
                   '--project', source, '--output', output / 'export']
        for entry in sorted(exports):
            command.extend(['--module', entry])
        shared.append(run('export', command, 180, output, source))
        assert shared[-1]['exit_code'] == 0, 'See the combined export result.'
        assert all(digest(Path(path)) == sha for path, sha in tracked.items())
        summary['shared_steps'] = shared
        write_json(output / 'suite.json', summary)

        def execute_recipe(item):
            filename, recipe, spec = item
            target = output / 'recipes' / recipe.name
            target.mkdir(parents=True)
            export = output / 'export' / (Path(recipe.export.split(':')[1]).stem + '.proof.json')
            expected_path = source / 'validation/reconstruction' / (recipe.name + '-reports.json')
            expected = json.loads(expected_path.read_text(), object_pairs_hook=unique_object)
            assert expected['version'] == 1 and set(expected['reports']) == set(recipe.executions)
            inputs = {str(source / path): sha for path, sha in spec['files'].items()}
            inputs.update({str(Path(__file__).resolve()): digest(Path(__file__).resolve()),
                           str(manifests[recipe.name]): digest(manifests[recipe.name]),
                           str(union_path): digest(union_path)})
            substitutions = {'project': str(source), 'output': str(target), 'proof': str(export), 'poly': str(poly)}
            steps = list(shared)
            for group in recipe.groups:
                jobs = [(job.name, [sys.executable, '-B', tools / job.script, '--proof', export, '--poly', poly,
                    *(argument.format_map(substitutions) for argument in job.arguments), '--output', target / job.name],
                    job.timeout, target, source) for job in group]
                if len(jobs) == 1:
                    results = [run(*jobs[0])]
                else:
                    with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
                        futures = [pool.submit(run, *job) for job in jobs]
                        results = [future.result() for future in futures]
                steps.extend(results)
                if any(step['exit_code'] != 0 for step in results):
                    break
            result = finish_reconstruction(target, source, recipe, steps, expected, inputs, False)
            result.update(shared_proof=str(output / 'proof/result.json'),
                          source_manifest_sha256=digest(manifests[recipe.name]),
                          suite_source_manifest_sha256=digest(union_path))
            write_json(target / 'reconstruction.json', result)
            print(json.dumps({'recipe': recipe.name, 'status': result['status'],
                              'reports_equal': result['reports_equal']}), flush=True)
            return result

        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = [pool.submit(execute_recipe, item) for item in recipes]
            results = [future.result() for future in as_completed(futures)]
        stable = all(Path(path).is_file() and digest(Path(path)) == sha for path, sha in tracked.items())
        summary.update(status='accepted' if stable and all(r['status'] == 'accepted' for r in results) else 'failed',
                       sources_and_tools_unchanged=stable,
                       results=[{'recipe': r['recipe'], 'status': r['status'],
                                 'sources_rebuilt': r['sources_rebuilt'], 'reports_equal': r['reports_equal'],
                                 'report_boundaries': r['report_boundaries']} for r in results])
    except Exception as error:
        summary.update(error=str(error), error_type=type(error).__name__, traceback=traceback.format_exc())
    write_json(output / 'suite.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k != 'execution_inputs'}), flush=True)
    return int(summary['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
