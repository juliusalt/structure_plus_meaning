"""Load workspace theories on the accepted base heap without rebuilding the repository.

The accepted base carries a stored heap for the sources it checked, so a theory that is
new in the workspace can be loaded directly onto that heap: every unchanged import is
resolved from the heap session and the cycle costs the load of the candidates alone. A
theory that already exists in the base is not loaded from source here, because the heap
holds its dependents built against the accepted text; the probe resolves such an import
from the heap and reports that it did, or from a supplied prelude that states the added
content on top of the heap. The probe therefore observes that the candidate sources load
against accepted content. It observes nothing about the dependents of a changed base
theory and does not replace the repository check.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import time

import build
import execution_support as investigate
import incremental_check
import proof_contexts

ROOT = Path(__file__).resolve().parent.parent


def workspace_theories():
    return {path.stem: path for path in sorted((ROOT / 'theories').glob('*.thy'))}


def changed(sources, present):
    """Theory names whose workspace text differs from the accepted source of the base."""
    return {name: sources.get(name) for name, path in present.items()
            if sources.get(name) != investigate.file_hash(path)}


def ordered(names):
    """Candidates in load order, so a failure is attributed to the first theory that fails."""
    remaining, order = dict(names), []
    while remaining:
        ready = [n for n, imports in remaining.items() if not (set(imports) & set(remaining))]
        assert ready, 'Candidate imports form a cycle: ' + ', '.join(sorted(remaining))
        order += sorted(ready)
        remaining = {n: i for n, i in remaining.items() if n not in ready}
    return order


def prepare(work, context, present, loaded, substitutions, prelude):
    """Write every candidate with its imports resolved to the heap, a prelude or another candidate."""
    providers = dict(context['providers'])
    providers |= {name: {'theory': theory} for name, theory in substitutions.items()}
    reused = {name for name in providers if name not in loaded}
    directory = work / 'theories'
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob('*.thy'):
        stale.unlink()
    sources = dict(prelude) | {name: present[name] for name in loaded if name in present}
    imports = {}
    for name, path in sources.items():
        text = path.read_text()
        imports[name] = [n for n in investigate.theory_imports(text, name) if n in loaded]
        (directory / (name + '.thy')).write_text(proof_contexts.rewritten_source(text, name, reused, providers))
    return directory, imports


def probe(base, work, targets, loaded, substitutions, prelude, parallel_proofs, timeout):
    context = proof_contexts.load_parent(base, None, *proof_contexts.new_lineage())
    assert context['sources'], 'The base carries no accepted sources.'
    present = workspace_theories()
    differing = changed(context['sources'], present)
    new = {name for name, accepted in differing.items() if accepted is None}
    loaded = set(loaded or new) | set(prelude)
    missing = loaded - set(present) - set(prelude)
    assert not missing, 'Not a workspace theory: ' + ', '.join(sorted(missing))
    directory, imports = prepare(work, context, present, loaded, substitutions, prelude)
    order = ordered({n: i for n, i in imports.items() if n in (targets or loaded)})
    marker = 'PROBE THEORIES LOADED'
    script = work / 'probe.ML'
    script.write_text(''.join('val _ = Thy_Info.use_thy_legacy "%s";\n' % (directory / name) for name in order)
                      + 'val _ = writeln "%s";\n' % marker)
    log = work / 'probe.log'
    options = [] if parallel_proofs is None else ['-o', 'parallel_proofs=%d' % parallel_proofs]
    directories = [argument for directory in context['directories'] for argument in ('-d', directory)]
    command = ['isabelle', 'ML_process', *directories, '-l', context['session'], *options, '-f', str(script)]
    started = time.monotonic()
    with log.open('w') as stream:
        try:
            returncode = build.run_session(command, env=incremental_check.ENV, stdout=stream,
                                           stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired:
            returncode = 'timeout'

    text = log.read_text()
    return {'base': str(base), 'session': context['session'], 'seconds': round(time.monotonic() - started, 1),
            'exit': returncode, 'loaded': marker in text, 'order': order,
            'parallel_proofs': parallel_proofs,
            'substituted': substitutions, 'prelude': sorted(prelude),
            'from_heap_despite_change': sorted(set(differing) - loaded - set(substitutions)),
            'errors': [line for line in text.splitlines() if line.startswith('***')][:40], 'log': str(log)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, help='Override the active accepted context.')
    parser.add_argument('--work', type=Path, required=True, help='Directory for the rewritten sources and the log.')
    parser.add_argument('--theory', action='append', default=[], help='Candidate to load; default every new theory.')
    parser.add_argument('--load', action='append', default=[],
                        help='Theory loaded from workspace source; default every theory absent from the base.')
    parser.add_argument('--prelude', type=Path, action='append', default=[],
                        help='Theory stating added content of a changed base theory on top of the heap.')
    parser.add_argument('--substitute', action='append', default=[], metavar='THEORY=PRELUDE',
                        help='Resolve imports of a changed base theory to a prelude instead of the heap.')
    parser.add_argument('--parallel-proofs', type=int,
                        help='Override Isabelle parallel_proofs; 0 attributes elapsed time to one failing proof.')
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Probing requires Python assertions.')
    args.work.mkdir(parents=True, exist_ok=True)
    substitutions = dict(pair.split('=', 1) for pair in args.substitute)
    prelude = {path.stem: path.resolve() for path in args.prelude}
    assert set(substitutions.values()) <= set(prelude), 'A substitution names no supplied prelude.'
    summary = probe(incremental_check.selected_base(args.base).resolve(), args.work.resolve(), args.theory,
                    args.load, substitutions, prelude, args.parallel_proofs, args.timeout)
    print(json.dumps(summary))
    return 0 if summary['loaded'] and not summary['exit'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
