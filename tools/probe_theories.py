"""Load workspace theories on the accepted base heap without rebuilding the repository.

The accepted base carries a stored heap for the sources it checked, so a theory that is
new in the workspace can be loaded directly onto that heap: every unchanged import is
resolved from the heap session and the cycle costs the load of the candidates alone.

A theory the base holds and the tree changes is loaded from the tree as well, under a renamed
copy (`<Name>_Probe`): the heap already holds a theory of its name, and one context cannot merge
two theories of one base name. Every loaded theory importing it imports the copy, every qualified
reference `Name.x` in a loaded theory is rewritten to the copy's, and the changed theories are
loaded in dependency order before the new ones. The probe certifies exactly the theories it loads
from the tree, and its summary names them. Two limits are reported, not repaired: a base theory the
tree does not change that imports a changed one stays the heap's and is not re-checked
(`not_rechecked`), and a loaded theory whose heap imports reach the heap's copy of a changed theory
sees both texts at once (`stale_heap_imports`). A supplied prelude can still stand for a changed
base theory (`--substitute`), and `--from-heap` takes a changed theory from the heap. The probe is
an inner loop and does not replace the repository check.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import time

import build
import execution_support as investigate
import incremental_check
import proof_contexts

ROOT = Path(__file__).resolve().parent.parent


def workspace_theories(candidates=()):
    """Theories of the workspace, overridden by candidate theories kept in scratch directories.

A candidate outside `theories/` is probed without entering the workspace, so a probe never changes
the inputs of a repository check that runs beside it."""
    present = {path.stem: path for path in sorted((ROOT / 'theories').glob('*.thy'))}
    for directory in candidates:
        present |= {path.stem: path for path in sorted(Path(directory).glob('*.thy'))}
    return present


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


def probe_name(name):
    """The name a base theory loaded from the tree takes beside the heap's theory of its name."""
    return name + '_Probe'


def renamed_source(text, name, renamed):
    """A loaded source with its own header and every qualified reference to a renamed theory renamed."""
    for old, new in renamed.items():
        text = re.sub(r"(?<![\w.'])%s\.(?=[A-Za-z_])" % re.escape(old), new + '.', text)
    if name in renamed:
        text = re.sub(r'^(\s*theory\s+)%s(?=\s)' % re.escape(name), lambda m: m[1] + renamed[name], text, count=1)
    return text


def prepare(work, context, present, loaded, substitutions, prelude, renamed=None):
    """Write every candidate with its imports resolved to the heap, a prelude, another candidate, or the
tree's renamed copy of a changed base theory; return the directory, the imports among loaded theories
and every theory's complete imports."""
    renamed = renamed or {}
    providers = dict(context['providers'])
    providers |= {name: {'theory': theory} for name, theory in substitutions.items()}
    providers |= {name: {'theory': theory} for name, theory in renamed.items()}
    reused = {name for name in providers if name not in loaded} | set(renamed)
    directory = work / 'theories'
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob('*.thy'):
        stale.unlink()
    sources = dict(prelude) | {name: present[name] for name in loaded if name in present}
    imports, complete = {}, {}
    for name, path in sources.items():
        text = path.read_text()
        complete[name] = investigate.theory_imports(text, name)
        imports[name] = [n for n in complete[name] if n in loaded]
        written = renamed_source(proof_contexts.rewritten_source(text, name, reused, providers), name, renamed)
        (directory / (renamed.get(name, name) + '.thy')).write_text(written)
    return directory, imports, complete


DEFAULT_TIMEOUT = 60


def last_command(text):
    """The command a streamed log last reached: its last non-empty line, or None for an empty log."""
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return lines[-1] if lines else None


def run_logged(command, log, timeout, env=None):
    """Run the probe's process with its output streamed to log; report its exit, the log and a timeout.

A run past its timeout is stopped with its whole process tree. It is reported as timed out, never as a
run with no error: its errors name the timeout, the command the log last reached and the log's path."""
    with log.open('w') as stream:
        try:
            returncode = build.run_session(command, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired:
            returncode = 'timeout'
    text = log.read_text()
    timed_out = returncode == 'timeout'
    reached = last_command(text) if timed_out else None
    errors = [line for line in text.splitlines() if line.startswith('***')][:40]
    if timed_out:
        errors.append('The probe timed out after %s s while processing: %s (log %s)'
                      % (timeout, reached if reached is not None else 'nothing, its log is empty', log))
    return {'exit': returncode, 'text': text, 'timed_out': timed_out, 'last_command': reached,
            'errors': errors}


def probe(base, work, targets, loaded, substitutions, prelude, parallel_proofs, timeout, candidates=(),
          from_heap=()):
    context = proof_contexts.load_parent(base, None, *proof_contexts.new_lineage())
    assert context['sources'], 'The base ' + str(base) + ' carries no accepted sources.'
    present = workspace_theories(candidates)
    differing = changed(context['sources'], present)
    new = {name for name, accepted in differing.items() if accepted is None}
    loaded = set(loaded or (set(differing) - set(from_heap) - set(substitutions))) | set(prelude)
    missing = loaded - set(present) - set(prelude)
    assert not missing, 'Not a workspace theory: ' + ', '.join(sorted(missing))
    from_tree = {name for name in loaded - set(prelude) if context['sources'].get(name) is not None}
    renamed = {name: probe_name(name) for name in sorted(from_tree)}
    clash = sorted(set(renamed.values()) & (set(present) | set(context['sources'])))
    assert not clash, 'A renamed copy would take the name of an existing theory: ' + ', '.join(clash)
    directory, imports, complete = prepare(work, context, present, loaded, substitutions, prelude, renamed)
    graph = context.get('imports', {})
    unchanged = investigate.contexts_satisfying(graph, lambda n: n not in from_tree)
    not_rechecked = sorted(n for n, clean in unchanged.items()
                           if not clean and n not in loaded and n not in substitutions)
    stale = {}
    for name in sorted(loaded):
        heap = [n for n in complete.get(name, []) if n not in loaded and n not in substitutions]
        reached = sorted(investigate.import_contexts(graph, heap) & from_tree)
        if reached:
            stale[name] = reached
    order = ordered({n: i for n, i in imports.items() if n in (targets or loaded)})
    marker = 'PROBE THEORIES LOADED'
    script = work / 'probe.ML'
    script.write_text(''.join('val _ = Thy_Info.use_thy_legacy "%s";\n' % (directory / renamed.get(name, name))
                              for name in order)
                      + 'val _ = writeln "%s";\n' % marker)
    log = work / 'probe.log'
    options = [] if parallel_proofs is None else ['-o', 'parallel_proofs=%d' % parallel_proofs]
    directories = [argument for directory in context['directories'] for argument in ('-d', directory)]
    command = ['isabelle', 'ML_process', *directories, '-l', context['session'], *options, '-f', str(script)]
    started = time.monotonic()
    run = run_logged(command, log, timeout, env=incremental_check.ENV)
    text = run['text']
    marker_line = next((line for line in text.splitlines() if marker in line), None)
    completed = marker_line is not None and not run['timed_out']
    summary = {'base': str(base), 'session': context['session'], 'seconds': round(time.monotonic() - started, 1),
               'exit': run['exit'], 'loaded': completed, 'order': order,
               'certified': order if completed and not run['errors'] else [],
               'from_tree': renamed, 'new': sorted(new & loaded),
               'not_rechecked': not_rechecked, 'stale_heap_imports': stale,
               'marker': marker_line, 'timed_out': run['timed_out'], 'last_command': run['last_command'],
               'parallel_proofs': parallel_proofs, 'timeout': timeout,
               'substituted': substitutions, 'prelude': {name: str(path) for name, path in sorted(prelude.items())},
               'from_heap_despite_change': sorted(set(differing) - loaded - set(substitutions)),
               'from_heap': sorted(from_heap),
               'errors': run['errors'], 'log': str(log), 'summary': str(work / 'probe.summary.json')}
    Path(summary['summary']).write_text(json.dumps(summary) + '\n')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, help='Override the active accepted context.')
    parser.add_argument('--work', type=Path, required=True, help='Directory for the rewritten sources and the log.')
    parser.add_argument('--theory', action='append', default=[], help='Candidate to load; default every new theory.')
    parser.add_argument('--load', action='append', default=[],
                        help='Theory loaded from workspace source; default every theory the tree changes or adds.')
    parser.add_argument('--from-heap', action='append', default=[], metavar='THEORY',
                        help='A changed base theory taken from the heap rather than loaded from the tree.')
    parser.add_argument('--prelude', type=Path, action='append', default=[],
                        help='Theory stating added content of a changed base theory on top of the heap.')
    parser.add_argument('--substitute', action='append', default=[], metavar='THEORY=PRELUDE',
                        help='Resolve imports of a changed base theory to a prelude instead of the heap.')
    parser.add_argument('--parallel-proofs', type=int,
                        help='Override Isabelle parallel_proofs; 0 attributes elapsed time to one failing proof.')
    parser.add_argument('--timeout', type=int, default=DEFAULT_TIMEOUT,
                        help='Seconds before the probe is stopped; a longer limit is a measurement.')
    parser.add_argument('--candidates', type=Path, action='append', default=[],
                        help='Directory of candidate theories kept outside theories/; a candidate overrides '
                             'the workspace theory of its name.')
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Probing requires Python assertions.')
    args.work.mkdir(parents=True, exist_ok=True)
    substitutions = dict(pair.split('=', 1) for pair in args.substitute)
    prelude = {path.stem: path.resolve() for path in args.prelude}
    absent = sorted(name for name in substitutions.values() if name not in prelude)
    assert not absent, ('A substitution names no supplied prelude: ' + ', '.join(absent)
                        + '; the supplied preludes are ' + (', '.join(sorted(prelude)) or 'none') + '.')
    summary = probe(incremental_check.selected_base(args.base).resolve(), args.work.resolve(), args.theory,
                    args.load, substitutions, prelude, args.parallel_proofs, args.timeout,
                    [directory.resolve() for directory in args.candidates], args.from_heap)
    print(json.dumps(summary))
    return 0 if summary['loaded'] and not summary['exit'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
