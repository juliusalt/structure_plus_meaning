"""Load workspace theories on the accepted base heap without rebuilding the repository.

The accepted base carries a stored heap for the sources it checked, so a theory that is
new in the workspace can be loaded directly onto that heap: every unchanged import is
resolved from the heap session and the cycle costs the load of the candidates alone.

A theory the base holds and the tree changes is loaded from the tree as well, under a renamed
copy (`<Name>_Probe`): the heap already holds a theory of its name, and one context cannot merge
two theories of one base name. Every loaded theory importing it imports the copy, every qualified
reference `Name.x` in a loaded theory is rewritten to the copy's, and the changed theories are
loaded in dependency order before the new ones. An unchanged base theory standing on an import path
from a changed base theory to a loaded theory is loaded as a renamed copy too (`intermediate`), so no
loaded theory meets the heap's copy of a theory the tree changes. The probe certifies exactly the
theories it loads from the tree, and its summary names them. Two limits are reported, not repaired: a
base theory the tree does not change that imports a changed one and that no loaded theory imports stays
the heap's and is not re-checked (`not_rechecked`), and a loaded theory whose heap imports reach the
heap's copy of a changed theory taken from the heap or a prelude sees both texts at once
(`stale_heap_imports`, then the cause of every error the run reports, said in the summary and the log).
A supplied prelude can still stand for a changed base theory (`--substitute`), and `--from-heap` takes
a changed theory from the heap. A load estimated to exceed the bound is refused before it runs, the
chain named. The probe is an inner loop and does not replace the repository check.

The probe runs Isabelle's ML process, which has no Scala side: `export_code … checking TARGET` writes the
generated code into a directory and compiles it through a shell, both functions of the Scala side
(`Isabelle_System.with_tmp_dir` and `bash_process` in Code_Target), and in the ML process it raises
`Protocol_Message invoke_scala`. Such a command is therefore blanked in the probe's copy, its lines kept, and
named in the summary as skipped (`skipped_code_checks`, a `PROBE SKIPPED` line in the log): it is never a
theory's error and never counted as certifying the exported code, which the repository's check exports and
checks. A command that exports (`in TARGET …`) stands. With `--base-sources` the probe reads the base's own
sources (its `original-sources`) instead of the workspace's, so a past base is probed as it was accepted.

A tree's theories can differ from the base without the task having changed them: the base advanced with main
after the tree left it. Such a theory (`advanced`: the tree holds its text of the branch point, the base main's
text) is never loaded as the task's change; the probe is refused before it writes anything, naming the theories,
the cause and the remedy (`v2.py bring-main`, or `--base` at a heap the tree matches).
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
import isabelle_places
import proof_contexts

ROOT = Path(__file__).resolve().parent.parent


def workspace_theories(candidates=(), sources=None):
    """Theories of the workspace, or of the directory sources, overridden by candidate theories kept in
scratch directories.

A candidate outside `theories/` is probed without entering the workspace, so a probe never changes
the inputs of a repository check that runs beside it."""
    present = {path.stem: path for path in sorted(Path(sources or ROOT / 'theories').glob('*.thy'))}
    for directory in candidates:
        present |= {path.stem: path for path in sorted(Path(directory).glob('*.thy'))}
    return present


def changed(sources, present):
    """Theory names whose workspace text differs from the accepted source of the base."""
    return {name: sources.get(name) for name, path in present.items()
            if sources.get(name) != investigate.file_hash(path)}


def git_output(*arguments, text=None):
    """The output of a git command in the tree, or None where git or the reference is not there."""
    try:
        return subprocess.run(['git', '-C', str(ROOT), *arguments], input=text, capture_output=True,
                              check=True).stdout
    except (OSError, subprocess.CalledProcessError):
        return None


def advanced_theories(differing, present, main='main'):
    """Differing theories the tree has not changed since it left main and whose accepted base text is main's:
they differ from the base only because main advanced after the tree's branch point."""
    theories = ROOT / 'theories'
    unchanged = [name for name, accepted in differing.items()
                 if accepted is not None and name in present and present[name].parent == theories]
    point = git_output('merge-base', 'HEAD', main) if unchanged else None
    if not point:
        return []
    ours = git_output('diff', '--name-only', point.decode().strip(), '--', 'theories')
    untracked = git_output('ls-files', '--others', '--exclude-standard', 'theories')
    if ours is None or untracked is None:
        return []
    touched = {Path(line).stem for line in (ours + untracked).decode().split()}
    unchanged = [name for name in unchanged if name not in touched]
    batch = git_output('cat-file', '--batch', text=''.join('%s:theories/%s.thy\n' % (main, n) for n in unchanged)
                       .encode()) if unchanged else None
    advanced, position = [], 0
    for name in unchanged if batch else []:
        header_end = batch.index(b'\n', position)
        header = batch[position:header_end].split()
        if header[-1] == b'missing':
            position = header_end + 1
            continue
        size = int(header[2])
        content = batch[header_end + 1:header_end + 1 + size]
        position = header_end + 2 + size
        if investigate.digest(content) == differing[name]:
            advanced.append(name)
    return sorted(advanced)


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


CODE_TARGETS = frozenset({'SML', 'OCaml', 'Haskell', 'Scala'})
COMMANDS = frozenset({'text', 'txt', 'section', 'subsection', 'subsubsection', 'paragraph', 'lemma', 'lemmas',
                      'theorem', 'corollary', 'proposition', 'definition', 'abbreviation', 'fun', 'function',
                      'primrec', 'datatype', 'record', 'type_synonym', 'typedef', 'declare', 'context', 'locale',
                      'interpretation', 'sublocale', 'end', 'ML', 'value', 'notation', 'code_printing',
                      'export_code', 'lift_definition', 'setup_lifting', 'termination', 'inductive'})
TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|\\<open>.*?\\<close>|\(\*.*?\*\)|\S+', re.S)
EXPORT_CODE = re.compile(r'^[ \t]*export_code(?=\s)', re.M)


def skip_code_checks(text):
    """The source with every `export_code … checking TARGET…` command blanked to its newlines, so every other
line keeps its number, and the commands skipped, each with the line it starts at and its words."""
    pieces, skipped, last = [], [], 0
    for match in EXPORT_CODE.finditer(text):
        if match.start() < last:
            continue
        tokens, end = TOKEN.finditer(text, match.end()), None
        for token in tokens:
            if token.group() == 'in' or token.group() in COMMANDS:
                break
            if token.group() == 'checking':
                for target in tokens:
                    if target.group() not in CODE_TARGETS:
                        break
                    end = target.end()
                break
        if end is None:
            continue
        span = text[match.start():end]
        pieces += [text[last:match.start()], '\n' * span.count('\n')]
        skipped.append({'line': text.count('\n', 0, match.start()) + 1, 'command': ' '.join(span.split())})
        last = end
    return ''.join(pieces) + text[last:], skipped


def prepare(work, context, present, loaded, substitutions, prelude, renamed=None):
    """Write every candidate with its imports resolved to the heap, a prelude, another candidate, or the
tree's renamed copy of a changed base theory, its code checks skipped; return the directory, the imports
among loaded theories, every theory's complete imports and the code checks skipped in each theory."""
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
    imports, complete, skipped = {}, {}, {}
    for name, path in sources.items():
        text = path.read_text()
        complete[name] = investigate.theory_imports(text, name)
        imports[name] = [n for n in complete[name] if n in loaded]
        written = renamed_source(proof_contexts.rewritten_source(text, name, reused, providers), name, renamed)
        written, checks = skip_code_checks(written)
        if checks:
            skipped[name] = checks
        (directory / (renamed.get(name, name) + '.thy')).write_text(written)
    return directory, imports, complete, skipped


DEFAULT_TIMEOUT = 60
# A probe's start on the base, by task 623's model (.build/tasks/623/result.md, "The estimate STARTUP_SECONDS should
# give"; measured on base 20260926-015341-train617-583 at light load): start = START_SECONDS + SECONDS_PER_SESSION
# x S + SECONDS_PER_GB x G, S the sessions of the base's chain above HOL (its directories), G the GB of the chain's
# heap files down to Pure. A lower envelope: within about 1 s of every measured prefix of the chain and of a base of
# one heap; contention only makes the start longer.
START_SECONDS = 1.6  # the process at HOL: the JVM, Isabelle/Scala, Poly/ML's start (623's IC and IHS runs)
SECONDS_PER_SESSION = 0.085  # Isabelle/Scala's session dependencies, per session of the chain (IBS - IHDS)
SECONDS_PER_GB = 1.5  # Poly/ML's load of the chain's heaps, per GB of heap file (PB - PC)
# The rate of a load past the start, re-derived by task 625 (.build/tasks/625/derive.py) from the 504 completed
# probes retained under .build/tasks/ on 2026-09-26 (their probe.summary.json, over 92 bases whose chains stand in
# the store), each probe's start computed by the model above for its own base and subtracted from its seconds. Over
# the 367 probes whose load past the start exceeds 5 s (five times the model's accuracy), the fastest loaded
# 394,188 bytes in 11.1 s: 35,512 bytes per second. At 36,000 no such probe is estimated above its measured seconds;
# 13 small loads (at most 239,484 bytes) are estimated 1-2.6 s above, where the start's accuracy dominates. Proofs
# make a load slower than this, never faster, so the estimate refuses only a load that cannot fit its bound; the
# timeout stays the backstop. (The earlier 25,000 was drawn with a constant start of 10 s.)
BYTES_PER_SECOND = 36000
ISABELLE_HOME = Path('/opt/isabelle')
HEAPS = isabelle_places.USER_HOME / '.isabelle/Isabelle2025-2/heaps/polyml-5.9.2_x86_64_32-linux'
SESSION_ENTRY = re.compile(r'^[ \t]*session[ \t]+"?([^\s"(=]+)"?[^=\n]*=[ \t]*(?:"?([^\s"+]+)"?)?', re.M)


def base_context(base, verify=False):
    """The claims of the accepted base: read from its context file, verified only when asked.

The lineage's verification digests every level's heap and database (5.4 s against 0.02 s for reading the
file, measured by task 271) and is the check's business, not the inner loop's. An unverified read trusts
the file's claims: a heap or database changed since the file was written is not detected by the probe,
and `--verify-base` is then its check. A base without a context file is verified, as it has no other
record."""
    path = Path(base) / proof_contexts.CONTEXT_FILE
    if verify or not path.is_file():
        return proof_contexts.load_parent(base, None, *proof_contexts.new_lineage())
    saved = json.loads(path.read_text())
    return {key: saved[key] for key in ('session', 'sources', 'imports', 'providers', 'directories')}


def intermediate_theories(graph, tree_imports, changed_base, loaded, excluded=()):
    """Unchanged base theories on an import path from a changed base theory to a loaded theory.

graph is the base's import graph; tree_imports the workspace imports of the loaded theories, which
take their place. A theory is on such a path when it imports a changed base theory, directly or
through others, and a loaded theory imports it, directly or through others, never through an excluded
theory: an excluded theory comes from the heap with the heap's imports, so no copy below it is met."""
    above = {n for n, clean in investigate.contexts_satisfying(graph, lambda n: n not in changed_base).items()
             if not clean}
    combined = {name: parents for name, parents in
                (dict(graph) | {name: list(parents) for name, parents in tree_imports.items()}).items()
                if name not in excluded}
    below = investigate.import_contexts(combined, [p for n in loaded for p in combined.get(n, [])])
    return sorted((above & below) - set(changed_base) - set(loaded) - set(excluded))


def session_parents(directories):
    """Each session the ROOT files of these directories declare, with the parent it names (None for none)."""
    parents = {}
    for directory in directories:
        root = Path(directory) / 'ROOT'
        if root.is_file():
            parents.update((name, parent or None) for name, parent in SESSION_ENTRY.findall(root.read_text()))
    return parents


def distribution_directories():
    """The session directories of the Isabelle distribution, as its ROOTS file lists them."""
    roots = ISABELLE_HOME / 'ROOTS'
    lines = roots.read_text().splitlines() if roots.is_file() else []
    return [ISABELLE_HOME / line.strip() for line in lines if line.strip() and not line.startswith('#')]


def session_chain(session, directories):
    """The session and its ancestors down to Pure: by the base's ROOT files, then the distribution's."""
    parents, distribution = session_parents(directories), None
    chain = []
    while session is not None and session not in chain:
        chain.append(session)
        if session not in parents and distribution is None:
            distribution = session_parents(distribution_directories())
        session = parents[session] if session in parents else distribution.get(session)
    return chain


def modeled_start(context):
    """A probe's start on the base by task 623's model: its seconds, the chain's sessions above HOL (the base's
directories) and the GB of the chain's heap files in the store."""
    sessions = len(context['directories'])
    heaps = [HEAPS / name for name in session_chain(context['session'], context['directories'])]
    gigabytes = sum(heap.stat().st_size for heap in heaps if heap.is_file()) / 1e9
    return round(START_SECONDS + SECONDS_PER_SESSION * sessions + SECONDS_PER_GB * gigabytes, 1), sessions, gigabytes


def load_estimate(paths, context):
    """Seconds a load of these sources is expected to take on the base: its modeled start and a rate of bytes;
the start, its sessions and GB returned beside the estimate and the bytes."""
    size = sum(Path(path).stat().st_size for path in paths)
    start = modeled_start(context)
    return round(start[0] + size / BYTES_PER_SECOND, 1), size, start


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
          from_heap=(), verify_base=False, base_sources=False):
    context = base_context(base, verify_base)
    assert context['sources'], 'The base ' + str(base) + ' carries no accepted sources.'
    present = workspace_theories(candidates, Path(base) / 'original-sources' if base_sources else None)
    if base_sources:
        absent = sorted(set(context['sources']) - set(present))
        assert not absent, ('The base %s keeps no original source of %d of its theories: %s'
                            % (base, len(absent), ', '.join(absent[:10])))
    differing = changed(context['sources'], present)
    new = {name for name, accepted in differing.items() if accepted is None}
    advanced = [name for name in advanced_theories(differing, present)
                if name not in from_heap and name not in substitutions]
    if advanced:
        refusal = ('The probe is refused before it loads: %d theories differ from the base %s only because main '
                   'advanced after this tree left it (the tree holds their text of its branch point, the base '
                   "main's): %s. Bring main into the tree (`.claude/orchestration/v2.py bring-main`), or give "
                   '--base a heap the tree matches.' % (len(advanced), base, ', '.join(advanced)))
        summary = {'base': str(base), 'session': context['session'], 'advanced': advanced, 'refused': refusal,
                   'loaded': False, 'certified': [], 'exit': None, 'seconds': 0, 'timed_out': False,
                   'marker': None, 'last_command': None, 'cause': refusal, 'errors': [refusal], 'messages': [],
                   'log': None, 'summary': str(work / 'probe.summary.json')}
        Path(summary['summary']).write_text(json.dumps(summary) + '\n')
        return summary
    loaded = set(loaded) | (set(differing) - set(from_heap) - set(substitutions)) | set(prelude)
    missing = loaded - set(present) - set(prelude)
    assert not missing, 'Not a workspace theory: ' + ', '.join(sorted(missing))
    graph = context.get('imports', {})
    changed_base = {name for name in loaded - set(prelude) if context['sources'].get(name) is not None}
    tree_imports = {name: investigate.theory_imports(present[name].read_text(), name)
                    for name in loaded if name in present}
    intermediate = intermediate_theories(graph, tree_imports, changed_base, loaded,
                                         set(substitutions) | set(from_heap))
    loaded |= set(intermediate)
    from_tree = {name for name in loaded - set(prelude) if context['sources'].get(name) is not None}
    renamed = {name: probe_name(name) for name in sorted(from_tree)}
    clash = sorted(set(renamed.values()) & (set(present) | set(context['sources'])))
    assert not clash, 'A renamed copy would take the name of an existing theory: ' + ', '.join(clash)
    directory, imports, complete, skipped = prepare(work, context, present, loaded, substitutions, prelude,
                                                    renamed)
    unchanged = investigate.contexts_satisfying(graph, lambda n: n not in from_tree)
    not_rechecked = sorted(n for n, clean in unchanged.items()
                           if not clean and n not in loaded and n not in substitutions)
    stale = {}
    for name in sorted(loaded):
        heap = [n for n in complete.get(name, []) if n not in loaded and n not in substitutions]
        reached = sorted(investigate.import_contexts(graph, heap) & from_tree)
        if reached:
            stale[name] = reached
    closure = investigate.import_contexts(imports, targets) if targets else set(loaded)
    order = ordered({n: i for n, i in imports.items() if n in closure})
    skipped = {name: skipped[name] for name in order if name in skipped}
    estimate, size, start = load_estimate([directory / (renamed.get(name, name) + '.thy') for name in order], context)
    common = {'base': str(base), 'session': context['session'], 'order': order, 'advanced': [],
              'from_tree': renamed, 'intermediate': intermediate, 'new': sorted(new & loaded),
              'not_rechecked': not_rechecked, 'stale_heap_imports': stale, 'skipped_code_checks': skipped,
              'estimate_seconds': estimate, 'estimate_bytes': size,
              'estimate_start': {'seconds': start[0], 'sessions': start[1], 'heap_gb': round(start[2], 3)},
              'parallel_proofs': parallel_proofs, 'timeout': timeout,
              'substituted': substitutions, 'prelude': {name: str(path) for name, path in sorted(prelude.items())},
              'from_heap_despite_change': sorted(set(differing) - loaded - set(substitutions)),
              'from_heap': sorted(from_heap), 'summary': str(work / 'probe.summary.json')}
    if estimate > timeout:
        refusal = ('The probe is refused before it loads: its load of %d theories (%d bytes) is estimated at '
                   '%s s, past its bound of %s s: the start on the base modeled at %s s (%d sessions above HOL, '
                   '%.2f GB of heaps) and %d bytes at %d bytes per second; the chain it would load is %s%s. Ask '
                   'for the repository check instead, or give the probe a longer --timeout as a measurement.'
                   % (len(order), size, estimate, timeout, start[0], start[1], start[2], size, BYTES_PER_SECOND,
                      ' -> '.join(order),
                      ('; its intermediates: ' + ', '.join(intermediate)) if intermediate else ''))
        summary = common | {'refused': refusal, 'loaded': False, 'certified': [], 'exit': None, 'seconds': 0,
                            'timed_out': False, 'marker': None, 'last_command': None, 'cause': None,
                            'errors': [refusal], 'messages': [], 'log': None}
        Path(summary['summary']).write_text(json.dumps(summary) + '\n')
        return summary
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
    if skipped:
        with log.open('a') as stream:
            stream.write(''.join('PROBE SKIPPED: %s line %d: %s (no Scala side in the probe; the repository '
                                 'check runs it)\n' % (name, check['line'], check['command'])
                                 for name, checks in skipped.items() for check in checks))
    text = run['text']
    marker_line = next((line for line in text.splitlines() if marker in line), None)
    completed = marker_line is not None and not run['timed_out']
    cause = None
    errors = run['errors']
    if stale:
        cause = ('stale_heap_imports: ' + '; '.join('%s reaches the heap copy of %s' % (name, ', '.join(reached))
                                                    for name, reached in sorted(stale.items()))
                 + '. The run meets the heap text and the tree text of these theories at once, so its '
                   'messages are this cause, not errors of the theories; they are kept under "messages".')
        errors = [cause] if (errors or not completed) else []
        with log.open('a') as stream:
            stream.write('PROBE CAUSE: ' + cause + '\n')
    summary = common | {'seconds': round(time.monotonic() - started, 1), 'exit': run['exit'], 'loaded': completed,
                        'certified': order if completed and not run['errors'] and not stale else [],
                        'refused': None, 'cause': cause, 'marker': marker_line, 'timed_out': run['timed_out'],
                        'last_command': run['last_command'], 'errors': errors, 'messages': run['errors'],
                        'log': str(log)}
    Path(summary['summary']).write_text(json.dumps(summary) + '\n')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, help='Override the active accepted context.')
    parser.add_argument('--work', type=Path, required=True, help='Directory for the rewritten sources and the log.')
    parser.add_argument('--theory', action='append', default=[],
                        help='Theory whose load the probe runs: it and the loaded theories it imports are '
                             'loaded and certified; default every loaded theory.')
    parser.add_argument('--load', action='append', default=[],
                        help='Theory loaded from workspace source besides every theory the tree changes or adds '
                             'and the unchanged theories between them.')
    parser.add_argument('--verify-base', action='store_true',
                        help='Verify the base lineage (its heaps and databases) before loading; the check does.')
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
    parser.add_argument('--base-sources', action='store_true',
                        help="Read the base's own accepted sources instead of the workspace's.")
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
                    [directory.resolve() for directory in args.candidates], args.from_heap, args.verify_base,
                    args.base_sources)
    print(json.dumps(summary))
    return 0 if summary['loaded'] and not summary['exit'] and not summary['cause'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
