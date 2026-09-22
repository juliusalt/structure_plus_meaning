#!/usr/bin/env python3
"""Adopt an accepted answer to a request of the refinement layer into the published repository state.

Adoption is a generation over the repository: the theory Isabelle accepted when the answer was
judged, framed where it is adopted, becomes a theory of the repository that the layer's import
boundary imports. The tool moves bytes and invokes the checked tools; it decides nothing. Each step
is judged by the existing machinery:

0. Before anything, a theory of the answer's name in the workspace refuses the adoption: already
   adopted when its evidence (`development_answer.adoption_evidence`) holds, obstructed otherwise,
   which is not this tool's to resolve. A tree whose `theories/`, `ROOT` or `tools/` differ from its
   commit is refused too, and that commit is retained as `revision`, so the precondition's judgment is
   reproducible from the repository.
1. The retained answer is judged again against the present workspace, and its verdict and
   publication words must be the retained ones: nothing the answer was accepted against has moved.
   A differing word makes the answer a re-evaluation for the process, and nothing is installed. An
   answer is adoptable when its verdict accepts it, or when the verdict refuses it only for constants
   it introduces and the repair derived from that refusal accepts it: the extension defining those
   constants is conservative and the answer is accepted against the request issued again over the
   extension. The derived definition problems are answered by the answer's own definitions. In both
   routes the admitted answer's certified generation must publish over the incumbent it was judged
   against: the native transaction that expects that incumbent at the problem's locus applies.
2. The judged frame is installed byte for byte, its digest the precondition's `frame_sha256`, the
   judged frame's identity, and the boundary imports it.
3. The ordinary incremental check proves the changed theories and executes every recipe whose
   execution boundary the change reaches; every report word must equal its retained word.
4. The adoption's evidence holds in the adopted workspace with the receipt the tool is about to
   retain, and the check's accepted proof context records the installed theory at the frame's digest:
   the check proved this content, not a later one. No harness judgment is run: the published state is
   never judged against itself. The tool then writes the receipt to its output and retains it as
   `validation/development-adoptions/<theory>.json` (a control's too, withdrawn), since without it
   the evidence does not hold.

An adoption that does not succeed changes nothing, whatever ends it. The files installation writes are
read before its first write, and one cleanup path, reached by every exit after the adoption directory
is made (any exception, `BaseException` included, and SIGINT, SIGTERM or SIGHUP, which are delivered as
exceptions while the adoption runs and deferred while it cleans up, `build.interruption_signals`; a
signal inherited as ignored stays ignored), returns them to their original
text and writes the receipt; a deferred or received termination signal is delivered again once the
receipt is written, and an exception other than a refusal propagates after it. A withdrawal that fails
part-way names the files it restored and those it could not, and ends the run with an error. A receipt
that cannot be written is printed to stderr and its error raised, chained to the original one, after
the signals are delivered again. The summary is printed and flushed, and a withdrawal that restored not every
file is reported, before any signal is delivered again, and SIGINT is delivered last: its default handler raises
KeyboardInterrupt, which ends the run there. A signal received between entering the handlers and the adoption's
first step is raised at that step, not deferred to the end. SIGKILL is beyond any handler. The receipt retains every step and, for every executed recipe, its measured
seconds beside its retained seconds. Measured cost is an observation; nothing is ranked or selected by
it. Which recipes a change reaches is computed by the host from manifests.
"""
from __future__ import annotations

import argparse
import contextlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

import build
import development_answer
from evidence_io import write_json
import execution_support as investigate
import proof_contexts

ROOT = development_answer.ROOT
TOOLS = ROOT / 'tools'
LAYER = development_answer.STATES['refinement_layer']['layer']


def revision(project=None):
    """The commit of the tree the adoption runs in, refusing a tree whose theories, ROOT or tools differ from it."""
    project = ROOT if project is None else project
    status = subprocess.run(['git', '-C', str(project), 'status', '--porcelain', '--untracked-files=all', '--',
                             'theories', 'ROOT', 'tools'], capture_output=True, text=True, check=True).stdout
    assert not status.strip(), 'The tree differs from its commit: ' + ', '.join(
        line[3:] for line in status.splitlines()[:8])
    return subprocess.run(['git', '-C', str(project), 'rev-parse', 'HEAD'], capture_output=True, text=True,
                          check=True).stdout.strip()


def context_sources(context):
    """The theory digests an accepted proof context records, read through its verified lineage."""
    return proof_contexts.load_parent(Path(context))['sources']


def retained_text(receipt):
    return json.dumps(receipt, indent=1, sort_keys=True) + '\n'


def redeliver(received):
    """Deliver the received termination signals again, SIGINT last: its default handler raises KeyboardInterrupt,
which would keep the others from being delivered."""
    for signum in sorted(set(received), key=lambda received_signal: received_signal == signal.SIGINT):
        os.kill(os.getpid(), signum)


def judge(answer_file, output, timeout):
    started = time.monotonic()
    completed = subprocess.run([sys.executable, '-B', str(TOOLS / 'development_answer.py'), 'answer', '--answer',
                                str(answer_file), '--output', str(output), '--timeout', str(timeout)],
                               cwd=ROOT, capture_output=True, text=True, timeout=timeout + 600)
    record = json.loads((output / 'answer.json').read_text()) if (output / 'answer.json').is_file() else \
        {'status': 'failed', 'error': completed.stdout[-2000:] + completed.stderr[-2000:]}
    record['seconds'] = round(time.monotonic() - started, 2)
    return record


def prepare(answer, judged, frame_sha256):
    """What installation writes: each file with its text before and after, all read before any write.

The theory exactly as it was judged, the layer importing it at its boundary and ROOT declaring it.
Every check that can refuse the installation is made here, so a refusal here has written nothing."""
    name = development_answer.answer_name(answer)
    text = (judged / 'project' / 'theories' / (name + '.thy')).read_text()
    assert investigate.digest(text.encode()) == frame_sha256, 'The judged frame is not the frame the judgment accepted.'
    theory = ROOT / 'theories' / (name + '.thy')
    assert not theory.exists()
    assert not (ROOT / development_answer.ADOPTIONS / (name + '.json')).exists(), \
        'A retained adoption receipt of this answer already stands.'
    layer = ROOT / 'theories' / (LAYER + '.thy')
    root = ROOT / 'ROOT'
    layer_text, root_text = layer.read_text(), root.read_text()
    header = re.match(r'(\s*theory\s+\S+\s+imports\s+)([\s\S]*?)(\s+begin\b)', layer_text)
    assert header and name not in investigate.theory_imports(layer_text, LAYER)
    entry = '    ' + LAYER + '\n'
    assert root_text.count(entry) == 1
    return [(theory, None, text),
            (layer, layer_text, header[1] + header[2] + ' ' + name + header[3] + layer_text[header.end():]),
            (root, root_text, root_text.replace(entry, '    ' + name + '\n' + entry))]


def install(answer, plan, frame_sha256):
    """Write the planned files. The caller holds the plan before this runs, so any failure here is withdrawn."""
    for path, before, after in plan:
        path.write_text(after)
    theory, layer, root = (path for path, before, after in plan)
    assert investigate.file_hash(theory) == frame_sha256, 'The installed theory is not the judged frame.'
    assert development_answer.answer_name(answer) in investigate.theory_imports(layer.read_text(), LAYER)
    return {'theory': str(theory.relative_to(ROOT)), 'theory_sha256': investigate.file_hash(theory),
            'layer_sha256': investigate.file_hash(layer), 'root_sha256': investigate.file_hash(root)}


def withdraw(plan):
    """Return every planned file to its text before installation, reporting what was restored and what not.

A file already at its original text is left alone, so a failure that came before its write does not
make the withdrawal write it. A file that cannot be restored is named with its error, and the others
are still restored."""
    withdrawal = {'restored': [], 'unchanged': [], 'unrestored': {}}
    for path, before, after in plan:
        name = str(path.relative_to(ROOT))
        try:
            if before is None:
                present = path.exists()
                path.unlink(missing_ok=True)
            else:
                present = path.read_text() != before
                if present:
                    path.write_text(before)
            withdrawal['restored' if present else 'unchanged'].append(name)
        except Exception as error:
            withdrawal['unrestored'][name] = type(error).__name__ + ': ' + str(error)
    return withdrawal



def recipe_costs(summary):
    """Measured seconds of every executed recipe beside the seconds of its retained execution."""
    rows = {}
    for recipe, result in summary.get('recipes', {}).items():
        if result.get('status') != 'accepted':
            continue
        verified = ROOT / 'validation/reconstruction' / (recipe + '-verified.json')
        retained = json.loads(verified.read_text()) if verified.is_file() else {}
        rows[recipe] = {'seconds': result['seconds'],
                        'retained_seconds': round(sum(s.get('seconds', 0) for s in retained.get('steps', [])), 2)}
    return rows


def adoptable(summary):
    """The route through which a judged answer is adoptable, if any."""
    summary = summary or {}
    if not summary.get('published'):
        return None
    if summary.get('accepted'):
        return 'request'
    if summary.get('repaired') and summary.get('extension'):
        return 'repaired request'
    return None


def adopt(args):
    record_path = args.record.resolve()
    record = json.loads(record_path.read_text())
    answer = record['answer']
    route = adoptable(record['summary']) if record['status'] == 'judged' else None
    assert route is not None, 'Only an accepted or a repaired and accepted answer is adopted.'
    assert answer['request']['state'] == 'refinement_layer', 'Only answers of the refinement layer are adoptable.'
    evidence = development_answer.adoption_evidence(answer, ROOT)
    assert not evidence['present'], ('The answer is already adopted.' if evidence['holds'] else
                                     'A theory of the answer\'s name obstructs the adoption: '
                                     + ', '.join(evidence['obstruction']) + ' fails.')
    record_name = str(record_path.relative_to(ROOT.resolve()))
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh adoption directory.'
    output.mkdir(parents=True)
    name = development_answer.answer_name(answer)
    retained = ROOT / development_answer.ADOPTIONS / (name + '.json')
    receipt = {'status': 'refused', 'answer_digest': development_answer.answer_digest(answer), 'record': record_name,
               'record_sha256': investigate.file_hash(record_path), 'theory': name, 'route': route,
               'control': args.control, 'steps': {}}
    # One cleanup path: every exit after this point reaches the handler below, which withdraws whatever
    # `plan` names and writes the receipt. The plan is read before installation's first write.
    # Termination signals take the same path (build.interruption_signals with a state): raised once while
    # the adoption runs, deferred while it cleans up, and delivered again once the handlers are restored.
    state = {'raising': False, 'received': []}
    signals = contextlib.ExitStack()
    signals.enter_context(build.interruption_signals(state))
    plan, raised, unwritten = None, None, None
    try:
        state['raising'] = True
        if state['received']:
            state['raising'] = False
            raise build.RunInterrupted(state['received'][0])
        receipt['revision'] = revision()
        answer_file = output / 'answer.json'
        answer_file.write_text(json.dumps(answer, indent=1) + '\n')
        before = judge(answer_file, output / 'before', args.timeout)
        receipt['steps']['precondition'] = {k: before.get(k) for k in ('status', 'accepted', 'verdict_word',
                                                                       'publication_word', 'summary', 'frame_sha256',
                                                                       'seconds', 'error')}
        assert before['status'] == 'judged' and adoptable(before.get('summary')) == route, \
            'The answer is no longer accepted through the retained route.'
        assert before['verdict_word'] == record['verdict_word'], \
            'The verdict changed since the answer was retained: it is a re-evaluation, not an adoption.'
        assert before.get('publication_word') == record.get('publication_word'), \
            'The publication changed since the answer was retained: it is a re-evaluation, not an adoption.'
        frame = before.get('frame_sha256')
        assert frame, 'The judgment retained no frame digest.'
        receipt['frame_sha256'] = frame
        plan = prepare(answer, output / 'before', frame)
        receipt['steps']['installation'] = install(answer, plan, frame)
        started = time.monotonic()
        code = subprocess.run([sys.executable, '-B', str(TOOLS / 'incremental_check.py'), 'check', '--output',
                               str(output / 'check'), '--jobs', '8', '--threads', '16'],
                              cwd=ROOT, capture_output=True, text=True).returncode
        summary = json.loads((output / 'check' / 'incremental.json').read_text())
        receipt['steps']['check'] = {'exit_code': code, 'status': summary['status'], 'error': summary.get('error'),
                                     'seconds': round(time.monotonic() - started, 2), 'phases': summary.get('phases'),
                                     'rebuilt_theories': len(summary.get('rebuilt_theories', [])),
                                     'recipes': {status: sorted(n for n, r in summary.get('recipes', {}).items()
                                                                if r['status'] == status)
                                                 for status in ('accepted', 'reused', 'unchanged', 'failed')},
                                     'costs': recipe_costs(summary)}
        assert code == 0 and summary['status'] == 'accepted', 'A report word changed or the check failed.'
        # The evidence with the receipt about to be retained; a control is established as an adoption is,
        # and its retained `control` and `withdrawn` keep it from ever establishing one.
        found = development_answer.adoption_evidence(answer, ROOT,
                                                     receipt={**receipt, 'status': 'adopted', 'control': False})
        receipt['steps']['evidence'] = {k: found[k] for k in ('holds', 'obstruction', 'connections', 'unverified')}
        assert found['holds'], 'The adoption\'s evidence fails: ' + ', '.join(found['obstruction']) + '.'
        context = summary.get('accepted_proof_context')
        recorded = context_sources(context).get(name)
        receipt['steps']['context'] = {'accepted_proof_context': context, 'recorded_sha256': recorded}
        assert recorded == frame, 'The check\'s accepted context does not record the installed theory at its frame digest.'
        receipt['status'] = 'adopted'
        if not args.control:
            text = retained_text(receipt)
            plan.append((retained, None, text))
            retained.parent.mkdir(parents=True, exist_ok=True)
            retained.write_text(text)
        state['raising'] = False
    except BaseException as error:
        state['raising'] = False
        raised = error
        receipt['status'] = 'refused'
        receipt['error'] = str(error) or type(error).__name__
        receipt['error_type'] = type(error).__name__
    try:
        if plan is not None and (raised is not None or args.control):
            withdrawal = withdraw(plan)
            receipt['withdrawal'] = withdrawal
            if not withdrawal['unrestored']:
                receipt['withdrawn'] = True
        try:
            write_json(output / 'receipt.json', receipt)
            if raised is None and args.control and receipt.get('withdrawn'):
                retained.parent.mkdir(parents=True, exist_ok=True)
                retained.write_text(retained_text(receipt))
        except Exception as error:
            unwritten = error
            print('The receipt could not be written (' + type(error).__name__ + ': ' + str(error) + '): '
                  + json.dumps(receipt, default=str), file=sys.stderr)
    finally:
        received, state['received'] = list(state['received']), []
        signals.close()
    print(json.dumps({k: receipt[k] for k in ('status', 'theory', 'error', 'withdrawn') if k in receipt}), flush=True)
    unrestored = (receipt.get('withdrawal') or {}).get('unrestored')
    if unrestored:
        print('The withdrawal could not restore ' + ', '.join(sorted(unrestored)), file=sys.stderr, flush=True)
    redeliver(received)
    if unwritten is not None:
        raise unwritten from raised
    if unrestored:
        raise OSError('The withdrawal could not restore ' + ', '.join(sorted(unrestored))) from raised
    if raised is not None and not isinstance(raised, (AssertionError, OSError, ValueError, KeyError,
                                                      build.RunInterrupted)):
        raise raised
    return 0 if receipt['status'] == 'adopted' else 1


def main():
    if not __debug__:
        raise ValueError('Adoption requires Python assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True, help='A retained judged answer record.')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--control', action='store_true',
                        help='Withdraw the adoption after it is established: the answer is a control of the process.')
    return adopt(parser.parse_args())


if __name__ == '__main__':
    raise SystemExit(main())
