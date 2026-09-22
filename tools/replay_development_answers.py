#!/usr/bin/env python3
"""Reconstruct the retained answers to development requests and compare their verdicts.

Every record in validation/development-answers retains an executor's answer and the outcome the
harness gave it on an accepted base. Replaying runs the harness again on each retained answer
against the current base and compares the outcome and the presented words with the record: the
verdict word (the verdict and repair) and the publication word (the certified generations and the
transaction that publishes an admitted answer over its incumbent). Equal words reconstruct the
retained evidence; a different word means that the requested state, the verdict or the publication
changed since the record was made, and the answer is a re-evaluation for the process, not a failure
of the replay. The replay moves bytes and compares digests only.

With --rerecord, a judged answer whose word differs is retained again as judged now: the harness writes
the retained record it would write for a new answer, and every field of the old record that the harness
does not write (an executor's or packet's digest) is kept. Re-recording is the re-evaluation made
explicit; it is never applied to an answer whose outcome changed from judged to failed or back.

The replay does not decide adoption: it reads the harness's status. Where a theory of an answer's name
stands in the workspace, the harness judges nothing and reports `adopted`, with the evidence it checked
(`development_answer.adoption_evidence`) and the connection it cannot verify, or `obstructed`, with the
connections that failed. An adopted row keeps that evidence; its record is the judgment that admitted the
answer before its adoption, historical evidence compared with nothing and never re-recorded. An obstructed
row is a condition of the workspace, neither a re-evaluation nor a run that left nothing, and fails the
replay. The replay also checks the converse: every retained adoption receipt that binds an answer has that
answer's judgment among the retained records.

A native answer (a record marked native) is judged again natively by `native_answers.py judge`: its octets
are read by the native reader of the request's state and judged by the verdict of the request's kind, and
the judgment word and summary are compared with the record, as the verdict word of a framed answer is.

An answer whose judgment could not be produced is reported apart from one whose word differs. A run
produces a judgment when the harness leaves its answer, whatever that answer says: a refusal and a
failed build are judgments the harness made, and their words are compared like any other. A run that
left no answer at all, because its Isabelle build never ran, died or outlived its limit, produced
nothing to compare, so it is neither a reconstruction nor a re-evaluation: it is reported as
`unproduced`, with the error the run left, and `differing` holds only words that were compared and
differed. A planner reads a differing word as a re-evaluation of that answer and an unproduced
judgment as a fault of this run alone. A row's own `status` is a third notion, the judgment the
harness made: the retained `failed-proof` record parts them, being a `failed` status that is
reconstructed and not unproduced.

The run's elapsed wall seconds are reported beside the run count on the error stream and in the summary,
so that the observed cost of a replay is readable where its counts are; each answer's own seconds are in
its row of the summary.

The records are replayed longest-first by the seconds their own record kept, so that a long answer is
not left to start last; a record that kept none is replayed last, and none keeps its seconds today.

Every replayed answer runs the answer harness, and each of those runs an Isabelle build, so the worker
count is the number of Isabelle runs the replay holds at once. This machine takes at most two at once,
so the default is two and the documented command stays within that limit as written; the run count the
replay will hold is reported before it begins, so the cost is visible to whatever launches it.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

import development_answer

ROOT = Path(__file__).resolve().parents[1]
RECORDS = ROOT / 'validation' / 'development-answers'
# The machine's limit, one fact about the machine rather than one per tool: heavy Isabelle runs share
# one machine of 60 GiB and the harness refuses a third, so at most two stand at once. Another tool
# that spawns Isabelle imports this name rather than restating the number. One Isabelle build runs per
# worker here, so the worker count is the number of runs held at once, and taking this as the default
# keeps the documented command within the limit as it is written.
ISABELLE_RUN_LIMIT = 2


def run_harness(command, directory, timeout):
    """Run one answer's harness and report what it left, raising nothing at its caller.

    A run that outlives its limit, or never starts, leaves no judgment to compare. Raised through
    the pool that replays the answers, such a failure would abort every other answer's run and
    leave no summary at all, so it is returned here as this run's error and costs its own answer
    alone. The limit the run outlived is named in that error, because raising it is the reader's
    remedy. The elapsed seconds are the run's, failed or not.
    """
    started = time.monotonic()
    try:
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        left = completed.stdout[-2000:] + completed.stderr[-2000:]
    except subprocess.TimeoutExpired as expired:
        # What a stopped run wrote comes back as bytes whatever `text` says, and as None when it wrote nothing.
        written = [stream.decode(errors='replace') if isinstance(stream, bytes) else (stream or '')
                   for stream in (expired.stdout, expired.stderr)]
        left = f'the harness run outlived its {expired.timeout}s limit and was stopped\n' \
               + written[0][-2000:] + written[1][-2000:]
    except (subprocess.SubprocessError, OSError) as failure:
        left = f'the harness run left no judgment: {type(failure).__name__}: {failure}'
    return round(time.monotonic() - started, 1), (directory / 'run' / 'answer.json').is_file(), left


def unproduced_observation(left):
    """The row of a run that left no judgment: no harness status, since the harness made none, and its error."""
    return {'status': None, 'error': left}


def replay_native(record_path, record, output, timeout, rerecord=False):
    directory = output / record_path.stem
    directory.mkdir(parents=True)
    answer = directory / 'answer.json'
    answer.write_text(json.dumps(record['answer'], indent=1) + '\n')
    elapsed, produced, left = run_harness(
        [sys.executable, '-B', str(ROOT / 'tools' / 'native_answers.py'), 'judge',
         '--answer', str(answer), '--output', str(directory / 'run'), '--timeout', str(timeout),
         '--retain', str(directory / 'retained.json')], directory, timeout + 300)
    observed = json.loads((directory / 'run' / 'answer.json').read_text()) if produced \
        else unproduced_observation(left)
    same = produced and observed['status'] == record['status'] and all(observed.get(k) == record.get(k)
                                                                      for k in ('judgment_word', 'summary'))
    if rerecord and not same and produced and observed['status'] == record['status'] == 'judged':
        retained = json.loads((directory / 'retained.json').read_text())
        record_path.write_text(json.dumps({**record, **retained}, indent=1) + '\n')
    return record_path.stem, {'status': observed['status'], 'expected_status': record['status'],
                              'judgment_word': observed.get('judgment_word'),
                              'expected_judgment_word': record.get('judgment_word'),
                              'summary': observed.get('summary'), 'expected_summary': record.get('summary'),
                              'error': observed.get('error'), 'produced': produced,
                              'elapsed_seconds': elapsed, 'reconstructed': same}


def replay(record_path, output, timeout, rerecord=False):
    record = json.loads(record_path.read_text())
    if record.get('native'):
        return replay_native(record_path, record, output, timeout, rerecord)
    directory = output / record_path.stem
    directory.mkdir(parents=True)
    answer = directory / 'answer.json'
    answer.write_text(json.dumps(record['answer'], indent=1) + '\n')
    elapsed, produced, left = run_harness(
        [sys.executable, '-B', str(ROOT / 'tools' / 'development_answer.py'), 'answer',
         '--answer', str(answer), '--output', str(directory / 'run'), '--timeout', str(timeout),
         '--retain', str(directory / 'retained.json')], directory, timeout + 300)
    observed = json.loads((directory / 'run' / 'answer.json').read_text()) if produced \
        else unproduced_observation(left)
    judged = observed['status'] not in ('adopted', 'obstructed')
    same_status = produced and observed['status'] == record['status']
    same_word = all(observed.get(word) == record.get(word) for word in ('verdict_word', 'publication_word', 'refusal', 'error'))
    if rerecord and produced and same_status and not same_word and observed['status'] in ('judged', 'refused'):
        retained = json.loads((directory / 'retained.json').read_text())
        record_path.write_text(json.dumps({**record, **retained}, indent=1) + '\n')
    evidence = {} if judged else {'evidence': observed.get('evidence'), 'unverified': observed.get('unverified'),
                                  'obstruction': observed.get('obstruction')}
    return record_path.stem, {'status': observed['status'], 'expected_status': record['status'], **evidence,
                              'verdict_word': observed.get('verdict_word'),
                              'expected_verdict_word': record.get('verdict_word'),
                              'publication_word': observed.get('publication_word'),
                              'expected_publication_word': record.get('publication_word'),
                              'refusal': observed.get('refusal'), 'expected_refusal': record.get('refusal'),
                              'error': observed.get('error'), 'expected_error': record.get('error'),
                              'produced': produced, 'elapsed_seconds': elapsed,
                              'reconstructed': produced and judged and same_status and same_word}


def unrecorded_adoptions(records=RECORDS, project=ROOT):
    """The adoption receipts binding an answer whose judgment no retained record holds."""
    recorded = {development_answer.answer_digest(json.loads(path.read_text())['answer'])
                for path in records.glob('*.json')}
    return sorted(file for file, receipt in development_answer.adoption_receipts(project).items()
                  if receipt.get('status') == 'adopted' and receipt.get('control') is False
                  and 'withdrawn' not in receipt and receipt.get('answer_sha256') not in recorded)


def retained_seconds(record_path):
    """The seconds a record kept of the run that judged it, and none as none rather than as short."""
    try:
        return float(json.loads(record_path.read_text()).get('elapsed_seconds') or 0.0)
    except (OSError, ValueError, TypeError):
        return 0.0


def replay_order(records):
    """The records longest-first, by the seconds their own retained record kept.

    Every replayed answer holds an Isabelle build of its own, so a replay lasts until its longest
    answer ends, and starting the longest answers first is what lets the shorter ones fill the
    workers behind them. A record that kept no seconds is placed last, its length being unknown
    rather than short, and the sort is stable, so records of equal seconds keep the order they
    came in. No retained record keeps its seconds today, the harness retaining the boundary of a
    judgment and not its cost, so this order is the records' own until one does.
    """
    return sorted(records, key=retained_seconds, reverse=True)


def answer_groups(results):
    """The groups a replay's answers fall into, each named for the notion that parts it from the rest.

    `unproduced` holds the answers whose run left no judgment, which is exactly the decider
    `produced` of their rows: nothing was compared, so they are neither a reconstruction nor a
    re-evaluation. `adopted` and `obstructed` are the harness's own status where a theory of the
    answer's name stands: the harness judged nothing, and its evidence held or failed. `differing`
    holds only judgments whose words were compared and differed, which a planner reads as a
    re-evaluation of that answer. An answer whose status is `failed` was judged, and is unproduced
    only when this run left no judgment at all.
    """
    produced = {name: row for name, row in results.items() if row['produced']}
    return {'adopted': sorted(name for name, row in produced.items() if row['status'] == 'adopted'),
            'obstructed': sorted(name for name, row in produced.items() if row['status'] == 'obstructed'),
            'differing': sorted(name for name, row in produced.items()
                                if row['status'] not in ('adopted', 'obstructed') and not row['reconstructed']),
            'unproduced': sorted(name for name, row in results.items() if not row['produced'])}


def replay_exit(groups, unrecorded):
    """A replay passes exactly when nothing differed, was unproduced or obstructed, and every adoption is recorded."""
    return 0 if not (groups['differing'] or groups['unproduced'] or groups['obstructed'] or unrecorded) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=ISABELLE_RUN_LIMIT,
                        help=f'Answers replayed at once, each holding one Isabelle build for its run. This '
                             f'machine takes at most {ISABELLE_RUN_LIMIT} Isabelle runs at once, so the default '
                             f'is {ISABELLE_RUN_LIMIT} and the command stays within the limit as written; lower '
                             f'it to 1 beside another run, and raise it only on a machine known to be free.')
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--keep', action='store_true', help='Keep the replayed runs instead of removing them.')
    parser.add_argument('--rerecord', action='store_true',
                        help='Retain again every judged or refused answer whose word differs; never an adopted or obstructed one.')
    args = parser.parse_args()
    if args.workers > ISABELLE_RUN_LIMIT:
        print(f"replay holds {args.workers} Isabelle runs at once, above this machine's limit of "
              f'{ISABELLE_RUN_LIMIT}; runs beside it may be refused for want of memory', file=sys.stderr)
    else:
        print(f'replay holds {args.workers} Isabelle run(s) at once', file=sys.stderr)
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh replay directory.'
    output.mkdir(parents=True)
    records = replay_order(sorted(RECORDS.glob('*.json')))
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = dict(pool.map(lambda path: replay(path, output, args.timeout, args.rerecord), records))
    elapsed = round(time.monotonic() - started, 1)
    groups = answer_groups(results)
    unrecorded = unrecorded_adoptions()
    report = {'replayed': len(results), 'reconstructed': sum(r['reconstructed'] for r in results.values()),
              **groups, 'unrecorded_adoptions': unrecorded, 'elapsed_seconds': elapsed, 'answers': results}
    (output / 'replay.json').write_text(json.dumps(report, indent=1, sort_keys=True) + '\n')
    if not args.keep:
        for name in results:
            shutil.rmtree(output / name, ignore_errors=True)
    print(f'replay held {args.workers} Isabelle run(s) at once and took {elapsed}s', file=sys.stderr)
    print(json.dumps({'replayed': report['replayed'], 'reconstructed': report['reconstructed'],
                      **groups, 'unrecorded_adoptions': unrecorded, 'elapsed_seconds': elapsed}))
    return replay_exit(groups, unrecorded)


if __name__ == '__main__':
    raise SystemExit(main())
