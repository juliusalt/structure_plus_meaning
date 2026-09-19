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

An adopted answer, whose theory is a theory of the repository, is judged by the harness as the published
state's unchanged answer. Its record is the judgment that admitted it before it was adopted, which the
harness no longer frames; that record is historical evidence of the admission and is never re-recorded.
The replay reports its present judgment beside the record and does not count it as a reconstruction.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import subprocess
import sys

import development_answer

ROOT = Path(__file__).resolve().parents[1]
RECORDS = ROOT / 'validation' / 'development-answers'


def replay(record_path, output, timeout, rerecord=False):
    record = json.loads(record_path.read_text())
    adopted = development_answer.adopted(record['answer'])
    directory = output / record_path.stem
    directory.mkdir(parents=True)
    answer = directory / 'answer.json'
    answer.write_text(json.dumps(record['answer'], indent=1) + '\n')
    completed = subprocess.run([sys.executable, '-B', str(ROOT / 'tools' / 'development_answer.py'), 'answer',
                                '--answer', str(answer), '--output', str(directory / 'run'), '--timeout', str(timeout),
                                '--retain', str(directory / 'retained.json')],
                               cwd=ROOT, capture_output=True, text=True, timeout=timeout + 300)
    observed = json.loads((directory / 'run' / 'answer.json').read_text()) if (directory / 'run' / 'answer.json').is_file() \
        else {'status': 'failed', 'error': completed.stdout[-2000:] + completed.stderr[-2000:]}
    same_status = observed['status'] == record['status']
    same_word = all(observed.get(word) == record.get(word) for word in ('verdict_word', 'publication_word'))
    if rerecord and same_status and not same_word and observed['status'] == 'judged' and not adopted:
        retained = json.loads((directory / 'retained.json').read_text())
        record_path.write_text(json.dumps({**record, **retained}, indent=1) + '\n')
    return record_path.stem, {'status': observed['status'], 'expected_status': record['status'],
                              'verdict_word': observed.get('verdict_word'),
                              'expected_verdict_word': record.get('verdict_word'),
                              'publication_word': observed.get('publication_word'),
                              'expected_publication_word': record.get('publication_word'),
                              'adopted': adopted, 'reconstructed': same_status and same_word and not adopted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--keep', action='store_true', help='Keep the replayed runs instead of removing them.')
    parser.add_argument('--rerecord', action='store_true', help='Retain again every judged answer whose word differs.')
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh replay directory.'
    output.mkdir(parents=True)
    records = sorted(RECORDS.glob('*.json'))
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = dict(pool.map(lambda path: replay(path, output, args.timeout, args.rerecord), records))
    report = {'replayed': len(results), 'reconstructed': sum(r['reconstructed'] for r in results.values()),
              'adopted': sorted(n for n, r in results.items() if r['adopted']), 'answers': results}
    (output / 'replay.json').write_text(json.dumps(report, indent=1, sort_keys=True) + '\n')
    if not args.keep:
        for name in results:
            shutil.rmtree(output / name, ignore_errors=True)
    differing = sorted(n for n, r in results.items() if not r['reconstructed'] and not r['adopted'])
    print(json.dumps({'replayed': report['replayed'], 'reconstructed': report['reconstructed'],
                      'adopted': report['adopted'], 'differing': differing}))
    return 0 if not differing else 1


if __name__ == '__main__':
    raise SystemExit(main())
