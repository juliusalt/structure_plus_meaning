#!/usr/bin/env python3
"""Reconstruct the retained answers to development requests and compare their verdicts.

Every record in validation/development-answers retains an executor's answer and the outcome the
harness gave it on an accepted base. Replaying runs the harness again on each retained answer
against the current base and compares the outcome and the presented verdict word with the record.
An equal word reconstructs the retained evidence; a different word means that the requested state
or the verdict changed since the record was made, and the answer is a re-evaluation for the
process, not a failure of the replay. The replay moves bytes and compares digests only.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RECORDS = ROOT / 'validation' / 'development-answers'


def replay(record_path, output, timeout):
    record = json.loads(record_path.read_text())
    directory = output / record_path.stem
    directory.mkdir(parents=True)
    answer = directory / 'answer.json'
    answer.write_text(json.dumps(record['answer'], indent=1) + '\n')
    completed = subprocess.run([sys.executable, '-B', str(ROOT / 'tools' / 'development_answer.py'), 'answer',
                                '--answer', str(answer), '--output', str(directory / 'run'), '--timeout', str(timeout)],
                               cwd=ROOT, capture_output=True, text=True, timeout=timeout + 300)
    observed = json.loads((directory / 'run' / 'answer.json').read_text()) if (directory / 'run' / 'answer.json').is_file() \
        else {'status': 'failed', 'error': completed.stdout[-2000:] + completed.stderr[-2000:]}
    same_status = observed['status'] == record['status']
    same_word = observed.get('verdict_word') == record.get('verdict_word')
    return record_path.stem, {'status': observed['status'], 'expected_status': record['status'],
                              'verdict_word': observed.get('verdict_word'),
                              'expected_verdict_word': record.get('verdict_word'),
                              'reconstructed': same_status and same_word}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--keep', action='store_true', help='Keep the replayed runs instead of removing them.')
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists(), 'Use a fresh replay directory.'
    output.mkdir(parents=True)
    records = sorted(RECORDS.glob('*.json'))
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        results = dict(pool.map(lambda path: replay(path, output, args.timeout), records))
    report = {'replayed': len(results), 'reconstructed': sum(r['reconstructed'] for r in results.values()),
              'answers': results}
    (output / 'replay.json').write_text(json.dumps(report, indent=1, sort_keys=True) + '\n')
    if not args.keep:
        for name in results:
            shutil.rmtree(output / name, ignore_errors=True)
    print(json.dumps({'replayed': report['replayed'], 'reconstructed': report['reconstructed'],
                      'differing': sorted(n for n, r in results.items() if not r['reconstructed'])}))
    return 0 if report['reconstructed'] == report['replayed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
