#!/usr/bin/env python3
"""Run declared decisions, follow exact revisions, and check mandatory criteria.

Candidate construction and interpretation remain external. This adapter reuses
existing comparison review, revision and execution operations without supplying
new decision semantics. A selected proposal still needs its stated validation.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
import re
import subprocess
import sys

import compare_reasoning_methods as compare
import investigate
from revise_investigation_case import revised_case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--specification', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Decision execution requires Python assertions.')
    specification = args.specification.resolve()
    spec = json.loads(specification.read_text())
    assert spec['question'] and spec['boundary'] and spec['problems']
    names = [p['name'] for p in spec['problems']]
    assert len(set(names)) == len(names)
    assert all(re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', n) for n in names)
    for problem in spec['problems']:
        investigate.validate_case(problem['case'])
        assert problem['case']['kind'] == 'basis'
        assert all(isinstance(f, int) and isinstance(w, int) and f in problem['case']['facets']
                   for f, w in problem['required_observations'])
    assert not args.output.exists(), 'Retain the preceding results and use a new directory.'
    args.output.mkdir(parents=True)
    dependencies = [{'path': str(p), 'sha256': investigate.file_hash(p)}
                    for p in [specification, Path(__file__).resolve()]]
    results = []
    for problem in spec['problems']:
        directory = args.output / problem['name']
        directory.mkdir()
        case = copy.deepcopy(problem['case'])
        case.setdefault('evidence', []).extend(dependencies)
        for stage in ['initial', 'followed']:
            if stage == 'followed':
                case = revised_case(directory / 'initial/receipt.json')
            case_path = directory / (stage + '-case.json')
            case_path.write_text(json.dumps(case, indent=2) + '\n')
            command = [sys.executable, str(Path(investigate.__file__).resolve()),
                       '--output', str(directory / stage), 'run', str(case_path)]
            with (directory / (stage + '-command.log')).open('w') as log:
                status = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode
            if status:
                print(f'{problem["name"]}/{stage}: exit {status}; see {directory}', flush=True)
                return status
        receipt_path = directory / 'followed/receipt.json'
        receipt = json.loads(receipt_path.read_text())
        assessment = compare.assess_candidates(case, receipt['result'], problem['required_observations'])
        assessment['receipt_sha256'] = investigate.file_hash(receipt_path)
        (directory / 'assessment.json').write_text(json.dumps(assessment, indent=2) + '\n')
        before = json.loads((directory / 'initial/receipt.json').read_text())['result']
        results.append({'problem': problem['name'], 'initial_result': before,
                        'followed_result': receipt['result'], 'assessment': assessment})
        print(json.dumps({'problem': problem['name'], 'initial_residual': before['residual'],
                          'returned_selection': before['revision']['selection'],
                          'followed_residual': receipt['result']['residual'],
                          'eligible': assessment['eligible'], 'dominant': assessment['dominant']}), flush=True)
    (args.output / 'complete-results.json').write_text(json.dumps({
        'question': spec['question'], 'boundary': spec['boundary'],
        'specification_sha256': investigate.file_hash(specification), 'results': results}, indent=2) + '\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
