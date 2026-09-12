#!/usr/bin/env python3
"""Execute complete fixed-investigation families from one proved code module."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import investigate
from check_reasoning import clone_json
import observation_contracts
import proved_code
import review_investigations as review


def program(engine, cases, contracts):
    parts = []
    for i, case in enumerate(cases):
        investigate.validate_case(case)
        assert case['kind'] in investigate.BUILTIN_CASES
        source = investigate.runtime_program(case, engine, contracts[case['kind']])
        assert source.count('"INVESTIGATION_RESULT "') == 1
        if i:
            source = source.partition('\n')[2]
        parts.append(source.replace('"INVESTIGATION_RESULT "', '"INDEXED_INVESTIGATION ' + str(i) + ' "'))
    return '\n'.join(parts)


def assess(cases, raw, before=None, contracts=None):
    seen, results = set(), []
    for line in raw.splitlines():
        if not line.startswith('INDEXED_INVESTIGATION '):
            continue
        identifier, encoded = line.removeprefix('INDEXED_INVESTIGATION ').split(' ', 1)
        i = int(identifier)
        assert 0 <= i < len(cases) and i not in seen
        seen.add(i)
        case = cases[i]
        result = json.loads(encoded)
        investigate.validate_result(result, case['kind'])
        if contracts is not None:
            contract = contracts[case['kind']]
            assert {p['candidate'] for p in result['profiles']} == set(contract['candidate_indices'])
            assert all(f in contract['facet_indices'] for f, c, w in result['observations'])
        mismatches, fields, facts = review.basis_analysis(case, result, case['scope'])
        assert not mismatches, (i, case['kind'], mismatches)
        results.append({'index':i, 'case':case, 'result':result, 'checked_fields':fields, 'facts':facts})
    assert seen == set(range(len(cases)))
    results.sort(key=lambda row:row['index'])
    results = clone_json(results)
    if before is not None:
        assert results == before['results'], 'The complete original cases, reports or assessments differ.'
    return {'checked_cases':len(cases), 'results':results,
            'formal_subject_contracts':contracts,
            'original_complete_result_equality':None if before is None else True,
            'boundary':'Actual proved fixed operations produce every observation and comparison. Complete finite-table reconstruction checks every returned field. This does not establish a registry description or infer arbitrary native truth from samples.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof', type=Path, required=True)
    parser.add_argument('--theory', required=True)
    parser.add_argument('--specification', type=Path, required=True)
    parser.add_argument('--poly', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--before', type=Path)
    args = parser.parse_args()
    spec = json.loads(args.specification.read_text())
    before = None
    dependencies = [Path(__file__), args.specification]
    proof, _, _ = proved_code.proved_export(args.proof, required_theories=[args.theory])
    contracts = {}
    for kind in sorted({case['kind'] for case in spec['cases']}):
        descriptor = investigate.BUILTIN_CASES[kind]
        assert descriptor['theory'] in proof['sources']
        artifacts = [row for row in proof['subject_contracts']
                     if Path(row['path']).name == descriptor['function'] + '.yxml']
        assert len(artifacts) == 1, (kind, 'Missing or ambiguous formal subject contract.')
        artifact = artifacts[0]
        path = Path(artifact['path'])
        assert investigate.file_hash(path) == artifact['sha256']
        contracts[kind] = observation_contracts.read_contract(path, descriptor['theory'], descriptor['function'])
        dependencies.append(path)
    if args.before is not None:
        receipt = json.loads((args.before/'receipt.json').read_text())
        assert receipt['status'] == 'accepted'
        assert json.loads((args.before/'cases.json').read_text()) == spec['cases']
        before_path = args.before/'complete-results.json'
        before = json.loads(before_path.read_text())
        assert before == receipt['assessment']
        dependencies.extend([before_path,args.before/'receipt.json',args.before/'cases.json'])
    receipt = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=[args.theory], inputs=spec['cases'], input_paths=dependencies,
        program=lambda engine,cases:program(engine,cases,contracts),
        assess=lambda cases,raw:assess(cases,raw,before,contracts),
        question=spec['question'], boundary=spec['boundary'])
    print(json.dumps({k:v for k,v in receipt.items() if k in ['status','error','exit_code','results_sha256']},indent=2))
    if receipt['status'] == 'accepted':
        print(json.dumps({'checked_cases':receipt['assessment']['checked_cases'],
            'original_complete_result_equality':receipt['assessment']['original_complete_result_equality']}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
