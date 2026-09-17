"""Execute a complete native packet through its original registered subject contract."""
from pathlib import Path
import argparse
import json

import compressed_native_execution
import execution_support as investigate
import native_packet_reports
import observation_contracts


def main(entrypoint, *, root, theory, definition, prefix, selections, program,
         question, boundary):
    parser = argparse.ArgumentParser(description=question)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']), theory, definition,
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    result = compressed_native_execution.checked_execution(args.proof, args.poly, args.output,
        required_theories=[root],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': selections},
        input_paths=[Path(entrypoint), *(Path(c['path']) for c in contracts)],
        program=program, assess=lambda inputs, path: native_packet_reports.assess(inputs, path, prefix=prefix),
        project=args.project.resolve(), timeout=7200, question=question, boundary=boundary)
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}), flush=True)
    return int(result['status'] != 'accepted')
