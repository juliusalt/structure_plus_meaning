"""Retain the unchanged complete native replay packet as separate complete records."""
from pathlib import Path
import argparse
import json

import check_digit_replay
import native_packet_reports
import compressed_native_execution
import investigate
import observation_contracts


def program(engine, inputs):
    code = check_digit_replay.program(engine, inputs)
    previous = r'''val () = List.app (fn (w,(context,cells)) => wemit ("DIGIT_REPLAY_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;'''
    replacement = r'''val () = List.app (fn (w,(context,cells)) => (
  wemit ("DIGIT_REPLAY_CONTEXT " ^ jnat w) (fn () => wcontext context);
  List.app (fn (m,assessment) => wemit ("DIGIT_REPLAY_CANDIDATE " ^ jnat w ^ " " ^ jnat m)
    (fn () => wassessment assessment)) cells)) table;'''
    assert code.count(previous) == 1
    return code.replace(previous, replacement)


def assess(inputs, path):
    return native_packet_reports.assess(inputs, path, prefix='DIGIT_REPLAY',
                                       introductory=('SEEDS', 'PREVIOUS_SOURCES'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    parser.add_argument('--timeout', type=int, default=7200)
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Digit_Replay_Investigation', 'digit_replay_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    result = compressed_native_execution.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Digit_Replay_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=args.timeout,
        # Sixteen deep-recursion workers exhaust the compact Poly/ML address space for this packet.
        workers=4,
        question='Which complete persistent digit replay recordings preserve the independently established '
                 'bounded operation and original certified-cause meaning on every original and subsequent input?',
        boundary='The unchanged proved native packet and registered original-subject contracts own every '
                 'observation, comparison and revision. Complete values are retained in separate records '
                 'through verified compression. Full physical cost, all six workflow conditions, historical '
                 'permission and reachability, native mathematical-proof admission, genesis and final audit remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}), flush=True)
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
