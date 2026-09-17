"""Compare a constructed policy check using the actual uniquely quoted replay scope."""
from pathlib import Path
import argparse
import json

import check_digit_history
import compressed_native_execution
import execution_support as investigate
import native_packet_reports
import observation_contracts


def program(engine, inputs):
    code = check_digit_history.program(engine, inputs)
    previous = r'''val () = List.app (fn (w,(context,cells)) => wemit ("DIGIT_HISTORY_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;'''
    replacement = r'''val () = List.app (fn (w,((original,additional),cells)) => (
  wemit ("DIGIT_HISTORY_CONTEXT " ^ jnat w) (fn () => wobject [
    ("\"original_context\"",fn () => wcontext original),
    ("\"additional_results\"",fn () => wlist (wf woutputRow) additional)]);
  List.app (fn (m,result) => wemit ("DIGIT_HISTORY_CANDIDATE " ^ jnat w ^ " " ^ jnat m)
    (fn () => wresult result)) cells)) table;'''
    assert code.count(previous) == 1
    code = code.replace(previous, replacement)
    source_pattern = 'val ((covered,(subjects,(prepared,reference))),cells) = lookup "subject" w table'
    assert code.count(source_pattern) == 1
    code = code.replace(source_pattern,
                        'val (((covered,(subjects,(prepared,reference))),known),cells) = lookup "subject" w table')
    assert code.count('N.digit_history_packet') == 1
    return code.replace('N.digit_history_packet', 'N.quoted_history_packet').replace('DIGIT_HISTORY_', 'QUOTED_HISTORY_')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Quoted_History_Investigation', 'quoted_history_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    result = compressed_native_execution.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Quoted_History_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=lambda inputs, path: native_packet_reports.assess(inputs, path, prefix='QUOTED_HISTORY'),
        project=args.project.resolve(), timeout=7200,
        question='Does construction using the actual uniquely quoted scope preserve every complete '
                 'original history result, while every original omitted-check and state-change control remains visible?',
        boundary='The actual quoted judgment and proved replay constructor establish the complete '
                 'generation scopes and base-cause certification. Original package and policy alignment, '
                 'membership, target readiness, ledger and cache conditions remain. All sixteen original '
                 'subjects and nineteen original methods accompany the refined operation and the actual '
                 'policy-preserving omitted-replay control. Full physical cost, all six workflow conditions, historical permission and '
                 'reachability, native mathematical-proof admission, genesis and final audit remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}), flush=True)
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
