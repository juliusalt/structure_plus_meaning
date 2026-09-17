"""Execute complete native certificate placement, actual calls and retained replay."""
from pathlib import Path
import argparse
import json

import check_native_certificates as shared
import execution_support as investigate
import machine_reports
import native_replay_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Native_Certificate_Replay_Execution', 'native_replay_indices')
    code += shared.native_graph_json.prelude('jsite') + shared.investigation_json.CYCLE
    code += native_replay_json.PRELUDE + r'''fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jcellResult (x,(reference,(result,a))) = "{\"subject\":" ^ jsubject x ^
  ",\"reference\":" ^ jreference reference ^ ",\"result\":" ^ jresult result ^ "}";
fun jcellAssessment (x,(reference,(result,a))) = "{\"subject\":" ^ jsubject x ^
  ",\"assessment\":" ^ jassessment a ^ ",\"qualities\":" ^ jlist jquality
    (map (fn f => (f,N.native_replay_inspect a f)) facets) ^ "}";
fun jcandidate (m,rows) = "{\"method\":" ^ jnat m ^ ",\"results\":" ^ jf jcellResult rows ^ "}";
fun jassessed (m,rows) = "{\"method\":" ^ jnat m ^ ",\"assessments\":" ^ jf jcellAssessment rows ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_replay_family_inspect rows f)) facets) ^ "}";
val () = print ("REPLAY_SCOPE " ^ jlist jnat N.native_replay_indices ^ "\n");
val (table,(comparison,cycles)) = N.native_replay_packet scope selections;
val () = List.app (fn (w,(xs,cells)) => print ("REPLAY_SUBJECT " ^ jnat w ^
  " {\"inputs\":" ^ jf jsubject xs ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n")) table;
val () = List.app (fn (w,(xs,cells)) => print ("REPLAY_ASSESSMENT " ^ jnat w ^ " " ^ jlist jassessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("REPLAY_COMPARISON {\"scope\":" ^ jlist jnat scope ^ ",\"observations\":" ^ jlist jtriple rows ^
  ",\"relation\":" ^ jlist jpair relation ^ ",\"selected_methods\":" ^ jlist jnat selected ^
  ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("REPLAY_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Native_Replay_Investigation', 'native_replay_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path, deferred=True))
        assert reports and reports[0]['tag'] == 'REPLAY_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'REPLAY_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'REPLAY_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'REPLAY_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'REPLAY_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every complete source and supplied certificate, candidate environment, full '
                            'correspondence and graph, actual application, least retained environment, all '
                            'native reader results, individual and family assessments, comparisons and '
                            'revision reasons are retained. The host checks reproduction only.'}

    modules = [shared, native_replay_json, shared.check_reasoning, shared.investigation_json, shared.native_program_json,
               shared.native_history_json, shared.native_graph_json, shared.native_certificate_json,
               shared.program_evaluation_json]
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Certificate_Replay_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1, 2, 5, 7, 9], list(range(10))]},
        input_paths=[Path(__file__), *(Path(m.__file__) for m in modules), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual certificate replay constructors preserve the original complete graph and source, '
                 'construct the actual call, retain exactly its least replay environment, recover every original '
                 'value there, produce closed native replay and refuse unavailable inputs?',
        boundary='Each original subject retains its full native source and supplied certificate. All family '
                 'members, actual result fields and complete native readings determine observations under '
                 'the exact registered contract. Native mathematical-proof admission, complete workflow '
                 'enforcement, arbitrary candidate-language coverage, full physical cost and genesis remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
