"""Execute complete original-requirement decisions and their native replay families."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_native_certificates as shared
import investigate
import machine_reports
import requirement_decision_json
import native_replay_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Decision_Replay_Execution', 'requirement_decision_indices')
    code += shared.native_graph_json.prelude('jsite') + admission_goal_json.PRELUDE + shared.investigation_json.CYCLE
    code += "structure Decision_JSON = struct\n" + requirement_decision_json.PRELUDE + "\nend;\n"
    code += "structure Replay_JSON = struct\n" + native_replay_json.PRELUDE + "\nend;\n"
    code += r'''fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jreplayRow (certificate,result) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"result\":" ^ Replay_JSON.jresult result ^ "}";
fun jresult NONE = "null"
  | jresult (SOME (decision,replays)) = "{\"decision\":" ^ Decision_JSON.jresult decision ^
      ",\"replays\":" ^ jf jreplayRow replays ^ "}";
fun jinspection ((certificate,result),(subject,(reference,assessment))) =
  "{\"certificate\":" ^ jcertificate certificate ^ ",\"result\":" ^ Replay_JSON.jresult result ^
  ",\"subject\":" ^ Replay_JSON.jsubject subject ^ ",\"reference\":" ^ Replay_JSON.jreference reference ^
  ",\"assessment\":" ^ Replay_JSON.jassessment assessment ^ ",\"qualities\":" ^ jlist jquality
    (map (fn f => (f,N.decision_replay_row_inspect (subject,(reference,assessment)) f))
      (map N.nat_of_integer [0,1,2,3,4,5,6,7,8,9])) ^ "}";
fun jfamily (expected,(complete,rows)) = "{\"expected_certificates\":" ^ jf jcertificate expected ^
  ",\"complete_functional_family\":" ^ Bool.toString complete ^ ",\"inspections\":" ^ jf jinspection rows ^ "}";
fun jassessment (decision,family) = "{\"decision\":" ^ Decision_JSON.jassessment decision ^
  ",\"replay_family\":" ^ Decision_JSON.jo jfamily family ^ "}";
fun jbase (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jcontext (x,((reference,original),bases)) = "{\"subject\":" ^ Decision_JSON.jsubject x ^
  ",\"reference\":" ^ Decision_JSON.jo Decision_JSON.jreference reference ^
  ",\"original\":" ^ Decision_JSON.joriginal original ^ ",\"bases\":" ^ jlist jbase bases ^ "}";
fun jcell (x,(reference,(result,a))) = "{\"subject\":" ^ Decision_JSON.jsubject x ^
  ",\"reference\":" ^ Decision_JSON.jo Decision_JSON.jreference reference ^ ",\"result\":" ^ jresult result ^ "}";
fun jcellAssessment (x,(reference,(result,a))) = jassessment a;
fun jcandidate (m,cell) = "{\"method\":" ^ jnat m ^ ",\"cell\":" ^ Decision_JSON.jo jcell cell ^ "}";
fun jassessed (m,cell) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ Decision_JSON.jo jcellAssessment cell ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.decision_replay_cell_inspect cell f)) facets) ^ "}";
val () = print ("DECISION_REPLAY_SCOPE " ^ jlist jnat N.requirement_decision_indices ^ "\n");
val (table,(comparison,cycles)) = N.decision_replay_packet scope selections;
val () = List.app (fn (w,(context,cells)) => print ("DECISION_REPLAY_SUBJECT " ^ jnat w ^
  " {\"context\":" ^ Decision_JSON.jo jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n")) table;
val () = List.app (fn (w,(context,cells)) => print ("DECISION_REPLAY_ASSESSMENT " ^ jnat w ^ " " ^ jlist jassessed cells ^ "\n")) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("DECISION_REPLAY_COMPARISON {\"scope\":" ^ jlist jnat scope ^ ",\"observations\":" ^ jlist jtriple rows ^
  ",\"relation\":" ^ jlist jpair relation ^ ",\"selected_methods\":" ^ jlist jnat selected ^
  ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("DECISION_REPLAY_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'Factor_Decision_Replay_Investigation', 'decision_replay_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'DECISION_REPLAY_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'DECISION_REPLAY_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'DECISION_REPLAY_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'DECISION_REPLAY_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'DECISION_REPLAY_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original requirements and sources, all original and target evaluation '
                            'conditions, applications, rules and answers, constructed candidate environments, '
                            'all certificates and independent proof checks, admitted terms, every native replay field and comparison '
                            'reasons remain actual native outputs. The host checks reproduction only.'}

    modules = [shared, requirement_decision_json, native_replay_json, admission_goal_json, shared.check_reasoning, shared.investigation_json,
               shared.native_program_json, shared.native_history_json, shared.native_graph_json,
               shared.native_certificate_json, shared.program_evaluation_json]
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Decision_Replay_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1, 2, 3, 4, 5, 6, 7, 17], list(range(19))]},
        input_paths=[Path(__file__), *(Path(m.__file__) for m in modules), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which compositions preserve every original requirement decision, retain exactly its required '
                 'target certificate family, and construct the actual native graph, call and least replay '
                 'environment for every admitted term?',
        boundary='Complete original sources, requirements and terms precede every actual candidate. Original '
                 'decision conditions, exact replay-family domain and every original replay condition have '
                 'registered subject contracts. Whole-workflow presentation and operative transitions, '
                 'development-subject coverage and independent criticism, historical permission, full cost '
                 'and genesis remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
