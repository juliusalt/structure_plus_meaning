"""Execute complete histories and their independently specified native conditions."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_History_Investigation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE + investigation_json.PRELUDE
    code += 'val candidates = map N.nat_of_integer ' + investigate.ml_list(inputs['candidates'], str) + ';\n'
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.native_history_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jcall q = jcallWith jsite q;
fun japplication a = japplicationWith jaddress jaddress jsite jaddress a;
fun jstep (x,w) = "{\"before\":" ^ jf jcall x ^ ",\"applications\":" ^ jf japplication w ^ "}";
fun jsource NONE = "null" | jsource (SOME p) = jprogram p;
fun jdetails NONE = "null"
  | jdetails (SOME (formed,(covered,(closed,applications)))) =
      "{\"formed\":" ^ Bool.toString formed ^ ",\"head_covered\":" ^ Bool.toString covered ^
      ",\"demand_closed\":" ^ Bool.toString closed ^ ",\"applications\":" ^ jf japplication applications ^ "}";
fun jevaluation NONE = "null" | jevaluation (SOME (p,a)) =
  "{\"program\":" ^ jprogram p ^ ",\"answer\":" ^ jf jcall a ^ "}";
fun jcoverage (d,(heads,result)) =
  "{\"expanded_demand\":" ^ jf jcall d ^ ",\"all_source_heads_covered\":" ^
    (case heads of NONE => "null" | SOME b => Bool.toString b) ^
    ",\"expanded_evaluation\":" ^ jevaluation result ^ "}";
fun jreference (source,(details,(result,coverage))) =
  "{\"source\":" ^ jsource source ^ ",\"details\":" ^ jdetails details ^
  ",\"evaluation\":" ^ jevaluation result ^ ",\"coverage\":" ^ jcoverage coverage ^ "}";
fun jproblem (e,(u,(r,d))) =
  "{\"environment\":" ^ jenvironment
    (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e)) ^
  ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^ ",\"demand\":" ^ jf jcall d ^ "}";
fun jhistory NONE = "null"
  | jhistory (SOME (p,(a,steps))) = "{\"program\":" ^ jprogram p ^
      ",\"answer\":" ^ jf jcall a ^ ",\"steps\":" ^ jlist jstep steps ^ "}";
fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jhistory result ^ "}";
fun jreport NONE = "null"
  | jreport (SOME (x,(reference,candidates))) =
      "{\"problem\":" ^ jproblem x ^ ",\"reference\":" ^ jreference reference ^
      ",\"candidates\":" ^ jlist jcandidate candidates ^ "}";
fun jdifferences NONE = "null"
  | jdifferences (SOME (extra,missing)) = "{\"extra\":" ^ jf jcall extra ^
      ",\"missing\":" ^ jf jcall missing ^ "}";
fun jassessment NONE = "null"
  | jassessment (SOME ((ready,(answers,(preserved,rejected))),(steps,witnesses))) =
      "{\"ready\":" ^ Bool.toString ready ^ ",\"differences\":" ^ jdifferences answers ^
      ",\"source_retained\":" ^ Bool.toString preserved ^ ",\"rejected\":" ^ Bool.toString rejected ^
      ",\"steps\":" ^ Bool.toString steps ^ ",\"witnesses\":" ^ Bool.toString witnesses ^ "}";
fun jstepCheck (expected,(actual,progress)) =
  "{\"expected\":" ^ jf jcall expected ^ ",\"offered\":" ^ jf jcall actual ^
  ",\"progress\":" ^ Bool.toString progress ^ "}";
fun jstepReview (rows,(expected,(actual,stopped))) =
  "{\"occurrences\":" ^ jlist jstepCheck rows ^ ",\"expected_final\":" ^ jf jcall expected ^
  ",\"offered_final\":" ^ jf jcall actual ^ ",\"stopped\":" ^ Bool.toString stopped ^ "}";
fun jwitnessReview (x,(extra,missing)) =
  "{\"before\":" ^ jf jcall x ^ ",\"extra\":" ^ jf japplication extra ^
  ",\"missing\":" ^ jf japplication missing ^ "}";
fun jevidence NONE = "null"
  | jevidence (SOME (steps,witnesses)) =
      "{\"steps\":" ^ jstepReview steps ^ ",\"witnesses\":" ^ jlist jwitnessReview witnesses ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun assess (m,report) = let
  val a = Option.map #1 report
  val evidence = case report of NONE => NONE | SOME (_,r) => r
in
  "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
    ",\"evidence\":" ^ jevidence evidence ^
    ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_history_optional_inspect a f)) facets) ^ "}" end;
fun emitSubject (w,report) = print ("HISTORY_SUBJECT " ^ jnat w ^ " " ^
  jreport report ^ "\n");
fun emitAssessment (w,assessments) = print ("HISTORY_ASSESSMENT " ^ jnat w ^ " " ^
  jlist assess assessments ^ "\n");
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";
val () = print ("HISTORY_SCOPE " ^ jlist jnat N.native_history_indices ^ "\n");
val (subjects,(assessments,comparison)) = N.native_history_report_packet scope selections;
val () = List.app emitSubject subjects;
val () = List.app emitAssessment assessments;
val ((rows,(relation,(selected,adequate))),cycles) = comparison;
val () = print ("HISTORY_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("HISTORY_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'Factor_Native_History_Investigation', 'native_history_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'HISTORY_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'HISTORY_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'HISTORY_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'HISTORY_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'HISTORY_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original source fields, requested calls, every candidate history, '
                            'answer differences, assessments, comparisons and revisions are in results.log. '
                            'The proved operations produce all semantic observations and decisions. '
                            'The launcher checks serialization and retains the complete reports.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_History_Investigation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 1, 2, 3], [0, 1, 2, 3, 4, 5], [3, 0, 1, 4, 5, 2]]},
        input_paths=[Path(__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), Path(program_evaluation_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual native history operations retain exact requested positive answers, the original '
                 'source, every progressive preceding state and complete schema witnesses, while refusing '
                 'unavailable source and evaluation inputs?',
        boundary='The exact observation equation relates actual candidate functions and original native inputs '
                 'to six independent semantic conditions. Adequacy retains all six. The finite execution '
                 'does not establish arbitrary-method coverage, native proof-artifact construction, native '
                 'mathematical-proof checking, complete development-cycle enforcement, the whole cost '
                 'account or genesis.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
