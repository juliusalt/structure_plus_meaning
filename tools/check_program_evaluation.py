"""Execute program judgments, operation comparisons and computed revisions on complete subjects."""
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
    code += 'structure N = Program_Evaluation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += investigation_json.PRELUDE
    code += 'val candidates = map N.nat_of_integer ' + investigate.ml_list(inputs['candidates'], str) + ';\n'
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    code += program_evaluation_json.PRELUDE
    code += r'''
fun jcall q = jcallWith jnat q;
fun japplication a = japplicationWith jnat jnat jnat jnat a;
fun jrule r = jruleWith jnat jnat r;
fun janswer a = janswerWith jnat a;
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jmethod (m,(a,qualities)) = "{\"method\":" ^ jnat m ^ ",\"answer\":" ^ janswer a ^
  ",\"qualities\":" ^ jlist jquality qualities ^ "}";
fun emitSubject w = let
  val (p,(d,(formed,(covered,(closed,(applications,(rules,(answer,methods)))))))) =
    N.program_evaluation_report w;
  in print ("PROGRAM_EVALUATION " ^ jnat w ^ " {\"program\":" ^
    jprogramWith jnat jnat jnat jnat p ^ ",\"demand\":" ^ jf jcall d ^
    ",\"formed\":" ^ Bool.toString formed ^ ",\"head_covered\":" ^ Bool.toString covered ^
    ",\"demand_closed\":" ^ Bool.toString closed ^ ",\"applications\":" ^ jf japplication applications ^
    ",\"rules\":" ^ jf jrule rules ^ ",\"answer\":" ^ janswer answer ^
    ",\"methods\":" ^ jlist jmethod methods ^ "}\n") end;
val observations = N.program_evaluation_investigation_observations;
val relation = N.program_evaluation_investigation_relation;
fun emitInvestigation (i,selected) = let
  val initial = N.program_evaluation_investigation selected;
  val repairs = N.investigation_repairs candidates facets selected observations relation;
  val revision as (_,(_,(_,(revised,_)))) =
    N.investigation_revision candidates facets selected observations relation;
  val followed = N.program_evaluation_investigation revised;
  in print ("PROGRAM_INVESTIGATION " ^ Int.toString i ^ " {\"selected\":" ^ jlist jnat selected ^
    ",\"initial\":" ^ jbasis initial ^ ",\"repairs\":" ^ jrepairs repairs ^
    ",\"revision\":" ^ jrevision revision ^ ",\"followed\":" ^ jbasis followed ^ "}\n") end;
val () = List.app emitSubject N.program_evaluation_workload_indices;
val () = print ("PROGRAM_COMPARISON {\"observations\":" ^ jlist jtriple observations ^
  ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat N.program_evaluation_selected ^ "}\n");
'''
    code += 'val () = List.app emitInvestigation ' + investigate.ml_list(
        list(enumerate(inputs['selections'])),
        lambda row: '(' + str(row[0]) + ',map N.nat_of_integer ' +
        investigate.ml_list(row[1], str) + ')') + ';\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Program_Evaluation_Investigation', 'program_evaluation_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert len(reports) == 23 + len(inputs['selections'])
        assert all(r['tag'] == 'PROGRAM_EVALUATION' and r['indices'] == [i]
                   for i, r in enumerate(reports[:22]))
        assert reports[22]['tag'] == 'PROGRAM_COMPARISON' and reports[22]['indices'] == []
        assert all(r['tag'] == 'PROGRAM_INVESTIGATION' and r['indices'] == [i]
                   and r['value']['selected'] == inputs['selections'][i]
                   for i, r in enumerate(reports[23:]))
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every program, requested call, generated application, rule and returned judgment '
                            'is retained. Proved operations derive quality observations, comparisons, selected '
                            'methods and revisions. This launcher checks serialization and retains execution '
                            'provenance; it supplies no condition truth or selected method.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Program_Evaluation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'selections': [[], [0], [0, 1, 2]]},
        input_paths=[Path(__file__), Path(investigation_json.__file__), Path(native_program_json.__file__),
                     Path(program_evaluation_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which proposed evaluation operations give sound and complete original program judgments '
                 'and withhold an answer when the finite decision prerequisites are absent?',
        boundary='The subjects are complete programs and demands, with equations through their actual maps. '
                 'The independent condition is original positive meaning. Complete head scope and closed '
                 'premise demand justify the finite answer; the reported method comparison has the stated '
                 'finite workload scope. Complete development-cycle enforcement and genesis remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
