"""Execute the selected finite evaluator on complete actual native packages."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import machine_reports
import native_program_json
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Program_Evaluation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE
    code += r'''
fun jsource NONE = "null" | jsource (SOME p) = jprogram p;
fun jfocus NONE = "null" | jfocus (SOME d) = jsite d;
fun jdetails NONE = "null"
  | jdetails (SOME (formed,(covered,(closed,(applications,rules))))) =
      "{\"formed\":" ^ Bool.toString formed ^ ",\"head_covered\":" ^ Bool.toString covered ^
      ",\"demand_closed\":" ^ Bool.toString closed ^
      ",\"applications\":" ^ jf (japplicationWith jaddress jaddress jsite jaddress) applications ^
      ",\"rules\":" ^ jf (jruleWith jaddress jsite) rules ^ "}";
fun jresult NONE = "null" | jresult (SOME (p,a)) =
  "{\"program\":" ^ jprogram p ^ ",\"answer\":" ^ jf (jcallWith jsite) a ^ "}";
fun jreport NONE = "null"
  | jreport (SOME (e,(u,(r,(focus,(source,(d,(details,result)))))))) =
    "{\"environment\":" ^ jenvironment
      (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e)) ^
    ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^ ",\"focus\":" ^ jfocus focus ^
    ",\"source\":" ^ jsource source ^ ",\"demand\":" ^ jf (jcallWith jsite) d ^
    ",\"details\":" ^ jdetails details ^ ",\"result\":" ^ jresult result ^ "}";
fun emit i = print ("NATIVE_EVALUATION " ^ jnat i ^ " " ^ jreport (N.native_evaluation_report i) ^ "\n");
'''
    code += 'val () = List.app emit (map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str) + ');\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert len(reports) == len(inputs['cases'])
        assert all(r['tag'] == 'NATIVE_EVALUATION' and r['indices'] == [i]
                   for i, r in zip(inputs['cases'], reports))
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every source is read from the actual complete native environment. The selected '
                            'evaluator derives its rule table and all judgments without supplied true seeds. '
                            'This launcher retains every structural field and checks serialization; it '
                            'does not decide native meaning or supply expected answers.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Program_Evaluation_Execution'],
        inputs={'cases': list(range(21))},
        input_paths=[Path(__file__), Path(native_program_json.__file__), Path(program_evaluation_json.__file__)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1200,
        question='What are the exact requested positive judgments of these actual constructed native packages?',
        boundary='Success establishes complete source recovery and the original positive-query predicate on '
                 'each requested call. Head coverage and closed demand remain checked prerequisites. '
                 'Missing source or incomplete prerequisites give no answer. This does not construct '
                 'native proof artifacts or enforce the complete development cycle.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
