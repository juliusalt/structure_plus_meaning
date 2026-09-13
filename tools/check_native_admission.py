"""Execute complete native admission construction subjects and observations."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_reasoning
import investigate
import machine_reports
import native_program_json
import program_evaluation_json
import proved_code


def serialization(engine, module, *, goal_serializer="jgoalWith jsite", goal_field="goal"):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = ' + module + ';\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE + admission_goal_json.PRELUDE
    code += "fun jgoalValue x = (" + goal_serializer + ") x;\n"
    code += r'''
fun jenv e = jenvironment
  (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jsource NONE = "null" | jsource (SOME p) = jprogram p;
fun jevaluation NONE = "null" | jevaluation (SOME (p,a)) =
  "{\"program\":" ^ jprogram p ^ ",\"answer\":" ^ jf (jcallWith jsite) a ^ "}";
fun jterms NONE = "null" | jterms (SOME t) = jf jterm t;
fun jproblem (e,(u,(r,(g,t)))) =
  "{\"environment\":" ^ jenv e ^ ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^
  ",\"GOAL_FIELD\":" ^ jgoalValue g ^ ",\"terms\":" ^ jf jterm t ^ "}";
fun jsourceReport (p,(supported,(d,(a,t)))) =
  "{\"program\":" ^ jsource p ^ ",\"supported\":" ^ Bool.toString supported ^
  ",\"demand\":" ^ jf (jcallWith jsite) d ^ ",\"evaluation\":" ^ jevaluation a ^
  ",\"goal_terms\":" ^ jterms t ^ "}";
fun jtargetReport NONE = "null"
  | jtargetReport (SOME (d,(e,(u,(p,(demand,(a,(terms,original)))))))) =
    "{\"entry\":" ^ jsite d ^ ",\"environment\":" ^ jenv e ^ ",\"use\":" ^ juse u ^
    ",\"program\":" ^ jsource p ^ ",\"demand\":" ^ jf (jcallWith jsite) demand ^
    ",\"evaluation\":" ^ jevaluation a ^ ",\"accepted_terms\":" ^ jterms terms ^
    ",\"original_package\":" ^ jsource original ^ "}";
fun jmethod (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jtargetReport result ^ "}";
fun jreport NONE = "null"
  | jreport (SOME (problem,(source,methods))) =
    "{\"problem\":" ^ jproblem problem ^ ",\"source\":" ^ jsourceReport source ^
    ",\"methods\":" ^ jlist jmethod methods ^ "}";
'''.replace('GOAL_FIELD', goal_field)
    return code


def program(engine, inputs):
    code = serialization(engine, 'Native_Admission_Execution')
    code += r'''
fun emit w = print ("NATIVE_ADMISSION " ^ jnat w ^ " " ^ jreport (N.native_admission_report w) ^ "\n");
val () = print ("NATIVE_ADMISSION_SCOPE " ^ jlist jnat N.native_admission_indices ^ "\n");
'''
    scope = ('N.native_admission_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val () = List.app emit (' + scope + ');\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(i >= 0 for i in args.cases)

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'NATIVE_ADMISSION_SCOPE'
        assert reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        assert len(reports) == len(requested) + 1
        assert all(r['tag'] == 'NATIVE_ADMISSION' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The complete reports remain in results.log. Their scope comes from the proved '
                            'program. This launcher checks serialization and preserves the reconstruction '
                            'boundary; it supplies no semantic answer or selected constructor.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Admission_Execution'],
        inputs={'cases': args.cases},
        input_paths=[Path(__file__), Path(admission_goal_json.__file__),
                     Path(native_program_json.__file__), Path(program_evaluation_json.__file__)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='How do the constructed native entries behave against the original admission goals '
                 'on these actual source environments?',
        boundary='The source reader, constructor and evaluator retain their Isabelle-established contracts. '
                 'These complete reports expose original goals, actual outputs and bounded evaluations. '
                 'An absent evaluation is not a negative judgment. Construction of complete development '
                 'cycles and native proof artifacts remains separate.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
