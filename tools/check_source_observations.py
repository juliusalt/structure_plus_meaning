"""Execute source observations and their computed revisions on complete native inputs."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import investigation_json
import machine_reports
import native_program_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_Source_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += investigation_json.PRELUDE
    code += r'''
val candidates = map N.nat_of_integer [0,1,2,3,4,5,6];
val facets = map N.nat_of_integer [0,1,2,3];
val observations = N.source_investigation_observations;
val relation = N.source_investigation_relation;
fun emitSource c = let
  val ((e,(u,(r,p))),(readings,(actual,values))) = N.source_example_report c;
  fun jvalue (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
  in print ("SOURCE_INPUT " ^ jnat c ^ " {\"environment\":" ^
    jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e)) ^
    ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^ ",\"program\":" ^ jprogram p ^
    ",\"readings\":" ^ jf jprogram readings ^ ",\"source_matches\":" ^ Bool.toString actual ^
    ",\"observations\":" ^ jlist jvalue values ^ "}\n") end;
fun emitInvestigation (i,selected) = let
  val initial = N.source_investigation selected;
  val repairs = N.investigation_repairs candidates facets selected observations relation;
  val revision as (_,(_,(_,(revised,_)))) =
    N.investigation_revision candidates facets selected observations relation;
  val followed = N.source_investigation revised;
  in print ("SOURCE_INVESTIGATION " ^ Int.toString i ^ " {\"selected\":" ^ jlist jnat selected ^
    ",\"initial\":" ^ jbasis initial ^ ",\"repairs\":" ^ jrepairs repairs ^
    ",\"revision\":" ^ jrevision revision ^ ",\"followed\":" ^ jbasis followed ^ "}\n") end;
val () = List.app emitSource candidates;
val () = print ("SOURCE_TABLE {\"observations\":" ^ jlist jtriple observations ^
  ",\"relation\":" ^ jlist jpair relation ^ "}\n");
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

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        subjects = reports[:7]
        assert all(r['tag'] == 'SOURCE_INPUT' and r['indices'] == [i] for i, r in enumerate(subjects))
        assert reports[7]['tag'] == 'SOURCE_TABLE' and reports[7]['indices'] == []
        revisions = reports[8:]
        assert len(revisions) == len(inputs['selections'])
        assert all(r['tag'] == 'SOURCE_INVESTIGATION' and r['indices'] == [i]
                   and r['value']['selected'] == inputs['selections'][i] for i, r in enumerate(revisions))
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The native readers derive every observation from the complete environment '
                            'and program. The existing investigation computes conflicts, repairs and revisions; '
                            'each returned revision is evaluated again. This launcher retains those complete '
                            'results and checks serialization, without supplying condition truth or a selected answer.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Source_Execution'],
        inputs={'selections': [[0, 1, 2], [], [3]]},
        input_paths=[Path(__file__), Path(investigation_json.__file__), Path(native_program_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=600,
        question='Which complete native-source observations determine the independently stated source-reading condition?',
        boundary='The subject and observation equations are proved against native_package_at on the actual '
                 'environment, use, root and complete program. The seven subjects criticize the available '
                 'field projections. The whole-program equation is universal; this does not decide arbitrary '
                 'alpha equivalence or admit the complete development protocol.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
