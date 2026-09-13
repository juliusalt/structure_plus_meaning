"""Execute proved requirement observations over the complete actual native sources."""
from pathlib import Path
import argparse
import json

import check_reasoning
import admission_plan_json
import investigate
import machine_reports
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Requirement_Source_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += admission_plan_json.PRELUDE
    code += r'''
fun emit (i,(changed,paired)) =
  let val (plan,holds) = N.source_requirement_plan_report changed paired
  in print ("NATIVE_REQUIREMENT_PLAN " ^ Int.toString i ^
    " {\"source_has_variable_clause\":" ^ Bool.toString changed ^
    ",\"paired_requirement\":" ^ Bool.toString paired ^
    ",\"checked_plan\":" ^ jchecked plan ^
    ",\"admission_at_terms\":" ^ jlist Bool.toString holds ^ "}\n") end;
'''
    def case(row):
        index, value = row
        boolean = lambda x: 'true' if x else 'false'
        return '(' + str(index) + ',(' + boolean(value['source_has_variable_clause']) + ',' + \
            boolean(value['paired_requirement']) + '))'

    code += 'val () = List.app emit ' + investigate.ml_list(list(enumerate(inputs['cases'])), case) + ';\n'
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
        assert [r['tag'] for r in reports] == ['NATIVE_REQUIREMENT_PLAN'] * len(inputs['cases'])
        assert [r['indices'] for r in reports] == [[i] for i in range(len(inputs['cases']))]
        for report, expected in zip(reports, inputs['cases']):
            assert all(report['value'][key] == value for key, value in expected.items())
            assert len(report['value']['admission_at_terms']) == len(inputs['observation_terms'])
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The complete native source readings and their ordinary coordinate models '
                            'are proved to correspond. The report computes the checked instruction sequence '
                            'and its source requirement on three concrete terms. The construction theorem '
                            'connects these observations to installed packages; this run does not execute '
                            'the existential package constructor. This launcher checks serialization.'}

    cases = [{'source_has_variable_clause': changed, 'paired_requirement': paired}
             for changed in [False, True] for paired in [False, True]]
    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Factor_Native_Requirement_Cases'],
        inputs={'cases': cases, 'observation_terms': ['empty_collection', 'singleton_empty_payload',
                                                    'singleton_equal_empty_payload_pair']},
        input_paths=[Path(__file__), Path(admission_plan_json.__file__)], program=program, assess=assess, project=args.project.resolve(),
        question='Do checked recursive plans retain the actual source meaning and the empty-collection distinction?',
        boundary='The complete source program, requirement goal, native planning verdict and resulting '
                 'installation are connected by proved contracts over every term. The finite run observes '
                 'the four complete combinations of the two source and requirement constructors.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('complete_reports')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
