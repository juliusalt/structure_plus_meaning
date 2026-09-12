"""Execute the actual-source counterexample to identifying a program by its domain."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import machine_reports
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Requirement_Source_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += r'''
fun jinstruction _ = raise Fail "The proved source-boundary controls contain no instructions";
fun jplan NONE = "null"
  | jplan (SOME (ds,(next,instructions))) =
    "{\"entries\":" ^ jlist jnat ds ^ ",\"next\":" ^ jnat next ^
    ",\"instructions\":" ^ jlist jinstruction instructions ^ "}";
fun emit (i,hasClause) =
  let val (domain,(plan,(blueprint,installed))) = N.requirement_source_boundary_report hasClause
  in print ("REQUIREMENT_SOURCE_BOUNDARY " ^ Int.toString i ^
    " {\"source_has_clause\":" ^ Bool.toString hasClause ^ ",\"domain\":" ^ jlist jnat domain ^
    ",\"checked_plan\":" ^ jplan plan ^ ",\"blueprint_admitted\":" ^ Bool.toString blueprint ^
    ",\"installed_guard_on_empty_payload\":" ^ Bool.toString installed ^ "}\n") end;
'''
    code += 'val () = List.app emit ' + investigate.ml_list(
        list(enumerate(inputs['clause_presence'])),
        lambda row: '(' + str(row[0]) + ',' + ('true' if row[1] else 'false') + ')') + ';\n'
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
        assert [r['tag'] for r in reports] == ['REQUIREMENT_SOURCE_BOUNDARY'] * 2
        assert [r['indices'] for r in reports] == [[0], [1]]
        assert [r['value']['source_has_clause'] for r in reports] == inputs['clause_presence']
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The input chooses whether the explicit ordinary source program contains its clause. '
                            'All observations are calculated on that actual program under the proved report equation. '
                            'This launcher checks complete serialization and retains the results.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Factor_Requirement_Source_Boundary'],
        inputs={'clause_presence': [False, True]}, input_paths=[Path(__file__)],
        program=program, assess=assess, project=args.project.resolve(),
        question='Can equal source domains and accepted plans identify the installed predicates meaning?',
        boundary='The two complete ordinary programs share a domain and blueprint but have different native meanings.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('complete_reports')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
