"""Execute the proved meaning observation on the two actual native guard packages."""
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
fun juse NONE = "null" | juse (SOME a) = jlist jnat a;
fun jsite (u,r) = "[" ^ juse u ^ "," ^ jlist jnat r ^ "]";
fun emit (i,changed) =
  let val (domain,holds) = N.native_guard_source_meaning_report changed
  in print ("NATIVE_GUARD_MEANING " ^ Int.toString i ^
    " {\"source_has_variable_clause\":" ^ Bool.toString changed ^
    ",\"installed_definitions\":" ^ jlist jsite domain ^
    ",\"installed_guard_on_empty_payload\":" ^ Bool.toString holds ^ "}\n") end;
'''
    code += 'val () = List.app emit ' + investigate.ml_list(
        list(enumerate(inputs['source_variants'])),
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
        assert [r['tag'] for r in reports] == ['NATIVE_GUARD_MEANING'] * len(inputs['source_variants'])
        assert [r['indices'] for r in reports] == [[i] for i in range(len(inputs['source_variants']))]
        assert [r['value']['source_has_variable_clause'] for r in reports] == inputs['source_variants']
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The observation is defined on the actual native programs recovered from '
                            'the complete finite source artifacts. Its code equation follows from '
                            'their all-term meaning theorem. This launcher checks serialization.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Factor_Requirement_Source_Examples'],
        inputs={'source_variants': [False, True]}, input_paths=[Path(__file__)],
        program=program, assess=assess, project=args.project.resolve(),
        question='Can identical installed native guards with equal domains have different meanings when their source changes?',
        boundary='The source constructor changes one actual clause; both complete native package readings '
                 'and the all-term meaning equations are established in the proof.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('complete_reports')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
