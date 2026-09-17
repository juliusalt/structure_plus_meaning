"""Run native-equivalent clause admission on complete finite source environments."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import machine_reports
import native_program_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Requirement_Source_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.SCHEMAS
    code += r'''
val n = N.nat_of_integer;
fun jobs [source,target,included,member,clause,admitted] =
  "{\"source_formed\":" ^ Bool.toString source ^ ",\"candidate_formed\":" ^ Bool.toString target ^
  ",\"source_included\":" ^ Bool.toString included ^ ",\"package_member\":" ^ Bool.toString member ^
  ",\"complete_clause\":" ^ Bool.toString clause ^ ",\"admitted\":" ^ Bool.toString admitted ^ "}"
  | jobs _ = raise Fail "Incomplete observation domain";
fun emit i =
  let val (source,(schema,(target,(pu,(pr,(entry,(domains,observations))))))) =
        N.retained_clause_control_report (n i)
  in print ("RETAINED_CLAUSE " ^ IntInf.toString i ^
    " {\"source\":" ^ jenvironment source ^ ",\"expected_schema\":" ^ jschema schema ^
    ",\"candidate\":" ^ jenvironment target ^ ",\"package_root\":" ^ jsite (pu,pr) ^
    ",\"entry\":" ^ jsite entry ^ ",\"recovered_domains\":" ^ jlist (jlist jsite) domains ^
    ",\"observations\":" ^ jobs observations ^ "}\n") end;
'''
    code += 'val () = List.app emit ' + investigate.ml_list(inputs['indices'], str) + ';\n'
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
        assert [r['tag'] for r in reports] == ['RETAINED_CLAUSE'] * len(inputs['indices'])
        assert [r['indices'] for r in reports] == [[i] for i in inputs['indices']]
        for row in reports:
            result = row['value']
            assert set(result) == {'source', 'expected_schema', 'candidate', 'package_root',
                                   'entry', 'recovered_domains', 'observations'}
            assert set(result['observations']) == {
                'source_formed', 'candidate_formed', 'source_included',
                'package_member', 'complete_clause', 'admitted'}
            assert all(isinstance(v, bool) for v in result['observations'].values())
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The proved input map selects actual complete source and candidate environments. '
                            'Each observation and the admission verdict is computed by its native-equivalent '
                            'finite operation. This launcher checks serialization and retains every field.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Retained_Clause_Execution'],
        inputs={'indices': list(range(15))}, input_paths=[Path(__file__), Path(native_program_json.__file__)],
        program=program, assess=assess, project=args.project.resolve(), timeout=600,
        question='Does complete clause admission retain the actual declared source when candidate sources change?',
        boundary='Both complete environment tables, the expected schema, recovered domains and all six '
                 'computed observations are retained for every control.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': len(receipt.get('assessment', {}).get('complete_reports', []))}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
