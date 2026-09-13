"""Execute extensions whose complete source premises are checked from the actual environment."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import machine_reports
import native_program_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_Source_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += r'''
fun joption f NONE = "null" | joption f (SOME x) = f x;
fun jrawEnvironment e = jenvironment
  (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jcoordinate (d,e) = "[" ^ jsite d ^ "," ^ jsite e ^ "]";
fun jresult (p,(coordinates,(e,(u,(oldReadings,newReadings))))) =
  "{\"source\":" ^ jprogram p ^ ",\"coordinates\":" ^ jf jcoordinate coordinates ^
  ",\"environment\":" ^ jrawEnvironment e ^ ",\"selector\":" ^ juse u ^
  ",\"original_readings\":" ^ jf jprogram oldReadings ^ ",\"target_readings\":" ^ jf jprogram newReadings ^ "}";
fun jcase (i,(q,(formed,(source,result)))) =
  "{\"case\":" ^ jnat i ^ ",\"target\":" ^ jprogram q ^ ",\"target_formed\":" ^ Bool.toString formed ^
  ",\"admitted_source\":" ^ joption jprogram source ^ ",\"result\":" ^ joption jresult result ^ "}";
fun jcases (e,(pu,(pr,(source,cases)))) =
  "{\"environment\":" ^ jrawEnvironment e ^ ",\"source_use\":" ^ juse pu ^
  ",\"source_root\":" ^ jaddress pr ^ ",\"recovered_source\":" ^ joption jprogram source ^
  ",\"cases\":" ^ jlist jcase cases ^ "}";
fun emit i = print ("SOURCE_EXTENSION " ^ IntInf.toString i ^ " " ^
  joption jcases (N.finite_source_extension_cases (N.nat_of_integer i)) ^ "\n");
'''
    code += 'val () = List.app emit ' + investigate.ml_list(inputs['sources'], str) + ';\n'
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
        assert len(reports) == len(inputs['sources'])
        for report, index in zip(reports, inputs['sources']):
            assert report['tag'] == 'SOURCE_EXTENSION' and report['indices'] == [index]
            group = report['value']
            assert group is not None
            assert set(group) == {'environment', 'source_use', 'source_root', 'recovered_source', 'cases'}
            assert [c['case'] for c in group['cases']] == list(range(6))
            for case in group['cases']:
                assert set(case) == {'case', 'target', 'target_formed', 'admitted_source', 'result'}
                assert isinstance(case['target_formed'], bool)
                if case['result'] is not None:
                    assert set(case['result']) == {'source', 'coordinates', 'environment', 'selector',
                                                   'original_readings', 'target_readings'}
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The actual package reader establishes each source; the extension computes '
                            'target formation and complete old-field agreement before construction. Every '
                            'source, target, coordinate row, returned artifact and binding, and original and '
                            'target package reading is retained. This launcher checks serialization only.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Source_Execution'],
        inputs={'sources': list(range(12))}, input_paths=[Path(__file__), Path(native_program_json.__file__)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1200,
        question='Does the extension establish its complete source premise from each actual native environment?',
        boundary='Every successful finite_extend_source_native call establishes the source package, '
                 'the complete mapped-extension profile and the actual underlying constructor result. '
                 'The reused constructor theorem supplies whole-target meaning and preservation of all old '
                 'material. General alpha-model search and the complete development protocol remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
