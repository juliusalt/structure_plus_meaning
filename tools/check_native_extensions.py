"""Execute actual native package extensions and retain their complete recovered fields."""
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
    code += 'structure N = Native_Extension_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += r'''
fun jobservation (formed,(copied,(wrong,(u,(programs,(artifacts,(bindings,environment))))))) =
    "\"formed\":" ^ Bool.toString formed ^ ",\"source_retained\":" ^ Bool.toString copied ^
    ",\"wrong_source_matches\":" ^ Bool.toString wrong ^ ",\"selector_use\":" ^ juse u ^
    ",\"programs\":" ^ jf jprogram programs ^
    ",\"artifact_count\":" ^ jnat artifacts ^ ",\"binding_count\":" ^ jnat bindings ^
    ",\"environment\":" ^ jenvironment environment;
fun jresult NONE = "null"
  | jresult (SOME (d,observation)) =
      "{" ^ jobservation observation ^ ",\"entry\":" ^ jsite d ^ "}";
fun jcoordinate (d,e) = "[" ^ jnat d ^ "," ^ jsite e ^ "]";
fun jcontrolResult NONE = "null"
  | jcontrolResult (SOME (coordinates,observation)) =
      "{" ^ jobservation observation ^ ",\"coordinates\":" ^ jf jcoordinate coordinates ^ "}";
fun emit (i,(changed,paired)) =
  let val result = N.finite_native_extension_report changed paired
  in print ("NATIVE_EXTENSION " ^ Int.toString i ^
    " {\"source_has_variable_clause\":" ^ Bool.toString changed ^
    ",\"paired_requirement\":" ^ Bool.toString paired ^
    ",\"result\":" ^ jresult result ^ "}\n") end;
fun emitControl i =
  let val (candidate,(formed,(agrees,result))) = N.finite_native_control_report (N.nat_of_integer i)
  in print ("NATIVE_CONSTRUCTOR " ^ IntInf.toString i ^
    " {\"candidate\":" ^ jprogramWith jnat jnat jnat jnat candidate ^
    ",\"candidate_formed\":" ^ Bool.toString formed ^ ",\"old_fields_agree\":" ^ Bool.toString agrees ^
    ",\"result\":" ^ jcontrolResult result ^ "}\n") end;
'''
    def case(row):
        index, value = row
        boolean = lambda x: 'true' if x else 'false'
        return '(' + str(index) + ',(' + boolean(value['source_has_variable_clause']) + ',' + \
            boolean(value['paired_requirement']) + '))'
    code += 'val () = List.app emit ' + investigate.ml_list(list(enumerate(inputs['cases'])), case) + ';\n'
    code += 'val () = List.app emitControl ' + investigate.ml_list(inputs['controls'], str) + ';\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    cases = [{'source_has_variable_clause': changed, 'paired_requirement': paired}
             for changed in [False, True] for paired in [False, True]]

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        extensions = [r for r in reports if r['tag'] == 'NATIVE_EXTENSION']
        controls = [r for r in reports if r['tag'] == 'NATIVE_CONSTRUCTOR']
        assert reports == extensions + controls
        assert [r['indices'] for r in extensions] == [[i] for i in range(len(inputs['cases']))]
        assert [r['indices'] for r in controls] == [[i] for i in inputs['controls']]

        def program_fields(value):
            assert set(value) == {'interfaces', 'clauses'}
            for _, schema in value['clauses']:
                assert set(schema) == {'conclusion', 'premises', 'materials'}

        def result_fields(result, field):
            assert isinstance(result, dict)
            assert set(result) == {'formed', 'source_retained', 'wrong_source_matches', 'selector_use',
                                   field, 'programs', 'artifact_count', 'binding_count', 'environment'}
            assert all(isinstance(result[key], bool) for key in ['formed', 'source_retained', 'wrong_source_matches'])
            assert set(result['environment']) == {'artifacts', 'bindings'}
            for native in result['programs']:
                program_fields(native)

        for report, expected in zip(extensions, inputs['cases']):
            value = report['value']
            assert set(value) == {'source_has_variable_clause', 'paired_requirement', 'result'}
            assert all(value[key] == item for key, item in expected.items())
            result_fields(value['result'], 'entry')
        for report in controls:
            value = report['value']
            assert set(value) == {'candidate', 'candidate_formed', 'old_fields_agree', 'result'}
            program_fields(value['candidate'])
            assert isinstance(value['candidate_formed'], bool) and isinstance(value['old_fields_agree'], bool)
            if value['result'] is not None:
                result_fields(value['result'], 'coordinates')
        return {'complete_reports': reports, 'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The checked planner and actual finite package constructor are executed. '
                            'Every artifact and binding in the returned environment and every recovered '
                            'native interface and clause is serialized. Formation and both complete source '
                            'comparisons are computed by the proved finite readers. This launcher checks '
                            'serialization and retains the complete reports.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Extension_Execution'],
        inputs={'cases': cases, 'controls': list(range(14))}, input_paths=[Path(__file__), Path(native_program_json.__file__)],
        program=program, assess=assess, project=args.project.resolve(), timeout=600,
        question='Do the executed checked plans construct complete native packages over their actual retained sources?',
        boundary='The universal construction theorem connects each returned environment and selector to '
                 'the whole target program and its all-term meaning. Complete source correspondence is '
                 'established for these inputs. A general native source-correspondence admission operation '
                 'and the complete development protocol remain further work.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
