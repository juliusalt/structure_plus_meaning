"""Execute original-subject certificate scope coverage and its full reasons."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_certificate_json
import native_certificate_coverage_json
import native_history_json
import native_program_json
import observation_contracts
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_Certificate_Coverage_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE + investigation_json.PRELUDE
    code += native_history_json.SOURCE + native_certificate_json.PRELUDE
    code += native_certificate_json.INSTANCES + native_certificate_coverage_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jproblemOption NONE = "null" | jproblemOption (SOME x) = jproblem x;
fun jassessment (retained,reports) = "{\"originals_retained\":" ^ Bool.toString retained ^
  ",\"coverage\":" ^ jlist jfamilyCoverage reports ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jcandidate (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jlist jderivation result ^ "}";
fun jassessed (m,(result,a)) = "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
  ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.certificate_coverage_inspect a f)) facets) ^ "}";
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";
val (xs,(originals,(cells,(comparison,cycles)))) = N.certificate_coverage_packet selections;
val () = print "COVERAGE_SCOPE [0]\n";
val () = print ("COVERAGE_SUBJECT 0 {\"native_indices\":" ^ jlist jnat N.native_certificate_indices ^
  ",\"native_inputs\":" ^ jlist jproblemOption xs ^ ",\"originals\":" ^ jlist jderivation originals ^
  ",\"candidates\":" ^ jlist jcandidate cells ^ "}\n");
val () = print ("COVERAGE_ASSESSMENT 0 " ^ jlist jassessed cells ^ "\n");
val (rows,(relation,(selected,adequate))) = comparison;
val () = print ("COVERAGE_COMPARISON {\"scope\":[0],\"observations\":" ^ jlist jtriple rows ^
  ",\"relation\":" ^ jlist jpair relation ^ ",\"selected_methods\":" ^ jlist jnat selected ^
  ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("COVERAGE_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
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
        'Factor_Native_Certificate_Coverage_Investigation', 'certificate_coverage_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert len(reports) == 4 + len(inputs['selections'])
        assert [(r['tag'], r['indices']) for r in reports[:4]] == [
            ('COVERAGE_SCOPE', []), ('COVERAGE_SUBJECT', [0]),
            ('COVERAGE_ASSESSMENT', [0]), ('COVERAGE_COMPARISON', [])]
        assert reports[0]['value'] == [0] and reports[3]['value']['scope'] == [0]
        assert all(r['tag'] == 'COVERAGE_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selected
                   for r, selected in zip(reports[4:], inputs['selections']))
        return {'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Original native inputs, source-derived certificate families, complete scope candidates, '
                            'all original paths and projection-conflict witnesses, actual assessments and full '
                            'revision reasons are retained. The proved operation supplies every verdict.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Certificate_Coverage_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'scope': [0], 'selections': [[], [0], [0, 1, 2, 3]]},
        input_paths=[Path(__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), Path(native_history_json.__file__),
                     Path(native_certificate_json.__file__), Path(native_certificate_coverage_json.__file__),
                     Path(program_evaluation_json.__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Does the actual original certificate scope retain its complete subjects and expose proof identity, '
                 'call identity and multiple-path sharing distinctions?',
        boundary='The original source and certificate families supply every complete conflict witness. The exact '
                 'coverage contracts connect computed observations to actual original nodes and paths. '
                 'Scope comparison and coverage do not alone authorize development adoption.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
