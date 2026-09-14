"""Execute actual finite certificates and their independent original-source conditions."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import native_history_json
import native_certificate_json
import observation_contracts
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\n'
    code += 'structure N = Native_Derivation_Investigation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += native_program_json.SCHEMAS + native_program_json.PROGRAMS
    code += program_evaluation_json.PRELUDE + investigation_json.PRELUDE
    code += 'val candidates = map N.nat_of_integer ' + investigate.ml_list(inputs['candidates'], str) + ';\n'
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.native_derivation_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += native_history_json.SOURCE
    code += r'''
'''
    code += native_certificate_json.PRELUDE
    code += r'''fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jderivation result ^ "}";
fun jreport NONE = "null"
  | jreport (SOME (x,(reference,candidates))) =
      "{\"problem\":" ^ jproblem x ^ ",\"reference\":" ^ jreference reference ^
      ",\"candidates\":" ^ jlist jcandidate candidates ^ "}";'''
    code += native_history_json.DIFFERENCES
    code += r'''
fun jassessment NONE = "null"
  | jassessment (SOME ((ready,(answers,(preserved,rejected))),(valid,domain))) =
      "{\"ready\":" ^ Bool.toString ready ^ ",\"differences\":" ^ jdifferences answers ^
      ",\"source_retained\":" ^ Bool.toString preserved ^ ",\"rejected\":" ^ Bool.toString rejected ^
      ",\"certificates_valid\":" ^ Bool.toString valid ^ ",\"certificate_domain\":" ^ Bool.toString domain ^ "}";
fun jcertificateReview (certificate,checked) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"checked\":" ^ Bool.toString checked ^ "}";
fun jevidence NONE = "null"
  | jevidence (SOME (rows,(extra,missing))) = "{\"certificates\":" ^ jf jcertificateReview rows ^
      ",\"extra_claims\":" ^ jf jcall extra ^ ",\"missing_claims\":" ^ jf jcall missing ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun assess (m,report) = let
  val a = Option.map #1 report
  val evidence = case report of NONE => NONE | SOME (_,r) => r
in
  "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
    ",\"evidence\":" ^ jevidence evidence ^
    ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_derivation_optional_inspect a f)) facets) ^ "}" end;
fun emitSubject (w,report) = print ("DERIVATION_SUBJECT " ^ jnat w ^ " " ^
  jreport report ^ "\n");
fun emitAssessment (w,assessments) = print ("DERIVATION_ASSESSMENT " ^ jnat w ^ " " ^
  jlist assess assessments ^ "\n");
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";
val () = print ("DERIVATION_SCOPE " ^ jlist jnat N.native_derivation_indices ^ "\n");
val (subjects,(assessments,comparison)) = N.native_derivation_report_packet scope selections;
val () = List.app emitSubject subjects;
val () = List.app emitAssessment assessments;
val ((rows,(relation,(selected,adequate))),cycles) = comparison;
val () = print ("DERIVATION_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("DERIVATION_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Native_Derivation_Investigation', 'native_derivation_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports and reports[0]['tag'] == 'DERIVATION_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'DERIVATION_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'DERIVATION_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'DERIVATION_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'DERIVATION_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original source fields, requested calls, every candidate certificate family, '
                            'full certificate checks, all answer and claim differences, assessments, comparisons and revisions are in results.log. '
                            'The proved operations produce all semantic observations and decisions. '
                            'The launcher checks serialization and retains the complete reports.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Derivation_Investigation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0, 2, 5], [0, 1, 2, 3, 4, 5], [5, 3, 4, 2, 1, 0]]},
        input_paths=[Path(__file__), Path(native_certificate_json.__file__), Path(check_reasoning.__file__), Path(investigation_json.__file__),
                     Path(native_program_json.__file__), Path(native_history_json.__file__), Path(program_evaluation_json.__file__),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual native certificate constructors return exactly the requested positive calls, '
                 'retain the original source and a complete valid certificate family, and refuse unavailable '
                 'original source and evaluation prerequisites?',
        boundary='The exact observation equation relates actual candidate functions and original native inputs '
                 'to six independent semantic conditions. The independent recursive checker is exactly the '
                 'original schema proof checker on every finite input. Adequacy retains all six conditions. '
                 'This finite execution does not establish arbitrary-method coverage, native artifact '
                 'placement, native mathematical-proof admission, complete development-cycle enforcement, '
                 'the whole cost account or genesis.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
