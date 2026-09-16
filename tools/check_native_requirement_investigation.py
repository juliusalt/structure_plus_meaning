"""Execute native requirement constructor conditions, complete subjects and computed revisions."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_native_admission
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import program_evaluation_json
import proved_code


def program(engine, inputs):
    code = check_native_admission.serialization(engine, 'Native_Requirement_Investigation_Execution',
        goal_serializer='jlist (jgoalWith jsite)', goal_field='requirements')
    code += investigation_json.PRELUDE
    code += 'val candidates = map N.nat_of_integer ' + investigate.ml_list(inputs['candidates'], str) + ';\n'
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.native_requirement_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jdifferences NONE = "null"
  | jdifferences (SOME (extra,missing)) = "{\"extra\":" ^ jf jterm extra ^
      ",\"missing\":" ^ jf jterm missing ^ "}";
fun jassessment NONE = "null"
  | jassessment (SOME (ready,(terms,(preserved,rejected)))) =
      "{\"ready\":" ^ Bool.toString ready ^ ",\"differences\":" ^ jdifferences terms ^
      ",\"preserved\":" ^ Bool.toString preserved ^ ",\"rejected\":" ^ Bool.toString rejected ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun assess (m,a) =
  "{\"method\":" ^ jnat m ^ ",\"assessment\":" ^ jassessment a ^
    ",\"qualities\":" ^ jlist jquality (map (fn f => (f,N.native_requirement_optional_inspect a f)) facets) ^ "}";
fun emitSubject (w,(subject,cells)) = print ("REQUIREMENT_SUBJECT " ^ jnat w ^ " " ^
  jreport subject ^ "\n");
fun emitAssessment (w,(subject,cells)) = print ("REQUIREMENT_ASSESSMENT " ^ jnat w ^ " " ^
  jlist assess cells ^ "\n");
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";
val () = print ("REQUIREMENT_SCOPE " ^ jlist jnat N.native_requirement_indices ^ "\n");
val timer = Timer.startRealTimer ();
val (table,((rows,(relation,(selected,adequate))),cycles)) = N.native_requirement_shared_packet scope selections;
val () = print ("Physicaltime shared-requirement-packet " ^ LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app emitSubject table;
val () = List.app emitAssessment table;
val () = print ("REQUIREMENT_COMPARISON {\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}\n");
val () = List.app (fn c => print ("REQUIREMENT_INVESTIGATION " ^ jcycle c ^ "\n")) cycles;
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
        'Factor_Native_Requirement_Investigation', 'native_requirement_investigation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path, deferred=True))
        assert reports and reports[0]['tag'] == 'REQUIREMENT_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(reports) == 2 * size + 2 + len(inputs['selections'])
        assert all(r['tag'] == 'REQUIREMENT_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1:1 + size]))
        assert all(r['tag'] == 'REQUIREMENT_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, reports[1 + size:1 + 2 * size]))
        compared = reports[1 + 2 * size]
        assert compared['tag'] == 'REQUIREMENT_COMPARISON' and compared['indices'] == []
        assert compared['value']['scope'] == requested
        assert all(r['tag'] == 'REQUIREMENT_INVESTIGATION' and r['indices'] == []
                   and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[2 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'The complete subject, assessment, comparison and revision reports are in '
                            'results.log. Proved operations derive the observations and every result. '
                            'The launcher checks serialization and scope and retains the reconstruction '
                            'boundary; it supplies no satisfaction claim or selected method.'}

    receipt = proved_code.checked_execution(
        args.proof, args.poly, args.output, required_theories=['Native_Requirement_Investigation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 3, 2], [0, 1, 2, 3]]},
        input_paths=[Path(__file__), Path(check_native_admission.__file__), Path(admission_goal_json.__file__),
                     Path(investigation_json.__file__), Path(native_program_json.__file__),
                     Path(program_evaluation_json.__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual native constructor operations satisfy the original requirement family, preserve the '
                 'complete source environment, and refuse unsupported source requests?',
        boundary='The exact observation equation relates actual candidate functions, original conjunction of positive '
                 'goal conditions and concrete source problems. Adequacy requires every represented '
                 'condition. Term observations require successful exact native evaluation. Coverage '
                 'beyond the executed problems and complete development-cycle enforcement remain open.')
    print(json.dumps({'status': receipt['status'], 'error': receipt.get('error'),
                      'reports': receipt.get('assessment', {}).get('reproduction_boundary')}))
    return int(receipt['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
