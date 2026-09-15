"""Compare actual guarded graft operations against complete original readiness and result relations."""
from pathlib import Path
import argparse
import json

import graft_program_json
import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code
import reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Graft_Admission_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.graft_admission_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += graft_program_json.SUBJECT
    code += r'''
fun joptionalEnvironment NONE = "null"
  | joptionalEnvironment (SOME e) = "{\"environment\":" ^ jenv e ^
    ",\"formed\":" ^ Bool.toString (N.graft_view_formed e) ^ "}";
'''
    code += reader_comparison_json.prelude('joptionalEnvironment', 'graft_admission_inspect')
    code += r'''
fun jusePair (u,v) = "[" ^ juse u ^ "," ^ juse v ^ "]";
fun jrequirements (oldFormed,(importedFormed,(shared,(compatible,(ready,(mapping,raw)))))) =
  "{\"original_formed\":" ^ Bool.toString oldFormed ^ ",\"imported_formed\":" ^ Bool.toString importedFormed ^
  ",\"shared_artifact\":" ^ Bool.toString shared ^ ",\"boundary_compatible\":" ^ Bool.toString compatible ^
  ",\"ready\":" ^ Bool.toString ready ^ ",\"complete_mapping\":" ^ jf jusePair mapping ^
  ",\"raw_graft\":" ^ jenv raw ^ ",\"raw_formed\":" ^ Bool.toString (N.graft_view_formed raw) ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "GRAFT_ADMISSION_SCOPE" (jlist jnat N.graft_admission_indices);
val (table,(comparison,cycles)) = N.graft_admission_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("GRAFT_ADMISSION_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("GRAFT_ADMISSION_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = List.app (fn w => emit ("GRAFT_ADMISSION_REQUIREMENTS " ^ jnat w)
  (jrequirements (N.graft_admission_requirements (N.graft_admission_case w)))) scope;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "GRAFT_ADMISSION_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "GRAFT_ADMISSION_INVESTIGATION" (jcycle c)) cycles;
'''
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'RRA_Graft_Admission_Investigation', 'graft_admission_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'GRAFT_ADMISSION_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 3 * size + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT', 'REQUIREMENTS']):
            assert all(r['tag'] == 'GRAFT_ADMISSION_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 3 * size]
        assert compared['tag'] == 'GRAFT_ADMISSION_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'GRAFT_ADMISSION_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[2 + 3 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete graft inputs, actual result families, original-condition '
                            'observations, comparisons, revision reasons and readiness components are '
                            'retained. The host checks report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Graft_Admission_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual guarded compact grafts preserve all original admission prerequisites, '
                 'every resulting relation and both successful and failed result rows?',
        boundary='Complete original readiness and constructor equations derive the registered observations. '
                 'All environment formation, shared-artifact and boundary compatibility prerequisites '
                 'are computed from the actual complete inputs. Closed indexed graft and generation '
                 'adoption, physical cost, full workflow enforcement and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
