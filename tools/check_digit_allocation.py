"""Compare persistent digit allocation against complete original result contracts."""
from pathlib import Path
import argparse
import json

import allocation_program_json
import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code
import reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Digit_Allocation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.digit_allocation_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += 'val chains = map N.nat_of_integer ' + investigate.ml_list(inputs['chains'], str) + ';\n'
    code += allocation_program_json.STATE + allocation_program_json.VIEWED_SUBJECT
    code += r'''
fun jsubject (input,operation) = jviewedSubject (Option.map N.digit_allocated_view input,operation);
'''
    code += reader_comparison_json.prelude('joptionalState', 'digit_allocation_inspect')
    code += allocation_program_json.PATHS
    code += r'''
fun joriginalContext (subject,reference) = "{\"subject\":" ^ jviewedSubject subject ^
  ",\"reference_readings\":" ^ jf joptionalState reference ^ "}";
fun jpairedResults (m,(original,(digit,equal))) = "{\"method\":" ^ jnat m ^
  ",\"original\":" ^ jf joptionalState original ^ ",\"digit\":" ^ jf joptionalState digit ^
  ",\"equal\":" ^ Bool.toString equal ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "DIGIT_ALLOCATION_SCOPE" (jlist jnat N.digit_allocation_indices);
val (table,(comparison,cycles)) = N.digit_allocation_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("DIGIT_ALLOCATION_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("DIGIT_ALLOCATION_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = List.app (fn w => let val (oldView,digitView) = N.allocation_case_views w in
  emit ("DIGIT_ALLOCATION_CASE_VIEWS " ^ jnat w) ("{\"original\":" ^ jviewedSubject oldView ^
    ",\"digit\":" ^ jviewedSubject digitView ^ ",\"equal\":" ^ Bool.toString (N.allocation_case_views_equal w) ^
    ",\"original_context\":" ^ joriginalContext (N.allocation_original_context w) ^
    ",\"paired_results\":" ^ jlist jpairedResults (N.allocation_case_result_pairs w) ^ "}") end) scope;
val () = List.app (fn n => emit ("DIGIT_ALLOCATION_CHAIN " ^ jnat n)
  ("{\"original\":" ^ jchainPaths (N.allocated_environment_chain_paths n) ^
    ",\"digit\":" ^ jchainPaths (N.digit_allocation_chain_paths n) ^ "}")) chains;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "DIGIT_ALLOCATION_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "DIGIT_ALLOCATION_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Digit_Allocation_Investigation', 'digit_allocation_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'DIGIT_ALLOCATION_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size, chains = len(requested), len(inputs['chains'])
        assert len(rows) == 3 * size + chains + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT', 'CASE_VIEWS']):
            assert all(r['tag'] == 'DIGIT_ALLOCATION_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        assert all(r['tag'] == 'DIGIT_ALLOCATION_CHAIN' and r['indices'] == [n]
                   for n, r in zip(inputs['chains'], rows[1 + 3 * size:1 + 3 * size + chains]))
        compared = rows[1 + 3 * size + chains]
        assert compared['tag'] == 'DIGIT_ALLOCATION_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'DIGIT_ALLOCATION_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[2 + 3 * size + chains:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete prepared states, actual result families, original-condition '
                            'observations, comparisons, revision reasons and persistent histories are '
                            'retained. The host checks report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Digit_Allocation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]], 'chains': [0, 32, 128]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual allocation-state operations preserve the original complete local '
                 'constructor, required head update, optional input and every result field across exact digit paths?',
        boundary='Registered original-constructor equations govern the complete state outputs. '
                 'A closed state carries original formation and a bound derived from all original uses. '
                 'Later digit allocation maintains that bound without scanning old rows. Key construction, '
                 'natural-number arithmetic and full physical cost, graft and generation adoption, '
                 'whole workflow enforcement and genesis remain further requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
