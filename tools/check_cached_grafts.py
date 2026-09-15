"""Compare complete original cached graft results and actual persistent histories."""
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
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Cached_Graft_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.cached_graft_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += 'val sourceScope = N.cached_graft_source_scope scope;\n'
    code += 'val histories = ' + investigate.ml_list(list(enumerate(inputs['histories'])),
        lambda row: '(N.nat_of_integer ' + str(row[0]) + ',' + str(row[1]['grow']).lower() +
                    ',N.nat_of_integer ' + str(row[1]['steps']) + ')') + ';\n'
    code += graft_program_json.SUBJECT.replace('fun jsubject', 'fun joriginalGraftSubject')
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jstate (n,e) = "{\"next_head\":" ^ jnat n ^ ",\"environment\":" ^ jenv e ^
  ",\"formed\":" ^ Bool.toString (N.graft_view_formed e) ^ "}";
fun joptionalState r = jo jstate r;
fun jsubject (input,(boundary,(artifacts,bindings))) = "{\"prepared_state\":" ^ jo
  (fn q => jstate (N.digit_allocated_view q)) input ^ ",\"boundary\":" ^ juse boundary ^
  ",\"imported_artifact_rows\":" ^ jlist jentry artifacts ^
  ",\"imported_binding_rows\":" ^ jlist jbinding bindings ^
  ",\"imported_environment\":" ^ jenv (N.finite_enumerated_environment artifacts bindings) ^ "}";
'''
    code += reader_comparison_json.prelude('joptionalState', 'cached_graft_inspect')
    code += r'''
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "CACHED_GRAFT_SCOPE" (jlist jnat N.cached_graft_indices);
val () = emit "CACHED_GRAFT_SOURCE_SCOPE" (jlist jnat sourceScope);
val (table,(comparison,cycles)) = N.cached_graft_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("CACHED_GRAFT_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("CACHED_GRAFT_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = List.app (fn w => let val (actual,previous) = N.cached_graft_source_report w in
  emit ("CACHED_GRAFT_SOURCE " ^ jnat w) ("{\"actual\":" ^ joriginalGraftSubject actual ^
    ",\"previous\":" ^ joriginalGraftSubject previous ^ ",\"equal\":" ^ Bool.toString (N.cached_graft_sources_equal w) ^ "}") end) sourceScope;
val () = List.app (fn (i,grow,n) => emit ("CACHED_GRAFT_CHAIN " ^ jnat i)
  ("{\"grow\":" ^ Bool.toString grow ^ ",\"steps\":" ^ jnat n ^
    ",\"state\":" ^ joptionalState (N.cached_graft_chain_report grow n) ^ "}")) histories;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "CACHED_GRAFT_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "CACHED_GRAFT_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Cached_Graft_Investigation', 'cached_graft_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'CACHED_GRAFT_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size, chains = len(requested), len(inputs['histories'])
        assert rows[1]['tag'] == 'CACHED_GRAFT_SOURCE_SCOPE'
        source_scope = rows[1]['value']
        assert set(source_scope) <= set(requested)
        source_count = len(source_scope)
        assert len(rows) == 2 * size + source_count + chains + 3 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'CACHED_GRAFT_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[2 + i * size:2 + (i + 1) * size]))
        assert all(r['tag'] == 'CACHED_GRAFT_SOURCE' and r['indices'] == [w]
                   for w, r in zip(source_scope, rows[2 + 2 * size:2 + 2 * size + source_count]))
        start = 2 + 2 * size + source_count
        assert all(r['tag'] == 'CACHED_GRAFT_CHAIN' and r['indices'] == [i]
                   and r['value']['grow'] == h['grow'] and r['value']['steps'] == h['steps']
                   for (i,h), r in zip(enumerate(inputs['histories']), rows[start:start + chains]))
        compared = rows[start + chains]
        assert compared['tag'] == 'CACHED_GRAFT_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'CACHED_GRAFT_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[start + chains + 1:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete prepared states, actual result families, original-condition '
                            'observations, comparisons, revision reasons and persistent histories are '
                            'retained. The host checks report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Cached_Graft_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]], 'histories': [{'grow': True, 'steps': n} for n in [0, 32, 128]] + [{'grow': False, 'steps': 3}]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual cached digit grafts preserve the original formed-input, shared-artifact '
                 'and binding prerequisites, the actual stored-prefix allocation and every returned field?',
        boundary='The existing closed store carries original formation and its strict actual use-head '
                 'bound. Grafting checks the imported rows and old shared-boundary lookups, merges '
                 'every renamed row into the actual index and advances the stored head. Complete '
                 'original result contracts and actual native observation equations govern the comparison. '
                 'Generation-store adoption, full physical cost, whole workflow enforcement, historical '
                 'permission and reachability, native mathematical-proof checking and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
