"""Compare complete original environment grafts and actual fresh-use mappings."""
from pathlib import Path
import argparse
import json

import check_reasoning
import investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Graft_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE + native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.graft_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jvalue c = jartifact (N.finite_artifact_rows c);
fun jentry (u,c) = "[" ^ juse u ^ "," ^ jvalue c ^ "]";
fun jenv e = "{\"artifacts\":" ^ jf jentry (N.finite_environment_artifacts e) ^
  ",\"bindings\":" ^ jf jbinding (N.finite_environment_bindings e) ^ "}";
fun jsubject (original,(use,imported)) = "{\"original\":" ^ jenv original ^ ",\"boundary\":" ^ juse use ^
  ",\"imported\":" ^ jenv imported ^ ",\"original_formed\":" ^ Bool.toString (N.graft_view_formed original) ^
  ",\"imported_formed\":" ^ Bool.toString (N.graft_view_formed imported) ^ "}";
fun jmapping (x,y) = "{\"input\":" ^ juse x ^ ",\"output\":" ^ juse y ^
  ",\"input_coordinates\":" ^ jnat (N.use_word_length x) ^
  ",\"output_coordinates\":" ^ jnat (N.use_word_length y) ^ "}";
fun jresult (subject,(rows,(result,reference))) = "{\"subject\":" ^ jsubject subject ^
  ",\"complete_mapping\":" ^ jf jmapping rows ^ ",\"result\":" ^ jenv result ^
  ",\"reference\":" ^ jenv reference ^ ",\"result_formed\":" ^ Bool.toString (N.graft_view_formed result) ^
  ",\"reference_formed\":" ^ Bool.toString (N.graft_view_formed reference) ^ "}";
fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.graft_inspect result f)) facets) ^ "}";
fun jcomparison (rows,(relation,(selected,adequate))) = "{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "GRAFT_SCOPE" (jlist jnat N.graft_indices);
val (table,(comparison,(semantics,cycles))) = N.graft_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("GRAFT_SUBJECT " ^ jnat w)
  ("{\"subject\":" ^ jsubject context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("GRAFT_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = emit "GRAFT_COMPARISON" (jcomparison comparison);
val () = emit "GRAFT_SEMANTICS" (jcomparison semantics);
val () = List.app (fn c => emit "GRAFT_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Graft_Investigation', 'graft_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'GRAFT_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 3 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'GRAFT_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        for i, tag in enumerate(['COMPARISON', 'SEMANTICS']):
            compared = rows[1 + 2 * size + i]
            assert compared['tag'] == 'GRAFT_' + tag and compared['value']['scope'] == requested
        assert all(r['tag'] == 'GRAFT_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[3 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original and imported environments, shared uses, actual mapping graphs, '
                            'original-constructor outputs, formation observations, coordinate counts, native '
                            'conditions and every comparison and revision reason are retained.'}


    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Graft_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1, 2, 3], [0, 1, 2, 3, 4]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual graft mappings and outputs preserve the original shared boundary, '
                 'distinct occurrences, freshness and complete environment constructors, and which '
                 'add one natural coordinate to each imported use?',
        boundary='Registered exact equations derive every observation from complete actual subjects. '
                 'The general graft contract makes formation equivalent to original shared-boundary '
                 'binding compatibility under its explicit premises. Exact raw output is separate '
                 'from admitted formation. Candidate scope, index and generation adoption, physical '
                 'cost, workflow and genesis remain separate requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
