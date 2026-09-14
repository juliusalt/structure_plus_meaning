"""Compare native fresh-use mappings under original semantics and coordinate growth."""
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
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Use_Allocation_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE + native_program_json.COORDINATES
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.use_allocation_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jsubject (uses,(boundary,words)) = "{\"reserved_uses\":" ^ jf juse uses ^
  ",\"boundary\":" ^ juse boundary ^ ",\"requested_words\":" ^ jf jaddress words ^ "}";
fun jmapping (x,y) = "{\"input\":" ^ juse x ^ ",\"output\":" ^ juse y ^
  ",\"input_coordinates\":" ^ jnat (N.use_word_length x) ^
  ",\"output_coordinates\":" ^ jnat (N.use_word_length y) ^ "}";
fun jresult (subject,rows) = "{\"subject\":" ^ jsubject subject ^
  ",\"complete_mapping\":" ^ jf jmapping rows ^ "}";
fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.use_allocation_inspect result f)) facets) ^ "}";
fun jcomparison (rows,(relation,(selected,adequate))) = "{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "USE_ALLOCATION_SCOPE" (jlist jnat N.use_allocation_indices);
val (table,(comparison,(semantics,cycles))) = N.use_allocation_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("USE_ALLOCATION_SUBJECT " ^ jnat w)
  ("{\"subject\":" ^ jsubject context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("USE_ALLOCATION_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = emit "USE_ALLOCATION_COMPARISON" (jcomparison comparison);
val () = emit "USE_ALLOCATION_SEMANTICS" (jcomparison semantics);
val () = List.app (fn c => emit "USE_ALLOCATION_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Use_Allocation_Investigation', 'use_allocation_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'USE_ALLOCATION_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 3 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'USE_ALLOCATION_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        for i, tag in enumerate(['COMPARISON', 'SEMANTICS']):
            compared = rows[1 + 2 * size + i]
            assert compared['tag'] == 'USE_ALLOCATION_' + tag and compared['value']['scope'] == requested
        assert all(r['tag'] == 'USE_ALLOCATION_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[3 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete native subjects, mappings, coordinate counts, original-condition '
                            'observations, semantic and growth comparisons, and revision reasons are retained. '
                            'Host checks cover report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Use_Allocation_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1, 2, 3], [0, 1, 2, 3, 4]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual fresh-use mappings preserve the original boundary, freshness, injectivity '
                 'and suffixes, and which also add exactly one natural word coordinate?',
        boundary='Registered exact equations derive observations from complete actual function graphs. '
                 'Original and compact prefix embeddings have all-input semantic proofs. Finite scope '
                 'coverage, initial head scanning, cached allocation, generation-store integration, natural '
                 'bit cost, the full physical decision cost and genesis remain separate requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
