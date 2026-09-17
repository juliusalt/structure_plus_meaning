"""Compare complete native use codecs and independently bounded path lengths."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import investigation_json
import machine_reports
import native_program_json
import observation_contracts
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Use_Codec_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE + native_program_json.COORDINATES
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.use_codec_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun jpath p = jlist Bool.toString p;
fun jdecoded NONE = "{\"accepted\":false}" | jdecoded (SOME u) =
  "{\"accepted\":true,\"use\":" ^ juse u ^ "}";
fun jencoded NONE = "null" | jencoded (SOME p) = jpath p;
fun jsubject (uses,(paths,k)) = "{\"uses\":" ^ jf juse uses ^ ",\"paths\":" ^ jf jpath paths ^
  ",\"coordinate_exponent\":" ^ jnat k ^ "}";
fun jforward k (u,(p,r)) = "{\"use\":" ^ juse u ^ ",\"path\":" ^ jpath p ^
  ",\"decoded\":" ^ jdecoded r ^ ",\"path_length\":" ^ jnat (N.size_list p) ^
  ",\"coordinate_bound_holds\":" ^ Bool.toString (N.use_coordinate_bound k u) ^
  ",\"path_budget\":" ^ jnat (N.use_path_budget k u) ^ "}";
fun jbackward (p,(r,q)) = "{\"path\":" ^ jpath p ^ ",\"decoded\":" ^ jdecoded r ^
  ",\"reencoded\":" ^ jencoded q ^ "}";
fun jresult ((uses,(paths,k)),(forward,backward)) = "{\"subject\":" ^ jsubject (uses,(paths,k)) ^
  ",\"complete_encoding_graph\":" ^ jf (jforward k) forward ^
  ",\"complete_decoding_graph\":" ^ jf jbackward backward ^ "}";
fun jcandidate (m,result) = "{\"method\":" ^ jnat m ^ ",\"result\":" ^ jresult result ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.use_codec_inspect result f)) facets) ^ "}";
fun jcomparison (rows,(relation,(selected,adequate))) = "{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "USE_CODEC_SCOPE" (jlist jnat N.use_codec_indices);
val (table,(comparison,(semantics,cycles))) = N.use_codec_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("USE_CODEC_SUBJECT " ^ jnat w)
  ("{\"subject\":" ^ jsubject context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("USE_CODEC_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = emit "USE_CODEC_COMPARISON" (jcomparison comparison);
val () = emit "USE_CODEC_SEMANTICS" (jcomparison semantics);
val () = List.app (fn c => emit "USE_CODEC_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Use_Codec_Investigation', 'use_codec_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'USE_CODEC_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 3 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'USE_CODEC_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        for i, tag in enumerate(['COMPARISON', 'SEMANTICS']):
            compared = rows[1 + 2 * size + i]
            assert compared['tag'] == 'USE_CODEC_' + tag and compared['value']['scope'] == requested
        assert all(r['tag'] == 'USE_CODEC_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[3 + 2 * size:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete native use and path graphs, decoder results, bounds, semantic and cost '
                            'comparisons, and revision reasons are retained. Host checks cover reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Use_Codec_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1, 2], [0, 1, 2, 3]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual codecs preserve every requested original use and every accepted path, '
                 'and which satisfy a structural path budget derived from original coordinate bounds?',
        boundary='Registered exact graph equations derive every observation. Unary, digit and reversed '
                 'digit codecs have all-input semantic proofs. Digit codecs satisfy the independent '
                 'coordinate-budget theorem. Finite candidate and path scope, actual store integration, '
                 'arithmetic and full physical cost, workflow and genesis remain separate requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
