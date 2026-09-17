"""Compare complete native data quotation readers on actual source artifacts."""
from pathlib import Path
import argparse
import json

import check_reasoning
import execution_support as investigate
import investigation_json
import machine_reports
import native_artifact_inputs
import native_certificate_json
import native_program_json
import observation_contracts
import program_evaluation_json
import reader_comparison_json
import proved_code


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Data_Reading_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += program_evaluation_json.PRELUDE + investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val n = N.nat_of_integer;\n'
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.data_reading_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    source = ('SOME (' + native_artifact_inputs.artifact(inputs['source']) + ')'
              if inputs['source'] is not None else 'fixtureSource')
    code += 'fun jcall q = jcallWith jsite q;\n' + native_certificate_json.PROOFS
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jfixtureRow (key,value) = "{\"certificate\":" ^ jcertificate key ^
  ",\"source\":" ^ jo (fn c => jartifact (N.finite_artifact_rows c)) value ^ "}";
fun jsubject (c,r) = "{\"artifact\":" ^ jartifact (N.finite_artifact_rows c) ^
  ",\"root\":" ^ jaddress r ^ "}";
'''
    code += reader_comparison_json.prelude('jterm', 'data_reading_inspect')
    code += r'''
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun measured label f = let val timer = Timer.startRealTimer () val answer = f ()
  val elapsed = Time.toMilliseconds (Timer.checkRealTimer timer)
  in print ("Physicaltime " ^ label ^ " " ^ LargeInt.toString elapsed ^ "ms\n");
     TextIO.flushOut TextIO.stdOut; answer end;
'''
    if inputs['source'] is None:
        code += 'val (fixtureRows,fixtureSource) = N.data_reading_fixture_packet;\n'
        code += 'val () = emit \"DATA_READING_FIXTURE\" (jf jfixtureRow fixtureRows);\n'
    code += r'''
fun run NONE = emit "DATA_READING_UNAVAILABLE" "null"
  | run (SOME sourceArtifact) = let
val () = emit "DATA_READING_SOURCE" (jartifact (N.finite_artifact_rows sourceArtifact));
val () = emit "DATA_READING_SCOPE" (jlist jnat N.data_reading_indices);
val prepared = measured "prepared-source-root" (fn () => N.finite_complete_data_readings_prepared sourceArtifact []);
val () = emit "DATA_READING_PREPARED" (jf jterm prepared);
val (table,(comparison,cycles)) = measured "complete-native-comparison"
  (fn () => N.data_reading_packet sourceArtifact scope selections);
val () = List.app (fn (w,(context,cells)) => emit ("DATA_READING_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("DATA_READING_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "DATA_READING_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "DATA_READING_INVESTIGATION" (jcycle c)) cycles;
in () end;
'''
    code += 'val () = run (' + source + ');\n'
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['proof', 'poly', 'project', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--source', type=Path, help='Supply a complete artifact instead of constructing the native fixture.')
    parser.add_argument('--cases', type=int, nargs='+')
    args = parser.parse_args()
    if args.cases is not None:
        assert all(type(i) is int and i >= 0 for i in args.cases)
    source = (json.loads(args.source.read_text(), object_pairs_hook=machine_reports.unique_object)
              if args.source is not None else None)
    if source is not None:
        native_artifact_inputs.artifact(source)
    proof = json.loads(args.proof.read_text())
    contracts = proof['subject_contracts']
    assert len(contracts) == 1
    assert all(investigate.file_hash(Path(c['path'])) == c['sha256'] for c in contracts)
    contract = observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Data_Reading_Investigation', 'data_reading_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        if inputs['source'] is None:
            assert rows[0]['tag'] == 'DATA_READING_FIXTURE' and rows[0]['indices'] == []
            rows = rows[1:]
            if len(rows) == 1 and rows[0]['tag'] == 'DATA_READING_UNAVAILABLE':
                return {'source_available': False, 'reproduction_boundary': machine_reports.boundary(path),
                        'boundary': 'The native constructor and uniform-family selector returned no source; no reader comparison was produced.'}
        assert rows[0]['tag'] == 'DATA_READING_SOURCE' and rows[1]['tag'] == 'DATA_READING_SCOPE'
        assert rows[2]['tag'] == 'DATA_READING_PREPARED'
        scope = rows[1]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 4 + len(inputs['selections'])
        assert all(r['tag'] == 'DATA_READING_SUBJECT' and r['indices'] == [w]
                   for w, r in zip(requested, rows[3:3 + size]))
        assert all(r['tag'] == 'DATA_READING_ASSESSMENT' and r['indices'] == [w]
                   for w, r in zip(requested, rows[3 + size:3 + 2 * size]))
        compared = rows[3 + 2 * size]
        assert compared['tag'] == 'DATA_READING_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'DATA_READING_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[4 + 2 * size:]))
        return {'source_available': True, 'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete actual source, every reference and candidate reading, soundness and completeness '
                            'conditions, comparisons and revisions are native results. Physical timing is diagnostic. '
                            'The host validates input serialization and complete report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Data_Reading_Execution'],
        inputs={'source': source, 'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *([args.source] if args.source is not None else []),
                     *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1800,
        question='Which actual data quotation readers preserve and reflect the original complete quotation '
                 'relation on whole source artifacts, including malformed bytes, shifted roots and counted data?',
        boundary='All satisfaction observations come from actual complete native readings under the registered '
                 'source equations. The source-formation guard is calculated from the complete artifact. '
                 'Physical timing does not establish an internal cost account or complete workflow enforcement.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
