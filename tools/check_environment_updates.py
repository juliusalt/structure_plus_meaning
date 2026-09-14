"""Compare complete native incremental environment updates and persistent chains."""
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
import reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Environment_Update_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.environment_update_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += 'val chains = map N.nat_of_integer ' + investigate.ml_list(inputs['chains'], str) + ';\n'
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jvalue c = jartifact (N.finite_artifact_rows c);
fun jentry (u,c) = "[" ^ juse u ^ "," ^ jvalue c ^ "]";
fun jenv e = "{\"artifacts\":" ^ jf jentry (N.finite_environment_artifacts e) ^
  ",\"bindings\":" ^ jf jbinding (N.finite_environment_bindings e) ^ "}";
fun joperation (N.Install_Artifact (u,c)) = "{\"install_artifact\":" ^ jentry (u,c) ^ "}"
  | joperation (N.Install_Binding (u,k,v)) = "{\"install_binding\":" ^ jbinding ((u,k),v) ^ "}";
fun jsubject (artifacts,(bindings,operation)) = "{\"artifact_rows\":" ^ jlist jentry artifacts ^
  ",\"binding_rows\":" ^ jlist jbinding bindings ^ ",\"operation\":" ^ joperation operation ^ "}";
'''
    code += reader_comparison_json.prelude('jenv', 'environment_update_inspect')
    code += r'''
fun jchain (e,(values,(bucket,steps))) = "{\"environment\":" ^ jenv e ^
  ",\"fixed_query_result\":" ^ jf jvalue values ^ ",\"actual_optional_bucket\":" ^ jo (jf jvalue) bucket ^
  ",\"actual_lookup_steps\":" ^ jnat steps ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "ENVIRONMENT_UPDATE_SCOPE" (jlist jnat N.environment_update_indices);
val timer = Timer.startRealTimer ();
val (table,(comparison,cycles)) = N.environment_update_packet scope selections;
val () = print ("Physicaltime environment-update-packet " ^ LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => emit ("ENVIRONMENT_UPDATE_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("ENVIRONMENT_UPDATE_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "ENVIRONMENT_UPDATE_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "ENVIRONMENT_UPDATE_INVESTIGATION" (jcycle c)) cycles;
val () = List.app (fn n => emit ("ENVIRONMENT_UPDATE_CHAIN " ^ jnat n)
  (jo jchain (N.environment_update_chain_report n))) chains;
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
        'RRA_Environment_Update_Investigation', 'environment_update_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'ENVIRONMENT_UPDATE_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 2 + len(inputs['selections']) + len(inputs['chains'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'ENVIRONMENT_UPDATE_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 2 * size]
        assert compared['tag'] == 'ENVIRONMENT_UPDATE_COMPARISON' and compared['value']['scope'] == requested
        begin = 2 + 2 * size
        assert all(r['tag'] == 'ENVIRONMENT_UPDATE_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[begin:begin + len(inputs['selections'])]))
        assert all(r['tag'] == 'ENVIRONMENT_UPDATE_CHAIN' and r['indices'] == [n]
                   for n, r in zip(inputs['chains'], rows[-len(inputs['chains']):]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every original artifact and binding row, requested update, complete expected '
                            'and actual result environment, native conditions and full comparison and revision '
                            'reasons is retained. Persistent chains execute every step on the preceding '
                            'abstract state and retain the full final view and actual fixed-path count.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Environment_Update_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]], 'chains': [0, 32, 128]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1200,
        question='Which actual update methods implement the whole original guarded environment '
                 'constructor on complete sources, including unavailable and invalid updates?',
        boundary='Exact original relations determine soundness and completeness of each full result. '
                 'The closed store API preserves original formation by construction. Whole-view '
                 'inspection, index preparation, fresh allocation, workflow integration and full '
                 'physical cost remain separate boundaries.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
