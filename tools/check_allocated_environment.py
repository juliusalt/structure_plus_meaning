"""Compare native allocation-state transitions and persistent-store histories."""
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
import reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Allocated_Environment_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.allocated_update_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += 'val chains = map N.nat_of_integer ' + investigate.ml_list(inputs['chains'], str) + ';\n'
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jvalue c = jartifact (N.finite_artifact_rows c);
fun jstoredArtifact (u,c) = "[" ^ juse u ^ "," ^ jvalue c ^ "]";
fun jenv e = "{\"artifacts\":" ^ jf jstoredArtifact (N.finite_environment_artifacts e) ^
  ",\"bindings\":" ^ jf jbinding (N.finite_environment_bindings e) ^ "}";
fun jstate (n,e) = "{\"next_head\":" ^ jnat n ^ ",\"environment\":" ^ jenv e ^ "}";
fun joptionalState r = jo jstate r;
fun joperation (N.Allocate_Artifact r) = "{\"allocate_artifact\":" ^ jvalue r ^ "}"
  | joperation (N.Add_Allocated_Binding (u,k,v)) = "{\"add_binding\":[" ^
      juse u ^ "," ^ jaddress k ^ "," ^ juse v ^ "]}";
fun jsubject (input,operation) = "{\"prepared_state\":" ^ jo
  (fn q => jstate (N.allocated_environment_view (N.raw_allocated_environment q))) input ^
  ",\"operation\":" ^ joperation operation ^ "}";
'''
    code += reader_comparison_json.prelude('joptionalState', 'allocated_update_inspect')
    code += r'''
fun jchain NONE = "null"
  | jchain (SOME (state,(next,(original,(bucket,count))))) = "{\"state\":" ^ jstate state ^
      ",\"next_use\":" ^ juse next ^ ",\"original_values\":" ^ jf jvalue original ^
      ",\"original_bucket\":" ^ jo (jf jvalue) bucket ^ ",\"original_read_steps\":" ^ jnat count ^ "}";

fun jallocationPath (path,((bucket,reads),((insertReads,updates),(values,result)))) =
  "{\"path\":" ^ jlist Bool.toString path ^ ",\"previous_bucket\":" ^ jo (jf jvalue) bucket ^
  ",\"lookup_steps\":" ^ jnat reads ^ ",\"insertion_read_steps\":" ^ jnat insertReads ^
  ",\"insertion_update_steps\":" ^ jnat updates ^ ",\"updated_values\":" ^ jf jvalue values ^
  ",\"updated_environment\":" ^ jenv result ^ "}";
fun jchainPaths NONE = "null"
  | jchainPaths (SOME (previous,path)) = "{\"previous\":" ^ jchain (SOME previous) ^
      ",\"allocation_path\":" ^ jallocationPath path ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "ALLOCATED_ENVIRONMENT_SCOPE" (jlist jnat N.allocated_update_indices);
val (table,(comparison,cycles)) = N.allocated_update_packet scope selections;
val () = List.app (fn (w,(context,cells)) => emit ("ALLOCATED_ENVIRONMENT_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("ALLOCATED_ENVIRONMENT_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val () = List.app (fn n => emit ("ALLOCATED_ENVIRONMENT_CHAIN " ^ jnat n)
  (jchainPaths (N.allocated_environment_chain_paths n))) chains;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "ALLOCATED_ENVIRONMENT_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "ALLOCATED_ENVIRONMENT_INVESTIGATION" (jcycle c)) cycles;
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
        'RRA_Allocated_Environment_Investigation', 'allocated_update_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'ALLOCATED_ENVIRONMENT_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size, chains = len(requested), len(inputs['chains'])
        assert len(rows) == 2 * size + chains + 2 + len(inputs['selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'ALLOCATED_ENVIRONMENT_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        assert all(r['tag'] == 'ALLOCATED_ENVIRONMENT_CHAIN' and r['indices'] == [n]
                   for n, r in zip(inputs['chains'], rows[1 + 2 * size:1 + 2 * size + chains]))
        compared = rows[1 + 2 * size + chains]
        assert compared['tag'] == 'ALLOCATED_ENVIRONMENT_COMPARISON' and compared['value']['scope'] == requested
        assert all(r['tag'] == 'ALLOCATED_ENVIRONMENT_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[2 + 2 * size + chains:]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete prepared states, actual result families, original-condition '
                            'observations, comparisons, revision reasons and persistent histories are '
                            'retained. The host checks report reproduction only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Allocated_Environment_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]], 'chains': [0, 32, 128]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=900,
        question='Which actual allocation-state operations preserve the original complete local '
                 'constructor, required head update, optional input and every result field?',
        boundary='Registered original-constructor equations govern the complete state outputs. '
                 'A closed state carries original formation and a bound derived from all original uses. '
                 'Later allocation maintains that bound without scanning old rows. Binary-path encoding, '
                 'natural-number arithmetic and full physical cost, graft and generation adoption, '
                 'whole workflow enforcement and genesis remain further requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
