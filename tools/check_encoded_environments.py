"""Compare native environment codecs against whole original updates and actual paths."""
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
import reader_product_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = Encoded_Environment_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS
    code += investigation_json.PRELUDE + investigation_json.CYCLE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.codec_environment_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += 'val heads = map N.nat_of_integer ' + investigate.ml_list(inputs['heads'], str) + ';\n'
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
    code += r'fun jrawViews (view,reference) = "{\"view\":" ^ jenv view ^ ",\"reference\":" ^ jenv reference ^ "}";' + '\n'
    code += reader_product_json.prelude('jenv', 'jenv', 'jrawViews', 'codec_environment_full_inspect')
    code += r'''
fun jpathResult (path,((bucket,reads),((insertReads,updates),(values,result)))) =
  "{\"path\":" ^ jlist Bool.toString path ^ ",\"original_bucket\":" ^ jo (jf jvalue) bucket ^
  ",\"lookup_steps\":" ^ jnat reads ^ ",\"insertion_read_steps\":" ^ jnat insertReads ^
  ",\"insertion_update_steps\":" ^ jnat updates ^ ",\"updated_values\":" ^ jf jvalue values ^
  ",\"updated_environment\":" ^ jenv result ^ "}";
fun jpaths (unary,digit) = "{\"unary\":" ^ jpathResult unary ^ ",\"digit\":" ^ jpathResult digit ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
val () = emit "ENCODED_ENVIRONMENT_SCOPE" (jlist jnat N.codec_environment_indices);
val timer = Timer.startRealTimer ();
val (table,(comparison,(cycles,(previousScope,(previousComparison,previousCycles))))) = N.codec_environment_packet scope selections;
val () = print ("Physicaltime environment-update-packet " ^ LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => emit ("ENCODED_ENVIRONMENT_SUBJECT " ^ jnat w)
  ("{\"context\":" ^ jcontext context ^ ",\"candidates\":" ^ jlist jcandidate cells ^ "}")) table;
val () = List.app (fn (w,(context,cells)) => emit ("ENCODED_ENVIRONMENT_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "ENCODED_ENVIRONMENT_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "ENCODED_ENVIRONMENT_INVESTIGATION" (jcycle c)) cycles;
val () = emit "ENCODED_ENVIRONMENT_PREVIOUS_SCOPE" (jlist jnat previousScope);
val (previousRows,(previousRelation,(previousSelected,previousAdequate))) = previousComparison;
val () = emit "ENCODED_ENVIRONMENT_PREVIOUS_COMPARISON" ("{\"scope\":" ^ jlist jnat previousScope ^
  ",\"observations\":" ^ jlist jtriple previousRows ^ ",\"relation\":" ^ jlist jpair previousRelation ^
  ",\"selected_methods\":" ^ jlist jnat previousSelected ^ ",\"adequate_methods\":" ^ jlist jnat previousAdequate ^ "}");
val () = List.app (fn c => emit "ENCODED_ENVIRONMENT_PREVIOUS_INVESTIGATION" (jcycle c)) previousCycles;
val () = List.app (fn n => emit ("ENCODED_ENVIRONMENT_PATH " ^ jnat n)
  (jpaths (N.codec_environment_path_comparison n))) heads;
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
        'RRA_Encoded_Environment_Investigation', 'codec_environment_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'ENCODED_ENVIRONMENT_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        assert len(rows) == 2 * size + 4 + len(inputs['selections']) + len(inputs['heads']) + len(inputs['previous_selections'])
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'ENCODED_ENVIRONMENT_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 2 * size]
        assert compared['tag'] == 'ENCODED_ENVIRONMENT_COMPARISON' and compared['value']['scope'] == requested
        begin = 2 + 2 * size
        assert all(r['tag'] == 'ENCODED_ENVIRONMENT_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[begin:begin + len(inputs['selections'])]))
        previous_begin = begin + len(inputs['selections'])
        previous_scope = [w for w in requested if w < 20]
        assert rows[previous_begin]['tag'] == 'ENCODED_ENVIRONMENT_PREVIOUS_SCOPE'
        assert rows[previous_begin]['value'] == previous_scope
        assert rows[previous_begin + 1]['tag'] == 'ENCODED_ENVIRONMENT_PREVIOUS_COMPARISON'
        assert rows[previous_begin + 1]['value']['scope'] == previous_scope
        assert all(r['tag'] == 'ENCODED_ENVIRONMENT_PREVIOUS_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['previous_selections'], rows[previous_begin + 2:previous_begin + 5]))
        assert all(r['tag'] == 'ENCODED_ENVIRONMENT_PATH' and r['indices'] == [n]
                   for n, r in zip(inputs['heads'], rows[-len(inputs['heads']):]))
        return {'complete_scope': scope, 'executed_scope': requested,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every original row, requested update, complete expected and actual environment, '
                            'native condition, comparison and revision reason is retained. The original update-only scope and results are retained separately. Each path report '
                            'executes the actual insertion and retains its whole result and both traversal counts.'}


    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Encoded_Environment_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1], [0, 1, 2]], 'previous_selections': [[], [0], [0, 1]], 'heads': [1, 2, 33, 129]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=1200,
        question='Which actual environment indexes preserve every original raw input row and the whole guarded constructor, '
                 'and what paths do their actual insertions traverse?',
        boundary='The complete environment relation is independent of its key codec. General lookup '
                 'contracts transfer the original local guards and formation proofs. Unary and digit '
                 'instances have all-input equality with the original update reference. Finite scope, '
                 'cached allocation, graft and generation adoption, arithmetic, full physical cost, '
                 'workflow and genesis remain separate requirements.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
