"""Compare complete original history states and actual indexed admission members."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import check_reasoning
import history_program_json
import investigate
import investigation_json
import machine_reports
import native_certificate_json
import native_program_json
import native_stream_json
import observation_contracts
import program_evaluation_json
import proved_code
import stream_reader_comparison_json


def program(engine, inputs):
    code = 'use ' + investigate.ml_string(str(engine)) + ';\nstructure N = History_Index_Execution;\n'
    code += check_reasoning.SCALAR_JSON_PRELUDE
    code += native_program_json.COORDINATES + native_program_json.ARTIFACT_ROWS + native_program_json.TARGETS
    code += program_evaluation_json.PRELUDE + '\nfun jcall q = jcallWith jsite q;\n'
    code += native_certificate_json.PROOFS + admission_goal_json.PRELUDE
    code += investigation_json.PRELUDE + investigation_json.CYCLE + native_stream_json.PRELUDE
    code += history_program_json.PRELUDE
    code += 'val facets = map N.nat_of_integer ' + investigate.ml_list(inputs['facets'], str) + ';\n'
    scope = ('N.history_index_indices' if inputs['cases'] is None else
             'map N.nat_of_integer ' + investigate.ml_list(inputs['cases'], str))
    code += 'val scope = ' + scope + ';\n'
    code += 'val selections = ' + investigate.ml_list(inputs['selections'],
        lambda s: 'map N.nat_of_integer ' + investigate.ml_list(s, str)) + ';\n'
    code += r'''
fun wview (state,members) = wobject [
  ("\"original_state\"",fn () => wstate state),
  ("\"indexed_members\"",fn () => wf wmember members)];
fun wsubject (q,input) = wobject [
  ("\"previous_state\"",fn () => wview (N.indexed_history_view q)),
  ("\"requested_step\"",fn () => winput input)];
fun wsourceRow (key,input) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input\"",fn () => woption wsubject input)];
fun wsubjects subjects = wf wsourceRow subjects;
fun woutputRow (key,result) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input_result\"",fn () => woption (fn following => wobject [
    ("\"next_state\"",fn () => woption wview following)]) result)];
fun wprepared (subject,(reference,(typed,unguarded))) = wobject [
  ("\"subject\"",fn () => wsubject subject),
  ("\"original_reference\"",fn () => woption wview reference),
  ("\"actual_typed_result\"",fn () => woption (wview o N.history_index_state_view) typed),
  ("\"membership_omitted_result\"",fn () => woption (wview o N.history_index_state_view) unguarded)];
fun wpreparedRow (key,input) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input\"",fn () => woption wprepared input)];
'''
    code += stream_reader_comparison_json.prelude('woutputRow', 'wsubjects', 'history_index_inspect')
    code += r'''
fun wcontext (subjects,(prepared,reference)) = wobject [
  ("\"subject\"",fn () => wsubjects subjects),
  ("\"prepared_operations\"",fn () => wf wpreparedRow prepared),
  ("\"reference_readings\"",fn () => wf woutputRow reference)];
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun jcoverage (total,available) = "{\"certificate_positions\":" ^ jnat total ^
  ",\"available_positions\":" ^ jnat available ^ "}";
fun lookup label key rows = case List.find (fn (k,_) => k=key) rows of
  NONE => raise Fail ("Missing complete " ^ label ^ " row") | SOME (_,value) => value;
val () = emit "HISTORY_INDEX_SCOPE" (jlist jnat N.history_index_indices);
val () = let
val timer = Timer.startRealTimer ();
val (table,(comparison,cycles)) = N.history_index_packet scope selections;
val () = print ("Physicaltime history-index-packet " ^
  LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => wemit ("HISTORY_INDEX_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("HISTORY_INDEX_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "HISTORY_INDEX_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "HISTORY_INDEX_INVESTIGATION" (jcycle c)) cycles;
val () = List.app (fn (w,((subjects,(prepared,reference)),cells)) => emit ("HISTORY_INDEX_COVERAGE " ^ jnat w)
  (jcoverage (N.required_history_subject_coverage (N.history_index_original_family subjects)))) table;
val () = emit "HISTORY_INDEX_SOURCE_SCOPE" (jlist jnat (N.history_index_source_scope scope));
val previous = N.history_index_previous_cases scope;
val () = List.app (fn (w,old) => let
  val ((subjects,(prepared,reference)),cells) = lookup "subject" w table
  in wemit ("HISTORY_INDEX_SOURCE " ^ jnat w) (fn () => wobject [
    ("\"previous\"",fn () => wf woriginalSourceRow old),
    ("\"projected\"",fn () => wf woriginalSourceRow (N.history_index_original_family subjects)),
    ("\"native_equal\"",fn () => print (Bool.toString (N.history_index_source_equal subjects old)))]) end) previous;
in () end;
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
        'Factor_History_Index_Investigation', 'history_index_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        rows = list(machine_reports.reports(path))
        assert rows[0]['tag'] == 'HISTORY_INDEX_SCOPE' and rows[0]['indices'] == []
        scope = rows[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        size = len(requested)
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'HISTORY_INDEX_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, rows[1 + i * size:1 + (i + 1) * size]))
        compared = rows[1 + 2 * size]
        assert compared['tag'] == 'HISTORY_INDEX_COMPARISON' and compared['value']['scope'] == requested
        start = 2 + 2 * size
        assert all(r['tag'] == 'HISTORY_INDEX_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], rows[start:start + len(inputs['selections'])]))
        start += len(inputs['selections'])
        assert all(r['tag'] == 'HISTORY_INDEX_COVERAGE' and r['indices'] == [w]
                   for w, r in zip(requested, rows[start:start + size]))
        start += size
        assert rows[start]['tag'] == 'HISTORY_INDEX_SOURCE_SCOPE' and rows[start]['indices'] == []
        source_scope = rows[start]['value']
        assert set(source_scope) <= set(requested)
        source_rows = rows[start + 1:]
        assert len(source_rows) == len(source_scope)
        assert all(r['tag'] == 'HISTORY_INDEX_SOURCE' and r['indices'] == [w]
                   for w, r in zip(source_scope, source_rows))
        assert len(rows) == 3 * size + 3 + len(inputs['selections']) + len(source_scope)
        return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': source_scope,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Every original source and policy field, ordered ledger, complete decoded '
                            'cache, actual request and shared operation result, optional candidate output, '
                            'native observation, comparison, revision and original source case is retained.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['History_Index_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=2400,
        question='Which indexed transitions preserve every original history field and exactly the '
                 'admitted predecessor relation through actual subsequent steps?',
        boundary='The closed type carries original history validity and complete index fidelity. '
                 'Whole original states and every decoded cache member are independently compared. '
                 'Replay, policy, material and allocation cost, whole workflow adequacy, complete '
                 'historical permission and reachability, native mathematical-proof admission and genesis remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
