"""Compare complete digit replay recording, retaining original cause readings and sources."""
from pathlib import Path
import argparse
import json

import admission_goal_json
import cause_reading_json
import check_native_certificates as shared
import generation_program_json
import history_program_json
import execution_support as investigate
import machine_reports
import native_cause_json
import native_replay_json
import native_stream_json
import observation_contracts
import proved_code
import replay_program_json
import requirement_decision_json


def program(engine, inputs):
    code = shared.source_preamble(engine, inputs, 'Digit_Replay_Execution', 'digit_replay_indices')
    code += shared.native_graph_json.prelude('jsite') + admission_goal_json.PRELUDE
    code += shared.investigation_json.CYCLE
    code += 'structure Decision_JSON = struct\n' + requirement_decision_json.PRELUDE + '\nend;\n'
    code += 'structure Replay_JSON = struct\n' + native_replay_json.PRELUDE + '\nend;\n'
    code += native_stream_json.PRELUDE + generation_program_json.PRELUDE
    code += history_program_json.PRELUDE + native_cause_json.SUBJECT
    code += cause_reading_json.PRELUDE + replay_program_json.PRELUDE
    code += r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jreplayRow (certificate,result) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"result\":" ^ Replay_JSON.jresult result ^ "}";
fun jdecision (decision,replays) = "{\"decision\":" ^ Decision_JSON.jresult decision ^
  ",\"replays\":" ^ jf jreplayRow replays ^ "}";
fun jseed seed = jo (fn (e,(u,(r,(a,decision)))) => "{\"environment\":" ^ jenv e ^
  ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^
  ",\"payload\":" ^ jartifact (N.finite_artifact_rows a) ^
  ",\"decision_replay\":" ^ jo jdecision decision ^ "}") seed;
fun wsubject x = wreplaySubjectView (N.digit_replay_subject_view x);
fun wkeyed write (key,input) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input\"",fn () => woption write input)];
fun wresultRow (key,result) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"result_family\"",fn () => woption (wf wreplayValue) result)];
fun wvariant (k,result) = wobject [
  ("\"variant\"",fn () => print (jnat k)),
  ("\"readings\"",fn () => wf wreplayValue result)];
fun wprepared (x,(reference,variants)) = wobject [
  ("\"subject\"",fn () => wsubject x),
  ("\"reference_readings\"",fn () => wf wreplayValue reference),
  ("\"prepared_operations\"",fn () => wlist wvariant variants)];
fun wcauseAssessment (value,cause) = wobject [
  ("\"value\"",fn () => wreplayValue value),
  ("\"cause\"",fn () => woption (fn (x,(report,certified)) => wobject [
    ("\"subject\"",fn () => wcause x),
    ("\"readings\"",fn () => wcauseReport report),
    ("\"certified\"",fn () => print (Bool.toString certified))]) cause)];
fun wrowAssessment (result,(reference,causes)) = wobject [
  ("\"readings\"",fn () => wf wreplayValue result),
  ("\"reference_readings\"",fn () => wf wreplayValue reference),
  ("\"original_causes\"",fn () => wf wcauseAssessment causes)];
fun wassessment (result,(reference,(covered,rows))) = wobject [
  ("\"results\"",fn () => wf wresultRow result),
  ("\"reference_results\"",fn () => wf wresultRow reference),
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"per_input_results_before_family_changes\"",fn () => wf (wkeyed wrowAssessment) rows)];
fun wcandidate (m,assessment) = wobject [
  ("\"method\"",fn () => print (jnat m)),
  ("\"assessment\"",fn () => wassessment assessment)];
fun wcontext (subjects,(covered,(prepared,reference))) = wobject [
  ("\"subjects\"",fn () => wf (wkeyed wsubject) subjects),
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"prepared\"",fn () => wf (wkeyed wprepared) prepared),
  ("\"reference_results\"",fn () => wf wresultRow reference)];
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,assessment) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.digit_replay_family_inspect assessment f)) facets) ^ "}";
fun wliteralSourceRow (certificate,result) = wobject [
  ("\"certificate\"",fn () => print (jcertificate certificate)),
  ("\"result\"",fn () => woption wliteralReplay result)];
fun wsourceCase write (w,rows) = wobject [
  ("\"case\"",fn () => print (jnat w)),
  ("\"rows\"",fn () => wf write rows)];
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun lookup label key rows = case List.find (fn (k,_) => k=key) rows of
  NONE => raise Fail ("Missing complete " ^ label ^ " row") | SOME (_,value) => value;
val () = emit "DIGIT_REPLAY_SCOPE" (jlist jnat N.digit_replay_indices);
val () = wemit "DIGIT_REPLAY_SEEDS" (fn () => wobject [
  ("\"literal_seed\"",fn () => print (jseed N.literal_replay_seed)),
  ("\"history_seed\"",fn () => print (jo jdecision N.required_history_seed_replays)),
  ("\"initial_generation_source\"",fn () => wgenerationProblem N.digit_replay_initial_material_source)]);
val () = wemit "DIGIT_REPLAY_PREVIOUS_SOURCES" (fn () => wobject [
  ("\"literal_replays\"",fn () => wlist (wsourceCase wliteralSourceRow) N.digit_replay_literal_sources),
  ("\"required_histories\"",fn () => wlist (wsourceCase woriginalSourceRow) N.digit_replay_history_sources)]);
val () = let
val (table,(comparison,cycles)) = N.digit_replay_packet scope selections;
val () = List.app (fn (w,(context,cells)) => wemit ("DIGIT_REPLAY_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("DIGIT_REPLAY_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "DIGIT_REPLAY_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "DIGIT_REPLAY_INVESTIGATION" (jcycle c)) cycles;
val () = emit "DIGIT_REPLAY_SOURCE_SCOPE" (jlist jnat (N.digit_replay_source_scope scope));
val () = List.app (fn (w,(initial,original)) => let
  val ((subjects,(covered,(prepared,reference))),cells) = lookup "subject" w table
  in wemit ("DIGIT_REPLAY_SOURCE " ^ jnat w) (fn () => wobject [
    ("\"initial_original_inputs\"",fn () => wf (wkeyed wreplayOriginalInput) initial),
    ("\"reference_inputs\"",fn () => wf (wkeyed wreplaySubjectView) original),
    ("\"projected_inputs\"",fn () => wf (wkeyed wsubject) subjects),
    ("\"construction_steps\"",fn () => print (jnat (N.digit_replay_chain_length w))),
    ("\"native_equal\"",fn () => print (Bool.toString (N.digit_replay_source_equal subjects original)))]) end)
  (N.digit_replay_source_cases scope);
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
        'Factor_Digit_Replay_Investigation', 'digit_replay_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')

    def assess(inputs, raw):
        path = args.output / 'results.log'
        assert path.read_text() == raw
        reports = list(machine_reports.reports(path))
        assert reports[0]['tag'] == 'DIGIT_REPLAY_SCOPE' and reports[0]['indices'] == []
        scope = reports[0]['value']
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        assert reports[1]['tag'] == 'DIGIT_REPLAY_SEEDS' and reports[1]['indices'] == []
        assert reports[2]['tag'] == 'DIGIT_REPLAY_PREVIOUS_SOURCES' and reports[2]['indices'] == []
        size = len(requested)
        for i, tag in enumerate(['SUBJECT', 'ASSESSMENT']):
            assert all(r['tag'] == 'DIGIT_REPLAY_' + tag and r['indices'] == [w]
                       for w, r in zip(requested, reports[3 + i * size:3 + (i + 1) * size]))
        compared = reports[3 + 2 * size]
        assert compared['tag'] == 'DIGIT_REPLAY_COMPARISON' and compared['value']['scope'] == requested
        start = 4 + 2 * size
        assert all(r['tag'] == 'DIGIT_REPLAY_INVESTIGATION' and r['value']['selected'] == selection
                   for selection, r in zip(inputs['selections'], reports[start:start + len(inputs['selections'])]))
        start += len(inputs['selections'])
        assert reports[start]['tag'] == 'DIGIT_REPLAY_SOURCE_SCOPE' and reports[start]['indices'] == []
        source_scope = reports[start]['value']
        assert source_scope == requested
        source_rows = reports[start + 1:]
        assert len(source_rows) == len(source_scope)
        assert all(r['tag'] == 'DIGIT_REPLAY_SOURCE' and r['indices'] == [w]
                   for w, r in zip(source_scope, source_rows))
        assert len(reports) == 2 * size + 5 + len(inputs['selections']) + len(source_scope)
        return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': source_scope,
                'reproduction_boundary': machine_reports.boundary(path),
                'boundary': 'Complete original literal and history inputs, optional states, full bounded replay '
                            'results, all original certified-cause readings, actual comparisons and every revision '
                            'reason are native outputs. The host checks reproduction and presentation only.'}

    result = proved_code.checked_execution(args.proof, args.poly, args.output,
        required_theories=['Digit_Replay_Execution'],
        inputs={'candidates': contract['candidate_indices'], 'facets': contract['facet_indices'],
                'cases': args.cases, 'selections': [[], [0], [0, 1]]},
        input_paths=[Path(__file__), *(Path(c['path']) for c in contracts)],
        program=program, assess=assess, project=args.project.resolve(), timeout=3600,
        question='Which complete persistent digit replay recordings preserve the independently established '
                 'bounded operation and original certified-cause meaning on the actual original and subsequent inputs?',
        boundary='Registered original-subject equations distinguish complete operation equality, generation '
                 'validity, certified cause meaning, optional preparation and every certificate key. Actual '
                 'history adoption, full physical cost, all six workflow conditions, historical permission '
                 'and reachability, native mathematical-proof admission, genesis and final audit remain open.')
    print(json.dumps({'status': result['status'], 'error': result.get('error'),
                      'reports': result.get('assessment', {}).get('reproduction_boundary')}))
    return int(result['status'] != 'accepted')


if __name__ == '__main__':
    raise SystemExit(main())
