"""Compare complete persistent digit histories under original policy and membership conditions."""
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


def program(engine,inputs):
    code='use '+investigate.ml_string(str(engine))+';\nstructure N = Digit_History_Execution;\n'
    code+=check_reasoning.SCALAR_JSON_PRELUDE
    code+=native_program_json.COORDINATES+native_program_json.ARTIFACT_ROWS+native_program_json.TARGETS
    code+=program_evaluation_json.PRELUDE+'\nfun jcall q = jcallWith jsite q;\n'
    code+=native_certificate_json.PROOFS+admission_goal_json.PRELUDE
    code+=investigation_json.PRELUDE+investigation_json.CYCLE+native_stream_json.PRELUDE+history_program_json.PRELUDE
    code+='val facets = map N.nat_of_integer '+investigate.ml_list(inputs['facets'],str)+';\n'
    scope='N.digit_history_indices' if inputs['cases'] is None else 'map N.nat_of_integer '+investigate.ml_list(inputs['cases'],str)
    code+='val scope = '+scope+';\n'
    code+='val selections = '+investigate.ml_list(inputs['selections'],lambda s:'map N.nat_of_integer '+investigate.ml_list(s,str))+';\n'
    code+=r'''
fun wview (n,(state,members)) = wobject [
  ("\"next_head\"",fn () => print (jnat n)),
  ("\"original_state\"",fn () => wstate state),
  ("\"indexed_members\"",fn () => wf wmember members)];
fun wsubjectView (state,input) = wobject [
  ("\"previous_state\"",fn () => wview state),
  ("\"requested_step\"",fn () => winput input)];
fun wsubject x = wsubjectView (N.digit_history_subject_view x);
fun wboundedSubject x = wsubjectView (N.bounded_history_subject_view x);
fun wsourceRow write (key,input) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input\"",fn () => woption write input)];
fun woutputRow (key,result) = wobject [
  ("\"certificate\"",fn () => woption (wencoded jcertificate) key),
  ("\"input_result\"",fn () => woption (fn following => wobject [
    ("\"next_state\"",fn () => woption wview following)]) result)];
fun wrawResult result = woption (wview o N.digit_history_state_view) result;
fun wprepared (subject,(reference,(typed,(legacy,(unguarded,(noPolicy,noReplay)))))) = wobject [
  ("\"subject\"",fn () => wsubject subject),
  ("\"original_reference\"",fn () => woption wview reference),
  ("\"actual_typed_result\"",fn () => wrawResult typed),
  ("\"legacy_result\"",fn () => woption wview legacy),
  ("\"membership_omitted_result\"",fn () => wrawResult unguarded),
  ("\"policy_omitted_result\"",fn () => wrawResult noPolicy),
  ("\"replay_and_policy_omitted_result\"",fn () => wrawResult noReplay)];
fun wcontext (covered,(subjects,(prepared,reference))) = wobject [
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"subjects\"",fn () => wf (wsourceRow wsubject) subjects),
  ("\"prepared_operations\"",fn () => wf (wsourceRow wprepared) prepared),
  ("\"reference_readings\"",fn () => wf woutputRow reference)];
fun wresult (covered,(result,reference)) = wobject [
  ("\"covered\"",fn () => print (Bool.toString covered)),
  ("\"readings\"",fn () => wf woutputRow result),
  ("\"reference_readings\"",fn () => wf woutputRow reference)];
fun wcandidate (m,result) = wobject [
  ("\"method\"",fn () => print (jnat m)),
  ("\"result\"",fn () => wresult result)];
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jassessed (m,result) = "{\"method\":" ^ jnat m ^ ",\"qualities\":" ^ jlist jquality
  (map (fn f => (f,N.digit_history_question_inspect result f)) facets) ^ "}";
fun emit tag value = (print (tag ^ " " ^ value ^ "\n"); TextIO.flushOut TextIO.stdOut);
fun lookup label key rows = case List.find (fn (k,_) => k=key) rows of
  NONE => raise Fail ("Missing complete " ^ label ^ " row") | SOME (_,value) => value;
val () = emit "DIGIT_HISTORY_SCOPE" (jlist jnat N.digit_history_indices);
val () = let
val timer = Timer.startRealTimer ();
val (table,(comparison,cycles)) = N.digit_history_packet scope selections;
val () = print ("Physicaltime digit-history-packet " ^
  LargeInt.toString (Time.toMilliseconds (Timer.checkRealTimer timer)) ^ "ms\n");
val () = List.app (fn (w,(context,cells)) => wemit ("DIGIT_HISTORY_SUBJECT " ^ jnat w)
  (fn () => wobject [("\"context\"",fn () => wcontext context),
    ("\"candidates\"",fn () => wlist wcandidate cells)])) table;
val () = List.app (fn (w,(context,cells)) => emit ("DIGIT_HISTORY_ASSESSMENT " ^ jnat w)
  (jlist jassessed cells)) table;
val (rows,(relation,(selected,adequate))) = comparison;
val () = emit "DIGIT_HISTORY_COMPARISON" ("{\"scope\":" ^ jlist jnat scope ^
  ",\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}");
val () = List.app (fn c => emit "DIGIT_HISTORY_INVESTIGATION" (jcycle c)) cycles;
val () = emit "DIGIT_HISTORY_SOURCE_SCOPE" (jlist jnat (N.digit_history_source_scope scope));
val () = List.app (fn (w,(old,original)) => let
  val ((covered,(subjects,(prepared,reference))),cells) = lookup "subject" w table
  in wemit ("DIGIT_HISTORY_SOURCE " ^ jnat w) (fn () => wobject [
    ("\"initial_original_source\"",fn () => wf woriginalSourceRow old),
    ("\"reference_inputs\"",fn () => wf (wsourceRow wboundedSubject) original),
    ("\"projected_inputs\"",fn () => wf (wsourceRow wsubject) subjects),
    ("\"history_steps\"",fn () => print (jnat (N.digit_history_chain_length w))),
    ("\"native_equal\"",fn () => print (Bool.toString (N.digit_history_source_equal subjects original)))]) end)
  (N.digit_history_source_cases scope);
in () end;
'''
    return code


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['proof','poly','project','output']:parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--cases',type=int,nargs='+');args=parser.parse_args()
    if args.cases is not None:assert all(type(i) is int and i>=0 for i in args.cases)
    proof=json.loads(args.proof.read_text());contracts=proof['subject_contracts'];assert len(contracts)==1
    assert all(investigate.file_hash(Path(c['path']))==c['sha256'] for c in contracts)
    contract=observation_contracts.read_contract(Path(contracts[0]['path']),
        'Factor_Digit_History_Investigation','digit_history_investigation',
        observer='Finite_Subject_Investigation.subject_investigation_observations',
        relation='Finite_Subject_Investigation.subject_investigation_relation')
    def assess(inputs,raw):
        path=args.output/'results.log';assert path.read_text()==raw;rows=list(machine_reports.reports(path))
        assert rows[0]['tag']=='DIGIT_HISTORY_SCOPE' and rows[0]['indices']==[]
        scope=rows[0]['value'];requested=scope if inputs['cases'] is None else inputs['cases'];assert set(requested)<=set(scope)
        size=len(requested)
        for i,tag in enumerate(['SUBJECT','ASSESSMENT']):
            assert all(r['tag']=='DIGIT_HISTORY_'+tag and r['indices']==[w]
                for w,r in zip(requested,rows[1+i*size:1+(i+1)*size]))
        compared=rows[1+2*size];assert compared['tag']=='DIGIT_HISTORY_COMPARISON' and compared['value']['scope']==requested
        start=2+2*size
        assert all(r['tag']=='DIGIT_HISTORY_INVESTIGATION' and r['value']['selected']==selection
            for selection,r in zip(inputs['selections'],rows[start:start+len(inputs['selections'])]))
        start+=len(inputs['selections']);assert rows[start]['tag']=='DIGIT_HISTORY_SOURCE_SCOPE' and rows[start]['indices']==[]
        assert rows[start]['value']==requested
        assert len(rows)==3*size+3+len(inputs['selections'])
        assert all(r['tag']=='DIGIT_HISTORY_SOURCE' and r['indices']==[w] for w,r in zip(requested,rows[start+1:]))
        return {'complete_scope':scope,'executed_scope':requested,'original_source_scope':requested,
            'reproduction_boundary':machine_reports.boundary(path),
            'boundary':'Every original source, complete state, actual counter, ordered ledger and cache relation, '
                'prepared operation, full candidate value, coverage condition, comparison and revision is retained.'}
    result=proved_code.checked_execution(args.proof,args.poly,args.output,required_theories=['Digit_History_Execution'],
        inputs={'candidates':contract['candidate_indices'],'facets':contract['facet_indices'],
                'cases':args.cases,'selections':[[],[0],[0,1]]},
        input_paths=[Path(__file__),*(Path(c['path']) for c in contracts)],program=program,assess=assess,
        project=args.project.resolve(),timeout=3600,
        question='Which actual persistent digit history steps preserve the complete bounded original transition, '
            'every policy requirement and the entire ordered ledger and membership cache?',
        boundary='Actual digit generation and policy readers and indexed membership implement the complete '
            'original bounded history operation. Coverage requires an actual successful semantic transition. '
            'Full physical cost, whole workflow adequacy, all six workflow conditions, historical permission '
            'and reachability, native mathematical-proof admission, genesis and final audit remain open.')
    print(json.dumps({'status':result['status'],'error':result.get('error'),
        'reports':result.get('assessment',{}).get('reproduction_boundary')}))
    return int(result['status']!='accepted')


if __name__=='__main__':raise SystemExit(main())
