from pathlib import Path
import datetime,fcntl,gzip,json,os,re,sys,time
base=Path('/tmp/native-control-segment4-20260918')
source=base/'source-v7'
sys.path.insert(0,str(source/'tools'))
import isabelle_native_execution,check_presented_report,native_stage_timing,execution_support,investigation_json
mode=sys.argv[1];assert mode in ['review','consume']
output=base/('judgment-scope-'+mode)
proof=base/'scope-export/native_control_judgment.proof.json'
poly=Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
registry=Path('/home/julius/structure_and_semantics/.overnight/JOBS.json')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(entry):
    with (base/'jobs.lock').open('w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        j=json.loads(registry.read_text());j['jobs']=[x for x in j['jobs'] if x['id']!=entry['id']]+[entry]
        j['active_jobs']=[x['id'] for x in j['jobs'] if x.get('status')=='running']
        tmp=registry.with_suffix('.json.tmp');tmp.write_text(json.dumps(j,indent=2)+'\n');tmp.replace(registry)
view=r'''
fun jnat n = Int.toString (N.integer_of_nat n);
fun jlist f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
fun joption f NONE = "null" | joption f (SOME x) = f x;
fun jtermword t = "\"" ^ String.implode (rev (N.finite_term_shared_word_fold
  (fn xs => fn b => (if b then #"1" else #"0") :: xs) t [])) ^ "\"";
'''+investigation_json.PRELUDE+investigation_json.CYCLE+r'''
fun jcomparison (rows,(relation,(selected,adequate))) =
 "{\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
 ",\"selected\":" ^ jlist jnat selected ^ ",\"adequate\":" ^ jlist jnat adequate ^ "}";
fun jcell (m,(a,(b,(c,(d,e))))) = "[" ^ jnat m ^ "," ^ jlist Bool.toString [a,b,c,d,e] ^ "]";
fun jcontext (w,cells) = "[" ^ jnat w ^ "," ^ jlist jcell cells ^ "]";
fun jresult (m,(claim,(admitted,(comparison,cycle)))) =
 "{\"method\":" ^ jnat m ^ ",\"claim_words\":" ^ joption (jlist jtermword) claim ^
 ",\"admitted_words\":" ^ joption (jlist jtermword) admitted ^
 ",\"comparison\":" ^ joption jcomparison comparison ^ ",\"cycle\":" ^ joption jcycle cycle ^ "}";
fun jsummary (chosen,(cells,results)) = "{\"chosen\":" ^ joption jnat chosen ^
 ",\"all_assessments\":" ^ jlist jcontext cells ^ ",\"results\":" ^ joption (jlist jresult) results ^ "}";
fun jreceived (i,flags) = "[" ^ jnat i ^ "," ^ joption (jlist Bool.toString) flags ^ "]";
'''
def program(engine,inputs):
    report='judgment_bridge_value' if mode=='review' else 'judgment_bridge_receiving_value'
    code=check_presented_report.program(engine,{'module':'Native_Control_Judgment','report':report,
        'scope':'runtime_result','selections':None},output/'report.word')
    loading='use '+execution_support.ml_string(str(engine))+';\nstructure N = Native_Control_Judgment;\n'
    assert code.count(loading)==1
    body=view+native_stage_timing.PRELUDE+r'''
val steering_questions = native_stage_timed "steering_questions" (fn () => N.judgment_steering_questions ());
val requests = native_stage_timed "original_requests" (fn () => [Option.valOf (N.judgment_bridge_question ())]);
val reviewed = native_stage_timed "native_review" (fn () => N.native_steered_development steering_questions requests);
val () = print ("NATIVE_REVIEW_SUMMARY_BEGIN\n" ^ jsummary (N.context_execution_summary reviewed) ^ "\nNATIVE_REVIEW_SUMMARY_END\n");
'''
    if mode=='consume':
        body+=r'''
val receiving = native_stage_timed "receiving_program" (fn () =>
  case #2 (#2 (#2 reviewed)) of SOME [(_,(_,(report,_)))] => N.judgment_bridge_receive report | _ => NONE);
val () = print ("NATIVE_RECEIVING_BEGIN\n" ^ joption (jlist jreceived) (N.judgment_bridge_receive_summary receiving) ^ "\nNATIVE_RECEIVING_END\n");
val report_value = native_stage_timed "presentation" (fn () => N.judgment_bridge_receiving_value (reviewed,receiving));
'''
    else:
        body+='val report_value = native_stage_timed "presentation" (fn () => N.judgment_bridge_value reviewed);\n'
    code=code.replace(loading,loading+body).replace('N.'+report+' N.runtime_result','report_value')
    fold='N.finite_term_shared_word_fold sink (report_value) (0, 0)'
    assert code.count(fold)==1
    code=code.replace(fold,'native_stage_timed "word" (fn () => '+fold+')')
    return code+'val () = print "CHECKED_JUDGMENT_EXECUTION_COMPLETED\\n";\n'
def assess(inputs,log):
    text=gzip.open(log,'rt').read();assert 'CHECKED_JUDGMENT_EXECUTION_COMPLETED' in text
    summary=json.loads(text.split('NATIVE_REVIEW_SUMMARY_BEGIN\n')[1].split('\nNATIVE_REVIEW_SUMMARY_END')[0])
    receiving=(json.loads(text.split('NATIVE_RECEIVING_BEGIN\n')[1].split('\nNATIVE_RECEIVING_END')[0]) if mode=='consume' else 'UNEXECUTED')
    word=check_presented_report.retain_word(output/'report.word',output/'report.word.gz');(output/'report.word').unlink()
    stages=re.findall(r'Physicalstage ([a-z_]+) wall=([0-9.]+) user=([0-9.]+) system=([0-9.]+)',text)
    return {'physical_completion':True,'mode':mode,'native_summary':summary,'receiving_summary':receiving,
        'complete_report_word':word,'timings':[dict(zip(('stage','wall','user','system'),r)) for r in stages],
        'scope':'Complete native results and physical integrity; no host satisfaction, authority or policy decision.'}
pid=os.getpid();started=time.monotonic()
entry={'id':'segment4-judgment-scope-'+mode,'pid':pid,'pid_namespace':os.readlink('/proc/self/ns/pid'),
    'proc_start_ticks':Path('/proc/self/stat').read_text().split()[21],'started_utc':utc(),
    'command':sys.argv,'observed_command':Path('/proc/self/cmdline').read_bytes().replace(b'\0',b' ').decode(),
    'immutable_working_directory':str(source),'input_boundary':str(proof),'output':str(output),
    'log':str(output/'results.log.gz'),'status':'running',
    'accepted_completion':'Exit 0; complete marker, stable live/archived inputs, complete native reports, all results reviewed. Physical execution only; no policy adoption.'}
save(entry);print(json.dumps({'started':entry['id'],'pid':pid,'utc':entry['started_utc']}),flush=True)
r=isabelle_native_execution.checked_execution(proof,poly,output,workers=8,program=program,
    input_paths=[Path(__file__),Path(check_presented_report.__file__),Path(native_stage_timing.__file__)],
    required_theories=['Native_Control_Judgment_Scope'],
    inputs={'mode':mode,'steering':'Actual seed-union and checked syntax-judgment questions',
        'request':'Original twelve-subject judgment-bridge question'},assess=assess,
    question='Resolve the observed producer ambiguity using both original real questions; re-admit the original judgment request before any receiving evaluation.',
    boundary='Full checked rooted contexts/propositions, computed original observations, original native criticism/admission and exact receiving-program contract. Generic HOL interpretation and governing policy remain separate.',
    timeout=180,project=source)
entry.update(status='exited',exit_code=0 if r['status']=='accepted' else 1,finished_utc=utc(),
    seconds=round(time.monotonic()-started,3),receipt=str(output/'receipt.json'),physical_status=r['status'],error=r.get('error'))
save(entry);print(json.dumps(entry,indent=2),flush=True)
raise SystemExit(entry['exit_code'])
