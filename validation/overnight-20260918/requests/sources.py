from pathlib import Path
import ast,gzip,json,re,sys
base=Path('/tmp/native-control-segment9-20260918')
source_name,export_name,label=sys.argv[1:]
source=base/source_name;output=base/label
sys.path.insert(0,str(source/'tools'))
import isabelle_native_execution,check_presented_report,native_stage_timing,execution_support,investigation_json
native_stage_timing.PRELUDE=native_stage_timing.PRELUDE.replace('in result end;','in TextIO.flushOut TextIO.stdOut; result end;')
proof=base/export_name/'native_control_source_execution.proof.json'
poly=Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
presenter=Path('/tmp/native-control-segment4-20260918/execute_scope.py')
tree=ast.parse(presenter.read_text())
node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='view' for t in n.targets))
view=eval(compile(ast.Expression(node),'<retained diagnostic presenter>','eval'),{'investigation_json':investigation_json})
words={'review':'N.judgment_artifact_value reviewed','sources':'N.guard_source_records_value sources'}
def program(engine,inputs):
    loading='use '+execution_support.ml_string(str(engine))+';\nstructure N = Native_Control_Source_Execution;\n'
    code=loading+view+native_stage_timing.PRELUDE+r'''
fun jsource (i,s) = "[" ^ jnat i ^ "," ^ joption (fn (a,(b,c)) =>
 "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "]") s ^ "]";
fun marker name value = (print (name ^ "_BEGIN\n" ^ value ^ "\n" ^ name ^ "_END\n"); TextIO.flushOut TextIO.stdOut);
val steering = native_stage_timed "steering_questions" (fn () => N.judgment_steering_questions ());
val questions = native_stage_timed "original_questions" (fn () =>
 [Option.valOf (N.judgment_bridge_question ()),Option.valOf (N.judgment_artifact_execution_question ()),
  Option.valOf (N.guard_representation_execution_question ())]);
val reviewed = native_stage_timed "original_native_admission" (fn () => N.native_steered_development steering questions);
val (body,adapter,target) = case #2 (#2 (#2 reviewed)) of
 SOME [(_,(_,(a,_))),(_,(_,(b,_))),(_,(_,(c,_)))] => (a,b,c)
 | _ => raise Fail "Original native reports unavailable";
val () = marker "SOURCE_NATIVE_SUMMARY" (jsummary (N.context_execution_summary reviewed));
val sources = native_stage_timed "actual_installed_source_and_coordinates" (fn () =>
 N.admitted_guard_source_records body adapter target);
val () = marker "SOURCE_RECORDS" (joption (jlist jsource) (N.guard_source_records_summary sources));
val refused = native_stage_timed "absent_original_reports" (fn () => map (fn (a,b,c) =>
 N.guard_source_records_summary (N.admitted_guard_source_records a b c))
 [(N.absent_development_report,adapter,target),(body,N.absent_development_report,target),
  (body,adapter,N.absent_development_report)]);
val () = marker "SOURCE_REFUSALS" (jlist (joption (jlist jsource)) refused);
'''
    for name,expression in words.items():
        fragment=check_presented_report.program(engine,{'module':'Native_Control_Source_Execution',
          'report':'guard_source_records_value','scope':'runtime_result','selections':None},output/(name+'.word'))
        assert fragment.count(loading)==1
        fragment=fragment.replace(loading,'').replace('N.guard_source_records_value N.runtime_result','report_value')
        code+='val report_value = native_stage_timed "'+name+'_presentation" (fn () => '+expression+');\n'+fragment
    return code+'val () = print "CHECKED_GUARD_SOURCES_COMPLETED\\n";\n'
def assess(inputs,log):
    text=gzip.open(log,'rt').read();assert 'CHECKED_GUARD_SOURCES_COMPLETED' in text
    def block(name):return json.loads(text.split(name+'_BEGIN\n')[1].split('\n'+name+'_END')[0])
    identities={}
    for name in words:
        identities[name]=check_presented_report.retain_word(output/(name+'.word'),output/(name+'.word.gz'))
        (output/(name+'.word')).unlink()
    return {'physical_completion':True,'native_summary':block('SOURCE_NATIVE_SUMMARY'),
      'source_records':block('SOURCE_RECORDS'),'original_refusals':block('SOURCE_REFUSALS'),'words':identities,
      'timings':[dict(zip(('stage','wall','user','system'),x)) for x in
       re.findall(r'Physicalstage ([a-z_]+) wall=([0-9.]+) user=([0-9.]+) system=([0-9.]+)',text)],
      'scope':'Original reports gate complete installation, actual finite_native_source recovery and definition coordinates. No source inferred from availability, no natural-to-native proof-tree conversion, replay or policy cause claimed.'}
r=isabelle_native_execution.checked_execution(proof,poly,output,workers=8,program=program,
 input_paths=[Path(__file__),presenter,Path(check_presented_report.__file__),Path(native_stage_timing.__file__)],
 required_theories=['Native_Control_Source_Execution'],
 inputs={'originals':'All three original native reports recomputed; every installation occurrence retained.',
         'source':'The original finite_native_source reader returns the complete actual program.',
         'refusals':'Omit each original report separately.',
         'presentation':'guard_source_records_value_injective preserves all original and installed source fields.'},
 assess=assess,question='Recover the actual source and complete definition-coordinate map for every originally admitted installed guard.',
 boundary='finite_install_quoted_guard_transport, guard_source_record_fields, admitted_guard_source_records_projection/original. No proof-tree transport or certificate supplied by source existence.',
 timeout=180,project=source)
print(json.dumps({k:r[k] for k in ['status','error','error_type'] if k in r}))
raise SystemExit(0 if r['status']=='accepted' else 1)
