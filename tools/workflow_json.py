"""Serialize every field of a complete native workflow source, trace and assessment."""

PRELUDE = r'''
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun joutputScope N.Workflow_Input = "{\"input\":true}"
  | joutputScope (N.Workflow_Values xs) = "{\"values\":" ^ jlist jterm xs ^ "}"
  | joutputScope (N.Workflow_Generated entry) = "{\"generated_entry\":" ^ jsite entry ^ "}";
fun jstage s = "{\"source\":" ^ jenv (N.workflow_source s) ^
  ",\"source_use\":" ^ juse (N.workflow_source_use s) ^
  ",\"source_root\":" ^ jaddress (N.workflow_source_root s) ^
  ",\"entry\":" ^ jsite (N.workflow_entry s) ^
  ",\"output_scope\":" ^ joutputScope (N.workflow_outputs s) ^ "}";
fun jworkflowSubject (w,p) = "{\"stages\":" ^ jlist jstage (N.development_workflow_stages w) ^
  ",\"problem\":" ^ jterm p ^ "}";
fun jgoal (N.Existing_Admission d) = "{\"existing\":" ^ jsite d ^ "}"
  | jgoal (N.Paired_Admission (a,b)) = "{\"paired\":[" ^ jgoal a ^ "," ^ jgoal b ^ "]}"
  | jgoal (N.Collected_Admission a) = "{\"collected\":" ^ jgoal a ^ "}";
fun jrequirement r = "{\"source\":" ^ jenv (N.requirement_source r) ^
  ",\"source_use\":" ^ juse (N.requirement_source_use r) ^
  ",\"source_root\":" ^ jaddress (N.requirement_source_root r) ^
  ",\"goals\":" ^ jlist jgoal (N.requirement_goals r) ^
  ",\"candidates\":" ^ joutputScope (N.requirement_candidates r) ^ "}";
fun jrequiredSubject (r,p) = "{\"requirements\":" ^ jlist jrequirement (N.development_workflow_requirements r) ^
  ",\"problem\":" ^ jterm p ^ "}";
fun jstageResult (p,(d,(a,(t,ys)))) = "{\"program\":" ^ jprogram p ^
  ",\"demand\":" ^ jf jcall d ^ ",\"answers\":" ^ jf jcall a ^
  ",\"certificates\":" ^ jf jcertificate t ^ ",\"outputs\":" ^ jlist jterm ys ^ "}";
fun jgeneratedRow ((d,c),(t,(v,h))) = japplication (d,(c,(t,(v,h))));
fun jgeneration NONE = "null"
  | jgeneration (SOME (p,(d,(a,rows)))) = "{\"program\":" ^ jprogram p ^
      ",\"demand\":" ^ jf jcall d ^ ",\"answers\":" ^ jf jcall a ^
      ",\"applications\":" ^ jlist jgeneratedRow rows ^ "}";
fun jscopeGeneration s input = case N.workflow_outputs s of N.Workflow_Generated _ =>
    jgeneration (N.finite_native_generation (N.workflow_source s) (N.workflow_source_use s)
      (N.workflow_source_root s) input)
  | _ => "null";
fun jexecution (N.Workflow_Finished ys) = "{\"finished\":" ^ jlist jterm ys ^ "}"
  | jexecution (N.Workflow_Unavailable (s,input)) =
      "{\"unavailable\":{\"stage\":" ^ jstage s ^ ",\"input\":" ^ jterm input ^
      ",\"generation\":" ^ jscopeGeneration s input ^ "}}"
  | jexecution (N.Workflow_Executed (s,input,result,children)) =
      "{\"executed\":{\"stage\":" ^ jstage s ^ ",\"input\":" ^ jterm input ^
      ",\"generation\":" ^ jscopeGeneration s input ^
      ",\"result\":" ^ jstageResult result ^ ",\"children\":" ^
      jlist (fn (y,child) => "{\"value\":" ^ jterm y ^ ",\"execution\":" ^ jexecution child ^ "}") children ^ "}}";
fun jworkflowAssessment (paths,(reference,valid)) = "{\"paths\":" ^ jlist (jlist jterm) paths ^
  ",\"reference_paths\":" ^ jlist (jlist jterm) reference ^ ",\"trace_valid\":" ^ Bool.toString valid ^ "}";
fun jquality (f,b) = "[" ^ jnat f ^ "," ^ Bool.toString b ^ "]";
fun jworkflowAssessed (m,(actual,assessment)) = "{\"method\":" ^ jnat m ^
  ",\"assessment\":" ^ jworkflowAssessment assessment ^ ",\"qualities\":" ^
  jlist jquality (map (fn f => (f,N.native_workflow_inspect assessment f)) facets) ^ "}";
'''
