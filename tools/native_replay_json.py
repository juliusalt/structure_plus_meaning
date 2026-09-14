"""Shared complete native replay value and assessment serialization."""

PRELUDE = r'''
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jsubject (e,(u,(r,(p,(d,t))))) = "{\"environment\":" ^ jenv e ^
  ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^ ",\"proof\":" ^ jproof p ^
  ",\"call\":" ^ jcall (d,t) ^ "}";
fun jreference NONE = "null"
  | jreference (SOME (p,checked)) = "{\"program\":" ^ jprogram p ^
      ",\"certificate_checked\":" ^ Bool.toString checked ^ "}";
fun jmapping m = jf (fn (n,s) => "[" ^ jinstantiated n ^ "," ^ jsite s ^ "]") m;
fun japplicationReading (q,(i,k)) = "{\"call\":" ^ jcall q ^ ",\"interior\":" ^ jf jaddress i ^
  ",\"slots\":" ^ jf jaddress k ^ "}";
fun jassertions h = jf (fn (n,q) => "[" ^ jsite n ^ "," ^ jcall q ^ "]") h;
fun jresult NONE = "null"
  | jresult (SOME (a,(m,(root,(g,(au,(i,(k,b)))))))) =
      "{\"environment\":" ^ jenv a ^ ",\"mapping\":" ^ jmapping m ^ ",\"root\":" ^ jsite root ^
      ",\"graph\":" ^ jgraphWith jsite g ^ ",\"application_use\":" ^ juse au ^
      ",\"interior\":" ^ jf jaddress i ^ ",\"slots\":" ^ jf jaddress k ^
      ",\"retained_environment\":" ^ jenv b ^ "}";
fun jgraphInspection NONE = "null"
  | jgraphInspection (SOME (readings,(recovery,(mapping,(source,(fresh,injective)))))) =
      "{\"readings\":" ^ jf (jgraphWith jsite) readings ^ ",\"recovered\":" ^ Bool.toString recovery ^
      ",\"mapping_exact\":" ^ Bool.toString mapping ^ ",\"source_preserved\":" ^ Bool.toString source ^
      ",\"fresh\":" ^ Bool.toString fresh ^ ",\"injective\":" ^ Bool.toString injective ^ "}";
fun jreadings (ps,(apps,(expected,(keptps,(keptapps,(keptgs,replay)))))) =
  "{\"source_readings\":" ^ jf jprogram ps ^ ",\"application_readings\":" ^ jf japplicationReading apps ^
  ",\"expected_retained_environment\":" ^ jenv expected ^
  ",\"retained_source_readings\":" ^ jf jprogram keptps ^
  ",\"retained_application_readings\":" ^ jf japplicationReading keptapps ^
  ",\"retained_graph_readings\":" ^ jf (jgraphWith jsite) keptgs ^
  ",\"replay_readings\":" ^ jf jassertions replay ^ "}";
fun jbody NONE = "null"
  | jbody (SOME (graph,(readings,(source,(boundary,(retained,closed)))))) =
      "{\"graph\":" ^ jgraphInspection graph ^ ",\"readings\":" ^ jreadings readings ^
      ",\"original_source_and_call\":" ^ Bool.toString source ^ ",\"boundary_exact\":" ^ Bool.toString boundary ^
      ",\"retained_recovery\":" ^ Bool.toString retained ^ ",\"closed_replay\":" ^ Bool.toString closed ^ "}";
fun jassessment (ready,(body,rejected)) = "{\"ready\":" ^ Bool.toString ready ^
  ",\"result\":" ^ jbody body ^ ",\"rejected\":" ^ Bool.toString rejected ^ "}";
'''
