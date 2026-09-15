"""Serialize complete allocation states, operations and counted insertion paths."""

STATE = r'''
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
'''

PATHS = r'''
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
'''

VIEWED_SUBJECT = r'''
fun jviewedSubject (input,operation) = "{\"prepared_state\":" ^ jo jstate input ^
  ",\"operation\":" ^ joperation operation ^ "}";
'''
