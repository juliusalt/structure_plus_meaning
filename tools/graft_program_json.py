"""Serialize complete graft input environments and their actual formation."""

SUBJECT = r'''
fun jvalue c = jartifact (N.finite_artifact_rows c);
fun jentry (u,c) = "[" ^ juse u ^ "," ^ jvalue c ^ "]";
fun jenv e = "{\"artifacts\":" ^ jf jentry (N.finite_environment_artifacts e) ^
  ",\"bindings\":" ^ jf jbinding (N.finite_environment_bindings e) ^ "}";
fun jsubject (original,(use,imported)) = "{\"original\":" ^ jenv original ^ ",\"boundary\":" ^ juse use ^
  ",\"imported\":" ^ jenv imported ^ ",\"original_formed\":" ^ Bool.toString (N.graft_view_formed original) ^
  ",\"imported_formed\":" ^ Bool.toString (N.graft_view_formed imported) ^ "}";
'''
