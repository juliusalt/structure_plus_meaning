"""Shared complete native requirement-decision value serialization."""

PRELUDE = r'''
fun jo f NONE = "null" | jo f (SOME x) = f x;
fun jenv e = jenvironment (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e));
fun jsubject (e,(u,(r,(gs,xs)))) = "{\"environment\":" ^ jenv e ^ ",\"use\":" ^ juse u ^
  ",\"root\":" ^ jaddress r ^ ",\"requirements\":" ^ jlist (jgoalWith jsite) gs ^ ",\"terms\":" ^ jf jterm xs ^ "}";
fun jreference (p,expected) = "{\"program\":" ^ jprogram p ^ ",\"admitted_terms\":" ^ jf jterm expected ^ "}";
fun jevaluated (formed,(covered,(closed,(applications,(rules,answer))))) =
  "{\"formed\":" ^ Bool.toString formed ^ ",\"head_covered\":" ^ Bool.toString covered ^
  ",\"demand_closed\":" ^ Bool.toString closed ^ ",\"applications\":" ^ jf japplication applications ^
  ",\"rules\":" ^ jf (jruleWith jaddress jsite) rules ^ ",\"answer\":" ^ janswerWith jsite answer ^ "}";
fun joriginal (source,(supported,(demand,evaluated))) = "{\"source\":" ^ jsource source ^
  ",\"supported\":" ^ jo Bool.toString supported ^ ",\"demand\":" ^ jo (jf jcall) demand ^
  ",\"evaluation\":" ^ jo jevaluated evaluated ^ "}";
fun jresult (d,(e,(u,(p,(demand,(answer,(proofs,terms))))))) = "{\"definition\":" ^ jsite d ^
  ",\"environment\":" ^ jenv e ^ ",\"use\":" ^ juse u ^ ",\"program\":" ^ jprogram p ^
  ",\"demand\":" ^ jf jcall demand ^ ",\"answer\":" ^ jf jcall answer ^
  ",\"certificates\":" ^ jf jcertificate proofs ^ ",\"admitted_terms\":" ^ jf jterm terms ^ "}";
fun jchecked (certificate,checked) = "{\"certificate\":" ^ jcertificate certificate ^
  ",\"checked\":" ^ Bool.toString checked ^ "}";
fun jbody (source,(actual,(inspected,(precise,(complete,(preserved,(native,(answers,(proofs,terms))))))))) =
  "{\"actual_source\":" ^ jsource source ^ ",\"actual_evaluation\":" ^ jevaluated actual ^
  ",\"certificate_checks\":" ^ jf jchecked inspected ^ ",\"precise\":" ^ Bool.toString precise ^
  ",\"complete\":" ^ Bool.toString complete ^ ",\"preserved\":" ^ Bool.toString preserved ^
  ",\"native\":" ^ Bool.toString native ^ ",\"answers_exact\":" ^ Bool.toString answers ^
  ",\"proofs_sound_and_complete\":" ^ Bool.toString proofs ^ ",\"terms_exact\":" ^ Bool.toString terms ^ "}";
fun jassessment (ready,(body,rejected)) = "{\"ready\":" ^ Bool.toString ready ^
  ",\"result\":" ^ jo jbody body ^ ",\"rejected\":" ^ Bool.toString rejected ^ "}";
'''
