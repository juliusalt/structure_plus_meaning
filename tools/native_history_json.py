"""Serialize complete original native history inputs and call differences."""

SOURCE = r'''
fun jcall q = jcallWith jsite q;
fun japplication a = japplicationWith jaddress jaddress jsite jaddress a;
fun jstep (x,w) = "{\"before\":" ^ jf jcall x ^ ",\"applications\":" ^ jf japplication w ^ "}";
fun jsource NONE = "null" | jsource (SOME p) = jprogram p;
fun jdetails NONE = "null"
  | jdetails (SOME (formed,(covered,(closed,applications)))) =
      "{\"formed\":" ^ Bool.toString formed ^ ",\"head_covered\":" ^ Bool.toString covered ^
      ",\"demand_closed\":" ^ Bool.toString closed ^ ",\"applications\":" ^ jf japplication applications ^ "}";
fun jevaluation NONE = "null" | jevaluation (SOME (p,a)) =
  "{\"program\":" ^ jprogram p ^ ",\"answer\":" ^ jf jcall a ^ "}";
fun jcoverage (d,(heads,result)) =
  "{\"expanded_demand\":" ^ jf jcall d ^ ",\"all_source_heads_covered\":" ^
    (case heads of NONE => "null" | SOME b => Bool.toString b) ^
    ",\"expanded_evaluation\":" ^ jevaluation result ^ "}";
fun jreference (source,(details,(result,coverage))) =
  "{\"source\":" ^ jsource source ^ ",\"details\":" ^ jdetails details ^
  ",\"evaluation\":" ^ jevaluation result ^ ",\"coverage\":" ^ jcoverage coverage ^ "}";
fun jproblem (e,(u,(r,d))) =
  "{\"environment\":" ^ jenvironment
    (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e)) ^
  ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^ ",\"demand\":" ^ jf jcall d ^ "}";'''

DIFFERENCES = r'''
fun jdifferences NONE = "null"
  | jdifferences (SOME (extra,missing)) = "{\"extra\":" ^ jf jcall extra ^
      ",\"missing\":" ^ jf jcall missing ^ "}";'''
