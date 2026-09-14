"""Serialize full query and supplied-certificate inputs and native checks."""

PRELUDE = r'''
fun jinput (N.Native_Certificate_Query x) =
    "{\"kind\":\"query\",\"query\":" ^ jproblemOption x ^ "}"
  | jinput (N.Native_Certificate_Supplied (e,u,r,a,t)) =
    "{\"kind\":\"supplied\",\"environment\":" ^ jenvironment
      (N.finite_environment_artifact_rows e,elements (N.finite_environment_bindings e)) ^
    ",\"use\":" ^ juse u ^ ",\"root\":" ^ jaddress r ^
    ",\"answer\":" ^ jf jcall a ^ ",\"certificates\":" ^ jf jcertificate t ^ "}";
fun jsuppliedInspection NONE = "null"
  | jsuppliedInspection (SOME (p,(covered,rows))) = "{\"program\":" ^ jprogram p ^
    ",\"answer_covered\":" ^ Bool.toString covered ^ ",\"proof_checks\":" ^
    jf (fn (n,b) => "{\"certificate\":" ^ jcertificate n ^
      ",\"checked\":" ^ Bool.toString b ^ "}") rows ^ "}";
fun jinputReport x = "{\"input\":" ^ jinput x ^ ",\"supplied_inspection\":" ^
  jsuppliedInspection (N.native_certificate_input_supplied_inspection x) ^ "}";
'''
