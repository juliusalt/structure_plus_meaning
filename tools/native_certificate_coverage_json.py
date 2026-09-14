"""Serialize every original value in certificate coverage witnesses."""

PRELUDE = r'''
fun jpathRow (ss,n) = "[" ^ jpath ss ^ "," ^ jinstantiated n ^ "]";
fun jproofConflict (p,(a,b)) = "[" ^ jproof p ^ "," ^ jinstantiated a ^ "," ^ jinstantiated b ^ "]";
fun jcallConflict (q,(a,b)) = "[" ^ jcall q ^ "," ^ jinstantiated a ^ "," ^ jinstantiated b ^ "]";
fun jsharedConflict (n,(a,b)) = "[" ^ jinstantiated n ^ "," ^ jpathRow a ^ "," ^ jpathRow b ^ "]";
fun jnodeCoverage (paths,(proofs,(calls,shared))) = "{\"paths\":" ^ jpaths paths ^
  ",\"proof_conflicts\":" ^ jf jproofConflict proofs ^ ",\"call_conflicts\":" ^ jf jcallConflict calls ^
  ",\"shared_paths\":" ^ jf jsharedConflict shared ^ "}";
fun jfamilyCoverage NONE = "null"
  | jfamilyCoverage (SOME rows) = jf (fn (n,a) => "{\"root\":" ^ jinstantiated n ^
      ",\"coverage\":" ^ jnodeCoverage a ^ "}") rows;
fun jcriticismRow (w,a) = "[" ^ jnat w ^ "," ^ jfamilyCoverage a ^ "]";
'''
