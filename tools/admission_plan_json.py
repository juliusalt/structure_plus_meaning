"""Serialize the complete computed admission instruction and sequence fields."""

PRELUDE = r'''
fun jinstruction (N.Pair_Admission_Instruction (d,a,b)) =
    "[\"pair\"," ^ jnat d ^ "," ^ jnat a ^ "," ^ jnat b ^ "]"
  | jinstruction (N.List_Admission_Instruction (d,a)) =
    "[\"list\"," ^ jnat d ^ "," ^ jnat a ^ "]";
fun jsequence (ds,(next,cs)) = "{\"entries\":" ^ jlist jnat ds ^
    ",\"next\":" ^ jnat next ^ ",\"instructions\":" ^ jlist jinstruction cs ^ "}";
fun jchecked NONE = "null" | jchecked (SOME plan) = jsequence plan;
'''
