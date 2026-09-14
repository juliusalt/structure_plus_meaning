theory Factor_Finite_Judgment_Reading_Sharing
  imports Factor_Finite_Judgment_Root_Selection Factor_Finite_Data_Reading_Sharing
begin

declare finite_whole_judgment_readings_def[code del]

lemma finite_whole_judgment_readings_shared_code [code]:
  "finite_whole_judgment_readings C=finite_whole_judgment_readings_at_roots C"
  by (rule finite_whole_judgment_readings_at_roots_exact[symmetric])

text \<open>
  Complete quotation support determines the actual root candidates. The
  selected reader preserves every original whole-judgment reading on every
  input, including arbitrary coordinates and noncanonical value enumerations.
\<close>

end
