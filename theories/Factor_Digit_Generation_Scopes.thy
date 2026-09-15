theory Factor_Digit_Generation_Scopes
  imports RRA_Digit_Generation_Readings Factor_Finite_Certified_Causes Factor_Finite_Judgment_Reading_Sharing
begin

definition digit_generation_judgment_readings where
  "digit_generation_judgment_readings q gu gr G=(if digit_check_generation q G gu gr then
    (case generation_cause G of Finite_Whole C \<Rightarrow> finite_whole_judgment_readings C | _ \<Rightarrow> {||})
    else {||})"

theorem digit_generation_judgment_readings_exact:
  "digit_generation_judgment_readings q gu gr G=
    finite_generation_judgment_readings (snd (digit_allocated_view q)) gu gr G"
  by (simp only: digit_generation_judgment_readings_def digit_generation_check_exact
    finite_generation_judgment_readings_def)

definition digit_certified_base_cause where
  "digit_certified_base_cause q gu gr G H root R=fBex (digit_generation_judgment_readings q gu gr G)
    (\<lambda>(F,pu,pr,au,ar). finite_certified_judgment_context F pu pr au ar G H root R)"

theorem digit_certified_base_cause_exact:
  "digit_certified_base_cause q gu gr G H root R=
    finite_certified_base_cause (snd (digit_allocated_view q)) gu gr G H root R"
  by (simp only: digit_certified_base_cause_def digit_generation_judgment_readings_exact finite_certified_base_cause_def)

corollary digit_certified_base_cause_original:
  "digit_certified_base_cause q gu gr G H root R \<longleftrightarrow>
    certified_base_cause_at (decode_finite_environment (snd (digit_allocated_view q))) gu gr
      (decode_finite_generation G) (decode_finite_environment H) root (decode_finite_object R)"
  by (simp only: digit_certified_base_cause_exact finite_certified_base_cause_exact)

text \<open>
  Actual digit lookups check the generation at its requested site. The whole
  cause then supplies every original judgment quotation reading. The complete
  material view occurs only in the contract, and all allowed cause presentations
  retain their original certified-base-cause meaning.
\<close>

end
