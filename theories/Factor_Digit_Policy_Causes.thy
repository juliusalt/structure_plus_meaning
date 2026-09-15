theory Factor_Digit_Policy_Causes
  imports Factor_Certified_Policy_Readings Factor_Digit_Generation_Scopes
begin

definition digit_certified_policy_cause where
  "digit_certified_policy_cause K pu pr d q gu gr G H root R=
    certified_policy_readings K pu pr d G H root R (digit_generation_judgment_readings q gu gr G)"

theorem digit_certified_policy_cause_exact:
  "digit_certified_policy_cause K pu pr d q gu gr G H root R=
    finite_certified_policy_cause K pu pr d (snd (digit_allocated_view q)) gu gr G H root R"
  by (simp only: digit_certified_policy_cause_def digit_generation_judgment_readings_exact
    finite_certified_policy_from_scopes)

corollary digit_certified_policy_cause_original:
  "digit_certified_policy_cause K pu pr d q gu gr G H root R \<longleftrightarrow>
    certified_policy_cause_at (decode_finite_environment K) pu pr d
      (decode_finite_environment (snd (digit_allocated_view q))) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R)"
  by (simp only: digit_certified_policy_cause_exact finite_certified_policy_cause_exact)

export_code digit_certified_policy_cause checking SML

text \<open>
  The actual digit policy checker derives the generation's complete scopes once
  and instantiates the original package, certification and alignment checks.
  It does not enumerate the accumulated generation material. Costs of the
  requested generation, quoted scope, policy and retained replay remain explicit
  input costs and require their own full physical account.
\<close>

end
