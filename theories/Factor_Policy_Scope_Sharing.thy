theory Factor_Policy_Scope_Sharing
  imports Factor_Certified_Policy_Readings
begin

declare finite_certified_policy_cause_def[code del]

lemmas finite_certified_policy_cause_shared_code [code] = finite_certified_policy_from_scopes

text \<open>
  The original policy cause reads the generation judgment scopes of its cause
  once and supplies that complete family to both original existential checks.
  Certification and policy alignment keep their separate witnesses, and every
  refusal of the original judgment is preserved.
\<close>

end
