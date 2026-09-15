theory Factor_Certified_Policy_Readings
  imports Factor_Finite_Policy_Causes
begin

definition certified_policy_readings where
  "certified_policy_readings K pu pr d G H root R scopes=(
    finite_native_package_readings K pu pr\<noteq>{||} \<and>
    fBex scopes (\<lambda>(F,qu,qr,au,ar). finite_certified_judgment_context F qu qr au ar G H root R) \<and>
    fBex scopes (finite_policy_cause_alignment K pu pr d R))"

theorem finite_certified_policy_from_scopes:
  "finite_certified_policy_cause K pu pr d E gu gr G H root R=
    certified_policy_readings K pu pr d G H root R (finite_generation_judgment_readings E gu gr G)"
  by (simp only: finite_certified_policy_cause_def finite_certified_base_cause_def certified_policy_readings_def)

text \<open>
  One complete scope family supplies the two original existential checks.
  Certification and policy alignment retain their original separate witnesses.
  A caller must establish the actual scope-reading equation before using this
  shared calculation as the original policy-cause judgment.
\<close>

end
