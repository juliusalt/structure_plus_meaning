theory Factor_Policy_Causes
  imports Factor_Certified_Base_Cause Factor_Package_Scope_Identity
begin

definition certified_policy_cause_at where
  "certified_policy_cause_at K pu pr d E gu gr G H root R=(
    (\<exists>P. native_package_at K pu pr P) \<and> certified_base_cause_at E gu gr G H root R \<and>
    (\<exists>F au ar I A. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment K pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A))"

theorem certified_policy_cause_sound:
  assumes policy: "native_package_at K pu pr P"
    and certified: "certified_policy_cause_at K pu pr d E gu gr G H root R"
  shows "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
proof -
  obtain F au ar I A where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and same: "native_package_environment F pu pr=native_package_environment K pu pr"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A"
    and base: "certified_base_cause_at E gu gr G H root R"
    using certified unfolding certified_policy_cause_at_def by blast
  have recorded: "recorded_base_cause_at E gu gr G R"
    by (rule certified_base_cause_sound[OF base])
  have admitted: "base_admission_judgment_at F pu pr au ar R"
    using recorded_base_cause_with_scope[OF scope] recorded by blast
  obtain Q where package: "native_package_at F pu pr Q"
    using admitted unfolding base_admission_judgment_at_def by blast
  have identity: "Q=P" by (rule native_package_same_scope[OF package policy same])
  show ?thesis using admitted by (simp only: base_admission_with_reads[OF package app] identity; blast)
qed

theorem certified_policy_cause_refuses_false_call:
  assumes "native_package_at K pu pr P" "(d,Target_Term (Whole_Artifact R))\<notin>positive_meaning P"
  shows "\<not>certified_policy_cause_at K pu pr d E gu gr G H root R"
proof
  assume checked: "certified_policy_cause_at K pu pr d E gu gr G H root R"
  have "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
    by (rule certified_policy_cause_sound[OF assms(1) checked])
  then show False using assms(2) by blast
qed

text \<open>
  A cause is bound to an independently supplied actual policy package, source
  site and called definition. The entire minimal program scope must agree.
  Its original certified-base-cause condition remains separate. A different
  accepting program cannot justify a call refused by this policy.
\<close>

end
