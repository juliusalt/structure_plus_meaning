theory Factor_Policy_Causes
  imports Factor_Certified_Base_Cause Factor_Package_Scope_Identity
begin

definition certified_policy_cause_at where
  "certified_policy_cause_at K pu pr d E gu gr G H root R=(
    (\<exists>P. native_package_at K pu pr P) \<and> certified_base_cause_at E gu gr G H root R \<and>
    (\<exists>F au ar I A. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment K pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A))"

section \<open>The policy cause over a scope reading\<close>

text \<open>
  The policy cause reads its scope only through the certified base cause and the package and
  application at the scope, so it is stated once over a scope reading
  (@{text Factor_Certified_Base_Cause}); @{const certified_policy_cause_at} is its instance at
  @{const generation_judgment_scope_at}. Soundness and refusal need the reading determined at the
  generation.
\<close>

definition scope_certified_policy_cause_at where
  "scope_certified_policy_cause_at S K pu pr d E gu gr G H root R=(
    (\<exists>P. native_package_at K pu pr P) \<and> scope_certified_base_cause_at S E gu gr G H root R \<and>
    (\<exists>F au ar I A. S E gu gr G F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment K pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A))"

lemma certified_policy_cause_scope_instance:
  "certified_policy_cause_at K pu pr d E gu gr G H root R =
    scope_certified_policy_cause_at generation_judgment_scope_at K pu pr d E gu gr G H root R"
  by (simp only: certified_policy_cause_at_def scope_certified_policy_cause_at_def
    certified_base_cause_scope_instance)

theorem scope_certified_policy_cause_sound:
  assumes determined: "scope_reading_determined S E gu gr G"
    and policy: "native_package_at K pu pr P"
    and certified: "scope_certified_policy_cause_at S K pu pr d E gu gr G H root R"
  shows "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
proof -
  obtain F au ar I A where scope: "S E gu gr G F pu pr au ar"
    and same: "native_package_environment F pu pr=native_package_environment K pu pr"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A"
    and base: "scope_certified_base_cause_at S E gu gr G H root R"
    using certified unfolding scope_certified_policy_cause_at_def by blast
  have recorded: "scope_recorded_base_cause_at S E gu gr G R"
    by (rule scope_certified_base_cause_sound[OF base])
  have admitted: "base_admission_judgment_at F pu pr au ar R"
    using scope_recorded_base_cause_with_scope[OF determined scope] recorded by blast
  obtain Q where package: "native_package_at F pu pr Q"
    using admitted unfolding base_admission_judgment_at_def by blast
  have identity: "Q=P" by (rule native_package_same_scope[OF package policy same])
  show ?thesis using admitted by (simp only: base_admission_with_reads[OF package app] identity; blast)
qed

theorem scope_certified_policy_cause_refuses_false_call:
  assumes "scope_reading_determined S E gu gr G"
    and "native_package_at K pu pr P" "(d,Target_Term (Whole_Artifact R))\<notin>positive_meaning P"
  shows "\<not>scope_certified_policy_cause_at S K pu pr d E gu gr G H root R"
proof
  assume checked: "scope_certified_policy_cause_at S K pu pr d E gu gr G H root R"
  have "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
    by (rule scope_certified_policy_cause_sound[OF assms(1,2) checked])
  then show False using assms(3) by blast
qed

section \<open>The whole-value reading's instances\<close>

theorem certified_policy_cause_sound:
  assumes policy: "native_package_at K pu pr P"
    and certified: "certified_policy_cause_at K pu pr d E gu gr G H root R"
  shows "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
  by (rule scope_certified_policy_cause_sound[OF generation_judgment_scope_determined policy
    certified[unfolded certified_policy_cause_scope_instance]])

theorem certified_policy_cause_refuses_false_call:
  assumes "native_package_at K pu pr P" "(d,Target_Term (Whole_Artifact R))\<notin>positive_meaning P"
  shows "\<not>certified_policy_cause_at K pu pr d E gu gr G H root R"
  using scope_certified_policy_cause_refuses_false_call[OF generation_judgment_scope_determined assms]
  by (simp only: certified_policy_cause_scope_instance)

text \<open>
  A cause is bound to an independently supplied actual policy package, source
  site and called definition. The entire minimal program scope must agree.
  Its original certified-base-cause condition remains separate. A different
  accepting program cannot justify a call refused by this policy.
\<close>

end
