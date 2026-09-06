theory Factor_Generation_Causes
  imports Factor_Recorded_Cause Factor_Base_Cause
begin

section \<open>The two cause roles are distinguished by their existing argument forms\<close>

lemma base_and_construction_judgments_disjoint:
  assumes base: "base_admission_judgment_at E pu pr au ar R"
    and built: "construction_judgment_at E qu qr au ar xs B W S"
  shows False
proof -
  obtain d I K where literal: "native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K"
    using base unfolding base_admission_judgment_at_def by blast
  obtain e t J L where account: "native_application_at E au ar e t J L"
    and presented: "construction_claim_presents xs B W S t"
    using built unfolding construction_judgment_at_def by blast
  have same: "t=Target_Term (Whole_Artifact R)" using native_application_unique[OF literal account] by simp
  show False using presented same by (auto simp: construction_claim_presents_def)
qed

theorem recorded_cause_roles_disjoint:
  assumes base: "recorded_base_cause_at E gu gr G R"
    and built: "recorded_construction_cause_at E' hu hr H xs B W S"
  shows "generation_cause G\<noteq>generation_cause H"
proof
  assume cause: "generation_cause G=generation_cause H"
  obtain F pu pr au ar where left: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    "base_admission_judgment_at F pu pr au ar R"
    using base unfolding recorded_base_cause_at_def by blast
  obtain F' qu qr bu br where right: "generation_judgment_scope_at E' hu hr H F' qu qr bu br"
    "construction_judgment_at F' qu qr bu br xs B W S"
    using built unfolding recorded_construction_cause_at_def by blast
  have same: "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    by (rule generation_judgment_scope_unique[OF left(1) right(1) cause])
  have other: "construction_judgment_at F pu pr au ar xs B W S" using right(2) same by simp
  show False by (rule base_and_construction_judgments_disjoint[OF left(2) other])
qed

section \<open>Cause validity covers the declared roles without changing formation\<close>

definition generation_cause_valid_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> bool" where
  "generation_cause_valid_at E u r G \<longleftrightarrow>
    (\<exists>R. recorded_base_cause_at E u r G R) \<or>
    (\<exists>xs B W R. recorded_construction_cause_at E u r G xs B W R)"

lemma valid_generation_has_scope:
  assumes "generation_cause_valid_at E u r G"
  shows "\<exists>F pu pr au ar. generation_judgment_scope_at E u r G F pu pr au ar"
  using assms unfolding generation_cause_valid_at_def recorded_base_cause_at_def
    recorded_construction_cause_at_def by blast

lemma valid_generation_is_read:
  assumes "generation_cause_valid_at E u r G"
  shows "generation_at E u r G"
  using valid_generation_has_scope[OF assms] unfolding generation_judgment_scope_at_def by blast

lemma valid_generation_cause_is_whole:
  assumes valid: "generation_cause_valid_at E u r G"
  shows "\<exists>C a. generation_cause G=Whole_Artifact C \<and> anchor_formed (C,a)"
proof -
  obtain F pu pr au ar where scope: "generation_judgment_scope_at E u r G F pu pr au ar"
    using valid_generation_has_scope[OF valid] by blast
  obtain C a where cause: "generation_cause G=Whole_Artifact C"
    and quote: "judgment_value_quoted_at C a F pu pr au ar"
    using generation_judgment_scope_cause[OF scope] by blast
  show ?thesis using cause judgment_value_quoted_anchor[OF quote] by blast
qed

theorem empty_cause_is_not_valid:
  assumes "generation_cause G=Whole_Artifact empty_artifact"
  shows "\<not>generation_cause_valid_at E u r G"
proof
  assume valid: "generation_cause_valid_at E u r G"
  show False using valid_generation_cause_is_whole[OF valid] assms empty_artifact_has_no_anchor by auto
qed

theorem generation_formation_does_not_validate_its_cause:
  "\<exists>E :: bool artifact_environment. \<exists>u r G.
    generation_at E u r G \<and> generation_formed G \<and> \<not>generation_cause_valid_at E u r G"
proof -
  let ?T = "Whole_Artifact empty_artifact"
  let ?G = "Generation ?T {||} ?T ?T"
  let ?E = "one_binding_environment base_generation_artifact [9] empty_artifact"
  have gen: "generation_at ?E False [] ?G" by (rule closed_base_generation(3)) simp
  have formed: "generation_formed ?G" by (rule generation_at_formed[OF gen])
  have whole: "generation_cause ?G=?T" by simp
  have invalid: "\<not>generation_cause_valid_at ?E False [] ?G"
    by (rule empty_cause_is_not_valid[OF whole])
  show ?thesis using gen formed invalid by blast
qed

theorem valid_generation_outer_transfer:
  assumes valid: "generation_cause_valid_at E u r G" and target: "generation_at F v a G"
  shows "generation_cause_valid_at F v a G"
proof -
  have alternatives: "(\<exists>R. recorded_base_cause_at E u r G R) \<or>
    (\<exists>xs B W R. recorded_construction_cause_at E u r G xs B W R)"
    using valid by (simp only: generation_cause_valid_at_def)
  then show ?thesis
  proof
    assume "\<exists>R. recorded_base_cause_at E u r G R"
    then obtain R where base: "recorded_base_cause_at E u r G R" by blast
    show ?thesis using recorded_base_outer_transfer[OF base target]
      unfolding generation_cause_valid_at_def by blast
  next
    assume "\<exists>xs B W R. recorded_construction_cause_at E u r G xs B W R"
    then obtain xs B W R where built: "recorded_construction_cause_at E u r G xs B W R" by blast
    show ?thesis using recorded_construction_outer_transfer[OF built target]
      unfolding generation_cause_valid_at_def by blast
  qed
qed

text \<open>
  The base literal and complete construction account cannot be the argument of
  the same native call. Equal recorded cause targets therefore cannot change
  roles across outer environments. This distinction follows from the existing
  argument structures and needs no additional role field.

  Cause validity is the derived union of these two declared profiles. An
  actual formed generation with an invalid cause is exhibited, and every
  presentation of the same core preserves cause validity. Historical
  continuation and authority remain separate judgments.
\<close>

end
