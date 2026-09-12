theory RRA_Binding_Omissions
  imports RRA_Read_Environment
begin

section \<open>Comparing environments with one binding omitted\<close>

definition omit_binding :: "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u artifact_environment" where
  "omit_binding E u k=E\<lparr>environment_bindings:={entry\<in>environment_bindings E. fst entry\<noteq>(u,k)}\<rparr>"

lemma omit_binding_artifacts [simp]:
  "environment_artifacts (omit_binding E u k)=environment_artifacts E"
  by (simp add: omit_binding_def)

lemma omit_binding_artifact_at [simp]:
  "artifact_at (omit_binding E u k) v R\<longleftrightarrow>artifact_at E v R"
  by (simp add: artifact_at_def)

lemma omit_binding_uses [simp]: "environment_uses (omit_binding E u k)=environment_uses E"
  by (simp add: environment_uses_def)

lemma omit_binding_binds [simp]:
  "binds_slot (omit_binding E u k) v a w\<longleftrightarrow>(v,a)\<noteq>(u,k) \<and> binds_slot E v a w"
  by (auto simp: omit_binding_def binds_slot_def)

lemma omit_binding_formed:
  assumes "environment_formed E"
  shows "environment_formed (omit_binding E u k)"
  using assms by (auto simp: environment_formed_def omit_binding_def artifact_at_def binds_slot_def
    environment_uses_def single_valued_def)

lemma omit_binding_included: "environment_included (omit_binding E u k) E"
  by (auto simp: environment_included_def omit_binding_def)

lemma omit_binding_exact_difference:
  assumes formed: "environment_formed E" and bound: "binds_slot E u k v"
  shows "environment_bindings (omit_binding E u k)=environment_bindings E-{((u,k),v)}"
  using formed bound by (auto simp: omit_binding_def environment_formed_def binds_slot_def single_valued_def)

lemma omitted_binding_excludes_environment:
  assumes "binds_slot F u k v"
  shows "\<not>environment_included F (omit_binding E u k)"
  using assms by (auto simp: environment_included_def omit_binding_def binds_slot_def)

lemma omit_binding_preserves_unrequested_scope:
  assumes "(u,k)\<notin>D"
  shows "environment_included (read_environment E U D) (omit_binding E u k)"
  using assms by (auto simp: environment_included_def read_environment_def omit_binding_def)

lemma omit_binding_preserves_other_subenvironment:
  assumes formed: "environment_formed F" and included: "environment_included F E"
    and outside: "u\<notin>environment_uses F"
  shows "environment_included F (omit_binding E u k)"
proof -
  have no_binding: "\<And>a v. \<not>binds_slot F u a v"
    using environment_binding_uses(1)[OF formed] outside by blast
  show ?thesis using included no_binding
    by (auto simp: environment_included_def omit_binding_def binds_slot_def)
qed

text \<open>
  These are two supplied finite environment values. They retain identical
  artifact placements and differ only at the stated source and slot. Formation
  makes an existing binding there unique, so the difference is exactly one
  edge. Every unrequested reading scope and every subenvironment with a
  different source-use boundary remains included. No mutation operation or
  permission to omit a semantic dependency is inferred.
\<close>

end
