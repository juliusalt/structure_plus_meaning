theory Factor_Authority_Scopes
  imports Factor_Authority Factor_Judgment_Scopes
begin

section \<open>Adoption retains its complete program-and-call environment\<close>

theorem native_adoption_judgment_restriction:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_adoption_judgment_at (native_judgment_environment E pu pr au ar) pu pr au ar A G p
    \<longleftrightarrow>native_adoption_judgment_at E pu pr au ar A G p"
  by (simp only: native_adoption_with_reads[OF native_judgment_environment_recovers(1,2)[OF package app]]
      native_adoption_with_reads[OF package app])

definition adoption_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "adoption_scope_quoted_at C q E pu pr au ar A G p \<longleftrightarrow>
    judgment_value_quoted_at C q E pu pr au ar \<and> E=native_judgment_environment E pu pr au ar \<and>
    native_adoption_judgment_at E pu pr au ar A G p"

theorem adoption_scope_quoted_unique:
  assumes first: "adoption_scope_quoted_at C q E pu pr au ar A G p"
    and second: "adoption_scope_quoted_at C q F qu qr bu br B H v"
  shows "E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> A=B \<and> G=H \<and> p=v"
proof -
  have left: "judgment_value_quoted_at C q E pu pr au ar" "native_adoption_judgment_at E pu pr au ar A G p"
    using first by (auto simp: adoption_scope_quoted_at_def)
  have right: "judgment_value_quoted_at C q F qu qr bu br" "native_adoption_judgment_at F qu qr bu br B H v"
    using second by (auto simp: adoption_scope_quoted_at_def)
  have scope: "E=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    by (rule judgment_value_quoted_unique[OF left(1) right(1)])
  have other: "native_adoption_judgment_at E pu pr au ar B H v" using right(2) scope by simp
  have subject: "A=B \<and> G=H \<and> p=v" by (rule native_adoption_subject_unique[OF left(2) other])
  show ?thesis using scope subject by blast
qed

lemma adoption_scope_quoted_formed:
  assumes quote: "adoption_scope_quoted_at C q E pu pr au ar A G p"
  shows "exact_formed C \<and> environment_formed E \<and> target_formed A \<and>
    generation_formed G \<and> target_formed p"
proof -
  have data: "judgment_value_quoted_at C q E pu pr au ar"
    and adopted: "native_adoption_judgment_at E pu pr au ar A G p"
    using quote by (auto simp: adoption_scope_quoted_at_def)
  show ?thesis using judgment_value_quoted_formed[OF data] native_adoption_formed[OF adopted] by blast
qed

theorem adoption_scope_quoted_total:
  fixes E :: "local_address option artifact_environment"
  assumes adopted: "native_adoption_judgment_at E pu pr au ar A G p"
  shows "\<exists>C. adoption_scope_quoted_at C [] (native_judgment_environment E pu pr au ar) pu pr au ar A G p"
proof -
  obtain P d t I K where read: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using adopted unfolding native_adoption_judgment_at_def by blast
  let ?F="native_judgment_environment E pu pr au ar"
  have kept: "native_package_at ?F pu pr P" "native_application_at ?F au ar d t I K" "environment_formed ?F"
    using native_judgment_environment_recovers[OF read] by blast+
  have sites: "(pu,pr)\<in>environment_positions ?F" "(au,ar)\<in>environment_positions ?F"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain C where quote: "judgment_value_quoted_at C [] ?F pu pr au ar"
    using judgment_value_quoted_total[OF kept(3) sites] by blast
  have fixed: "?F=native_judgment_environment ?F pu pr au ar"
    using native_judgment_environment_idempotent[OF read] by simp
  have truth: "native_adoption_judgment_at ?F pu pr au ar A G p"
    using native_adoption_judgment_restriction[OF read] adopted by blast
  show ?thesis using quote fixed truth unfolding adoption_scope_quoted_at_def by blast
qed

theorem adoption_scope_quoted_in_environment:
  assumes quote: "adoption_scope_quoted_at C q E pu pr au ar A G p"
    and formed: "environment_formed F" and source: "artifact_at F u C"
  shows "\<exists>t. judgment_value_presents E pu pr au ar t \<and>
    term_quoted_at F u q t (rra_carrier (object_structure C)) {}"
  using quote unfolding adoption_scope_quoted_at_def
  by (meson judgment_value_quoted_in_environment[OF _ formed source])

text \<open>
  The exact recorded value stores the complete minimal judgment environment
  and its two sites. Authority, generation, and purpose are recovered from the
  actual call, without adding duplicate subject fields. Equal quotation targets
  preserve the complete scope and subject across outer environments. The raw
  judgment still requires its ordinary program's permission and presentation
  invariance. No proof or cause-validity condition enters this scope layer.
\<close>

end
