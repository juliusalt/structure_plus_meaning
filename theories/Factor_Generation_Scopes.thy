theory Factor_Generation_Scopes
  imports Factor_Judgment_Values Factor_Judgment_Retention RRA_Generation_Dependencies
begin

section \<open>Recovering the self-contained scope recorded by a generation\<close>

definition generation_judgment_scope_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_judgment_scope_at E gu gr G F pu pr au ar \<longleftrightarrow>
    generation_at E gu gr G \<and>
    (\<exists>cu cr C. generation_cause_location E gu gr cu cr \<and> artifact_at E cu C \<and>
      judgment_value_quoted_at C cr F pu pr au ar)"

lemma generation_judgment_scope_cause:
  assumes "generation_judgment_scope_at E gu gr G F pu pr au ar"
  shows "\<exists>C r. generation_cause G=Occurrence_Anchor (C,r) \<and>
    judgment_value_quoted_at C r F pu pr au ar"
proof -
  obtain cu cr C where parts: "generation_at E gu gr G"
    "generation_cause_location E gu gr cu cr" "artifact_at E cu C"
    "judgment_value_quoted_at C cr F pu pr au ar"
    using assms unfolding generation_judgment_scope_at_def by blast
  show ?thesis using generation_cause_location_target[OF parts(1-3)] parts(4) by blast
qed

theorem generation_judgment_scope_unique:
  assumes first: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and second: "generation_judgment_scope_at E' hu hr H F' qu qr bu br"
    and cause: "generation_cause G=generation_cause H"
  shows "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain cu cr C where left: "generation_at E gu gr G" "generation_cause_location E gu gr cu cr"
    "artifact_at E cu C" "judgment_value_quoted_at C cr F pu pr au ar"
    using first unfolding generation_judgment_scope_at_def by blast
  obtain vu vr D where right: "generation_at E' hu hr H" "generation_cause_location E' hu hr vu vr"
    "artifact_at E' vu D" "judgment_value_quoted_at D vr F' qu qr bu br"
    using second unfolding generation_judgment_scope_at_def by blast
  have c: "generation_cause G=Occurrence_Anchor (C,cr)"
    by (rule generation_cause_location_target[OF left(1-3)])
  have d: "generation_cause H=Occurrence_Anchor (D,vr)"
    by (rule generation_cause_location_target[OF right(1-3)])
  have same: "C=D \<and> cr=vr" using c d cause by simp
  have other: "judgment_value_quoted_at C cr F' qu qr bu br" using right(4) same by simp
  show ?thesis by (rule judgment_value_quoted_unique[OF left(4) other])
qed

lemma generation_judgment_scope_from_core:
  assumes gen: "generation_at E gu gr G"
    and cause: "generation_cause G=Occurrence_Anchor (C,r)"
    and quote: "judgment_value_quoted_at C r F pu pr au ar"
  shows "generation_judgment_scope_at E gu gr G F pu pr au ar"
proof -
  obtain cu where site: "generation_cause_location E gu gr cu r" "artifact_at E cu C"
    using generation_cause_location_complete[OF gen cause] by blast
  show ?thesis using gen site quote unfolding generation_judgment_scope_at_def by blast
qed

theorem generation_judgment_scope_outer_transfer:
  assumes source: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and target: "generation_at E' hu hr G"
  shows "generation_judgment_scope_at E' hu hr G F pu pr au ar"
proof -
  obtain cu cr C where parts: "generation_at E gu gr G"
    "generation_cause_location E gu gr cu cr" "artifact_at E cu C"
    "judgment_value_quoted_at C cr F pu pr au ar"
    using source unfolding generation_judgment_scope_at_def by blast
  have cause: "generation_cause G=Occurrence_Anchor (C,cr)"
    by (rule generation_cause_location_target[OF parts(1-3)])
  show ?thesis by (rule generation_judgment_scope_from_core[OF target cause parts(4)])
qed

section \<open>Recording the minimal scope of any native program and call\<close>

theorem native_judgment_recordable:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "\<exists>F C. judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  let ?F = "native_judgment_environment E pu pr au ar"
  have kept: "native_package_at ?F pu pr P" "native_application_at ?F au ar d t I K" "environment_formed ?F"
    using native_judgment_environment_recovers[OF package app] by blast+
  have canonical: "?F=native_judgment_environment ?F pu pr au ar"
    using native_judgment_environment_idempotent[OF package app] by simp
  have program: "native_package_environment ?F pu pr=native_package_environment E pu pr"
    by (rule native_judgment_program_environment[OF package app])
  have sites: "(pu,pr)\<in>environment_positions ?F" "(au,ar)\<in>environment_positions ?F"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain C where quote: "judgment_value_quoted_at C [] ?F pu pr au ar"
    using judgment_value_quoted_total[OF kept(3) sites] by blast
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ C])
    (use quote canonical kept(1,2) program in blast)
qed

text \<open>
  The generation records a complete program-and-call scope as exact data.
  Equal cause targets recover equal scopes, independently of outer bindings.
  Scope recovery establishes neither the truth nor the role of the application.
\<close>

end
