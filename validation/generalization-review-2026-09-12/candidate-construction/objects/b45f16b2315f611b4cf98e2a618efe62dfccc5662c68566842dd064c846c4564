theory Factor_Generation_Scopes
  imports Factor_Judgment_Scopes RRA_Generation
begin

section \<open>Recovering the self-contained scope recorded by a generation\<close>

definition generation_judgment_scope_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_judgment_scope_at E gu gr G F pu pr au ar \<longleftrightarrow>
    generation_at E gu gr G \<and>
    (\<exists>C cr. generation_cause G=Whole_Artifact C \<and>
      judgment_value_quoted_at C cr F pu pr au ar)"

lemma generation_judgment_scope_cause:
  assumes "generation_judgment_scope_at E gu gr G F pu pr au ar"
  shows "\<exists>C r. generation_cause G=Whole_Artifact C \<and>
    judgment_value_quoted_at C r F pu pr au ar"
  using assms unfolding generation_judgment_scope_at_def by blast

theorem generation_judgment_scope_unique:
  assumes first: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and second: "generation_judgment_scope_at E' hu hr H F' qu qr bu br"
    and cause: "generation_cause G=generation_cause H"
  shows "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain C cr where left: "generation_cause G=Whole_Artifact C" "judgment_value_quoted_at C cr F pu pr au ar"
    using generation_judgment_scope_cause[OF first] by blast
  obtain D dr where right: "generation_cause H=Whole_Artifact D" "judgment_value_quoted_at D dr F' qu qr bu br"
    using generation_judgment_scope_cause[OF second] by blast
  have same: "C=D" using left(1) right(1) cause by simp
  have other: "judgment_value_quoted_at C dr F' qu qr bu br" using right(2) same by simp
  show ?thesis using judgment_value_whole_unique[OF left(2) other] by blast
qed

lemma generation_judgment_scope_from_core:
  assumes gen: "generation_at E gu gr G"
    and cause: "generation_cause G=Whole_Artifact C"
    and quote: "judgment_value_quoted_at C r F pu pr au ar"
  shows "generation_judgment_scope_at E gu gr G F pu pr au ar"
  using gen cause quote unfolding generation_judgment_scope_at_def by blast

theorem generation_judgment_scope_outer_transfer:
  assumes source: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and target: "generation_at E' hu hr G"
  shows "generation_judgment_scope_at E' hu hr G F pu pr au ar"
  using source target unfolding generation_judgment_scope_at_def by blast

theorem generation_judgment_scope_material:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
  shows "\<exists>C cu cr t. generation_cause G=Whole_Artifact C \<and> artifact_at E cu C \<and>
    judgment_value_quoted_at C cr F pu pr au ar \<and> judgment_value_presents F pu pr au ar t \<and>
    term_quoted_at E cu cr t (rra_carrier (object_structure C)) {}"
proof -
  have gen: "generation_at E gu gr G" using scope by (simp add: generation_judgment_scope_at_def)
  obtain C cr where cause: "generation_cause G=Whole_Artifact C"
    and quote: "judgment_value_quoted_at C cr F pu pr au ar"
    using generation_judgment_scope_cause[OF scope] by blast
  obtain cu where material: "artifact_at E cu C"
    using generation_cause_artifact[OF gen] cause by auto
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  obtain t where read: "judgment_value_presents F pu pr au ar t"
    "term_quoted_at E cu cr t (rra_carrier (object_structure C)) {}"
    using judgment_value_quoted_in_environment[OF quote formed material] by blast
  show ?thesis using cause material quote read by blast
qed

text \<open>
  The generation records the whole complete program-and-call scope artifact.
  Its data structure determines the quotation root, so no root coordinate is
  stored in the cause target. Equal cause values recover equal roots and scopes,
  independently of outer bindings. The actual generation reading ensures that
  the quoted artifact is present, and its native data reading uses no slots.
  Scope recovery establishes neither the truth nor the role of the application.
\<close>

end
