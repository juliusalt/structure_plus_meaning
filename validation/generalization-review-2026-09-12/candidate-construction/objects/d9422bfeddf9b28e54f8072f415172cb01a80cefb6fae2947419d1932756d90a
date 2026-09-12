theory Factor_Target_Presentations
  imports Factor_Presentation_Classes Factor_Target_Admission
begin

section \<open>The actual artifact and optional occurrence determine the target\<close>

lemma optional_address_presentation_class:
  "presentation_class (\<lambda>r t. t=optional_payload_term r) (\<lambda>_. True)
    (\<lambda>t. \<exists>r. t=optional_payload_term r)"
  using injective_presentation_class[where f=optional_payload_term and D="\<lambda>_. True"]
    optional_payload_term_injective by simp

theorem target_value_presentation_class:
  "presentation_class target_value_presents target_formed
    (\<lambda>t. (35,t)\<in>positive_meaning target_admission_system)"
proof -
  let ?R="factor_pair_presents artifact_value_presents (\<lambda>r t. t=optional_payload_term r)"
  let ?A="\<lambda>t. \<exists>a b. (11,a)\<in>positive_meaning artifact_admission_system \<and>
    (\<exists>r. b=optional_payload_term r) \<and> t=Pair_Term a b"
  have fields: "presentation_class ?R (\<lambda>z. exact_formed (fst z)) ?A"
    using factor_pair_class[OF artifact_presentations.presentation_class_axioms
      optional_address_presentation_class] by simp
  let ?observe="\<lambda>x. (target_artifact x,target_occurrence x)"
  have observed: "presentation_class (\<lambda>x t. target_formed x \<and> ?R (?observe x) t)
      target_formed (\<lambda>t. \<exists>x. target_formed x \<and> ?R (?observe x) t)"
  proof (rule presentation_class_observations[OF fields])
    fix x assume "target_formed x"
    then show "exact_formed (fst (?observe x))" by (simp add: target_formed_artifact)
  next
    fix x y assume "target_formed x" "target_formed y" "?observe x=?observe y"
    then show "x=y" by (simp add: exact_target_identity)
  qed
  have pointwise: "(target_formed x \<and> ?R (?observe x) t) \<longleftrightarrow> target_value_presents x t" for x t
    by (auto simp: target_value_presents_def factor_pair_presents_def)
  have reading: "(\<lambda>x t. target_formed x \<and> ?R (?observe x) t)=target_value_presents"
    by (intro ext) (rule pointwise)
  have admission: "(\<lambda>t. \<exists>x. target_value_presents x t)=
      (\<lambda>t. (35,t)\<in>positive_meaning target_admission_system)"
    by (rule ext) (simp only: target_admission_exact)
  show ?thesis using observed by (simp only: reading pointwise admission)
qed

interpretation target_presentations: presentation_class target_value_presents target_formed
  "\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  by (rule target_value_presentation_class)

theorem target_quotation_presentation_class:
  "presentation_class
    (composed_presentation target_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    target_formed
    (\<lambda>p. \<exists>t. (35,t)\<in>positive_meaning target_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t)"
proof (rule complete_quotation_presentation_class[OF target_value_presentation_class])
  fix t assume allowed: "(35,t)\<in>positive_meaning target_admission_system"
  obtain x where presented: "target_value_presents x t"
    using allowed by (simp only: target_admission_exact) blast
  show "term_formed t \<and> self_contained_term t"
    using target_value_presents_formed[OF presented] by blast
qed

text \<open>
  Products retain the complete artifact and the optional occurrence in their
  separate positions. The observation map is injective by exact target
  identity. Its domain requires any selected occurrence to belong to that
  very artifact. The existing two ordinary target clauses admit exactly this
  derived class over every input term.

  Complete quotation composes with the entire target value. A whole target
  has no selected occurrence; an empty occurrence address remains a present
  address. These two cases are not identified.
\<close>

end
