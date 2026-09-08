theory Factor_Base_Cause_Presentations
  imports Factor_Base_Cause Factor_Judgment_Retention_Presentations Factor_Generation_Scope_Presentations
begin

section \<open>The existing judgments determine their exact payloads\<close>

abbreviation base_admission_context :: "judgment_context \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "base_admission_context z R \<equiv> base_admission_judgment_at (fst z)
    (fst (fst (snd z))) (snd (fst (snd z))) (fst (snd (snd z))) (snd (snd (snd z))) R"

abbreviation recorded_base_context :: "generation_source \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "recorded_base_context z R \<equiv> recorded_base_cause_at (fst (fst z))
    (fst (snd (fst z))) (snd (snd (fst z))) (snd z) R"

lemma base_admission_context_source:
  assumes "base_admission_context z R"
  shows "judgment_source_readable z"
proof -
  obtain P d I K where reads: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d
      (Target_Term (Whole_Artifact R)) I K"
    using assms unfolding base_admission_judgment_at_def by blast
  show ?thesis by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ "Target_Term (Whole_Artifact R)"],
    rule exI[of _ I], rule exI[of _ K]) (use reads in blast)
qed

lemma base_admission_context_formed:
  assumes "base_admission_context z R"
  shows "exact_formed R"
  by (rule base_admission_formed[OF assms])

lemma base_admission_context_unique:
  assumes "base_admission_context z R" "base_admission_context z S"
  shows "R=S"
  by (rule base_admission_payload_unique[OF assms])

lemma recorded_base_context_join:
  "recorded_base_context z R \<longleftrightarrow>
    (\<exists>j. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
      generation_payload (snd z)=Whole_Artifact R \<and> base_admission_context j R)"
  by (auto simp: recorded_base_cause_at_def generation_recorded_scope_def;
    metis fst_conv snd_conv)

lemma recorded_base_context_at_scope:
  assumes scope: "generation_recorded_scope z j"
  shows "recorded_base_context z R \<longleftrightarrow> judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact R \<and> base_admission_context j R"
  using recorded_base_cause_with_scope[OF scope[unfolded generation_recorded_scope_def], of R]
  by (simp only: eq_commute)

lemma recorded_base_context_source:
  assumes "recorded_base_context z R"
  shows "generation_at_context (fst z) (snd z)"
  using assms generation_recorded_scope_source by (simp only: recorded_base_context_join; blast)

lemma recorded_base_context_formed:
  assumes "recorded_base_context z R"
  shows "exact_formed R"
  using assms base_admission_context_formed by (simp only: recorded_base_context_join; blast)

lemma recorded_base_context_unique:
  assumes "recorded_base_context z R" "recorded_base_context z S"
  shows "R=S"
  by (rule recorded_base_payload_unique[OF assms refl])

theorem base_admission_context_retained:
  assumes readable: "judgment_source_readable z"
  shows "base_admission_context (judgment_required_environment z,snd z) R \<longleftrightarrow>
    base_admission_context z R"
proof -
  obtain P d t I K where package: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    and app: "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using readable by blast
  have kept: "native_package_at (judgment_required_environment z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    "native_application_at (judgment_required_environment z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by blast+
  show ?thesis by (simp only: fst_conv snd_conv base_admission_with_reads[OF kept]
    base_admission_with_reads[OF package app])
qed

theorem recorded_base_context_outer_invariance:
  assumes first: "generation_at_context (fst z) (snd z)"
    and second: "generation_at_context (fst w) (snd w)"
    and cause: "generation_cause (snd z)=generation_cause (snd w)"
    and payload: "generation_payload (snd z)=generation_payload (snd w)"
  shows "recorded_base_context z R \<longleftrightarrow> recorded_base_context w R"
proof -
  have scopes: "generation_recorded_scope z j \<longleftrightarrow> generation_recorded_scope w j" for j
    using first second cause by (simp add: generation_recorded_scope_def generation_judgment_scope_at_def)
  show ?thesis by (simp only: recorded_base_context_join scopes payload)
qed

section \<open>Determined payloads use complete source and report classes\<close>

definition base_admission_source_presents ::
  "(judgment_context\<times>exact_artifact) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "base_admission_source_presents z p \<longleftrightarrow> judgment_source_presents (fst z) p \<and> base_admission_context (fst z) (snd z)"

theorem base_admission_source_presentation_class:
  "presentation_class base_admission_source_presents (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. \<exists>z. base_admission_source_presents z p)"
proof -
  have determined: "presentation_class
      (\<lambda>z p. judgment_source_presents (fst z) p \<and> base_admission_context (fst z) (snd z))
      (\<lambda>z. judgment_source_readable (fst z) \<and> base_admission_context (fst z) (snd z))
      (\<lambda>p. \<exists>z R. judgment_source_presents z p \<and> base_admission_context z R)"
    by (rule presentation_class_determined[OF judgment_source_presentation_class base_admission_context_unique])
  have domain: "(judgment_source_readable z \<and> base_admission_context z R) \<longleftrightarrow> base_admission_context z R" for z R
    using base_admission_context_source by blast
  have admission: "(\<exists>z R. judgment_source_presents z p \<and> base_admission_context z R) \<longleftrightarrow>
      (\<exists>z. base_admission_source_presents z p)" for p
    by (auto simp: base_admission_source_presents_def; metis fst_conv snd_conv)
  show ?thesis using determined by (simp only: presentation_class_def base_admission_source_presents_def domain admission)
qed

lemma base_admission_source_formed:
  assumes "base_admission_source_presents z p"
  shows "term_formed p \<and> self_contained_term p"
proof -
  have source: "judgment_source_presents (fst z) p" using assms by (simp only: base_admission_source_presents_def; blast)
  show ?thesis by (rule judgment_source_presents_formed[OF source])
qed

theorem base_admission_source_quotation_class:
  "presentation_class
    (composed_presentation base_admission_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. base_admission_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF base_admission_source_presentation_class])
    (use base_admission_source_formed in blast)

definition base_admission_report_presents ::
  "(judgment_context\<times>exact_artifact) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "base_admission_report_presents z p \<longleftrightarrow> base_admission_context (fst z) (snd z) \<and>
    factor_pair_presents judgment_source_presents artifact_value_presents z p"

theorem base_admission_report_presentation_class:
  "presentation_class base_admission_report_presents (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. \<exists>z. base_admission_report_presents z p)"
proof -
  let ?R="factor_pair_presents judgment_source_presents artifact_value_presents"
  let ?D="\<lambda>z. judgment_source_readable (fst z) \<and> exact_formed (snd z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. judgment_source_presents z p) \<and>
    (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q"
  have raw: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF judgment_source_presentation_class artifact_presentations.presentation_class_axioms])
  have restricted: "presentation_class (\<lambda>z p. base_admission_context (fst z) (snd z) \<and> ?R z p)
      (\<lambda>z. base_admission_context (fst z) (snd z))
      (\<lambda>p. \<exists>z. base_admission_context (fst z) (snd z) \<and> ?R z p)"
  proof (rule presentation_class_subdomain[OF raw])
    fix z assume admitted: "base_admission_context (fst z) (snd z)"
    show "?D z" using base_admission_context_source[OF admitted] base_admission_context_formed[OF admitted] by blast
  qed
  show ?thesis using restricted by (simp only: presentation_class_def base_admission_report_presents_def)
qed

lemma base_admission_report_formed:
  assumes "base_admission_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where source: "judgment_source_presents (fst z) p" and expected: "artifact_value_presents (snd z) q"
    and shape: "t=Pair_Term p q"
    using assms by (auto simp: base_admission_report_presents_def factor_pair_presents_def)
  show ?thesis using judgment_source_presents_formed[OF source] artifact_value_presents_formed[OF expected] shape by simp
qed

theorem base_admission_report_quotation_class:
  "presentation_class
    (composed_presentation base_admission_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. base_admission_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF base_admission_report_presentation_class])
    (use base_admission_report_formed in blast)

lemma base_admission_report_relation:
  "(\<exists>z. base_admission_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation judgment_source_presents artifact_value_presents base_admission_context p q"
  by (auto simp: base_admission_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

definition recorded_base_source_presents ::
  "(generation_source\<times>exact_artifact) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "recorded_base_source_presents z p \<longleftrightarrow> generation_source_presents (fst z) p \<and> recorded_base_context (fst z) (snd z)"

theorem recorded_base_source_presentation_class:
  "presentation_class recorded_base_source_presents (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. \<exists>z. recorded_base_source_presents z p)"
proof -
  have determined: "presentation_class
      (\<lambda>z p. generation_source_presents (fst z) p \<and> recorded_base_context (fst z) (snd z))
      (\<lambda>z. (\<lambda>z. generation_at_context (fst z) (snd z)) (fst z) \<and> recorded_base_context (fst z) (snd z))
      (\<lambda>p. \<exists>z R. generation_source_presents z p \<and> recorded_base_context z R)"
    by (rule presentation_class_determined[OF generation_source_presentation_class recorded_base_context_unique])
  have domain: "((\<lambda>z. generation_at_context (fst z) (snd z)) z \<and> recorded_base_context z R) \<longleftrightarrow> recorded_base_context z R" for z R
    using recorded_base_context_source by blast
  have admission: "(\<exists>z R. generation_source_presents z p \<and> recorded_base_context z R) \<longleftrightarrow>
      (\<exists>z. recorded_base_source_presents z p)" for p
    by (auto simp: recorded_base_source_presents_def; metis fst_conv snd_conv)
  show ?thesis using determined by (simp only: presentation_class_def recorded_base_source_presents_def domain admission)
qed

lemma recorded_base_source_formed:
  assumes "recorded_base_source_presents z p"
  shows "term_formed p \<and> self_contained_term p"
proof -
  have source: "generation_source_presents (fst z) p" using assms by (simp only: recorded_base_source_presents_def; blast)
  show ?thesis by (rule generation_source_presents_formed[OF source])
qed

theorem recorded_base_source_quotation_class:
  "presentation_class
    (composed_presentation recorded_base_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. recorded_base_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF recorded_base_source_presentation_class])
    (use recorded_base_source_formed in blast)

definition recorded_base_report_presents ::
  "(generation_source\<times>exact_artifact) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "recorded_base_report_presents z p \<longleftrightarrow> recorded_base_context (fst z) (snd z) \<and>
    factor_pair_presents generation_source_presents artifact_value_presents z p"

theorem recorded_base_report_presentation_class:
  "presentation_class recorded_base_report_presents (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. \<exists>z. recorded_base_report_presents z p)"
proof -
  let ?R="factor_pair_presents generation_source_presents artifact_value_presents"
  let ?D="\<lambda>z. (\<lambda>z. generation_at_context (fst z) (snd z)) (fst z) \<and> exact_formed (snd z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. generation_source_presents z p) \<and>
    (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q"
  have raw: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF generation_source_presentation_class artifact_presentations.presentation_class_axioms])
  have restricted: "presentation_class (\<lambda>z p. recorded_base_context (fst z) (snd z) \<and> ?R z p)
      (\<lambda>z. recorded_base_context (fst z) (snd z))
      (\<lambda>p. \<exists>z. recorded_base_context (fst z) (snd z) \<and> ?R z p)"
  proof (rule presentation_class_subdomain[OF raw])
    fix z assume admitted: "recorded_base_context (fst z) (snd z)"
    show "?D z" using recorded_base_context_source[OF admitted] recorded_base_context_formed[OF admitted] by blast
  qed
  show ?thesis using restricted by (simp only: presentation_class_def recorded_base_report_presents_def)
qed

lemma recorded_base_report_formed:
  assumes "recorded_base_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where source: "generation_source_presents (fst z) p" and expected: "artifact_value_presents (snd z) q"
    and shape: "t=Pair_Term p q"
    using assms by (auto simp: recorded_base_report_presents_def factor_pair_presents_def)
  show ?thesis using generation_source_presents_formed[OF source] artifact_value_presents_formed[OF expected] shape by simp
qed

theorem recorded_base_report_quotation_class:
  "presentation_class
    (composed_presentation recorded_base_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. recorded_base_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF recorded_base_report_presentation_class])
    (use recorded_base_report_formed in blast)

lemma recorded_base_report_relation:
  "(\<exists>z. recorded_base_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation generation_source_presents artifact_value_presents recorded_base_context p q"
  by (auto simp: recorded_base_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

text \<open>
  Base admission and recorded base cause retain their existing independent
  definitions. The actual application determines the base payload; the
  complete generation and recorded declaration determine the recorded one.
  These are determined components, with no second payload stored in a source.
  A report pairs the complete source with any exact presentation of that same
  artifact. Products, subdomains, and complete quotation supply both classes.

  Least judgment restriction preserves base admission. A recorded base cause
  additionally requires the exact fixed scope and agreement with the actual
  generation payload. Equal cause and payload fields preserve that relation
  across outer sources, without constraining historical predecessors.
\<close>

end
