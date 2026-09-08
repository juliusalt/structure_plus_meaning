theory Factor_Generation_Program_Presentations
  imports Factor_Generation_Programs Factor_Generation_Presentations Factor_Program_Scope_Reading
begin

section \<open>An actual generation's whole payload determines a program scope\<close>

type_synonym program_context = "site_context\<times>local_address option native_system"

definition generation_payload_scope :: "generation_source \<Rightarrow> program_context \<Rightarrow> bool" where
  "generation_payload_scope z k \<longleftrightarrow> generation_at_context (fst z) (snd z) \<and>
    generation_program_scope (snd z) (fst (fst k)) (fst (snd (fst k))) (snd (snd (fst k))) (snd k)"

lemma generation_payload_scope_unique:
  assumes "generation_payload_scope z k" "generation_payload_scope z h"
  shows "k=h"
  using assms generation_program_scope_unique
  by (auto simp: generation_payload_scope_def prod_eq_iff; blast)

lemma generation_payload_scope_source:
  assumes "generation_payload_scope z k"
  shows "generation_at_context (fst z) (snd z)"
  using assms by (simp add: generation_payload_scope_def)

lemma generation_payload_scope_subject:
  assumes "generation_payload_scope z k"
  shows "program_scope_subject k"
  using assms generation_program_scope_closed by (auto simp: generation_payload_scope_def)

definition generation_payload_scope_presents ::
  "(generation_source\<times>program_context) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_payload_scope_presents z t \<longleftrightarrow>
    generation_source_presents (fst z) t \<and> generation_payload_scope (fst z) (snd z)"

theorem generation_payload_scope_presentation_class:
  "presentation_class generation_payload_scope_presents
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_payload_scope_presents z t)"
proof -
  have determined: "presentation_class
      (\<lambda>z t. generation_source_presents (fst z) t \<and> generation_payload_scope (fst z) (snd z))
      (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and> generation_payload_scope (fst z) (snd z))
      (\<lambda>t. \<exists>z k. generation_source_presents z t \<and> generation_payload_scope z k)"
    by (rule presentation_class_determined[OF generation_source_presentation_class generation_payload_scope_unique])
  have domain: "(generation_at_context (fst z) (snd z) \<and> generation_payload_scope z k) \<longleftrightarrow>
      generation_payload_scope z k" for z k
    using generation_payload_scope_source by blast
  have admission: "(\<exists>z k. generation_source_presents z t \<and> generation_payload_scope z k) \<longleftrightarrow>
      (\<exists>z. generation_payload_scope_presents z t)" for t
    by (auto simp: generation_payload_scope_presents_def; metis fst_conv snd_conv)
  show ?thesis using determined
    by (simp only: presentation_class_def generation_payload_scope_presents_def domain admission)
qed

interpretation generation_payload_sources: presentation_class generation_payload_scope_presents
  "\<lambda>z. generation_payload_scope (fst z) (snd z)" "\<lambda>t. \<exists>z. generation_payload_scope_presents z t"
  by (rule generation_payload_scope_presentation_class)

theorem generation_payload_scope_quotation_class:
  "presentation_class
    (composed_presentation generation_payload_scope_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_payload_scope_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_payload_scope_presentation_class])
    (use generation_source_presents_formed in \<open>auto simp: generation_payload_scope_presents_def\<close>)

section \<open>The report presents the scope of the actual payload\<close>

definition generation_payload_report_presents ::
  "(generation_source\<times>program_context) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_payload_report_presents z t \<longleftrightarrow> generation_payload_scope (fst z) (snd z) \<and>
    factor_pair_presents generation_source_presents program_scope_value_presents z t"

theorem generation_payload_report_presentation_class:
  "presentation_class generation_payload_report_presents
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_payload_report_presents z t)"
proof -
  let ?R="factor_pair_presents generation_source_presents program_scope_value_presents"
  let ?D="\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and> program_scope_subject (snd z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. generation_source_presents z p) \<and>
    (122,q)\<in>positive_meaning package_retention_admission_system \<and> t=Pair_Term p q"
  have raw: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF generation_source_presentation_class program_scope_value_presentation_class])
  have restricted: "presentation_class
      (\<lambda>z t. generation_payload_scope (fst z) (snd z) \<and> ?R z t)
      (\<lambda>z. generation_payload_scope (fst z) (snd z))
      (\<lambda>t. \<exists>z. generation_payload_scope (fst z) (snd z) \<and> ?R z t)"
    by (rule presentation_class_subdomain[OF raw])
      (use generation_payload_scope_source generation_payload_scope_subject in blast)
  show ?thesis using restricted by (simp only: presentation_class_def generation_payload_report_presents_def)
qed

theorem generation_payload_report_relation:
  "(\<exists>z. generation_payload_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation generation_source_presents program_scope_value_presents generation_payload_scope p q"
  by (auto simp: generation_payload_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

corollary generation_payload_report_at_presentations:
  assumes source: "generation_source_presents z p" and expected: "program_scope_value_presents k q"
  shows "(\<exists>w. generation_payload_report_presents w (Pair_Term p q)) \<longleftrightarrow> generation_payload_scope z k"
  by (simp only: generation_payload_report_relation
    presented_relation_at[OF generation_source_presentation_class program_scope_value_presentation_class assms])

theorem generation_payload_report_exact_body:
  assumes source: "generation_source_presents ((E,(u,r)),G) p" and expected: "program_scope_value_presents k q"
  shows "(\<exists>z. generation_payload_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    (\<exists>C cr v. generation_payload G=Whole_Artifact C \<and>
      complete_data_quoted_at C cr v \<and> program_scope_value_presents k v)"
proof -
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have formed: "generation_formed G" by (rule generation_at_formed[OF actual])
  show ?thesis by (simp only: generation_payload_report_at_presentations[OF assms])
    (use actual formed in \<open>auto simp: generation_payload_scope_def generation_program_scope_def
      program_scope_quoted_at_def site_value_quoted_at_def\<close>)
qed

lemma generation_payload_report_formed:
  assumes "generation_payload_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where first: "generation_source_presents (fst z) p"
    and second: "program_scope_value_presents (snd z) q" and shape: "t=Pair_Term p q"
    using assms by (auto simp: generation_payload_report_presents_def factor_pair_presents_def)
  show ?thesis using generation_source_presents_formed[OF first] site_value_presents_formed second shape by auto
qed

theorem generation_payload_report_quotation_class:
  "presentation_class
    (composed_presentation generation_payload_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_payload_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_payload_report_presentation_class])
    (use generation_payload_report_formed in blast)

section \<open>Every closed program scope has actual generation presentations\<close>

theorem generation_payload_scope_total:
  assumes scope: "program_scope_subject k" and locus: "target_formed l"
    and cause: "target_formed c" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>E u C. generation_at E u [] (Generation l V (Whole_Artifact C) c) \<and>
    generation_source_environment E u []=E \<and>
    generation_payload_scope ((E,(u,[])),Generation l V (Whole_Artifact C) c) k \<and>
    program_scope_quoted_at C [] (fst (fst k)) (fst (snd (fst k))) (snd (snd (fst k))) (snd k)"
proof -
  obtain F v r P where coordinates: "k=((F,(v,r)),P)" by (cases k; auto)
  have closed: "closed_native_package_at F v r P" using scope coordinates by simp
  have package: "native_package_at F v r P" using closed by (simp add: closed_native_package_at_def)
  have minimal: "native_package_environment F v r=F" by (rule native_package_closed_environment_fixed[OF closed])
  obtain C where cf: "exact_formed C" and quote: "program_scope_quoted_at C [] F v r P"
    using program_scope_quoted_total[OF package] minimal by auto
  let ?G="Generation l V (Whole_Artifact C) c"
  have formed: "generation_formed ?G"
    by (rule generation_formed.formed[OF locus _ cause predecessors]) (use cf in simp)
  obtain E :: "local_address option artifact_environment" and u where source: "generation_at E u [] ?G"
    and retained: "generation_environment_closed E {(u,[])}"
    using closed_generation_presentation_total[OF formed] by blast
  have canonical: "generation_source_environment E u []=E" by (rule generation_source_environment_fixed[OF retained])
  have carried: "generation_payload_scope ((E,(u,[])),?G) k"
    using source formed quote coordinates by (auto simp: generation_payload_scope_def generation_program_scope_def)
  show ?thesis using source canonical carried quote coordinates by auto
qed

theorem generation_payload_report_total:
  assumes scope: "generation_payload_scope z k"
  shows "\<exists>p q. generation_source_presents z p \<and> program_scope_value_presents k q \<and>
    generation_payload_report_presents (z,k) (Pair_Term p q) \<and>
    complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
proof -
  obtain p where first: "generation_source_presents z p"
    using generation_sources.total[OF generation_payload_scope_source[OF scope]] by blast
  have target: "presentation_class program_scope_value_presents program_scope_subject
      (\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system)"
    by (rule program_scope_value_presentation_class)
  obtain q where second: "program_scope_value_presents k q"
    using presentation_class.total[OF target generation_payload_scope_subject[OF scope]] by blast
  have report: "generation_payload_report_presents (z,k) (Pair_Term p q)"
    using scope first second by (simp add: generation_payload_report_presents_def)
  have formed: "term_formed (Pair_Term p q)" and closed: "self_contained_term (Pair_Term p q)"
    using generation_payload_report_formed[OF report] by blast+
  have quote: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    by (rule complete_data_quotation_total[OF formed closed])
  show ?thesis using first second report quote by blast
qed

corollary generation_payload_report_outer_invariance:
  assumes first: "generation_source_presents ((E,(u,r)),G) p"
    and second: "generation_source_presents ((F,(v,a)),H) p'"
    and payload: "generation_payload G=generation_payload H"
    and expected: "program_scope_value_presents k q"
  shows "(\<exists>z. generation_payload_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    (\<exists>z. generation_payload_report_presents z (Pair_Term p' q))"
  by (simp only: generation_payload_report_exact_body[OF first expected]
    generation_payload_report_exact_body[OF second expected] payload)

section \<open>The actual payload citation retains its complete quoted material\<close>

theorem generation_payload_scope_material:
  assumes presented: "generation_payload_scope_presents (((E,(u,r)),G),((F,(pu,pr)),P)) t"
  shows "\<exists>C cr v R lr M payr cause_r cite I cu.
    generation_payload G=Whole_Artifact C \<and> artifact_at E cu C \<and>
    complete_data_quoted_at C cr v \<and> program_scope_value_presents ((F,(pu,pr)),P) v \<and>
    term_quoted_at E cu cr v (rra_carrier (object_structure C)) {} \<and>
    artifact_at E u R \<and> generation_syntax_at R r lr M payr cause_r \<and>
    citation_at R payr cite I \<and> interpret_citation E u cite (Whole_Artifact C) \<and>
    ((cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu))"
proof -
  have source: "generation_source_presents ((E,(u,r)),G) t"
    and scope: "generation_program_scope G F pu pr P"
    using presented by (auto simp: generation_payload_scope_presents_def generation_payload_scope_def)
  have gen: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  obtain C cr v where payload: "generation_payload G=Whole_Artifact C"
    and body: "complete_data_quoted_at C cr v" and body_value: "program_scope_value_presents ((F,(pu,pr)),P) v"
    using scope by (auto simp: generation_program_scope_def program_scope_quoted_at_def site_value_quoted_at_def)
  obtain R lr M payr cause_r where art: "artifact_at E u R"
    and layout: "generation_syntax_at R r lr M payr cause_r" and anchored: "anchored_at E u payr (generation_payload G)"
    using generation_presented_fields[OF source] by blast
  obtain S cite I where other: "artifact_at E u S" and citation: "citation_at S payr cite I"
    and interpreted: "interpret_citation E u cite (Whole_Artifact C)"
    using anchored payload by (auto simp: anchored_at_def)
  have same: "R=S" by (rule environment_artifact_unique[OF ef art other])
  have read_citation: "citation_at R payr cite I" using citation same by simp
  obtain cu where material: "artifact_at E cu C"
    and resolution: "(cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu)"
    using interpreted by (cases cite) auto
  have native: "term_quoted_at E cu cr v (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF body] ef material])
  show ?thesis using payload material body body_value native art layout read_citation interpreted resolution by blast
qed

text \<open>
  The relation is the existing actual generation reading linked to the
  independently specified program carried by its payload. The source class
  derives that program and scope without storing another copy. The report
  class admits every compatible scope value while keeping the artifact's
  actual quoted body and citation use distinct from the expected report.

  Every closed program scope is carried by some actual generation with any
  formed locus, cause, and predecessor set. The outer generation environment
  may already be its least source environment. The material theorem retains
  the payload citation, actual artifact use, and complete quotation. None of
  these relations validates the cause or selects a program as an authority.
\<close>

end
