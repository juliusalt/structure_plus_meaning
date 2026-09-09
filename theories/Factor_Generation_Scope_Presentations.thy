theory Factor_Generation_Scope_Presentations
  imports Factor_Generation_Presentations Factor_Generation_Causes Factor_Native_Equality
begin

section \<open>The whole recorded cause determines its quoted judgment context\<close>

definition generation_recorded_scope :: "generation_source \<Rightarrow> judgment_context \<Rightarrow> bool" where
  "generation_recorded_scope z j \<longleftrightarrow>
    generation_judgment_scope_at (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z)
      (fst j) (fst (fst (snd j))) (snd (fst (snd j))) (fst (snd (snd j))) (snd (snd (snd j)))"

lemma generation_recorded_scope_unique:
  assumes "generation_recorded_scope z j" "generation_recorded_scope z k"
  shows "j=k"
  using generation_judgment_scope_unique[OF assms[unfolded generation_recorded_scope_def] refl]
  by (auto simp: prod_eq_iff)

lemma generation_recorded_scope_source:
  assumes "generation_recorded_scope z j"
  shows "generation_at_context (fst z) (snd z)"
  using assms by (auto simp: generation_recorded_scope_def generation_judgment_scope_at_def)

lemma generation_recorded_scope_formed:
  assumes scope: "generation_recorded_scope z j"
  shows "judgment_context_formed j"
proof -
  obtain C r where quote: "judgment_value_quoted_at C r (fst j)
      (fst (fst (snd j))) (snd (fst (snd j))) (fst (snd (snd j))) (snd (snd (snd j)))"
    using generation_judgment_scope_cause[OF scope[unfolded generation_recorded_scope_def]] by blast
  show ?thesis using judgment_value_quoted_formed[OF quote] by (simp add: judgment_context_formed_def)
qed

definition generation_recorded_scope_presents ::
  "(generation_source\<times>judgment_context) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_recorded_scope_presents z t \<longleftrightarrow>
    generation_source_presents (fst z) t \<and> generation_recorded_scope (fst z) (snd z)"

theorem generation_recorded_scope_presentation_class:
  "presentation_class generation_recorded_scope_presents
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_recorded_scope_presents z t)"
unfolding generation_recorded_scope_presents_def
  by (rule presentation_class_determined_subdomain[OF generation_source_presentation_class generation_recorded_scope_unique generation_recorded_scope_source])

theorem generation_recorded_scope_quotation_class:
  "presentation_class
    (composed_presentation generation_recorded_scope_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_recorded_scope_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_recorded_scope_presentation_class])
    (use generation_source_presents_formed in \<open>auto simp: generation_recorded_scope_presents_def\<close>)

section \<open>An expected scope report remains linked to the actual quoted body\<close>

definition generation_scope_report_presents ::
  "(generation_source\<times>judgment_context) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_scope_report_presents z t \<longleftrightarrow> generation_recorded_scope (fst z) (snd z) \<and>
    factor_pair_presents generation_source_presents judgment_context_presents z t"

theorem generation_scope_report_presentation_class:
  "presentation_class generation_scope_report_presents
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>t. \<exists>z. generation_scope_report_presents z t)"
unfolding generation_scope_report_presents_def
  by (rule factor_pair_subdomain_class[OF generation_source_presentation_class judgment_context_presentation_class])
    (use generation_recorded_scope_source generation_recorded_scope_formed in blast)

theorem generation_scope_report_relation:
  "(\<exists>z. generation_scope_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation generation_source_presents judgment_context_presents generation_recorded_scope p q"
  by (auto simp: generation_scope_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

corollary generation_scope_report_at_presentations:
  assumes source: "generation_source_presents z p" and expected: "judgment_context_presents j q"
  shows "(\<exists>w. generation_scope_report_presents w (Pair_Term p q)) \<longleftrightarrow> generation_recorded_scope z j"
  by (simp only: generation_scope_report_relation
    presented_relation_at[OF generation_source_presentation_class judgment_context_presentation_class assms])

theorem generation_scope_report_exact_body:
  assumes source: "generation_source_presents ((E,(u,r)),G) p" and expected: "judgment_context_presents j q"
  shows "(\<exists>z. generation_scope_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    (\<exists>C cr v. generation_cause G=Whole_Artifact C \<and>
      complete_data_quoted_at C cr v \<and> judgment_context_presents j v)"
proof -
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  show ?thesis
    by (simp only: generation_scope_report_at_presentations[OF assms])
      (use actual in \<open>auto simp: generation_recorded_scope_def generation_judgment_scope_at_def
        judgment_value_quoted_at_def; blast\<close>)
qed

lemma generation_scope_report_formed:
  assumes "generation_scope_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where first: "generation_source_presents (fst z) p"
    and second: "judgment_context_presents (snd z) q" and shape: "t=Pair_Term p q"
    using assms by (auto simp: generation_scope_report_presents_def factor_pair_presents_def)
  show ?thesis using generation_source_presents_formed[OF first] judgment_context_formed_value[OF second] shape by simp
qed

theorem generation_scope_report_quotation_class:
  "presentation_class
    (composed_presentation generation_scope_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_scope_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_scope_report_presentation_class])
    (use generation_scope_report_formed in blast)

theorem generation_recorded_scope_material:
  assumes presented: "generation_recorded_scope_presents (((E,(u,r)),G),(F,((pu,pr),(au,ar)))) t"
  shows "\<exists>C cr v R lr M payr cause_r cite I cu.
    generation_cause G=Whole_Artifact C \<and> artifact_at E cu C \<and>
    complete_data_quoted_at C cr v \<and> judgment_value_presents F pu pr au ar v \<and>
    term_quoted_at E cu cr v (rra_carrier (object_structure C)) {} \<and>
    artifact_at E u R \<and> generation_syntax_at R r lr M payr cause_r \<and>
    citation_at R cause_r cite I \<and> interpret_citation E u cite (Whole_Artifact C) \<and>
    ((cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu))"
proof -
  have source: "generation_source_presents ((E,(u,r)),G) t"
    and scope: "generation_judgment_scope_at E u r G F pu pr au ar"
    using presented by (auto simp: generation_recorded_scope_presents_def generation_recorded_scope_def)
  have gen: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  obtain C cr where cause: "generation_cause G=Whole_Artifact C"
    and quote: "judgment_value_quoted_at C cr F pu pr au ar"
    using generation_judgment_scope_cause[OF scope] by blast
  obtain v where body: "complete_data_quoted_at C cr v" and body_value: "judgment_value_presents F pu pr au ar v"
    using quote by (auto simp: judgment_value_quoted_at_def)
  obtain R lr M payr cause_r where art: "artifact_at E u R"
    and layout: "generation_syntax_at R r lr M payr cause_r" and anchored: "anchored_at E u cause_r (generation_cause G)"
    using generation_presented_fields[OF source] by blast
  obtain S cite I where other: "artifact_at E u S" and citation: "citation_at S cause_r cite I"
    and interpreted: "interpret_citation E u cite (Whole_Artifact C)"
    using anchored cause by (auto simp: anchored_at_def)
  have same: "R=S" by (rule environment_artifact_unique[OF ef art other])
  have read_citation: "citation_at R cause_r cite I" using citation same by simp
  obtain cu where material: "artifact_at E cu C"
    and resolution: "(cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu)"
    using interpreted by (cases cite) auto
  have native: "term_quoted_at E cu cr v (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF body] ef material])
  show ?thesis using cause material body body_value native art layout read_citation interpreted resolution by blast
qed

section \<open>Every formed context can be recorded without a truth premise\<close>

theorem generation_recorded_scope_total:
  assumes context_formed: "judgment_context_formed j" and locus: "target_formed l"
    and payload: "target_formed p" and predecessors: "\<forall>H\<in>fset P. generation_formed H"
  shows "\<exists>E u C. generation_at E u [] (Generation l P p (Whole_Artifact C)) \<and>
    generation_source_environment E u []=E \<and>
    generation_recorded_scope ((E,(u,[])),Generation l P p (Whole_Artifact C)) j \<and>
    judgment_quotation_presents j (C,[])"
proof -
  obtain F pu pr au ar where coordinates: "j=(F,((pu,pr),(au,ar)))"
    by (rule that[of "fst j" "fst (fst (snd j))" "snd (fst (snd j))"
      "fst (snd (snd j))" "snd (snd (snd j))"]) simp
  have ef: "environment_formed F" and program: "(pu,pr)\<in>environment_positions F"
    and application: "(au,ar)\<in>environment_positions F"
    using context_formed coordinates by (auto simp: judgment_context_formed_def)
  obtain C where cf: "exact_formed C" and quote: "judgment_value_quoted_at C [] F pu pr au ar"
    using judgment_value_quoted_total[OF ef program application] by blast
  let ?G="Generation l P p (Whole_Artifact C)"
  have formed: "generation_formed ?G" by (rule generation_formed.formed[OF locus payload _ predecessors]) (use cf in simp)
  obtain E :: "local_address option artifact_environment" and u where source: "generation_at E u [] ?G"
    and closed: "generation_environment_closed E {(u,[])}"
    using closed_generation_presentation_total[OF formed] by blast
  have canonical: "generation_source_environment E u []=E" by (rule generation_source_environment_fixed[OF closed])
  have scope: "generation_recorded_scope ((E,(u,[])),?G) j"
    using source quote coordinates by (auto simp: generation_recorded_scope_def generation_judgment_scope_at_def)
  have quoted: "judgment_quotation_presents j (C,[])" using quote coordinates by simp
  show ?thesis using source canonical scope quoted by blast
qed

theorem generation_scope_report_total:
  assumes scope: "generation_recorded_scope z j"
  shows "\<exists>p q. generation_source_presents z p \<and> judgment_context_presents j q \<and>
    generation_scope_report_presents (z,j) (Pair_Term p q) \<and>
    complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
proof -
  have source: "generation_at_context (fst z) (snd z)" by (rule generation_recorded_scope_source[OF scope])
  obtain p where first: "generation_source_presents z p" using generation_sources.total[OF source] by blast
  obtain q where second: "judgment_context_presents j q"
    using judgments.total[OF generation_recorded_scope_formed[OF scope]] by blast
  have report: "generation_scope_report_presents (z,j) (Pair_Term p q)"
    using scope first second by (simp add: generation_scope_report_presents_def)
  have formed: "term_formed (Pair_Term p q)" and closed: "self_contained_term (Pair_Term p q)"
    using generation_scope_report_formed[OF report] by blast+
  have quote: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    by (rule complete_data_quotation_total[OF formed closed])
  show ?thesis using first second report quote by blast
qed

corollary generation_scope_report_outer_invariance:
  assumes first: "generation_source_presents ((E,(u,r)),G) p"
    and second: "generation_source_presents ((F,(v,a)),G) p'"
    and expected: "judgment_context_presents j q"
  shows "(\<exists>z. generation_scope_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    (\<exists>z. generation_scope_report_presents z (Pair_Term p' q))"
  by (simp only: generation_scope_report_exact_body[OF first expected] generation_scope_report_exact_body[OF second expected])

section \<open>Exact scope presentation does not validate the recorded cause\<close>

theorem false_recorded_scope_has_invalid_cause:
  assumes scope: "generation_judgment_scope_at E u r G F pu pr au ar"
    and false_call: "\<not>native_positive_holds F pu pr au ar"
  shows "\<not>generation_cause_valid_at E u r G"
proof
  assume valid: "generation_cause_valid_at E u r G"
  have roles: "(\<exists>R. base_admission_judgment_at F pu pr au ar R) \<or>
    (\<exists>xs B W R. construction_judgment_at F pu pr au ar xs B W R)"
    using valid by (auto simp: generation_cause_valid_at_def
      recorded_base_cause_with_scope[OF scope] recorded_construction_cause_with_scope[OF scope])
  from roles consider (base) R where "base_admission_judgment_at F pu pr au ar R"
    | (construction) xs B W R where "construction_judgment_at F pu pr au ar xs B W R"
    by blast
  then have "native_positive_holds F pu pr au ar"
  proof cases
    case base
    show ?thesis by (rule base_admission_truth[OF base])
  next
    case construction
    show ?thesis by (rule construction_judgment_truth[OF construction])
  qed
  then show False using false_call by blast
qed

theorem generation_scope_presentations_do_not_validate_causes:
  "\<exists>F pu pr au ar E u G p q.
    native_application_formed F pu pr au ar \<and> \<not>native_positive_holds F pu pr au ar \<and>
    generation_source_environment E u []=E \<and> generation_source_presents ((E,(u,[])),G) p \<and>
    judgment_context_presents (F,((pu,pr),(au,ar))) q \<and>
    generation_scope_report_presents (((E,(u,[])),G),(F,((pu,pr),(au,ar)))) (Pair_Term p q) \<and>
    complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q) \<and>
    \<not>generation_cause_valid_at E u [] G"
proof -
  let ?F="equality_query_environment (Payload_Term [])"
  let ?j="(?F,((None,[0]),(Some [],[])))"
  have tf: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  have call: "native_application_formed ?F None [0] (Some []) []"
    by (rule native_equality_future_application_formed[OF tf])
  have false_call: "\<not>native_positive_holds ?F None [0] (Some []) []"
    by (simp only: native_equality_future_truth[OF tf]) simp
  obtain P d x I K where package: "native_package_at ?F None [0] P"
    and app: "native_application_at ?F (Some []) [] d x I K"
    using call by (auto simp: native_application_formed_def)
  have formed: "environment_formed ?F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have positions: "(None,[0])\<in>environment_positions ?F" "(Some [],[])\<in>environment_positions ?F"
    using native_judgment_positions[OF package app] by blast+
  have context_formed: "judgment_context_formed ?j"
    using formed positions by (simp add: judgment_context_formed_def)
  let ?target="Whole_Artifact empty_artifact"
  have target: "target_formed ?target" by simp
  have predecessors: "\<forall>H\<in>fset {||}. generation_formed H" by simp
  obtain E u C where canonical: "generation_source_environment E u []=E"
    and scope: "generation_recorded_scope ((E,(u,[])),Generation ?target {||} ?target (Whole_Artifact C)) ?j"
    using generation_recorded_scope_total[OF context_formed target target predecessors] by blast
  let ?G="Generation ?target {||} ?target (Whole_Artifact C)"
  obtain p q where first: "generation_source_presents ((E,(u,[])),?G) p"
    and second: "judgment_context_presents ?j q"
    and report: "generation_scope_report_presents (((E,(u,[])),?G),?j) (Pair_Term p q)"
    and quote: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    using generation_scope_report_total[OF scope] by blast
  have recorded: "generation_judgment_scope_at E u [] ?G ?F None [0] (Some []) []"
    using scope by (simp add: generation_recorded_scope_def)
  have invalid: "\<not>generation_cause_valid_at E u [] ?G"
    by (rule false_recorded_scope_has_invalid_cause[OF recorded false_call])
  show ?thesis
    by (rule exI[of _ ?F], rule exI[of _ None], rule exI[of _ "[0]"], rule exI[of _ "Some []"],
      rule exI[of _ "[]"], rule exI[of _ E], rule exI[of _ u], rule exI[of _ ?G],
      rule exI[of _ p], rule exI[of _ q])
      (intro conjI; fact call false_call canonical first second report quote invalid)
qed

text \<open>
  The existing whole cause artifact determines its complete judgment context.
  The class derives that context without a duplicate stored value. Its joint
  report class keeps the expected context related to the source through the
  actual complete quotation. The expected report may use another permitted
  presentation of the same context; the cause artifact still quotes its own
  actual body.

  The material theorem recovers the native cause citation, its local or
  externally bound artifact use, and the complete body read at that use with
  no slots. Every formed context can be recorded with any formed locus,
  payload, and finite formed predecessor collection. The constructed outer
  environment is already its minimal generation scope. Every recorded scope
  has complete report presentations and quotations, and equal cores preserve
  the scope report across outer environments.

  Formation, scope recovery, and cause validity remain separate. A formed
  false native equality call has an actual recorded scope, a complete report,
  and a complete quotation, while its recorded cause is invalid. The class
  construction does not turn the displayed call into a true judgment.
\<close>

end
