theory Factor_Presentation_Transport
  imports Presentation_Contracts Factor_Presentation_Classes
begin

section \<open>Existing native comparisons export local relation contracts\<close>

interpretation artifact_identity_contract: presented_relation_contract
  artifact_value_presents exact_formed "\<lambda>t. (11,t)\<in>positive_meaning artifact_admission_system"
  artifact_value_presents exact_formed "\<lambda>t. (11,t)\<in>positive_meaning artifact_admission_system"
  "(=)" "\<lambda>p q. (12,Pair_Term p q)\<in>positive_meaning artifact_identity_system"
  by (unfold_locales)
    (use artifact_presentations.presentation_class_axioms artifact_identity_presented in
      \<open>auto simp: presentation_class_def\<close>)

interpretation environment_identity_contract: presented_relation_contract
  environment_value_presents environment_formed
    "\<lambda>t. (26,t)\<in>positive_meaning environment_admission_system"
  environment_value_presents environment_formed
    "\<lambda>t. (26,t)\<in>positive_meaning environment_admission_system"
  "(=)" "\<lambda>p q. (27,Pair_Term p q)\<in>positive_meaning environment_identity_system"
  by (unfold_locales)
    (use environment_presentations.presentation_class_axioms environment_identity_presented in
      \<open>auto simp: presentation_class_def\<close>)

theorem artifact_identity_adaptation:
  assumes "presentation_class R exact_formed A" "presentation_class S exact_formed B"
  shows "presented_relation_contract R exact_formed A S exact_formed B (=)
    (adapted_relation artifact_value_presents artifact_value_presents R S
      (\<lambda>p q. (12,Pair_Term p q)\<in>positive_meaning artifact_identity_system))"
  by (rule artifact_identity_contract.adaptation_contract[OF assms])

theorem environment_identity_adaptation:
  assumes "presentation_class R environment_formed A" "presentation_class S environment_formed B"
  shows "presented_relation_contract R environment_formed A S environment_formed B (=)
    (adapted_relation environment_value_presents environment_value_presents R S
      (\<lambda>p q. (27,Pair_Term p q)\<in>positive_meaning environment_identity_system))"
  by (rule environment_identity_contract.adaptation_contract[OF assms])

section \<open>The same constructors transport their complete components\<close>

lemma factor_pair_presentation_transport:
  "presentation_transport (factor_pair_presents R S) (factor_pair_presents R' S')
      (Pair_Term p q) (Pair_Term p' q') \<longleftrightarrow>
    presentation_transport R R' p p' \<and> presentation_transport S S' q q'"
  by (auto simp: presentation_transport_def factor_pair_presents_def; metis fst_conv snd_conv)

lemma data_sequence_presentation_transport:
  "presentation_transport (data_sequence_presents R) (data_sequence_presents S)
      (data_list_term ps) (data_list_term qs) \<longleftrightarrow>
    list_all2 (presentation_transport R S) ps qs"
  using presentation_transport_lists[of R S ps qs]
  by (auto simp: presentation_transport_def data_sequence_presents_def data_list_term_injective)

theorem data_collection_presentation_change:
  assumes "presentation_class R D A" "presentation_class S D B"
  shows "presentation_change (data_collection_presents R) (\<lambda>X. finite X \<and> (\<forall>a\<in>X. D a))
    (presented_predicate (data_sequence_presents R) distinct)
    (data_collection_presents S) (presented_predicate (data_sequence_presents S) distinct)"
  by (rule presentation_change.intro)
    (rule data_collection_presentation_class[OF assms(1)],
      rule data_collection_presentation_class[OF assms(2)])

section \<open>Quotation changes the presentation while retaining its actual body\<close>

theorem complete_quotation_presentation_change:
  assumes source: "presentation_class R D A"
    and boundary: "\<And>t. A t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  shows "presentation_change R D A
    (composed_presentation R (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>p. \<exists>t. A t \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule presentation_change.intro[OF source])
    (rule complete_quotation_presentation_class[OF source boundary])

interpretation artifact_quotation_change: presentation_change
  artifact_value_presents exact_formed "\<lambda>t. (11,t)\<in>positive_meaning artifact_admission_system"
  "composed_presentation artifact_value_presents
    (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)"
  "\<lambda>p. \<exists>t. (11,t)\<in>positive_meaning artifact_admission_system \<and>
    complete_data_quoted_at (fst p) (snd p) t"
  by (rule complete_quotation_presentation_change[OF artifact_presentations.presentation_class_axioms])
    (use artifact_value_presents_formed in \<open>auto simp: artifact_admission_exact\<close>)

theorem artifact_data_to_quotation:
  "presentation_transport artifact_value_presents
      (composed_presentation artifact_value_presents
        (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)) t (C,r) \<longleftrightarrow>
    (\<exists>u. (12,Pair_Term t u)\<in>positive_meaning artifact_identity_system \<and>
      complete_data_quoted_at C r u)"
  by (auto simp: presentation_transport_def composed_presentation_def
    artifact_identity_contract.exact presented_relation_def)

theorem artifact_quoted_identity_contract:
  "presented_relation_contract
    (composed_presentation artifact_value_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)) exact_formed
    (\<lambda>p. \<exists>t. (11,t)\<in>positive_meaning artifact_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t)
    (composed_presentation artifact_value_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t)) exact_formed
    (\<lambda>p. \<exists>t. (11,t)\<in>positive_meaning artifact_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t) (=)
    (adapted_relation artifact_value_presents artifact_value_presents
      (composed_presentation artifact_value_presents
        (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
      (composed_presentation artifact_value_presents
        (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
      (\<lambda>p q. (12,Pair_Term p q)\<in>positive_meaning artifact_identity_system))"
  by (rule artifact_identity_contract.adaptation_contract)
    (rule artifact_quotation_change.target.presentation_class_axioms)+

theorem subject_transport_does_not_replace_quoted_body:
  assumes "R a t" "R a u" "t\<noteq>u" "complete_data_quoted_at C r u"
  shows "presentation_transport R
      (composed_presentation R (\<lambda>v p. complete_data_quoted_at (fst p) (snd p) v)) t (C,r) \<and>
    \<not>complete_data_quoted_at C r t"
  using assms complete_data_quotation_unique
  by (auto simp: presentation_transport_def composed_presentation_def; blast)

text \<open>
  Artifact and environment identity now export the same relation contract.
  Their existing native exactness theorems discharge the local proof once;
  adaptation then applies to every independently exact class of those same
  subjects. Pair and sequence transport is componentwise. Finite-collection
  transport comes from the whole set class and allows independent orders.

  The quotation example uses different presentation types and the existing
  complete material account. A direct value can correspond to a quotation of
  another presentation of the same artifact. The quoted source still contains
  its actual body. The final theorem preserves this distinction even when the
  two bodies differ. The adapted contracts are mathematical relations; the
  only native identity operation used here is the already admitted reader.
\<close>

end
