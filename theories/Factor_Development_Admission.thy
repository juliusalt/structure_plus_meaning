theory Factor_Development_Admission
  imports Factor_Development_Cycle
begin

lemma development_candidate_observation_exact:
  assumes evidence: "development_condition_family_evidence Q ys observations"
    and candidate: "m<length ys" and facet: "f<length (development_conditions Q)"
  shows "development_candidate_observation ys observations m w f \<longleftrightarrow>
    development_condition_holds (development_conditions Q!f) (development_problem Q) (ys!m)"
proof -
  have length: "length observations=length (development_conditions Q)"
    using evidence by (simp add: development_condition_family_evidence_def)
  obtain execution where actual: "observations!f=Some execution"
    and valid: "development_condition_evidence (development_conditions Q!f) (development_problem Q) ys execution"
    using evidence facet by (auto simp: development_condition_family_evidence_def length split: option.splits)
  have member: "ys!m\<in>set ys" by (rule nth_mem[OF candidate])
  show ?thesis using development_condition_evidence_exact[OF valid, of "ys!m"]
    by (simp add: development_candidate_observation_def candidate length facet actual member)
qed

lemma development_compare_adequate:
  "m\<in>set (snd (snd (snd (development_compare ys observations)))) \<longleftrightarrow>
    m<length ys \<and> (\<forall>f<length observations. development_candidate_observation ys observations m 0 f)"
  by (auto simp: development_compare_def assessed_subject_investigation_equation subject_investigation_adequate_def)

lemma development_selected_value:
  assumes "y\<in>set (map (nth ys) (snd (snd (snd (development_compare ys observations)))))"
  obtains m where "m<length ys" "y=ys!m"
    "\<forall>f<length observations. development_candidate_observation ys observations m 0 f"
  using assms by (auto simp: development_compare_adequate)

lemma native_development_admission_fields:
  assumes admitted: "native_development_admission Q report=Some accepted"
  obtains G observations review where
    "development_generation report=Some G"
    "finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)=Some G"
    "development_observed_conditions report=Some observations"
    "development_condition_family_evidence Q (development_generated_values Q G) observations"
    "development_scope_review report=Some review"
    "development_condition_evidence (development_scope_criticism Q)
      (development_review_input Q (development_generated_values Q G) observations)
      [development_review_input Q (development_generated_values Q G) observations] review"
    "development_condition_outputs review=[development_review_input Q (development_generated_values Q G) observations]"
    "accepted=map (nth (development_generated_values Q G))
      (snd (snd (snd (development_compare (development_generated_values Q G) observations))))"
    "development_comparison report=Some (development_compare (development_generated_values Q G) observations)"
    "development_revision report=Some (development_revise (development_generated_values Q G) observations
      (development_selected_facets Q))"
    "development_conditions Q\<noteq>[]"
    "condition_goals (development_scope_criticism Q)\<noteq>[]"
  using admitted by (auto simp: native_development_admission_def Let_def split: option.splits if_splits)

theorem native_development_original_conditions:
  assumes admitted: "native_development_admission Q report=Some accepted"
    and chosen: "y\<in>set accepted" and original: "C\<in>set (development_conditions Q)"
  shows "development_condition_holds C (development_problem Q) y"
proof -
  obtain G observations where evidence:
    "development_condition_family_evidence Q (development_generated_values Q G) observations"
    and selected: "accepted=map (nth (development_generated_values Q G))
      (snd (snd (snd (development_compare (development_generated_values Q G) observations))))"
    by (rule native_development_admission_fields[OF admitted]) blast
  obtain m where candidate: "m<length (development_generated_values Q G)"
    and selected_value: "y=development_generated_values Q G!m"
    and qualities: "\<forall>f<length observations.
      development_candidate_observation (development_generated_values Q G) observations m 0 f"
    by (rule development_selected_value[OF chosen[unfolded selected]]) blast
  obtain f where bound: "f<length (development_conditions Q)" and C: "C=development_conditions Q!f"
    using original by (auto simp: in_set_conv_nth)
  have length: "length observations=length (development_conditions Q)"
    using evidence by (simp add: development_condition_family_evidence_def)
  have observation: "development_candidate_observation (development_generated_values Q G) observations m 0 f"
    using qualities bound by (simp only: length; blast)
  show ?thesis using observation development_candidate_observation_exact[OF evidence candidate bound]
    by (simp only: C selected_value)
qed

theorem native_development_generated_origin:
  assumes admitted: "native_development_admission Q report=Some accepted" and chosen: "y\<in>set accepted"
  shows "\<exists>P D A rows. finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)=Some (P,D,A,rows) \<and>
    (development_generator_entry Q,Pair_Term (decode_finite_term (development_problem Q)) (decode_finite_term y))
      \<in>positive_meaning (decode_finite_system P)"
proof -
  obtain G observations where generation:
    "finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)=Some G"
    and selected: "accepted=map (nth (development_generated_values Q G))
      (snd (snd (snd (development_compare (development_generated_values Q G) observations))))"
    by (rule native_development_admission_fields[OF admitted]) blast
  obtain m where candidate: "m<length (development_generated_values Q G)"
    and selected_value: "y=development_generated_values Q G!m"
    and qualities: "\<forall>f<length observations.
      development_candidate_observation (development_generated_values Q G) observations m 0 f"
    by (rule development_selected_value[OF chosen[unfolded selected]]) blast
  have member: "y\<in>set (development_generated_values Q G)"
    using nth_mem[OF candidate] by (simp only: selected_value)
  obtain P D A rows where shape: "G=(P,D,A,rows)" by (cases G) auto
  have call: "(development_generator_entry Q,Pair_Term (decode_finite_term (development_problem Q)) (decode_finite_term y))
      \<in>positive_meaning (decode_finite_system P)"
    by (rule finite_generated_outputs_sound[OF generation[unfolded shape]])
      (use member in \<open>simp only: development_generated_values_def shape case_prod_conv\<close>)
  show ?thesis using generation call by (auto simp: shape)
qed

theorem native_development_original_criticism:
  assumes "native_development_admission Q report=Some accepted"
  obtains G observations where
    "development_generation report=Some G" "development_observed_conditions report=Some observations"
    "development_condition_family_evidence Q (development_generated_values Q G) observations"
    "development_condition_holds (development_scope_criticism Q)
      (development_review_input Q (development_generated_values Q G) observations)
      (development_review_input Q (development_generated_values Q G) observations)"
proof -
  obtain G observations review where generated: "development_generation report=Some G"
    and observed: "development_observed_conditions report=Some observations"
    and evidence: "development_condition_family_evidence Q (development_generated_values Q G) observations"
    and valid: "development_condition_evidence (development_scope_criticism Q)
      (development_review_input Q (development_generated_values Q G) observations)
      [development_review_input Q (development_generated_values Q G) observations] review"
    and outputs: "development_condition_outputs review=[development_review_input Q (development_generated_values Q G) observations]"
    by (rule native_development_admission_fields[OF assms]) blast
  have holds: "development_condition_holds (development_scope_criticism Q)
      (development_review_input Q (development_generated_values Q G) observations)
      (development_review_input Q (development_generated_values Q G) observations)"
    using development_condition_evidence_exact[OF valid] by (simp only: outputs set_simps; blast)
  show thesis by (rule that[OF generated observed evidence holds])
qed

corollary missing_native_development_phase_refuses:
  "development_generation report=None \<or> development_compiled_conditions report=None \<or>
    development_observed_conditions report=None \<or> development_scope_review report=None \<or>
    development_comparison report=None \<or> development_revision report=None \<Longrightarrow>
    native_development_admission Q report=None"
  by (auto simp: native_development_admission_def Let_def split: option.splits if_splits)

text \<open>
  Admission is tied to the original question, every original native criterion,
  actual generation and independent criticism. An omitted operation or changed
  result fails this gate. Every accepted candidate occurrence has both its
  original generator judgment and every original criterion judgment; the
  evidence family and native whole-scope criticism are mandatory. Partial facet
  selections affect the derived revision report, never this semantic guarantee.
\<close>

end
