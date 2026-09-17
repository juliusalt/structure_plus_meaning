theory Finite_Presented_Reviews
  imports Finite_Presented_Investigations Finite_Partial_Result_Inspection Finite_Term_Observation_Comparisons
    Finite_Inference_Histories
begin

section \<open>Collection differences, comparisons and partial results present their elements\<close>

definition finite_collection_differences_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a fset\<times>'a fset \<Rightarrow> finite_factor_term" where
  "finite_collection_differences_value element=finite_pair_presentation (finite_collection_presentation element)
    (finite_collection_presentation element)"

lemma finite_collection_differences_value_injective [intro]:
  "inj element \<Longrightarrow> inj (finite_collection_differences_value element)"
  unfolding finite_collection_differences_value_def
  by (intro finite_pair_presentation_injective finite_collection_presentation_injective)

definition finite_observation_comparison_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('a fset\<times>'a fset) option \<Rightarrow> finite_factor_term" where
  "finite_observation_comparison_value element=finite_option_presentation (finite_collection_differences_value element)"

lemma finite_observation_comparison_value_injective [intro]:
  "inj element \<Longrightarrow> inj (finite_observation_comparison_value element)"
  unfolding finite_observation_comparison_value_def
  by (intro finite_option_presentation_injective finite_collection_differences_value_injective)

definition finite_partial_result_assessment_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a finite_partial_result_assessment \<Rightarrow> finite_factor_term" where
  "finite_partial_result_assessment_value element=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation (finite_observation_comparison_value element)
      (finite_pair_presentation finite_boolean_data finite_boolean_data))"

lemma finite_partial_result_assessment_value_injective [intro]:
  "inj element \<Longrightarrow> inj (finite_partial_result_assessment_value element)"
  unfolding finite_partial_result_assessment_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective
      finite_observation_comparison_value_injective)

definition finite_evidence_assessment_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a finite_partial_result_assessment\<times>bool\<times>bool \<Rightarrow> finite_factor_term" where
  "finite_evidence_assessment_value element=finite_pair_presentation (finite_partial_result_assessment_value element)
    (finite_pair_presentation finite_boolean_data finite_boolean_data)"

lemma finite_evidence_assessment_value_injective [intro]:
  "inj element \<Longrightarrow> inj (finite_evidence_assessment_value element)"
  unfolding finite_evidence_assessment_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective
      finite_partial_result_assessment_value_injective)

section \<open>Iterations and witnessed histories present every offered state\<close>

definition finite_iteration_check_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a\<times>'a\<times>bool \<Rightarrow> finite_factor_term" where
  "finite_iteration_check_value state=finite_pair_presentation state (finite_pair_presentation state finite_boolean_data)"

lemma finite_iteration_check_value_injective [intro]:
  "inj state \<Longrightarrow> inj (finite_iteration_check_value state)"
  unfolding finite_iteration_check_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective)

definition finite_iteration_review_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a iteration_review \<Rightarrow> finite_factor_term" where
  "finite_iteration_review_value state=finite_pair_presentation
    (finite_sequence_presentation (finite_iteration_check_value state)) (finite_iteration_check_value state)"

lemma finite_iteration_review_value_injective [intro]:
  "inj state \<Longrightarrow> inj (finite_iteration_review_value state)"
  unfolding finite_iteration_review_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
      finite_iteration_check_value_injective)

definition finite_witnessed_history_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('w \<Rightarrow> finite_factor_term) \<Rightarrow> ('a\<times>'w fset) list \<Rightarrow> finite_factor_term" where
  "finite_witnessed_history_value state witness=finite_sequence_presentation
    (finite_pair_presentation state (finite_collection_presentation witness))"

lemma finite_witnessed_history_value_injective [intro]:
  "inj state \<Longrightarrow> inj witness \<Longrightarrow> inj (finite_witnessed_history_value state witness)"
  unfolding finite_witnessed_history_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
      finite_collection_presentation_injective)

definition finite_witness_review_value ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('w \<Rightarrow> finite_factor_term) \<Rightarrow> ('a\<times>'w fset\<times>'w fset) list \<Rightarrow> finite_factor_term" where
  "finite_witness_review_value state witness=finite_sequence_presentation
    (finite_pair_presentation state (finite_collection_differences_value witness))"

lemma finite_witness_review_value_injective [intro]:
  "inj state \<Longrightarrow> inj witness \<Longrightarrow> inj (finite_witness_review_value state witness)"
  unfolding finite_witness_review_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
      finite_collection_differences_value_injective)

text \<open>
  These presentations belong to the generic notions they are named after: the
  extra and missing members of two collections, an optional observation
  comparison, a partial result assessment with its readiness, preservation and
  refusal, an assessment accompanied by two evidence checks, every offered
  iteration state with its expected state and progress, a history of states with
  their witnesses, and the extra and missing witnesses at each state. Every
  presentation is parameterized by the presentations of its elements and states
  only their injectivity contracts; a family specializes them with its own
  notions. No presentation computes an observation of its subject.
\<close>

end
