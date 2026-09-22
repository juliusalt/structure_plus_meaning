theory Native_Control_Prepared_Cause_Review
  imports Native_Control_Cause_Review Cached_Faceted_Questions
begin

definition cause_root_prepare where
  "cause_root_prepare subject = (subject,prepare_faceted_observations cause_root_methods
    cause_root_facets (cause_root_observation subject))"

definition cause_root_prepared_question where
  "cause_root_prepared_question prepared methods facets = (case prepared of (subject,cache) \<Rightarrow>
    prepared_faceted_question (cause_root_observation subject) cache methods facets)"

lemma cause_root_prepared_question_exact:
  "cause_root_prepared_question (cause_root_prepare subject) methods facets =
    cause_root_question subject methods facets"
  by (simp only: cause_root_prepared_question_def cause_root_prepare_def prod.case
    prepared_faceted_question_exact cause_root_question_def)

definition cause_root_prepared_choice where
  "cause_root_prepared_choice prepared methods facets report =
    keyed_admitted_choice (first_occurrence_key methods) methods
    (cause_root_prepared_question prepared methods facets) report"

theorem cause_root_prepared_choice_exact:
  "cause_root_prepared_choice (cause_root_prepare subject) methods facets report =
    cause_root_choice subject methods facets report"
  by (simp only: cause_root_prepared_choice_def cause_root_prepared_question_exact cause_root_choice_def)

definition cause_root_prepared_profile where
  "cause_root_prepared_profile prepared method = (case prepared of (subject,cache) \<Rightarrow>
    map (prepared_faceted_observation (cause_root_observation subject) cache method) cause_root_facets)"

lemma cause_root_prepared_profile_exact:
  "cause_root_prepared_profile (cause_root_prepare subject) method =
    map (cause_root_observation subject method) cause_root_facets"
  by (simp only: cause_root_prepared_profile_def cause_root_prepare_def prod.case
    prepared_faceted_observation_exact[abs_def])

definition cause_root_prepared_family where
  "cause_root_prepared_family subjects = Parallel.map cause_root_prepare subjects"

lemma cause_root_prepared_family_exact:
  "cause_root_prepared_family subjects = map cause_root_prepare subjects"
  by (simp only: cause_root_prepared_family_def Parallel.map_def)

export_code cause_root_subject cause_root_prepared_family cause_root_prepared_question
  cause_root_prepared_choice cause_root_prepared_profile cause_root_methods cause_root_facets
  cause_root_review_scopes cause_root_observation_controls
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Prepared_Cause_Review file_prefix "native_control_prepared_cause_review"

text \<open>The complete actual subject fixes each internally computed cache.
  Exact equations preserve the original question, choice and every profile;
  the parallel family retains order and multiplicity. No source, certificate,
  premise truth, replay or policy authority follows from this preparation.\<close>

end
