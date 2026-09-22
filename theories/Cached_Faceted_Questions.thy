theory Cached_Faceted_Questions
  imports Faceted_Native_Questions Finite_Evaluation_Caches
begin

definition prepare_faceted_observations where
  "prepare_faceted_observations subjects facets observe =
    finite_evaluation_cache (\<lambda>(s,f). observe s f) (List.product subjects facets)"

definition prepared_faceted_observation where
  "prepared_faceted_observation observe cache s f =
    finite_cached_evaluation (\<lambda>(s,f). observe s f) cache (s,f)"

lemma prepared_faceted_observation_exact:
  "prepared_faceted_observation observe (prepare_faceted_observations subjects facets observe) s f = observe s f"
  by (simp only: prepared_faceted_observation_def prepare_faceted_observations_def
    finite_cached_evaluation_exact prod.case)

definition prepared_faceted_question where
  "prepared_faceted_question observe cache subjects facets =
    faceted_native_question subjects facets (prepared_faceted_observation observe cache)"

theorem prepared_faceted_question_exact:
  "prepared_faceted_question observe (prepare_faceted_observations scope language observe) subjects facets =
    faceted_native_question subjects facets observe"
  by (simp only: prepared_faceted_question_def prepared_faceted_observation_exact[abs_def])

theorem prepared_faceted_choice_exact:
  "keyed_admitted_choice (first_occurrence_key subjects) subjects
    (prepared_faceted_question observe (prepare_faceted_observations scope language observe) subjects facets) report =
    keyed_admitted_choice (first_occurrence_key subjects) subjects (faceted_native_question subjects facets observe) report"
  by (simp only: prepared_faceted_question_exact)

text \<open>All cache rows are computed by the actual observation operation.
  The original complete question and admission are preserved for every report,
  including queries outside the prepared scope, empty scopes, changed order,
  repeated occurrences and omitted facets. A supplied table is not an instance
  of these theorems. Cache row count is not an elapsed-time bound.\<close>

end
