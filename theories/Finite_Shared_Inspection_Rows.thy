theory Finite_Shared_Inspection_Rows
  imports Finite_Assessment_Reports
begin

definition inspected_observation_rows where
  "inspected_observation_rows inspect fs c w=map (\<lambda>f. (f,c,w)) (filter inspect fs)"

declare assessed_subject_observations_def[code del]

lemma assessed_subject_observations_prepared_code [code]:
  "assessed_subject_observations cs fs ws assess inspect=concat (map (\<lambda>c.
    concat (map (\<lambda>w. inspected_observation_rows (inspect (assess c w)) fs c w) ws)) cs)"
  by (simp only: assessed_subject_observations_def inspected_observation_rows_def Let_def)

text \<open>The actual prepared inspection is supplied as a function argument
  before its facet traversal. The helper preserves the complete ordered rows
  for arbitrary index lists, including repeated indices and an empty facet
  list. Generated code must still be inspected and timed to establish the
  physical sharing achieved by this evaluation boundary.\<close>

end
