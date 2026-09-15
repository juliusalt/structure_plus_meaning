theory Parallel_Assessment_Execution
  imports "HOL-Library.Parallel" Prepared_Assessment_Functions Finite_Shared_Inspection_Rows
begin

declare context_assessment_table_def[code del]
declare prepared_context_assessment_table_def[code del]
declare assessed_subject_observations_prepared_code[code del]

lemma context_assessment_table_parallel_code [code]:
  "context_assessment_table cs ws context assess=Parallel.map (\<lambda>w.
    let C=context w in (w,C,map (\<lambda>c. (c,assess c C)) cs)) ws"
  by (simp only: context_assessment_table_def Parallel.map_def)

lemma prepared_context_assessment_table_parallel_code [code]:
  "prepared_context_assessment_table cs ws context prepare=Parallel.map (\<lambda>w.
    let C=context w; evaluate=prepare C
    in (w,C,map (\<lambda>c. (c,evaluate c)) cs)) ws"
  by (simp only: prepared_context_assessment_table_def Parallel.map_def)

lemma assessed_subject_observations_parallel_code [code]:
  "assessed_subject_observations cs fs ws assess inspect=concat (Parallel.map (\<lambda>c.
    concat (map (\<lambda>w. inspected_observation_rows (inspect (assess c w)) fs c w) ws)) cs)"
  by (simp only: assessed_subject_observations_prepared_code Parallel.map_def)

text \<open>Independent complete input contexts and independent candidate
  inspections use Isabelle's existing parallel-list implementation for its Eval
  target. The library's exact map equation retains order, repeated indices,
  every context, every result and every observation. Preparation within each
  input still precedes its dependent candidates. There is no parallel output
  mutation and no supplied satisfaction value.\<close>

end
