theory Parallel_Presented_Investigations
  imports "HOL-Library.Parallel" Finite_Presented_Assessments
begin

section \<open>Rows of a presented assessment table are presented in parallel\<close>

declare finite_assessment_table_value_def[code del]

lemma finite_assessment_table_value_parallel_code [code]:
  "finite_assessment_table_value fc fa table=finite_data_list (Parallel.map
    (finite_pair_presentation finite_natural_data (finite_pair_presentation fc (finite_indexed_rows_value fa))) table)"
  by (simp only: finite_assessment_table_value_def finite_indexed_rows_value_def finite_sequence_presentation_def
    Parallel.map_def)

declare assessment_truth_rows_def[code del]

lemma assessment_truth_rows_parallel_code [code]:
  "assessment_truth_rows inspect fs table=Parallel.map (\<lambda>(w,C,cells).
    (w,map (\<lambda>(m,A). (m,map (\<lambda>f. (f,inspect A f)) fs)) cells)) table"
  by (simp only: assessment_truth_rows_def Parallel.map_def)

text \<open>Each input context of an assessment table is presented with all of its
  candidate assessments independently of every other context. Isabelle's exact
  parallel map equation keeps the table order, repeated indices and every
  presented context and assessment; the presented term is unchanged. The actual
  inspection truth rows of each context are likewise independent of the others.\<close>

end
