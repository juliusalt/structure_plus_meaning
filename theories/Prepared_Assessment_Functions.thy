theory Prepared_Assessment_Functions
  imports Finite_Assessment_Reports
begin

definition prepared_context_assessment_table where
  "prepared_context_assessment_table cs ws context prepare=map (\<lambda>w.
    let C=context w; evaluate=prepare C
    in (w,C,map (\<lambda>c. (c,evaluate c)) cs)) ws"

theorem prepared_context_assessment_table_exact:
  assumes prepare: "\<And>C c. prepare C c=assess c C"
  shows "prepared_context_assessment_table cs ws context prepare=
    context_assessment_table cs ws context assess"
  by (simp add: prepared_context_assessment_table_def context_assessment_table_def Let_def prepare)

text \<open>Preparation returns the actual assessment operation under a
  pointwise complete-result equation. Every context, ordered candidate cell
  and repeated index remains in the original table.\<close>

end
