theory Finite_Assessment_Projections
  imports Finite_Assessment_Reports
begin

definition project_assessment_contexts where
  "project_assessment_contexts project table=map (\<lambda>(w,C,cells). (w,project C,cells)) table"

theorem context_assessment_table_projection:
  assumes original: "\<And>w. project (context w)=original_context w"
    and exact: "\<And>c w. assess c (context w)=original_assess c (original_context w)"
  shows "project_assessment_contexts project (context_assessment_table cs ws context assess)=
    context_assessment_table cs ws original_context original_assess"
  by (simp only: project_assessment_contexts_def context_assessment_table_def map_map comp_def
    Let_def case_prod_conv original exact)

text \<open>
  Prepared internal context may carry derived shared values. An explicit
  projection and exact assessment equation preserve the entire original
  public table, including its contexts, candidate rows, order and repetitions.
\<close>

end
