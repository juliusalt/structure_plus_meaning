theory Context_Source_Projections
  imports Finite_Assessment_Reports
begin

definition context_source_rows where
  "context_source_rows project table=map (\<lambda>(w,C,cells). (w,project w C)) table"

theorem context_source_rows_exact:
  assumes each: "\<And>w. w\<in>set ws \<Longrightarrow> project w (context w)=source w"
  shows "context_source_rows project (context_assessment_table cs ws context assess)=
    map (\<lambda>w. (w,source w)) ws"
  using each by (auto simp: context_source_rows_def context_assessment_table_def
    Let_def map_map intro!: map_cong)

text \<open>The complete source projection is read from the actual constructed
  context. Its equation requires the actual context operation at every requested
  index. Ordered and repeated indices are retained; an arbitrary supplied table
  does not establish the source equation.\<close>

end
