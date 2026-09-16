theory Constructed_Assessment_Functions
  imports Prepared_Assessment_Functions "HOL-Library.Parallel"
begin

lemma constructed_option_evidence:
  assumes valid: "\<And>x. result=Some x \<Longrightarrow> evidence x"
  shows "(case result of None \<Rightarrow> False | Some x \<Rightarrow> evidence x)=(result\<noteq>None)"
  using valid by (cases result) auto

definition constructed_context_assessment_table where
  "constructed_context_assessment_table cs ws prepare=Parallel.map (\<lambda>w.
    let (C,assess)=prepare w in (w,C,map (\<lambda>c. (c,assess c)) cs)) ws"

theorem constructed_context_assessment_table_exact:
  assumes context_eq: "\<And>w. fst (prepare w)=context w"
    and assessment_eq: "\<And>w c. snd (prepare w) c=assess c (context w)"
  shows "constructed_context_assessment_table cs ws prepare=
    context_assessment_table cs ws context assess"
  by (simp add: constructed_context_assessment_table_def context_assessment_table_def
    Parallel.map_def case_prod_unfold Let_def context_eq assessment_eq)

text \<open>Construction may share one actual computation between its retained
  context and its prepared assessment function. Both projections have complete
  original-result equations. Ordered contexts, candidates and repeated positions
  remain unchanged. No supplied context or callback receives an assertion of
  correctness merely from being present in this representation.\<close>

end
