theory Optional_Success_Reuse
  imports Optional_Checked_Results
begin

definition optional_success_reuse where
  "optional_success_reuse result fallback=(case result of None \<Rightarrow> fallback () | Some value \<Rightarrow> Some value)"

theorem optional_success_reuse_exact:
  assumes success: "\<And>value. result=Some value \<Longrightarrow> fallback ()=Some value"
  shows "optional_success_reuse result fallback=fallback ()"
  using success by (cases result) (auto simp: optional_success_reuse_def)

lemma mapped_checked_success_unfiltered:
  assumes result: "map_option project (optional_checked_result check extract input)=Some following"
  shows "map_option (project \<circ> extract) input=Some following"
  using result by (cases input) (auto simp: optional_checked_result_def split: if_splits)

text \<open>A successful checked result may replace an unchecked computation
  only under equality of that complete successful result. Every unsuccessful
  checked result executes the actual fallback. A function argument defers that
  computation until this branch, while the universal equation preserves it.\<close>

end
