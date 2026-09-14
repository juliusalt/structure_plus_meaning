theory Exact_Cache_Readings
  imports Main
begin

definition exact_cache_read where
  "exact_cache_read evaluate lookup x=(case lookup x of None \<Rightarrow> evaluate x | Some y \<Rightarrow> y)"

theorem exact_cache_read_correct:
  assumes exact: "\<And>y. lookup x=Some y \<Longrightarrow> y=evaluate x"
  shows "exact_cache_read evaluate lookup x=evaluate x"
  using exact by (cases "lookup x") (auto simp: exact_cache_read_def)

end
