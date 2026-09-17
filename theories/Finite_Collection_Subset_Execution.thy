theory Finite_Collection_Subset_Execution
  imports Main
begin

lemma list_superset_shared_code [code]:
  "List.superset ys xs=(xs=ys \<or> list_all (\<lambda>x. x\<in>set ys) xs)"
  by (auto simp: List.superset_iff list_all_iff)

text \<open>Equal complete list presentations establish subset by one ordered
  comparison. Every other presentation executes the original complete membership
  traversal. Repetition and order do not acquire set meaning; neither list length
  nor a supplied identity flag decides the result. The equation holds for all
  element values and both empty and nonempty lists.\<close>

end
