theory Merge_Sort_Keys
  imports "HOL-Library.Sorting_Algorithms"
begin

section \<open>Sorting by a key is the library's merge sort at the key's comparator\<close>

text \<open>
  \<^const>\<open>sort_key\<close> is stated by insertion, so its code is quadratic in the list. The library's merge sort
  (\<^const>\<open>Sorting_Algorithms.mergesort\<close>, with its code equation \<open>mergesort_code\<close>) is its sort by a
  comparator; at the comparator of a key under the default order its insertion is \<^const>\<open>insort_key\<close>
  (@{text insort_key_comparator}), so \<^const>\<open>sort_key\<close> is that merge sort on every list
  (@{text sort_key_by_mergesort}), and a use states \<^const>\<open>sort_key\<close> and computes the merge sort. The
  library's short names that would shadow the list theory's (\<open>sort\<close>, \<open>sorted\<close>, \<open>insort\<close>) and the key
  comparator's name, which the development uses for variables, are hidden here.
\<close>

lemma insort_key_comparator: "Sorting_Algorithms.insort (key f default)=insort_key f"
proof (intro ext)
  fix y xs
  show "Sorting_Algorithms.insort (key f default) y xs=insort_key f y xs"
    by (induction xs) (auto simp: not_less)
qed

lemma sort_key_by_mergesort: "sort_key f xs=Sorting_Algorithms.mergesort (key f default) xs"
  by (simp add: sort_key_def Sorting_Algorithms.sort_def insort_key_comparator)

hide_const (open) Sorting_Algorithms.sort Sorting_Algorithms.sorted Sorting_Algorithms.insort Comparator.key

end
