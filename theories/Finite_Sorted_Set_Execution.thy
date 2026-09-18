theory Finite_Sorted_Set_Execution
  imports "HOL-Library.Multiset"
begin

lemma sorted_remdups_adj_distinct:
  "sorted (xs::'a::linorder list) \<Longrightarrow> distinct (remdups_adj xs)"
  by (induction xs rule: remdups_adj.induct)
    (auto simp: sorted_simps dest: order.antisym)

lemma sorted_list_of_set_after_sort:
  "sorted_list_of_set (set xs)=remdups_adj (sort xs)"
  by (rule sorted_distinct_set_unique)
    (simp_all add: sorted_remdups_adj_distinct)

section \<open>An unordered listing is sorted by merging\<close>

text \<open>
  Sorting a listing of a linearly ordered type has one result: every sorted permutation of
  the listing is it, because equal elements are identical. A merge sort computes that result
  with a number of comparisons proportional to the length times its logarithm, where the
  library's insertion sort compares every pair.
\<close>

fun merge_ascending :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_ascending [] ys=ys"
| "merge_ascending xs []=xs"
| "merge_ascending (x#xs) (y#ys)=(if y<x then y#merge_ascending (x#xs) ys
    else x#merge_ascending xs (y#ys))"

lemma merge_ascending_mset: "mset (merge_ascending xs ys)=mset xs+mset ys"
  by (induction xs ys rule: merge_ascending.induct) simp_all

lemma merge_ascending_set: "set (merge_ascending xs ys)=set xs\<union>set ys"
  by (induction xs ys rule: merge_ascending.induct) auto

lemma merge_ascending_sorted:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_ascending xs ys)"
  by (induction xs ys rule: merge_ascending.induct) (auto simp: merge_ascending_set)

function ascending_sort :: "'a::linorder list \<Rightarrow> 'a list" where
  "ascending_sort []=[]"
| "ascending_sort [x]=[x]"
| "ascending_sort (x#y#zs)=merge_ascending
    (ascending_sort (take ((length zs+2) div 2) (x#y#zs)))
    (ascending_sort (drop ((length zs+2) div 2) (x#y#zs)))"
  by pat_completeness auto
termination by (relation "measure length") auto

lemma ascending_sort_mset: "mset (ascending_sort xs)=mset xs"
proof (induction xs rule: ascending_sort.induct)
  case (3 x y zs)
  let ?n="(length zs+2) div 2"
  have "mset (take ?n (x#y#zs))+mset (drop ?n (x#y#zs))=mset (x#y#zs)"
    by (simp only: mset_append[symmetric] append_take_drop_id)
  then show ?case by (simp only: ascending_sort.simps(3) merge_ascending_mset 3)
qed simp_all

lemma ascending_sort_sorted: "sorted (ascending_sort xs)"
  by (induction xs rule: ascending_sort.induct) (simp_all add: merge_ascending_sorted)

theorem sort_ascending_sort: "sort xs=ascending_sort xs"
  by (rule properties_for_sort) (simp_all only: ascending_sort_mset ascending_sort_sorted)

section \<open>Canonical listings are recognized by one adjacent pass\<close>

fun ascending_listing :: "'a::linorder list \<Rightarrow> bool" where
  "ascending_listing (x#y#zs) \<longleftrightarrow> x<y \<and> ascending_listing (y#zs)"
| "ascending_listing xs \<longleftrightarrow> True"

fun nondescending_listing :: "'a::linorder list \<Rightarrow> bool" where
  "nondescending_listing (x#y#zs) \<longleftrightarrow> x\<le>y \<and> nondescending_listing (y#zs)"
| "nondescending_listing xs \<longleftrightarrow> True"

lemma ascending_listing_exact: "ascending_listing xs \<longleftrightarrow> sorted xs \<and> distinct xs"
proof -
  have "ascending_listing xs \<longleftrightarrow> sorted_wrt (<) xs"
    by (induction xs rule: ascending_listing.induct)
      (simp_all only: ascending_listing.simps sorted_wrt2[OF transp_on_less] sorted_wrt1 sorted_wrt.simps(1))
  then show ?thesis by (simp only: strict_sorted_iff)
qed

lemma nondescending_listing_exact: "nondescending_listing xs \<longleftrightarrow> sorted xs"
  by (induction xs rule: nondescending_listing.induct)
    (simp_all only: nondescending_listing.simps sorted2 sorted1 sorted0)

declare sorted_list_of_set_sort_remdups[code del]

lemma sorted_list_of_set_listing_code [code]:
  "sorted_list_of_set (set xs)=(if ascending_listing xs then xs else remdups_adj (ascending_sort xs))"
  by (simp only: sort_ascending_sort[symmetric])
    (rule sorted_distinct_set_unique, simp_all add: ascending_listing_exact sorted_remdups_adj_distinct)

declare sorted_list_of_multiset_mset[code del]

lemma sorted_list_of_multiset_listing_code [code]:
  "sorted_list_of_multiset (mset xs)=(if nondescending_listing xs then xs else ascending_sort xs)"
  by (simp add: nondescending_listing_exact sorted_sort_id sort_ascending_sort[symmetric])

text \<open>
  A finite set listed in strictly ascending order already is its canonical
  list, and a counted collection listed in nondescending order already is its
  canonical sorted list; one pass over adjacent members recognizes both. Any
  other listing is sorted as before: sorting puts equal values next to each
  other and removing adjacent repetitions returns the same complete canonical
  set list, including for empty lists and arbitrary repeated inputs. Every
  member, counted occurrence and original comparison is unchanged. Physical
  execution time is measured separately.
\<close>

end
