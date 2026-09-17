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
  "sorted_list_of_set (set xs)=(if ascending_listing xs then xs else remdups_adj (sort xs))"
  by (rule sorted_distinct_set_unique)
    (simp_all add: ascending_listing_exact sorted_remdups_adj_distinct)

declare sorted_list_of_multiset_mset[code del]

lemma sorted_list_of_multiset_listing_code [code]:
  "sorted_list_of_multiset (mset xs)=(if nondescending_listing xs then xs else sort xs)"
  by (simp add: nondescending_listing_exact sorted_sort_id)

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
