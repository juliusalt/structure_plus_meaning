theory Finite_Ordered_Relation_Checks
  imports RRA_Finite_Artifacts Finite_Sorted_Set_Execution "HOL-Library.Sublist"
    "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

definition ordered_fset_subset :: "'a::linorder fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "ordered_fset_subset A B=subseq (sorted_list_of_fset A) (sorted_list_of_fset B)"

theorem ordered_fset_subset_exact:
  "ordered_fset_subset A B \<longleftrightarrow> A |\<subseteq>| B"
proof
  assume "ordered_fset_subset A B"
  then have "set (sorted_list_of_fset A) \<subseteq> set (sorted_list_of_fset B)"
    unfolding ordered_fset_subset_def by (auto dest: list_emb_set)
  then show "A |\<subseteq>| B" by (simp add: less_eq_fset.rep_eq)
next
  assume "A |\<subseteq>| B"
  then have subset: "set (sorted_list_of_fset A) \<subseteq> set (sorted_list_of_fset B)"
    by (simp add: less_eq_fset.rep_eq)
  show "ordered_fset_subset A B"
    unfolding ordered_fset_subset_def
    by (rule sorted_subset_imp_subseq[OF subset])
      (simp_all add: strict_sorted_iff sorted_list_of_fset.rep_eq)
qed

lemma sorted_duplicate_check:
  "remdups_adj (sort xs)=sort xs \<longleftrightarrow> distinct (xs::'a::linorder list)"
proof
  assume same: "remdups_adj (sort xs)=sort xs"
  have "distinct (remdups_adj (sort xs))" by (rule sorted_remdups_adj_distinct) simp
  then show "distinct xs" by (simp only: same distinct_sort)
next
  assume "distinct xs"
  then show "remdups_adj (sort xs)=sort xs" by (simp add: remdups_adj_distinct)
qed

lemma finite_relation_functional_first_injective:
  "finite_relation_functional R \<longleftrightarrow> inj_on fst (fset R)"
  by (auto simp: finite_relation_functional_def inj_on_def prod_eq_iff)

definition ordered_relation_functional ::
  "('a::linorder \<times> 'b::linorder) fset \<Rightarrow> bool" where
  "ordered_relation_functional R=(let keys=sort (map fst (sorted_list_of_fset R))
    in remdups_adj keys=keys)"

theorem ordered_relation_functional_exact:
  "ordered_relation_functional R=finite_relation_functional R"
  by (simp add: ordered_relation_functional_def Let_def sorted_duplicate_check
      distinct_map finite_relation_functional_first_injective)

text \<open>The original finite subset and functionality predicates are computed
  from their complete canonical lists. The subsequence scan is the existing
  proved list operation. Functionality checks duplicate keys after exact-pair
  deduplication; repeated equal rows and conflicting values remain distinct
  cases under the original relation. No supplied satisfaction table is used.\<close>

end
