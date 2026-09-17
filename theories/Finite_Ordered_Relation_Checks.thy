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

lemma sorted_pair_keys:
  "sorted (xs::('a::linorder \<times> 'b::linorder) list) \<Longrightarrow> sorted (map fst xs)"
  unfolding sorted_wrt_map
  by (rule sorted_wrt_mono_rel[of _ "(\<le>)"]) (auto simp: less_eq_prod_def)

definition ordered_relation_functional ::
  "('a::linorder \<times> 'b::linorder) fset \<Rightarrow> bool" where
  "ordered_relation_functional R=ascending_listing (map fst (sorted_list_of_fset R))"

theorem ordered_relation_functional_exact:
  "ordered_relation_functional R=finite_relation_functional R"
proof -
  have "sorted (map fst (sorted_list_of_fset R))" by (rule sorted_pair_keys) (simp add: sorted_list_of_fset.rep_eq)
  then show ?thesis
    by (simp add: ordered_relation_functional_def ascending_listing_exact
      distinct_map finite_relation_functional_first_injective)
qed

text \<open>The original finite subset and functionality predicates are computed
  from their complete canonical lists. The subsequence scan is the existing
  proved list operation. The canonical list of exact pairs orders their keys,
  so functionality is one adjacent pass over those keys: repeated equal rows are
  already one pair, and conflicting values at one key remain adjacent equal keys
  under the original relation. No supplied satisfaction table is used.\<close>

end
