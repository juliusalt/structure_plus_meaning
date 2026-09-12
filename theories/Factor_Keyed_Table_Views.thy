theory Factor_Keyed_Table_Views
  imports Factor_Keyed_Table_Comparison Factor_Proof_Claim_Values
begin

section \<open>Injective row presentations preserve complete table comparison\<close>

theorem keyed_table_comparison_mapped_rows:
  assumes key: "inj f" and selected_value: "inj g"
  shows "(353,Pair_Term
      (pair_list_term (map (\<lambda>(k,v). (f k,g v)) xs))
      (pair_list_term (map (\<lambda>(k,v). (f k,g v)) ys)))\<in>positive_meaning keyed_table_comparison_system
    \<longleftrightarrow> formed_key_rows (map (\<lambda>(k,v). (f k,g v)) xs) \<and>
      formed_key_rows (map (\<lambda>(k,v). (f k,g v)) ys) \<and>
      distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
proof -
  have keys: "distinct (map fst (map (\<lambda>(k,v). (f k,g v)) zs)) \<longleftrightarrow> distinct (map fst zs)" for zs
  proof -
    have mapped: "map fst (map (\<lambda>(k,v). (f k,g v)) zs)=map f (map fst zs)"
      by (simp add: comp_def case_prod_unfold)
    have injective: "inj_on f (set (map fst zs))" by (rule inj_on_subset[OF key subset_UNIV])
    show ?thesis by (simp only: mapped distinct_map) (use injective in blast)
  qed
  have injective: "inj (\<lambda>(k,v). (f k,g v))"
    using key selected_value by (auto simp: inj_def)
  have rows: "set (map (\<lambda>(k,v). (f k,g v)) xs)=set (map (\<lambda>(k,v). (f k,g v)) ys)
      \<longleftrightarrow> set xs=set ys"
    by (simp only: set_map inj_image_eq_iff[OF injective])
  show ?thesis by (simp only: keyed_table_comparison_lists keys rows)
qed

corollary keyed_table_comparison_call_rows:
  "(353,Pair_Term (call_instance_rows_term xs) (call_instance_rows_term ys))
      \<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    term_formed (call_instance_rows_term xs) \<and> term_formed (call_instance_rows_term ys) \<and>
      distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
  using keyed_table_comparison_mapped_rows[OF payload_term_inj call_instance_pair_injective,
    where xs=xs and ys=ys]
  by (simp add: local_call_rows_encoding pair_list_term_formed_iff data_list_term_formed
    comp_def case_prod_unfold)

text \<open>
  This transports the existing comparator through actual injective key and
  value functions. The source lists still require one occurrence per key and
  formed complete values. No order restriction is imposed between the tables.
\<close>

end
