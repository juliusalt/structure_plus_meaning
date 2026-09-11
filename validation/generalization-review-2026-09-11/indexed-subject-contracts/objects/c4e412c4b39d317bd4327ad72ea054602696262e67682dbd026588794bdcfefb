theory Factor_Table_Literal_Lookup
  imports Factor_Key_Fibres Factor_Table_Presentations
begin

section \<open>A complete functional table gives one actual value at a key\<close>

theorem key_fibre_at_literal_table:
  assumes table: "data_table_presents (\<lambda>k p. p=f k) (\<lambda>v q. q=g v) Q p"
    and injective: "inj f"
    and key: "term_formed (f k)" "self_contained_term (f k)"
    and boundary: "\<And>j v. (j,v)\<in>Q \<Longrightarrow>
      term_formed (f j) \<and> self_contained_term (f j) \<and> term_formed (g v)"
  shows "(28,key_fibre_argument (f k) p (data_list_term [q]))\<in>positive_meaning key_fibre_system
    \<longleftrightarrow> (\<exists>v. (k,v)\<in>Q \<and> q=g v)"
proof -
  obtain xs where source: "distinct xs" "set xs=Q" "single_valued Q"
    "p=data_list_term (map (\<lambda>z. Pair_Term (f (fst z)) (g (snd z))) xs)"
    using table by (simp only: data_table_literal_enumeration; blast)
  have unique: "distinct (map fst xs)"
    using source(1-3) by (simp only: distinct_keys_iff)
  have rows: "formed_key_rows (map (\<lambda>(j,v). (f j,g v)) xs)"
    using boundary source(2) by auto
  have collected: "(28,key_fibre_argument (f k) p (data_list_term [q]))\<in>positive_meaning key_fibre_system
      \<longleftrightarrow> data_list_term [q]=data_list_term (map g (key_values k xs))"
    using key_fibre_mapped_lists[where f=f and g=g and k=k and xs=xs and t="data_list_term [q]",
      OF injective key rows] by (simp only: source(4))
  have orientation: "([q]=map g (key_values k xs))=(map g (key_values k xs)=[q])" by (rule eq_commute)
  show ?thesis by (simp only: collected data_list_term_injective orientation
    key_values_mapped_singleton[where g=g and q=q and k=k, OF unique] source(2))
qed

corollary key_fibre_at_literal_entry:
  assumes table: "data_table_presents (\<lambda>k p. p=f k) (\<lambda>v q. q=g v) Q p"
    and injective: "inj f" and member: "(k,v)\<in>Q"
    and boundary: "\<And>j w. (j,w)\<in>Q \<Longrightarrow>
      term_formed (f j) \<and> self_contained_term (f j) \<and> term_formed (g w)"
  shows "(28,key_fibre_argument (f k) p (data_list_term [q]))\<in>positive_meaning key_fibre_system
    \<longleftrightarrow> q=g v"
proof -
  have key: "term_formed (f k)" "self_contained_term (f k)" using boundary[OF member] by blast+
  have functional: "single_valued Q" using table by (simp add: data_table_presents_def)
  show ?thesis using member functional
    by (simp only: key_fibre_at_literal_table[OF table injective key boundary])
      (auto simp: single_valued_def; blast)
qed

theorem singleton_fibre_does_not_admit_whole_table:
  "\<exists>p. (28,key_fibre_argument (Payload_Term []) p
      (data_list_term [Target_Term (Whole_Artifact empty_artifact)]))\<in>positive_meaning key_fibre_system \<and>
    \<not>(21,p)\<in>positive_meaning keyed_list_system"
proof -
  let ?xs="[(Payload_Term [],Target_Term (Whole_Artifact empty_artifact)),
    (Payload_Term [0],Payload_Term []),(Payload_Term [0],Payload_Term [])]"
  have fibre: "(28,key_fibre_argument (Payload_Term []) (pair_list_term ?xs)
      (data_list_term [Target_Term (Whole_Artifact empty_artifact)]))\<in>positive_meaning key_fibre_system"
    by (simp only: key_fibre_lists) (simp add: octets_formed_def)
  have rejected: "\<not>(21,pair_list_term ?xs)\<in>positive_meaning keyed_list_system"
    by (simp only: keyed_list_exact pair_list_term_injective) simp
  show ?thesis using fibre rejected by blast
qed

text \<open>
  The complete table fixes every key and literal value, and the existing
  collector returns precisely its singleton fibre. Values may be formed
  target-bearing terms. Only the keys require self-contained data. Neither
  this specialization nor the collector reorders or replaces a stored value.

  The explicit source premise includes functionality of the whole relation.
  A successful singleton fibre alone cannot supply that premise: duplicated
  unrelated keys remain a counterexample. For a value notion with several
  presentations, this literal result needs the separately proved semantic
  correspondence before it can represent every compatible output.
\<close>

end
