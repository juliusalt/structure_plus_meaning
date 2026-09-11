theory Factor_Data_Table_Operations
  imports Factor_Table_Presentations Factor_Collection_Selection
    List_Relation_Indexing Factor_Row_Values
begin

section \<open>Complete table rows retain their supplied key order and value forms\<close>

theorem data_table_indexed_rows:
  "data_table_presents K V Q t \<longleftrightarrow>
    (\<exists>ks row. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. factor_pair_presents K V (k,rel_value Q k) (row k)) \<and>
      t=data_list_term (map row ks))"
proof
  assume table: "data_table_presents K V Q t"
  obtain xs ts where source: "distinct xs" "set xs=Q" "single_valued Q"
    "list_all2 (factor_pair_presents K V) xs ts" "t=data_list_term ts"
    using table by (auto simp: data_table_presents_def data_collection_presents_def)
  let ?ks="map fst xs"
  have keys: "distinct ?ks" using source(1-3) by (simp add: distinct_keys_iff)
  have domain: "set ?ks=rel_dom Q" using source(2) by (auto simp: rel_dom_def intro: rev_image_eqI)
  have rows: "map (\<lambda>k. (k,rel_value Q k)) ?ks=xs"
    by (rule functional_list_at_keys[OF source(3,2)])
  have paired: "list_all2 (\<lambda>k p. factor_pair_presents K V (k,rel_value Q k) p) ?ks ts"
  proof -
    have "list_all2 (factor_pair_presents K V) (map (\<lambda>k. (k,rel_value Q k)) ?ks) ts"
      by (simp only: rows; rule source(4))
    then show ?thesis by (simp only: list_all2_map1)
  qed
  obtain row where actual: "ts=map row ?ks"
    "\<forall>k\<in>set ?ks. factor_pair_presents K V (k,rel_value Q k) (row k)"
    using paired by (simp only: list_all2_distinct_indexing[OF keys]; blast)
  show "\<exists>ks row. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. factor_pair_presents K V (k,rel_value Q k) (row k)) \<and>
      t=data_list_term (map row ks)"
    by (intro exI[of _ ?ks] exI[of _ row]) (use keys domain source(3,5) actual in blast)
next
  assume "\<exists>ks row. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. factor_pair_presents K V (k,rel_value Q k) (row k)) \<and>
      t=data_list_term (map row ks)"
  then obtain ks row where source: "distinct ks" "set ks=rel_dom Q" "single_valued Q"
    "\<forall>k\<in>set ks. factor_pair_presents K V (k,rel_value Q k) (row k)"
    "t=data_list_term (map row ks)" by blast
  let ?xs="map (\<lambda>k. (k,rel_value Q k)) ks"
  have distinct: "distinct ?xs" using source(1) by (simp add: distinct_map inj_on_def)
  have complete: "set ?xs=Q"
    using single_valued_graph[OF source(3)] source(2) by (auto simp: graph_map_def)
  have paired: "list_all2 (factor_pair_presents K V) ?xs (map row ks)"
    using source(4) by (simp add: list_all2_map1 list_all2_map2 list_all2_same)
  show "data_table_presents K V Q t"
    unfolding data_table_presents_def data_collection_presents_def
    by (rule conjI[OF source(3)], rule exI[of _ ?xs], rule exI[of _ "map row ks"])
      (use distinct complete paired source(5) in blast)
qed

theorem data_table_indexed_components:
  "data_table_presents K V Q t \<longleftrightarrow>
    (\<exists>ks key value. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. K k (key k) \<and> V (rel_value Q k) (value k)) \<and>
      t=pair_list_term (map (\<lambda>k. (key k,value k)) ks))"
proof
  assume table: "data_table_presents K V Q t"
  obtain ks row where source: "distinct ks" "set ks=rel_dom Q" "single_valued Q"
    "\<forall>k\<in>set ks. factor_pair_presents K V (k,rel_value Q k) (row k)"
    "t=data_list_term (map row ks)" using table by (simp only: data_table_indexed_rows; blast)
  have witnesses: "\<forall>k\<in>set ks. \<exists>z. K k (fst z) \<and> V (rel_value Q k) (snd z) \<and>
      row k=Pair_Term (fst z) (snd z)"
    using source(4) by (auto simp: factor_pair_presents_def)
  obtain f where chosen: "\<forall>k\<in>set ks. K k (fst (f k)) \<and> V (rel_value Q k) (snd (f k)) \<and>
      row k=Pair_Term (fst (f k)) (snd (f k))" using bchoice[OF witnesses] by blast
  have same: "map row ks=map (\<lambda>k. Pair_Term (fst (f k)) (snd (f k))) ks"
    by (rule map_cong) (use chosen in auto)
  show "\<exists>ks key stored. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. K k (key k) \<and> V (rel_value Q k) (stored k)) \<and>
      t=pair_list_term (map (\<lambda>k. (key k,stored k)) ks)"
    by (rule exI[of _ ks], rule exI[of _ "\<lambda>k. fst (f k)"], rule exI[of _ "\<lambda>k. snd (f k)"])
      (use source(1-3,5) chosen same in \<open>auto simp: comp_def case_prod_unfold\<close>)
next
  assume "\<exists>ks key stored. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. K k (key k) \<and> V (rel_value Q k) (stored k)) \<and>
      t=pair_list_term (map (\<lambda>k. (key k,stored k)) ks)"
  then obtain ks key stored where source: "distinct ks" "set ks=rel_dom Q" "single_valued Q"
    "\<forall>k\<in>set ks. K k (key k) \<and> V (rel_value Q k) (stored k)"
    "t=pair_list_term (map (\<lambda>k. (key k,stored k)) ks)" by blast
  show "data_table_presents K V Q t"
    by (simp only: data_table_indexed_rows; intro exI[of _ ks]
      exI[of _ "\<lambda>k. Pair_Term (key k) (stored k)"])
      (use source in \<open>auto simp: comp_def\<close>)
qed

corollary data_table_encoded_keys:
  "data_table_presents (\<lambda>k p. D k \<and> p=encode k) V Q t \<longleftrightarrow>
    (\<exists>ks value. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. D k \<and> V (rel_value Q k) (value k)) \<and>
      t=pair_list_term (map (\<lambda>k. (encode k,value k)) ks))"
proof
  assume table: "data_table_presents (\<lambda>k p. D k \<and> p=encode k) V Q t"
  obtain ks key stored where source: "distinct ks" "set ks=rel_dom Q" "single_valued Q"
    "\<forall>k\<in>set ks. (D k \<and> key k=encode k) \<and> V (rel_value Q k) (stored k)"
    "t=pair_list_term (map (\<lambda>k. (key k,stored k)) ks)"
    using table by (simp only: data_table_indexed_components; blast)
  have same: "map (\<lambda>k. (key k,stored k)) ks=map (\<lambda>k. (encode k,stored k)) ks"
    by (rule map_cong) (use source(4) in auto)
  show "\<exists>ks stored. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. D k \<and> V (rel_value Q k) (stored k)) \<and>
      t=pair_list_term (map (\<lambda>k. (encode k,stored k)) ks)"
    by (intro exI[of _ ks] exI[of _ stored]) (use source same in \<open>auto simp: same\<close>)
next
  assume "\<exists>ks stored. distinct ks \<and> set ks=rel_dom Q \<and> single_valued Q \<and>
      (\<forall>k\<in>set ks. D k \<and> V (rel_value Q k) (stored k)) \<and>
      t=pair_list_term (map (\<lambda>k. (encode k,stored k)) ks)"
  then obtain ks stored where source: "distinct ks" "set ks=rel_dom Q" "single_valued Q"
    "\<forall>k\<in>set ks. D k \<and> V (rel_value Q k) (stored k)"
    "t=pair_list_term (map (\<lambda>k. (encode k,stored k)) ks)" by blast
  show "data_table_presents (\<lambda>k p. D k \<and> p=encode k) V Q t"
    by (simp only: data_table_indexed_components; rule exI[of _ ks], rule exI[of _ encode], rule exI[of _ stored])
      (use source in simp)
qed

section \<open>The existing projections return the actual rows' components\<close>

lemma indexed_row_projections:
  assumes formed: "\<And>k. k\<in>set ks \<Longrightarrow> term_formed (key k) \<and> term_formed (value k)"
  shows "(51,Pair_Term (pair_list_term (map (\<lambda>k. (key k,value k)) ks)) p)
      \<in>positive_meaning row_keys_system \<longleftrightarrow> p=data_list_term (map key ks)"
    and "(59,Pair_Term (pair_list_term (map (\<lambda>k. (key k,value k)) ks)) p)
      \<in>positive_meaning row_values_system \<longleftrightarrow> p=data_list_term (map value ks)"
  by (simp_all only: row_keys_at_rows row_values_at_rows)
    (use formed in \<open>auto simp: data_list_term_formed comp_def\<close>)

text \<open>
  These equivalences decompose the table term actually supplied. They retain
  its complete semantic key order and each stored key and value presentation.
  Relational value classes may have many forms, and equal values at distinct
  keys remain separate rows. Function values outside the listed domain are
  temporary proof choices, not additional parts of the table subject.

  The native row projections preserve this actual order and every occurrence.
  Their result contains the stored component forms. Obtaining every other
  form of a semantic value requires the separately established comparison
  transport; a literal projection alone does not supply that contract.
\<close>

end
