theory Factor_Keyed_Table_Comparison
  imports Factor_Keyed_Table_Clauses Keyed_Fibre_Identity
begin

declare [[goals_limit=100]]

section \<open>The native row test keeps the entire returned fibre\<close>

lemma keyed_table_row_exact:
  "(351,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (\<exists>b k v. t=Pair_Term b (Pair_Term k v) \<and>
      (28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system)"
proof -
  have valuation: "(351,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
        term_formed (h 2) \<and> t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
        (28,key_fibre_argument (h 1) (h 0) (data_list_term [h 2]))\<in>positive_meaning key_fibre_system)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: keyed_table_comparison_clause keyed_table_clause_family_def keyed_table_row_schema_def
        schema_variables_def keyed_table_comparison_call keyed_table_fibre_meaning)
  have formed: "term_formed b" "term_formed k" "term_formed v"
    if "(28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system" for b k v
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by auto
  show ?thesis
  proof
    assume "(351,t)\<in>positive_meaning keyed_table_comparison_system"
    then show "\<exists>b k v. t=Pair_Term b (Pair_Term k v) \<and>
      (28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
      by (simp only: valuation) blast
  next
    assume "\<exists>b k v. t=Pair_Term b (Pair_Term k v) \<and>
      (28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
    then obtain b k v where parts: "t=Pair_Term b (Pair_Term k v)"
      "(28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system" by blast
    show "(351,t)\<in>positive_meaning keyed_table_comparison_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then b else if i=1 then k else v"])
        (use parts formed[OF parts(2)] in auto)
  qed
qed

corollary keyed_table_row_at_arguments:
  "(351,Pair_Term b (Pair_Term k v))\<in>positive_meaning keyed_table_comparison_system
    \<longleftrightarrow> (28,key_fibre_argument k b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
  by (auto simp only: keyed_table_row_exact factor_term.inject)

corollary keyed_table_row_at:
  "(351,Pair_Term (pair_list_term ys) (Pair_Term k v))\<in>positive_meaning keyed_table_comparison_system
    \<longleftrightarrow> term_formed k \<and> self_contained_term k \<and> formed_key_rows ys \<and> key_values k ys=[v]"
  by (simp only: keyed_table_row_at_arguments key_fibre_lists data_list_term_injective eq_commute)

lemma keyed_table_comparison_equation:
  "(353,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and>
      (352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system \<and>
      (352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system)"
proof -
  have valuation: "(353,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
        t=Pair_Term (h 0) (h 1) \<and>
        (352,Pair_Term (h 1) (h 0))\<in>positive_meaning keyed_table_comparison_system \<and>
        (352,Pair_Term (h 0) (h 1))\<in>positive_meaning keyed_table_comparison_system)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: keyed_table_comparison_clause keyed_table_clause_family_def related_set_schema_def
        schema_variables_def keyed_table_comparison_call)
  have formed: "term_formed p \<and> term_formed q"
    if "(352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system" for p q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by auto
  show ?thesis
  proof
    assume "(353,t)\<in>positive_meaning keyed_table_comparison_system"
    then show "\<exists>p q. t=Pair_Term p q \<and>
      (352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system \<and>
      (352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system"
      by (simp only: valuation) blast
  next
    assume "\<exists>p q. t=Pair_Term p q \<and>
      (352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system \<and>
      (352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system"
    then obtain p q where parts: "t=Pair_Term p q"
      "(352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system"
      "(352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system" by blast
    show "(353,t)\<in>positive_meaning keyed_table_comparison_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else q"])
        (use parts formed[OF parts(2)] in auto)
  qed
qed

corollary keyed_table_comparison_at_arguments:
  "(353,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system \<and>
    (352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system"
  by (auto simp only: keyed_table_comparison_equation factor_term.inject)

theorem keyed_table_comparison_lists:
  "(353,Pair_Term (pair_list_term xs) (pair_list_term ys))\<in>positive_meaning keyed_table_comparison_system
    \<longleftrightarrow> formed_key_rows xs \<and> formed_key_rows ys \<and>
      distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
proof -
  have raw: "(353,Pair_Term (pair_list_term xs) (pair_list_term ys))\<in>positive_meaning keyed_table_comparison_system
      \<longleftrightarrow> term_formed (pair_list_term xs) \<and> term_formed (pair_list_term ys) \<and>
        (\<forall>(k,v)\<in>set xs. term_formed k \<and> self_contained_term k \<and> formed_key_rows ys \<and> key_values k ys=[v]) \<and>
        (\<forall>(k,v)\<in>set ys. term_formed k \<and> self_contained_term k \<and> formed_key_rows xs \<and> key_values k xs=[v])"
    apply (simp only: keyed_table_comparison_at_arguments)
    apply (simp only: keyed_table_rows.lists pair_list_term_formed_iff)
    apply (auto simp: keyed_table_row_at)
    done
  have formed: "(term_formed (pair_list_term xs) \<and> term_formed (pair_list_term ys) \<and>
        (\<forall>(k,v)\<in>set xs. term_formed k \<and> self_contained_term k \<and> formed_key_rows ys \<and> key_values k ys=[v]) \<and>
        (\<forall>(k,v)\<in>set ys. term_formed k \<and> self_contained_term k \<and> formed_key_rows xs \<and> key_values k xs=[v]))
      \<longleftrightarrow> formed_key_rows xs \<and> formed_key_rows ys \<and>
        (\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k ys=[v]) \<and>
        (\<forall>k v. (k,v)\<in>set ys \<longrightarrow> key_values k xs=[v])"
    by (cases xs; cases ys) (auto simp: pair_list_term_formed_iff octets_formed_def)
  show ?thesis by (simp only: raw formed mutual_key_fibres)
qed

lemma keyed_table_comparison_shapes:
  assumes "(353,t)\<in>positive_meaning keyed_table_comparison_system"
  shows "\<exists>xs ys. t=Pair_Term (pair_list_term xs) (pair_list_term ys)"
proof -
  obtain p q where parts: "t=Pair_Term p q"
    "(352,Pair_Term q p)\<in>positive_meaning keyed_table_comparison_system"
    "(352,Pair_Term p q)\<in>positive_meaning keyed_table_comparison_system"
    using assms by (simp only: keyed_table_comparison_equation) blast
  obtain ps qs where lists: "p=data_list_term ps" "q=data_list_term qs"
    "\<forall>x\<in>set ps. (351,Pair_Term q x)\<in>positive_meaning keyed_table_comparison_system"
    "\<forall>x\<in>set qs. (351,Pair_Term p x)\<in>positive_meaning keyed_table_comparison_system"
    using parts(2,3) by (auto simp only: keyed_table_rows.exact factor_term.inject)
  have row: "\<exists>k v. x=Pair_Term k v"
    if "(351,Pair_Term b x)\<in>positive_meaning keyed_table_comparison_system" for b x
    using that by (auto simp only: keyed_table_row_exact factor_term.inject)
  have first_range: "\<forall>x\<in>set ps. \<exists>kv. x=(\<lambda>(k,v). Pair_Term k v) kv"
    using lists(3) row by auto
  have second_range: "\<forall>x\<in>set qs. \<exists>kv. x=(\<lambda>(k,v). Pair_Term k v) kv"
    using lists(4) row by auto
  obtain xs where first: "ps=map (\<lambda>(k,v). Pair_Term k v) xs"
    using first_range by (auto simp only: list_range_witnesses)
  obtain ys where second: "qs=map (\<lambda>(k,v). Pair_Term k v) ys"
    using second_range by (auto simp only: list_range_witnesses)
  show ?thesis by (rule exI[of _ xs], rule exI[of _ ys])
    (use parts(1) lists(1,2) first second in simp)
qed

theorem keyed_table_comparison_exact:
  "(353,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (pair_list_term xs) (pair_list_term ys) \<and>
      formed_key_rows xs \<and> formed_key_rows ys \<and>
      distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys)"
  using keyed_table_comparison_shapes keyed_table_comparison_lists by blast

theorem keyed_table_self_admission:
  "(353,Pair_Term t t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (21,t)\<in>positive_meaning keyed_list_system"
proof
  assume checked: "(353,Pair_Term t t)\<in>positive_meaning keyed_table_comparison_system"
  obtain xs ys where shape: "t=pair_list_term xs" "t=pair_list_term ys"
    using keyed_table_comparison_shapes[OF checked] by (auto simp only: factor_term.inject)
  have rows: "formed_key_rows xs" "distinct (map fst xs)"
    using checked by (simp only: shape(1) keyed_table_comparison_lists; blast)+
  show "(21,t)\<in>positive_meaning keyed_list_system"
    using keyed_list_complete[OF rows] by (simp only: shape(1))
next
  assume admitted: "(21,t)\<in>positive_meaning keyed_list_system"
  obtain xs where fields: "t=pair_list_term xs" "formed_key_rows xs" "distinct (map fst xs)"
    using keyed_list_sound[OF admitted] by blast
  show "(353,Pair_Term t t)\<in>positive_meaning keyed_table_comparison_system"
    by (simp only: fields(1) keyed_table_comparison_lists; use fields(2,3) in simp)
qed

text \<open>
  This is equality of complete functional tables with independently ordered
  row presentations. Both tables must contain each key once. Even two equal
  repeated rows fail that boundary; they are not silently identified. Values
  may be any formed terms, including literal targets. Keys retain their
  existing self-contained data contract. No equality of arbitrary alternative
  presentations of a value is asserted: that value needs its own contract.
\<close>

end
