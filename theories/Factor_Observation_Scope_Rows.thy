theory Factor_Observation_Scope_Rows
  imports Factor_Observation_Scope_Clauses Factor_Observation_Presentations
begin

abbreviation observation_scope_context where
  "observation_scope_context C U F \<equiv> Pair_Term C (Pair_Term U F)"

abbreviation observation_scope_argument where
  "observation_scope_argument C U F T \<equiv> Pair_Term (observation_scope_context C U F) T"

lemma observation_scope_components:
  "(2,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  "(303,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    (303,t)\<in>positive_meaning observation_system"
  using observation_scope_base_meaning[of 2 t] observation_scope_base_meaning[of 303 t]
    observation_collection_meaning[of 2 t] observation_collection_meaning[of 303 t]
    observation_components(1)[of t] observation_base_roots
  by auto

lemma observation_scope_row_valuation:
  "(308,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      term_formed (h 2) \<and> term_formed (h 3) \<and> term_formed (h 4) \<and> term_formed (h 5) \<and>
      t=observation_scope_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (Pair_Term (h 4) (h 5))) \<and>
      (303,Pair_Term (h 0) (h 4))\<in>positive_meaning observation_scope_system \<and>
      (303,Pair_Term (h 1) (h 3))\<in>positive_meaning observation_scope_system \<and>
      (2,h 5)\<in>positive_meaning observation_scope_system)"
proof -
  have family: "((308,c),S)\<in>system_clauses observation_scope_system \<longleftrightarrow>
      (c,S)\<in>observation_scope_clause_family 308" for c S
    by (rule observation_scope_clause) simp
  show ?thesis by (subst ordinary_positive_entry_valuation)
    (auto simp: family observation_scope_clause_family_def observation_scope_row_schema_def
      schema_variables_def observation_scope_call)
qed

lemma observation_scope_row_exact:
  "(308,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    (\<exists>C U F f c w. data_elements C \<and> data_elements U \<and> term_formed F \<and>
      data_elements [f,c,w] \<and> f\<in>set U \<and> c\<in>set C \<and>
      t=observation_scope_argument (data_list_term C) (data_list_term U) F (observation_row_term (f,c,w)))"
proof
  assume "(308,t)\<in>positive_meaning observation_scope_system"
  then show "\<exists>C U F f c w. data_elements C \<and> data_elements U \<and> term_formed F \<and>
      data_elements [f,c,w] \<and> f\<in>set U \<and> c\<in>set C \<and>
      t=observation_scope_argument (data_list_term C) (data_list_term U) F (observation_row_term (f,c,w))"
    by (auto simp: observation_scope_row_valuation observation_scope_components observation_member_exact; blast)
next
  assume "\<exists>C U F f c w. data_elements C \<and> data_elements U \<and> term_formed F \<and>
      data_elements [f,c,w] \<and> f\<in>set U \<and> c\<in>set C \<and>
      t=observation_scope_argument (data_list_term C) (data_list_term U) F (observation_row_term (f,c,w))"
  then obtain C U F f c w where parts: "data_elements C" "data_elements U" "term_formed F"
    "data_elements [f,c,w]" "f\<in>set U" "c\<in>set C"
    "t=observation_scope_argument (data_list_term C) (data_list_term U) F (observation_row_term (f,c,w))"
    by (elim exE conjE) (rule that; assumption)
  let ?h="\<lambda>i::nat. if i=0 then data_list_term C else if i=1 then data_list_term U
    else if i=2 then F else if i=3 then f else if i=4 then c else w"
  show "(308,t)\<in>positive_meaning observation_scope_system"
    by (simp only: observation_scope_row_valuation; rule exI[of _ ?h])
      (use parts in \<open>auto simp: observation_scope_components observation_member_exact data_list_term_formed\<close>)
qed

interpretation observation_scope_rows: context_list_profile observation_scope_system 308 309
  by (rule context_list_profile.intro[OF observation_scope_system_formed])
    (auto simp: observation_scope_clause observation_scope_clause_family_def observation_scope_call)

lemma observation_scope_rows_encoded:
  "(309,observation_scope_argument (data_list_term C) (data_list_term U) (data_list_term F)
    (data_list_term (map observation_row_term rows)))\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    term_formed (data_list_term C) \<and> term_formed (data_list_term U) \<and> term_formed (data_list_term F) \<and>
    (\<forall>(f,c,w)\<in>set rows. data_elements C \<and> data_elements U \<and>
      data_elements [f,c,w] \<and> f\<in>set U \<and> c\<in>set C)"
  by (auto simp: observation_scope_rows.lists observation_scope_row_exact
    data_list_term_injective split: prod.splits)

section \<open>The complete input subject also owns its declared domains\<close>

definition observation_scope_subject_formed where
  "observation_scope_subject_formed C U F T \<longleftrightarrow>
    observation_facets_domain C \<and> observation_facets_domain U \<and> observation_facets_domain F \<and>
    observation_table_domain T \<and> finite_observation_table_formed C U T \<and> fset F\<subseteq>fset U"

lemma observation_scope_subject_lists:
  "observation_scope_subject_formed (fset_of_list C) (fset_of_list U) (fset_of_list F) (fset_of_list rows)
    \<longleftrightarrow> data_elements C \<and> data_elements U \<and> data_elements F \<and> observation_rows_data rows \<and>
      (\<forall>(f,c,w)\<in>set rows. f\<in>set U \<and> c\<in>set C) \<and> set F\<subseteq>set U"
  by (auto simp: observation_scope_subject_formed_def finite_observation_table_formed_def
    fset_of_list.rep_eq split: prod.splits)

text \<open>
  These entries check individual rows and then every row of the supplied table.
  The list combinator retains its original empty-list behavior. Admission of
  the declared scopes and the selection is a further operation: it cannot be
  recovered from element calls when the table is empty.
\<close>

end
