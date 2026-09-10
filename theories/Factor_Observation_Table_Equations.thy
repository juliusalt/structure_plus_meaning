theory Factor_Observation_Table_Equations
  imports Factor_Observation_Table_Clauses Finite_Observation_Tables
begin

lemma observation_table_components:
  "(301,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> (301,t)\<in>positive_meaning observation_system"
  "(306,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> (306,t)\<in>positive_meaning observation_system"
  "(311,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> (311,t)\<in>positive_meaning observation_scope_system"
  "(317,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> (317,t)\<in>positive_meaning keyed_set_system"
  "(324,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> (324,t)\<in>positive_meaning data_product_system"
  using observation_table_base_meaning[of 301 t] observation_table_base_meaning[of 306 t]
    observation_table_base_meaning[of 311 t] observation_table_base_meaning[of 317 t] observation_table_base_meaning[of 324 t]
    observation_table_components_observation_meaning[of 301 t] observation_table_components_observation_meaning[of 306 t]
    observation_table_components_scope_meaning[of t] observation_table_components_keyed_meaning[of t]
    observation_table_components_product_meaning[of t] by auto

interpretation observation_table_profile_key: keyed_calculation_profile observation_table_system 326 301
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_profiles: related_list_profile observation_table_system 326 327
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_profile_admitted: admitted_context_profile observation_table_system 329 311 328
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_profile_comparison: result_comparison_profile observation_table_system 330 329 317
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_loss_key: keyed_calculation_profile observation_table_system 331 306
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_losses: related_list_profile observation_table_system 331 332
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_loss_admitted: admitted_context_profile observation_table_system 334 311 333
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

interpretation observation_table_loss_comparison: result_comparison_profile observation_table_system 335 334 317
  by (unfold_locales) (auto simp: observation_table_clause observation_table_clause_family_def observation_table_call)

section \<open>The complete query is passed unchanged to admission and calculation\<close>

lemma observation_profile_table_valuation:
  "(328,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      term_formed (h 3) \<and> term_formed (h 4) \<and>
      t=Pair_Term (observation_scope_argument (h 0) (h 1) (h 2) (h 3)) (h 4) \<and>
      (327,context_relation_argument (Pair_Term (h 2) (h 3)) (h 0) (h 4))\<in>positive_meaning observation_table_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: observation_table_clause observation_table_clause_family_def observation_profile_table_schema_def
      schema_variables_def observation_table_call)

lemma observation_profile_table_raw_exact:
  "(328,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    (\<exists>C U F T q. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (327,context_relation_argument (Pair_Term F T) C q)\<in>positive_meaning observation_table_system)"
proof
  assume "(328,t)\<in>positive_meaning observation_table_system"
  then show "\<exists>C U F T q. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (327,context_relation_argument (Pair_Term F T) C q)\<in>positive_meaning observation_table_system"
    by (simp only: observation_profile_table_valuation) blast
next
  assume "\<exists>C U F T q. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (327,context_relation_argument (Pair_Term F T) C q)\<in>positive_meaning observation_table_system"
  then obtain C U F T q where parts: "t=Pair_Term (observation_scope_argument C U F T) q" "term_formed U"
    "(327,context_relation_argument (Pair_Term F T) C q)\<in>positive_meaning observation_table_system" by blast
  have terms: "term_formed C" "term_formed F" "term_formed T" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then C else if i=1 then U else if i=2 then F else if i=3 then T else q"
  show "(328,t)\<in>positive_meaning observation_table_system"
    by (simp only: observation_profile_table_valuation; rule exI[of _ ?h]) (use parts terms in auto)
qed

lemma observation_profile_table_raw:
  "(328,Pair_Term (observation_scope_argument C U F T) q)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    term_formed U \<and> (327,context_relation_argument (Pair_Term F T) C q)\<in>positive_meaning observation_table_system"
  by (auto simp only: observation_profile_table_raw_exact factor_term.inject; blast)

lemma observation_loss_table_valuation:
  "(333,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      term_formed (h 3) \<and> term_formed (h 4) \<and> term_formed (h 5) \<and>
      t=Pair_Term (observation_scope_argument (h 0) (h 1) (h 2) (h 3)) (h 4) \<and>
      (324,context_relation_argument (h 0) (h 0) (h 5))\<in>positive_meaning observation_table_system \<and>
      (332,context_relation_argument (Pair_Term (h 2) (h 3)) (h 5) (h 4))\<in>positive_meaning observation_table_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: observation_table_clause observation_table_clause_family_def observation_loss_table_schema_def
      schema_variables_def observation_table_call)

lemma observation_loss_table_raw_exact:
  "(333,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    (\<exists>C U F T q keys. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (324,context_relation_argument C C keys)\<in>positive_meaning observation_table_system \<and>
      (332,context_relation_argument (Pair_Term F T) keys q)\<in>positive_meaning observation_table_system)"
proof
  assume "(333,t)\<in>positive_meaning observation_table_system"
  then show "\<exists>C U F T q keys. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (324,context_relation_argument C C keys)\<in>positive_meaning observation_table_system \<and>
      (332,context_relation_argument (Pair_Term F T) keys q)\<in>positive_meaning observation_table_system"
    by (simp only: observation_loss_table_valuation) blast
next
  assume "\<exists>C U F T q keys. t=Pair_Term (observation_scope_argument C U F T) q \<and> term_formed U \<and>
      (324,context_relation_argument C C keys)\<in>positive_meaning observation_table_system \<and>
      (332,context_relation_argument (Pair_Term F T) keys q)\<in>positive_meaning observation_table_system"
  then obtain C U F T q keys where parts: "t=Pair_Term (observation_scope_argument C U F T) q" "term_formed U"
    "(324,context_relation_argument C C keys)\<in>positive_meaning observation_table_system"
    "(332,context_relation_argument (Pair_Term F T) keys q)\<in>positive_meaning observation_table_system" by blast
  have terms: "term_formed C" "term_formed F" "term_formed T" "term_formed q" "term_formed keys"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then C else if i=1 then U else if i=2 then F else if i=3 then T
    else if i=4 then q else keys"
  show "(333,t)\<in>positive_meaning observation_table_system"
    by (simp only: observation_loss_table_valuation; rule exI[of _ ?h]) (use parts terms in auto)
qed

lemma observation_loss_table_raw:
  "(333,Pair_Term (observation_scope_argument C U F T) q)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    term_formed U \<and> (\<exists>keys. (324,context_relation_argument C C keys)\<in>positive_meaning observation_table_system \<and>
      (332,context_relation_argument (Pair_Term F T) keys q)\<in>positive_meaning observation_table_system)"
  by (auto simp only: observation_loss_table_raw_exact factor_term.inject; blast)

section \<open>Owned calculation and mapping contracts return the ordered row witnesses\<close>

abbreviation observation_profile_table_row where
  "observation_profile_table_row fs rows c \<equiv>
    Pair_Term c (data_list_term (map observation_value_term (observation_profile_list fs rows c)))"

abbreviation observation_loss_table_row where
  "observation_loss_table_row fs rows z \<equiv> Pair_Term (observation_value_term z)
    (data_list_term (map observation_value_term (observation_losses_list fs rows (fst z) (snd z))))"

abbreviation observation_profile_table_term where
  "observation_profile_table_term cs fs rows \<equiv> data_list_term (map (observation_profile_table_row fs rows) cs)"

abbreviation observation_loss_table_term where
  "observation_loss_table_term cs fs rows \<equiv>
    data_list_term (map (observation_loss_table_row fs rows) (List.product cs cs))"

lemma observation_table_profile_key_lists:
  "(326,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) c q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow>
    data_elements fs \<and> data_term_boundary c \<and> observation_rows_data rows \<and> q=observation_profile_table_row fs rows c"
  by (simp only: observation_table_profile_key.at_key observation_table_components observation_encoded_profile) auto

lemma observation_table_loss_key_lists:
  "(331,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) (Pair_Term c d) q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow>
    data_elements fs \<and> data_elements [c,d] \<and> observation_rows_data rows \<and> q=observation_loss_table_row fs rows (c,d)"
  by (simp only: observation_table_loss_key.at_key observation_table_components observation_encoded_losses) auto

lemma observation_table_profile_map:
  assumes facets: "data_elements fs" and rows: "observation_rows_data rows"
  shows "(327,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) p q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow>
    (\<exists>cs. data_elements cs \<and> p=data_list_term cs \<and> q=observation_profile_table_term cs fs rows)"
proof -
  have formed: "term_formed (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows)))"
    using facets rows by (auto simp: data_list_term_formed split: prod.splits)
  have element: "observation_table_profiles.related
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) c q \<longleftrightarrow>
      data_term_boundary c \<and> q=observation_profile_table_row fs rows c" for c q
    using facets rows by (simp only: observation_table_profile_key_lists; blast)
  show ?thesis by (rule observation_table_profiles.partial_function_exact[
    where D=data_term_boundary and f="observation_profile_table_row fs rows", OF formed element])
qed

lemma observation_table_profile_map_lists:
  assumes "data_elements fs" "observation_rows_data rows"
  shows "(327,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) (data_list_term cs) q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow>
    data_elements cs \<and> q=observation_profile_table_term cs fs rows"
  by (simp only: observation_table_profile_map[OF assms] data_list_term_injective; auto)

lemma observation_table_loss_map_lists:
  assumes facets: "data_elements fs" and rows: "observation_rows_data rows"
    and keys: "\<forall>(c,d)\<in>set pairs. data_elements [c,d]"
  shows "(332,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows)))
      (data_list_term (map observation_value_term pairs)) q)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    q=data_list_term (map (observation_loss_table_row fs rows) pairs)"
proof -
  have formed: "term_formed (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows)))"
    using facets rows by (auto simp: data_list_term_formed split: prod.splits)
  have element: "observation_table_losses.related
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) (observation_value_term z) q \<longleftrightarrow>
      q=observation_loss_table_row fs rows z" if "z\<in>set pairs" for z q
    using facets rows keys that by (cases z) (auto simp only: observation_table_loss_key_lists fst_conv snd_conv)
  show ?thesis by (rule observation_table_losses.encoded_input[
    where f=observation_value_term and g="observation_loss_table_row fs rows", OF formed element])
qed

lemma observation_table_candidate_product:
  "data_product_list cs cs=map observation_value_term (List.product cs cs)"
  by (simp add: product_concat_map map_concat map_map comp_def)

end
