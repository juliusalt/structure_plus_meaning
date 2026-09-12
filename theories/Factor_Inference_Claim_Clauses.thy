theory Factor_Inference_Claim_Clauses
  imports Factor_Inference_Claim_Components
begin

section \<open>The original inference argument and the complete claim table\<close>

abbreviation inference_claim_source_argument where
  "inference_claim_source_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk \<equiv>
    inference_specialization_argument e pu pr nu nr du dr c f v r q b
      (Pair_Term (Pair_Term hx (Pair_Term qs cs)) (Pair_Term hy (Pair_Term ws ms))) ds ni nk ri rk"

abbreviation inference_claim_source_pattern where
  "inference_claim_source_pattern e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk \<equiv>
    inference_specialization_pattern e pu pr nu nr du dr c f v r q b
      (Pattern_Pair (Pattern_Pair hx (Pattern_Pair qs cs)) (Pattern_Pair hy (Pattern_Pair ws ms))) ds ni nk ri rk"

abbreviation inference_claim_argument where
  "inference_claim_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js \<equiv>
    Pair_Term (inference_claim_source_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk) js"

abbreviation inference_claim_pattern where
  "inference_claim_pattern e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js \<equiv>
    Pattern_Pair (inference_claim_source_pattern e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk) js"

definition inference_claim_schema :: "(nat,nat,nat) factor_schema" where
  "inference_claim_schema=data_rule
    (inference_claim_pattern data_x data_y data_z data_w (Pattern_Variable 4)
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
      (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)
      (Pattern_Variable 19) (Pattern_Variable 20) (Pattern_Variable 21)
      (Pattern_Variable 22) (Pattern_Variable 23) (Pattern_Variable 24)
      (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 16)
      (Pattern_Variable 17) (Pattern_Variable 18) (Pattern_Variable 13))
    {(0,350,inference_claim_source_pattern data_x data_y data_z data_w (Pattern_Variable 4)
       (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
       (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)
       (Pattern_Variable 19) (Pattern_Variable 20) (Pattern_Variable 21)
       (Pattern_Variable 22) (Pattern_Variable 23) (Pattern_Variable 24)
       (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 16)
       (Pattern_Variable 17) (Pattern_Variable 18)),
     (1,21,Pattern_Variable 13),
     (2,28,keyed_row_join_pattern (Pattern_Pair data_w (Pattern_Variable 4)) (Pattern_Variable 13)
       (data_list_pattern [Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))
         (Pattern_Pair (Pattern_Variable 19) (Pattern_Variable 22))])),
     (3,100,keyed_row_join_pattern (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 25)),
     (4,358,paired_context_results_pattern (Pattern_Variable 5) (Pattern_Variable 25)
       (Pattern_Variable 26) (Pattern_Variable 27)),
     (5,353,Pattern_Pair (Pattern_Variable 26) (Pattern_Variable 20)),
     (6,353,Pattern_Pair (Pattern_Variable 27) (Pattern_Variable 23))}"

definition inference_claim_full_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_claim_full_system=add_view_definition inference_claim_components 359 data_x {(0,inference_claim_schema)}"

interpretation inference_claim_view:
  positive_view inference_claim_components 359 data_x "{(0,inference_claim_schema)}"
  by (rule positive_view.intro)
    (auto simp: inference_claim_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma inference_claim_full_formed [simp]: "schema_system_formed inference_claim_full_system"
  using inference_claim_view.formed by (simp only: inference_claim_full_system_def)

lemma inference_claim_full_definitions [simp]:
  "system_definitions inference_claim_full_system=insert 359 (system_definitions inference_claim_components)"
  by (simp add: inference_claim_full_system_def)

lemma inference_claim_full_call:
  "schema_call_formed inference_claim_full_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_claim_full_system \<and> term_formed t"
  using added_variable_calls[OF inference_claim_components_formed
    inference_claim_full_formed[unfolded inference_claim_full_system_def] inference_claim_components_call]
  by (simp only: inference_claim_full_system_def[symmetric])

lemma inference_claim_full_clause [simp]:
  "((359,c),S)\<in>system_clauses inference_claim_full_system \<longleftrightarrow>
    c=0 \<and> S=inference_claim_schema"
  using inference_claim_view.no_old_clause by (auto simp: inference_claim_full_system_def)

lemma inference_claim_full_old_meaning:
  assumes "d\<in>system_definitions inference_claim_components"
  shows "(d,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning inference_claim_components"
  using inference_claim_view.old_meaning[OF assms] by (simp only: inference_claim_full_system_def)

lemma inference_claim_full_readers:
  "(350,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow>
    (350,t)\<in>positive_meaning inference_specialization_system"
  "(21,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(28,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  "(100,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow> (100,t)\<in>positive_meaning keyed_row_join_system"
  "(353,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow> (353,t)\<in>positive_meaning keyed_table_comparison_system"
  "(358,t)\<in>positive_meaning inference_claim_full_system \<longleftrightarrow> (358,t)\<in>positive_meaning prefixed_observation_program"
  using inference_claim_full_old_meaning[of 350 t] inference_claim_full_old_meaning[of 21 t]
    inference_claim_full_old_meaning[of 28 t] inference_claim_full_old_meaning[of 100 t]
    inference_claim_full_old_meaning[of 353 t] inference_claim_full_old_meaning[of 358 t]
    inference_claim_component_meanings[of t] by auto

section \<open>The public program retains exactly the reader's dependency closure\<close>

definition inference_claim_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_claim_system=rooted_system inference_claim_full_system {359}"

lemma inference_claim_formed [simp]: "schema_system_formed inference_claim_system"
  unfolding inference_claim_system_def by (rule rooted_system_formed[OF inference_claim_full_formed])

lemma inference_claim_root: "359\<in>system_definitions inference_claim_system"
  using rooted_system_roots[OF inference_claim_full_formed, of "{359}"]
  by (auto simp: inference_claim_system_def)

lemma inference_claim_least:
  assumes "359\<in>U" "system_dependency_closed inference_claim_full_system U"
  shows "system_definitions inference_claim_system\<subseteq>U"
  unfolding inference_claim_system_def
  by (rule rooted_system_least[OF inference_claim_full_formed _ _ assms(2)]) (use assms(1) in auto)

lemma inference_claim_call:
  "schema_call_formed inference_claim_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_claim_system \<and> term_formed t"
  unfolding inference_claim_system_def
  by (rule rooted_system_variable_calls[OF inference_claim_full_formed inference_claim_full_call])

lemma inference_claim_meaning:
  "(359,t)\<in>positive_meaning inference_claim_system \<longleftrightarrow>
    (359,t)\<in>positive_meaning inference_claim_full_system"
  unfolding inference_claim_system_def
  by (rule rooted_system_meaning_at[OF inference_claim_full_formed
    inference_claim_root[unfolded inference_claim_system_def]])

text \<open>
  The public operand is the complete original inference argument paired with
  the complete claim table. The actual node supplies the parent key; its
  actual cited definition supplies the callee and the premise-key owner.
  Both material reports, all binder information, discharges and source
  supports remain present. Three private values contain the discharge join
  and its two complete projections. Whole-graph and claim-call formation
  remain conditions of the surrounding symbolic argument.
\<close>

end
