theory Factor_Inference_Claim_Contracts
  imports Factor_Inference_Claim_Clauses Factor_Inference_Specialization_Contracts
begin

section \<open>Every original field participates in the same seven native premises\<close>

lemma inference_claim_valuation:
  "(359,z)\<in>positive_meaning inference_claim_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27}. term_formed (h j)) \<and>
      z=inference_claim_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 19) (h 20) (h 21) (h 22) (h 23) (h 24) (h 14) (h 15) (h 16) (h 17) (h 18) (h 13) \<and>
      (350,inference_claim_source_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 19) (h 20) (h 21) (h 22) (h 23) (h 24) (h 14) (h 15) (h 16) (h 17) (h 18))\<in>positive_meaning inference_specialization_system \<and>
      (21,(h 13))\<in>positive_meaning keyed_list_system \<and>
      (28,key_fibre_argument (Pair_Term (h 3) (h 4)) (h 13) (data_list_term [Pair_Term (Pair_Term (h 5) (h 6)) (Pair_Term (h 19) (h 22))]))\<in>positive_meaning key_fibre_system \<and>
      (100,keyed_row_join_argument (h 13) (h 14) (h 25))\<in>positive_meaning keyed_row_join_system \<and>
      (358,paired_context_results_argument (h 5) (h 25) (h 26) (h 27))\<in>positive_meaning prefixed_observation_program \<and>
      (353,Pair_Term (h 26) (h 20))\<in>positive_meaning keyed_table_comparison_system \<and>
      (353,Pair_Term (h 27) (h 23))\<in>positive_meaning keyed_table_comparison_system)"
proof -
  have ordinary: "schema_material_premises inference_claim_schema={}"
    by (simp add: inference_claim_schema_def)
  have accepts: "schema_call_formed inference_claim_full_system 359
      (evaluate_pattern h (schema_conclusion inference_claim_schema))"
    if "\<forall>a\<in>schema_variables inference_claim_schema. term_formed (h a)" for h
    using that by (auto simp: inference_claim_full_call inference_claim_schema_def
      schema_variables_def octets_formed_def)
  show ?thesis
    apply (simp only: inference_claim_meaning)
    apply (subst ordinary_single_clause_valuation[OF inference_claim_full_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: inference_claim_schema_def schema_variables_def inference_claim_full_readers
      conj_ac all_conj_distrib imp_conjL)
    done
qed

definition inference_claim_calls where
  "inference_claim_calls e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js \<longleftrightarrow>
    (350,inference_claim_source_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk)\<in>positive_meaning inference_specialization_system \<and>
    (21,js)\<in>positive_meaning keyed_list_system \<and>
    (28,key_fibre_argument (Pair_Term nu nr) js (data_list_term [Pair_Term (Pair_Term du dr) (Pair_Term hx hy)]))\<in>positive_meaning key_fibre_system \<and>
    (\<exists>joined left right. (100,keyed_row_join_argument js ds joined)\<in>positive_meaning keyed_row_join_system \<and>
      (358,paired_context_results_argument du joined left right)\<in>positive_meaning prefixed_observation_program \<and>
      (353,Pair_Term left qs)\<in>positive_meaning keyed_table_comparison_system \<and>
      (353,Pair_Term right ws)\<in>positive_meaning keyed_table_comparison_system)"

theorem inference_claim_at_arguments:
  "(359,inference_claim_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js)\<in>positive_meaning inference_claim_system \<longleftrightarrow>
    inference_claim_calls e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js"
proof
  assume "(359,inference_claim_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js)\<in>positive_meaning inference_claim_system"
  then show "inference_claim_calls e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js"
    by (simp only: inference_claim_valuation data_list_term.simps factor_term.inject inference_claim_calls_def) blast
next
  assume "inference_claim_calls e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js"
  then obtain joined left right where reads:
    "(350,inference_claim_source_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk)\<in>positive_meaning inference_specialization_system"
    "(21,js)\<in>positive_meaning keyed_list_system"
    "(28,key_fibre_argument (Pair_Term nu nr) js (data_list_term [Pair_Term (Pair_Term du dr) (Pair_Term hx hy)]))\<in>positive_meaning key_fibre_system"
    "(100,keyed_row_join_argument js ds joined)\<in>positive_meaning keyed_row_join_system"
    "(358,paired_context_results_argument du joined left right)\<in>positive_meaning prefixed_observation_program"
    "(353,Pair_Term left qs)\<in>positive_meaning keyed_table_comparison_system"
    "(353,Pair_Term right ws)\<in>positive_meaning keyed_table_comparison_system"
    by (auto simp only: inference_claim_calls_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then nu else if j=4 then nr else if j=5 then du else if j=6 then dr else if j=7 then c else if j=8 then f else if j=9 then v else if j=10 then r else if j=11 then q else if j=12 then b else if j=13 then js else if j=14 then ds else if j=15 then ni else if j=16 then nk else if j=17 then ri else if j=18 then rk else if j=19 then hx else if j=20 then qs else if j=21 then cs else if j=22 then hy else if j=23 then ws else if j=24 then ms else if j=25 then joined else if j=26 then left else right"
  have formed:
    "term_formed (inference_claim_source_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk)"
    "term_formed js"
    "term_formed (paired_context_results_argument du joined left right)"
    using schema_call_formed_target[OF positive_meaning_formed[OF reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(5)]] by auto
  show "(359,inference_claim_argument e pu pr nu nr du dr c f v r q b hx qs cs hy ws ms ds ni nk ri rk js)\<in>positive_meaning inference_claim_system"
    by (simp only: inference_claim_valuation; rule exI[of _ ?h]) (use reads formed in auto)
qed

text \<open>
  This equation is for the actual complete native operand. It retains the
  original source admission and separately checks the whole claim table,
  parent fibre, every discharge occurrence and both complete observations.
  No correctness of a represented symbolic claim is inferred merely from
  its table membership. That connection uses the symbolic source contracts.
\<close>

end
