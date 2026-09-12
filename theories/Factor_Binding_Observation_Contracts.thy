theory Factor_Binding_Observation_Contracts
  imports Factor_Binding_Observation_Clauses Factor_Scheme_Observations
    Factor_Proof_Node_Reading Factor_Compiled_Applications
begin

section \<open>The independent row relation includes every supplied field\<close>

definition binding_observation_row :: "bool\<Rightarrow>factor_term\<Rightarrow>factor_term\<Rightarrow>factor_term\<Rightarrow>bool" where
  "binding_observation_row first u r v \<longleftrightarrow>
    (\<exists>a x y. r=Pair_Term (Pair_Term u a) (Pair_Term x y) \<and>
      v=Pair_Term a (if first then x else y) \<and>
      term_formed u \<and> term_formed a \<and> term_formed x \<and> term_formed y)"

locale binding_observation_row_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry :: nat and first :: bool
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=binding_observation_row_schema first"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=context_relation_argument (h 0) (Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)))
        (Pair_Term (h 1) (if first then h 2 else h 3)))"
  by (cases first; subst ordinary_positive_entry_valuation)
    (auto simp: family binding_observation_row_schema_def schema_variables_def call)

theorem at_arguments:
  "(entry,context_relation_argument u r v)\<in>positive_meaning P \<longleftrightarrow>
    binding_observation_row first u r v"
proof
  assume "(entry,context_relation_argument u r v)\<in>positive_meaning P"
  then show "binding_observation_row first u r v"
    by (simp only: valuation factor_term.inject binding_observation_row_def) blast
next
  assume "binding_observation_row first u r v"
  then obtain a x y where fields: "r=Pair_Term (Pair_Term u a) (Pair_Term x y)"
    "v=Pair_Term a (if first then x else y)"
    "term_formed u" "term_formed a" "term_formed x" "term_formed y"
    by (auto simp: binding_observation_row_def)
  let ?h="(\<lambda>_::nat. u)(1:=a,2:=x,3:=y)"
  show "(entry,context_relation_argument u r v)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h]) (use fields in auto)
qed

end

interpretation binding_observation_first:
  binding_observation_row_profile binding_observation_program 343 True
  by (rule binding_observation_row_profile.intro)
    (auto simp: binding_observation_clauses_def binding_observation_call)

interpretation binding_observation_second:
  binding_observation_row_profile binding_observation_program 344 False
  by (rule binding_observation_row_profile.intro)
    (auto simp: binding_observation_clauses_def binding_observation_call)

interpretation binding_observation_first_list: related_list_profile binding_observation_program 343 345
  by (rule related_list_profile.intro)
    (auto simp: binding_observation_clauses_def binding_observation_call)

interpretation binding_observation_second_list: related_list_profile binding_observation_program 344 346
  by (rule related_list_profile.intro)
    (auto simp: binding_observation_clauses_def binding_observation_call)

section \<open>Both complete observations concern the same input sequence\<close>

interpretation binding_observation_pair:
  paired_context_results_profile binding_observation_program 347 345 346
  by (rule paired_context_results_profile.intro)
    (auto simp: binding_observation_clauses_def binding_observation_pair_schema_def binding_observation_call)

lemmas binding_observation_pair_valuation=binding_observation_pair.valuation
lemmas binding_observation_pair_arguments=binding_observation_pair.at_arguments

definition binding_observation_result :: "factor_term\<Rightarrow>bool" where
  "binding_observation_result t \<longleftrightarrow>
    (\<exists>u bs xs ys. t=binding_observation_argument u (data_list_term bs) (data_list_term xs) (data_list_term ys) \<and>
      term_formed u \<and> list_all2 (binding_observation_row True u) bs xs \<and>
      list_all2 (binding_observation_row False u) bs ys)"

theorem binding_observation_exact:
  "(347,t)\<in>positive_meaning binding_observation_program \<longleftrightarrow> binding_observation_result t"
  unfolding binding_observation_result_def
  by (rule binding_observation_pair.related_lists_exact)
    (simp only: binding_observation_first_list.exact binding_observation_first.at_arguments
      binding_observation_second_list.exact binding_observation_second.at_arguments)+

corollary binding_observation_lists:
  "(347,binding_observation_argument u (data_list_term bs) (data_list_term xs) (data_list_term ys))
      \<in>positive_meaning binding_observation_program \<longleftrightarrow>
    term_formed u \<and> list_all2 (binding_observation_row True u) bs xs \<and>
    list_all2 (binding_observation_row False u) bs ys"
  by (simp only: binding_observation_pair_arguments binding_observation_first_list.lists
    binding_observation_second_list.lists binding_observation_first.at_arguments
    binding_observation_second.at_arguments; blast)

section \<open>Actual pattern observations preserve every source key\<close>

theorem binding_observation_pattern_rows:
  assumes owner_formed: "term_formed (use_data_term u)"
    and source: "\<forall>a\<in>set As. octets_formed a \<and> pattern_formed (s a)"
    and variables: "\<forall>a\<in>set As. \<forall>b\<in>pattern_variables (s a). octets_formed b"
  shows "(347,binding_observation_argument (use_data_term u)
    (positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As))
    (binding_rows_term (map (\<lambda>a. (a,evaluate_pattern Payload_Term (s a))) As))
    (binding_rows_term (map (\<lambda>a. (a,evaluate_pattern
      (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) (s a))) As)))
    \<in>positive_meaning binding_observation_program"
proof -
  have first: "term_formed (evaluate_pattern Payload_Term (s a))" if "a\<in>set As" for a
    by (rule evaluate_pattern_formed) (use source variables that in auto)
  have second: "term_formed (evaluate_pattern (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) (s a))"
    if "a\<in>set As" for a
    by (rule evaluate_pattern_formed) (use source that in auto)
  have inputs: "positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)=
      data_list_term (map (\<lambda>a. Pair_Term (Pair_Term (use_data_term u) (Payload_Term a))
        (pattern_claim_observation (s a))) As)"
    by (induction As) (simp_all add: site_data_term_def)
  show ?thesis
    using owner_formed source first second
    by (simp only: inputs binding_rows_as_terms map_map comp_def binding_observation_lists
      list_all2_map1 list_all2_map2 list_all2_same)
      (auto simp: pattern_claim_observation_def binding_observation_row_def site_data_term_def)
qed

text \<open>
  Both list operations reuse the general native sequence-relation proof.
  All input row fields must be formed, including the component that one
  projection does not return. Each row's owning use must equal the shared
  context. Both outputs preserve the original row order and repetitions.

  This is a conversion of rows. Complete functional binding admission and
  admission of the represented patterns remain separate prerequisites of a
  symbolic-argument checker. The pattern-row theorem connects this operation
  to the determining observations of actual replacement patterns.
\<close>

end
