theory Factor_Prefixed_Observation_Patterns
  imports Factor_Prefixed_Observation_Contracts Factor_Scheme_Claim_Tables Factor_Keyed_Table_Views Factor_Proof_Claim_Instances
begin

section \<open>Positioned symbolic calls have two complete callee-preserving views\<close>

abbreviation claim_pattern_view where
  "claim_pattern_view first p \<equiv>
    evaluate_pattern (if first then Payload_Term else (\<lambda>_. Target_Term (Whole_Artifact empty_artifact))) p"

definition lowered_claim_rows where
  "lowered_claim_rows xs=map (\<lambda>(s,q). (snd s,q)) xs"

definition projected_claim_rows where
  "projected_claim_rows first xs=map (map_prod id (map_prod id (claim_pattern_view first))) (lowered_claim_rows xs)"

lemma prefixed_observation_pattern_row:
  "prefixed_observation_row first (use_data_term u)
      (Pair_Term (definition_site_value s) (call_instance_value d (pattern_claim_observation p))) z
    \<longleftrightarrow> z=Pair_Term (Payload_Term (snd s)) (call_instance_value d (claim_pattern_view first p)) \<and>
      fst s=u \<and> term_formed (definition_site_value s) \<and>
      term_formed (call_instance_value d (pattern_claim_observation p))"
  by (cases s; cases d; cases first)
    (auto simp: prefixed_observation_row_def pattern_claim_observation_def call_instance_value_def
      site_data_term_def inj_eq[OF use_data_term_injective])

lemma projected_claim_rows_term:
  "call_instance_rows_term (projected_claim_rows first xs)=
    data_list_term (map (\<lambda>(s,d,p). Pair_Term (Payload_Term (snd s))
      (call_instance_value d (claim_pattern_view first p))) xs)"
  by (simp add: projected_claim_rows_def lowered_claim_rows_def binding_rows_as_terms
    comp_def map_prod_def case_prod_unfold)

lemma prefixed_observation_pattern_list:
  "list_all2 (prefixed_observation_row first (use_data_term u))
      (map (\<lambda>(s,d,p). Pair_Term (definition_site_value s)
        (call_instance_value d (pattern_claim_observation p))) xs) zs \<longleftrightarrow>
    zs=map (\<lambda>(s,d,p). Pair_Term (Payload_Term (snd s))
      (call_instance_value d (claim_pattern_view first p))) xs \<and>
    (\<forall>s d p. (s,d,p)\<in>set xs \<longrightarrow> fst s=u \<and>
      term_formed (definition_site_value s) \<and>
      term_formed (call_instance_value d (pattern_claim_observation p)))"
  by (simp only: list_all2_map1)
    (auto simp: prefixed_observation_pattern_row list_all2_function_restricted case_prod_unfold split: prod.splits; blast)

theorem prefixed_observation_pattern_rows:
  "(358,paired_context_results_argument (use_data_term u)
      (positioned_call_rows_term (observed_claim_rows xs)) left right)
      \<in>positive_meaning prefixed_observation_program \<longleftrightarrow>
    term_formed (use_data_term u) \<and>
      formed_key_rows (encoded_positioned_calls (observed_claim_rows xs)) \<and>
      (\<forall>s q. (s,q)\<in>set xs \<longrightarrow> fst s=u) \<and>
      left=call_instance_rows_term (projected_claim_rows True xs) \<and>
      right=call_instance_rows_term (projected_claim_rows False xs)"
proof -
  have input: "positioned_call_rows_term (observed_claim_rows xs)=
      data_list_term (map (\<lambda>(s,d,p). Pair_Term (definition_site_value s)
        (call_instance_value d (pattern_claim_observation p))) xs)"
    by (simp add: observed_claim_rows_def comp_def map_prod_def case_prod_unfold)
  show ?thesis
    by (simp only: prefixed_observation_exact prefixed_observation_result_def factor_term.inject
      input data_list_term_injective prefixed_observation_pattern_list
      projected_claim_rows_term)
      (auto simp: observed_claim_rows_def map_prod_def case_prod_unfold
        prefixed_observation_pattern_list[unfolded case_prod_unfold] data_list_term_injective; blast)
qed

lemma projected_claim_rows_keys:
  "map fst (projected_claim_rows first xs)=map snd (map fst xs)"
  by (simp add: projected_claim_rows_def lowered_claim_rows_def comp_def map_prod_def case_prod_unfold)

lemma projected_claim_rows_set:
  "set (projected_claim_rows first xs)=
    map_relation_values (map_prod id (claim_pattern_view first)) (set (lowered_claim_rows xs))"
  by (auto simp: projected_claim_rows_def map_relation_values_def map_prod_def)

lemma lowered_claim_rows_restore:
  assumes owner: "\<And>s q. (s,q)\<in>set xs \<Longrightarrow> fst s=u"
  shows "map (\<lambda>(s,q). ((u,s),q)) (lowered_claim_rows xs)=xs"
  unfolding lowered_claim_rows_def by (rule owned_rows_recover[OF owner])

lemma projected_claim_rows_distinct_keys:
  assumes keys: "distinct (map fst xs)"
    and owner: "\<And>s q. (s,q)\<in>set xs \<Longrightarrow> fst s=u"
  shows "distinct (map fst (projected_claim_rows first xs))"
proof -
  have restore: "map (\<lambda>(s,q). ((u,s),q)) (lowered_claim_rows xs)=xs"
    by (rule lowered_claim_rows_restore[OF owner])
  have nested: "distinct (map (Pair u) (map fst (lowered_claim_rows xs)))"
    using arg_cong[OF restore, where f="\<lambda>ys. distinct (map fst ys)"] keys
    by (simp add: comp_def case_prod_unfold)
  have "distinct (map fst (lowered_claim_rows xs))" using nested by (simp only: distinct_map; blast)
  then show ?thesis by (simp add: projected_claim_rows_def comp_def map_prod_def case_prod_unfold)
qed

theorem schema_reference_projected_claims:
  assumes report: "schema_reference_presents S
      (schema_reference_value b hx (call_instance_rows_term qs) cs hy (call_instance_rows_term ws) ms)"
  shows "(set (projected_claim_rows True xs)=set qs \<and>
      set (projected_claim_rows False xs)=set ws) \<longleftrightarrow>
    set (lowered_claim_rows xs)=schema_premises S"
proof -
  have formed: "schema_formed S" using report by (simp add: schema_reference_presents_def schema_data_formed_def)
  have functional: "single_valued (schema_premises S)" using formed by (simp add: schema_formed_def)
  have fields: "set qs=evaluate_schema_premises Payload_Term S"
    "set ws=evaluate_schema_premises (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) S"
    using report by (simp only: schema_reference_presents_def schema_reference_data_def
      schema_reference_outputs_def schema_reference_record_fields factor_term.inject
      call_instance_rows_term_injective; blast)+
  have determining: "inj (\<lambda>q. (map_prod id (claim_pattern_view True) q,
      map_prod id (claim_pattern_view False) q))"
    by (rule paired_observations_prefixed_injective)
      (auto simp: inj_def; metis pattern_claim_observation_def pattern_claim_observation_injective)
  show ?thesis
    using functional_reference_observations_exact[OF functional determining,
      where R="set (lowered_claim_rows xs)"]
    by (simp only: projected_claim_rows_set fields if_True if_False)
      (simp add: evaluate_schema_premises_def map_socket_graph_def map_relation_values_def
        map_prod_def case_prod_unfold)
qed

theorem native_claim_premise_comparison:
  assumes report: "schema_reference_presents S
      (schema_reference_value b hx (call_instance_rows_term qs) cs hy (call_instance_rows_term ws) ms)"
    and formed: "formed_key_rows (encoded_positioned_calls (observed_claim_rows xs))"
    and keys: "distinct (map fst xs)" and owner_formed: "term_formed (use_data_term u)"
  shows "(\<exists>left right.
      (358,paired_context_results_argument (use_data_term u)
        (positioned_call_rows_term (observed_claim_rows xs)) left right)\<in>positive_meaning prefixed_observation_program \<and>
      (353,Pair_Term left (call_instance_rows_term qs))\<in>positive_meaning keyed_table_comparison_system \<and>
      (353,Pair_Term right (call_instance_rows_term ws))\<in>positive_meaning keyed_table_comparison_system)
    \<longleftrightarrow> set xs=map_socket_graph (Pair u) id id (schema_premises S)"
proof -
  have qformed: "term_formed (call_instance_rows_term qs)" and wformed: "term_formed (call_instance_rows_term ws)"
    using schema_reference_presents_formed[OF report] by auto
  have reference_keys: "distinct (map fst qs)" "distinct (map fst ws)"
  proof -
    have order: "distinct qs" "distinct ws"
      and fields: "set qs=evaluate_schema_premises Payload_Term S"
        "set ws=evaluate_schema_premises (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) S"
      using report by (simp only: schema_reference_presents_def schema_reference_data_def
        schema_reference_outputs_def schema_reference_record_fields factor_term.inject
        call_instance_rows_term_injective; blast)+
    have sf: "schema_formed S" using report by (simp add: schema_reference_presents_def schema_data_formed_def)
    have sv: "single_valued (evaluate_schema_premises f S)" for f
      using sf by (auto simp: schema_formed_def evaluate_schema_premises_def map_socket_graph_def single_valued_def; blast)
    show "distinct (map fst qs)" using order(1) fields(1) sv
      by (simp add: distinct_keys_iff)
    show "distinct (map fst ws)" using order(2) fields(2) sv
      by (simp add: distinct_keys_iff)
  qed
  have views: "term_formed (call_instance_rows_term (projected_claim_rows first xs))"
    if owner: "\<forall>s q. (s,q)\<in>set xs \<longrightarrow> fst s=u" for first
  proof -
    have native: "(358,paired_context_results_argument (use_data_term u)
        (positioned_call_rows_term (observed_claim_rows xs))
        (call_instance_rows_term (projected_claim_rows True xs))
        (call_instance_rows_term (projected_claim_rows False xs)))\<in>positive_meaning prefixed_observation_program"
      by (simp only: prefixed_observation_pattern_rows) (use formed owner_formed owner in blast)
    show ?thesis using schema_call_formed_target[OF positive_meaning_formed[OF native]] by (cases first) auto
  qed
  have ordered: "distinct (map fst (projected_claim_rows first xs))"
    if "\<forall>s q. (s,q)\<in>set xs \<longrightarrow> fst s=u" for first
    by (rule projected_claim_rows_distinct_keys[OF keys, where u=u]) (use that in blast)
  have comparison: "(\<exists>left right.
      (358,paired_context_results_argument (use_data_term u)
        (positioned_call_rows_term (observed_claim_rows xs)) left right)\<in>positive_meaning prefixed_observation_program \<and>
      (353,Pair_Term left (call_instance_rows_term qs))\<in>positive_meaning keyed_table_comparison_system \<and>
      (353,Pair_Term right (call_instance_rows_term ws))\<in>positive_meaning keyed_table_comparison_system)
      \<longleftrightarrow> (\<forall>s q. (s,q)\<in>set xs \<longrightarrow> fst s=u) \<and>
        set (lowered_claim_rows xs)=schema_premises S"
    by (simp only: prefixed_observation_pattern_rows)
      (use formed owner_formed qformed wformed reference_keys views ordered
        schema_reference_projected_claims[OF report, of xs]
        keyed_table_comparison_call_rows in blast)
  have positioned: "((\<forall>s q. (s,q)\<in>set xs \<longrightarrow> fst s=u) \<and>
      set (lowered_claim_rows xs)=schema_premises S) \<longleftrightarrow>
      set xs=map_socket_graph (Pair u) id id (schema_premises S)"
    by (auto simp: lowered_claim_rows_def map_socket_graph_def map_prod_def; force)
  show ?thesis by (simp only: comparison positioned)
qed

text \<open>
  Both complete table views retain the same callee at each socket. The original
  schema's functional premise relation prevents mixing observations belonging
  to different patterns. Projection also enforces the original owning use on
  every row. The full report, including material observations and binder scope,
  remains an assumption of this correspondence and is never reconstructed from
  only its ordinary premises.
\<close>

end
