theory Factor_Inference_Claim_Correspondence
  imports Factor_Inference_Claim_Contracts Factor_Inference_Specialization_Observed
    Factor_Prefixed_Observation_Patterns
begin

section \<open>The actual complete native operand is the original symbolic local judgment\<close>

theorem inference_claim_on_symbolic_sources:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents H g"
    and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root (map_inference_values pattern_claim_observation G)"
    and node: "((nu,nr),Schema_Inference (du,c) V)\<in>fset (graph_inferences G)"
    and target: "native_schema_at H w t T"
    and domain: "rel_dom (set xs)=schema_graph_nodes G"
    and claim: "((nu,nr),(du,dr),p)\<in>set xs"
  shows "(359,inference_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term nu) (Payload_Term nr)
      (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term r)
      (Pair_Term g (Pair_Term (use_data_term w) (Payload_Term t))) b hx (call_instance_rows_term qs) cs
      hy (call_instance_rows_term ws) ms (discharge_rows_term ds)
      (data_list_term (map Payload_Term NIs)) (data_list_term (map Payload_Term NKs))
      (data_list_term (map Payload_Term RIs)) (data_list_term (map Payload_Term RKs)) (positioned_call_rows_term (observed_claim_rows xs)))\<in>positive_meaning inference_claim_system
    \<longleftrightarrow> inference_specialization_at E pu pr nu nr (du,dr) c F v r H w t
      (schema_reference_value b hx (call_instance_rows_term qs) cs hy (call_instance_rows_term ws) ms)
      ds NIs NKs RIs RKs \<and>
      formed_key_rows (encoded_positioned_calls (observed_claim_rows xs)) \<and>
      distinct (map fst xs) \<and>
      schema_scheme_local_reading (positioned_program P) G (set xs) (nu,nr) (Schema_Inference (du,c) V)"
proof -
  let ?arg="inference_claim_argument e (use_data_term pu) (Payload_Term pr) (use_data_term nu) (Payload_Term nr)
      (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term r)
      (Pair_Term g (Pair_Term (use_data_term w) (Payload_Term t))) b hx (call_instance_rows_term qs) cs
      hy (call_instance_rows_term ws) ms (discharge_rows_term ds)
      (data_list_term (map Payload_Term NIs)) (data_list_term (map Payload_Term NKs))
      (data_list_term (map Payload_Term RIs)) (data_list_term (map Payload_Term RKs)) (positioned_call_rows_term (observed_claim_rows xs))"
  let ?actual="inference_specialization_at E pu pr nu nr (du,dr) c F v r H w t
      (schema_reference_value b hx (call_instance_rows_term qs) cs hy (call_instance_rows_term ws) ms)
      ds NIs NKs RIs RKs"
  let ?rest="(28,key_fibre_argument (Pair_Term (use_data_term nu) (Payload_Term nr))
        (positioned_call_rows_term (observed_claim_rows xs))
        (data_list_term [Pair_Term (Pair_Term (use_data_term du) (Payload_Term dr)) (Pair_Term hx hy)]))
        \<in>positive_meaning key_fibre_system \<and>
      (\<exists>joined left right.
        (100,keyed_row_join_argument (positioned_call_rows_term (observed_claim_rows xs))
          (discharge_rows_term ds) joined)\<in>positive_meaning keyed_row_join_system \<and>
        (358,paired_context_results_argument (use_data_term du) joined left right)\<in>positive_meaning prefixed_observation_program \<and>
        (353,Pair_Term left (call_instance_rows_term qs))\<in>positive_meaning keyed_table_comparison_system \<and>
        (353,Pair_Term right (call_instance_rows_term ws))\<in>positive_meaning keyed_table_comparison_system)"
  let ?local="schema_scheme_local_reading (positioned_program P) G (set xs) (nu,nr) (Schema_Inference (du,c) V)"
  have source_gate: "(350,inference_claim_source_argument e (use_data_term pu) (Payload_Term pr) (use_data_term nu) (Payload_Term nr)
      (use_data_term du) (Payload_Term dr) (Payload_Term c) f (use_data_term v) (Payload_Term r)
      (Pair_Term g (Pair_Term (use_data_term w) (Payload_Term t))) b hx (call_instance_rows_term qs) cs
      hy (call_instance_rows_term ws) ms (discharge_rows_term ds)
      (data_list_term (map Payload_Term NIs)) (data_list_term (map Payload_Term NKs))
      (data_list_term (map Payload_Term RIs)) (data_list_term (map Payload_Term RKs)))\<in>positive_meaning inference_specialization_system
      \<longleftrightarrow> ?actual"
    by (simp only: inference_specialization_on_sources[OF sources])
  have whole_gate: "(359,?arg)\<in>positive_meaning inference_claim_system \<longleftrightarrow>
      ?actual \<and> formed_key_rows (encoded_positioned_calls (observed_claim_rows xs)) \<and>
        distinct (map fst xs) \<and> ?rest"
    by (simp only: inference_claim_at_arguments inference_claim_calls_def source_gate observed_claim_table_admission conj_assoc)
  have remaining: "?rest \<longleftrightarrow> ?local"
    if actual: "?actual" and rows: "formed_key_rows (encoded_positioned_calls (observed_claim_rows xs))"
      and keys: "distinct (map fst xs)"
  proof -
    let ?report="schema_reference_value b hx (call_instance_rows_term qs) cs hy (call_instance_rows_term ws) ms"
    let ?R="rename_schema id (Pair du) id T"
    let ?joined="joined_relation_rows (set xs) ds"
    have correspondence: "set ds=schema_graph_premises G (nu,nr)"
      "schema_clause_specialization (positioned_program P) (du,dr) (du,c) (fset V) ?R"
      "schema_reference_presents T ?report"
      using inference_specialization_observed[where n="(nu,nr)" and d="(du,dr)",
        unfolded fst_conv snd_conv, OF actual package graph node target] by simp_all
    have gf: "schema_graph_formed G root"
      using graph by (simp only: native_schema_graph_at_def scheme_observations_preserve_geometry; blast)
    have functional: "single_valued (set xs)" using keys by (simp only: distinct_keys_iff; blast)
    have covered: "rel_ran (set ds)\<subseteq>rel_dom (set xs)"
      using schema_graph_premises_targets[OF gf, of "(nu,nr)"] domain correspondence(1) by simp
    obtain bs where raw: "native_proof_node_at E nu nr (Schema_Inference (du,c) (fset_of_list bs))
        (set ds) (set NIs) (set NKs)"
      using actual by (auto simp only: inference_specialization_at_def fst_conv)
    have source_rows: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
        term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
      using native_discharge_values_formed[OF raw subset_refl] by (auto simp: case_prod_unfold)
    have native_join: "(100,keyed_row_join_argument (positioned_call_rows_term (observed_claim_rows xs)) (discharge_rows_term ds)
        (positioned_call_rows_term (observed_claim_rows ?joined)))\<in>positive_meaning keyed_row_join_system"
      by (rule observed_claim_join[OF rows keys covered source_rows])
    have joined_formed: "formed_key_rows (encoded_positioned_calls (observed_claim_rows ?joined))"
      using schema_call_formed_target[OF positive_meaning_formed[OF native_join]]
      by (auto simp: pair_list_term_formed_iff data_list_term_formed comp_def case_prod_unfold)
    have dorder: "distinct ds" using actual by (simp only: inference_specialization_at_def; blast)
    have dfunctional: "single_valued (set ds)"
      by (simp only: correspondence(1)) (rule schema_graph_premises_functional[OF gf])
    have dkeys: "distinct (map fst ds)" using dorder dfunctional by (simp only: distinct_keys_iff)
    have joined_keys: "distinct (map fst ?joined)" by (simp only: joined_relation_rows_keys dkeys)
    have owner: "term_formed (use_data_term du)"
      using actual by (auto simp only: inference_specialization_at_def specialization_binding_at_def fst_conv)
    have views: "(\<exists>left right.
        (358,paired_context_results_argument (use_data_term du)
          (positioned_call_rows_term (observed_claim_rows ?joined)) left right)\<in>positive_meaning prefixed_observation_program \<and>
        (353,Pair_Term left (call_instance_rows_term qs))\<in>positive_meaning keyed_table_comparison_system \<and>
        (353,Pair_Term right (call_instance_rows_term ws))\<in>positive_meaning keyed_table_comparison_system)
      \<longleftrightarrow> set ?joined=map_socket_graph (Pair du) id id (schema_premises T)"
      by (rule native_claim_premise_comparison[OF correspondence(3) joined_formed joined_keys owner])
    have nposition: "(nu,nr)\<in>environment_positions E"
      using native_schema_graph_positions[OF graph, unfolded map_inference_values_geometry(2)] node
      by (auto simp: schema_graph_nodes_def rel_dom_def)
    have nformed: "term_formed (definition_site_value (nu,nr))"
      by (rule environment_position_value_formed[OF native_schema_graph_environment[OF graph] nposition])
    have same_claim: "((nu,nr),(du,dr),schema_conclusion T)\<in>set xs \<longleftrightarrow> schema_conclusion T=p"
      using single_valued_outputs[OF functional claim] claim by auto
    have head: "pattern_claim_observation (schema_conclusion T)=Pair_Term hx hy"
      by (rule schema_reference_claim_observations(1)[OF correspondence(3)])
    have parent: "(28,key_fibre_argument (Pair_Term (use_data_term nu) (Payload_Term nr))
        (positioned_call_rows_term (observed_claim_rows xs)) (data_list_term [Pair_Term (Pair_Term (use_data_term du) (Payload_Term dr)) (Pair_Term hx hy)]))
        \<in>positive_meaning key_fibre_system \<longleftrightarrow> schema_conclusion T=p"
      using observed_claim_parent_fibre[OF keys, where n="(nu,nr)" and d="(du,dr)" and p="schema_conclusion T"]
        nformed rows same_claim
      by (simp only: head call_instance_value_def site_data_term_def fst_conv snd_conv; blast)
    have joined_set: "set ?joined=schema_graph_premises G (nu,nr) O set xs"
      using joined_relation_rows_set[OF functional covered] by (simp only: correspondence(1))
    have renamed: "schema_premises ?R=map_socket_graph (Pair du) id id (schema_premises T)"
      by (simp add: rename_schema_def map_socket_graph_def map_prod_def case_prod_unfold)
    have rest: "?rest \<longleftrightarrow> schema_conclusion T=p \<and>
        schema_premises ?R=schema_graph_premises G (nu,nr) O set xs"
      by (simp only: parent observed_claim_join_output[OF rows keys covered source_rows] renamed)
        (use views joined_set in blast)
    have local: "?local \<longleftrightarrow> schema_conclusion T=p \<and>
        schema_premises ?R=schema_graph_premises G (nu,nr) O set xs"
      using schema_scheme_local_reading_fixed_target[OF gf functional domain claim correspondence(2)]
      by (simp add: rename_schema_def)
    show ?thesis using rest local by blast
  qed
  show ?thesis using whole_gate remaining by blast
qed

text \<open>
  The equivalence concerns the existing symbolic local-reading judgment and
  the actual native entry 359. Both directions retain the complete original
  inference-specialization input, including the actual replacement, native
  target, report, discharge occurrences and four support lists. Whole table
  formation and one occurrence per key remain explicit on the right-hand side.

  The native graph is the injective observation of the supplied symbolic graph.
  Its complete domain is related to the supplied claim list independently.
  This local theorem does not assert that every claim is a formed symbolic call,
  that every graph node passes its local reader, or that assertion claims hold.
\<close>

end
