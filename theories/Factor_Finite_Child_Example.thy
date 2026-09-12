theory Factor_Finite_Child_Example
  imports Factor_Finite_Child_Source_Checks Factor_Ground_Schema_Reports
    Factor_Executable_Environment_Values Factor_Inference_Claim_Correspondence
    Factor_Inference_Specialization_Total Factor_Single_Premise_Graphs Factor_Scheme_Claim_Values
begin

abbreviation example_child_environment where
  "example_child_environment p \<equiv> decode_finite_environment (finite_child_sources p)"

abbreviation example_child_extension where
  "example_child_extension p \<equiv> decode_finite_environment (finite_child_extension p)"

abbreviation example_child_schema where
  "example_child_schema p \<equiv> decode_finite_schema (finite_child_schema p)"

abbreviation example_child_program where
  "example_child_program p \<equiv> decode_finite_system (finite_child_program p)"

section \<open>The complete new sources retain all existing data\<close>

lemma finite_child_original_included:
  "environment_included (decode_finite_environment (finite_literal_sources p)) (example_child_environment p)"
  by (auto simp: environment_included_def finite_child_sources_def Let_def map_relation_values_def)

lemma finite_child_source_included:
  "environment_included (example_child_environment p) (example_child_extension p)"
  by (auto simp: environment_included_def finite_child_extension_def Let_def map_relation_values_def)

lemma finite_child_presentations:
  "environment_value_presents (example_child_environment []) (finite_environment_term (finite_child_sources []))"
  "environment_value_presents (example_child_extension []) (finite_environment_term (finite_child_extension []))"
  using finite_environment_value_exact[where E="example_child_environment []" and C="finite_child_sources []"]
    finite_environment_value_exact[where E="example_child_extension []" and C="finite_child_extension []"]
    finite_child_environment_checks by auto

lemma finite_child_extended_package:
  "native_package_at (example_child_extension []) (Some [2]) [0] (example_child_program [])"
  by (rule native_package_included[OF finite_child_native_package finite_child_source_included finite_child_environments_formed(2)])

definition finite_child_ordinary_rows ::
  "octets\<Rightarrow>(local_address\<times>(local_address option definition_site\<times>factor_term)) list" where
  "finite_child_ordinary_rows p=[([24],(Some [2],[1]),Payload_Term p)]"

definition finite_child_report :: "octets\<Rightarrow>factor_term" where
  "finite_child_report p=ground_schema_rows_report (Payload_Term p) (finite_child_ordinary_rows p) []"

lemma finite_child_report_presents:
  "schema_reference_presents (example_child_schema []) (finite_child_report [])"
proof -
  have data: "schema_data_formed (example_child_schema [])" by (rule native_schema_data_formed[OF finite_child_native_schema])
  have ground: "schema_variables (example_child_schema [])={}"
    by (simp add: finite_child_schema_def decode_finite_schema_def schema_variables_def map_relation_values_def)
  have formed: "schema_formed (example_child_schema [])" by (rule native_schema_formed[OF finite_child_native_schema])
  have ground_instance: "schema_instance (example_child_schema []) {} (Payload_Term []) (set (finite_child_ordinary_rows []))"
    using schema_evaluation_instance[OF formed, where f="\<lambda>_. Payload_Term []"]
    by (simp only: ground)
      (simp add: finite_child_schema_def decode_finite_schema_def finite_child_ordinary_rows_def
        evaluate_schema_premises_def map_socket_graph_def map_relation_values_def map_prod_def)
  show ?thesis
    by (simp only: finite_child_report_def ground_schema_reference_rows[OF ground])
      (use data ground_instance in \<open>simp add: finite_child_ordinary_rows_def finite_child_schema_def
        decode_finite_schema_def material_instance_relation_def map_relation_values_def\<close>)
qed

lemma finite_child_pattern_call:
  "schema_pattern_call (example_child_program []) (Some [2],[1]) (Pattern_Payload [])"
proof -
  have formed: "schema_system_formed (example_child_program [])" by (rule native_package_system_formed[OF finite_child_native_package])
  show ?thesis unfolding schema_pattern_call_def
    by (rule conjI[OF formed], rule exI[of _ "Pattern_Payload []"], rule exI[of _ "{}"])
      (simp add: finite_child_program_def decode_finite_system_def map_relation_values_def
        pattern_bindings_formed_def single_valued_def rel_dom_def)
qed

lemma finite_child_pattern_boundary:
  "schema_pattern_boundary (example_child_program []) (Some [2],[1]) (example_child_schema [])"
  using finite_child_pattern_call native_schema_formed[OF finite_child_native_schema]
  by (simp add: schema_pattern_boundary_def finite_child_schema_def decode_finite_schema_def map_relation_values_def)

lemma finite_child_binding:
  "specialization_binding_at (example_child_extension []) (Some [2]) [0] (Some [2],[1]) [7]
    (example_child_environment []) (Some [2]) [3] (example_child_environment []) (Some [2]) [8]
    (finite_child_report []) (positioned_binding_rows_term []) [[3]] []"
proof -
  have clause: "(((Some [2],[1]),[7]),example_child_schema [])\<in>system_clauses (example_child_program [])"
    by (simp add: finite_child_program_def decode_finite_system_def map_relation_values_def)
  have ground: "schema_variables (example_child_schema [])={}"
    by (simp add: finite_child_schema_def decode_finite_schema_def schema_variables_def map_relation_values_def)
  show ?thesis by (rule ground_specialization_binding[OF finite_child_extended_package clause ground
      finite_child_environments_formed(1) finite_child_artifact_at finite_child_binder
      finite_child_native_schema finite_child_pattern_boundary finite_child_report_presents])
qed

lemma finite_child_inference:
  "inference_specialization_at (example_child_extension []) (Some [2]) [0] (Some []) [] (Some [2],[1]) [7]
    (example_child_environment []) (Some [2]) [3] (example_child_environment []) (Some [2]) [8]
    (finite_child_report []) finite_child_discharges finite_child_parent_interior finite_child_parent_slots [[3]] []"
  unfolding inference_specialization_at_def
  by (intro conjI, simp add: finite_child_discharges_def,
    simp add: finite_child_parent_interior_def finite_literal_node_interior_def,
    simp add: finite_child_parent_slots_def, rule exI[of _ "[]"])
    (use finite_child_native_parent finite_child_binding in simp)

section \<open>The original symbolic graph, its claims and identified assumption boundary\<close>

definition child_symbolic_graph ::
  "(local_address option definition_site,local_address option definition_site,
    local_address option definition_site,local_address option definition_site,local_address) schema_proof_scheme" where
  "child_symbolic_graph=single_premise_graph (Some [],[]) (Some [1],[]) (Some [2],[24]) (Some [2],[7]) {||}"

definition child_symbolic_claims ::
  "octets\<Rightarrow>(local_address option definition_site\<times>(local_address option definition_site\<times>local_address term_pattern)) list" where
  "child_symbolic_claims p=[((Some [],[]),(Some [2],[1]),Pattern_Payload p),
    ((Some [1],[]),(Some [2],[1]),Pattern_Payload p)]"

lemma child_symbolic_graph_formed:
  "schema_graph_formed child_symbolic_graph (Some [],[])"
  unfolding child_symbolic_graph_def by (rule single_premise_graph_formed) simp

lemma finite_child_native_graph:
  "native_schema_graph_at (example_child_extension []) (Some [],[])
    (map_inference_values pattern_claim_observation child_symbolic_graph)"
proof -
  have formed: "schema_graph_formed (map_inference_values pattern_claim_observation child_symbolic_graph) (Some [],[])"
    by (rule map_inference_values_formed[OF child_symbolic_graph_formed])
  show ?thesis unfolding native_schema_graph_at_def
    by (intro conjI, rule formed)
      (use finite_child_native_parent finite_child_native_assertion in
        \<open>simp only: child_symbolic_graph_def single_premise_graph_values;
          auto simp: single_premise_graph_def
          schema_graph_premises_def finite_child_discharges_def\<close>)
qed

lemma child_symbolic_local_reading:
  "schema_scheme_local_reading (positioned_program (example_child_program [])) child_symbolic_graph
    (set (child_symbolic_claims [])) (Some [],[]) (Schema_Inference (Some [2],[7]) {||})"
proof -
  have clause: "(((Some [2],[1]),[7]),example_child_schema [])\<in>system_clauses (example_child_program [])"
    by (simp add: finite_child_program_def decode_finite_system_def map_relation_values_def)
  have original: "schema_clause_specialization (example_child_program []) (Some [2],[1]) [7] {} (example_child_schema [])"
    using schema_clause_specialization_graph(1)[OF clause, where s=Pattern_Variable]
      finite_child_pattern_boundary
    by (simp add: finite_child_schema_def decode_finite_schema_def schema_variables_def map_relation_values_def)
  have specialized: "schema_clause_specialization (positioned_program (example_child_program [])) (Some [2],[1])
      (Some [2],[7]) {} (rename_schema id (Pair (Some [2])) id (example_child_schema []))"
    using positioned_clause_specializationI[OF native_package_system_formed[OF finite_child_native_package] original]
    by (simp add: rekey_pattern_bindings_def)
  have functional: "single_valued (set (child_symbolic_claims []))"
    by (simp add: child_symbolic_claims_def single_valued_def)
  have domain: "rel_dom (set (child_symbolic_claims []))=schema_graph_nodes child_symbolic_graph"
    by (auto simp: child_symbolic_claims_def child_symbolic_graph_def single_premise_graph_def schema_graph_nodes_def rel_dom_def)
  have claim: "((Some [],[]),(Some [2],[1]),Pattern_Payload [])\<in>set (child_symbolic_claims [])"
    by (simp add: child_symbolic_claims_def)
  show ?thesis
    by (simp only: schema_scheme_local_reading_fixed_target[where V="{||}", unfolded fset_simps(1),
      OF child_symbolic_graph_formed functional domain claim specialized])
      (auto simp: child_symbolic_claims_def child_symbolic_graph_def single_premise_graph_def schema_graph_premises_def
        finite_child_schema_def decode_finite_schema_def map_relation_values_def rename_schema_def
        map_socket_graph_def map_prod_def case_prod_unfold)
qed

lemma child_symbolic_claim_values:
  "scheme_claim_values (positioned_program (example_child_program [])) child_symbolic_graph
    (set (child_symbolic_claims [])) (child_symbolic_claims []) [((Some [1],[]),(Some [2],[1]),Pattern_Payload [])]"
proof -
  have call: "schema_pattern_call (positioned_program (example_child_program [])) (Some [2],[1]) (Pattern_Payload [])"
    using schema_pattern_call_agreement[OF positioned_program_calls[OF native_package_system_formed[OF finite_child_native_package]],
      of "(Some [2],[1])" "Pattern_Payload []"] finite_child_pattern_call by blast
  show ?thesis using call child_symbolic_local_reading
    by (auto simp: scheme_claim_values_def child_symbolic_claims_def child_symbolic_graph_def single_premise_graph_def
      schema_graph_premises_def)
qed

text \<open>
  The one-premise identity clause has an actual separate assertion child. Both
  complete native sources and the original symbolic local judgment are checked.
  The identified assumption boundary is exactly the child row. This supplies
  no claim that the asserted literal is a closed positive consequence of the
  identity-only program.
\<close>


section \<open>The compiled values contain exactly the admitted complete operands\<close>

definition finite_child_inference_term :: "octets\<Rightarrow>factor_term" where
  "finite_child_inference_term p=inference_claim_source_argument
    (finite_environment_term (finite_child_extension p)) (use_data_term (Some [2])) (Payload_Term [0])
    (use_data_term (Some [])) (Payload_Term []) (use_data_term (Some [2])) (Payload_Term [1]) (Payload_Term [7])
    (finite_environment_term (finite_child_sources p)) (use_data_term (Some [2])) (Payload_Term [3])
    (Pair_Term (finite_environment_term (finite_child_sources p)) (Pair_Term (use_data_term (Some [2])) (Payload_Term [8])))
    (Payload_Term []) (Payload_Term p) (call_instance_rows_term (finite_child_ordinary_rows p)) (Payload_Term [])
    (Payload_Term p) (call_instance_rows_term (finite_child_ordinary_rows p)) (Payload_Term [])
    (discharge_rows_term finite_child_discharges)
    (data_list_term (map Payload_Term finite_child_parent_interior))
    (data_list_term (map Payload_Term finite_child_parent_slots))
    (data_list_term (map Payload_Term [[3]])) (Payload_Term [])"

definition finite_child_claim_term :: "octets\<Rightarrow>factor_term" where
  "finite_child_claim_term p=Pair_Term (finite_child_inference_term p)
    (positioned_call_rows_term (observed_claim_rows (child_symbolic_claims p)))"

lemma finite_child_terms_data:
  "self_contained_term (finite_child_inference_term p)"
  "self_contained_term (finite_child_claim_term p)"
  by (simp_all add: finite_child_inference_term_def finite_child_claim_term_def finite_child_ordinary_rows_def
    child_symbolic_claims_def observed_claim_rows_def map_prod_def pattern_claim_observation_def
    data_list_term_self_contained call_instance_value_def case_prod_unfold)

definition finite_child_inference_value :: "octets\<Rightarrow>finite_factor_term" where
  "finite_child_inference_value p=the (finite_self_contained_term (finite_child_inference_term p))"

definition finite_child_claim_value :: "octets\<Rightarrow>finite_factor_term" where
  "finite_child_claim_value p=the (finite_self_contained_term (finite_child_claim_term p))"

lemma decode_finite_child_values [simp]:
  "decode_finite_term (finite_child_inference_value p)=finite_child_inference_term p"
  "decode_finite_term (finite_child_claim_value p)=finite_child_claim_term p"
  unfolding finite_child_inference_value_def finite_child_claim_value_def
  by (rule decode_finite_self_contained_term[OF finite_child_terms_data(1)],
      rule decode_finite_self_contained_term[OF finite_child_terms_data(2)])

theorem finite_child_inference_admitted:
  "(350,decode_finite_term (finite_child_inference_value []))\<in>positive_meaning inference_specialization_system"
  using inference_specialization_on_sources[OF finite_child_presentations(2) finite_child_presentations(1)
    finite_child_presentations(1), where pu="Some [2]" and pr="[0]" and nu="Some []" and nr="[]"
    and du="Some [2]" and dr="[1]" and c="[7]" and v="Some [2]" and r="[3]" and w="Some [2]" and t="[8]"
    and ds=finite_child_discharges and NIs=finite_child_parent_interior and NKs=finite_child_parent_slots
    and RIs="[[3]]" and RKs="[]"] finite_child_inference
  by (simp add: finite_child_inference_term_def finite_child_report_def)

theorem finite_child_claim_admitted:
  "(359,decode_finite_term (finite_child_claim_value []))\<in>positive_meaning inference_claim_system"
proof -
  have node: "((Some [],[]),Schema_Inference (Some [2],[7]) {||})\<in>fset (graph_inferences child_symbolic_graph)"
    by (simp add: child_symbolic_graph_def single_premise_graph_def)
  have domain: "rel_dom (set (child_symbolic_claims []))=schema_graph_nodes child_symbolic_graph"
    by (auto simp: child_symbolic_claims_def child_symbolic_graph_def single_premise_graph_def schema_graph_nodes_def rel_dom_def)
  have claim: "((Some [],[]),(Some [2],[1]),Pattern_Payload [])\<in>set (child_symbolic_claims [])"
    by (simp add: child_symbolic_claims_def)
  have rows: "formed_key_rows (encoded_positioned_calls (observed_claim_rows (child_symbolic_claims [])))"
    by (simp add: child_symbolic_claims_def observed_claim_rows_def map_prod_def pattern_claim_observation_def
      call_instance_value_def octets_formed_def)
  have keys: "distinct (map fst (child_symbolic_claims []))" by (simp add: child_symbolic_claims_def)
  show ?thesis
    using inference_claim_on_symbolic_sources[OF finite_child_presentations(2) finite_child_presentations(1)
      finite_child_presentations(1) finite_child_extended_package finite_child_native_graph node
      finite_child_native_schema domain claim, where v="Some [2]" and r="[3]"
      and b="Payload_Term []" and hx="Payload_Term []" and qs="finite_child_ordinary_rows []"
      and cs="Payload_Term []" and hy="Payload_Term []" and ws="finite_child_ordinary_rows []"
      and ms="Payload_Term []" and ds=finite_child_discharges
      and NIs=finite_child_parent_interior and NKs=finite_child_parent_slots
      and RIs="[[3]]" and RKs="[]"]
      finite_child_inference rows keys child_symbolic_local_reading
    by (simp add: finite_child_claim_term_def finite_child_inference_term_def finite_child_report_def)
qed

end
