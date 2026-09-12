theory Factor_Inference_Claim_Compilation
  imports Factor_Inference_Claim_Clauses Factor_Inference_Reader_Investigation
    Finite_Keyed_Table_Comparison Factor_Finite_Inference_Premises
begin

section \<open>New finite schemas are compiled from the complete actual native clauses\<close>

definition compiled_inference_claim_schema where
  "compiled_inference_claim_schema=finite_schema_of (inference_claim_schema)"

lemmas compiled_inference_claim_schema_code [code]=compiled_inference_claim_schema_def
  [unfolded inference_claim_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_inference_claim_schema_exact:
  "decode_finite_schema (compiled_inference_claim_schema)=inference_claim_schema"
  unfolding compiled_inference_claim_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: inference_claim_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_claim_join_nil_schema where
  "compiled_claim_join_nil_schema=finite_schema_of (keyed_row_join_nil_schema)"

lemmas compiled_claim_join_nil_schema_code [code]=compiled_claim_join_nil_schema_def
  [unfolded keyed_row_join_nil_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_claim_join_nil_schema_exact:
  "decode_finite_schema (compiled_claim_join_nil_schema)=keyed_row_join_nil_schema"
  unfolding compiled_claim_join_nil_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: keyed_row_join_nil_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_claim_join_step_schema where
  "compiled_claim_join_step_schema=finite_schema_of (keyed_row_join_cons_schema)"

lemmas compiled_claim_join_step_schema_code [code]=compiled_claim_join_step_schema_def
  [unfolded keyed_row_join_cons_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_claim_join_step_schema_exact:
  "decode_finite_schema (compiled_claim_join_step_schema)=keyed_row_join_cons_schema"
  unfolding compiled_claim_join_step_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: keyed_row_join_cons_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_prefixed_row_schema where
  "compiled_prefixed_row_schema first=finite_schema_of (prefixed_observation_row_schema first)"

declare compiled_prefixed_row_schema_def[code del]

lemmas compiled_prefixed_row_schema_code [code]=
  compiled_prefixed_row_schema_def[where first=True,
    unfolded prefixed_observation_row_schema_def finite_schema_of_def map_relation_values_def, simplified]
  compiled_prefixed_row_schema_def[where first=False,
    unfolded prefixed_observation_row_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_prefixed_row_schema_exact:
  "decode_finite_schema (compiled_prefixed_row_schema first)=prefixed_observation_row_schema first"
  unfolding compiled_prefixed_row_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: prefixed_observation_row_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_prefixed_nil_schema where
  "compiled_prefixed_nil_schema=finite_schema_of (related_list_nil_schema)"

lemmas compiled_prefixed_nil_schema_code [code]=compiled_prefixed_nil_schema_def
  [unfolded related_list_nil_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_prefixed_nil_schema_exact:
  "decode_finite_schema (compiled_prefixed_nil_schema)=related_list_nil_schema"
  unfolding compiled_prefixed_nil_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: related_list_nil_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_prefixed_step_schema where
  "compiled_prefixed_step_schema row entry=finite_schema_of (related_list_step_schema row entry)"

lemmas compiled_prefixed_step_schema_code [code]=compiled_prefixed_step_schema_def
  [unfolded related_list_step_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_prefixed_step_schema_exact:
  "decode_finite_schema (compiled_prefixed_step_schema row entry)=related_list_step_schema row entry"
  unfolding compiled_prefixed_step_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: related_list_step_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

definition compiled_prefixed_pair_schema where
  "compiled_prefixed_pair_schema=finite_schema_of (paired_context_results_schema 356 357)"

lemmas compiled_prefixed_pair_schema_code [code]=compiled_prefixed_pair_schema_def
  [unfolded paired_context_results_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma compiled_prefixed_pair_schema_exact:
  "decode_finite_schema (compiled_prefixed_pair_schema)=paired_context_results_schema 356 357"
  unfolding compiled_prefixed_pair_schema_def
  by (rule decode_finite_schema_of)
    (auto simp: paired_context_results_schema_def schema_formed_def single_valued_def rel_dom_def octets_formed_def)

lemmas compiled_claim_schemas=
  compiled_inference_claim_schema_exact compiled_claim_join_nil_schema_exact compiled_claim_join_step_schema_exact compiled_prefixed_row_schema_exact compiled_prefixed_nil_schema_exact compiled_prefixed_step_schema_exact compiled_prefixed_pair_schema_exact

definition inference_claim_new_library where
  "inference_claim_new_library=finite_compiled_library
    [(359,compiled_inference_claim_schema),
     (100,compiled_claim_join_nil_schema),(100,compiled_claim_join_step_schema),
     (354,compiled_prefixed_row_schema True),(355,compiled_prefixed_row_schema False),
     (356,compiled_prefixed_nil_schema),(356,compiled_prefixed_step_schema 354 356),
     (357,compiled_prefixed_nil_schema),(357,compiled_prefixed_step_schema 355 357),
     (358,compiled_prefixed_pair_schema)]"

section \<open>Each constructor retains its complete component clause contract\<close>

lemma inference_claim_full_inference_agreement:
  "systems_agree_on inference_specialization_system inference_claim_full_system
    (system_definitions inference_specialization_system)"
proof -
  have fresh: "359\<notin>system_definitions inference_specialization_system" by simp
  show ?thesis unfolding inference_claim_full_system_def
    by (rule iffD2[OF systems_agree_on_added[OF fresh] inference_claim_components_inference_agreement])
qed

lemma inference_claim_full_table_agreement:
  "systems_agree_on keyed_table_comparison_system inference_claim_full_system
    (system_definitions keyed_table_comparison_system)"
proof -
  have fresh: "359\<notin>system_definitions keyed_table_comparison_system"
    using keyed_table_base_subdomain by auto
  show ?thesis unfolding inference_claim_full_system_def
    by (rule iffD2[OF systems_agree_on_added[OF fresh] inference_claim_components_table_agreement])
qed

lemma inference_claim_full_join_agreement:
  "systems_agree_on keyed_row_join_system inference_claim_full_system
    (system_definitions keyed_row_join_system)"
proof -
  have fresh: "359\<notin>system_definitions keyed_row_join_system" by simp
  show ?thesis unfolding inference_claim_full_system_def
    by (rule iffD2[OF systems_agree_on_added[OF fresh] inference_claim_components_join_agreement])
qed

lemma inference_claim_full_projection_agreement:
  "systems_agree_on prefixed_observation_program inference_claim_full_system
    (system_definitions prefixed_observation_program)"
proof -
  have component: "systems_agree_on prefixed_observation_program inference_claim_components
      (system_definitions prefixed_observation_program)"
    using inference_claim_projection_group.group_agreement
    by (simp only: inference_claim_components_def)
  have fresh: "359\<notin>system_definitions prefixed_observation_program" by simp
  show ?thesis unfolding inference_claim_full_system_def
    by (rule iffD2[OF systems_agree_on_added[OF fresh] component])
qed

lemma inference_claim_new_compiled_clause:
  assumes member: "(d,S,ps)\<in>set inference_claim_new_library"
  shows "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses inference_claim_full_system \<and>
    (d,Pattern_Variable 0)\<in>system_interfaces inference_claim_full_system"
proof -
  have own_clause: "((359,0),inference_claim_schema)\<in>system_clauses inference_claim_full_system" by simp
  have own_interface: "(359,data_x)\<in>system_interfaces inference_claim_full_system"
    by (simp add: inference_claim_full_system_def)
  have own: "\<exists>c. ((359,c),inference_claim_schema)\<in>system_clauses inference_claim_full_system \<and>
      (359,data_x)\<in>system_interfaces inference_claim_full_system"
    using own_clause own_interface by blast
  have join: "\<exists>c. ((100,c),T)\<in>system_clauses inference_claim_full_system \<and>
      (100,data_x)\<in>system_interfaces inference_claim_full_system"
    if source_schema: "T\<in>{keyed_row_join_nil_schema,keyed_row_join_cons_schema}" for T
  proof -
    obtain c where clause: "((100,c),T)\<in>system_clauses keyed_row_join_system"
      using source_schema by (auto simp: keyed_row_join_clauses_def)
    have interface: "(100,data_x)\<in>system_interfaces keyed_row_join_system"
      by (simp add: keyed_row_join_system_def)
    show ?thesis by (rule exI[of _ c],
      rule whole_agreement_clause_interface[OF inference_claim_full_join_agreement clause interface])
  qed
  have projection: "\<exists>c. ((e,c),T)\<in>system_clauses inference_claim_full_system \<and>
      (e,data_x)\<in>system_interfaces inference_claim_full_system"
    if inside: "e\<in>{354,355,356,357,358}" and clause: "(c,T)\<in>prefixed_observation_clauses e" for e c T
    by (rule exI[of _ c], rule whole_agreement_clause_interface[OF inference_claim_full_projection_agreement])
      (use inside clause in auto)
  have sources:
    "(d=359 \<and> decode_finite_schema S=inference_claim_schema) \<or>
     (d=100 \<and> decode_finite_schema S\<in>{keyed_row_join_nil_schema,keyed_row_join_cons_schema}) \<or>
     (d\<in>{354,355,356,357,358} \<and> (\<exists>c. (c,decode_finite_schema S)\<in>prefixed_observation_clauses d))"
    using member by (auto simp: inference_claim_new_library_def finite_compiled_library_member
      compiled_claim_schemas prefixed_observation_clauses_def related_list_clauses_def)
  consider (reader_case) "d=359" "decode_finite_schema S=inference_claim_schema"
    | (join_case) "d=100" "decode_finite_schema S\<in>{keyed_row_join_nil_schema,keyed_row_join_cons_schema}"
    | (projection_case) c where "d\<in>{354,355,356,357,358}"
        "(c,decode_finite_schema S)\<in>prefixed_observation_clauses d"
    using sources by blast
  then show ?thesis
  proof cases
    case reader_case
    show ?thesis using own by (simp only: reader_case)
  next
    case join_case
    show ?thesis using join[OF join_case(2)] by (simp only: join_case(1))
  next
    case (projection_case c)
    show ?thesis by (rule projection[OF projection_case])
  qed
qed

section \<open>Original inference and table libraries share that complete program\<close>

definition inference_claim_construction_library where
  "inference_claim_construction_library=inference_reader_investigation_library @
    keyed_table_construction_library @ inference_claim_new_library"

lemma inference_claim_compiled_clause:
  assumes member: "(d,S,ps)\<in>set inference_claim_construction_library"
  shows "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses inference_claim_full_system \<and>
    (d,Pattern_Variable 0)\<in>system_interfaces inference_claim_full_system"
proof -
  have inherited: "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses inference_claim_full_system \<and>
      (d,Pattern_Variable 0)\<in>system_interfaces inference_claim_full_system"
    if source_member: "(d,S,ps)\<in>set inference_reader_investigation_library"
  proof -
    obtain c where clause: "((d,c),decode_finite_schema S)\<in>system_clauses inference_specialization_system"
      and interface: "(d,Pattern_Variable 0)\<in>system_interfaces inference_specialization_system"
      using inference_reader_investigation_clause[OF source_member] by blast
    show ?thesis by (rule exI[of _ c],
      rule whole_agreement_clause_interface[OF inference_claim_full_inference_agreement clause interface])
  qed
  have table: "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses inference_claim_full_system \<and>
      (d,Pattern_Variable 0)\<in>system_interfaces inference_claim_full_system"
    if table_member: "(d,S,ps)\<in>set keyed_table_construction_library"
  proof -
    obtain c where clause: "((d,c),decode_finite_schema S)\<in>system_clauses keyed_table_comparison_system"
      and interface: "(d,Pattern_Variable 0)\<in>system_interfaces keyed_table_comparison_system"
      using keyed_table_compiled_clause[OF table_member] by blast
    show ?thesis by (rule exI[of _ c],
      rule whole_agreement_clause_interface[OF inference_claim_full_table_agreement clause interface])
  qed
  show ?thesis using member inherited table inference_claim_new_compiled_clause[of d S ps]
    by (auto simp: inference_claim_construction_library_def)
qed

theorem inference_claim_construction_member_sound:
  assumes member: "(d,S,ps)\<in>set inference_claim_construction_library"
    and rule_instance: "schema_rule_instance (decode_finite_schema S) (positive_meaning inference_claim_full_system) t"
  shows "(d,t)\<in>positive_meaning inference_claim_full_system"
proof -
  obtain c where clause: "((d,c),decode_finite_schema S)\<in>system_clauses inference_claim_full_system"
    and interface: "(d,Pattern_Variable 0)\<in>system_interfaces inference_claim_full_system"
    using inference_claim_compiled_clause[OF member] by blast
  show ?thesis by (rule positive_variable_clause_rule[OF inference_claim_full_formed clause interface rule_instance])
qed

theorem inference_claim_selected_guided_sound:
  assumes selected: "set L\<subseteq>set inference_claim_construction_library"
    and known: "image decode_finite_call_term (fset K)\<subseteq>positive_meaning inference_claim_full_system"
  shows "image decode_finite_call_term (finite_inference_result (finite_guided_rules n L C Q) K)
    \<subseteq>positive_meaning inference_claim_full_system"
  by (rule finite_guided_closure_sound)
    (use selected known inference_claim_construction_member_sound in blast)+

corollary inference_claim_constructed_root_sound:
  assumes selected: "set L\<subseteq>set inference_claim_construction_library"
    and known: "image decode_finite_call_term (fset K)\<subseteq>positive_meaning inference_claim_full_system"
    and found: "(359,t)\<in>finite_inference_result (finite_guided_rules n L C Q) K"
  shows "(359,decode_finite_term t)\<in>positive_meaning inference_claim_system"
proof -
  have sound: "image decode_finite_call_term (finite_inference_result (finite_guided_rules n L C Q) K)
      \<subseteq>positive_meaning inference_claim_full_system"
    by (rule inference_claim_selected_guided_sound[OF selected known])
  have decoded: "decode_finite_call_term (359,t)\<in>positive_meaning inference_claim_full_system"
    by (rule subsetD[OF sound imageI[OF found]])
  show ?thesis using decoded
    by (simp add: decode_finite_call_term_def inference_claim_meaning)
qed

theorem inference_claim_literal_known_sound:
  "image decode_finite_call_term (set (finite_literal_inference_known []))
    \<subseteq>positive_meaning inference_claim_full_system"
  by (rule subset_trans[OF finite_literal_inference_known_sound
    whole_agreement_positive_subset[OF inference_specialization_formed inference_claim_full_formed
      inference_claim_full_inference_agreement]])

text \<open>
  The complete library contains actual clauses of one formed program. Both
  projection traversals, both recursive join clauses and the local reader
  are compiled from their source schemas, with complete premise enumerations.
  Original inference and table constructors reuse their established clause
  contracts through whole agreement. Generated closure remains conditional
  on every supplied known premise; a resulting reader call then transfers
  to its least dependency program. The retained literal source example's
  initial calls are proved in this same program without assuming entry 350.
\<close>

export_code inference_claim_construction_library checking SML

end
