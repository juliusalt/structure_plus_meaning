theory Factor_Replay_Slot_Reading
  imports Factor_Replay_Source_Reading
begin

section \<open>One actual binding key is read by the selected grammar\<close>

abbreviation replay_root_slot_observed where
  "replay_root_slot_observed e pu pr k \<equiv> \<exists>a rows socket endpoint slots address interior.
    (37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system \<and>
    (32,rooted_rows_argument a pr rows)\<in>positive_meaning family_admission_system \<and>
    selected_data_member (Pair_Term socket endpoint) rows \<and>
    (42,citation_reading_argument e pu endpoint (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system \<and>
    selected_data_member k slots"

abbreviation replay_slot_observed where
  "replay_slot_observed e pu pr au ar ru rr u k \<equiv>
    (u=pu \<and> replay_root_slot_observed e pu pr k) \<or>
    (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term u a))\<in>positive_meaning package_membership_system \<and>
      (105,citation_observation_argument e u a k)\<in>positive_meaning definition_slot_reading_system) \<or>
    (u=au \<and> (\<exists>d t i slots. (58,application_reading_argument e au ar d t i slots)\<in>positive_meaning application_reading_system \<and>
      selected_data_member k slots)) \<or>
    (\<exists>a n i slots. (98,proof_graph_subject_argument e ru rr (Pair_Term u a))\<in>positive_meaning proof_graph_membership_system \<and>
      (94,term_quotation_argument e u a n i slots)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member k slots)"

abbreviation replay_slot_candidates where
  "replay_slot_candidates E pu pr au ar ru rr u k \<equiv>
    (\<exists>v r. pu=use_data_term v \<and> pr=Payload_Term r \<and> u=v \<and>
      (u,k)\<in>requested_slots E (native_root_requests E v r)) \<or>
    (\<exists>v r a P. pu=use_data_term v \<and> pr=Payload_Term r \<and> native_package_at E v r P \<and>
      (u,a)\<in>system_definitions P \<and> k\<in>native_definition_slots E u a) \<or>
    (\<exists>r d t I K. au=use_data_term u \<and> ar=Payload_Term r \<and> native_application_at E u r d t I K \<and> k\<in>K) \<or>
    (\<exists>v r a G N D I K. ru=use_data_term v \<and> rr=Payload_Term r \<and> native_schema_graph_at E (v,r) G \<and>
      (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D I K \<and> k\<in>K)"

abbreviation replay_slot_reading_result :: "factor_term \<Rightarrow> bool" where
  "replay_slot_reading_result z \<equiv> \<exists>E e pu pr au ar ru rr u k.
    z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term (use_data_term u) (Payload_Term k)) \<and>
    environment_value_presents E e \<and> term_formed (replay_context_term e pu pr au ar ru rr) \<and>
    replay_slot_candidates E pu pr au ar ru rr u k"

definition replay_root_slot_schema :: "(nat,nat,nat) factor_schema" where
  "replay_root_slot_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair data_y (Pattern_Variable 7)))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 8)),
     (1,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) data_z) (Pattern_Variable 9)),
     (2,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)) (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12))),
     (3,42,citation_reading_pattern data_x data_y (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14)) (Pattern_Variable 15)),
     (4,5,Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 16)))}"

definition replay_definition_slot_schema :: "(nat,nat,nat) factor_schema" where
  "replay_definition_slot_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 9))),
     (1,105,citation_observation_pattern data_x (Pattern_Variable 7) (Pattern_Variable 9) (Pattern_Variable 8))}"

definition replay_application_slot_schema :: "(nat,nat,nat) factor_schema" where
  "replay_application_slot_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair data_w (Pattern_Variable 7)))
    {(0,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)),
     (1,5,Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)))}"

definition replay_node_slot_schema :: "(nat,nat,nat) factor_schema" where
  "replay_node_slot_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))
    {(0,98,proof_graph_subject_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 9))),
     (1,94,term_quotation_pattern data_x (Pattern_Variable 7) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)),
     (2,5,Pattern_Pair (Pattern_Variable 8) (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13)))}"

definition replay_slot_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "replay_slot_reading_clauses={(0,replay_root_slot_schema),(1,replay_definition_slot_schema),(2,replay_application_slot_schema),(3,replay_node_slot_schema)}"

definition replay_slot_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_slot_reading_system=add_view_definition replay_source_reading_system 107 data_x replay_slot_reading_clauses"

lemma replay_slot_reading_system_formed [simp]: "schema_system_formed replay_slot_reading_system"
  unfolding replay_slot_reading_system_def
  by (rule add_recursive_definition_formed[OF replay_source_reading_system_formed])
    (auto simp: replay_slot_reading_clauses_def replay_root_slot_schema_def replay_definition_slot_schema_def replay_application_slot_schema_def replay_node_slot_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma replay_slot_reading_definitions [simp]:
  "system_definitions replay_slot_reading_system=insert 107 (system_definitions replay_source_reading_system)"
  by (simp add: replay_slot_reading_system_def)

lemma replay_slot_reading_call:
  "schema_call_formed replay_slot_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_slot_reading_system \<and> term_formed t"
  using added_variable_calls[OF replay_source_reading_system_formed
    replay_slot_reading_system_formed[unfolded replay_slot_reading_system_def] replay_source_reading_call]
  by (simp only: replay_slot_reading_system_def[symmetric])

lemma replay_slot_reading_old_meaning:
  assumes "d\<in>system_definitions replay_source_reading_system"
  shows "(d,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning replay_source_reading_system"
  using added_definition_preserves_old(2)[OF replay_source_reading_system_formed
    replay_slot_reading_system_formed[unfolded replay_slot_reading_system_def], of d t] assms
  by (auto simp: replay_slot_reading_system_def)

lemma replay_slot_reading_clause [simp]:
  "((107,c),S)\<in>system_clauses replay_slot_reading_system \<longleftrightarrow> (c,S)\<in>replay_slot_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses replay_source_reading_system \<Longrightarrow>
    d\<in>system_definitions replay_source_reading_system" for d c S
    using replay_source_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((107,c),S)\<notin>system_clauses replay_source_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: replay_slot_reading_system_def)
qed

lemma replay_slot_reading_pattern_meaning:
  assumes "d\<in>system_definitions pattern_instantiation_system"
  shows "(d,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning pattern_instantiation_system"
  using replay_slot_reading_old_meaning[of d t] replay_source_reading_material_meaning[of d t]
    material_instantiation_old_meaning[of d t] record_instantiation_old_meaning[of d t]
    vector_instantiation_pattern_meaning[OF assms, of t] assms by auto

lemma replay_slot_reading_components:
  "(37,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(32,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(5,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(42,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (42,t)\<in>positive_meaning citation_reading_system"
  "(83,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(105,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (105,t)\<in>positive_meaning definition_slot_reading_system"
  "(58,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(98,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (98,t)\<in>positive_meaning proof_graph_membership_system"
  "(94,t)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> (94,t)\<in>positive_meaning proof_node_reading_system"
  using replay_slot_reading_old_meaning[of 37 t] replay_source_reading_components(1)[of t]
    replay_slot_reading_old_meaning[of 32 t] replay_source_reading_old_meaning[of 32 t] definition_slot_reading_components(3)[of t]
    replay_slot_reading_old_meaning[of 5 t] replay_source_reading_old_meaning[of 5 t] definition_slot_reading_components(4)[of t]
    replay_slot_reading_pattern_meaning[of 42 t] pattern_instantiation_components(2)[of t]
    replay_slot_reading_old_meaning[of 83 t] replay_source_reading_components(2)[of t]
    replay_slot_reading_old_meaning[of 105 t] replay_source_reading_old_meaning[of 105 t]
    replay_slot_reading_old_meaning[of 58 t] replay_source_reading_material_meaning[of 58 t]
    material_instantiation_old_meaning[of 58 t] record_instantiation_old_meaning[of 58 t]
    vector_instantiation_old_meaning[of 58 t] row_values_old_meaning[of 58 t]
    replay_slot_reading_old_meaning[of 98 t] replay_source_reading_components(3)[of t]
    replay_slot_reading_old_meaning[of 94 t] replay_source_reading_graph_meaning[of 94 t]
    proof_graph_membership_node_meaning[of 94 t] by auto

lemma replay_root_slot_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)" and read:
    "(37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system"
    "(32,rooted_rows_argument a pr rows)\<in>positive_meaning family_admission_system"
    "(5,Pair_Term (Pair_Term socket endpoint) (Pair_Term rows rest))\<in>positive_meaning bag_comparison_system"
    "(42,citation_reading_argument e pu endpoint (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system"
    "(5,Pair_Term k (Pair_Term slots remainder))\<in>positive_meaning bag_comparison_system"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term pu k))\<in>positive_meaning replay_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then k else if j=8 then a else if j=9 then rows else if j=10 then socket else if j=11 then endpoint else if j=12 then rest else if j=13 then slots else if j=14 then address else if j=15 then interior else remainder"
  have result: "(107,evaluate_pattern ?h (schema_conclusion replay_root_slot_schema))\<in>positive_meaning replay_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(4)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(5)]] in
        \<open>auto simp: replay_slot_reading_clauses_def replay_root_slot_schema_def schema_variables_def
          replay_slot_reading_call replay_slot_reading_components\<close>)
  show ?thesis using result by (simp add: replay_root_slot_schema_def)
qed

lemma replay_definition_slot_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)" and read:
    "(83,package_subject_argument e pu pr (Pair_Term u a))\<in>positive_meaning package_membership_system"
    "(105,citation_observation_argument e u a k)\<in>positive_meaning definition_slot_reading_system"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k))\<in>positive_meaning replay_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then u else if j=8 then k else a"
  have result: "(107,evaluate_pattern ?h (schema_conclusion replay_definition_slot_schema))\<in>positive_meaning replay_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]] in
        \<open>auto simp: replay_slot_reading_clauses_def replay_definition_slot_schema_def schema_variables_def
          replay_slot_reading_call replay_slot_reading_components\<close>)
  show ?thesis using result by (simp add: replay_definition_slot_schema_def)
qed

lemma replay_application_slot_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)" and read:
    "(58,application_reading_argument e au ar d t i slots)\<in>positive_meaning application_reading_system"
    "(5,Pair_Term k (Pair_Term slots rest))\<in>positive_meaning bag_comparison_system"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term au k))\<in>positive_meaning replay_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then k else if j=8 then d else if j=9 then t else if j=10 then i else if j=11 then slots else rest"
  have result: "(107,evaluate_pattern ?h (schema_conclusion replay_application_slot_schema))\<in>positive_meaning replay_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]] in
        \<open>auto simp: replay_slot_reading_clauses_def replay_application_slot_schema_def schema_variables_def
          replay_slot_reading_call replay_slot_reading_components\<close>)
  show ?thesis using result by (simp add: replay_application_slot_schema_def)
qed

lemma replay_node_slot_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)" and read:
    "(98,proof_graph_subject_argument e ru rr (Pair_Term u a))\<in>positive_meaning proof_graph_membership_system"
    "(94,term_quotation_argument e u a n i slots)\<in>positive_meaning proof_node_reading_system"
    "(5,Pair_Term k (Pair_Term slots rest))\<in>positive_meaning bag_comparison_system"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k))\<in>positive_meaning replay_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then u else if j=8 then k else if j=9 then a else if j=10 then n else if j=11 then i else if j=12 then slots else rest"
  have result: "(107,evaluate_pattern ?h (schema_conclusion replay_node_slot_schema))\<in>positive_meaning replay_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=3])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(3)]] in
        \<open>auto simp: replay_slot_reading_clauses_def replay_node_slot_schema_def schema_variables_def
          replay_slot_reading_call replay_slot_reading_components\<close>)
  show ?thesis using result by (simp add: replay_node_slot_schema_def)
qed

lemma replay_slot_reading_fields:
  "(107,z)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    (\<exists>e pu pr au ar ru rr u k. z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k) \<and>
      term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_slot_observed e pu pr au ar ru rr u k)"
proof
  assume holds: "(107,z)\<in>positive_meaning replay_slot_reading_system"
  have ordinary: "schema_material_premises S={}" if "((107,c),S)\<in>system_clauses replay_slot_reading_system" for c S
    using that by (auto simp: replay_slot_reading_clauses_def replay_root_slot_schema_def replay_definition_slot_schema_def replay_application_slot_schema_def replay_node_slot_schema_def)
  have valuation: "(107,z)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    (\<exists>c S f. ((107,c),S)\<in>system_clauses replay_slot_reading_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion S) \<and>
      schema_call_formed replay_slot_reading_system 107 z \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning replay_slot_reading_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((107,c),S)\<in>system_clauses replay_slot_reading_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning replay_slot_reading_system"
    using iffD1[OF valuation holds] by blast
  consider (root) "S=replay_root_slot_schema" | (declared) "S=replay_definition_slot_schema" | (application) "S=replay_application_slot_schema" | (node) "S=replay_node_slot_schema"
    using clause by (auto simp: replay_slot_reading_clauses_def)
  then show "\<exists>e pu pr au ar ru rr u k. z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k) \<and>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_slot_observed e pu pr au ar ru rr u k"
  proof cases
    case root
    have formed: "term_formed (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))"
      using assignment by (auto simp: root replay_root_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)) (Pair_Term (h 1) (h 7))"
      using shape by (simp add: root replay_root_slot_schema_def)
    have read_0: "(37,artifact_lookup_argument (h 0) (h 1) (h 8))\<in>positive_meaning artifact_lookup_system"
      using support[rule_format, of 0 37 "artifact_lookup_pattern data_x data_y (Pattern_Variable 8)"]
      by (simp add: root replay_root_slot_schema_def replay_slot_reading_components)
    have read_1: "(32,rooted_rows_argument (h 8) (h 2) (h 9))\<in>positive_meaning family_admission_system"
      using support[rule_format, of 1 32 "Pattern_Pair (Pattern_Pair (Pattern_Variable 8) data_z) (Pattern_Variable 9)"]
      by (simp add: root replay_root_slot_schema_def replay_slot_reading_components)
    have read_2: "(5,Pair_Term (Pair_Term (h 10) (h 11)) (Pair_Term (h 9) (h 12)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 2 5 "Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)) (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12))"]
      by (simp add: root replay_root_slot_schema_def replay_slot_reading_components)
    have read_3: "(42,citation_reading_argument (h 0) (h 1) (h 11) (Pair_Term (h 13) (h 14)) (h 15))\<in>positive_meaning citation_reading_system"
      using support[rule_format, of 3 42 "citation_reading_pattern data_x data_y (Pattern_Variable 11) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14)) (Pattern_Variable 15)"]
      by (simp add: root replay_root_slot_schema_def replay_slot_reading_components)
    have read_4: "(5,Pair_Term (h 7) (Pair_Term (h 13) (h 16)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 4 5 "Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 16))"]
      by (simp add: root replay_root_slot_schema_def replay_slot_reading_components)
    have observed: "replay_slot_observed (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 1) (h 7)"
      using read_0 read_1 read_2 read_3 read_4 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"], rule exI[of _ "h 1"], rule exI[of _ "h 7"])
        (use encoded formed observed in blast)
  next
    case declared
    have formed: "term_formed (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))"
      using assignment by (auto simp: declared replay_definition_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)) (Pair_Term (h 7) (h 8))"
      using shape by (simp add: declared replay_definition_slot_schema_def)
    have read_0: "(83,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 7) (h 9)))\<in>positive_meaning package_membership_system"
      using support[rule_format, of 0 83 "package_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 9))"]
      by (simp add: declared replay_definition_slot_schema_def replay_slot_reading_components)
    have read_1: "(105,citation_observation_argument (h 0) (h 7) (h 9) (h 8))\<in>positive_meaning definition_slot_reading_system"
      using support[rule_format, of 1 105 "citation_observation_pattern data_x (Pattern_Variable 7) (Pattern_Variable 9) (Pattern_Variable 8)"]
      by (simp add: declared replay_definition_slot_schema_def replay_slot_reading_components)
    have observed: "replay_slot_observed (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8)"
      using read_0 read_1 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"], rule exI[of _ "h 7"], rule exI[of _ "h 8"])
        (use encoded formed observed in blast)
  next
    case application
    have formed: "term_formed (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))"
      using assignment by (auto simp: application replay_application_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)) (Pair_Term (h 3) (h 7))"
      using shape by (simp add: application replay_application_slot_schema_def)
    have read_0: "(58,application_reading_argument (h 0) (h 3) (h 4) (h 8) (h 9) (h 10) (h 11))\<in>positive_meaning application_reading_system"
      using support[rule_format, of 0 58 "application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)"]
      by (simp add: application replay_application_slot_schema_def replay_slot_reading_components)
    have read_1: "(5,Pair_Term (h 7) (Pair_Term (h 11) (h 12)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 1 5 "Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12))"]
      by (simp add: application replay_application_slot_schema_def replay_slot_reading_components)
    have observed: "replay_slot_observed (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 3) (h 7)"
      using read_0 read_1 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"], rule exI[of _ "h 3"], rule exI[of _ "h 7"])
        (use encoded formed observed in blast)
  next
    case node
    have formed: "term_formed (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))"
      using assignment by (auto simp: node replay_node_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (replay_context_term (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)) (Pair_Term (h 7) (h 8))"
      using shape by (simp add: node replay_node_slot_schema_def)
    have read_0: "(98,proof_graph_subject_argument (h 0) (h 5) (h 6) (Pair_Term (h 7) (h 9)))\<in>positive_meaning proof_graph_membership_system"
      using support[rule_format, of 0 98 "proof_graph_subject_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 9))"]
      by (simp add: node replay_node_slot_schema_def replay_slot_reading_components)
    have read_1: "(94,term_quotation_argument (h 0) (h 7) (h 9) (h 10) (h 11) (h 12))\<in>positive_meaning proof_node_reading_system"
      using support[rule_format, of 1 94 "term_quotation_pattern data_x (Pattern_Variable 7) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)"]
      by (simp add: node replay_node_slot_schema_def replay_slot_reading_components)
    have read_2: "(5,Pair_Term (h 8) (Pair_Term (h 12) (h 13)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 2 5 "Pattern_Pair (Pattern_Variable 8) (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13))"]
      by (simp add: node replay_node_slot_schema_def replay_slot_reading_components)
    have observed: "replay_slot_observed (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8)"
      using read_0 read_1 read_2 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"], rule exI[of _ "h 7"], rule exI[of _ "h 8"])
        (use encoded formed observed in blast)
  qed
next
  assume "\<exists>e pu pr au ar ru rr u k. z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k) \<and>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_slot_observed e pu pr au ar ru rr u k"
  then show "(107,z)\<in>positive_meaning replay_slot_reading_system"
    by (auto intro: replay_root_slot_step replay_definition_slot_step replay_application_slot_step replay_node_slot_step)
qed

lemma replay_root_slot_at_source:
  assumes source: "environment_value_presents E e"
  shows "replay_root_slot_observed e pu pr x \<longleftrightarrow>
    (\<exists>u r k. pu=use_data_term u \<and> pr=Payload_Term r \<and> x=Payload_Term k \<and>
      (u,k)\<in>requested_slots E (native_root_requests E u r))"
proof
  assume "replay_root_slot_observed e pu pr x"
  then obtain a rows socket endpoint slots address interior where calls:
    "(37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system"
    "(32,rooted_rows_argument a pr rows)\<in>positive_meaning family_admission_system"
    "selected_data_member (Pair_Term socket endpoint) rows"
    "(42,citation_reading_argument e pu endpoint (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system"
    "selected_data_member x slots" by blast
  obtain u R where lookup: "pu=use_data_term u" "artifact_at E u R" "artifact_value_presents R a"
    using calls(1) by (auto simp: artifact_lookup_at_source[OF source])
  obtain r where address: "pr=Payload_Term r"
    using calls(2) by (auto simp: family_admission_at_source[OF lookup(3)])
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have family_read: "\<exists>rows socket.
    (32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system \<and>
      selected_data_member (Pair_Term socket endpoint) rows"
    using calls(2)[unfolded address] calls(3) by blast
  obtain q where endpoint: "endpoint=Payload_Term q" "q\<in>family_endpoints E u r"
    using iffD1[OF family_endpoint_observation[OF ef lookup(2,3)] family_read] by blast
  have citation: "\<exists>slots address interior.
    (42,citation_reading_argument e (use_data_term u) (Payload_Term q) (Pair_Term slots address) interior)
      \<in>positive_meaning citation_reading_system \<and> selected_data_member x slots"
    using calls(4)[unfolded lookup(1) endpoint(1)] calls(5) by blast
  obtain k S c I where raw: "x=Payload_Term k" "artifact_at E u S" "citation_at S q c I" "k\<in>citation_slots c"
    using citation by (simp only: citation_slot_observation[OF source]) blast
  have request: "\<exists>q R c I. (u,q)\<in>native_root_requests E u r \<and> artifact_at E u R \<and>
    citation_at R q c I \<and> k\<in>citation_slots c"
    by (rule exI[of _ q], rule exI[of _ S], rule exI[of _ c], rule exI[of _ I])
      (use endpoint(2) raw(2-4) in \<open>simp add: native_root_requests_def\<close>)
  have demand: "(u,k)\<in>requested_slots E (native_root_requests E u r)"
    using request by (simp add: requested_slots_def)
  show "\<exists>u r k. pu=use_data_term u \<and> pr=Payload_Term r \<and> x=Payload_Term k \<and>
    (u,k)\<in>requested_slots E (native_root_requests E u r)"
    by (rule exI[of _ u], rule exI[of _ r], rule exI[of _ k]) (use lookup(1) address raw(1) demand in blast)
next
  assume "\<exists>u r k. pu=use_data_term u \<and> pr=Payload_Term r \<and> x=Payload_Term k \<and>
    (u,k)\<in>requested_slots E (native_root_requests E u r)"
  then obtain u r k q S c I where fields: "pu=use_data_term u" "pr=Payload_Term r" "x=Payload_Term k"
    and raw: "q\<in>family_endpoints E u r" "artifact_at E u S" "citation_at S q c I" "k\<in>citation_slots c"
    by (auto simp: requested_slots_def native_root_requests_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain R M where family: "artifact_at E u R" "family_at R r M" using raw(1) by (auto simp: family_endpoints_def)
  have rf: "exact_formed R" using ef family(1) by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using family(1) presented by (auto simp: artifact_lookup_at_source[OF source])
  have endpoint_read: "\<exists>rows socket.
    (32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system \<and>
      selected_data_member (Pair_Term socket (Payload_Term q)) rows"
    by (rule iffD2[OF family_endpoint_observation[OF ef family(1) presented]]) (use raw(1) in auto)
  obtain rows socket where family_read: "(32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system"
    "selected_data_member (Pair_Term socket (Payload_Term q)) rows" using endpoint_read by blast
  have citation_read: "\<exists>slots address interior.
    (42,citation_reading_argument e (use_data_term u) (Payload_Term q) (Pair_Term slots address) interior)
      \<in>positive_meaning citation_reading_system \<and> selected_data_member x slots"
    by (rule iffD2[OF citation_slot_observation[OF source]]) (use fields(3) raw(2-4) in blast)
  obtain slots address interior where citation:
    "(42,citation_reading_argument e (use_data_term u) (Payload_Term q) (Pair_Term slots address) interior)
      \<in>positive_meaning citation_reading_system" "selected_data_member x slots" using citation_read by blast
  show "replay_root_slot_observed e pu pr x" using lookup family_read citation by (simp only: fields; blast)
qed

lemma replay_slot_observed_environment:
  assumes "replay_slot_observed e pu pr au ar ru rr u k"
  shows "\<exists>E. environment_value_presents E e"
  using assms by (auto simp: artifact_lookup_exact package_membership_exact application_reading_exact proof_graph_membership_exact)

lemma replay_slot_observed_at_source:
  assumes source: "environment_value_presents E e"
  shows "replay_slot_observed e pu pr au ar ru rr u k \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and> replay_slot_candidates E pu pr au ar ru rr v a)"
proof -
  have grouped:
    "(\<exists>a n i slots. (98,proof_graph_subject_argument e ru rr (Pair_Term u a))\<in>positive_meaning proof_graph_membership_system \<and>
      (94,term_quotation_argument e u a n i slots)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member k slots)
    \<longleftrightarrow> (\<exists>a. (98,proof_graph_subject_argument e ru rr (Pair_Term u a))\<in>positive_meaning proof_graph_membership_system \<and>
      (\<exists>n i slots. (94,term_quotation_argument e u a n i slots)\<in>positive_meaning proof_node_reading_system \<and>
        selected_data_member k slots))" by blast
  have graph_slots:
    "(\<exists>a n i slots. (98,proof_graph_subject_argument e ru rr (Pair_Term u a))\<in>positive_meaning proof_graph_membership_system \<and>
      (94,term_quotation_argument e u a n i slots)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member k slots)
    \<longleftrightarrow> (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>w r b G N D I K. ru=use_data_term w \<and> rr=Payload_Term r \<and> native_schema_graph_at E (w,r) G \<and>
        (v,b)\<in>schema_graph_nodes G \<and> native_proof_node_at E v b N D I K \<and> a\<in>K))"
    by (simp only: grouped)
      (simp only: proof_slot_observation_fields[OF source] proof_graph_membership_at_source[OF source]
        site_data_term_def factor_term.inject; auto simp: inj_eq[OF use_data_term_injective]; blast)
  have root_slots:
    "(u=pu \<and> replay_root_slot_observed e pu pr k) \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>w r. pu=use_data_term w \<and> pr=Payload_Term r \<and> v=w \<and>
        (v,a)\<in>requested_slots E (native_root_requests E w r)))"
    by (simp only: replay_root_slot_at_source[OF source]) blast
  have definition_slots:
    "(\<exists>b. (83,package_subject_argument e pu pr (Pair_Term u b))\<in>positive_meaning package_membership_system \<and>
      (105,citation_observation_argument e u b k)\<in>positive_meaning definition_slot_reading_system) \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>w r b P. pu=use_data_term w \<and> pr=Payload_Term r \<and> native_package_at E w r P \<and>
        (v,b)\<in>system_definitions P \<and> a\<in>native_definition_slots E v b))"
    by (simp only: package_membership_at_source[OF source] definition_slot_reading_at_source[OF source]
      site_data_term_def factor_term.inject; auto simp: inj_eq[OF use_data_term_injective]; blast)
  have application_slots:
    "(u=au \<and> (\<exists>d t i slots. (58,application_reading_argument e au ar d t i slots)\<in>positive_meaning application_reading_system \<and>
      selected_data_member k slots)) \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>r d t I K. au=use_data_term v \<and> ar=Payload_Term r \<and> native_application_at E v r d t I K \<and> a\<in>K))"
    by (simp only: application_slot_observation_fields[OF source]) blast
  show ?thesis
    by (simp only: root_slots definition_slots application_slots graph_slots conj_disj_distribL ex_disj_distrib)

qed

theorem replay_slot_reading_exact:
  "(107,z)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow> replay_slot_reading_result z"
proof
  assume holds: "(107,z)\<in>positive_meaning replay_slot_reading_system"
  obtain e pu pr au ar ru rr u k where parts:
    "z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term u k)"
    "term_formed (replay_context_term e pu pr au ar ru rr)" "replay_slot_observed e pu pr au ar ru rr u k"
    using holds[unfolded replay_slot_reading_fields] by (elim exE conjE) (rule that; assumption)
  obtain E where source: "environment_value_presents E e" using replay_slot_observed_environment[OF parts(3)] by blast
  obtain v a where selected_value: "u=use_data_term v" "k=Payload_Term a" "replay_slot_candidates E pu pr au ar ru rr v a"
    using parts(3)[unfolded replay_slot_observed_at_source[OF source]]
    by (elim exE conjE) (rule that; assumption)
  show "replay_slot_reading_result z"
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ au],
      rule exI[of _ ar], rule exI[of _ ru], rule exI[of _ rr], rule exI[of _ v], rule exI[of _ a])
      (use parts(1,2) source selected_value in auto)
next
  assume "replay_slot_reading_result z"
  then obtain E e pu pr au ar ru rr u k where parts:
    "z=Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term (use_data_term u) (Payload_Term k))"
    "environment_value_presents E e" "term_formed (replay_context_term e pu pr au ar ru rr)"
    "replay_slot_candidates E pu pr au ar ru rr u k"
    by (elim exE conjE) (rule that; assumption)
  have observed: "replay_slot_observed e pu pr au ar ru rr (use_data_term u) (Payload_Term k)"
    by (simp only: replay_slot_observed_at_source[OF parts(2)], rule exI[of _ u], rule exI[of _ k])
      (use parts(4) in simp)
  show "(107,z)\<in>positive_meaning replay_slot_reading_system"
    by (simp only: replay_slot_reading_fields, rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr],
      rule exI[of _ au], rule exI[of _ ar], rule exI[of _ ru], rule exI[of _ rr],
      rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term k"])
      (use parts(1,3) observed in blast)
qed

corollary replay_slot_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and>
    (\<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and> replay_slot_candidates E pu pr au ar ru rr u k)"
proof -
  have fields: "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and>
      (\<exists>u k. x=Pair_Term u k \<and> replay_slot_observed e pu pr au ar ru rr u k)"
  proof
    assume checked: "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system"
    obtain f qu qr bu br nu nr u k where parts:
      "Pair_Term (replay_context_term e pu pr au ar ru rr) x=Pair_Term (replay_context_term f qu qr bu br nu nr) (Pair_Term u k)"
      "term_formed (replay_context_term f qu qr bu br nu nr)" "replay_slot_observed f qu qr bu br nu nr u k"
      using checked[unfolded replay_slot_reading_fields] by (elim exE conjE) (rule that; assumption)
    have same: "f=e" "qu=pu" "qr=pr" "bu=au" "br=ar" "nu=ru" "nr=rr" using parts(1) by auto
    have encoded: "x=Pair_Term u k" using parts(1) by simp
    have formed: "term_formed (replay_context_term e pu pr au ar ru rr)" using parts(2) by (simp only: same)
    have observed: "replay_slot_observed e pu pr au ar ru rr u k" using parts(3) by (simp only: same)
    show "term_formed (replay_context_term e pu pr au ar ru rr) \<and>
      (\<exists>u k. x=Pair_Term u k \<and> replay_slot_observed e pu pr au ar ru rr u k)"
    proof (rule conjI)
      show "term_formed (replay_context_term e pu pr au ar ru rr)" by (rule formed)
      show "\<exists>u k. x=Pair_Term u k \<and> replay_slot_observed e pu pr au ar ru rr u k"
        by (rule exI[of _ u], rule exI[of _ k]) (use encoded observed in blast)
    qed
  next
    assume "term_formed (replay_context_term e pu pr au ar ru rr) \<and>
      (\<exists>u k. x=Pair_Term u k \<and> replay_slot_observed e pu pr au ar ru rr u k)"
    then obtain u k where parts: "term_formed (replay_context_term e pu pr au ar ru rr)"
      "x=Pair_Term u k" "replay_slot_observed e pu pr au ar ru rr u k"
      by (elim conjE exE) (rule that; assumption)
    show "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system"
      by (simp only: replay_slot_reading_fields, rule exI[of _ e], rule exI[of _ pu], rule exI[of _ pr],
        rule exI[of _ au], rule exI[of _ ar], rule exI[of _ ru], rule exI[of _ rr], rule exI[of _ u], rule exI[of _ k])
        (use parts in auto)
  qed
  have encoding: "(\<exists>u k. x=Pair_Term u k \<and>
      (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and> P v a)) \<longleftrightarrow>
    (\<exists>v a. x=Pair_Term (use_data_term v) (Payload_Term a) \<and> P v a)"
    for P :: "local_address option \<Rightarrow> local_address \<Rightarrow> bool"
    by blast
  show ?thesis by (simp only: fields replay_slot_observed_at_source[OF source] encoding)
qed

lemma replay_slot_candidates_at_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E (ru,rr) G"
  shows "replay_slot_candidates E (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)
    (use_data_term ru) (Payload_Term rr) u k \<longleftrightarrow> (u,k)\<in>native_replay_demands E pu pr au ar G"
proof -
  have package_slots: "(\<exists>Q. native_package_at E pu pr Q \<and> (u,a)\<in>system_definitions Q \<and>
      k\<in>native_definition_slots E u a) \<longleftrightarrow>
    (u,a)\<in>system_definitions P \<and> k\<in>native_definition_slots E u a" for a
    using package native_package_unique[OF _ package] by blast
  have node_slots:
    "(\<exists>X N D J L. native_schema_graph_at E (ru,rr) X \<and> (u,a)\<in>schema_graph_nodes X \<and>
      native_proof_node_at E u a N D J L \<and> k\<in>L) \<longleftrightarrow>
    (\<exists>N D J L. (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D J L \<and> k\<in>L)" for a
    using graph native_schema_graph_unique[OF _ graph] by blast
  have normalized_nodes:
    "(\<exists>X. native_schema_graph_at E (ru,rr) X \<and> (u,a)\<in>schema_graph_nodes X \<and>
      (\<exists>N D J L. native_proof_node_at E u a N D J L \<and> k\<in>L)) \<longleftrightarrow>
    (u,a)\<in>schema_graph_nodes G \<and> (\<exists>N D J L. native_proof_node_at E u a N D J L \<and> k\<in>L)" for a
    using graph native_schema_graph_unique[OF _ graph] by blast
  have app_slots: "(\<exists>f s J L. native_application_at E au ar f s J L \<and> k\<in>L) \<longleftrightarrow> k\<in>K"
    using app native_application_unique[OF _ app] by blast
  have applications:
    "(\<exists>r f s J L. use_data_term au=use_data_term u \<and> Payload_Term ar=Payload_Term r \<and>
      native_application_at E u r f s J L \<and> k\<in>L) \<longleftrightarrow> u=au \<and> k\<in>K"
  proof (cases "u=au")
    case True
    then show ?thesis using app_slots by auto
  next
    case False
    then show ?thesis by (simp add: inj_eq[OF use_data_term_injective] eq_commute)
  qed
  have root_owner: "(u,k)\<in>requested_slots E (native_root_requests E pu pr) \<Longrightarrow> u=pu"
    by (auto simp: requested_slots_def native_root_requests_def)
  have roots:
    "(\<exists>v r. use_data_term pu=use_data_term v \<and> Payload_Term pr=Payload_Term r \<and> u=v \<and>
      (u,k)\<in>requested_slots E (native_root_requests E v r)) \<longleftrightarrow>
    (u,k)\<in>requested_slots E (native_root_requests E pu pr)"
    by (simp add: inj_eq[OF use_data_term_injective]) (use root_owner in blast)
  have demands: "(u,k)\<in>native_replay_demands E pu pr au ar G \<longleftrightarrow>
    (u,k)\<in>requested_slots E (native_root_requests E pu pr) \<or>
    (\<exists>a. (u,a)\<in>system_definitions P \<and> k\<in>native_definition_slots E u a) \<or>
    (u=au \<and> k\<in>K) \<or>
    (\<exists>a N D J L. (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D J L \<and> k\<in>L)"
    by (auto simp: native_replay_demands_def native_package_demands_def
      native_package_projection(3)[OF package, symmetric] native_application_demands_at[OF app]
      native_graph_demands_at_nodes[OF graph])
  show ?thesis by (simp only: roots applications demands)
    (simp add: inj_eq[OF use_data_term_injective] package_slots node_slots normalized_nodes disj_assoc)

qed

corollary replay_slot_reading_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(107,Pair_Term (replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au)
    (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) x)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    (\<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and> (u,k)\<in>native_replay_demands E pu pr au ar G)"
  by (simp only: replay_slot_reading_at_source[OF source] replay_context_formed[OF source package app graph]
    replay_slot_candidates_at_reads[OF package app graph]; simp)

corollary replay_slot_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(107,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system \<longleftrightarrow>
    (107,Pair_Term (replay_context_term f pu pr au ar ru rr) x)\<in>positive_meaning replay_slot_reading_system"
  using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)]
  by (simp only: replay_slot_reading_at_source[OF assms(1)] replay_slot_reading_at_source[OF assms(2)]) auto

text \<open>
  The four branches select root-family citation slots, reached-definition
  slots, actual application slots, or actual graph-node slots. Their exact
  output is an owning use and local slot. The actual package, application,
  and graph fix the complete demand set used by retention.

  The helper retains the partial role boundary of its selected branch.
  Complete context admission belongs to the enclosing retention entry.
  Structural recognition and slot coverage require neither derivation
  validity nor the truth of any selected call.
\<close>

end
