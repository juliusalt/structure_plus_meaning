theory Factor_Replay_Source_Reading
  imports Factor_Definition_Slot_Reading Factor_Retention_Observations
begin

section \<open>One stored use has an actual structural or binding source\<close>

abbreviation replay_source_candidates where
  "replay_source_candidates E pu pr au ru rr v \<equiv>
    (((pu=use_data_term v \<or> au=use_data_term v) \<and> (\<exists>R. artifact_at E v R)) \<or>
     (\<exists>u r a P. pu=use_data_term u \<and> pr=Payload_Term r \<and>
       native_package_at E u r P \<and> (v,a)\<in>system_definitions P) \<or>
     (\<exists>u r a G. ru=use_data_term u \<and> rr=Payload_Term r \<and>
       native_schema_graph_at E (u,r) G \<and> (v,a)\<in>schema_graph_nodes G) \<or>
     v\<in>rel_ran (environment_bindings E))"

abbreviation replay_source_reading_result :: "factor_term \<Rightarrow> bool" where
  "replay_source_reading_result z \<equiv> \<exists>E e pu pr au ar ru rr v.
    z=Pair_Term (replay_context_term e pu pr au ar ru rr) (use_data_term v) \<and>
    environment_value_presents E e \<and> term_formed (replay_context_term e pu pr au ar ru rr) \<and>
    replay_source_candidates E pu pr au ru rr v"

abbreviation replay_source_observed where
  "replay_source_observed e pu pr au ru rr x \<equiv>
    (x=pu \<and> (\<exists>a. (37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system)) \<or>
    (x=au \<and> (\<exists>a. (37,artifact_lookup_argument e au a)\<in>positive_meaning artifact_lookup_system)) \<or>
    (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term x a))\<in>positive_meaning package_membership_system) \<or>
    (\<exists>a. (98,proof_graph_subject_argument e ru rr (Pair_Term x a))\<in>positive_meaning proof_graph_membership_system) \<or>
    (\<exists>u k. (38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system)"

definition replay_package_source_schema :: "(nat,nat,nat) factor_schema" where
  "replay_package_source_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) data_y)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 7))}"

definition replay_application_source_schema :: "(nat,nat,nat) factor_schema" where
  "replay_application_source_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) data_w)
    {(0,37,artifact_lookup_pattern data_x data_w (Pattern_Variable 7))}"

definition replay_definition_source_schema :: "(nat,nat,nat) factor_schema" where
  "replay_definition_source_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7))
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))}"

definition replay_node_source_schema :: "(nat,nat,nat) factor_schema" where
  "replay_node_source_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7))
    {(0,98,proof_graph_subject_pattern data_x (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))}"

definition replay_binding_target_schema :: "(nat,nat,nat) factor_schema" where
  "replay_binding_target_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7))
    {(0,38,binding_lookup_pattern data_x (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 7))}"

definition replay_source_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "replay_source_reading_clauses={(0,replay_package_source_schema),(1,replay_application_source_schema),(2,replay_definition_source_schema),(3,replay_node_source_schema),(4,replay_binding_target_schema)}"

definition replay_source_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_source_reading_system=add_view_definition definition_slot_reading_system 106 data_x replay_source_reading_clauses"

lemma replay_source_reading_system_formed [simp]: "schema_system_formed replay_source_reading_system"
  unfolding replay_source_reading_system_def
  by (rule add_recursive_definition_formed[OF definition_slot_reading_system_formed])
    (auto simp: replay_source_reading_clauses_def replay_package_source_schema_def replay_application_source_schema_def replay_definition_source_schema_def replay_node_source_schema_def replay_binding_target_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma replay_source_reading_definitions [simp]:
  "system_definitions replay_source_reading_system=insert 106 (system_definitions definition_slot_reading_system)"
  by (simp add: replay_source_reading_system_def)

lemma replay_source_reading_call:
  "schema_call_formed replay_source_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_source_reading_system \<and> term_formed t"
  using added_variable_calls[OF definition_slot_reading_system_formed
    replay_source_reading_system_formed[unfolded replay_source_reading_system_def] definition_slot_reading_call]
  by (simp only: replay_source_reading_system_def[symmetric])

lemma replay_source_reading_old_meaning:
  assumes "d\<in>system_definitions definition_slot_reading_system"
  shows "(d,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_slot_reading_system"
  using added_definition_preserves_old(2)[OF definition_slot_reading_system_formed
    replay_source_reading_system_formed[unfolded replay_source_reading_system_def], of d t] assms
  by (auto simp: replay_source_reading_system_def)

lemma replay_source_reading_clause [simp]:
  "((106,c),S)\<in>system_clauses replay_source_reading_system \<longleftrightarrow> (c,S)\<in>replay_source_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_slot_reading_system \<Longrightarrow>
    d\<in>system_definitions definition_slot_reading_system" for d c S
    using definition_slot_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((106,c),S)\<notin>system_clauses definition_slot_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: replay_source_reading_system_def)
qed

lemma replay_source_reading_graph_meaning:
  assumes "d\<in>system_definitions proof_graph_membership_system"
  shows "(d,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning proof_graph_membership_system"
  using replay_source_reading_old_meaning[of d t] definition_slot_reading_old_meaning[of d t]
    schema_slot_reading_old_meaning[of d t] premise_slot_reading_old_meaning[of d t]
    derivation_admission_old_meaning[of d t] proof_claim_checking_graph_meaning[OF assms, of t] assms by auto

lemma replay_source_reading_material_meaning:
  assumes "d\<in>system_definitions material_instantiation_system"
  shows "(d,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning material_instantiation_system"
  using replay_source_reading_old_meaning[of d t] definition_slot_reading_old_meaning[of d t]
    schema_slot_reading_old_meaning[of d t] premise_slot_reading_material_meaning[OF assms, of t] assms by auto

lemma replay_source_reading_components:
  "(37,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(83,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(98,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> (98,t)\<in>positive_meaning proof_graph_membership_system"
  "(38,t)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> (38,t)\<in>positive_meaning binding_lookup_system"
  using replay_source_reading_old_meaning[of 37 t] definition_slot_reading_components(1)[of t]
    replay_source_reading_graph_meaning[of 83 t] proof_graph_membership_node_meaning[of 83 t]
    proof_node_reading_base_meaning[of 83 t] admitted_instantiation_old_meaning[of 83 t]
    program_call_list_old_meaning[of 83 t] application_admission_old_meaning[of 83 t] program_call_admission_old_meaning[of 83 t]
    replay_source_reading_graph_meaning[of 98 t]
    replay_source_reading_material_meaning[of 38 t] material_instantiation_old_meaning[of 38 t]
    record_instantiation_old_meaning[of 38 t] vector_instantiation_pattern_meaning[of 38 t]
    pattern_instantiation_quotation_meaning[of 38 t] quotation_admission_reading_meaning[of 38 t]
    citation_reading_old_meaning[of 38 t] citation_location_old_meaning[of 38 t]
    citation_interpretation_old_meaning[of 38 t] citation_resolution_old_meaning[of 38 t] by auto

lemma replay_package_source_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)"
    and read: "(37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) pu)\<in>positive_meaning replay_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else a"
  have result: "(106,evaluate_pattern ?h (schema_conclusion replay_package_source_schema))\<in>positive_meaning replay_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: replay_source_reading_clauses_def replay_package_source_schema_def schema_variables_def
          replay_source_reading_call replay_source_reading_components\<close>)
  show ?thesis using result by (simp add: replay_package_source_schema_def)
qed

lemma replay_application_source_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)"
    and read: "(37,artifact_lookup_argument e au a)\<in>positive_meaning artifact_lookup_system"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) au)\<in>positive_meaning replay_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else a"
  have result: "(106,evaluate_pattern ?h (schema_conclusion replay_application_source_schema))\<in>positive_meaning replay_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: replay_source_reading_clauses_def replay_application_source_schema_def schema_variables_def
          replay_source_reading_call replay_source_reading_components\<close>)
  show ?thesis using result by (simp add: replay_application_source_schema_def)
qed

lemma replay_definition_source_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)"
    and read: "(83,package_subject_argument e pu pr (Pair_Term v a))\<in>positive_meaning package_membership_system"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) v)\<in>positive_meaning replay_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then v else a"
  have result: "(106,evaluate_pattern ?h (schema_conclusion replay_definition_source_schema))\<in>positive_meaning replay_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: replay_source_reading_clauses_def replay_definition_source_schema_def schema_variables_def
          replay_source_reading_call replay_source_reading_components\<close>)
  show ?thesis using result by (simp add: replay_definition_source_schema_def)
qed

lemma replay_node_source_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)"
    and read: "(98,proof_graph_subject_argument e ru rr (Pair_Term v a))\<in>positive_meaning proof_graph_membership_system"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) v)\<in>positive_meaning replay_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then v else a"
  have result: "(106,evaluate_pattern ?h (schema_conclusion replay_node_source_schema))\<in>positive_meaning replay_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=3])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: replay_source_reading_clauses_def replay_node_source_schema_def schema_variables_def
          replay_source_reading_call replay_source_reading_components\<close>)
  show ?thesis using result by (simp add: replay_node_source_schema_def)
qed

lemma replay_binding_target_step:
  assumes formed: "term_formed (replay_context_term e pu pr au ar ru rr)"
    and read: "(38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) v)\<in>positive_meaning replay_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then v else if j=8 then u else k"
  have result: "(106,evaluate_pattern ?h (schema_conclusion replay_binding_target_schema))\<in>positive_meaning replay_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=4])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: replay_source_reading_clauses_def replay_binding_target_schema_def schema_variables_def
          replay_source_reading_call replay_source_reading_components\<close>)
  show ?thesis using result by (simp add: replay_binding_target_schema_def)
qed

lemma replay_source_reading_fields:
  "(106,z)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (\<exists>e pu pr au ar ru rr x. z=Pair_Term (replay_context_term e pu pr au ar ru rr) x \<and>
      term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_source_observed e pu pr au ru rr x)"
proof
  assume holds: "(106,z)\<in>positive_meaning replay_source_reading_system"
  have ordinary: "schema_material_premises S={}" if "((106,c),S)\<in>system_clauses replay_source_reading_system" for c S
    using that by (auto simp: replay_source_reading_clauses_def replay_package_source_schema_def replay_application_source_schema_def replay_definition_source_schema_def replay_node_source_schema_def replay_binding_target_schema_def)
  have valuation: "(106,z)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (\<exists>c S f. ((106,c),S)\<in>system_clauses replay_source_reading_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion S) \<and>
      schema_call_formed replay_source_reading_system 106 z \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning replay_source_reading_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((106,c),S)\<in>system_clauses replay_source_reading_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning replay_source_reading_system"
    using iffD1[OF valuation holds] by blast
  show "\<exists>e pu pr au ar ru rr x. z=Pair_Term (replay_context_term e pu pr au ar ru rr) x \<and>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_source_observed e pu pr au ru rr x"
    using clause assignment shape support by (auto simp: replay_source_reading_clauses_def
      replay_package_source_schema_def replay_application_source_schema_def replay_definition_source_schema_def replay_node_source_schema_def replay_binding_target_schema_def
      schema_variables_def replay_source_reading_components)
next
  assume "\<exists>e pu pr au ar ru rr x. z=Pair_Term (replay_context_term e pu pr au ar ru rr) x \<and>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_source_observed e pu pr au ru rr x"
  then show "(106,z)\<in>positive_meaning replay_source_reading_system"
    by (auto intro: replay_package_source_step replay_application_source_step replay_definition_source_step replay_node_source_step replay_binding_target_step)
qed

lemma replay_source_observed_environment:
  assumes "replay_source_observed e pu pr au ru rr x"
  shows "\<exists>E. environment_value_presents E e"
  using assms by (auto simp: artifact_lookup_exact package_membership_exact proof_graph_membership_exact binding_lookup_exact)

lemma replay_source_observed_at_source:
  assumes source: "environment_value_presents E e"
  shows "replay_source_observed e pu pr au ru rr x \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> replay_source_candidates E pu pr au ru rr v)"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have material: "\<exists>a. artifact_value_presents R a" if "artifact_at E u R" for u R
    by (rule artifact_value_presents_total) (use ef that in \<open>auto simp: environment_formed_def\<close>)
  have lookup: "(\<exists>a. (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system) \<longleftrightarrow>
    (\<exists>v R. u=use_data_term v \<and> artifact_at E v R)" for u
    by (simp only: artifact_lookup_at_source[OF source]) (use material in blast)
  show ?thesis
    by (simp only: lookup package_membership_at_source[OF source] proof_graph_membership_at_source[OF source]
      binding_lookup_at_source[OF source] site_data_term_def factor_term.inject)
      (auto simp: rel_ran_def binds_slot_def)
qed

theorem replay_source_reading_exact:
  "(106,z)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow> replay_source_reading_result z"
proof
  assume holds: "(106,z)\<in>positive_meaning replay_source_reading_system"
  obtain e pu pr au ar ru rr x where parts: "z=Pair_Term (replay_context_term e pu pr au ar ru rr) x"
    "term_formed (replay_context_term e pu pr au ar ru rr)" "replay_source_observed e pu pr au ru rr x"
    using holds by (simp only: replay_source_reading_fields) blast
  obtain E where source: "environment_value_presents E e" using replay_source_observed_environment[OF parts(3)] by blast
  obtain v where selected_value: "x=use_data_term v" "replay_source_candidates E pu pr au ru rr v"
    using parts(3) by (simp only: replay_source_observed_at_source[OF source]) blast
  show "replay_source_reading_result z" using parts(1,2) source selected_value by blast
next
  assume "replay_source_reading_result z"
  then obtain E e pu pr au ar ru rr v where parts:
    "z=Pair_Term (replay_context_term e pu pr au ar ru rr) (use_data_term v)"
    "environment_value_presents E e" "term_formed (replay_context_term e pu pr au ar ru rr)"
    "replay_source_candidates E pu pr au ru rr v" by blast
  have observed: "replay_source_observed e pu pr au ru rr (use_data_term v)"
    by (simp only: replay_source_observed_at_source[OF parts(2)]) (use parts(4) in blast)
  show "(106,z)\<in>positive_meaning replay_source_reading_system"
    by (simp only: replay_source_reading_fields) (use parts(1,3) observed in blast)
qed

corollary replay_source_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and>
      (\<exists>v. x=use_data_term v \<and> replay_source_candidates E pu pr au ru rr v)"
proof -
  have fields: "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    term_formed (replay_context_term e pu pr au ar ru rr) \<and> replay_source_observed e pu pr au ru rr x"
    by (simp only: replay_source_reading_fields factor_term.inject; blast)
  show ?thesis by (simp only: fields replay_source_observed_at_source[OF source])
qed

lemma replay_source_candidates_at_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E (ru,rr) G"
  shows "replay_source_candidates E (use_data_term pu) (Payload_Term pr) (use_data_term au)
    (use_data_term ru) (Payload_Term rr) v \<longleftrightarrow>
    v\<in>native_replay_sources E pu pr au G\<union>rel_ran (environment_bindings E)"
proof -
  have package_use: "\<exists>R. artifact_at E pu R" using package
    by (auto simp: native_package_at_def native_root_family_at_def)
  have app_use: "\<exists>R. artifact_at E au R" using app by (auto simp: native_application_at_def)
  have definitions: "(\<exists>Q. native_package_at E pu pr Q \<and> (v,a)\<in>system_definitions Q) \<longleftrightarrow>
    (v,a)\<in>system_definitions P" for a
    using package native_package_unique[OF _ package] by blast
  have nodes: "(\<exists>X. native_schema_graph_at E (ru,rr) X \<and> (v,a)\<in>schema_graph_nodes X) \<longleftrightarrow>
    (v,a)\<in>schema_graph_nodes G" for a
    using graph native_schema_graph_unique[OF _ graph] by blast
  have initial: "((pu=v \<or> au=v) \<and> (\<exists>R. artifact_at E v R)) \<longleftrightarrow> (v=pu \<or> v=au)"
    using package_use app_use by auto
  have projection: "v\<in>image fst A \<longleftrightarrow> (\<exists>a. (v,a)\<in>A)" for A
  proof
    assume "v\<in>image fst A"
    then obtain q where row: "q\<in>A" "v=fst q" by blast
    show "\<exists>a. (v,a)\<in>A" by (rule exI[of _ "snd q"]) (use row in auto)
  next
    assume "\<exists>a. (v,a)\<in>A"
    then obtain a where row: "(v,a)\<in>A" by blast
    show "v\<in>image fst A"
    proof (rule image_eqI[where f=fst and x="(v,a)"])
      show "v=fst (v,a)" by simp
      show "(v,a)\<in>A" by (rule row)
    qed
  qed
  have sources: "v\<in>native_replay_sources E pu pr au G \<longleftrightarrow>
    v=pu \<or> v=au \<or> (\<exists>a. (v,a)\<in>system_definitions P) \<or> (\<exists>a. (v,a)\<in>schema_graph_nodes G)"
    by (auto simp: native_replay_sources_def native_package_sources_def native_graph_sources_def
      native_package_projection(3)[OF package, symmetric] projection)
  show ?thesis
    by (simp add: inj_eq[OF use_data_term_injective] definitions nodes initial sources disj_assoc)

qed

corollary replay_source_reading_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(106,Pair_Term (replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au)
    (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) x)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> v\<in>native_replay_sources E pu pr au G\<union>rel_ran (environment_bindings E))"
  by (simp only: replay_source_reading_at_source[OF source] replay_context_formed[OF source package app graph]
    replay_source_candidates_at_reads[OF package app graph]; simp)

corollary replay_source_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(106,Pair_Term (replay_context_term e pu pr au ar ru rr) x)\<in>positive_meaning replay_source_reading_system \<longleftrightarrow>
    (106,Pair_Term (replay_context_term f pu pr au ar ru rr) x)\<in>positive_meaning replay_source_reading_system"
  using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)]
  by (simp only: replay_source_reading_at_source[OF assms(1)] replay_source_reading_at_source[OF assms(2)]) auto

text \<open>
  Five ordinary clauses identify source uses from the two selected sites,
  reached package definitions, reached graph nodes, or actual binding targets.
  A target can retain a whole literal artifact without giving its outgoing
  bindings any role. The complete coverage check separately requires every
  stored binding to be read.

  The helper checks the role used by its selected branch. Other context fields
  are merely formed terms until the enclosing retention entry admits all three
  actual roles. Its contract states that boundary over every input term.
\<close>

end
