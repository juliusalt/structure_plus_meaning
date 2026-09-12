theory Factor_Judgment_Retention_Base
  imports Factor_Package_Slot_Reading Factor_Environment_Inclusion_Contracts
    Factor_Judgment_Retention_Presentations Factor_Recursive_Groups
begin

section \<open>Existing readers retain their complete definitions\<close>

lemma judgment_retention_membership_agreement:
  "systems_agree_on package_membership_system package_slot_reading_system
    (system_definitions package_membership_system)"
  by (simp add: systems_agree_on_added
    package_slot_reading_system_def package_source_reading_system_def scope_forwarding_system_def
    native_positive_admission_system_def positive_query_system_def
    environment_inclusion_system_def artifact_inclusion_system_def replay_admission_system_def
    retention_admission_system_def replay_slot_list_system_def replay_source_list_system_def
    replay_slot_reading_system_def replay_source_reading_system_def definition_slot_reading_system_def
    schema_slot_reading_system_def premise_slot_reading_system_def derivation_admission_system_def
    proof_claim_checking_system_def keyed_row_join_system_def row_qualification_system_def
    proof_graph_membership_system_def proof_graph_admission_system_def proof_bound_checking_system_def
    proof_link_checking_system_def proof_node_reading_system_def discharge_table_reading_system_def
    binding_table_reading_system_def site_link_vector_system_def application_vector_system_def
    site_link_reading_system_def site_citation_reading_system_def admitted_instantiation_system_def
    program_call_list_system_def application_admission_system_def program_call_admission_system_def)

lemma judgment_retention_slot_agreement:
  "systems_agree_on definition_slot_reading_system package_slot_reading_system
    (system_definitions definition_slot_reading_system)"
  by (simp add: systems_agree_on_added
    package_slot_reading_system_def package_source_reading_system_def scope_forwarding_system_def
    native_positive_admission_system_def positive_query_system_def
    environment_inclusion_system_def artifact_inclusion_system_def replay_admission_system_def
    retention_admission_system_def replay_slot_list_system_def replay_source_list_system_def
    replay_slot_reading_system_def replay_source_reading_system_def)

lemma judgment_retention_inclusion_agreement:
  "systems_agree_on environment_inclusion_system package_slot_reading_system
    (system_definitions environment_inclusion_system)"
  by (simp add: systems_agree_on_added
    package_slot_reading_system_def package_source_reading_system_def scope_forwarding_system_def
    native_positive_admission_system_def positive_query_system_def)

lemma judgment_retention_inclusion_meaning:
  assumes "d\<in>system_definitions environment_inclusion_system"
  shows "(d,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_inclusion_system"
proof -
  have closed: "system_dependency_closed environment_inclusion_system (system_definitions environment_inclusion_system)"
    using system_dependency_boundary(1)[OF environment_inclusion_system_formed]
    unfolding system_dependency_closed_def by blast
  show ?thesis using positive_meaning_dependency_locality[OF environment_inclusion_system_formed
    package_slot_reading_system_formed judgment_retention_inclusion_agreement closed assms, of t] by blast
qed

lemma judgment_retention_component_meanings:
  "(5,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(38,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (38,t)\<in>positive_meaning binding_lookup_system"
  "(51,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(58,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(80,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(83,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(113,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  using package_slot_reading_components(3,5)[of t]
    package_slot_reading_old_meaning[of 38 t] package_source_reading_components(3)[of t]
    judgment_retention_inclusion_meaning[of 51 t] environment_inclusion_row_keys_meaning[of 51 t]
    package_slot_reading_replay_meaning[of 58 t] replay_slot_reading_components(7)[of t]
    package_slot_reading_replay_meaning[of 80 t] retention_admission_slot_meaning[of 80 t]
    retention_admission_components(1)[of t] judgment_retention_inclusion_meaning[of 113 t] by auto

section \<open>The actual clauses exclude proof and truth checking\<close>

lemma judgment_retention_slot_dependencies:
  assumes entry: "d\<in>{103,104,105}" and edge: "(d,e)\<in>system_dependency_edges package_slot_reading_system"
  shows "e\<in>system_definitions package_membership_system\<union>{103,104,105}"
proof -
  have member: "d\<in>system_definitions definition_slot_reading_system" using entry by auto
  have original: "(d,e)\<in>system_dependency_edges definition_slot_reading_system"
    using edge systems_agree_on_dependencies[OF judgment_retention_slot_agreement member] by blast
  have premise_family: "((103,c),S)\<in>system_clauses definition_slot_reading_system \<longleftrightarrow>
      (c,S)\<in>premise_slot_reading_clauses" for c S
    by (simp add: definition_slot_reading_system_def schema_slot_reading_system_def)
  have schema_family: "((104,c),S)\<in>system_clauses definition_slot_reading_system \<longleftrightarrow>
      (c,S)\<in>schema_slot_reading_clauses" for c S
    by (simp add: definition_slot_reading_system_def)
  have definition_family: "((105,c),S)\<in>system_clauses definition_slot_reading_system \<longleftrightarrow>
      (c,S)\<in>definition_slot_reading_clauses" for c S by simp
  show ?thesis using entry original
    by (auto simp: system_dependency_edges_def premise_family schema_family definition_family
      premise_slot_reading_clauses_def schema_slot_reading_clauses_def definition_slot_reading_clauses_def
      premise_call_slot_schema_def premise_material_slot_schema_def schema_conclusion_slot_schema_def
      schema_premise_slot_schema_def definition_interface_slot_schema_def definition_schema_slot_schema_def
      schema_dependencies_def rel_ran_image)
qed

lemma judgment_retention_component_boundary:
  "system_dependency_closed package_slot_reading_system
    (system_definitions package_membership_system\<union>{103,104,105,112,113,119})"
proof -
  have original: "system_dependency_closed package_membership_system (system_definitions package_membership_system)"
    using system_dependency_boundary(1)[OF package_membership_system_formed]
    unfolding system_dependency_closed_def by blast
  have package: "system_dependency_closed package_slot_reading_system (system_definitions package_membership_system)"
    by (rule systems_agree_on_closed[OF judgment_retention_membership_agreement original])
  have sub: "system_definitions row_keys_system\<union>{112,113}\<subseteq>system_definitions environment_inclusion_system"
    by auto
  have inclusion_agreement: "systems_agree_on environment_inclusion_system package_slot_reading_system
      (system_definitions row_keys_system\<union>{112,113})"
    by (rule systems_agree_on_subdomain[OF judgment_retention_inclusion_agreement sub])
  have inclusion: "system_dependency_closed package_slot_reading_system
      (system_definitions row_keys_system\<union>{112,113})"
    by (rule systems_agree_on_closed[OF inclusion_agreement environment_inclusion_dependency_boundary])
  have slot: "e\<in>{5,32,37,42,83,105}" if dependency: "(119,e)\<in>system_dependency_edges package_slot_reading_system" for e
  proof -
    obtain c S where clause: "((119,c),S)\<in>system_clauses package_slot_reading_system"
      and needed: "e\<in>schema_dependencies S"
      using dependency by (simp only: system_dependency_edges_def mem_Collect_eq case_prod_conv) blast
    have alternatives: "S=package_root_slot_schema \<or> S=package_definition_slot_schema"
      using clause by (auto simp only: package_slot_reading_clause package_slot_reading_clauses_def)
    have root: "schema_dependencies package_root_slot_schema={37,32,5,42}"
      by (simp add: package_root_slot_schema_def schema_dependencies_def rel_ran_image; auto)
    have definition_slots: "schema_dependencies package_definition_slot_schema={83,105}"
      by (simp add: package_definition_slot_schema_def schema_dependencies_def rel_ran_image)
    from alternatives show ?thesis
    proof
      assume "S=package_root_slot_schema"
      then have "e\<in>{37,32,5,42}" using needed by (simp only: root)
      then show ?thesis by auto
    next
      assume "S=package_definition_slot_schema"
      then have "e\<in>{83,105}" using needed by (simp only: definition_slots)
      then show ?thesis by auto
    qed
  qed
  have needed: "system_definitions row_keys_system\<subseteq>system_definitions package_membership_system"
    "{5,32,37,42,83}\<subseteq>system_definitions package_membership_system" by auto
  show ?thesis unfolding system_dependency_closed_def
  proof (intro ballI allI impI)
    fix d e
    assume member: "d\<in>system_definitions package_membership_system\<union>{103,104,105,112,113,119}"
      and edge: "(d,e)\<in>system_dependency_edges package_slot_reading_system"
    consider (original) "d\<in>system_definitions package_membership_system"
      | (slots) "d\<in>{103,104,105}"
      | (included) "d\<in>{112,113}"
      | (package_slot) "d=119"
      using member by blast
    then show "e\<in>system_definitions package_membership_system\<union>{103,104,105,112,113,119}"
    proof cases
      case original
      have target: "e\<in>system_definitions package_membership_system"
        by (rule package[unfolded system_dependency_closed_def, rule_format, OF original edge])
      show ?thesis by (rule UnI1[OF target])
    next
      case slots
      have target: "e\<in>system_definitions package_membership_system\<union>{103,104,105}"
        by (rule judgment_retention_slot_dependencies[OF slots edge])
      show ?thesis using target by blast
    next
      case included
      have source: "d\<in>system_definitions row_keys_system\<union>{112,113}" using included by blast
      have target: "e\<in>system_definitions row_keys_system\<union>{112,113}"
        by (rule inclusion[unfolded system_dependency_closed_def, rule_format, OF source edge])
      show ?thesis using target needed(1) by blast
    next
      case package_slot
      have dependency: "(119,e)\<in>system_dependency_edges package_slot_reading_system"
        using edge by (simp only: package_slot)
      have target: "e\<in>{5,32,37,42,83,105}" by (rule slot[OF dependency])
      show ?thesis using target needed(2) by blast
    qed
  qed
qed

text \<open>
  The earlier package-slot program contains the required readers. Complete
  definition agreement preserves its package, slot, and inclusion components.
  The closed upper boundary follows their actual clauses and excludes proof
  graphs, derivation, replay, positive truth, and the older broad source query.

  The following group selects the least closure of its actual external
  callees. Historical theory imports are broader than this operative program;
  no imported definition acquires a role merely through that organization.
\<close>

end
