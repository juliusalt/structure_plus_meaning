theory Factor_Environment_Inclusion_Contracts
  imports Factor_Environment_Inclusion Factor_Presentation_Classes
    Presentation_Contracts Factor_System_Composition
begin

section \<open>Complete environment inclusion owns its relation contract\<close>

theorem environment_inclusion_presented:
  "(113,Pair_Term p q)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    presented_relation environment_value_presents environment_value_presents environment_included p q"
  by (auto simp: environment_inclusion_exact presented_relation_def)

interpretation environment_inclusion_contract: presented_relation_contract
  environment_value_presents environment_formed "\<lambda>t. (26,t)\<in>positive_meaning environment_admission_system"
  environment_value_presents environment_formed "\<lambda>t. (26,t)\<in>positive_meaning environment_admission_system"
  environment_included "\<lambda>p q. (113,Pair_Term p q)\<in>positive_meaning environment_inclusion_system"
  by (unfold_locales)
    (use environment_presentations.presentation_class_axioms environment_inclusion_presented
      in \<open>auto simp: presentation_class_def\<close>)

section \<open>The actual inclusion clauses require only data and lookup definitions\<close>

lemma environment_inclusion_located_agreement:
  "systems_agree_on located_admission_system environment_inclusion_system
    (system_definitions located_admission_system)"
  by (simp add: systems_agree_on_added
    environment_inclusion_system_def artifact_inclusion_system_def replay_admission_system_def
    retention_admission_system_def replay_slot_list_system_def replay_source_list_system_def
    replay_slot_reading_system_def replay_source_reading_system_def definition_slot_reading_system_def
    schema_slot_reading_system_def premise_slot_reading_system_def derivation_admission_system_def
    proof_claim_checking_system_def keyed_row_join_system_def row_qualification_system_def
    proof_graph_membership_system_def proof_graph_admission_system_def proof_bound_checking_system_def
    proof_link_checking_system_def proof_node_reading_system_def discharge_table_reading_system_def
    binding_table_reading_system_def site_link_vector_system_def application_vector_system_def
    site_link_reading_system_def site_citation_reading_system_def admitted_instantiation_system_def
    program_call_list_system_def application_admission_system_def program_call_admission_system_def
    package_membership_system_def definition_edge_reading_system_def definition_clause_reading_system_def
    package_admission_system_def root_family_reading_system_def located_list_system_def
    package_closure_admission_system_def definition_callee_list_system_def definition_callee_inclusion_system_def
    schema_callee_list_system_def schema_callee_inclusion_system_def definition_call_admission_system_def
    schema_family_admission_system_def schema_root_list_system_def schema_admission_system_def
    schema_material_checking_system_def material_rows_checking_system_def material_checking_system_def
    schema_instantiation_system_def premise_family_instantiation_system_def premise_rows_system_def
    material_instantiation_system_def record_instantiation_system_def vector_instantiation_system_def
    row_values_system_def application_reading_system_def prospective_instantiation_system_def
    scoped_instantiation_system_def pattern_instantiation_system_def binder_admission_system_def
    diagonal_rows_system_def binding_admission_system_def row_keys_system_def
    quotation_admission_system_def payload_disjoint_system_def data_union_system_def
    data_subset_system_def data_append_system_def target_projection_system_def)

lemma environment_inclusion_row_keys_agreement:
  "systems_agree_on row_keys_system environment_inclusion_system (system_definitions row_keys_system)"
  by (simp add: systems_agree_on_added
    environment_inclusion_system_def artifact_inclusion_system_def replay_admission_system_def
    retention_admission_system_def replay_slot_list_system_def replay_source_list_system_def
    replay_slot_reading_system_def replay_source_reading_system_def definition_slot_reading_system_def
    schema_slot_reading_system_def premise_slot_reading_system_def derivation_admission_system_def
    proof_claim_checking_system_def keyed_row_join_system_def row_qualification_system_def
    proof_graph_membership_system_def proof_graph_admission_system_def proof_bound_checking_system_def
    proof_link_checking_system_def proof_node_reading_system_def discharge_table_reading_system_def
    binding_table_reading_system_def site_link_vector_system_def application_vector_system_def
    site_link_reading_system_def site_citation_reading_system_def admitted_instantiation_system_def
    program_call_list_system_def application_admission_system_def program_call_admission_system_def
    package_membership_system_def definition_edge_reading_system_def definition_clause_reading_system_def
    package_admission_system_def root_family_reading_system_def located_list_system_def
    package_closure_admission_system_def definition_callee_list_system_def definition_callee_inclusion_system_def
    schema_callee_list_system_def schema_callee_inclusion_system_def definition_call_admission_system_def
    schema_family_admission_system_def schema_root_list_system_def schema_admission_system_def
    schema_material_checking_system_def material_rows_checking_system_def material_checking_system_def
    schema_instantiation_system_def premise_family_instantiation_system_def premise_rows_system_def
    material_instantiation_system_def record_instantiation_system_def vector_instantiation_system_def
    row_values_system_def application_reading_system_def prospective_instantiation_system_def
    scoped_instantiation_system_def pattern_instantiation_system_def binder_admission_system_def
    diagonal_rows_system_def binding_admission_system_def)

lemma environment_inclusion_located_meaning:
  assumes "d\<in>system_definitions located_admission_system"
  shows "(d,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning located_admission_system"
proof -
  have closed: "system_dependency_closed located_admission_system (system_definitions located_admission_system)"
    using system_dependency_boundary(1)[OF located_admission_system_formed]
    unfolding system_dependency_closed_def by blast
  show ?thesis
    using positive_meaning_dependency_locality[OF located_admission_system_formed environment_inclusion_system_formed
      environment_inclusion_located_agreement closed assms, of t] by blast
qed

lemma environment_inclusion_row_keys_meaning:
  assumes "d\<in>system_definitions row_keys_system"
  shows "(d,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning row_keys_system"
proof -
  have closed: "system_dependency_closed row_keys_system (system_definitions row_keys_system)"
    using system_dependency_boundary(1)[OF row_keys_system_formed]
    unfolding system_dependency_closed_def by blast
  show ?thesis
    using positive_meaning_dependency_locality[OF row_keys_system_formed environment_inclusion_system_formed
      environment_inclusion_row_keys_agreement closed assms, of t] by blast
qed

lemma environment_inclusion_dependency_boundary:
  "system_dependency_closed environment_inclusion_system
    (system_definitions row_keys_system\<union>{112,113})"
proof -
  have original: "system_dependency_closed row_keys_system (system_definitions row_keys_system)"
    using system_dependency_boundary(1)[OF row_keys_system_formed]
    unfolding system_dependency_closed_def by blast
  have lower: "system_dependency_closed environment_inclusion_system (system_definitions row_keys_system)"
    by (rule systems_agree_on_closed[OF environment_inclusion_row_keys_agreement original])
  have rows: "e\<in>{37,112}" if "(112,e)\<in>system_dependency_edges environment_inclusion_system" for e
    using that by (auto simp: system_dependency_edges_def environment_inclusion_system_def
      context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_dependencies_def rel_ran_def)
  have whole: "e\<in>{26,47,112}" if "(113,e)\<in>system_dependency_edges environment_inclusion_system" for e
    using that by (auto simp: system_dependency_edges_def environment_inclusion_schema_def
      schema_dependencies_def rel_ran_def)
  have needed: "{26,37,47}\<subseteq>system_definitions row_keys_system" by auto
  show ?thesis using lower rows whole needed unfolding system_dependency_closed_def by blast
qed

text \<open>
  The inclusion relation compares both complete environment tables, with each
  artifact at its actual use and each binding at its actual source slot.
  Its local presentation contract supplies general transport and composition
  laws to clients.

  Its existing construction follows the earlier replay program, but the
  complete dependency closure of the inclusion clauses lies within ordinary
  data, lookup, and the two inclusion definitions. The retained boundary is
  established from the actual clause families. This proof does not change the
  earlier program, any represented environment, or the meaning of inclusion.
\<close>

end
