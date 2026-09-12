theory Factor_Scope_Reading_Base
  imports Factor_Context_Admission Factor_Complete_Data_Admission
begin

section \<open>Context and quotation readers share complete lower definitions\<close>

lemma complete_data_located_agreement:
  "systems_agree_on located_admission_system complete_data_admission_system
    (system_definitions located_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def root_family_reading_system_def
    located_list_system_def package_closure_admission_system_def definition_callee_list_system_def
    definition_callee_inclusion_system_def schema_callee_list_system_def schema_callee_inclusion_system_def
    definition_call_admission_system_def schema_family_admission_system_def schema_root_list_system_def
    schema_admission_system_def schema_material_checking_system_def material_rows_checking_system_def
    material_checking_system_def schema_instantiation_system_def premise_family_instantiation_system_def
    premise_rows_system_def material_instantiation_system_def record_instantiation_system_def
    vector_instantiation_system_def row_values_system_def application_reading_system_def
    prospective_instantiation_system_def scoped_instantiation_system_def pattern_instantiation_system_def
    binder_admission_system_def diagonal_rows_system_def binding_admission_system_def
    row_keys_system_def quotation_admission_system_def payload_disjoint_system_def
    data_union_system_def data_subset_system_def data_append_system_def
    target_projection_system_def)

lemma complete_data_quotation_agreement:
  "systems_agree_on quotation_admission_system complete_data_admission_system
    (system_definitions quotation_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def root_family_reading_system_def
    located_list_system_def package_closure_admission_system_def definition_callee_list_system_def
    definition_callee_inclusion_system_def schema_callee_list_system_def schema_callee_inclusion_system_def
    definition_call_admission_system_def schema_family_admission_system_def schema_root_list_system_def
    schema_admission_system_def schema_material_checking_system_def material_rows_checking_system_def
    material_checking_system_def schema_instantiation_system_def premise_family_instantiation_system_def
    premise_rows_system_def material_instantiation_system_def record_instantiation_system_def
    vector_instantiation_system_def row_values_system_def application_reading_system_def
    prospective_instantiation_system_def scoped_instantiation_system_def pattern_instantiation_system_def
    binder_admission_system_def diagonal_rows_system_def binding_admission_system_def
    row_keys_system_def)

lemma located_lookup_agreement:
  "systems_agree_on artifact_lookup_system located_admission_system
    (system_definitions artifact_lookup_system)"
  by (simp add: systems_agree_on_added located_admission_system_def anchored_admission_system_def
    citation_reading_system_def citation_location_system_def citation_interpretation_system_def
    citation_resolution_system_def binding_lookup_system_def)

lemma complete_data_lookup_agreement:
  "systems_agree_on artifact_lookup_system complete_data_admission_system
    (system_definitions artifact_lookup_system)"
proof -
  have sub: "system_definitions artifact_lookup_system\<subseteq>system_definitions located_admission_system" by auto
  have later: "systems_agree_on located_admission_system complete_data_admission_system
      (system_definitions artifact_lookup_system)"
    by (rule systems_agree_on_subdomain[OF complete_data_located_agreement sub])
  show ?thesis by (rule systems_agree_on_transitive[OF located_lookup_agreement later])
qed

lemma scope_context_agreement:
  "systems_agree_on complete_data_admission_system context_admission_system
    (system_definitions complete_data_admission_system\<inter>system_definitions context_admission_system)"
proof -
  have sub: "system_definitions context_base_system\<subseteq>system_definitions complete_data_admission_system"
    using context_base_subdomain by (auto dest: subsetD)
  have overlap: "system_definitions complete_data_admission_system\<inter>system_definitions context_admission_system=
      system_definitions context_base_system"
    using sub by auto
  have first: "systems_agree_on complete_data_admission_system artifact_lookup_system
      (system_definitions context_base_system)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF complete_data_lookup_agreement] context_base_subdomain])
  have second: "systems_agree_on complete_data_admission_system context_base_system
      (system_definitions context_base_system)"
    by (rule systems_agree_on_transitive[OF first context_base_agreement])
  show ?thesis by (simp only: overlap; rule systems_agree_on_transitive[OF second context_admission_old_agreement])
qed

definition scope_reading_components_system :: "(nat,nat,nat,nat) schema_system" where
  "scope_reading_components_system=system_union complete_data_admission_system context_admission_system"

lemma scope_reading_components_formed [simp]: "schema_system_formed scope_reading_components_system"
  unfolding scope_reading_components_system_def
  by (rule system_union_agree_formed[OF complete_data_admission_system_formed context_admission_system_formed
    scope_context_agreement])

lemma scope_reading_components_definitions [simp]:
  "system_definitions scope_reading_components_system=
    system_definitions complete_data_admission_system\<union>system_definitions context_admission_system"
  by (simp add: scope_reading_components_system_def)

lemma scope_reading_components_call:
  "schema_call_formed scope_reading_components_system d t \<longleftrightarrow>
    d\<in>system_definitions scope_reading_components_system \<and> term_formed t"
  using system_union_agree_call[OF complete_data_admission_system_formed context_admission_system_formed
    scope_context_agreement, of d t]
  by (simp only: scope_reading_components_system_def system_union_definitions
    complete_data_admission_call context_admission_call Un_iff; blast)

lemma scope_reading_complete_agreement:
  "systems_agree_on complete_data_admission_system scope_reading_components_system
    (system_definitions complete_data_admission_system)"
  using system_union_agree_left[OF context_admission_system_formed scope_context_agreement]
  by (simp only: scope_reading_components_system_def)

lemma scope_reading_context_agreement:
  "systems_agree_on context_admission_system scope_reading_components_system
    (system_definitions context_admission_system)"
proof -
  have reverse: "systems_agree_on context_admission_system complete_data_admission_system
      (system_definitions context_admission_system\<inter>system_definitions complete_data_admission_system)"
    using systems_agree_on_sym[OF scope_context_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF complete_data_admission_system_formed reverse]
    by (simp only: scope_reading_components_system_def system_union_commute)
qed

theorem scope_reading_complete_locality:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "schema_call_formed scope_reading_components_system d t \<longleftrightarrow>
      schema_call_formed complete_data_admission_system d t"
    and "(d,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning complete_data_admission_system"
  using system_union_agree_left_locality[OF complete_data_admission_system_formed context_admission_system_formed
    scope_context_agreement assms, of t]
  by (simp_all only: scope_reading_components_system_def)

theorem scope_reading_context_locality:
  assumes "d\<in>system_definitions context_admission_system"
  shows "schema_call_formed scope_reading_components_system d t \<longleftrightarrow>
      schema_call_formed context_admission_system d t"
    and "(d,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning context_admission_system"
  using system_union_agree_right_locality[OF complete_data_admission_system_formed context_admission_system_formed
    scope_context_agreement assms, of t]
  by (simp_all only: scope_reading_components_system_def)

lemma scope_reading_components:
  "(122,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
    (122,t)\<in>positive_meaning package_retention_admission_system"
  "(123,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  "(158,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
    (158,t)\<in>positive_meaning context_admission_system"
  "(159,t)\<in>positive_meaning scope_reading_components_system \<longleftrightarrow>
    (159,t)\<in>positive_meaning context_admission_system"
  using scope_reading_complete_locality(2)[of 122 t] complete_data_admission_old_meaning[of 122 t]
    scope_reading_complete_locality(2)[of 123 t] scope_reading_context_locality(2)[of 158 t]
    scope_reading_context_locality(2)[of 159 t] by auto

section \<open>Judgment quotation has no package or truth dependency\<close>

lemma complete_quotation_dependency_boundary:
  "system_dependency_closed complete_data_admission_system
    (insert 123 (system_definitions quotation_admission_system))"
proof -
  have original: "system_dependency_closed quotation_admission_system
      (system_definitions quotation_admission_system)"
    using system_dependency_boundary(1)[OF quotation_admission_system_formed]
    unfolding system_dependency_closed_def by blast
  have inherited: "system_dependency_closed complete_data_admission_system
      (system_definitions quotation_admission_system)"
    by (rule systems_agree_on_closed[OF complete_data_quotation_agreement original])
  have sole: "e=50" if "(123,e)\<in>system_dependency_edges complete_data_admission_system" for e
    using that by (auto simp: system_dependency_edges_def complete_data_admission_schema_def
      schema_dependencies_def rel_ran_def)
  have root: "50\<in>system_definitions quotation_admission_system" by simp
  show ?thesis using inherited sole root unfolding system_dependency_closed_def by blast
qed

lemma scope_judgment_dependency_boundary:
  "system_dependency_closed scope_reading_components_system
    (insert 123 (system_definitions quotation_admission_system)\<union>system_definitions context_admission_system)"
proof -
  let ?U="insert 123 (system_definitions quotation_admission_system)"
  have sub: "?U\<subseteq>system_definitions complete_data_admission_system" by auto
  have first: "system_dependency_closed scope_reading_components_system ?U"
    by (rule systems_agree_on_closed[OF systems_agree_on_subdomain[OF scope_reading_complete_agreement sub]
      complete_quotation_dependency_boundary])
  have original: "system_dependency_closed context_admission_system (system_definitions context_admission_system)"
    using system_dependency_boundary(1)[OF context_admission_system_formed]
    unfolding system_dependency_closed_def by blast
  have second: "system_dependency_closed scope_reading_components_system (system_definitions context_admission_system)"
    by (rule systems_agree_on_closed[OF scope_reading_context_agreement original])
  show ?thesis using first second unfolding system_dependency_closed_def by blast
qed

text \<open>
  Complete-definition agreement supplies one structural source for local scope
  programs. The following readers select the least dependency-closed part
  containing their actual quotation, comparison, and optional package-scope
  callees. Both original programs keep every interface, clause, and meaning.

  The judgment-quotation branch is already closed inside ordinary term
  quotation and the independent context program. Its closure requires no
  program admission or positive-judgment checker. The separate program-scope
  branch uses package retention because minimal complete program scope is
  part of that independently specified notion.
\<close>

end
