theory Factor_Reader_Payloads
  imports Factor_System_Payloads Factor_Package_Additions Factor_Payload_Audit Factor_Generation_Source_Clauses
    Factor_Adoption_Comparison
begin

section \<open>The payloads of the reader programs, down their lineages\<close>

text \<open>
  Every reader program is built from a base program by fresh views, unions and rooted restrictions, each
  program's lineage the chain of those steps. Its payloads are bounded step by step: a view adds the payloads of
  its interface and of its clauses (@{thm [source] add_view_definition_payloads}), each computed by simp on that
  step's own patterns; a union states what its two parts state (@{thm [source] system_union_payloads}); a rooted
  restriction no more than its source (@{thm [source] rooted_system_payloads}); a group of definitions given as
  fields is computed on its own clauses. Every program of every lineage states the empty payload alone, so the
  fact of each is reusable by any program containing it, and a chain two lineages share is followed once:
  the payload audit's lineage leaves the common one at definition admission, the generation lineages at the bag
  comparison, the artifact identity, the target admission and the located admission. The five reader systems
  the given's program joins are @{const use_additions_system}, @{const payload_audit_system},
  @{const generation_value_system}, @{const generation_source_system} and @{const adoption_value_system}.
\<close>

lemma distinct_payloads_system_payloads: "system_payloads distinct_payloads_system\<subseteq>{[]}"
  unfolding distinct_payloads_system_def system_payloads_def system_leaves_def
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def carrier_projection_empty_schema_def carrier_projection_cons_schema_def distinct_payloads_schema_def distinct_payloads_material_def)

lemma data_recognition_system_payloads: "system_payloads data_recognition_system\<subseteq>{[]}"
  using distinct_payloads_system_payloads unfolding data_recognition_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_recognition_clauses_def data_payload_schema_def data_pair_schema_def)

lemma data_comparison_system_payloads: "system_payloads data_comparison_system\<subseteq>{[]}"
  using data_recognition_system_payloads unfolding data_comparison_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_comparison_clauses_def data_payload_difference_schema_def data_left_leaf_schema_def data_right_leaf_schema_def data_left_difference_schema_def data_right_difference_schema_def)

lemma data_list_system_payloads: "system_payloads data_list_system\<subseteq>{[]}"
  using data_comparison_system_payloads unfolding data_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_list_clauses_def data_list_nil_schema_def data_list_cons_schema_def list_step_schema_def)

lemma data_selection_system_payloads: "system_payloads data_selection_system\<subseteq>{[]}"
  using data_list_system_payloads unfolding data_selection_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_selection_clauses_def data_selection_here_schema_def data_selection_later_schema_def selection_later_schema_def)

lemma bag_comparison_system_payloads: "system_payloads bag_comparison_system\<subseteq>{[]}"
  using data_selection_system_payloads unfolding bag_comparison_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def bag_comparison_clauses_def bag_nil_schema_def bag_cons_schema_def bag_step_schema_def)

lemma artifact_comparison_system_payloads: "system_payloads artifact_comparison_system\<subseteq>{[]}"
  using bag_comparison_system_payloads unfolding artifact_comparison_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_comparison_schema_def)

lemma atom_lookup_system_payloads: "system_payloads atom_lookup_system\<subseteq>{[]}"
  using artifact_comparison_system_payloads unfolding atom_lookup_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def atom_lookup_clauses_def atom_lookup_here_schema_def atom_lookup_later_schema_def)

lemma material_data_system_payloads: "system_payloads material_data_system\<subseteq>{[]}"
  using atom_lookup_system_payloads unfolding material_data_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def material_projection_clauses_def material_projection_empty_schema_def material_projection_address_schema_def material_projection_payload_schema_def material_projection_pair_schema_def)

lemma artifact_projection_system_payloads: "system_payloads artifact_projection_system\<subseteq>{[]}"
  using material_data_system_payloads unfolding artifact_projection_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_projection_schema_def artifact_projection_material_def)

lemma artifact_admission_system_payloads: "system_payloads artifact_admission_system\<subseteq>{[]}"
  using artifact_projection_system_payloads unfolding artifact_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_admission_schema_def)

lemma artifact_identity_system_payloads: "system_payloads artifact_identity_system\<subseteq>{[]}"
  using artifact_admission_system_payloads unfolding artifact_identity_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_identity_schema_def)

lemma environment_entry_system_payloads: "system_payloads environment_entry_system\<subseteq>{[]}"
  using artifact_identity_system_payloads unfolding environment_entry_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def environment_entry_schema_def)

lemma environment_selection_system_payloads: "system_payloads environment_selection_system\<subseteq>{[]}"
  using environment_entry_system_payloads unfolding environment_selection_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def related_selection_clauses_def related_selection_here_schema_def selection_later_schema_def)

lemma environment_bag_system_payloads: "system_payloads environment_bag_system\<subseteq>{[]}"
  using environment_selection_system_payloads unfolding environment_bag_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def related_bag_clauses_def bag_nil_schema_def bag_step_schema_def)

lemma environment_comparison_system_payloads: "system_payloads environment_comparison_system\<subseteq>{[]}"
  using environment_bag_system_payloads unfolding environment_comparison_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def environment_comparison_schema_def)

lemma natural_admission_system_payloads: "system_payloads natural_admission_system\<subseteq>{[]}"
  using environment_comparison_system_payloads unfolding natural_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def natural_admission_clauses_def data_list_nil_schema_def natural_successor_schema_def)

lemma natural_list_system_payloads: "system_payloads natural_list_system\<subseteq>{[]}"
  using natural_admission_system_payloads unfolding natural_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def list_profile_clauses_def data_list_nil_schema_def list_step_schema_def)

lemma coordinate_admission_system_payloads: "system_payloads coordinate_admission_system\<subseteq>{[]}"
  using natural_list_system_payloads unfolding coordinate_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def coordinate_admission_clauses_def data_list_nil_schema_def coordinate_some_schema_def)

lemma key_absence_system_payloads: "system_payloads key_absence_system\<subseteq>{[]}"
  using coordinate_admission_system_payloads unfolding key_absence_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def key_absence_clauses_def key_absence_nil_schema_def key_absence_cons_schema_def)

lemma keyed_list_system_payloads: "system_payloads keyed_list_system\<subseteq>{[]}"
  using key_absence_system_payloads unfolding keyed_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def keyed_list_clauses_def data_list_nil_schema_def keyed_list_cons_schema_def)

lemma artifact_entry_admission_system_payloads: "system_payloads artifact_entry_admission_system\<subseteq>{[]}"
  using keyed_list_system_payloads unfolding artifact_entry_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_entry_admission_schema_def)

lemma artifact_entries_system_payloads: "system_payloads artifact_entries_system\<subseteq>{[]}"
  using artifact_entry_admission_system_payloads unfolding artifact_entries_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def list_profile_clauses_def data_list_nil_schema_def list_step_schema_def)

lemma binding_entry_system_payloads: "system_payloads binding_entry_system\<subseteq>{[]}"
  using artifact_entries_system_payloads unfolding binding_entry_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def binding_entry_schema_def)

lemma binding_entries_system_payloads: "system_payloads binding_entries_system\<subseteq>{[]}"
  using binding_entry_system_payloads unfolding binding_entries_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma environment_admission_system_payloads: "system_payloads environment_admission_system\<subseteq>{[]}"
  using binding_entries_system_payloads unfolding environment_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def environment_admission_schema_def)

lemma environment_identity_system_payloads: "system_payloads environment_identity_system\<subseteq>{[]}"
  using environment_admission_system_payloads unfolding environment_identity_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def environment_identity_schema_def)

lemma key_fibre_system_payloads: "system_payloads key_fibre_system\<subseteq>{[]}"
  using environment_identity_system_payloads unfolding key_fibre_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def key_fibre_clauses_def key_fibre_nil_schema_def key_fibre_keep_schema_def key_fibre_skip_schema_def)

lemma headed_material_system_payloads: "system_payloads headed_material_system\<subseteq>{[]}"
  using key_fibre_system_payloads unfolding headed_material_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def headed_material_schema_def)

lemma family_socket_system_payloads: "system_payloads family_socket_system\<subseteq>{[]}"
  using headed_material_system_payloads unfolding family_socket_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def family_socket_schema_def)

lemma family_sockets_system_payloads: "system_payloads family_sockets_system\<subseteq>{[]}"
  using family_socket_system_payloads unfolding family_sockets_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma family_admission_system_payloads: "system_payloads family_admission_system\<subseteq>{[]}"
  using family_sockets_system_payloads unfolding family_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def family_admission_schema_def)

lemma socket_chain_system_payloads: "system_payloads socket_chain_system\<subseteq>{[]}"
  using family_admission_system_payloads unfolding socket_chain_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def socket_chain_clauses_def context_list_nil_schema_def socket_chain_last_schema_def socket_chain_step_schema_def)

lemma record_admission_system_payloads: "system_payloads record_admission_system\<subseteq>{[]}"
  using socket_chain_system_payloads unfolding record_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def record_admission_schema_def)

lemma target_admission_system_payloads: "system_payloads target_admission_system\<subseteq>{[]}"
  using record_admission_system_payloads unfolding target_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def target_admission_clauses_def target_whole_schema_def target_occurrence_schema_def)

lemma citation_admission_system_payloads: "system_payloads citation_admission_system\<subseteq>{[]}"
  using target_admission_system_payloads unfolding citation_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def citation_admission_clauses_def citation_local_schema_def citation_local_whole_schema_def citation_external_whole_schema_def citation_external_schema_def)

lemma artifact_lookup_system_payloads: "system_payloads artifact_lookup_system\<subseteq>{[]}"
  using citation_admission_system_payloads unfolding artifact_lookup_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_lookup_schema_def)

lemma binding_lookup_system_payloads: "system_payloads binding_lookup_system\<subseteq>{[]}"
  using artifact_lookup_system_payloads unfolding binding_lookup_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def binding_lookup_schema_def)

lemma citation_resolution_system_payloads: "system_payloads citation_resolution_system\<subseteq>{[]}"
  using binding_lookup_system_payloads unfolding citation_resolution_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def citation_resolution_clauses_def citation_resolve_local_schema_def citation_resolve_external_schema_def)

lemma citation_interpretation_system_payloads: "system_payloads citation_interpretation_system\<subseteq>{[]}"
  using citation_resolution_system_payloads unfolding citation_interpretation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def citation_interpretation_schema_def)

lemma citation_location_system_payloads: "system_payloads citation_location_system\<subseteq>{[]}"
  using citation_interpretation_system_payloads unfolding citation_location_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def citation_location_schema_def)

lemma citation_reading_system_payloads: "system_payloads citation_reading_system\<subseteq>{[]}"
  using citation_location_system_payloads unfolding citation_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def citation_reading_schema_def)

lemma anchored_admission_system_payloads: "system_payloads anchored_admission_system\<subseteq>{[]}"
  using citation_reading_system_payloads unfolding anchored_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def anchored_admission_schema_def)

lemma located_admission_system_payloads: "system_payloads located_admission_system\<subseteq>{[]}"
  using anchored_admission_system_payloads unfolding located_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def located_admission_schema_def)

lemma target_projection_system_payloads: "system_payloads target_projection_system\<subseteq>{[]}"
  using located_admission_system_payloads unfolding target_projection_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def target_projection_clauses_def target_projection_whole_schema_def target_projection_occurrence_schema_def artifact_projection_material_def)

lemma data_append_system_payloads: "system_payloads data_append_system\<subseteq>{[]}"
  using target_projection_system_payloads unfolding data_append_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_append_clauses_def data_append_nil_schema_def data_append_cons_schema_def)

lemma data_subset_system_payloads: "system_payloads data_subset_system\<subseteq>{[]}"
  using data_append_system_payloads unfolding data_subset_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_subset_clauses_def data_subset_nil_schema_def data_subset_cons_schema_def)

lemma data_union_system_payloads: "system_payloads data_union_system\<subseteq>{[]}"
  using data_subset_system_payloads unfolding data_union_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def data_union_schema_def)

lemma payload_disjoint_system_payloads: "system_payloads payload_disjoint_system\<subseteq>{[]}"
  using data_union_system_payloads unfolding payload_disjoint_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def payload_disjoint_schema_def)

lemma quotation_admission_system_payloads: "system_payloads quotation_admission_system\<subseteq>{[]}"
  using payload_disjoint_system_payloads unfolding quotation_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def quotation_admission_clauses_def quotation_payload_schema_def quotation_target_schema_def quotation_pair_schema_def)

lemma row_keys_system_payloads: "system_payloads row_keys_system\<subseteq>{[]}"
  using quotation_admission_system_payloads unfolding row_keys_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def row_keys_clauses_def bag_nil_schema_def row_keys_cons_schema_def)

lemma binding_admission_system_payloads: "system_payloads binding_admission_system\<subseteq>{[]}"
  using row_keys_system_payloads unfolding binding_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def binding_admission_schema_def)

lemma diagonal_rows_system_payloads: "system_payloads diagonal_rows_system\<subseteq>{[]}"
  using binding_admission_system_payloads unfolding diagonal_rows_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def diagonal_rows_clauses_def bag_nil_schema_def diagonal_rows_cons_schema_def)

lemma binder_admission_system_payloads: "system_payloads binder_admission_system\<subseteq>{[]}"
  using diagonal_rows_system_payloads unfolding binder_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def binder_admission_schema_def)

lemma pattern_instantiation_system_payloads: "system_payloads pattern_instantiation_system\<subseteq>{[]}"
  using binder_admission_system_payloads unfolding pattern_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def pattern_instantiation_clauses_def instantiation_variable_schema_def instantiation_constant_schema_def instantiation_pair_schema_def)

lemma scoped_instantiation_system_payloads: "system_payloads scoped_instantiation_system\<subseteq>{[]}"
  using pattern_instantiation_system_payloads unfolding scoped_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def scoped_instantiation_schema_def)

lemma prospective_instantiation_system_payloads: "system_payloads prospective_instantiation_system\<subseteq>{[]}"
  using scoped_instantiation_system_payloads unfolding prospective_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def prospective_instantiation_schema_def)

lemma application_reading_system_payloads: "system_payloads application_reading_system\<subseteq>{[]}"
  using prospective_instantiation_system_payloads unfolding application_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def application_reading_schema_def)

lemma row_values_system_payloads: "system_payloads row_values_system\<subseteq>{[]}"
  using application_reading_system_payloads unfolding row_values_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def row_values_clauses_def bag_nil_schema_def row_values_cons_schema_def)

lemma vector_instantiation_system_payloads: "system_payloads vector_instantiation_system\<subseteq>{[]}"
  using row_values_system_payloads unfolding vector_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def vector_instantiation_clauses_def vector_instantiation_nil_schema_def vector_instantiation_cons_schema_def)

lemma record_instantiation_system_payloads: "system_payloads record_instantiation_system\<subseteq>{[]}"
  using vector_instantiation_system_payloads unfolding record_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def record_instantiation_schema_def)

lemma material_instantiation_system_payloads: "system_payloads material_instantiation_system\<subseteq>{[]}"
  using record_instantiation_system_payloads unfolding material_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def material_instantiation_schema_def)

lemma premise_rows_system_payloads: "system_payloads premise_rows_system\<subseteq>{[]}"
  using material_instantiation_system_payloads unfolding premise_rows_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def premise_rows_clauses_def premise_rows_nil_schema_def premise_rows_call_schema_def premise_rows_material_schema_def)

lemma premise_family_instantiation_system_payloads: "system_payloads premise_family_instantiation_system\<subseteq>{[]}"
  using premise_rows_system_payloads unfolding premise_family_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def premise_family_instantiation_schema_def)

lemma schema_instantiation_system_payloads: "system_payloads schema_instantiation_system\<subseteq>{[]}"
  using premise_family_instantiation_system_payloads unfolding schema_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_instantiation_schema_def)

lemma material_checking_system_payloads: "system_payloads material_checking_system\<subseteq>{[]}"
  using schema_instantiation_system_payloads unfolding material_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def material_checking_schema_def artifact_projection_material_def)

lemma material_rows_checking_system_payloads: "system_payloads material_rows_checking_system\<subseteq>{[]}"
  using material_checking_system_payloads unfolding material_rows_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def material_rows_checking_clauses_def data_list_nil_schema_def material_rows_checking_cons_schema_def)

lemma schema_material_checking_system_payloads: "system_payloads schema_material_checking_system\<subseteq>{[]}"
  using material_rows_checking_system_payloads unfolding schema_material_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_material_checking_schema_def)

lemma schema_admission_system_payloads: "system_payloads schema_admission_system\<subseteq>{[]}"
  using schema_material_checking_system_payloads unfolding schema_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_admission_schema_def)

lemma schema_root_list_system_payloads: "system_payloads schema_root_list_system\<subseteq>{[]}"
  using schema_admission_system_payloads unfolding schema_root_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma schema_family_admission_system_payloads: "system_payloads schema_family_admission_system\<subseteq>{[]}"
  using schema_root_list_system_payloads unfolding schema_family_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_family_admission_schema_def)

lemma definition_call_admission_system_payloads: "system_payloads definition_call_admission_system\<subseteq>{[]}"
  using schema_family_admission_system_payloads unfolding definition_call_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def definition_call_admission_schema_def)

lemma schema_callee_inclusion_system_payloads: "system_payloads schema_callee_inclusion_system\<subseteq>{[]}"
  using definition_call_admission_system_payloads unfolding schema_callee_inclusion_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_callee_inclusion_schema_def)

lemma schema_callee_list_system_payloads: "system_payloads schema_callee_list_system\<subseteq>{[]}"
  using schema_callee_inclusion_system_payloads unfolding schema_callee_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma definition_callee_inclusion_system_payloads: "system_payloads definition_callee_inclusion_system\<subseteq>{[]}"
  using schema_callee_list_system_payloads unfolding definition_callee_inclusion_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def definition_callee_inclusion_schema_def)

lemma definition_callee_list_system_payloads: "system_payloads definition_callee_list_system\<subseteq>{[]}"
  using definition_callee_inclusion_system_payloads unfolding definition_callee_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma package_closure_admission_system_payloads: "system_payloads package_closure_admission_system\<subseteq>{[]}"
  using definition_callee_list_system_payloads unfolding package_closure_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_closure_admission_schema_def)

lemma located_list_system_payloads: "system_payloads located_list_system\<subseteq>{[]}"
  using package_closure_admission_system_payloads unfolding located_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma root_family_reading_system_payloads: "system_payloads root_family_reading_system\<subseteq>{[]}"
  using located_list_system_payloads unfolding root_family_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def root_family_reading_schema_def)

lemma package_admission_system_payloads: "system_payloads package_admission_system\<subseteq>{[]}"
  using root_family_reading_system_payloads unfolding package_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_admission_schema_def)

lemma definition_clause_reading_system_payloads: "system_payloads definition_clause_reading_system\<subseteq>{[]}"
  using package_admission_system_payloads unfolding definition_clause_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def definition_clause_reading_schema_def)

lemma definition_edge_reading_system_payloads: "system_payloads definition_edge_reading_system\<subseteq>{[]}"
  using definition_clause_reading_system_payloads unfolding definition_edge_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def definition_edge_reading_schema_def)

lemma package_membership_system_payloads: "system_payloads package_membership_system\<subseteq>{[]}"
  using definition_edge_reading_system_payloads unfolding package_membership_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_membership_clauses_def package_membership_root_schema_def package_membership_step_schema_def)

lemma program_call_admission_system_payloads: "system_payloads program_call_admission_system\<subseteq>{[]}"
  using package_membership_system_payloads unfolding program_call_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def program_call_admission_schema_def)

lemma application_admission_system_payloads: "system_payloads application_admission_system\<subseteq>{[]}"
  using program_call_admission_system_payloads unfolding application_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def application_admission_schema_def)

lemma program_call_list_system_payloads: "system_payloads program_call_list_system\<subseteq>{[]}"
  using application_admission_system_payloads unfolding program_call_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma admitted_instantiation_system_payloads: "system_payloads admitted_instantiation_system\<subseteq>{[]}"
  using program_call_list_system_payloads unfolding admitted_instantiation_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def admitted_instantiation_schema_def)

lemma site_citation_reading_system_payloads: "system_payloads site_citation_reading_system\<subseteq>{[]}"
  using admitted_instantiation_system_payloads unfolding site_citation_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def site_citation_reading_schema_def)

lemma site_link_reading_system_payloads: "system_payloads site_link_reading_system\<subseteq>{[]}"
  using site_citation_reading_system_payloads unfolding site_link_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def site_link_reading_schema_def)

lemma application_vector_system_payloads: "system_payloads application_vector_system\<subseteq>{[]}"
  using site_link_reading_system_payloads unfolding application_vector_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def boundary_list_clauses_def boundary_list_nil_schema_def boundary_list_cons_schema_def)

lemma site_link_vector_system_payloads: "system_payloads site_link_vector_system\<subseteq>{[]}"
  using application_vector_system_payloads unfolding site_link_vector_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def boundary_list_clauses_def boundary_list_nil_schema_def boundary_list_cons_schema_def)

lemma binding_table_reading_system_payloads: "system_payloads binding_table_reading_system\<subseteq>{[]}"
  using site_link_vector_system_payloads unfolding binding_table_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def table_reading_schema_def)

lemma discharge_table_reading_system_payloads: "system_payloads discharge_table_reading_system\<subseteq>{[]}"
  using binding_table_reading_system_payloads unfolding discharge_table_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def table_reading_schema_def)

lemma proof_node_reading_system_payloads: "system_payloads proof_node_reading_system\<subseteq>{[]}"
  using discharge_table_reading_system_payloads unfolding proof_node_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_node_reading_clauses_def proof_node_assertion_schema_def proof_node_inference_schema_def)

lemma proof_link_checking_system_payloads: "system_payloads proof_link_checking_system\<subseteq>{[]}"
  using proof_node_reading_system_payloads unfolding proof_link_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_link_checking_clauses_def proof_link_nil_schema_def proof_link_assertion_schema_def proof_link_inference_schema_def)

lemma proof_bound_checking_system_payloads: "system_payloads proof_bound_checking_system\<subseteq>{[]}"
  using proof_link_checking_system_payloads unfolding proof_bound_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_bound_checking_clauses_def proof_bound_nil_schema_def proof_bound_assertion_schema_def proof_bound_inference_schema_def)

lemma proof_graph_admission_system_payloads: "system_payloads proof_graph_admission_system\<subseteq>{[]}"
  using proof_bound_checking_system_payloads unfolding proof_graph_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_graph_admission_schema_def)

lemma proof_graph_membership_system_payloads: "system_payloads proof_graph_membership_system\<subseteq>{[]}"
  using proof_graph_admission_system_payloads unfolding proof_graph_membership_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_graph_membership_clauses_def proof_graph_membership_root_schema_def proof_graph_membership_step_schema_def)

lemma row_qualification_system_payloads: "system_payloads row_qualification_system\<subseteq>{[]}"
  using proof_graph_membership_system_payloads unfolding row_qualification_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def row_qualification_clauses_def row_qualification_nil_schema_def row_qualification_cons_schema_def)

lemma keyed_row_join_system_payloads: "system_payloads keyed_row_join_system\<subseteq>{[]}"
  using row_qualification_system_payloads unfolding keyed_row_join_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def keyed_row_join_clauses_def keyed_row_join_nil_schema_def keyed_row_join_cons_schema_def)

lemma proof_claim_checking_system_payloads: "system_payloads proof_claim_checking_system\<subseteq>{[]}"
  using keyed_row_join_system_payloads unfolding proof_claim_checking_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def proof_claim_checking_clauses_def proof_claim_nil_schema_def proof_claim_assertion_schema_def proof_claim_inference_schema_def)

lemma derivation_admission_system_payloads: "system_payloads derivation_admission_system\<subseteq>{[]}"
  using proof_claim_checking_system_payloads unfolding derivation_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def derivation_admission_schema_def)

lemma premise_slot_reading_system_payloads: "system_payloads premise_slot_reading_system\<subseteq>{[]}"
  using derivation_admission_system_payloads unfolding premise_slot_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def premise_slot_reading_clauses_def premise_call_slot_schema_def premise_material_slot_schema_def)

lemma schema_slot_reading_system_payloads: "system_payloads schema_slot_reading_system\<subseteq>{[]}"
  using premise_slot_reading_system_payloads unfolding schema_slot_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def schema_slot_reading_clauses_def schema_conclusion_slot_schema_def schema_premise_slot_schema_def)

lemma definition_slot_reading_system_payloads: "system_payloads definition_slot_reading_system\<subseteq>{[]}"
  using schema_slot_reading_system_payloads unfolding definition_slot_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def definition_slot_reading_clauses_def definition_interface_slot_schema_def definition_schema_slot_schema_def)

lemma replay_source_reading_system_payloads: "system_payloads replay_source_reading_system\<subseteq>{[]}"
  using definition_slot_reading_system_payloads unfolding replay_source_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def replay_source_reading_clauses_def replay_package_source_schema_def replay_application_source_schema_def replay_definition_source_schema_def replay_node_source_schema_def replay_binding_target_schema_def)

lemma replay_slot_reading_system_payloads: "system_payloads replay_slot_reading_system\<subseteq>{[]}"
  using replay_source_reading_system_payloads unfolding replay_slot_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def replay_slot_reading_clauses_def replay_root_slot_schema_def replay_definition_slot_schema_def replay_application_slot_schema_def replay_node_slot_schema_def)

lemma replay_source_list_system_payloads: "system_payloads replay_source_list_system\<subseteq>{[]}"
  using replay_slot_reading_system_payloads unfolding replay_source_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma replay_slot_list_system_payloads: "system_payloads replay_slot_list_system\<subseteq>{[]}"
  using replay_source_list_system_payloads unfolding replay_slot_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma retention_admission_system_payloads: "system_payloads retention_admission_system\<subseteq>{[]}"
  using replay_slot_list_system_payloads unfolding retention_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def retention_admission_schema_def)

lemma replay_admission_system_payloads: "system_payloads replay_admission_system\<subseteq>{[]}"
  using retention_admission_system_payloads unfolding replay_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def replay_admission_schema_def)

lemma artifact_inclusion_system_payloads: "system_payloads artifact_inclusion_system\<subseteq>{[]}"
  using replay_admission_system_payloads unfolding artifact_inclusion_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma environment_inclusion_system_payloads: "system_payloads environment_inclusion_system\<subseteq>{[]}"
  using artifact_inclusion_system_payloads unfolding environment_inclusion_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def environment_inclusion_schema_def)

lemma positive_query_system_payloads: "system_payloads positive_query_system\<subseteq>{[]}"
  using environment_inclusion_system_payloads unfolding positive_query_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def positive_query_schema_def)

lemma native_positive_admission_system_payloads: "system_payloads native_positive_admission_system\<subseteq>{[]}"
  using positive_query_system_payloads unfolding native_positive_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def native_positive_admission_schema_def)

lemma scope_forwarding_system_payloads: "system_payloads scope_forwarding_system\<subseteq>{[]}"
  using native_positive_admission_system_payloads unfolding scope_forwarding_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def scope_forwarding_schema_def)

lemma package_source_reading_system_payloads: "system_payloads package_source_reading_system\<subseteq>{[]}"
  using scope_forwarding_system_payloads unfolding package_source_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_source_reading_clauses_def package_root_source_schema_def package_definition_source_schema_def package_binding_target_schema_def)

lemma package_slot_reading_system_payloads: "system_payloads package_slot_reading_system\<subseteq>{[]}"
  using package_source_reading_system_payloads unfolding package_slot_reading_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_slot_reading_clauses_def package_root_slot_schema_def package_definition_slot_schema_def)

lemma package_source_list_system_payloads: "system_payloads package_source_list_system\<subseteq>{[]}"
  using package_slot_reading_system_payloads unfolding package_source_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma package_slot_list_system_payloads: "system_payloads package_slot_list_system\<subseteq>{[]}"
  using package_source_list_system_payloads unfolding package_slot_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma package_retention_admission_system_payloads: "system_payloads package_retention_admission_system\<subseteq>{[]}"
  using package_slot_list_system_payloads unfolding package_retention_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_retention_admission_schema_def)

lemma complete_data_admission_system_payloads: "system_payloads complete_data_admission_system\<subseteq>{[]}"
  using package_retention_admission_system_payloads unfolding complete_data_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def complete_data_admission_schema_def)

lemma context_definition_group_payloads: "system_payloads context_definition_group\<subseteq>{[]}"
  unfolding context_definition_group_def system_payloads_def system_leaves_def
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_group_clauses_def site_context_admission_schema_def judgment_context_admission_schema_def context_identity_schema_def)

lemma context_base_system_payloads: "system_payloads context_base_system\<subseteq>{[]}"
  unfolding context_base_system_def by (rule subset_trans[OF rooted_system_payloads artifact_lookup_system_payloads])

lemma context_admission_system_payloads: "system_payloads context_admission_system\<subseteq>{[]}"
  using context_base_system_payloads context_definition_group_payloads unfolding context_admission_system_def system_union_payloads by blast

lemma scope_reading_components_system_payloads: "system_payloads scope_reading_components_system\<subseteq>{[]}"
  using complete_data_admission_system_payloads context_admission_system_payloads unfolding scope_reading_components_system_def system_union_payloads by blast

lemma use_absence_system_payloads: "system_payloads use_absence_system\<subseteq>{[]}"
  using scope_reading_components_system_payloads unfolding use_absence_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def use_absence_schema_def)

lemma addition_element_system_payloads: "system_payloads addition_element_system\<subseteq>{[]}"
  using use_absence_system_payloads unfolding addition_element_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def addition_element_clauses_def addition_member_schema_def addition_callee_schema_def)

lemma addition_list_system_payloads: "system_payloads addition_list_system\<subseteq>{[]}"
  using addition_element_system_payloads unfolding addition_list_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma use_additions_system_payloads: "system_payloads use_additions_system\<subseteq>{[]}"
  using addition_list_system_payloads unfolding use_additions_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def package_additions_schema_def)

lemma empty_payloads_system_payloads: "system_payloads empty_payloads_system\<subseteq>{[]}"
  using definition_call_admission_system_payloads unfolding empty_payloads_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def empty_payloads_clauses_def data_list_nil_schema_def empty_payloads_target_schema_def empty_payloads_pair_schema_def)

lemma empty_payload_rows_system_payloads: "system_payloads empty_payload_rows_system\<subseteq>{[]}"
  using empty_payloads_system_payloads unfolding empty_payload_rows_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def empty_payload_rows_clauses_def data_list_nil_schema_def empty_payload_rows_schema_def)

lemma empty_payload_calls_system_payloads: "system_payloads empty_payload_calls_system\<subseteq>{[]}"
  using empty_payload_rows_system_payloads unfolding empty_payload_calls_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def empty_payload_calls_clauses_def data_list_nil_schema_def empty_payload_calls_schema_def)

lemma clause_payloads_system_payloads: "system_payloads clause_payloads_system\<subseteq>{[]}"
  using empty_payload_calls_system_payloads unfolding clause_payloads_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def clause_payloads_schema_def)

lemma clause_family_payloads_system_payloads: "system_payloads clause_family_payloads_system\<subseteq>{[]}"
  using clause_payloads_system_payloads unfolding clause_family_payloads_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma payload_audit_system_payloads: "system_payloads payload_audit_system\<subseteq>{[]}"
  using clause_family_payloads_system_payloads unfolding payload_audit_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def payload_audit_schema_def)

lemma data_absence_system_payloads: "system_payloads data_absence_system\<subseteq>{[]}"
  using bag_comparison_system_payloads unfolding data_absence_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma bag_difference_system_payloads: "system_payloads bag_difference_system\<subseteq>{[]}"
  using data_absence_system_payloads unfolding bag_difference_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def bag_difference_clauses_def bag_extra_schema_def bag_missing_schema_def bag_step_schema_def)

lemma artifact_difference_base_system_payloads: "system_payloads artifact_difference_base_system\<subseteq>{[]}"
  using artifact_identity_system_payloads bag_difference_system_payloads unfolding artifact_difference_base_system_def system_union_payloads by blast

lemma artifact_difference_system_payloads: "system_payloads artifact_difference_system\<subseteq>{[]}"
  using artifact_difference_base_system_payloads unfolding artifact_difference_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def artifact_difference_clauses_def artifact_difference_schema_def)

lemma target_comparison_base_system_payloads: "system_payloads target_comparison_base_system\<subseteq>{[]}"
  using target_admission_system_payloads artifact_difference_system_payloads unfolding target_comparison_base_system_def system_union_payloads by blast

lemma target_identity_system_payloads: "system_payloads target_identity_system\<subseteq>{[]}"
  using target_comparison_base_system_payloads unfolding target_identity_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def target_identity_schema_def)

lemma target_difference_system_payloads: "system_payloads target_difference_system\<subseteq>{[]}"
  using target_identity_system_payloads unfolding target_difference_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def target_difference_clauses_def target_artifact_difference_schema_def target_occurrence_difference_schema_def)

lemma generation_definition_group_payloads: "system_payloads generation_definition_group\<subseteq>{[]}"
  unfolding generation_definition_group_def system_payloads_def system_leaves_def
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def generation_group_clauses_def generation_admission_schema_def generation_identity_schema_def generation_difference_schema_def context_list_clauses_def separated_list_clauses_def related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def context_list_nil_schema_def context_list_step_schema_def data_list_nil_schema_def separated_list_step_schema_def related_selection_here_schema_def selection_later_schema_def bag_nil_schema_def bag_step_schema_def related_extra_schema_def related_missing_schema_def)

lemma generation_target_system_payloads: "system_payloads generation_target_system\<subseteq>{[]}"
  unfolding generation_target_system_def by (rule subset_trans[OF rooted_system_payloads target_difference_system_payloads])

lemma generation_value_system_payloads: "system_payloads generation_value_system\<subseteq>{[]}"
  using generation_target_system_payloads generation_definition_group_payloads unfolding generation_value_system_def system_union_payloads by blast

lemma generation_source_components_system_payloads: "system_payloads generation_source_components_system\<subseteq>{[]}"
  using located_admission_system_payloads generation_value_system_payloads unfolding generation_source_components_system_def system_union_payloads by blast

lemma generation_source_definition_group_payloads: "system_payloads generation_source_definition_group\<subseteq>{[]}"
  unfolding generation_source_definition_group_def system_payloads_def system_leaves_def
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def generation_source_group_clauses_def generation_syntax_schema_def generation_fields_schema_def generation_child_value_schema_def related_list_clauses_def generation_core_report_schema_def generation_source_schema_def generation_child_row_schema_def generation_predecessor_report_schema_def related_list_nil_schema_def related_list_step_schema_def)

lemma generation_source_base_system_payloads: "system_payloads generation_source_base_system\<subseteq>{[]}"
  unfolding generation_source_base_system_def by (rule subset_trans[OF rooted_system_payloads generation_source_components_system_payloads])

lemma generation_source_system_payloads: "system_payloads generation_source_system\<subseteq>{[]}"
  using generation_source_base_system_payloads generation_source_definition_group_payloads unfolding generation_source_system_def system_union_payloads by blast

lemma adoption_comparison_base_payloads: "system_payloads adoption_comparison_base\<subseteq>{[]}"
  unfolding adoption_comparison_base_def by (rule subset_trans[OF rooted_system_payloads generation_value_system_payloads])

lemma adoption_admission_system_payloads: "system_payloads adoption_admission_system\<subseteq>{[]}"
  using adoption_comparison_base_payloads unfolding adoption_admission_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def adoption_admission_schema_def)

lemma adoption_value_system_payloads: "system_payloads adoption_value_system\<subseteq>{[]}"
  using adoption_admission_system_payloads unfolding adoption_value_system_def add_view_definition_payloads
  by (auto simp: schema_leaves_def material_leaves_def material_fields_def adoption_identity_schema_def)

end
