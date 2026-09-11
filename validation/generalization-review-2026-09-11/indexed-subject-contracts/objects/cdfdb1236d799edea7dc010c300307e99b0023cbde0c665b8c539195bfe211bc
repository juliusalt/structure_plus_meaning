theory Factor_Row_Value_Agreement
  imports Factor_Row_Values Factor_System_Composition
begin

section \<open>Actual extension boundaries retain their complete ancestors\<close>

lemma row_values_row_keys_agreement:
  "systems_agree_on row_keys_system row_values_system (system_definitions row_keys_system)"
  by (simp add: row_values_system_def application_reading_system_def prospective_instantiation_system_def
    scoped_instantiation_system_def pattern_instantiation_system_def binder_admission_system_def
    diagonal_rows_system_def binding_admission_system_def systems_agree_on_added)

lemma row_values_subset_agreement:
  "systems_agree_on data_subset_system row_values_system (system_definitions data_subset_system)"
proof -
  have prefix: "systems_agree_on data_subset_system row_keys_system (system_definitions data_subset_system)"
    by (simp add: row_keys_system_def quotation_admission_system_def payload_disjoint_system_def
    data_union_system_def systems_agree_on_added)
  have suffix: "systems_agree_on row_keys_system row_values_system (system_definitions data_subset_system)"
    by (rule systems_agree_on_subdomain[OF row_values_row_keys_agreement]) auto
  show ?thesis by (rule systems_agree_on_transitive[OF prefix suffix])
qed

lemma row_values_append_agreement:
  "systems_agree_on data_append_system row_values_system (system_definitions data_append_system)"
proof -
  have prefix: "systems_agree_on data_append_system data_subset_system (system_definitions data_append_system)"
    by (simp add: data_subset_system_def systems_agree_on_added)
  have suffix: "systems_agree_on data_subset_system row_values_system (system_definitions data_append_system)"
    by (rule systems_agree_on_subdomain[OF row_values_subset_agreement]) auto
  show ?thesis by (rule systems_agree_on_transitive[OF prefix suffix])
qed

lemma row_values_keyed_agreement:
  "systems_agree_on keyed_list_system row_values_system (system_definitions keyed_list_system)"
proof -
  have prefix: "systems_agree_on keyed_list_system data_append_system (system_definitions keyed_list_system)"
    by (simp add: data_append_system_def target_projection_system_def located_admission_system_def
    anchored_admission_system_def citation_reading_system_def citation_location_system_def
    citation_interpretation_system_def citation_resolution_system_def binding_lookup_system_def
    artifact_lookup_system_def citation_admission_system_def target_admission_system_def
    record_admission_system_def socket_chain_system_def family_admission_system_def
    family_sockets_system_def family_socket_system_def headed_material_system_def
    key_fibre_system_def environment_identity_system_def environment_admission_system_def
    binding_entries_system_def binding_entry_system_def artifact_entries_system_def
    artifact_entry_admission_system_def systems_agree_on_added)
  have suffix: "systems_agree_on data_append_system row_values_system (system_definitions keyed_list_system)"
    by (rule systems_agree_on_subdomain[OF row_values_append_agreement]) auto
  show ?thesis by (rule systems_agree_on_transitive[OF prefix suffix])
qed

lemma row_values_artifact_agreement:
  "systems_agree_on artifact_identity_system row_values_system (system_definitions artifact_identity_system)"
proof -
  have prefix: "systems_agree_on artifact_identity_system keyed_list_system (system_definitions artifact_identity_system)"
    by (simp add: keyed_list_system_def key_absence_system_def coordinate_admission_system_def
    natural_list_system_def natural_admission_system_def environment_comparison_system_def
    environment_bag_system_def environment_selection_system_def environment_entry_system_def systems_agree_on_added)
  have suffix: "systems_agree_on keyed_list_system row_values_system (system_definitions artifact_identity_system)"
    by (rule systems_agree_on_subdomain[OF row_values_keyed_agreement]) auto
  show ?thesis by (rule systems_agree_on_transitive[OF prefix suffix])
qed

lemma row_values_bag_agreement:
  "systems_agree_on bag_comparison_system row_values_system (system_definitions bag_comparison_system)"
proof -
  have prefix: "systems_agree_on bag_comparison_system artifact_identity_system (system_definitions bag_comparison_system)"
    by (simp add: artifact_identity_system_def artifact_admission_system_def artifact_projection_system_def
    material_data_system_def atom_lookup_system_def artifact_comparison_system_def systems_agree_on_added)
  have suffix: "systems_agree_on artifact_identity_system row_values_system (system_definitions bag_comparison_system)"
    by (rule systems_agree_on_subdomain[OF row_values_artifact_agreement]) auto
  show ?thesis by (rule systems_agree_on_transitive[OF prefix suffix])
qed

text \<open>
  Each agreement concerns the actual interfaces and complete clause families.
  The fresh-definition rule checks each extension boundary; transitivity and
  restriction reuse the already established suffix. A later program join can
  retain these whole ancestors without re-proving each entry's meaning.
\<close>

end
