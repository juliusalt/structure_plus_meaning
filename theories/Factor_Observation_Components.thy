theory Factor_Observation_Components
  imports Factor_Observation_Clauses Factor_Data_Set_Comparison Factor_Component_Agreement
begin

section \<open>Actual shared collection definitions support the program join\<close>

lemma data_subset_bag_agreement:
  "systems_agree_on bag_comparison_system data_subset_system (system_definitions bag_comparison_system)"
  by (simp add: systems_agree_on_added
    data_subset_system_def data_append_system_def target_projection_system_def
    located_admission_system_def anchored_admission_system_def citation_reading_system_def
    citation_location_system_def citation_interpretation_system_def citation_resolution_system_def
    binding_lookup_system_def artifact_lookup_system_def citation_admission_system_def
    target_admission_system_def record_admission_system_def socket_chain_system_def
    family_admission_system_def family_sockets_system_def family_socket_system_def
    headed_material_system_def key_fibre_system_def environment_identity_system_def
    environment_admission_system_def binding_entries_system_def binding_entry_system_def
    artifact_entries_system_def artifact_entry_admission_system_def keyed_list_system_def
    key_absence_system_def coordinate_admission_system_def natural_list_system_def
    natural_admission_system_def environment_comparison_system_def environment_bag_system_def
    environment_selection_system_def environment_entry_system_def artifact_identity_system_def
    artifact_admission_system_def artifact_projection_system_def material_data_system_def
    atom_lookup_system_def artifact_comparison_system_def)

lemma data_subset_absence_agreement:
  "systems_agree_on data_subset_system data_absence_system
    (system_definitions data_subset_system\<inter>system_definitions data_absence_system)"
proof -
  have original: "systems_agree_on bag_comparison_system data_absence_system
      (system_definitions bag_comparison_system)"
    by (simp add: data_absence_system_def systems_agree_on_added)
  have same: "systems_agree_on data_subset_system data_absence_system (system_definitions bag_comparison_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF data_subset_bag_agreement] original])
  have overlap: "system_definitions data_subset_system\<inter>system_definitions data_absence_system=
      system_definitions bag_comparison_system" by auto
  show ?thesis using same by (simp only: overlap)
qed

lemma data_set_absence_agreement:
  "systems_agree_on data_set_comparison_system data_absence_system
    (system_definitions data_set_comparison_system\<inter>system_definitions data_absence_system)"
proof -
  have base: "systems_agree_on data_set_comparison_base_system data_absence_system
      (system_definitions data_set_comparison_base_system\<inter>system_definitions data_absence_system)"
    unfolding data_set_comparison_base_system_def
    by (rule rooted_overlap_agreement[OF data_subset_absence_agreement])
  show ?thesis unfolding data_set_comparison_system_def
    by (rule positive_definition_group.extended_overlap_agreement[OF data_set_comparison_group.positive_definition_group_axioms base]) auto
qed

lemma observation_set_agreement:
  "systems_agree_on observation_system data_set_comparison_system
    (system_definitions observation_system\<inter>system_definitions data_set_comparison_system)"
proof -
  have reverse: "systems_agree_on data_absence_system data_set_comparison_system
      (system_definitions data_absence_system\<inter>system_definitions data_set_comparison_system)"
    using systems_agree_on_sym[OF data_set_absence_agreement] by (simp only: Int_commute)
  have base: "systems_agree_on observation_base_system data_set_comparison_system
      (system_definitions observation_base_system\<inter>system_definitions data_set_comparison_system)"
    unfolding observation_base_system_def by (rule rooted_overlap_agreement[OF reverse])
  show ?thesis unfolding observation_system_def
    by (rule positive_definition_group.extended_overlap_agreement[OF observation_group.positive_definition_group_axioms base])
      (use data_set_comparison_base_subdomain in auto)
qed

definition observation_collection_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_collection_system=system_union observation_system data_set_comparison_system"

lemma observation_collection_formed [simp]: "schema_system_formed observation_collection_system"
  unfolding observation_collection_system_def
  by (rule system_union_agree_formed[OF observation_system_formed data_set_comparison_system_formed
    observation_set_agreement])

lemma observation_collection_definitions [simp]:
  "system_definitions observation_collection_system=
    system_definitions observation_system\<union>system_definitions data_set_comparison_system"
  by (simp add: observation_collection_system_def)

lemma observation_collection_call:
  "schema_call_formed observation_collection_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_collection_system \<and> term_formed t"
  using system_union_agree_call[OF observation_system_formed data_set_comparison_system_formed
    observation_set_agreement, of d t]
  by (simp only: observation_collection_system_def system_union_definitions observation_call
    data_set_comparison_call Un_iff; blast)

lemma observation_collection_meaning:
  assumes "d\<in>system_definitions observation_system"
  shows "(d,t)\<in>positive_meaning observation_collection_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning observation_system"
  unfolding observation_collection_system_def
  by (rule system_union_agree_left_locality(2)[OF observation_system_formed data_set_comparison_system_formed
    observation_set_agreement assms])

lemma observation_collection_set_meaning:
  "(219,t)\<in>positive_meaning observation_collection_system \<longleftrightarrow>
    (219,t)\<in>positive_meaning data_set_comparison_system"
  unfolding observation_collection_system_def
  by (rule system_union_agree_right_locality(2)[OF observation_system_formed data_set_comparison_system_formed
    observation_set_agreement]) auto

text \<open>
  The join retains both programs' actual definitions. Agreement is established
  through their common collection component before any meanings are transferred.
  Restriction and the fresh groups carry that structural agreement to their
  own dependency boundaries. Equality of meanings alone is not used to justify
  shared definition coordinates.
\<close>

end
