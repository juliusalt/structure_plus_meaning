theory Factor_Generation_Reader_Payloads
  imports Factor_Reader_Payloads Factor_Generation_Source_Clauses Factor_Adoption_Comparison
begin

section \<open>The payloads of the generation and adoption readers, down their lineages\<close>

text \<open>
  The generation and adoption readers the given's program is granted continue the lineages of
  @{text Factor_Reader_Payloads} above it, each step's fact derived by the same lineage rule: the generation lineages leave the common
  one at the bag comparison, the artifact identity, the target admission and the located admission. Standing
  apart, they keep a change of these lineages from rebuilding the guard's readers, whose payloads need only the
  use-additions and payload-audit lineages. The three reader systems the given's program joins here are
  @{const generation_value_system}, @{const generation_source_system} and @{const adoption_value_system}.
\<close>

lemma data_absence_system_payloads [lineage_payloads]: "system_payloads data_absence_system\<subseteq>{[]}"
  unfolding data_absence_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)

lemma bag_difference_system_payloads [lineage_payloads]: "system_payloads bag_difference_system\<subseteq>{[]}"
  unfolding bag_difference_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps bag_difference_clauses_def bag_extra_schema_def bag_missing_schema_def bag_step_schema_def)

lemma artifact_difference_base_system_payloads [lineage_payloads]: "system_payloads artifact_difference_base_system\<subseteq>{[]}"
  unfolding artifact_difference_base_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma artifact_difference_system_payloads [lineage_payloads]: "system_payloads artifact_difference_system\<subseteq>{[]}"
  unfolding artifact_difference_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps artifact_difference_clauses_def artifact_difference_schema_def)

lemma target_comparison_base_system_payloads [lineage_payloads]: "system_payloads target_comparison_base_system\<subseteq>{[]}"
  unfolding target_comparison_base_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma target_identity_system_payloads [lineage_payloads]: "system_payloads target_identity_system\<subseteq>{[]}"
  unfolding target_identity_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps target_identity_schema_def)

lemma target_difference_system_payloads [lineage_payloads]: "system_payloads target_difference_system\<subseteq>{[]}"
  unfolding target_difference_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps target_difference_clauses_def target_artifact_difference_schema_def target_occurrence_difference_schema_def)

lemma generation_definition_group_payloads [lineage_payloads]: "system_payloads generation_definition_group\<subseteq>{[]}"
  unfolding generation_definition_group_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps generation_group_clauses_def generation_admission_schema_def generation_identity_schema_def generation_difference_schema_def context_list_clauses_def separated_list_clauses_def related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def context_list_nil_schema_def context_list_step_schema_def data_list_nil_schema_def separated_list_step_schema_def related_selection_here_schema_def selection_later_schema_def bag_nil_schema_def bag_step_schema_def related_extra_schema_def related_missing_schema_def)

lemma generation_target_system_payloads [lineage_payloads]: "system_payloads generation_target_system\<subseteq>{[]}"
  unfolding generation_target_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma generation_value_system_payloads [lineage_payloads]: "system_payloads generation_value_system\<subseteq>{[]}"
  unfolding generation_value_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma generation_source_components_system_payloads [lineage_payloads]: "system_payloads generation_source_components_system\<subseteq>{[]}"
  unfolding generation_source_components_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma generation_source_definition_group_payloads [lineage_payloads]: "system_payloads generation_source_definition_group\<subseteq>{[]}"
  unfolding generation_source_definition_group_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps generation_source_group_clauses_def generation_syntax_schema_def generation_fields_schema_def generation_child_value_schema_def related_list_clauses_def generation_core_report_schema_def generation_source_schema_def generation_child_row_schema_def generation_predecessor_report_schema_def related_list_nil_schema_def related_list_step_schema_def)

lemma generation_source_base_system_payloads [lineage_payloads]: "system_payloads generation_source_base_system\<subseteq>{[]}"
  unfolding generation_source_base_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma generation_source_system_payloads [lineage_payloads]: "system_payloads generation_source_system\<subseteq>{[]}"
  unfolding generation_source_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma adoption_comparison_base_payloads [lineage_payloads]: "system_payloads adoption_comparison_base\<subseteq>{[]}"
  unfolding adoption_comparison_base_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps)

lemma adoption_admission_system_payloads [lineage_payloads]: "system_payloads adoption_admission_system\<subseteq>{[]}"
  unfolding adoption_admission_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps adoption_admission_schema_def)

lemma adoption_value_system_payloads [lineage_payloads]: "system_payloads adoption_value_system\<subseteq>{[]}"
  unfolding adoption_value_system_def by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps adoption_identity_schema_def)

end
