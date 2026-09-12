theory Factor_Inference_Claim_Components
  imports Factor_Inference_Specialization_Clauses Factor_Keyed_Row_Join
    Factor_Keyed_Table_Comparison Factor_Prefixed_Observation_Contracts Factor_Construction_Components
begin

section \<open>The inference and discharge readers retain their common source clauses\<close>

lemma inference_specialization_node_agreement:
  "systems_agree_on proof_node_reading_system inference_specialization_system
    (system_definitions proof_node_reading_system)"
proof -
  have base: "systems_agree_on proof_node_reading_system inference_specialization_base_system
      (system_definitions proof_node_reading_system)"
    unfolding inference_specialization_base_system_def
    by (subst system_union_commute, rule system_union_agree_left[OF specialization_binding_formed])
      (use systems_agree_on_sym[OF inference_specialization_agreement] in \<open>simp only: Int_commute\<close>)
  show ?thesis using base by (simp add: inference_specialization_system_def systems_agree_on_added)
qed

lemma keyed_row_join_node_agreement:
  "systems_agree_on proof_node_reading_system keyed_row_join_system
    (system_definitions proof_node_reading_system)"
  by (simp add: keyed_row_join_system_def row_qualification_system_def proof_graph_membership_system_def
    proof_graph_admission_system_def proof_bound_checking_system_def proof_link_checking_system_def
    systems_agree_on_added)

lemma inference_claim_join_agreement:
  "systems_agree_on inference_specialization_system keyed_row_join_system
    (system_definitions inference_specialization_system\<inter>system_definitions keyed_row_join_system)"
  by (rule common_component_overlap_agreement[where B=proof_node_reading_system])
    (rule systems_agree_on_subdomain[OF inference_specialization_node_agreement], blast,
     rule systems_agree_on_subdomain[OF keyed_row_join_node_agreement], blast, auto)

definition inference_claim_source_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_claim_source_system=system_union inference_specialization_system keyed_row_join_system"

lemma inference_claim_source_formed [simp]: "schema_system_formed inference_claim_source_system"
  unfolding inference_claim_source_system_def
  by (rule system_union_agree_formed[OF inference_specialization_formed keyed_row_join_system_formed
    inference_claim_join_agreement])

lemma inference_claim_source_definitions [simp]:
  "system_definitions inference_claim_source_system=
    system_definitions inference_specialization_system\<union>system_definitions keyed_row_join_system"
  by (simp add: inference_claim_source_system_def)

lemma inference_claim_source_call:
  "schema_call_formed inference_claim_source_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_claim_source_system \<and> term_formed t"
  using system_union_agree_call[OF inference_specialization_formed keyed_row_join_system_formed
    inference_claim_join_agreement, of d t]
  by (simp only: inference_claim_source_system_def system_union_definitions
    inference_specialization_call keyed_row_join_call; blast)

lemma inference_claim_inference_agreement:
  "systems_agree_on inference_specialization_system inference_claim_source_system
    (system_definitions inference_specialization_system)"
  unfolding inference_claim_source_system_def
  by (rule system_union_agree_left[OF keyed_row_join_system_formed inference_claim_join_agreement])

lemma inference_claim_join_source_agreement:
  "systems_agree_on keyed_row_join_system inference_claim_source_system
    (system_definitions keyed_row_join_system)"
  unfolding inference_claim_source_system_def
  by (subst system_union_commute, rule system_union_agree_left[OF inference_specialization_formed])
    (use systems_agree_on_sym[OF inference_claim_join_agreement] in \<open>simp only: Int_commute\<close>)

section \<open>The same complete key-fibre component supplies the comparison group\<close>

lemma reference_bindings_row_agreement:
  "systems_agree_on row_values_system reference_bindings_system (system_definitions row_values_system)"
  apply (simp add: reference_bindings_system_def definition_call_admission_system_def
    schema_family_admission_system_def schema_root_list_system_def schema_admission_system_def
    schema_material_checking_system_def material_rows_checking_system_def material_checking_system_def
    schema_instantiation_system_def premise_family_instantiation_system_def premise_rows_system_def
    material_instantiation_system_def record_instantiation_system_def vector_instantiation_system_def
    systems_agree_on_added)
  done

lemma inference_specialization_reference_agreement:
  "systems_agree_on reference_bindings_system inference_specialization_system
    (system_definitions reference_bindings_system)"
proof -
  have report: "systems_agree_on specialization_report_system specialization_binding_base_system
      (system_definitions specialization_report_system)"
    unfolding specialization_binding_base_system_def
    by (rule system_union_agree_left[OF binding_record_formed specialization_binding_agreement])
  have binding: "systems_agree_on specialization_report_system specialization_binding_system
      (system_definitions specialization_report_system)"
    using report by (simp add: specialization_binding_system_def systems_agree_on_added)
  have source: "systems_agree_on specialization_binding_system inference_specialization_base_system
      (system_definitions specialization_binding_system)"
    unfolding inference_specialization_base_system_def
    by (rule system_union_agree_left[OF proof_node_reading_system_formed inference_specialization_agreement])
  have inference: "systems_agree_on specialization_binding_system inference_specialization_system
      (system_definitions specialization_binding_system)"
    using source by (simp add: inference_specialization_system_def systems_agree_on_added)
  show ?thesis
    by (rule whole_agreement_transitive[OF specialization_report_reference_agreement],
      rule whole_agreement_transitive[OF binding inference])
qed

lemma inference_claim_fibre_agreement:
  "systems_agree_on key_fibre_system inference_claim_source_system (system_definitions key_fibre_system)"
  by (rule whole_agreement_transitive[OF row_values_key_fibre_agreement],
    rule whole_agreement_transitive[OF reference_bindings_row_agreement],
    rule whole_agreement_transitive[OF inference_specialization_reference_agreement inference_claim_inference_agreement])

lemma inference_claim_table_base_agreement:
  "systems_agree_on keyed_table_base_system inference_claim_source_system
    (system_definitions keyed_table_base_system)"
  unfolding keyed_table_base_system_def
  by (rule rooted_agreement_transfer[OF inference_claim_fibre_agreement])

interpretation inference_claim_table_group:
  positive_definition_group inference_claim_source_system keyed_table_group_system
  by (rule positive_definition_group.rebased_group[OF keyed_table_group.positive_definition_group_axioms inference_claim_source_formed inference_claim_table_base_agreement]) auto

definition inference_claim_table_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_claim_table_system=system_union inference_claim_source_system keyed_table_group_system"

lemma inference_claim_table_formed [simp]: "schema_system_formed inference_claim_table_system"
  using inference_claim_table_group.formed by (simp only: inference_claim_table_system_def)

lemma inference_claim_table_definitions [simp]:
  "system_definitions inference_claim_table_system=
    system_definitions inference_claim_source_system\<union>system_definitions keyed_table_group_system"
  by (simp add: inference_claim_table_system_def)

lemma inference_claim_table_call:
  "schema_call_formed inference_claim_table_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_claim_table_system \<and> term_formed t"
  unfolding inference_claim_table_system_def
  by (rule inference_claim_table_group.variable_calls[OF inference_claim_source_call keyed_table_group_interfaces])

lemma inference_claim_source_table_agreement:
  "systems_agree_on inference_claim_source_system inference_claim_table_system
    (system_definitions inference_claim_source_system)"
  using inference_claim_table_group.old_agreement by (simp only: inference_claim_table_system_def)

lemma inference_claim_table_original_agreement:
  "systems_agree_on keyed_table_comparison_system inference_claim_table_system
    (system_definitions keyed_table_comparison_system)"
  using keyed_table_group.rebased_agreement[OF inference_claim_source_formed inference_claim_table_base_agreement]
  by (simp add: keyed_table_comparison_system_def inference_claim_table_system_def)

section \<open>The complete paired projection is a separate closed component\<close>

interpretation inference_claim_projection_group:
  positive_definition_group inference_claim_table_system prefixed_observation_program
  by (rule positive_definition_group.intro)
    (simp, rule schema_system_formed_over_mono[where D="{}"], simp, blast, auto)

definition inference_claim_components :: "(nat,nat,nat,nat) schema_system" where
  "inference_claim_components=system_union inference_claim_table_system prefixed_observation_program"

lemma inference_claim_components_formed [simp]: "schema_system_formed inference_claim_components"
  using inference_claim_projection_group.formed by (simp only: inference_claim_components_def)

lemma inference_claim_components_definitions [simp]:
  "system_definitions inference_claim_components=
    system_definitions inference_claim_table_system\<union>system_definitions prefixed_observation_program"
  by (simp add: inference_claim_components_def)

lemma inference_claim_components_call:
  "schema_call_formed inference_claim_components d t \<longleftrightarrow>
    d\<in>system_definitions inference_claim_components \<and> term_formed t"
  unfolding inference_claim_components_def
  by (rule inference_claim_projection_group.variable_calls[OF inference_claim_table_call prefixed_observation_interfaces])

lemma inference_claim_table_components_agreement:
  "systems_agree_on inference_claim_table_system inference_claim_components
    (system_definitions inference_claim_table_system)"
  using inference_claim_projection_group.old_agreement by (simp only: inference_claim_components_def)

lemma inference_claim_components_inference_agreement:
  "systems_agree_on inference_specialization_system inference_claim_components
    (system_definitions inference_specialization_system)"
  by (rule whole_agreement_transitive[OF inference_claim_inference_agreement],
    rule whole_agreement_transitive[OF inference_claim_source_table_agreement inference_claim_table_components_agreement])

lemma inference_claim_components_join_agreement:
  "systems_agree_on keyed_row_join_system inference_claim_components (system_definitions keyed_row_join_system)"
  by (rule whole_agreement_transitive[OF inference_claim_join_source_agreement],
    rule whole_agreement_transitive[OF inference_claim_source_table_agreement inference_claim_table_components_agreement])

lemma inference_claim_components_table_agreement:
  "systems_agree_on keyed_table_comparison_system inference_claim_components
    (system_definitions keyed_table_comparison_system)"
  by (rule whole_agreement_transitive[OF inference_claim_table_original_agreement inference_claim_table_components_agreement])

lemma inference_claim_component_meanings:
  "(350,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow>
    (350,t)\<in>positive_meaning inference_specialization_system"
  "(21,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(28,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  "(100,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (100,t)\<in>positive_meaning keyed_row_join_system"
  "(353,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (353,t)\<in>positive_meaning keyed_table_comparison_system"
  "(358,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (358,t)\<in>positive_meaning prefixed_observation_program"
proof -
  have inference: "(350,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow>
      (350,t)\<in>positive_meaning inference_specialization_system"
    by (rule whole_system_agreement_meaning[OF inference_specialization_formed inference_claim_components_formed
      inference_claim_components_inference_agreement]) auto
  have join: "(d,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow>
      (d,t)\<in>positive_meaning keyed_row_join_system" if "d\<in>system_definitions keyed_row_join_system" for d
    by (rule whole_system_agreement_meaning[OF keyed_row_join_system_formed inference_claim_components_formed
      inference_claim_components_join_agreement that])
  show "(350,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow>
      (350,t)\<in>positive_meaning inference_specialization_system" by (rule inference)
  show "(21,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
    using join[of 21] keyed_row_join_graph_meaning[of 21 t] proof_graph_membership_old_meaning[of 21 t]
      proof_graph_admission_components(3)[of t] by auto
  show "(28,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
    using join[of 28] keyed_row_join_fibre[of t] by auto
  show "(100,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (100,t)\<in>positive_meaning keyed_row_join_system"
    using join[of 100] by auto
  show "(353,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (353,t)\<in>positive_meaning keyed_table_comparison_system"
    by (rule whole_system_agreement_meaning[OF keyed_table_comparison_formed inference_claim_components_formed
      inference_claim_components_table_agreement]) auto
  have projection: "systems_agree_on prefixed_observation_program inference_claim_components
      (system_definitions prefixed_observation_program)"
    using inference_claim_projection_group.group_agreement by (simp only: inference_claim_components_def)
  show "(358,t)\<in>positive_meaning inference_claim_components \<longleftrightarrow> (358,t)\<in>positive_meaning prefixed_observation_program"
    by (rule whole_system_agreement_meaning[OF prefixed_observation_formed inference_claim_components_formed projection]) auto
qed

text \<open>
  Agreement concerns actual interfaces and complete clause families. Reusing
  the comparison group therefore preserves its existing meaning theorem.
  This combined source also preserves all the original source-reader clauses.
  The local reader will retain the least dependency closure of its own entry.
\<close>

end
