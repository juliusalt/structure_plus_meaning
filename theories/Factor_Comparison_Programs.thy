theory Factor_Comparison_Programs
  imports Factor_Target_Comparison Factor_Replay_Reading
begin

section \<open>Local readers compose with the complete replay program\<close>

lemma replay_target_admission_agreement:
  "systems_agree_on target_admission_system replay_reading_system (system_definitions target_admission_system)"
  by (simp add: systems_agree_on_added
    replay_reading_system_def replay_reading_stage_system_def closed_replay_source_system_def
    replay_source_system_def complete_data_admission_system_def package_retention_admission_system_def
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
    target_projection_system_def located_admission_system_def anchored_admission_system_def
    citation_reading_system_def citation_location_system_def citation_interpretation_system_def
    citation_resolution_system_def binding_lookup_system_def artifact_lookup_system_def
    citation_admission_system_def)

lemma comparison_reading_agreement:
  "systems_agree_on replay_reading_system target_collection_system
    (system_definitions replay_reading_system \<inter> system_definitions target_collection_system)"
proof -
  have agreement: "systems_agree_on replay_reading_system target_collection_system
      (system_definitions target_admission_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF replay_target_admission_agreement]
      target_collection_base_agreement])
  have overlap: "system_definitions replay_reading_system \<inter> system_definitions target_collection_system=
      system_definitions target_admission_system" by auto
  show ?thesis using agreement by (simp only: overlap)
qed

definition comparison_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "comparison_reading_system=system_union replay_reading_system target_collection_system"

lemma comparison_reading_system_formed [simp]: "schema_system_formed comparison_reading_system"
  unfolding comparison_reading_system_def
  by (rule system_union_agree_formed[OF replay_reading_system_formed target_collection_system_formed
    comparison_reading_agreement])

lemma comparison_reading_definitions [simp]:
  "system_definitions comparison_reading_system=
    system_definitions replay_reading_system \<union> system_definitions target_collection_system"
  by (simp add: comparison_reading_system_def)

lemma comparison_reading_call:
  "schema_call_formed comparison_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions comparison_reading_system \<and> term_formed t"
  using system_union_agree_call[OF replay_reading_system_formed target_collection_system_formed
    comparison_reading_agreement, of d t]
  by (simp only: comparison_reading_system_def system_union_definitions replay_reading_call
    target_collection_call Un_iff; blast)

theorem comparison_reading_replay_locality:
  assumes "d\<in>system_definitions replay_reading_system"
  shows "schema_call_formed comparison_reading_system d t \<longleftrightarrow> schema_call_formed replay_reading_system d t"
    and "(d,t)\<in>positive_meaning comparison_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning replay_reading_system"
  using system_union_agree_left_locality[OF replay_reading_system_formed target_collection_system_formed
    comparison_reading_agreement assms, of t]
  by (simp_all only: comparison_reading_system_def)

theorem comparison_reading_target_locality:
  assumes "d\<in>system_definitions target_collection_system"
  shows "schema_call_formed comparison_reading_system d t \<longleftrightarrow> schema_call_formed target_collection_system d t"
    and "(d,t)\<in>positive_meaning comparison_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning target_collection_system"
  using system_union_agree_right_locality[OF replay_reading_system_formed target_collection_system_formed
    comparison_reading_agreement assms, of t]
  by (simp_all only: comparison_reading_system_def)

theorem comparison_reading_operations_exact:
  assumes "d\<in>{132,133,134,135,136,137,138}"
  shows "(d,t)\<in>positive_meaning comparison_reading_system \<longleftrightarrow> target_comparison_operation_result d t"
proof -
  have member: "d\<in>system_definitions target_collection_system" using assms by auto
  show ?thesis using comparison_reading_target_locality(2)[OF member, of t]
    target_comparison_operations_exact[OF assms, of t] by blast
qed

section \<open>One fixed native program serves every future complete operand\<close>

theorem native_target_comparison_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {132::nat,133,134,135,136,137,138} \<and>
    (\<forall>d\<in>{132,133,134,135,136,137,138}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> target_comparison_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions comparison_reading_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions comparison_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed comparison_reading_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning comparison_reading_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF comparison_reading_system_formed] by blast
  have sites: "inj_on g {132,133,134,135,136,137,138}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {132,133,134,135,136,137,138}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{132,133,134,135,136,137,138}" and formed: "term_formed t"
    have member: "d\<in>system_definitions comparison_reading_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed comparison_reading_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning comparison_reading_system"
      "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R"
      "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
      using future[rule_format, OF member formed] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> target_comparison_operation_result d t) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts formed member comparison_reading_operations_exact[OF selected]
          in \<open>auto simp: comparison_reading_call\<close>)
  qed
qed

text \<open>
  The bag and target programs are defined and proved at their own boundaries.
  This module separately combines the target collection program with replay.
  Both retain every complete definition and every old call meaning by the
  general shared-definition composition rule. Their common prefix is checked
  structurally through fresh-definition agreement, without revisiting the
  semantic proofs of any lower reader.

  The seven new entries have the same complete contracts in this combined
  program. Native compilation fixes one closed program and distinct entry
  sites before all future formed operands. Every application preserves that
  program's exact original scope, artifacts, and outgoing bindings. No target
  or generation instance is chosen when the program is constructed.
\<close>

end
