theory Factor_Assembly_Components
  imports Factor_Row_Value_Agreement Factor_Structural_Table_Admission Factor_Data_Set_Comparison
begin

section \<open>Table admission retains the actual row-operation program\<close>

interpretation assembly_table_group: positive_definition_group row_values_system structural_table_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF structural_table_group_formed_over,
      where E="system_definitions row_values_system"] in auto)

definition assembly_table_components_system :: "(nat,nat,nat,nat) schema_system" where
  "assembly_table_components_system=system_union row_values_system structural_table_group_system"

lemma assembly_table_components_formed [simp]: "schema_system_formed assembly_table_components_system"
  using assembly_table_group.formed by (simp only: assembly_table_components_system_def)

lemma assembly_table_components_definitions [simp]:
  "system_definitions assembly_table_components_system=
    system_definitions row_values_system\<union>system_definitions structural_table_group_system"
  by (simp add: assembly_table_components_system_def)

lemma assembly_table_components_call:
  "schema_call_formed assembly_table_components_system d t \<longleftrightarrow>
    d\<in>system_definitions assembly_table_components_system \<and> term_formed t"
  unfolding assembly_table_components_system_def
  by (rule assembly_table_group.variable_calls[OF row_values_call structural_table_group_interfaces])

lemma assembly_table_components_row_agreement:
  "systems_agree_on row_values_system assembly_table_components_system (system_definitions row_values_system)"
  using assembly_table_group.old_agreement by (simp only: assembly_table_components_system_def)

lemma assembly_table_components_table_agreement:
  "systems_agree_on structural_table_system assembly_table_components_system (system_definitions structural_table_system)"
proof -
  have original: "systems_agree_on structural_table_base_system keyed_list_system
      (system_definitions structural_table_base_system)"
    unfolding structural_table_base_system_def by (rule systems_agree_on_sym[OF rooted_system_agreement])
  have continued: "systems_agree_on keyed_list_system row_values_system
      (system_definitions structural_table_base_system)"
    by (rule systems_agree_on_subdomain[OF row_values_keyed_agreement structural_table_base_subdomain])
  have base: "systems_agree_on structural_table_base_system row_values_system
      (system_definitions structural_table_base_system)"
    by (rule systems_agree_on_transitive[OF original continued])
  show ?thesis using structural_table_group.rebased_agreement[OF row_values_system_formed base]
    by (simp add: structural_table_system_def assembly_table_components_system_def)
qed

section \<open>Set comparison retains the same complete inclusion definition\<close>

interpretation assembly_comparison_group:
  positive_definition_group assembly_table_components_system data_set_comparison_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF data_set_comparison_group_formed_over,
      where E="system_definitions assembly_table_components_system"] in auto)

definition assembly_components_system :: "(nat,nat,nat,nat) schema_system" where
  "assembly_components_system=system_union assembly_table_components_system data_set_comparison_group_system"

lemma assembly_components_formed [simp]: "schema_system_formed assembly_components_system"
  using assembly_comparison_group.formed by (simp only: assembly_components_system_def)

lemma assembly_components_definitions [simp]:
  "system_definitions assembly_components_system=
    system_definitions assembly_table_components_system\<union>system_definitions data_set_comparison_group_system"
  by (simp add: assembly_components_system_def)

lemma assembly_components_call:
  "schema_call_formed assembly_components_system d t \<longleftrightarrow>
    d\<in>system_definitions assembly_components_system \<and> term_formed t"
  unfolding assembly_components_system_def
  by (rule assembly_comparison_group.variable_calls[OF assembly_table_components_call]) auto

lemma assembly_components_prefix_agreement:
  "systems_agree_on assembly_table_components_system assembly_components_system
    (system_definitions assembly_table_components_system)"
  using assembly_comparison_group.old_agreement by (simp only: assembly_components_system_def)

lemma assembly_components_row_agreement:
  "systems_agree_on row_values_system assembly_components_system (system_definitions row_values_system)"
proof (rule systems_agree_on_transitive[OF assembly_table_components_row_agreement])
  show "systems_agree_on assembly_table_components_system assembly_components_system (system_definitions row_values_system)"
    by (rule systems_agree_on_subdomain[OF assembly_components_prefix_agreement]) auto
qed

lemma assembly_components_table_agreement:
  "systems_agree_on structural_table_system assembly_components_system (system_definitions structural_table_system)"
proof (rule systems_agree_on_transitive[OF assembly_table_components_table_agreement])
  show "systems_agree_on assembly_table_components_system assembly_components_system
      (system_definitions structural_table_system)"
    by (rule systems_agree_on_subdomain[OF assembly_components_prefix_agreement])
      (use structural_table_base_subdomain in auto)
qed

lemma assembly_components_comparison_agreement:
  "systems_agree_on data_set_comparison_system assembly_components_system (system_definitions data_set_comparison_system)"
proof -
  have original: "systems_agree_on data_set_comparison_base_system data_subset_system
      (system_definitions data_set_comparison_base_system)"
    unfolding data_set_comparison_base_system_def by (rule systems_agree_on_sym[OF rooted_system_agreement])
  have continued: "systems_agree_on data_subset_system row_values_system
      (system_definitions data_set_comparison_base_system)"
    by (rule systems_agree_on_subdomain[OF row_values_subset_agreement data_set_comparison_base_subdomain])
  have suffix: "systems_agree_on row_values_system assembly_table_components_system
      (system_definitions data_set_comparison_base_system)"
    by (rule systems_agree_on_subdomain[OF assembly_table_components_row_agreement])
      (use data_set_comparison_base_subdomain in auto)
  have base: "systems_agree_on data_set_comparison_base_system assembly_table_components_system
      (system_definitions data_set_comparison_base_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_transitive[OF original continued] suffix])
  show ?thesis using data_set_comparison_group.rebased_agreement[OF assembly_table_components_formed base]
    by (simp add: data_set_comparison_system_def assembly_components_system_def)
qed

lemma assembly_components_row_meaning:
  assumes "d\<in>system_definitions row_values_system"
  shows "(d,t)\<in>positive_meaning assembly_components_system \<longleftrightarrow> (d,t)\<in>positive_meaning row_values_system"
  by (rule whole_system_agreement_meaning[OF row_values_system_formed assembly_components_formed
    assembly_components_row_agreement assms])

lemma assembly_components_table_meaning:
  assumes "d\<in>system_definitions structural_table_system"
  shows "(d,t)\<in>positive_meaning assembly_components_system \<longleftrightarrow> (d,t)\<in>positive_meaning structural_table_system"
  by (rule whole_system_agreement_meaning[OF structural_table_system_formed assembly_components_formed
    assembly_components_table_agreement assms])

lemma assembly_components_comparison_meaning:
  assumes "d\<in>system_definitions data_set_comparison_system"
  shows "(d,t)\<in>positive_meaning assembly_components_system \<longleftrightarrow> (d,t)\<in>positive_meaning data_set_comparison_system"
  by (rule whole_system_agreement_meaning[OF data_set_comparison_system_formed assembly_components_formed
    assembly_components_comparison_agreement assms])

text \<open>
  The combined source contains the existing row operations and the two closed
  groups for table admission and set comparison. Rebasing preserves each
  group's entire original base, interface, and clause family. The agreements
  therefore support reuse of each component's complete semantic contract.
  The later assembly clauses will select their least actual dependency closure.
\<close>

end
