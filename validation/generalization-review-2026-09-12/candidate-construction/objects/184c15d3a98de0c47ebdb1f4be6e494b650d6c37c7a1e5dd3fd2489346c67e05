theory Factor_Data_Product_Components
  imports Factor_Data_Flattening_Contracts Factor_Data_Set_Comparison_Contracts Factor_Component_Agreement
begin

section \<open>Append, flattening, and set comparison share their actual definitions\<close>

lemma data_append_subset_agreement:
  "systems_agree_on data_append_system data_subset_system (system_definitions data_append_system)"
  by (simp add: data_subset_system_def systems_agree_on_added)

lemma data_flatten_subset_agreement:
  "systems_agree_on data_flatten_system data_subset_system
    (system_definitions data_flatten_system\<inter>system_definitions data_subset_system)"
proof -
  have base: "systems_agree_on data_flatten_base_system data_subset_system
      (system_definitions data_flatten_base_system)"
    unfolding data_flatten_base_system_def
    by (rule rooted_agreement_transfer[OF data_append_subset_agreement])
  have overlap: "systems_agree_on data_flatten_base_system data_subset_system
      (system_definitions data_flatten_base_system\<inter>system_definitions data_subset_system)"
    by (rule systems_agree_on_subdomain[OF base]) blast
  show ?thesis unfolding data_flatten_system_def
    by (rule positive_definition_group.extended_overlap_agreement[OF data_flatten_group.positive_definition_group_axioms overlap]) auto
qed

lemma data_set_subset_agreement:
  "systems_agree_on data_set_comparison_system data_subset_system
    (system_definitions data_set_comparison_system\<inter>system_definitions data_subset_system)"
proof -
  have base: "systems_agree_on data_set_comparison_base_system data_subset_system
      (system_definitions data_set_comparison_base_system\<inter>system_definitions data_subset_system)"
    unfolding data_set_comparison_base_system_def by (rule rooted_overlap_agreement) simp
  show ?thesis unfolding data_set_comparison_system_def
    by (rule positive_definition_group.extended_overlap_agreement[OF data_set_comparison_group.positive_definition_group_axioms base]) auto
qed

lemma data_flatten_set_agreement:
  "systems_agree_on data_flatten_system data_set_comparison_system
    (system_definitions data_flatten_system\<inter>system_definitions data_set_comparison_system)"
proof -
  have first: "systems_agree_on data_subset_system data_flatten_system
      (system_definitions data_subset_system\<inter>system_definitions data_flatten_system)"
    using systems_agree_on_sym[OF data_flatten_subset_agreement] by (simp only: Int_commute)
  have second: "systems_agree_on data_subset_system data_set_comparison_system
      (system_definitions data_subset_system\<inter>system_definitions data_set_comparison_system)"
    using systems_agree_on_sym[OF data_set_subset_agreement] by (simp only: Int_commute)
  show ?thesis by (rule common_component_overlap_agreement[OF first second])
    (use data_flatten_base_subdomain data_set_comparison_base_subdomain in auto)
qed

definition data_product_components_system :: "(nat,nat,nat,nat) schema_system" where
  "data_product_components_system=system_union data_flatten_system data_set_comparison_system"

lemma data_product_components_formed [simp]: "schema_system_formed data_product_components_system"
  unfolding data_product_components_system_def
  by (rule system_union_agree_formed[OF data_flatten_system_formed data_set_comparison_system_formed
    data_flatten_set_agreement])

lemma data_product_components_definitions [simp]:
  "system_definitions data_product_components_system=
    system_definitions data_flatten_system\<union>system_definitions data_set_comparison_system"
  by (simp add: data_product_components_system_def)

lemma data_product_components_call:
  "schema_call_formed data_product_components_system d t \<longleftrightarrow>
    d\<in>system_definitions data_product_components_system \<and> term_formed t"
  using system_union_agree_call[OF data_flatten_system_formed data_set_comparison_system_formed
    data_flatten_set_agreement, of d t]
  by (simp only: data_product_components_system_def system_union_definitions data_flatten_call
    data_set_comparison_call Un_iff; blast)

lemma data_product_flatten_meaning:
  assumes "d\<in>system_definitions data_flatten_system"
  shows "(d,t)\<in>positive_meaning data_product_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_flatten_system"
  unfolding data_product_components_system_def
  by (rule system_union_agree_left_locality(2)[OF data_flatten_system_formed data_set_comparison_system_formed
    data_flatten_set_agreement assms])

lemma data_product_set_meaning:
  assumes "d\<in>system_definitions data_set_comparison_system"
  shows "(d,t)\<in>positive_meaning data_product_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_set_comparison_system"
  unfolding data_product_components_system_def
  by (rule system_union_agree_right_locality(2)[OF data_flatten_system_formed data_set_comparison_system_formed
    data_flatten_set_agreement assms])

lemma data_flatten_base_data_roots:
  "{2,4}\<subseteq>system_definitions data_flatten_base_system"
proof -
  have roots: "{46}\<subseteq>system_definitions data_append_system" by auto
  have domain: "system_definitions data_flatten_base_system=system_definition_closure data_append_system {46}"
    unfolding data_flatten_base_system_def data_flatten_external_dependencies
    by (rule rooted_system_definitions[OF data_append_system_formed roots])
  have append: "46\<in>system_definition_closure data_append_system {46}"
    using system_definition_closure_roots[of "{46}" data_append_system] by blast
  have first: "(46,2)\<in>system_dependency_edges data_append_system"
    by (simp only: system_dependency_edges_def mem_Collect_eq case_prod_conv;
        intro exI[of _ 1] exI[of _ data_append_cons_schema])
      (auto simp: data_append_clauses_def data_append_cons_schema_def schema_dependencies_def rel_ran_image)
  have second: "(46,4)\<in>system_dependency_edges data_append_system"
    by (simp only: system_dependency_edges_def mem_Collect_eq case_prod_conv;
        intro exI[of _ 0] exI[of _ data_append_nil_schema])
      (auto simp: data_append_clauses_def data_append_nil_schema_def schema_dependencies_def rel_ran_image)
  show ?thesis using system_definition_closure_step[OF append first]
    system_definition_closure_step[OF append second] by (simp only: domain; blast)
qed

text \<open>
  The common subset program covers every overlap of the two rooted
  components. Agreement passes through the actual append extension, rooted
  restrictions, and fresh groups before the native meanings are joined.
\<close>

end
