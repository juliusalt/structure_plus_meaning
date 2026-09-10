theory Factor_Observation_Table_Components
  imports Factor_Data_Product_Contracts Factor_Observation_Scope_Contracts Factor_Observation_Collection_Contracts
begin

section \<open>The shared computation base retains each original definition\<close>

lemma data_flatten_absence_agreement:
  "systems_agree_on data_flatten_system data_absence_system
    (system_definitions data_flatten_system\<inter>system_definitions data_absence_system)"
proof -
  have first: "systems_agree_on data_subset_system data_flatten_system
      (system_definitions data_subset_system\<inter>system_definitions data_flatten_system)"
    using systems_agree_on_sym[OF data_flatten_subset_agreement] by (simp only: Int_commute)
  show ?thesis by (rule common_component_overlap_agreement[OF first data_subset_absence_agreement])
    (use data_flatten_base_subdomain in auto)
qed

lemma observation_flatten_agreement:
  "systems_agree_on observation_system data_flatten_system
    (system_definitions observation_system\<inter>system_definitions data_flatten_system)"
proof -
  have reverse: "systems_agree_on data_absence_system data_flatten_system
      (system_definitions data_absence_system\<inter>system_definitions data_flatten_system)"
    using systems_agree_on_sym[OF data_flatten_absence_agreement] by (simp only: Int_commute)
  have base: "systems_agree_on observation_base_system data_flatten_system
      (system_definitions observation_base_system\<inter>system_definitions data_flatten_system)"
    unfolding observation_base_system_def by (rule rooted_overlap_agreement[OF reverse])
  show ?thesis unfolding observation_system_def
    by (rule positive_definition_group.extended_overlap_agreement[OF observation_group.positive_definition_group_axioms base])
      (use data_flatten_base_subdomain in auto)
qed

lemma observation_collection_flatten_agreement:
  "systems_agree_on observation_collection_system data_flatten_system
    (system_definitions observation_collection_system\<inter>system_definitions data_flatten_system)"
proof -
  have reverse: "systems_agree_on data_set_comparison_system data_flatten_system
      (system_definitions data_set_comparison_system\<inter>system_definitions data_flatten_system)"
    using systems_agree_on_sym[OF data_flatten_set_agreement] by (simp only: Int_commute)
  show ?thesis unfolding observation_collection_system_def
    by (rule overlap_agreement_union[OF observation_system_formed data_set_comparison_system_formed
      observation_flatten_agreement reverse])
qed

definition observation_table_common_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_common_system=system_union observation_collection_system data_flatten_system"

lemma observation_table_common_formed [simp]: "schema_system_formed observation_table_common_system"
  unfolding observation_table_common_system_def
  by (rule system_union_agree_formed[OF observation_collection_formed data_flatten_system_formed
    observation_collection_flatten_agreement])

lemma observation_table_common_definitions [simp]:
  "system_definitions observation_table_common_system=
    system_definitions observation_collection_system\<union>system_definitions data_flatten_system"
  by (simp add: observation_table_common_system_def)

lemma observation_table_common_call:
  "schema_call_formed observation_table_common_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_common_system \<and> term_formed t"
  using system_union_agree_call[OF observation_collection_formed data_flatten_system_formed
    observation_collection_flatten_agreement, of d t]
  by (simp only: observation_table_common_system_def system_union_definitions observation_collection_call
    data_flatten_call Un_iff; blast)

lemma observation_table_common_observation_agreement:
  "systems_agree_on observation_collection_system observation_table_common_system
    (system_definitions observation_collection_system)"
  unfolding observation_table_common_system_def
  by (rule system_union_agree_left[OF data_flatten_system_formed observation_collection_flatten_agreement])

lemma observation_table_common_flatten_agreement:
  "systems_agree_on data_flatten_system observation_table_common_system (system_definitions data_flatten_system)"
proof -
  have reverse: "systems_agree_on data_flatten_system observation_collection_system
      (system_definitions data_flatten_system\<inter>system_definitions observation_collection_system)"
    using systems_agree_on_sym[OF observation_collection_flatten_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF observation_collection_formed reverse]
    by (simp only: observation_table_common_system_def system_union_commute)
qed

lemma observation_table_common_set_agreement:
  "systems_agree_on data_set_comparison_system observation_table_common_system
    (system_definitions data_set_comparison_system)"
proof -
  have reverse: "systems_agree_on data_set_comparison_system observation_system
      (system_definitions data_set_comparison_system\<inter>system_definitions observation_system)"
    using systems_agree_on_sym[OF observation_set_agreement] by (simp only: Int_commute)
  have first: "systems_agree_on data_set_comparison_system observation_collection_system
      (system_definitions data_set_comparison_system)"
    using system_union_agree_left[OF observation_system_formed reverse]
    by (simp only: observation_collection_system_def system_union_commute)
  show ?thesis by (rule whole_agreement_transitive[OF first observation_table_common_observation_agreement])
qed

lemma observation_table_common_product_agreement:
  "systems_agree_on data_product_components_system observation_table_common_system
    (system_definitions data_product_components_system)"
  unfolding data_product_components_system_def
  by (rule whole_agreement_union[OF data_flatten_system_formed data_set_comparison_system_formed
    observation_table_common_flatten_agreement observation_table_common_set_agreement])

section \<open>The existing product group is rebased through whole agreement\<close>

lemma observation_table_product_base_agreement:
  "systems_agree_on data_product_base_system observation_table_common_system (system_definitions data_product_base_system)"
  unfolding data_product_base_system_def by (rule rooted_agreement_transfer[OF observation_table_common_product_agreement])

interpretation observation_table_product_group: positive_definition_group observation_table_common_system data_product_group_system
proof (rule positive_definition_group.rebased_group[OF data_product_group.positive_definition_group_axioms
    observation_table_common_formed observation_table_product_base_agreement])
  show "system_definitions observation_table_common_system\<inter>system_definitions data_product_group_system={}"
    using observation_base_subdomain data_set_comparison_base_subdomain data_flatten_base_subdomain by auto
qed

definition observation_table_product_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_product_system=system_union observation_table_common_system data_product_group_system"

lemma observation_table_product_formed [simp]: "schema_system_formed observation_table_product_system"
  using observation_table_product_group.formed by (simp only: observation_table_product_system_def)

lemma observation_table_product_definitions [simp]:
  "system_definitions observation_table_product_system=system_definitions observation_table_common_system\<union>{318,319,320,321,322,323,324,325}"
  by (simp add: observation_table_product_system_def)

lemma observation_table_product_call:
  "schema_call_formed observation_table_product_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_product_system \<and> term_formed t"
  unfolding observation_table_product_system_def
  by (rule observation_table_product_group.variable_calls[where D="{318,319,320,321,322,323,324,325}" and a=0, OF observation_table_common_call]) auto

lemma observation_table_product_old_agreement:
  "systems_agree_on observation_table_common_system observation_table_product_system (system_definitions observation_table_common_system)"
  using observation_table_product_group.old_agreement by (simp only: observation_table_product_system_def)

lemma observation_table_product_observation_agreement:
  "systems_agree_on observation_collection_system observation_table_product_system (system_definitions observation_collection_system)"
  by (rule whole_agreement_transitive[OF observation_table_common_observation_agreement observation_table_product_old_agreement])

lemma observation_table_product_original_agreement:
  "systems_agree_on data_product_system observation_table_product_system (system_definitions data_product_system)"
proof -
  have fresh: "system_definitions observation_table_common_system\<inter>system_definitions data_product_group_system={}"
    using observation_table_product_group.separate by blast
  show ?thesis using data_product_group.rebased_agreement[OF observation_table_common_formed observation_table_product_base_agreement fresh]
    by (simp only: data_product_system_def observation_table_product_system_def)
qed

section \<open>The existing scope group is rebased through whole agreement\<close>

lemma observation_table_scope_base_agreement:
  "systems_agree_on observation_scope_base_system observation_table_product_system (system_definitions observation_scope_base_system)"
  unfolding observation_scope_base_system_def by (rule rooted_agreement_transfer[OF observation_table_product_observation_agreement])

interpretation observation_table_scope_group: positive_definition_group observation_table_product_system observation_scope_group_system
proof (rule positive_definition_group.rebased_group[OF observation_scope_group.positive_definition_group_axioms
    observation_table_product_formed observation_table_scope_base_agreement])
  show "system_definitions observation_table_product_system\<inter>system_definitions observation_scope_group_system={}"
    using observation_base_subdomain data_set_comparison_base_subdomain data_flatten_base_subdomain by auto
qed

definition observation_table_scope_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_scope_system=system_union observation_table_product_system observation_scope_group_system"

lemma observation_table_scope_formed [simp]: "schema_system_formed observation_table_scope_system"
  using observation_table_scope_group.formed by (simp only: observation_table_scope_system_def)

lemma observation_table_scope_definitions [simp]:
  "system_definitions observation_table_scope_system=system_definitions observation_table_product_system\<union>{308,309,310,311}"
  by (simp add: observation_table_scope_system_def)

lemma observation_table_scope_call:
  "schema_call_formed observation_table_scope_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_scope_system \<and> term_formed t"
  unfolding observation_table_scope_system_def
  by (rule observation_table_scope_group.variable_calls[where D="{308,309,310,311}" and a=0, OF observation_table_product_call]) auto

lemma observation_table_scope_old_agreement:
  "systems_agree_on observation_table_product_system observation_table_scope_system (system_definitions observation_table_product_system)"
  using observation_table_scope_group.old_agreement by (simp only: observation_table_scope_system_def)

lemma observation_table_scope_observation_agreement:
  "systems_agree_on observation_collection_system observation_table_scope_system (system_definitions observation_collection_system)"
  by (rule whole_agreement_transitive[OF observation_table_product_observation_agreement observation_table_scope_old_agreement])

lemma observation_table_scope_original_agreement:
  "systems_agree_on observation_scope_system observation_table_scope_system (system_definitions observation_scope_system)"
proof -
  have fresh: "system_definitions observation_table_product_system\<inter>system_definitions observation_scope_group_system={}"
    using observation_table_scope_group.separate by blast
  show ?thesis using observation_scope_group.rebased_agreement[OF observation_table_product_formed observation_table_scope_base_agreement fresh]
    by (simp only: observation_scope_system_def observation_table_scope_system_def)
qed

section \<open>The existing keyed group is rebased through whole agreement\<close>

lemma observation_table_components_base_agreement:
  "systems_agree_on keyed_set_base_system observation_table_scope_system (system_definitions keyed_set_base_system)"
  unfolding keyed_set_base_system_def by (rule rooted_agreement_transfer[OF observation_table_scope_observation_agreement])

interpretation observation_table_components_group: positive_definition_group observation_table_scope_system keyed_set_group_system
proof (rule positive_definition_group.rebased_group[OF keyed_set_group.positive_definition_group_axioms
    observation_table_scope_formed observation_table_components_base_agreement])
  show "system_definitions observation_table_scope_system\<inter>system_definitions keyed_set_group_system={}"
    using observation_base_subdomain data_set_comparison_base_subdomain data_flatten_base_subdomain by auto
qed

definition observation_table_components_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_components_system=system_union observation_table_scope_system keyed_set_group_system"

lemma observation_table_components_formed [simp]: "schema_system_formed observation_table_components_system"
  using observation_table_components_group.formed by (simp only: observation_table_components_system_def)

lemma observation_table_components_definitions [simp]:
  "system_definitions observation_table_components_system=system_definitions observation_table_scope_system\<union>{312,313,314,315,316,317}"
  by (simp add: observation_table_components_system_def)

lemma observation_table_components_call:
  "schema_call_formed observation_table_components_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_components_system \<and> term_formed t"
  unfolding observation_table_components_system_def
  by (rule observation_table_components_group.variable_calls[where D="{312,313,314,315,316,317}" and a=0, OF observation_table_scope_call]) auto

lemma observation_table_components_old_agreement:
  "systems_agree_on observation_table_scope_system observation_table_components_system (system_definitions observation_table_scope_system)"
  using observation_table_components_group.old_agreement by (simp only: observation_table_components_system_def)

lemma observation_table_components_observation_agreement:
  "systems_agree_on observation_collection_system observation_table_components_system (system_definitions observation_collection_system)"
  by (rule whole_agreement_transitive[OF observation_table_scope_observation_agreement observation_table_components_old_agreement])

lemma observation_table_components_original_agreement:
  "systems_agree_on keyed_set_system observation_table_components_system (system_definitions keyed_set_system)"
proof -
  have fresh: "system_definitions observation_table_scope_system\<inter>system_definitions keyed_set_group_system={}"
    using observation_table_components_group.separate by blast
  show ?thesis using keyed_set_group.rebased_agreement[OF observation_table_scope_formed observation_table_components_base_agreement fresh]
    by (simp only: keyed_set_system_def observation_table_components_system_def)
qed

section \<open>The resulting program preserves all four operation owners\<close>

lemma observation_table_components_product_agreement:
  "systems_agree_on data_product_system observation_table_components_system (system_definitions data_product_system)"
  by (rule whole_agreement_transitive[OF whole_agreement_transitive[
    OF observation_table_product_original_agreement observation_table_scope_old_agreement]
    observation_table_components_old_agreement])

lemma observation_table_components_scope_agreement:
  "systems_agree_on observation_scope_system observation_table_components_system (system_definitions observation_scope_system)"
  by (rule whole_agreement_transitive[OF observation_table_scope_original_agreement observation_table_components_old_agreement])

lemma observation_table_components_observation_meaning:
  assumes "d\<in>system_definitions observation_system"
  shows "(d,t)\<in>positive_meaning observation_table_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning observation_system"
proof -
  have member: "d\<in>system_definitions observation_collection_system" using assms by auto
  have original: "(d,t)\<in>positive_meaning observation_table_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning observation_collection_system"
    by (rule whole_system_agreement_meaning[OF observation_collection_formed observation_table_components_formed
      observation_table_components_observation_agreement member])
  show ?thesis by (simp only: original observation_collection_meaning[OF assms])
qed

lemma observation_table_components_scope_meaning:
  "(311,t)\<in>positive_meaning observation_table_components_system \<longleftrightarrow>
    (311,t)\<in>positive_meaning observation_scope_system"
  by (rule whole_system_agreement_meaning[OF observation_scope_system_formed observation_table_components_formed
    observation_table_components_scope_agreement]) auto

lemma observation_table_components_keyed_meaning:
  "(317,t)\<in>positive_meaning observation_table_components_system \<longleftrightarrow>
    (317,t)\<in>positive_meaning keyed_set_system"
  by (rule whole_system_agreement_meaning[OF keyed_set_system_formed observation_table_components_formed
    observation_table_components_original_agreement]) auto

lemma observation_table_components_product_meaning:
  "(324,t)\<in>positive_meaning observation_table_components_system \<longleftrightarrow>
    (324,t)\<in>positive_meaning data_product_system"
  by (rule whole_system_agreement_meaning[OF data_product_system_formed observation_table_components_formed
    observation_table_components_product_agreement]) auto

text \<open>
  The common program first joins actual observation and collection operations
  with flattening. Each existing product, scope, and keyed comparison group
  is then rebased using its whole rooted-base agreement and fresh coordinates.
  The generic group contract preserves the entire original program at each
  step. The resulting parent exposes profile calculation, loss calculation,
  complete input admission, Cartesian enumeration, and nested comparison
  with their original clauses and independently proved meanings intact.
\<close>

end
