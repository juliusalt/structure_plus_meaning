theory Factor_Construction_Components
  imports Factor_Source_Contracts Factor_Fragment_Contracts Factor_Assembly_Contracts
    Factor_Component_Agreement
begin

section \<open>The existing common ancestors retain their actual definitions\<close>

lemma row_values_key_fibre_agreement:
  "systems_agree_on key_fibre_system row_values_system (system_definitions key_fibre_system)"
proof -
  have prefix: "systems_agree_on key_fibre_system data_append_system (system_definitions key_fibre_system)"
    by (simp add: data_append_system_def target_projection_system_def located_admission_system_def
      anchored_admission_system_def citation_reading_system_def citation_location_system_def
      citation_interpretation_system_def citation_resolution_system_def binding_lookup_system_def
      artifact_lookup_system_def citation_admission_system_def target_admission_system_def
      record_admission_system_def socket_chain_system_def family_admission_system_def
      family_sockets_system_def family_socket_system_def headed_material_system_def systems_agree_on_added)
  show ?thesis by (rule whole_agreement_transitive[OF prefix row_values_append_agreement])
qed

definition construction_sequence_components :: "(nat,nat,nat,nat) schema_system" where
  "construction_sequence_components=system_union assembly_components_system term_sequence_system"

lemma construction_sequence_components_formed [simp]: "schema_system_formed construction_sequence_components"
  unfolding construction_sequence_components_def
  by (rule system_union_formed[OF assembly_components_formed term_sequence_system_formed]) auto

lemma construction_sequence_components_definitions [simp]:
  "system_definitions construction_sequence_components=
    system_definitions assembly_components_system\<union>system_definitions term_sequence_system"
  by (simp add: construction_sequence_components_def)

lemma construction_sequence_components_call:
  "schema_call_formed construction_sequence_components d t \<longleftrightarrow>
    d\<in>system_definitions construction_sequence_components \<and> term_formed t"
proof -
  have agreement: "systems_agree_on assembly_components_system term_sequence_system
      (system_definitions assembly_components_system\<inter>system_definitions term_sequence_system)"
    by (simp add: systems_agree_on_def)
  have call: "schema_call_formed construction_sequence_components d t \<longleftrightarrow>
      schema_call_formed assembly_components_system d t \<or> schema_call_formed term_sequence_system d t"
    by (simp only: construction_sequence_components_def
      system_union_agree_call[OF assembly_components_formed term_sequence_system_formed agreement])
  show ?thesis by (simp only: call construction_sequence_components_definitions
    assembly_components_call term_sequence_call Un_iff; blast)
qed

lemma construction_sequence_assembly_agreement:
  "systems_agree_on assembly_components_system construction_sequence_components
    (system_definitions assembly_components_system)"
  unfolding construction_sequence_components_def
  by (rule system_union_left_agreement[OF term_sequence_system_formed]) auto

lemma construction_sequence_term_agreement:
  "systems_agree_on term_sequence_system construction_sequence_components (system_definitions term_sequence_system)"
  unfolding construction_sequence_components_def
  by (subst system_union_commute, rule system_union_left_agreement[OF assembly_components_formed]) auto

lemma construction_sequence_row_agreement:
  "systems_agree_on row_values_system construction_sequence_components (system_definitions row_values_system)"
  by (rule whole_agreement_transitive[OF assembly_components_row_agreement construction_sequence_assembly_agreement])

lemma construction_sequence_key_agreement:
  "systems_agree_on key_fibre_system construction_sequence_components (system_definitions key_fibre_system)"
  by (rule whole_agreement_transitive[OF row_values_key_fibre_agreement construction_sequence_row_agreement])

lemma construction_sequence_artifact_agreement:
  "systems_agree_on artifact_identity_system construction_sequence_components (system_definitions artifact_identity_system)"
  by (rule whole_agreement_transitive[OF row_values_artifact_agreement construction_sequence_row_agreement])

lemma construction_sequence_bag_agreement:
  "systems_agree_on bag_comparison_system construction_sequence_components (system_definitions bag_comparison_system)"
  by (rule whole_agreement_transitive[OF row_values_bag_agreement construction_sequence_row_agreement])

lemma construction_bag_component_agreement:
  "systems_agree_on construction_sequence_components bag_difference_system
    (system_definitions construction_sequence_components\<inter>system_definitions bag_difference_system)"
proof (rule common_component_overlap_agreement[where B=bag_comparison_system])
  show "systems_agree_on bag_comparison_system construction_sequence_components
      (system_definitions bag_comparison_system\<inter>system_definitions construction_sequence_components)"
    by (rule systems_agree_on_subdomain[OF construction_sequence_bag_agreement]) blast
  show "systems_agree_on bag_comparison_system bag_difference_system
      (system_definitions bag_comparison_system\<inter>system_definitions bag_difference_system)"
    by (rule systems_agree_on_subdomain[OF bag_difference_base_agreement]) blast
  show "system_definitions construction_sequence_components\<inter>system_definitions bag_difference_system
      \<subseteq>system_definitions bag_comparison_system" by auto
qed

definition construction_component_base :: "(nat,nat,nat,nat) schema_system" where
  "construction_component_base=system_union construction_sequence_components bag_difference_system"

lemma construction_component_base_formed [simp]: "schema_system_formed construction_component_base"
  unfolding construction_component_base_def
  by (rule system_union_agree_formed[OF construction_sequence_components_formed bag_difference_system_formed
    construction_bag_component_agreement])

lemma construction_component_base_definitions [simp]:
  "system_definitions construction_component_base=
    system_definitions construction_sequence_components\<union>system_definitions bag_difference_system"
  by (simp add: construction_component_base_def)

lemma construction_component_base_call:
  "schema_call_formed construction_component_base d t \<longleftrightarrow>
    d\<in>system_definitions construction_component_base \<and> term_formed t"
proof -
  have call: "schema_call_formed construction_component_base d t \<longleftrightarrow>
      schema_call_formed construction_sequence_components d t \<or> schema_call_formed bag_difference_system d t"
    by (simp only: construction_component_base_def
      system_union_agree_call[OF construction_sequence_components_formed bag_difference_system_formed construction_bag_component_agreement])
  show ?thesis by (simp only: call construction_component_base_definitions
    construction_sequence_components_call bag_difference_call Un_iff; blast)
qed

lemma construction_base_sequence_agreement:
  "systems_agree_on construction_sequence_components construction_component_base
    (system_definitions construction_sequence_components)"
  unfolding construction_component_base_def
  by (rule system_union_agree_left[OF bag_difference_system_formed construction_bag_component_agreement])

lemma construction_base_bag_agreement:
  "systems_agree_on bag_difference_system construction_component_base (system_definitions bag_difference_system)"
  unfolding construction_component_base_def
  by (subst system_union_commute, rule system_union_agree_left[OF construction_sequence_components_formed])
    (use systems_agree_on_sym[OF construction_bag_component_agreement] in \<open>simp only: Int_commute\<close>)

lemma construction_base_source_agreement:
  "systems_agree_on source_components_system construction_component_base (system_definitions source_components_system)"
proof -
  have keys: "systems_agree_on key_fibre_system construction_component_base (system_definitions key_fibre_system)"
    by (rule whole_agreement_transitive[OF construction_sequence_key_agreement construction_base_sequence_agreement])
  have terms: "systems_agree_on term_sequence_system construction_component_base (system_definitions term_sequence_system)"
    by (rule whole_agreement_transitive[OF construction_sequence_term_agreement construction_base_sequence_agreement])
  show ?thesis unfolding source_components_system_def
    by (rule whole_agreement_union[OF key_fibre_system_formed term_sequence_system_formed keys terms])
qed

lemma construction_base_fragment_agreement:
  "systems_agree_on artifact_difference_base_system construction_component_base
    (system_definitions artifact_difference_base_system)"
proof -
  have artifacts: "systems_agree_on artifact_identity_system construction_component_base
      (system_definitions artifact_identity_system)"
    by (rule whole_agreement_transitive[OF construction_sequence_artifact_agreement construction_base_sequence_agreement])
  show ?thesis unfolding artifact_difference_base_system_def
    by (rule whole_agreement_union[OF artifact_identity_system_formed bag_difference_system_formed
      artifacts construction_base_bag_agreement])
qed

lemma construction_base_assembly_agreement:
  "systems_agree_on assembly_components_system construction_component_base (system_definitions assembly_components_system)"
  by (rule whole_agreement_transitive[OF construction_sequence_assembly_agreement construction_base_sequence_agreement])

section \<open>Three independent groups reuse that complete base\<close>

lemma construction_fragment_base_agreement:
  "systems_agree_on fragment_base_system construction_component_base (system_definitions fragment_base_system)"
  unfolding fragment_base_system_def by (rule rooted_agreement_transfer[OF construction_base_fragment_agreement])

interpretation construction_fragment_group: positive_definition_group construction_component_base fragment_group_system
  by (rule positive_definition_group.rebased_group[OF fragment_group.positive_definition_group_axioms construction_component_base_formed construction_fragment_base_agreement]) auto

definition construction_fragment_components :: "(nat,nat,nat,nat) schema_system" where
  "construction_fragment_components=system_union construction_component_base fragment_group_system"

lemma construction_fragment_components_formed [simp]: "schema_system_formed construction_fragment_components"
  using construction_fragment_group.formed by (simp only: construction_fragment_components_def)

lemma construction_fragment_components_definitions [simp]:
  "system_definitions construction_fragment_components=
    system_definitions construction_component_base\<union>system_definitions fragment_group_system"
  by (simp add: construction_fragment_components_def)

lemma construction_fragment_components_call:
  "schema_call_formed construction_fragment_components d t \<longleftrightarrow>
    d\<in>system_definitions construction_fragment_components \<and> term_formed t"
  unfolding construction_fragment_components_def
  by (rule construction_fragment_group.variable_calls[OF construction_component_base_call fragment_group_interfaces])

lemma construction_fragment_prefix_agreement:
  "systems_agree_on construction_component_base construction_fragment_components (system_definitions construction_component_base)"
  using construction_fragment_group.old_agreement by (simp only: construction_fragment_components_def)

lemma construction_fragment_original_agreement:
  "systems_agree_on fragment_system construction_fragment_components (system_definitions fragment_system)"
  using fragment_group.rebased_agreement[OF construction_component_base_formed construction_fragment_base_agreement]
  by (simp add: fragment_system_def construction_fragment_components_def)

lemma construction_source_base_agreement:
  "systems_agree_on source_base_system construction_fragment_components (system_definitions source_base_system)"
proof -
  have whole: "systems_agree_on source_components_system construction_fragment_components
      (system_definitions source_components_system)"
    by (rule whole_agreement_transitive[OF construction_base_source_agreement construction_fragment_prefix_agreement])
  show ?thesis unfolding source_base_system_def by (rule rooted_agreement_transfer[OF whole])
qed

interpretation construction_source_group: positive_definition_group construction_fragment_components source_group_system
  by (rule positive_definition_group.rebased_group[OF source_group.positive_definition_group_axioms construction_fragment_components_formed construction_source_base_agreement]) auto

definition construction_source_components :: "(nat,nat,nat,nat) schema_system" where
  "construction_source_components=system_union construction_fragment_components source_group_system"

lemma construction_source_components_formed [simp]: "schema_system_formed construction_source_components"
  using construction_source_group.formed by (simp only: construction_source_components_def)

lemma construction_source_components_definitions [simp]:
  "system_definitions construction_source_components=
    system_definitions construction_fragment_components\<union>system_definitions source_group_system"
  by (simp add: construction_source_components_def)

lemma construction_source_components_call:
  "schema_call_formed construction_source_components d t \<longleftrightarrow>
    d\<in>system_definitions construction_source_components \<and> term_formed t"
  unfolding construction_source_components_def
  by (rule construction_source_group.variable_calls[OF construction_fragment_components_call source_group_interfaces])

lemma construction_source_prefix_agreement:
  "systems_agree_on construction_fragment_components construction_source_components
    (system_definitions construction_fragment_components)"
  using construction_source_group.old_agreement by (simp only: construction_source_components_def)

lemma construction_source_original_agreement:
  "systems_agree_on source_system construction_source_components (system_definitions source_system)"
  using source_group.rebased_agreement[OF construction_fragment_components_formed construction_source_base_agreement]
  by (simp add: source_system_def construction_source_components_def)

lemma construction_assembly_base_agreement:
  "systems_agree_on assembly_base_system construction_source_components (system_definitions assembly_base_system)"
proof -
  have first: "systems_agree_on assembly_components_system construction_fragment_components
      (system_definitions assembly_components_system)"
    by (rule whole_agreement_transitive[OF construction_base_assembly_agreement construction_fragment_prefix_agreement])
  have whole: "systems_agree_on assembly_components_system construction_source_components
      (system_definitions assembly_components_system)"
    by (rule whole_agreement_transitive[OF first construction_source_prefix_agreement])
  show ?thesis unfolding assembly_base_system_def by (rule rooted_agreement_transfer[OF whole])
qed

interpretation construction_assembly_group: positive_definition_group construction_source_components assembly_group_system
  by (rule positive_definition_group.rebased_group[OF assembly_group.positive_definition_group_axioms construction_source_components_formed construction_assembly_base_agreement]) auto

definition construction_components_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_components_system=system_union construction_source_components assembly_group_system"

lemma construction_components_formed [simp]: "schema_system_formed construction_components_system"
  using construction_assembly_group.formed by (simp only: construction_components_system_def)

lemma construction_components_definitions [simp]:
  "system_definitions construction_components_system=
    system_definitions construction_source_components\<union>system_definitions assembly_group_system"
  by (simp add: construction_components_system_def)

lemma construction_components_call:
  "schema_call_formed construction_components_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_components_system \<and> term_formed t"
  unfolding construction_components_system_def
  by (rule construction_assembly_group.variable_calls[OF construction_source_components_call assembly_group_interfaces])

lemma construction_components_prefix_agreement:
  "systems_agree_on construction_source_components construction_components_system
    (system_definitions construction_source_components)"
  using construction_assembly_group.old_agreement by (simp only: construction_components_system_def)

lemma construction_components_source_agreement:
  "systems_agree_on source_system construction_components_system (system_definitions source_system)"
  by (rule whole_agreement_transitive[OF construction_source_original_agreement construction_components_prefix_agreement])

lemma construction_components_fragment_agreement:
  "systems_agree_on fragment_system construction_components_system (system_definitions fragment_system)"
  by (rule whole_agreement_transitive[OF construction_fragment_original_agreement],
      rule whole_agreement_transitive[OF construction_source_prefix_agreement construction_components_prefix_agreement])

lemma construction_components_assembly_agreement:
  "systems_agree_on assembly_checking_system construction_components_system (system_definitions assembly_checking_system)"
  using assembly_group.rebased_agreement[OF construction_source_components_formed construction_assembly_base_agreement]
  by (simp add: assembly_checking_system_def construction_components_system_def)

lemma construction_component_meanings:
  "(1,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
  "(6,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(10,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(21,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(205,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (205,t)\<in>positive_meaning fragment_system"
  "(206,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (206,t)\<in>positive_meaning fragment_system"
  "(230,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (230,t)\<in>positive_meaning assembly_checking_system"
  "(233,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
  "(242,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (242,t)\<in>positive_meaning source_system"
  "(244,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (244,t)\<in>positive_meaning source_system"
proof -
  have sources: "(d,t)\<in>positive_meaning construction_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning source_system" if "d\<in>system_definitions source_system" for d
    by (rule whole_system_agreement_meaning[OF source_system_formed construction_components_formed
      construction_components_source_agreement that])
  have fragments: "(d,t)\<in>positive_meaning construction_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning fragment_system" if "d\<in>system_definitions fragment_system" for d
    by (rule whole_system_agreement_meaning[OF fragment_system_formed construction_components_formed
      construction_components_fragment_agreement that])
  have assembly: "(d,t)\<in>positive_meaning construction_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning assembly_checking_system" if "d\<in>system_definitions assembly_checking_system" for d
    by (rule whole_system_agreement_meaning[OF assembly_checking_system_formed construction_components_formed
      construction_components_assembly_agreement that])
  show "(1,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
    using sources[of 1] source_component_meanings(1)[of t] source_base_roots by auto
  show "(6,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
    using fragments[of 6] fragment_components(3)[of t] fragment_base_roots by auto
  show "(10,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
    using sources[of 10] source_component_meanings(2)[of t] source_base_roots by auto
  show "(21,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
    using sources[of 21] source_component_meanings(3)[of t] source_base_roots by auto
  show "(205,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (205,t)\<in>positive_meaning fragment_system"
    using fragments[of 205] by auto
  show "(206,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (206,t)\<in>positive_meaning fragment_system"
    using fragments[of 206] by auto
  show "(230,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (230,t)\<in>positive_meaning assembly_checking_system"
    using assembly[of 230] by auto
  show "(233,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
    using sources[of 233] source_component_meanings(5)[of t] source_base_roots by auto
  show "(242,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (242,t)\<in>positive_meaning source_system"
    using sources[of 242] by auto
  show "(244,t)\<in>positive_meaning construction_components_system \<longleftrightarrow> (244,t)\<in>positive_meaning source_system"
    using sources[of 244] by auto
qed

lemma construction_components_row_agreement:
  "systems_agree_on row_values_system construction_components_system (system_definitions row_values_system)"
  by (rule whole_agreement_transitive[OF construction_sequence_row_agreement],
      rule whole_agreement_transitive[OF construction_base_sequence_agreement],
      rule whole_agreement_transitive[OF construction_fragment_prefix_agreement],
      rule whole_agreement_transitive[OF construction_source_prefix_agreement construction_components_prefix_agreement])

text \<open>
  Whole agreement, covered union, rooted restriction, and group rebasing
  account for the common definitions. The source, fragment, and assembly
  programs retain their complete original interfaces, clause families, and
  meanings. Their local contracts are therefore available together before
  the construction reader selects its least actual dependency closure.
\<close>

end
