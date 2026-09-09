theory Factor_Base_Cause_Base
  imports Factor_Generation_Scope_Contracts Factor_Judgment_Retention_Contracts
    Factor_Base_Cause_Presentations Factor_Component_Agreement
begin

section \<open>Complete generation and quotation programs agree on their shared definitions\<close>

lemma base_cause_source_shared_boundary:
  "system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system
    \<subseteq>system_definitions located_admission_system"
  "system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system
    \<subseteq>system_definitions generation_source_base_system"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system"
  have fresh: "{147,148,149,150,151,152,153,154,155}\<inter>system_definitions complete_data_admission_system={}"
    by auto
  have retained: "?U\<subseteq>system_definitions generation_source_base_system"
    using fresh unfolding generation_source_definitions by blast
  have extra: "{139,140,141,142,143,144,145,146}\<inter>system_definitions complete_data_admission_system={}"
    by auto
  have lower: "system_definitions target_difference_system\<inter>system_definitions complete_data_admission_system
      \<subseteq>system_definitions located_admission_system" by auto
  have component: "system_definitions generation_source_components_system\<inter>system_definitions complete_data_admission_system
      \<subseteq>system_definitions located_admission_system"
    using generation_target_subdomain lower extra
    unfolding generation_source_components_definitions generation_value_definitions by blast
  show "?U\<subseteq>system_definitions located_admission_system"
    using retained generation_source_base_subdomain component by blast
  show "?U\<subseteq>system_definitions generation_source_base_system" by (rule retained)
qed

lemma base_cause_source_agreement:
  "systems_agree_on complete_data_admission_system generation_source_system
    (system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system)"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system"
  have one: "systems_agree_on complete_data_admission_system located_admission_system ?U"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF complete_data_located_agreement]
      base_cause_source_shared_boundary(1)])
  have two: "systems_agree_on located_admission_system generation_source_components_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_located_agreement base_cause_source_shared_boundary(1)])
  have three: "systems_agree_on generation_source_components_system generation_source_base_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_base_agreement base_cause_source_shared_boundary(2)])
  have four: "systems_agree_on generation_source_base_system generation_source_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_retained_agreement base_cause_source_shared_boundary(2)])
  show ?thesis by (rule systems_agree_on_transitive[OF one systems_agree_on_transitive[OF two
    systems_agree_on_transitive[OF three four]]])
qed

lemma base_cause_scope_agreement:
  "systems_agree_on complete_data_admission_system scope_programs_system
    (system_definitions scope_programs_system\<inter>system_definitions complete_data_admission_system)"
proof -
  let ?U="system_definitions scope_programs_system\<inter>system_definitions complete_data_admission_system"
  have fresh: "{160,161,164,165,166}\<inter>system_definitions complete_data_admission_system={}"
    by auto
  have retained: "?U\<subseteq>system_definitions judgment_scope_base_system\<union>system_definitions program_report_base_system"
    using fresh unfolding scope_programs_definitions judgment_scope_reading_definitions program_scope_reports_definitions by blast
  have one: "systems_agree_on complete_data_admission_system scope_reading_components_system ?U"
    by (rule systems_agree_on_subdomain[OF scope_reading_complete_agreement]) blast
  have two: "systems_agree_on scope_reading_components_system scope_programs_system ?U"
    by (rule systems_agree_on_subdomain[OF scope_programs_base_agreement retained])
  show ?thesis by (rule systems_agree_on_transitive[OF one two])
qed

lemma base_cause_component_agreement:
  "systems_agree_on complete_data_admission_system generation_scope_components_system
    (system_definitions generation_scope_components_system\<inter>system_definitions complete_data_admission_system)"
proof -
  have source: "systems_agree_on generation_source_system complete_data_admission_system
      (system_definitions generation_source_system\<inter>system_definitions complete_data_admission_system)"
    by (rule systems_agree_on_sym[OF base_cause_source_agreement])
  have scope: "systems_agree_on scope_programs_system complete_data_admission_system
      (system_definitions scope_programs_system\<inter>system_definitions complete_data_admission_system)"
    by (rule systems_agree_on_sym[OF base_cause_scope_agreement])
  have joined: "systems_agree_on generation_scope_components_system complete_data_admission_system
      (system_definitions generation_scope_components_system\<inter>system_definitions complete_data_admission_system)"
    unfolding generation_scope_components_system_def
    by (rule overlap_agreement_union[OF generation_source_system_formed scope_programs_formed source scope])
  show ?thesis by (rule systems_agree_on_sym[OF joined])
qed

lemma base_cause_program_agreement:
  "systems_agree_on generation_scope_system complete_data_admission_system
    (system_definitions generation_scope_system\<inter>system_definitions complete_data_admission_system)"
proof -
  let ?U="system_definitions generation_scope_system\<inter>system_definitions complete_data_admission_system"
  have retained: "?U\<subseteq>system_definitions generation_scope_base_system"
    unfolding generation_scope_definitions by auto
  have source: "?U\<subseteq>system_definitions generation_scope_components_system\<inter>system_definitions complete_data_admission_system"
    using retained generation_scope_base_subdomain by blast
  have one: "systems_agree_on complete_data_admission_system generation_scope_components_system ?U"
    by (rule systems_agree_on_subdomain[OF base_cause_component_agreement source])
  have two: "systems_agree_on generation_scope_components_system generation_scope_base_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_scope_base_agreement retained])
  have old: "systems_agree_on generation_scope_base_system generation_scope_system
      (system_definitions generation_scope_base_system)"
    using generation_scope_group.old_agreement by (simp only: generation_scope_system_def)
  have three: "systems_agree_on generation_scope_base_system generation_scope_system ?U"
    by (rule systems_agree_on_subdomain[OF old retained])
  show ?thesis by (rule systems_agree_on_sym[OF systems_agree_on_transitive[OF one
    systems_agree_on_transitive[OF two three]]])
qed

definition base_cause_source_system :: "(nat,nat,nat,nat) schema_system" where
  "base_cause_source_system=system_union generation_scope_system complete_data_admission_system"

lemma base_cause_source_formed [simp]: "schema_system_formed base_cause_source_system"
  unfolding base_cause_source_system_def
  by (rule system_union_agree_formed[OF generation_scope_system_formed complete_data_admission_system_formed
    base_cause_program_agreement])

lemma base_cause_source_definitions [simp]:
  "system_definitions base_cause_source_system=
    system_definitions generation_scope_system\<union>system_definitions complete_data_admission_system"
  by (simp add: base_cause_source_system_def)

lemma base_cause_source_call:
  "schema_call_formed base_cause_source_system d t \<longleftrightarrow>
    d\<in>system_definitions base_cause_source_system \<and> term_formed t"
  using system_union_agree_call[OF generation_scope_system_formed complete_data_admission_system_formed
    base_cause_program_agreement, of d t]
  by (simp only: base_cause_source_system_def system_union_definitions generation_scope_call
    complete_data_admission_call; blast)

lemma base_cause_old_fresh:
  "system_definitions base_cause_source_system\<inter>{178,179,180,181,182,183,184,185,186,187,188}={}"
proof -
  let ?N="{178,179,180,181,182,183,184,185,186,187,188}"
  have source_bound: "system_definitions generation_source_system\<subseteq>
      system_definitions generation_source_components_system\<union>{147,148,149,150,151,152,153,154,155}"
    using generation_source_base_subdomain unfolding generation_source_definitions by blast
  have source_fresh: "?N\<inter>(system_definitions generation_source_components_system\<union>{147,148,149,150,151,152,153,154,155})={}"
    using generation_target_subdomain by (auto dest: subsetD)
  have scope_fresh: "?N\<inter>(system_definitions scope_reading_components_system\<union>{160,161,164,165,166})={}"
    using context_base_subdomain by (auto dest: subsetD)
  have component_fresh: "system_definitions generation_scope_components_system\<inter>?N={}"
    using source_bound scope_programs_boundary source_fresh scope_fresh
    unfolding generation_scope_components_definitions by blast
  have retained_fresh: "system_definitions generation_scope_base_system\<inter>?N={}"
    using generation_scope_base_subdomain component_fresh by blast
  show ?thesis using retained_fresh by auto
qed

lemma base_cause_complete_agreement:
  "systems_agree_on complete_data_admission_system base_cause_source_system
    (system_definitions complete_data_admission_system)"
proof -
  have reverse: "systems_agree_on complete_data_admission_system generation_scope_system
      (system_definitions complete_data_admission_system\<inter>system_definitions generation_scope_system)"
    using systems_agree_on_sym[OF base_cause_program_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF generation_scope_system_formed reverse]
    by (simp only: base_cause_source_system_def system_union_commute)
qed

lemma base_cause_slot_agreement:
  "systems_agree_on package_slot_reading_system complete_data_admission_system
    (system_definitions package_slot_reading_system)"
  by (simp add: systems_agree_on_added complete_data_admission_system_def
    package_retention_admission_system_def package_slot_list_system_def package_source_list_system_def)

lemma base_cause_retention_base_agreement:
  "systems_agree_on judgment_retention_base_system base_cause_source_system
    (system_definitions judgment_retention_base_system)"
proof -
  have sub: "system_definitions judgment_retention_base_system\<subseteq>system_definitions complete_data_admission_system"
    using judgment_retention_base_subdomain by (auto dest: subsetD)
  have one: "systems_agree_on judgment_retention_base_system package_slot_reading_system
      (system_definitions judgment_retention_base_system)"
    by (rule systems_agree_on_sym[OF judgment_retention_base_agreement])
  have two: "systems_agree_on package_slot_reading_system complete_data_admission_system
      (system_definitions judgment_retention_base_system)"
    by (rule systems_agree_on_subdomain[OF base_cause_slot_agreement judgment_retention_base_subdomain])
  have three: "systems_agree_on complete_data_admission_system base_cause_source_system
      (system_definitions judgment_retention_base_system)"
    by (rule systems_agree_on_subdomain[OF base_cause_complete_agreement sub])
  show ?thesis by (rule systems_agree_on_transitive[OF one systems_agree_on_transitive[OF two three]])
qed

interpretation base_cause_retention_group:
  positive_definition_group base_cause_source_system judgment_retention_definition_group
proof (rule positive_definition_group.intro[OF base_cause_source_formed])
  have sub: "system_definitions package_slot_reading_system\<subseteq>system_definitions base_cause_source_system" by auto
  show "schema_system_formed_over (system_definitions base_cause_source_system) judgment_retention_definition_group"
    by (rule schema_system_formed_over_mono[OF judgment_retention_group_source_formation sub])
  show "system_definitions base_cause_source_system\<inter>system_definitions judgment_retention_definition_group={}"
    using base_cause_old_fresh by auto
qed

definition base_cause_components_system :: "(nat,nat,nat,nat) schema_system" where
  "base_cause_components_system=system_union base_cause_source_system judgment_retention_definition_group"

lemma base_cause_components_formed [simp]: "schema_system_formed base_cause_components_system"
  using base_cause_retention_group.formed by (simp only: base_cause_components_system_def)

lemma base_cause_components_definitions [simp]:
  "system_definitions base_cause_components_system=
    system_definitions base_cause_source_system\<union>{178,179,180,181,182,183,184}"
  by (simp add: base_cause_components_system_def)

lemma base_cause_components_call:
  "schema_call_formed base_cause_components_system d t \<longleftrightarrow>
    d\<in>system_definitions base_cause_components_system \<and> term_formed t"
  using base_cause_retention_group.variable_calls[OF base_cause_source_call judgment_retention_group_interfaces, of d t]
  by (simp only: base_cause_components_system_def)

lemma base_cause_retention_agreement:
  "systems_agree_on judgment_retention_system base_cause_components_system
    (system_definitions judgment_retention_system)"
  using judgment_retention_group.rebased_agreement[OF base_cause_source_formed
    base_cause_retention_base_agreement base_cause_retention_group.separate]
  by (simp only: judgment_retention_system_def base_cause_components_system_def)

lemma base_cause_retention_meaning:
  assumes "d\<in>system_definitions judgment_retention_system"
  shows "(d,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning judgment_retention_system"
proof -
  have closed: "system_dependency_closed judgment_retention_system (system_definitions judgment_retention_system)"
    using system_dependency_boundary(1)[OF judgment_retention_system_formed]
    unfolding system_dependency_closed_def by blast
  show ?thesis using positive_meaning_dependency_locality[OF judgment_retention_system_formed
    base_cause_components_formed base_cause_retention_agreement closed assms, of t] by blast
qed

lemma base_cause_generation_meaning:
  assumes "d\<in>system_definitions generation_scope_system"
  shows "(d,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_scope_system"
  using base_cause_retention_group.old_meaning[of d t]
    system_union_agree_left_locality(2)[OF generation_scope_system_formed complete_data_admission_system_formed
      base_cause_program_agreement assms, of t] assms
  by (simp only: base_cause_components_system_def base_cause_source_system_def system_union_definitions; blast)

lemma base_cause_complete_meaning:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "(d,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning complete_data_admission_system"
  using base_cause_retention_group.old_meaning[of d t]
    system_union_agree_right_locality(2)[OF generation_scope_system_formed complete_data_admission_system_formed
      base_cause_program_agreement assms, of t] assms
  by (simp only: base_cause_components_system_def base_cause_source_system_def system_union_definitions; blast)

lemma base_cause_component_meanings:
  "(10,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(58,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(115,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (115,t)\<in>positive_meaning native_positive_admission_system"
  "(151,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (151,t)\<in>positive_meaning generation_source_system"
  "(162,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (162,t)\<in>positive_meaning generation_scope_system"
  "(183,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (183,t)\<in>positive_meaning judgment_retention_system"
proof -
  have projection: "(10,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
      (10,t)\<in>positive_meaning artifact_projection_system"
    using complete_data_admission_old_meaning[of 10 t] package_retention_admission_old_meaning[of 10 t]
      package_slot_list_old_meaning[of 10 t] package_source_list_old_meaning[of 10 t]
      judgment_retention_inclusion_meaning[of 10 t] environment_inclusion_located_meaning[of 10 t]
      located_admission_old_meaning[of 10 t] anchored_admission_old_meaning[of 10 t]
      citation_reading_old_meaning[of 10 t] citation_location_old_meaning[of 10 t]
      citation_interpretation_old_meaning[of 10 t] citation_resolution_old_meaning[of 10 t]
      binding_lookup_old_meaning[of 10 t] artifact_lookup_environment_meaning[of 10 t]
      environment_identity_old_meaning[of 10 t] environment_comparison_old_meaning[of 10 t]
      environment_bag_old_meaning[of 10 t] environment_entry_old_meaning[of 10 t]
      artifact_identity_previous_meaning[of 10 t]
      artifact_admission_old_meaning[of 10 t] by auto
  have positive: "(115,t)\<in>positive_meaning complete_data_admission_system \<longleftrightarrow>
      (115,t)\<in>positive_meaning native_positive_admission_system"
    using complete_data_admission_old_meaning[of 115 t] package_retention_admission_old_meaning[of 115 t]
      package_slot_list_old_meaning[of 115 t] package_source_list_old_meaning[of 115 t]
      package_slot_reading_old_meaning[of 115 t] package_source_reading_old_meaning[of 115 t]
      scope_forwarding_old_meaning[of 115 t] by auto
  show "(10,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
    using base_cause_complete_meaning[of 10 t] projection by auto
  show "(58,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
    using base_cause_retention_meaning[of 58 t] judgment_retention_base_roots judgment_retention_components(4)[of t] by auto
  show "(115,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (115,t)\<in>positive_meaning native_positive_admission_system"
    using base_cause_complete_meaning[of 115 t] positive by auto
  show "(151,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (151,t)\<in>positive_meaning generation_source_system"
    using base_cause_generation_meaning[of 151 t] generation_scope_base_roots generation_scope_components(1)[of t] by auto
  show "(162,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (162,t)\<in>positive_meaning generation_scope_system"
    using base_cause_generation_meaning[of 162 t] by auto
  show "(183,t)\<in>positive_meaning base_cause_components_system \<longleftrightarrow> (183,t)\<in>positive_meaning judgment_retention_system"
    using base_cause_retention_meaning[of 183 t] by auto
qed

section \<open>Later readers reuse the complete shared row and difference boundaries\<close>

lemma base_cause_component_domain_bounds:
  "system_definitions base_cause_components_system\<subseteq>{..184}"
  "system_definitions base_cause_components_system\<inter>{124,125,126,127}={}"
proof -
  let ?D="{..123}\<union>{132..184}"
  have target: "system_definitions generation_target_system\<subseteq>?D"
    by (rule subset_trans[OF generation_target_subdomain]) auto
  have value_bound: "system_definitions generation_value_system\<subseteq>?D"
    using target by auto
  have source_base: "system_definitions generation_source_base_system\<subseteq>?D"
    by (rule subset_trans[OF generation_source_base_subdomain]) (use value_bound in auto)
  have source: "system_definitions generation_source_system\<subseteq>?D"
    using source_base by auto
  have context_base: "system_definitions context_base_system\<subseteq>?D"
    by (rule subset_trans[OF context_base_subdomain]) auto
  have scope: "system_definitions scope_programs_system\<subseteq>?D"
    by (rule subset_trans[OF scope_programs_boundary]) (use context_base in auto)
  have scope_base: "system_definitions generation_scope_base_system\<subseteq>?D"
    by (rule subset_trans[OF generation_scope_base_subdomain]) (use source scope in auto)
  show "system_definitions base_cause_components_system\<subseteq>{..184}"
    "system_definitions base_cause_components_system\<inter>{124,125,126,127}={}"
    using scope_base by auto
qed

lemma base_cause_inclusion_agreement:
  "systems_agree_on environment_inclusion_system base_cause_components_system
    (system_definitions environment_inclusion_system)"
proof -
  have quoted: "systems_agree_on environment_inclusion_system complete_data_admission_system
      (system_definitions environment_inclusion_system)"
    by (rule whole_agreement_transitive[OF judgment_retention_inclusion_agreement base_cause_slot_agreement])
  have source: "systems_agree_on environment_inclusion_system base_cause_source_system
      (system_definitions environment_inclusion_system)"
    by (rule whole_agreement_transitive[OF quoted base_cause_complete_agreement])
  have retained: "systems_agree_on base_cause_source_system base_cause_components_system
      (system_definitions base_cause_source_system)"
    using base_cause_retention_group.old_agreement by (simp only: base_cause_components_system_def)
  show ?thesis by (rule whole_agreement_transitive[OF source retained])
qed

lemma base_cause_row_agreement:
  "systems_agree_on row_values_system base_cause_components_system (system_definitions row_values_system)"
  by (rule whole_agreement_transitive[OF environment_inclusion_row_values_agreement base_cause_inclusion_agreement])

lemma base_cause_bag_overlap_agreement:
  "systems_agree_on base_cause_components_system bag_difference_system
    (system_definitions base_cause_components_system\<inter>system_definitions bag_difference_system)"
proof -
  have quoted: "systems_agree_on environment_inclusion_system complete_data_admission_system
      (system_definitions environment_inclusion_system)"
    by (rule whole_agreement_transitive[OF judgment_retention_inclusion_agreement base_cause_slot_agreement])
  have rows: "systems_agree_on row_values_system complete_data_admission_system (system_definitions row_values_system)"
    by (rule whole_agreement_transitive[OF environment_inclusion_row_values_agreement quoted])
  have bags: "systems_agree_on bag_comparison_system complete_data_admission_system
      (system_definitions bag_comparison_system)"
    by (rule whole_agreement_transitive[OF row_values_bag_agreement rows])
  have complete: "systems_agree_on complete_data_admission_system bag_difference_system
      (system_definitions complete_data_admission_system\<inter>system_definitions bag_difference_system)"
  proof (rule common_component_overlap_agreement[where B=bag_comparison_system])
    show "systems_agree_on bag_comparison_system complete_data_admission_system
        (system_definitions bag_comparison_system\<inter>system_definitions complete_data_admission_system)"
      by (rule systems_agree_on_subdomain[OF bags]) blast
    show "systems_agree_on bag_comparison_system bag_difference_system
        (system_definitions bag_comparison_system\<inter>system_definitions bag_difference_system)"
      by (rule systems_agree_on_subdomain[OF bag_difference_base_agreement]) blast
    show "system_definitions complete_data_admission_system\<inter>system_definitions bag_difference_system
        \<subseteq>system_definitions bag_comparison_system" by auto
  qed
  have located_bags: "systems_agree_on bag_comparison_system located_admission_system
      (system_definitions bag_comparison_system)"
    by (rule whole_agreement_transitive[OF artifact_identity_bag_agreement
      whole_agreement_transitive[OF target_admission_artifact_agreement located_target_agreement]])
  have located: "systems_agree_on located_admission_system bag_difference_system
      (system_definitions located_admission_system\<inter>system_definitions bag_difference_system)"
  proof (rule common_component_overlap_agreement[where B=bag_comparison_system])
    show "systems_agree_on bag_comparison_system located_admission_system
        (system_definitions bag_comparison_system\<inter>system_definitions located_admission_system)"
      by (rule systems_agree_on_subdomain[OF located_bags]) blast
    show "systems_agree_on bag_comparison_system bag_difference_system
        (system_definitions bag_comparison_system\<inter>system_definitions bag_difference_system)"
      by (rule systems_agree_on_subdomain[OF bag_difference_base_agreement]) blast
    show "system_definitions located_admission_system\<inter>system_definitions bag_difference_system
        \<subseteq>system_definitions bag_comparison_system" by auto
  qed
  have target: "systems_agree_on target_difference_system bag_difference_system
      (system_definitions target_difference_system\<inter>system_definitions bag_difference_system)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF target_difference_bag_agreement]]) blast
  have selected: "systems_agree_on generation_target_system bag_difference_system
      (system_definitions generation_target_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_target_system_def by (rule rooted_overlap_agreement[OF target])
  have value_agreement: "systems_agree_on generation_value_system bag_difference_system
      (system_definitions generation_value_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_value_system_def
    by (rule generation_group.extended_overlap_agreement[OF selected]) auto
  have source_components: "systems_agree_on generation_source_components_system bag_difference_system
      (system_definitions generation_source_components_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_source_components_system_def
    by (rule overlap_agreement_union[OF located_admission_system_formed generation_value_system_formed located value_agreement])
  have source_base: "systems_agree_on generation_source_base_system bag_difference_system
      (system_definitions generation_source_base_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_source_base_system_def by (rule rooted_overlap_agreement[OF source_components])
  have source: "systems_agree_on generation_source_system bag_difference_system
      (system_definitions generation_source_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_source_system_def
    by (rule generation_source_group.extended_overlap_agreement[OF source_base]) auto
  have scope: "systems_agree_on scope_programs_system bag_difference_system
      (system_definitions scope_programs_system\<inter>system_definitions bag_difference_system)"
  proof (rule common_component_overlap_agreement[where B=complete_data_admission_system])
    show "systems_agree_on complete_data_admission_system scope_programs_system
        (system_definitions complete_data_admission_system\<inter>system_definitions scope_programs_system)"
      using base_cause_scope_agreement by (simp only: Int_commute)
    show "systems_agree_on complete_data_admission_system bag_difference_system
        (system_definitions complete_data_admission_system\<inter>system_definitions bag_difference_system)"
      by (rule complete)
    have retained_context: "system_definitions context_base_system\<subseteq>system_definitions complete_data_admission_system"
      by (rule subset_trans[OF context_base_subdomain]) auto
    have lower: "system_definitions scope_programs_system\<subseteq>
        system_definitions complete_data_admission_system\<union>{156..166}"
      by (rule subset_trans[OF scope_programs_boundary]) (use retained_context in auto)
    show "system_definitions scope_programs_system\<inter>system_definitions bag_difference_system
        \<subseteq>system_definitions complete_data_admission_system"
      by (rule subset_trans[OF Int_mono[OF lower subset_refl]]) auto
  qed
  have scope_components: "systems_agree_on generation_scope_components_system bag_difference_system
      (system_definitions generation_scope_components_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_scope_components_system_def
    by (rule overlap_agreement_union[OF generation_source_system_formed scope_programs_formed source scope])
  have scope_base: "systems_agree_on generation_scope_base_system bag_difference_system
      (system_definitions generation_scope_base_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_scope_base_system_def by (rule rooted_overlap_agreement[OF scope_components])
  have generation_scope: "systems_agree_on generation_scope_system bag_difference_system
      (system_definitions generation_scope_system\<inter>system_definitions bag_difference_system)"
    unfolding generation_scope_system_def
    by (rule generation_scope_group.extended_overlap_agreement[OF scope_base]) auto
  have combined: "systems_agree_on base_cause_source_system bag_difference_system
      (system_definitions base_cause_source_system\<inter>system_definitions bag_difference_system)"
    unfolding base_cause_source_system_def
    by (rule overlap_agreement_union[OF generation_scope_system_formed complete_data_admission_system_formed
      generation_scope complete])
  show ?thesis unfolding base_cause_components_system_def
    by (rule base_cause_retention_group.extended_overlap_agreement[OF combined]) auto
qed

text \<open>
  Complete interfaces and clause families establish compatibility before any
  program union. A generic union law assembles their agreement on a covered
  domain. A generic group law then preserves the judgment retention program
  when its base is enlarged by agreeing definitions. Neither operation changes
  an independently owned reader contract or adds a semantic parameter.

  This source supplies existing literal, application, truth, generation, scope,
  and retention entries. The following four clauses select only the least
  complete-definition closure of their actual external calls.
\<close>

end
