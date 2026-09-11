theory Factor_Generation_Retention_Base
  imports Factor_Generation_Source_Contracts Factor_Environment_Inclusion_Contracts
begin

section \<open>Generation sources and environment inclusion share complete definitions\<close>

lemma generation_retention_shared_boundary:
  "system_definitions generation_source_system\<inter>system_definitions environment_inclusion_system
    \<subseteq>system_definitions located_admission_system"
  "system_definitions generation_source_system\<inter>system_definitions environment_inclusion_system
    \<subseteq>system_definitions generation_source_base_system"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions environment_inclusion_system"
  have fresh: "{147,148,149,150,151,152,153,154,155}\<inter>system_definitions environment_inclusion_system={}"
    by auto
  have retained: "?U\<subseteq>system_definitions generation_source_base_system"
    using fresh unfolding generation_source_definitions by blast
  have extra: "{139,140,141,142,143,144,145,146}\<inter>system_definitions environment_inclusion_system={}"
    by auto
  have lower: "system_definitions target_difference_system\<inter>system_definitions environment_inclusion_system
      \<subseteq>system_definitions located_admission_system" by auto
  have component: "system_definitions generation_source_components_system\<inter>system_definitions environment_inclusion_system
      \<subseteq>system_definitions located_admission_system"
    using generation_target_subdomain lower extra
    unfolding generation_source_components_definitions generation_value_definitions by blast
  show "?U\<subseteq>system_definitions located_admission_system"
    using retained generation_source_base_subdomain component by blast
  show "?U\<subseteq>system_definitions generation_source_base_system" by (rule retained)
qed

lemma generation_retention_program_agreement:
  "systems_agree_on generation_source_system environment_inclusion_system
    (system_definitions generation_source_system\<inter>system_definitions environment_inclusion_system)"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions environment_inclusion_system"
  have inherited: "systems_agree_on located_admission_system generation_source_components_system
      (system_definitions located_admission_system)"
    using system_union_agree_left[OF generation_value_system_formed generation_located_agreement]
    by (simp only: generation_source_components_system_def)
  have one: "systems_agree_on located_admission_system generation_source_components_system ?U"
    by (rule systems_agree_on_subdomain[OF inherited generation_retention_shared_boundary(1)])
  have two: "systems_agree_on generation_source_components_system generation_source_base_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_base_agreement generation_retention_shared_boundary(2)])
  have base: "systems_agree_on generation_source_base_system generation_source_system
      (system_definitions generation_source_base_system)"
    using generation_source_group.old_agreement by (simp only: generation_source_system_def)
  have three: "systems_agree_on generation_source_base_system generation_source_system ?U"
    by (rule systems_agree_on_subdomain[OF base generation_retention_shared_boundary(2)])
  have source: "systems_agree_on located_admission_system generation_source_system ?U"
    by (rule systems_agree_on_transitive[OF one systems_agree_on_transitive[OF two three]])
  have inclusion: "systems_agree_on located_admission_system environment_inclusion_system ?U"
    by (rule systems_agree_on_subdomain[OF environment_inclusion_located_agreement generation_retention_shared_boundary(1)])
  show ?thesis by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF source] inclusion])
qed

definition generation_retention_components_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_retention_components_system=system_union generation_source_system environment_inclusion_system"

lemma generation_retention_components_formed [simp]: "schema_system_formed generation_retention_components_system"
  unfolding generation_retention_components_system_def
  by (rule system_union_agree_formed[OF generation_source_system_formed environment_inclusion_system_formed
    generation_retention_program_agreement])

lemma generation_retention_components_definitions [simp]:
  "system_definitions generation_retention_components_system=
    system_definitions generation_source_system\<union>system_definitions environment_inclusion_system"
  by (simp add: generation_retention_components_system_def)

lemma generation_retention_components_call:
  "schema_call_formed generation_retention_components_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_retention_components_system \<and> term_formed t"
  using system_union_agree_call[OF generation_source_system_formed environment_inclusion_system_formed
    generation_retention_program_agreement, of d t]
  by (simp only: generation_retention_components_system_def system_union_definitions
    generation_source_call environment_inclusion_call Un_iff; blast)

theorem generation_retention_source_locality:
  assumes "d\<in>system_definitions generation_source_system"
  shows "schema_call_formed generation_retention_components_system d t \<longleftrightarrow>
      schema_call_formed generation_source_system d t"
    and "(d,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning generation_source_system"
  using system_union_agree_left_locality[OF generation_source_system_formed environment_inclusion_system_formed
    generation_retention_program_agreement assms, of t]
  by (simp_all only: generation_retention_components_system_def)

theorem generation_retention_inclusion_locality:
  assumes "d\<in>system_definitions environment_inclusion_system"
  shows "schema_call_formed generation_retention_components_system d t \<longleftrightarrow>
      schema_call_formed environment_inclusion_system d t"
    and "(d,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning environment_inclusion_system"
  using system_union_agree_right_locality[OF generation_source_system_formed environment_inclusion_system_formed
    generation_retention_program_agreement assms, of t]
  by (simp_all only: generation_retention_components_system_def)

lemma generation_retention_component_meanings:
  "(5,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (5,t)\<in>positive_meaning bag_comparison_system"
  "(37,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(38,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (38,t)\<in>positive_meaning binding_lookup_system"
  "(42,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (42,t)\<in>positive_meaning citation_reading_system"
  "(51,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (51,t)\<in>positive_meaning row_keys_system"
  "(113,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  "(147,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (147,t)\<in>positive_meaning generation_source_system"
  "(152,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (152,t)\<in>positive_meaning generation_source_system"
  "(155,t)\<in>positive_meaning generation_retention_components_system \<longleftrightarrow>
    (155,t)\<in>positive_meaning generation_source_system"
  using generation_retention_inclusion_locality(2)[of 5 t] environment_inclusion_located_meaning[of 5 t]
    located_admission_old_meaning[of 5 t] anchored_admission_old_meaning[of 5 t]
    citation_reading_old_meaning[of 5 t] citation_location_old_meaning[of 5 t]
    citation_interpretation_old_meaning[of 5 t] citation_resolution_old_meaning[of 5 t]
    binding_lookup_old_meaning[of 5 t] artifact_lookup_components(2)[of t]
    generation_retention_inclusion_locality(2)[of 37 t] environment_inclusion_located_meaning[of 37 t]
    located_admission_old_meaning[of 37 t] anchored_admission_old_meaning[of 37 t] citation_reading_components(2)[of t]
    generation_retention_inclusion_locality(2)[of 38 t] environment_inclusion_located_meaning[of 38 t]
    located_admission_old_meaning[of 38 t] anchored_admission_old_meaning[of 38 t]
    citation_reading_old_meaning[of 38 t] citation_location_old_meaning[of 38 t]
    citation_interpretation_old_meaning[of 38 t] citation_resolution_old_meaning[of 38 t]
    generation_retention_inclusion_locality(2)[of 42 t] environment_inclusion_located_meaning[of 42 t]
    located_admission_old_meaning[of 42 t] anchored_admission_components(1)[of t]
    generation_retention_inclusion_locality(2)[of 51 t] environment_inclusion_row_keys_meaning[of 51 t]
    generation_retention_inclusion_locality(2)[of 113 t]
    generation_retention_source_locality(2)[of 147 t] generation_retention_source_locality(2)[of 152 t]
    generation_retention_source_locality(2)[of 155 t] by auto

lemma generation_retention_component_boundary:
  "system_dependency_closed generation_retention_components_system
    (system_definitions generation_source_system\<union>system_definitions row_keys_system\<union>{112,113})"
proof -
  have source_agree: "systems_agree_on generation_source_system generation_retention_components_system
      (system_definitions generation_source_system)"
    using system_union_agree_left[OF environment_inclusion_system_formed generation_retention_program_agreement]
    by (simp only: generation_retention_components_system_def)
  have source_closed: "system_dependency_closed generation_source_system (system_definitions generation_source_system)"
    using system_dependency_boundary(1)[OF generation_source_system_formed]
    unfolding system_dependency_closed_def by blast
  have left: "system_dependency_closed generation_retention_components_system (system_definitions generation_source_system)"
    by (rule systems_agree_on_closed[OF source_agree source_closed])
  have reverse: "systems_agree_on environment_inclusion_system generation_source_system
      (system_definitions environment_inclusion_system\<inter>system_definitions generation_source_system)"
    using systems_agree_on_sym[OF generation_retention_program_agreement] by (simp only: Int_commute)
  have inclusion_agree: "systems_agree_on environment_inclusion_system generation_retention_components_system
      (system_definitions environment_inclusion_system)"
    using system_union_agree_left[OF generation_source_system_formed reverse]
    by (simp only: generation_retention_components_system_def system_union_commute)
  have boundary: "system_definitions row_keys_system\<union>{112,113}\<subseteq>system_definitions environment_inclusion_system"
    by auto
  have restricted: "systems_agree_on environment_inclusion_system generation_retention_components_system
      (system_definitions row_keys_system\<union>{112,113})"
    by (rule systems_agree_on_subdomain[OF inclusion_agree boundary])
  have right: "system_dependency_closed generation_retention_components_system (system_definitions row_keys_system\<union>{112,113})"
    by (rule systems_agree_on_closed[OF restricted environment_inclusion_dependency_boundary])
  show ?thesis using left right unfolding system_dependency_closed_def by blast
qed

text \<open>
  Source reading and complete environment inclusion are composed only after
  their shared interfaces and clause families agree. Both complete meanings
  survive the union. The following program retains the least closure of its
  actual external calls. The proved upper boundary excludes the earlier
  replay and protocol readers that happen to precede inclusion in its original
  construction.
\<close>

end
