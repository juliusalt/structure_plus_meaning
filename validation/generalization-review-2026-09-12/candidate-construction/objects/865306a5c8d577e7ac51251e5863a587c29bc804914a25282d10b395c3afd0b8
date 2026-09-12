theory Factor_Construction_Cause_Components
  imports Factor_Base_Cause_Base Factor_Construction_Comparison Factor_Related_Test_Admission
begin

section \<open>Complete row and counted-difference components cover the first overlap\<close>

lemma construction_cause_comparison_agreement:
  "systems_agree_on base_cause_components_system construction_comparison_system
    (system_definitions base_cause_components_system\<inter>system_definitions construction_comparison_system)"
proof -
  have sequence: "systems_agree_on construction_sequence_components base_cause_components_system
      (system_definitions construction_sequence_components\<inter>system_definitions base_cause_components_system)"
  proof (rule common_component_overlap_agreement[where B=row_values_system])
    show "systems_agree_on row_values_system construction_sequence_components
        (system_definitions row_values_system\<inter>system_definitions construction_sequence_components)"
      by (rule systems_agree_on_subdomain[OF construction_sequence_row_agreement]) blast
    show "systems_agree_on row_values_system base_cause_components_system
        (system_definitions row_values_system\<inter>system_definitions base_cause_components_system)"
      by (rule systems_agree_on_subdomain[OF base_cause_row_agreement]) blast
    show "system_definitions construction_sequence_components\<inter>system_definitions base_cause_components_system
        \<subseteq>system_definitions row_values_system"
      using base_cause_component_domain_bounds(1) by (auto dest: subsetD)
  qed
  have bag: "systems_agree_on bag_difference_system base_cause_components_system
      (system_definitions bag_difference_system\<inter>system_definitions base_cause_components_system)"
    using systems_agree_on_sym[OF base_cause_bag_overlap_agreement] by (simp only: Int_commute)
  have component_base: "systems_agree_on construction_component_base base_cause_components_system
      (system_definitions construction_component_base\<inter>system_definitions base_cause_components_system)"
    unfolding construction_component_base_def
    by (rule overlap_agreement_union[OF construction_sequence_components_formed bag_difference_system_formed sequence bag])
  have fragments: "systems_agree_on construction_fragment_components base_cause_components_system
      (system_definitions construction_fragment_components\<inter>system_definitions base_cause_components_system)"
    unfolding construction_fragment_components_def
    by (rule construction_fragment_group.extended_overlap_agreement[OF component_base])
      (use base_cause_component_domain_bounds(1) in \<open>auto dest: subsetD\<close>)
  have sources: "systems_agree_on construction_source_components base_cause_components_system
      (system_definitions construction_source_components\<inter>system_definitions base_cause_components_system)"
    unfolding construction_source_components_def
    by (rule construction_source_group.extended_overlap_agreement[OF fragments])
      (use base_cause_component_domain_bounds(1) in \<open>auto dest: subsetD\<close>)
  have components: "systems_agree_on construction_components_system base_cause_components_system
      (system_definitions construction_components_system\<inter>system_definitions base_cause_components_system)"
    unfolding construction_components_system_def
    by (rule construction_assembly_group.extended_overlap_agreement[OF sources])
      (use base_cause_component_domain_bounds(1) in \<open>auto dest: subsetD\<close>)
  have admission_base: "systems_agree_on construction_admission_base_system base_cause_components_system
      (system_definitions construction_admission_base_system\<inter>system_definitions base_cause_components_system)"
    unfolding construction_admission_base_system_def by (rule rooted_overlap_agreement[OF components])
  have admission: "systems_agree_on construction_admission_system base_cause_components_system
      (system_definitions construction_admission_system\<inter>system_definitions base_cause_components_system)"
    unfolding construction_admission_system_def
    by (rule construction_admission_group.extended_overlap_agreement[OF admission_base])
      (use base_cause_component_domain_bounds(1) in \<open>auto dest: subsetD\<close>)
  have comparison_base: "systems_agree_on construction_comparison_base_system base_cause_components_system
      (system_definitions construction_comparison_base_system\<inter>system_definitions base_cause_components_system)"
    unfolding construction_comparison_base_system_def by (rule rooted_overlap_agreement[OF admission])
  have comparison: "systems_agree_on construction_comparison_system base_cause_components_system
      (system_definitions construction_comparison_system\<inter>system_definitions base_cause_components_system)"
    unfolding construction_comparison_system_def
    by (rule construction_comparison_group.extended_overlap_agreement[OF comparison_base])
      (use base_cause_component_domain_bounds(1) in \<open>auto dest: subsetD\<close>)
  show ?thesis using systems_agree_on_sym[OF comparison] by (simp only: Int_commute)
qed

definition construction_cause_source_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_cause_source_system=system_union base_cause_components_system construction_comparison_system"

lemma construction_cause_source_formed [simp]: "schema_system_formed construction_cause_source_system"
  unfolding construction_cause_source_system_def
  by (rule system_union_agree_formed[OF base_cause_components_formed construction_comparison_system_formed
    construction_cause_comparison_agreement])

lemma construction_cause_source_definitions [simp]:
  "system_definitions construction_cause_source_system=
    system_definitions base_cause_components_system\<union>system_definitions construction_comparison_system"
  by (simp add: construction_cause_source_system_def)

lemma construction_cause_source_bound:
  "system_definitions construction_cause_source_system\<subseteq>{..261}"
  using base_cause_component_domain_bounds(1) construction_comparison_definition_bound by auto

lemma construction_cause_source_call:
  "schema_call_formed construction_cause_source_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_cause_source_system \<and> term_formed t"
  using system_union_agree_call[OF base_cause_components_formed construction_comparison_system_formed
    construction_cause_comparison_agreement, of d t]
  by (simp only: construction_cause_source_system_def system_union_definitions
    base_cause_components_call construction_comparison_call; blast)

lemma construction_cause_source_base_agreement:
  "systems_agree_on base_cause_components_system construction_cause_source_system
    (system_definitions base_cause_components_system)"
  unfolding construction_cause_source_system_def
  by (rule system_union_agree_left[OF construction_comparison_system_formed construction_cause_comparison_agreement])

lemma construction_cause_source_comparison_agreement:
  "systems_agree_on construction_comparison_system construction_cause_source_system
    (system_definitions construction_comparison_system)"
proof -
  have reverse: "systems_agree_on construction_comparison_system base_cause_components_system
      (system_definitions construction_comparison_system\<inter>system_definitions base_cause_components_system)"
    using systems_agree_on_sym[OF construction_cause_comparison_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF base_cause_components_formed reverse]
    by (simp only: construction_cause_source_system_def system_union_commute)
qed

section \<open>The fixed permission checker shares only covered existing definitions\<close>

lemma construction_cause_related_base_agreement:
  "systems_agree_on base_cause_components_system related_test_admission_base
    (system_definitions base_cause_components_system\<inter>system_definitions related_test_admission_base)"
proof -
  have shared_definition_calls: "systems_agree_on definition_call_admission_system base_cause_components_system
      (system_definitions definition_call_admission_system)"
    by (rule whole_agreement_transitive[OF environment_inclusion_definition_agreement base_cause_inclusion_agreement])
  have single: "systems_agree_on single_clause_reading_system base_cause_components_system
      (system_definitions single_clause_reading_system\<inter>system_definitions base_cause_components_system)"
  proof (rule common_component_overlap_agreement[where B=definition_call_admission_system])
    show "systems_agree_on definition_call_admission_system single_clause_reading_system
        (system_definitions definition_call_admission_system\<inter>system_definitions single_clause_reading_system)"
      by (rule systems_agree_on_subdomain[OF single_clause_reading_base_agreement]) blast
    show "systems_agree_on definition_call_admission_system base_cause_components_system
        (system_definitions definition_call_admission_system\<inter>system_definitions base_cause_components_system)"
      by (rule systems_agree_on_subdomain[OF shared_definition_calls]) blast
    show "system_definitions single_clause_reading_system\<inter>system_definitions base_cause_components_system
        \<subseteq>system_definitions definition_call_admission_system"
      using base_cause_component_domain_bounds(2) by auto
  qed
  have inclusion: "systems_agree_on environment_inclusion_system base_cause_components_system
      (system_definitions environment_inclusion_system\<inter>system_definitions base_cause_components_system)"
    by (rule systems_agree_on_subdomain[OF base_cause_inclusion_agreement]) blast
  have components: "systems_agree_on related_test_components_system base_cause_components_system
      (system_definitions related_test_components_system\<inter>system_definitions base_cause_components_system)"
    unfolding related_test_components_system_def
    by (rule overlap_agreement_union[OF single_clause_reading_system_formed environment_inclusion_system_formed single inclusion])
  have retained: "systems_agree_on related_test_admission_base base_cause_components_system
      (system_definitions related_test_admission_base\<inter>system_definitions base_cause_components_system)"
    unfolding related_test_admission_base_def by (rule rooted_overlap_agreement[OF components])
  show ?thesis using systems_agree_on_sym[OF retained] by (simp only: Int_commute)
qed

lemma construction_cause_related_comparison_agreement:
  "systems_agree_on construction_comparison_system related_test_admission_base
    (system_definitions construction_comparison_system\<inter>system_definitions related_test_admission_base)"
proof (rule common_component_overlap_agreement[where B=base_cause_components_system])
  show "systems_agree_on base_cause_components_system construction_comparison_system
      (system_definitions base_cause_components_system\<inter>system_definitions construction_comparison_system)"
    by (rule construction_cause_comparison_agreement)
  show "systems_agree_on base_cause_components_system related_test_admission_base
      (system_definitions base_cause_components_system\<inter>system_definitions related_test_admission_base)"
    by (rule construction_cause_related_base_agreement)
  have components: "system_definitions construction_components_system\<inter>{..127}
      \<subseteq>system_definitions row_values_system" by auto
  have admission_base: "system_definitions construction_admission_base_system\<inter>{..127}
      \<subseteq>system_definitions row_values_system"
    by (rule subset_trans[OF Int_mono[OF construction_admission_base_subdomain subset_refl] components])
  have admission: "system_definitions construction_admission_system\<inter>{..127}
      \<subseteq>system_definitions row_values_system"
    using admission_base by auto
  have comparison_base: "system_definitions construction_comparison_base_system\<inter>{..127}
      \<subseteq>system_definitions row_values_system"
    by (rule subset_trans[OF Int_mono[OF construction_comparison_base_subdomain subset_refl] admission])
  have low: "system_definitions construction_comparison_system\<inter>{..127}
      \<subseteq>system_definitions row_values_system"
    using comparison_base by auto
  have shared: "system_definitions construction_comparison_system\<inter>system_definitions related_test_admission_base
      \<subseteq>system_definitions row_values_system"
    using low related_test_admission_base_bound by blast
  show "system_definitions construction_comparison_system\<inter>system_definitions related_test_admission_base
      \<subseteq>system_definitions base_cause_components_system"
    by (rule subset_trans[OF shared whole_agreement_definitions[OF base_cause_row_agreement]])
qed

lemma construction_cause_related_agreement:
  "systems_agree_on construction_cause_source_system (related_test_admission_system c k)
    (system_definitions construction_cause_source_system\<inter>system_definitions (related_test_admission_system c k))"
proof -
  have base: "systems_agree_on construction_cause_source_system related_test_admission_base
      (system_definitions construction_cause_source_system\<inter>system_definitions related_test_admission_base)"
    unfolding construction_cause_source_system_def
    by (rule overlap_agreement_union[OF base_cause_components_formed construction_comparison_system_formed
      construction_cause_related_base_agreement construction_cause_related_comparison_agreement])
  have fresh: "264\<notin>system_definitions construction_cause_source_system"
    using construction_cause_source_bound by auto
  have domain: "system_definitions construction_cause_source_system\<inter>system_definitions (related_test_admission_system c k)=
      system_definitions construction_cause_source_system\<inter>system_definitions related_test_admission_base"
    using fresh by (auto simp: related_test_admission_system_def)
  show ?thesis unfolding domain related_test_admission_system_def
    using base fresh by (simp add: systems_agree_on_added)
qed

definition construction_cause_components_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "construction_cause_components_system c k=
    system_union construction_cause_source_system (related_test_admission_system c k)"

context related_test_admission
begin

lemma construction_cause_components_formed:
  "schema_system_formed (construction_cause_components_system c k)"
  unfolding construction_cause_components_system_def
  by (rule system_union_agree_formed[OF construction_cause_source_formed formed construction_cause_related_agreement])

lemma construction_cause_components_definitions:
  "system_definitions (construction_cause_components_system c k)=
    system_definitions construction_cause_source_system\<union>insert 264 (system_definitions related_test_admission_base)"
  by (simp add: construction_cause_components_system_def)

lemma construction_cause_components_bound:
  "system_definitions (construction_cause_components_system c k)\<subseteq>{..264}"
  using construction_cause_source_bound related_test_admission_base_bound
  by (auto simp: construction_cause_components_definitions)

lemma construction_cause_components_call:
  "schema_call_formed (construction_cause_components_system c k) d t \<longleftrightarrow>
    d\<in>system_definitions (construction_cause_components_system c k) \<and> term_formed t"
  using system_union_agree_call[OF construction_cause_source_formed formed construction_cause_related_agreement, of d t]
  by (simp only: construction_cause_components_system_def system_union_definitions construction_cause_source_call calls; blast)

lemma construction_cause_components_source_agreement:
  "systems_agree_on construction_cause_source_system (construction_cause_components_system c k)
    (system_definitions construction_cause_source_system)"
  unfolding construction_cause_components_system_def
  by (rule system_union_agree_left[OF formed construction_cause_related_agreement])

lemma construction_cause_components_profile_agreement:
  "systems_agree_on (related_test_admission_system c k) (construction_cause_components_system c k)
    (system_definitions (related_test_admission_system c k))"
proof -
  have reverse: "systems_agree_on (related_test_admission_system c k) construction_cause_source_system
      (system_definitions (related_test_admission_system c k)\<inter>system_definitions construction_cause_source_system)"
    using systems_agree_on_sym[OF construction_cause_related_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF construction_cause_source_formed reverse]
    by (simp only: construction_cause_components_system_def system_union_commute)
qed

lemma construction_cause_components_base_agreement:
  "systems_agree_on base_cause_components_system (construction_cause_components_system c k)
    (system_definitions base_cause_components_system)"
  by (rule whole_agreement_transitive[OF construction_cause_source_base_agreement
    construction_cause_components_source_agreement])

lemma construction_cause_components_comparison_agreement:
  "systems_agree_on construction_comparison_system (construction_cause_components_system c k)
    (system_definitions construction_comparison_system)"
  by (rule whole_agreement_transitive[OF construction_cause_source_comparison_agreement
    construction_cause_components_source_agreement])

lemma construction_cause_component_meanings:
  "(10,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system"
  "(58,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (58,t)\<in>positive_meaning application_reading_system"
  "(115,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (115,t)\<in>positive_meaning native_positive_admission_system"
  "(151,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (151,t)\<in>positive_meaning generation_source_system"
  "(162,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (162,t)\<in>positive_meaning generation_scope_system"
  "(183,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (183,t)\<in>positive_meaning judgment_retention_system"
  "(261,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (261,t)\<in>positive_meaning construction_comparison_system"
  "(264,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (264,t)\<in>positive_meaning (related_test_admission_system c k)"
proof -
  have base: "(d,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
      (d,t)\<in>positive_meaning base_cause_components_system"
    if "d\<in>system_definitions base_cause_components_system" for d
    by (rule whole_system_agreement_meaning[OF base_cause_components_formed
      construction_cause_components_formed construction_cause_components_base_agreement that])
  show "(10,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system"
    using base[of 10] base_cause_component_meanings(1)[of t] by auto
  show "(58,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (58,t)\<in>positive_meaning application_reading_system"
    using base[of 58] base_cause_component_meanings(2)[of t] by auto
  show "(115,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (115,t)\<in>positive_meaning native_positive_admission_system"
    using base[of 115] base_cause_component_meanings(3)[of t] by auto
  show "(151,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (151,t)\<in>positive_meaning generation_source_system"
    using base[of 151] base_cause_component_meanings(4)[of t] generation_scope_base_roots by auto
  show "(162,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (162,t)\<in>positive_meaning generation_scope_system"
    using base[of 162] base_cause_component_meanings(5)[of t] by auto
  show "(183,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (183,t)\<in>positive_meaning judgment_retention_system"
    using base[of 183] base_cause_component_meanings(6)[of t] by auto
  show "(261,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (261,t)\<in>positive_meaning construction_comparison_system"
    by (rule whole_system_agreement_meaning[OF construction_comparison_system_formed
      construction_cause_components_formed construction_cause_components_comparison_agreement]) simp
  show "(264,t)\<in>positive_meaning (construction_cause_components_system c k) \<longleftrightarrow>
    (264,t)\<in>positive_meaning (related_test_admission_system c k)"
    by (rule whole_system_agreement_meaning[OF formed construction_cause_components_formed
      construction_cause_components_profile_agreement]) simp
qed

end

text \<open>
  The ordinary union retains complete interfaces and clause families from
  each original program. The common row ancestor covers the ordinary lower
  overlap; the counted-difference agreement passes separately through the
  generation reader's actual restrictions and groups. The permission reader's
  whole overlap is covered before its configured clause is added.

  No namespace copy or semantic-equivalence substitution removes a sharing
  condition. All eight existing reader meanings survive in one formed source.
  The following clauses retain only the least dependency closure of their
  actual external calls in this source.
\<close>

end
