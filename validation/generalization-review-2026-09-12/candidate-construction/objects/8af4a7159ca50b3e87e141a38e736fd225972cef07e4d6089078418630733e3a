theory Factor_Generation_Source_Base
  imports Factor_Generation_Contracts Factor_Anchored_Admission
begin

section \<open>Generation values and actual citations share complete definitions\<close>

lemma located_target_agreement:
  "systems_agree_on target_admission_system located_admission_system
    (system_definitions target_admission_system)"
  by (simp add: systems_agree_on_added located_admission_system_def anchored_admission_system_def
    citation_reading_system_def citation_location_system_def citation_interpretation_system_def
    citation_resolution_system_def binding_lookup_system_def artifact_lookup_system_def citation_admission_system_def)

lemma target_difference_target_agreement:
  "systems_agree_on target_admission_system target_difference_system
    (system_definitions target_admission_system)"
proof -
  have base: "systems_agree_on target_admission_system target_comparison_base_system
      (system_definitions target_admission_system)"
    using system_union_agree_left[OF artifact_difference_system_formed target_artifact_difference_agreement]
    by (simp only: target_comparison_base_system_def)
  show ?thesis using base
    by (simp add: target_difference_system_def target_identity_system_def systems_agree_on_added)
qed

lemma generation_located_agreement:
  "systems_agree_on located_admission_system generation_value_system
    (system_definitions located_admission_system\<inter>system_definitions generation_value_system)"
proof -
  let ?U="system_definitions located_admission_system\<inter>system_definitions generation_value_system"
  have base_domain: "?U\<subseteq>system_definitions generation_target_system" by auto
  have shared: "system_definitions located_admission_system\<inter>system_definitions target_difference_system=
      system_definitions target_admission_system" by auto
  have target_domain: "?U\<subseteq>system_definitions target_admission_system"
    using base_domain generation_target_subdomain shared by blast
  have inherited: "systems_agree_on located_admission_system target_difference_system
      (system_definitions target_admission_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF located_target_agreement]
      target_difference_target_agreement])
  have first: "systems_agree_on located_admission_system target_difference_system ?U"
    by (rule systems_agree_on_subdomain[OF inherited target_domain])
  have second: "systems_agree_on target_difference_system generation_target_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_target_agreement base_domain])
  have third: "systems_agree_on generation_target_system generation_value_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_value_base_agreement base_domain])
  show ?thesis by (rule systems_agree_on_transitive[OF first systems_agree_on_transitive[OF second third]])
qed

definition generation_source_components_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_source_components_system=system_union located_admission_system generation_value_system"

lemma generation_source_components_formed [simp]: "schema_system_formed generation_source_components_system"
  unfolding generation_source_components_system_def
  by (rule system_union_agree_formed[OF located_admission_system_formed generation_value_system_formed
    generation_located_agreement])

lemma generation_source_components_definitions [simp]:
  "system_definitions generation_source_components_system=
    system_definitions located_admission_system\<union>system_definitions generation_value_system"
  by (simp add: generation_source_components_system_def)

lemma generation_source_components_call:
  "schema_call_formed generation_source_components_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_source_components_system \<and> term_formed t"
  using system_union_agree_call[OF located_admission_system_formed generation_value_system_formed
    generation_located_agreement, of d t]
  by (simp only: generation_source_components_system_def system_union_definitions
    located_admission_call generation_value_call Un_iff; blast)

theorem generation_source_citation_locality:
  assumes "d\<in>system_definitions located_admission_system"
  shows "schema_call_formed generation_source_components_system d t \<longleftrightarrow>
      schema_call_formed located_admission_system d t"
    and "(d,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning located_admission_system"
  using system_union_agree_left_locality[OF located_admission_system_formed generation_value_system_formed
    generation_located_agreement assms, of t]
  by (simp_all only: generation_source_components_system_def)

theorem generation_source_value_locality:
  assumes "d\<in>system_definitions generation_value_system"
  shows "schema_call_formed generation_source_components_system d t \<longleftrightarrow>
      schema_call_formed generation_value_system d t"
    and "(d,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning generation_value_system"
  using system_union_agree_right_locality[OF located_admission_system_formed generation_value_system_formed
    generation_located_agreement assms, of t]
  by (simp_all only: generation_source_components_system_def)

lemma located_target_meaning:
  assumes "d\<in>system_definitions target_admission_system"
  shows "(d,t)\<in>positive_meaning located_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_admission_system"
proof -
  have closed: "system_dependency_closed target_admission_system (system_definitions target_admission_system)"
    using system_dependency_boundary(1)[OF target_admission_system_formed]
    unfolding system_dependency_closed_def by blast
  show ?thesis
    using positive_meaning_dependency_locality[OF target_admission_system_formed located_admission_system_formed
      located_target_agreement closed assms, of t] by blast
qed

lemma generation_source_component_payload:
  "(1,data_list_term [t])\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (\<exists>b. octets_formed b \<and> t=Payload_Term b)"
  using generation_source_citation_locality(2)[of 1 "data_list_term [t]"]
    located_target_meaning[of 1 "data_list_term [t]"]
    target_admission_headed_meaning[of 1 "data_list_term [t]"]
    headed_material_old_meaning[of 1 "data_list_term [t]"]
    key_fibre_bag_meaning[of 1 "data_list_term [t]"]
    bag_comparison_old_meaning[of 1 "data_list_term [t]"]
    data_comparison_payloads[of "data_list_term [t]"] payload_recognition_exact[of t] by auto

lemma generation_source_component_meanings:
  "(32,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (32,t)\<in>positive_meaning family_admission_system"
  "(34,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (34,t)\<in>positive_meaning record_admission_system"
  "(37,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(43,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (43,t)\<in>positive_meaning anchored_admission_system"
  "(44,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (44,t)\<in>positive_meaning located_admission_system"
  "(139,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (139,t)\<in>positive_meaning generation_value_system"
  "(145,t)\<in>positive_meaning generation_source_components_system \<longleftrightarrow>
    (145,t)\<in>positive_meaning generation_value_system"
  using generation_source_citation_locality(2)[of 32 t] located_target_meaning[of 32 t]
    target_admission_old_meaning[of 32 t] record_admission_old_meaning[of 32 t] socket_chain_old_meaning[of 32 t]
    generation_source_citation_locality(2)[of 34 t] located_target_meaning[of 34 t] target_admission_old_meaning[of 34 t]
    generation_source_citation_locality(2)[of 37 t] located_admission_old_meaning[of 37 t]
    anchored_admission_old_meaning[of 37 t] citation_reading_components(2)[of t]
    generation_source_citation_locality(2)[of 43 t] located_admission_anchor[of t]
    generation_source_citation_locality(2)[of 44 t]
    generation_source_value_locality(2)[of 139 t] generation_source_value_locality(2)[of 145 t] by auto

text \<open>
  This formed source program combines actual citation reading with the local
  generation value program. Shared interfaces and every clause at their
  shared definition heads agree before the union is formed. Both programs'
  call boundaries and positive meanings are preserved.

  The following source group selects its base by the least closure of its
  actual external callees in this program. Forming this common source does
  not itself enlarge that retained base or introduce a replay dependency.
\<close>

end
