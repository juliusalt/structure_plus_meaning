theory Factor_Generation_Value_Programs
  imports Factor_Generation_Contracts Factor_Comparison_Programs
begin

section \<open>Local generation operations join the existing reader program\<close>

lemma target_collection_comparison_agreement:
  "systems_agree_on target_collection_system comparison_reading_system (system_definitions target_collection_system)"
proof -
  have reverse: "systems_agree_on target_collection_system replay_reading_system
      (system_definitions target_collection_system\<inter>system_definitions replay_reading_system)"
    using systems_agree_on_sym[OF comparison_reading_agreement] by (simp only: Int_commute)
  have same: "systems_agree_on target_collection_system (system_union target_collection_system replay_reading_system)
      (system_definitions target_collection_system)"
    by (rule system_union_agree_left[OF replay_reading_system_formed reverse])
  show ?thesis using same by (simp only: comparison_reading_system_def system_union_commute)
qed

lemma target_difference_comparison_agreement:
  "systems_agree_on target_difference_system comparison_reading_system (system_definitions target_difference_system)"
proof -
  have source: "systems_agree_on target_difference_system target_collection_system
      (system_definitions target_difference_system)"
    by (simp add: target_collection_system_def target_separation_system_def systems_agree_on_added)
  have included: "system_definitions target_difference_system\<subseteq>system_definitions target_collection_system" by auto
  have target: "systems_agree_on target_collection_system comparison_reading_system
      (system_definitions target_difference_system)"
    by (rule systems_agree_on_subdomain[OF target_collection_comparison_agreement included])
  show ?thesis by (rule systems_agree_on_transitive[OF source target])
qed

lemma generation_reading_agreement:
  "systems_agree_on comparison_reading_system generation_value_system
    (system_definitions comparison_reading_system\<inter>system_definitions generation_value_system)"
proof -
  have inherited: "systems_agree_on target_difference_system comparison_reading_system
      (system_definitions generation_target_system)"
    by (rule systems_agree_on_subdomain[OF target_difference_comparison_agreement generation_target_subdomain])
  have base_same: "systems_agree_on generation_target_system comparison_reading_system
      (system_definitions generation_target_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF generation_target_agreement] inherited])
  have same: "systems_agree_on comparison_reading_system generation_value_system
      (system_definitions generation_target_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF base_same] generation_value_base_agreement])
  have original: "system_definitions target_difference_system\<subseteq>system_definitions comparison_reading_system" by auto
  have base: "system_definitions generation_target_system\<subseteq>system_definitions comparison_reading_system"
    using generation_target_subdomain original by blast
  have fresh: "system_definitions comparison_reading_system\<inter>{139,140,141,142,143,144,145,146}={}"
    by auto
  have overlap: "system_definitions comparison_reading_system\<inter>system_definitions generation_value_system=
      system_definitions generation_target_system"
    using base fresh by (simp only: generation_value_definitions) blast
  show ?thesis using same by (simp only: overlap)
qed

definition generation_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_reading_system=system_union comparison_reading_system generation_value_system"

lemma generation_reading_system_formed [simp]: "schema_system_formed generation_reading_system"
  unfolding generation_reading_system_def
  by (rule system_union_agree_formed[OF comparison_reading_system_formed generation_value_system_formed generation_reading_agreement])

lemma generation_reading_definitions [simp]:
  "system_definitions generation_reading_system=
    system_definitions comparison_reading_system\<union>system_definitions generation_value_system"
  by (simp add: generation_reading_system_def)

lemma generation_reading_call:
  "schema_call_formed generation_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_reading_system \<and> term_formed t"
  using system_union_agree_call[OF comparison_reading_system_formed generation_value_system_formed generation_reading_agreement,
    of d t]
  by (simp only: generation_reading_system_def system_union_definitions comparison_reading_call generation_value_call Un_iff; blast)

theorem generation_reading_old_locality:
  assumes "d\<in>system_definitions comparison_reading_system"
  shows "schema_call_formed generation_reading_system d t \<longleftrightarrow> schema_call_formed comparison_reading_system d t"
    and "(d,t)\<in>positive_meaning generation_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning comparison_reading_system"
  using system_union_agree_left_locality[OF comparison_reading_system_formed generation_value_system_formed
    generation_reading_agreement assms, of t]
  by (simp_all only: generation_reading_system_def)

theorem generation_reading_value_locality:
  assumes "d\<in>system_definitions generation_value_system"
  shows "schema_call_formed generation_reading_system d t \<longleftrightarrow> schema_call_formed generation_value_system d t"
    and "(d,t)\<in>positive_meaning generation_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning generation_value_system"
  using system_union_agree_right_locality[OF comparison_reading_system_formed generation_value_system_formed
    generation_reading_agreement assms, of t]
  by (simp_all only: generation_reading_system_def)

theorem generation_reading_value_operations_exact:
  assumes "d\<in>{139,140,141,142,143,144,145,146}"
  shows "(d,t)\<in>positive_meaning generation_reading_system \<longleftrightarrow> generation_operation_result d t"
proof -
  have member: "d\<in>system_definitions generation_value_system" using assms by auto
  show ?thesis using generation_reading_value_locality(2)[OF member, of t] generation_operations_exact[OF assms, of t] by blast
qed

abbreviation generation_reading_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_reading_operation_result d t \<equiv>
    if d\<in>{132,133,134,135,136,137,138} then target_comparison_operation_result d t
    else generation_operation_result d t"

theorem generation_reading_operations_exact:
  assumes "d\<in>{132,133,134,135,136,137,138,139,140,141,142,143,144,145,146}"
  shows "(d,t)\<in>positive_meaning generation_reading_system \<longleftrightarrow> generation_reading_operation_result d t"
proof (cases "d\<in>{132,133,134,135,136,137,138}")
  case True
  have member: "d\<in>system_definitions comparison_reading_system" using True by auto
  have meaning: "(d,t)\<in>positive_meaning generation_reading_system \<longleftrightarrow> target_comparison_operation_result d t"
    using generation_reading_old_locality(2)[OF member, of t] comparison_reading_operations_exact[OF True, of t] by blast
  show ?thesis using meaning by (simp only: True if_True)
next
  case False
  have selected: "d\<in>{139,140,141,142,143,144,145,146}" using assms False by blast
  show ?thesis using generation_reading_value_operations_exact[OF selected, of t] by (simp only: False if_False)
qed

theorem native_generation_reading_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {132::nat,133,134,135,136,137,138,139,140,141,142,143,144,145,146} \<and>
    (\<forall>d\<in>{132,133,134,135,136,137,138,139,140,141,142,143,144,145,146}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> generation_reading_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{132,133,134,135,136,137,138,139,140,141,142,143,144,145,146}\<subseteq>
      system_definitions generation_reading_system" by auto
  have calls: "schema_call_formed generation_reading_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{132,133,134,135,136,137,138,139,140,141,142,143,144,145,146}" for d t
    using generation_reading_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF generation_reading_system_formed selected calls generation_reading_operations_exact])
qed

text \<open>
  Generation value operations are defined and proved over their own target
  base. This separate join preserves that local program and the complete
  earlier reader program through shared-definition agreement. All earlier
  call boundaries and meanings remain available, including replay.

  The combined native program has distinct sites for all fifteen comparison
  and value operations before future arguments are supplied. Its complete
  original scope, artifacts, and bindings remain unchanged across those
  applications. The integration adds no clause to any earlier definition.
\<close>

end
