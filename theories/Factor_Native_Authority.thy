theory Factor_Native_Authority
  imports Factor_Authority Factor_Compiled_Applications
begin

section \<open>Actual future applications of an ordinary adoption policy\<close>

theorem native_adoption_application_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P"
    and member: "d\<in>system_definitions P"
    and invariant: "adoption_permission_invariant P d"
    and present: "adoption_value_presents A G purpose t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    (native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t) \<and>
    (native_adoption_judgment_at F pu pr au [] A G purpose\<longleftrightarrow>factor_adopts P d A G purpose) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w)"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain R where source: "artifact_at E (fst d) R" "anchor_formed (R,snd d)"
    using native_package_definition_anchor[OF package member] by blast
  have tf: "term_formed t" using adoption_value_presents_formed[OF present] by blast
  let ?F="future_call_environment E (fst d) R (snd d) t"
  let ?au="future_call_use E (fst d)"
  have ff: "environment_formed ?F" by (rule future_call_environment_formed[OF ef source tf])
  have included: "environment_included E ?F" by (rule future_call_includes_existing)
  have fresh: "?au\<notin>environment_uses E" by (rule future_call_use_fresh[OF ef])
  obtain I K where app: "native_application_at ?F ?au [] d t I K"
    using future_call_representation[OF ef source tf] by auto
  have preserved: "native_package_at ?F pu pr P"
    by (rule future_call_preserves_program(1)[OF package source tf])
  have canonical: "native_package_environment ?F pu pr=native_package_environment E pu pr"
    by (rule future_call_preserves_program(2)[OF package source tf])
  have boundary: "native_application_formed ?F pu pr ?au []\<longleftrightarrow>schema_call_formed P d t"
    by (rule native_application_formed_with_reads[OF preserved app])
  have truth: "native_adoption_judgment_at ?F pu pr ?au [] A G purpose\<longleftrightarrow>
      factor_adopts P d A G purpose"
    by (rule native_adoption_at_presentation[OF preserved app invariant present])
  have arts: "\<forall>v\<in>environment_uses E. \<forall>S. artifact_at ?F v S\<longleftrightarrow>artifact_at E v S"
    by (intro ballI allI) (rule future_call_existing_artifacts[OF ef source tf]; assumption)
  have bindings: "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot ?F v k w\<longleftrightarrow>binds_slot E v k w"
    by (intro ballI allI) (rule future_call_existing_bindings[OF ef]; assumption)
  show ?thesis
    by (rule exI[of _ ?F], rule exI[of _ ?au], rule exI[of _ I], rule exI[of _ K])
       (use ff included fresh preserved app canonical boundary truth arts bindings in blast)
qed

lemma compiled_adoption_permission:
  assumes injective: "inj_on g (system_definitions P)"
    and member: "d\<in>system_definitions P"
    and meaning: "positive_meaning Q=image (map_prod g id) (positive_meaning P)"
    and boundary: "\<And>t. schema_call_formed Q (g d) t\<longleftrightarrow>schema_call_formed P d t"
  shows "factor_adopts Q (g d) A G purpose\<longleftrightarrow>factor_adopts P d A G purpose"
  using compiled_system_meaning_at[OF injective member meaning] boundary
  by (simp add: factor_adopts_def adoption_permission_invariant_def)

section \<open>Compilation preserves adoption for every complete argument\<close>

theorem native_adoption_program_compilation:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes formed: "schema_system_formed P" and member: "d\<in>system_definitions P"
    and invariant: "adoption_permission_invariant P d"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> adoption_permission_invariant Q e \<and>
    (\<forall>t. (schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t) \<and>
      ((e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P)) \<and>
    (\<forall>A G purpose. factor_adopts Q e A G purpose\<longleftrightarrow>factor_adopts P d A G purpose)"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site" and E pu Q where compiled:
    "inj_on g (system_definitions P)" "closed_native_package_at E pu [] Q"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g P) Q"
    "positive_meaning Q=image (map_prod g id) (positive_meaning P)"
    using program_compilation_total[OF formed] by metis
  have boundary: "\<And>t. schema_call_formed Q (g d) t\<longleftrightarrow>schema_call_formed P d t"
    by (rule compiled_system_call_boundary[OF formed compiled(1,4) member])
  have meaning: "\<And>t. (g d,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule compiled_system_meaning_at[OF compiled(1) member compiled(5)])
  have admitted: "adoption_permission_invariant Q (g d)"
    using adoption_permission_invariant_transport[OF boundary meaning] invariant by blast
  have inside: "g d\<in>system_definitions Q"
    using compiled(4) member by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have permission: "\<And>A G purpose. factor_adopts Q (g d) A G purpose\<longleftrightarrow>
      factor_adopts P d A G purpose"
    by (rule compiled_adoption_permission[OF compiled(1) member compiled(5) boundary])
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g d"])
       (use compiled(2,3) inside admitted boundary meaning permission in blast)
qed

text \<open>
  One closed finite compilation preserves the selected definition's formation
  boundary, truth, presentation invariance, and adoption relation for every
  argument. Every complete adoption presentation then has an actual future
  native call under that same package. Adding the call preserves the complete
  program environment and every existing artifact and binding.
\<close>

end
