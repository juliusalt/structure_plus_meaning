theory Factor_Native_Construction
  imports Factor_Construction_Recovery Factor_Construction_Omissions Factor_Compiled_Applications
begin

section \<open>Actual future native applications of construction permission\<close>

lemma native_construction_permission_with_reads:
  assumes package: "native_package_at E pu pr P"
    and call: "native_application_at E au ar d t I K"
    and built: "source_constructs xs B W R"
    and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    and present: "construction_claim_presents xs B W R t"
  shows "native_positive_holds E pu pr au ar \<longleftrightarrow> factor_constructs P d xs B W R"
  using native_positive_holds_with_reads[OF package call]
    factor_construction_at_presentation[OF built coords invariant present] by blast

theorem native_construction_application_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P"
    and member: "d \<in> system_definitions P"
    and built: "source_constructs xs B W R"
    and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    and present: "construction_claim_presents xs B W R t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au \<notin> environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and>
    native_package_environment F pu pr = native_package_environment E pu pr \<and>
    (native_positive_holds F pu pr au [] \<longleftrightarrow> factor_constructs P d xs B W R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain S where source: "artifact_at E (fst d) S" "anchor_formed (S,snd d)"
    using native_package_definition_anchor[OF package member] by blast
  have tf: "term_formed t" by (rule construction_claim_presents_formed[OF built coords present])
  let ?F = "future_call_environment E (fst d) S (snd d) t"
  let ?au = "future_call_use E (fst d)"
  have ff: "environment_formed ?F" by (rule future_call_environment_formed[OF ef source tf])
  have included: "environment_included E ?F" by (rule future_call_includes_existing)
  have fresh: "?au \<notin> environment_uses E" by (rule future_call_use_fresh[OF ef])
  obtain I K where call: "native_application_at ?F ?au [] d t I K"
    using future_call_representation[OF ef source tf] by auto
  have preserved: "native_package_at ?F pu pr P"
    by (rule future_call_preserves_program(1)[OF package source tf])
  have canonical: "native_package_environment ?F pu pr = native_package_environment E pu pr"
    by (rule future_call_preserves_program(2)[OF package source tf])
  have truth: "native_positive_holds ?F pu pr ?au [] \<longleftrightarrow> factor_constructs P d xs B W R"
    by (rule native_construction_permission_with_reads[OF preserved call built coords invariant present])
  have arts: "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
    by (intro ballI allI) (rule future_call_existing_artifacts[OF ef source tf]; assumption)
  have bindings: "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w"
    by (intro ballI allI) (rule future_call_existing_bindings[OF ef]; assumption)
  show ?thesis
    by (rule exI[of _ ?F], rule exI[of _ ?au], rule exI[of _ I], rule exI[of _ K])
       (use ff included fresh call preserved canonical truth arts bindings in blast)
qed

lemma compiled_construction_permission:
  assumes injective: "inj_on g (system_definitions P)"
    and member: "d \<in> system_definitions P"
    and meaning: "positive_meaning Q = map_prod g id ` positive_meaning P"
    and boundary: "\<And>t. schema_call_formed Q (g d) t \<longleftrightarrow> schema_call_formed P d t"
  shows "factor_constructs Q (g d) xs B W R \<longleftrightarrow> factor_constructs P d xs B W R"
  using compiled_system_meaning_at[OF injective member meaning] boundary
  by (simp add: factor_constructs_def construction_permission_invariant_def)

theorem native_construction_presentations_agree:
  assumes first_package: "native_package_at E pu pr P"
    and second_package: "native_package_at F qu qr P"
    and first_call: "native_application_at E au ar d t I K"
    and second_call: "native_application_at F bu br d v J L"
    and built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    and first: "construction_claim_presents xs B W R t"
    and second: "construction_claim_presents xs B W R v"
  shows "native_application_formed E pu pr au ar \<longleftrightarrow> native_application_formed F qu qr bu br"
    "native_positive_holds E pu pr au ar \<longleftrightarrow> native_positive_holds F qu qr bu br"
  using native_application_formed_with_reads[OF first_package first_call]
    native_application_formed_with_reads[OF second_package second_call]
    native_positive_holds_with_reads[OF first_package first_call]
    native_positive_holds_with_reads[OF second_package second_call]
    construction_permission_invariantD[OF invariant built coords first second] by blast+

text \<open>
  Every complete presentation of a formed construction account has an actual
  future native application. When the selected definition has proved invariance
  across all presentations, native truth is exactly construction permission. Adding the
  application preserves the canonical program environment and every old
  artifact and binding. The existing general program compiler also preserves
  this permission under its injective definition coordinates.
\<close>

end
