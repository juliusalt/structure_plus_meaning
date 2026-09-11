theory Factor_Native_Continuation
  imports Factor_Continuation Factor_Compiled_Applications Factor_Judgment_Scopes
begin

section \<open>Future continuation calls preserve every existing semantic binding\<close>

theorem native_continuation_application_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and invariant: "continuation_permission_invariant P d"
    and present: "continuation_value_presents S T U C cu cr t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    (native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t) \<and>
    (native_continuation_at F pu pr au [] S T U C cu cr\<longleftrightarrow>factor_continues P d S T U C cu cr) \<and>
    (native_advance_at F pu pr au [] S T U C cu cr\<longleftrightarrow>factor_advances P d S T U C cu cr) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w)"
proof -
  have tf: "term_formed t" using continuation_value_presents_formed[OF present] by blast
  obtain F au I K where future: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t"
    "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w"
    using native_application_extension_total[OF package member tf] by blast
  have permission: "native_continuation_at F pu pr au [] S T U C cu cr\<longleftrightarrow>factor_continues P d S T U C cu cr"
    by (rule native_continuation_at_presentation[OF future(4,5) invariant present])
  have advance: "native_advance_at F pu pr au [] S T U C cu cr\<longleftrightarrow>factor_advances P d S T U C cu cr"
    by (rule native_advance_at_presentation[OF future(4,5) invariant present])
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
       (use future permission advance in blast)
qed

lemma compiled_continuation_permission:
  assumes injective: "inj_on g (system_definitions P)" and member: "d\<in>system_definitions P"
    and meaning: "positive_meaning Q=image (map_prod g id) (positive_meaning P)"
    and boundary: "\<And>t. schema_call_formed Q (g d) t\<longleftrightarrow>schema_call_formed P d t"
  shows "factor_continues Q (g d) S T U C cu cr\<longleftrightarrow>factor_continues P d S T U C cu cr"
  using compiled_system_meaning_at[OF injective member meaning] boundary
  by (simp add: factor_continues_def continuation_permission_invariant_def)

theorem native_continuation_program_compilation:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes formed: "schema_system_formed P" and member: "d\<in>system_definitions P"
    and invariant: "continuation_permission_invariant P d"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> continuation_permission_invariant Q e \<and>
    (\<forall>t. (schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t) \<and>
      ((e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P)) \<and>
    (\<forall>S T U C cu cr. factor_continues Q e S T U C cu cr\<longleftrightarrow>factor_continues P d S T U C cu cr) \<and>
    (\<forall>S T U C cu cr. factor_advances Q e S T U C cu cr\<longleftrightarrow>factor_advances P d S T U C cu cr)"
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
  have admitted: "continuation_permission_invariant Q (g d)"
    using continuation_permission_invariant_transport[OF boundary meaning] invariant by blast
  have inside: "g d\<in>system_definitions Q"
    using compiled(4) member by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have permission: "\<And>S T U C cu cr. factor_continues Q (g d) S T U C cu cr\<longleftrightarrow>
      factor_continues P d S T U C cu cr"
    by (rule compiled_continuation_permission[OF compiled(1) member compiled(5) boundary])
  have advance: "\<And>S T U C cu cr. factor_advances Q (g d) S T U C cu cr\<longleftrightarrow>
      factor_advances P d S T U C cu cr"
    by (simp only: factor_advances_def permission)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g d"])
       (use compiled(2,3) inside admitted boundary meaning permission advance in blast)
qed

section \<open>The complete minimal judgment scope is recordable\<close>

theorem native_continuation_judgment_restriction:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_continuation_at (native_judgment_environment E pu pr au ar) pu pr au ar S T U C cu cr
    \<longleftrightarrow>native_continuation_at E pu pr au ar S T U C cu cr"
  by (simp only: native_continuation_with_reads[OF native_judgment_environment_recovers(1,2)[OF package app]]
      native_continuation_with_reads[OF package app])

theorem native_continuation_recordable:
  fixes E :: "local_address option artifact_environment"
  assumes permitted: "native_continuation_at E pu pr au ar S T U C cu cr"
  shows "\<exists>F R. judgment_value_quoted_at R [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_continuation_at F pu pr au ar S T U C cu cr \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  obtain P d t I K where read: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using permitted unfolding native_continuation_at_def by blast
  obtain F R where quote: "judgment_value_quoted_at R [] F pu pr au ar"
    "F=native_judgment_environment F pu pr au ar"
    and kept: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and canonical: "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_judgment_recordable[OF read] by blast
  have truth: "native_continuation_at F pu pr au ar S T U C cu cr"
    using permitted by (simp only: native_continuation_with_reads[OF kept] native_continuation_with_reads[OF read])
  show ?thesis using quote canonical truth by blast
qed

text \<open>
  A single closed finite compilation preserves the policy for every complete
  future argument. Actual native applications keep the original program scope
  and all existing artifacts and bindings. The submitted material remains
  ordinary argument data. Recording the minimal judgment scope retains that
  program and its complete call; the subject is recovered from the call.
\<close>

end
