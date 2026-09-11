theory Factor_Construction_Permission_Admission
  imports Factor_Related_Test_Admission Factor_Construction_Permission_Completion Factor_Permission_Admission
begin

section \<open>The comparison reference is established before submitted permissions\<close>

locale construction_permission_admission =
  fixes C :: "local_address option artifact_environment" and k :: "local_address option definition_site"
    and c :: factor_term and cu cr R
  assumes reference: "native_package_at C cu cr R" and reference_value: "environment_value_presents C c"
    and entry: "k\<in>system_definitions R"
    and comparison: "\<And>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents p q"
begin

lemma reference_fields: "term_formed c" "term_formed (definition_site_value k)"
proof -
  have formed: "environment_formed C" using environment_value_presents_formed[OF reference_value] by blast
  have position: "k\<in>environment_positions C" by (rule native_package_entry_position[OF reference entry])
  show "term_formed c" using environment_value_presents_formed[OF reference_value] by blast
  show "term_formed (definition_site_value k)" using environment_position_address[OF formed position] by simp
qed

sublocale checker: related_test_admission c "definition_site_value k"
  by (rule related_test_admission.intro[OF reference_fields])

sublocale permission: presented_permission_admission construction_account_presents
  construction_account_domain "\<lambda>t. \<exists>a. construction_account_presents a t" C k c cu cr R
  by (rule presented_permission_admission.intro[OF construction_account_presentation_class _
    reference reference_value entry comparison])
    (use construction_account_formed in blast)

theorem profile_permission:
  assumes package: "native_package_at E pu pr P"
    and profile: "native_related_test_package C k E pu pr d"
  shows "construction_permission_invariant P d"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation construction_account_presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
proof -
  have invariant: "presented_program_invariant construction_account_presents P d"
    by (rule permission.profile_permission(1)[OF package profile])
  show "construction_permission_invariant P d"
    using invariant by (simp only: construction_permission_observations presented_program_observations)
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    by (rule permission.profile_permission(2)[OF package profile])
  show "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation construction_account_presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (rule permission.profile_permission(3)[OF package profile])
qed

theorem admitted_permission:
  assumes package: "native_package_at E pu pr P"
    and source: "program_entry_value_presents E pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  shows "construction_permission_invariant P d"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation construction_account_presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
proof -
  have invariant: "presented_program_invariant construction_account_presents P d"
    by (rule permission.admitted_permission(1)[OF package source checked])
  show "construction_permission_invariant P d"
    using invariant by (simp only: construction_permission_observations presented_program_observations)
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    by (rule permission.admitted_permission(2)[OF package source checked])
  show "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation construction_account_presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (rule permission.admitted_permission(3)[OF package source checked])
qed

theorem permission_conditions_discharged:
  assumes "native_package_at E pu pr P" "program_entry_value_presents E pu pr d p"
    "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  shows "remaining_obligations {q. observation_condition q} (construction_permission_obligations P d)={}"
  using admitted_permission(1)[OF assms]
  by (simp only: remaining_obligations_empty construction_permission_obligations_exact)

theorem recorded_construction:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and application: "native_application_at F au ar d z I K"
    and source: "program_entry_value_presents F pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    and minimal: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact (construction_account_output a)"
    and account: "construction_account_presents a z" and truth: "(d,z)\<in>positive_meaning P"
  shows "recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
proof -
  have invariant: "construction_permission_invariant P d" by (rule admitted_permission(1)[OF package source checked])
  show ?thesis by (simp only: recorded_construction_residual_exact[OF scope package application])
    (use minimal payload account truth invariant in
      \<open>auto simp: remaining_obligations_def recorded_construction_obligations_def\<close>)
qed

theorem candidate_total:
  assumes package: "native_package_at E pu pr P" and retained: "environment_included C E"
    and callees: "k\<in>system_definitions P" "test\<in>system_definitions P"
  shows "\<exists>F u Q d. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    d\<notin>system_definitions P \<and> system_definitions Q=insert d (system_definitions P) \<and>
    construction_permission_invariant Q d \<and>
    (\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P))"
  using permission.candidate_total[OF package retained callees]
  by (simp only: construction_permission_observations presented_program_observations)

theorem inhabited_admission:
  "\<exists>F u Q d p. closed_native_package_at F u [] Q \<and> program_entry_value_presents F u [] d p \<and>
    construction_permission_invariant Q d \<and>
    (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  using permission.inhabited_admission
  by (simp only: construction_permission_observations presented_program_observations)

end

section \<open>One proved native reference and checker precede all future candidates\<close>

theorem fixed_native_construction_permission_checker:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu R k c.
    \<exists>B :: local_address option artifact_environment. \<exists>bu T entry.
    closed_native_package_at C cu [] R \<and> environment_value_presents C c \<and> k\<in>system_definitions R \<and>
    (\<forall>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents p q) \<and>
    (\<forall>E pu pr P d p. native_package_at E pu pr P \<longrightarrow> program_entry_value_presents E pu pr d p \<longrightarrow>
      related_test_admission_result c (definition_site_value k) p \<longrightarrow> construction_permission_invariant P d) \<and>
    (\<exists>E pu P d p. closed_native_package_at E pu [] P \<and> program_entry_value_presents E pu [] d p \<and>
      construction_permission_invariant P d \<and> related_test_admission_result c (definition_site_value k) p) \<and>
    closed_native_package_at B bu [] T \<and>
    (\<forall>p. term_formed p \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> related_test_admission_result c (definition_site_value k) p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))"
proof -
  obtain C :: "local_address option artifact_environment" and cu R k where reference:
    "closed_native_package_at C cu [] R" "k\<in>system_definitions R"
    "\<forall>z. (k,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)"
    using native_construction_correspondence by blast
  have package: "native_package_at C cu [] R" using reference(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed C" using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain c where presented: "environment_value_presents C c" using environment_value_presents_total[OF formed] by blast
  have comparison: "(k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents p q" for p q
    using reference(3)[rule_format, of "Pair_Term p q"] by simp
  interpret permission: construction_permission_admission C k c cu "[]" R
    by (rule construction_permission_admission.intro[OF package presented reference(2) comparison])
  have correct: "construction_permission_invariant P d"
    if "native_package_at E pu pr P" "program_entry_value_presents E pu pr d p"
      "related_test_admission_result c (definition_site_value k) p" for E pu pr P d p
    by (rule permission.admitted_permission(1)[OF that(1,2)]) (use that(3) in \<open>simp only: permission.checker.exact\<close>)
  have inhabited: "\<exists>E pu P d p. closed_native_package_at E pu [] P \<and> program_entry_value_presents E pu [] d p \<and>
      construction_permission_invariant P d \<and> related_test_admission_result c (definition_site_value k) p"
    using permission.inhabited_admission by (simp only: permission.checker.exact)
  obtain B :: "local_address option artifact_environment" and bu T entry where checker:
    "closed_native_package_at B bu [] T"
    "\<forall>p. term_formed p \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> related_test_admission_result c (definition_site_value k) p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x))"
    using permission.checker.native_checker by (elim exE conjE) (rule that; assumption)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ R], rule exI[of _ k], rule exI[of _ c],
      rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ entry])
    (use reference(1,2) presented comparison correct inhabited checker in blast)
qed

text \<open>
  The complete native profile check now supplies global construction permission
  invariance for the actual submitted program. The comparison reference is
  obtained independently from the complete correspondence implementation and
  fixed before future candidates. One ordinary native checker evaluates the
  finite evidence, preserves its own scope, and has constructed admitted inputs.

  Every compatible package containing the comparison and a supplied test has
  an admitted new permission definition, with all previous meanings retained.
  The original recorded-cause reduction consumes native profile admission
  alongside least scope, exact payload, complete account, and positive truth.
  It does not change the generation's program or insert evidence into identity.

  This sufficient structural class does not decide invariance of every positive
  program. General recorded-cause admission, native presentations of mathematical
  contracts and proofs, higher protocols, reflection, genesis, and the complete
  repository audit remain separate obligations.
\<close>

end
