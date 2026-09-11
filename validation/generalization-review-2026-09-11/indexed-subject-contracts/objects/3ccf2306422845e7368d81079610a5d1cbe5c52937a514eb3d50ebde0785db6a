theory Factor_Adoption_Permission_Admission
  imports Factor_Permission_Admission Factor_Permission_Families Factor_Adoption_Comparison
    Factor_Certified_Authority
begin

section \<open>The complete adoption comparison fixes the shared admission instance\<close>

locale adoption_permission_admission =
  fixes C :: "local_address option artifact_environment" and k :: "local_address option definition_site"
    and c :: factor_term and cu cr R
  assumes reference: "native_package_at C cu cr R"
    and reference_value: "environment_value_presents C c"
    and entry: "k\<in>system_definitions R"
    and comparison: "\<And>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport adoption_context_presents adoption_context_presents p q"
begin

sublocale permission: presented_permission_admission adoption_context_presents
  adoption_context_formed "\<lambda>t. \<exists>a. adoption_context_presents a t" C k c cu cr R
  by (rule presented_permission_admission.intro[OF adoption_context_presentation_class _
    reference reference_value entry comparison])
    (use adoption_context_value_formed in blast)

theorem profile_permission:
  assumes package: "native_package_at E pu pr P" and profile: "native_related_test_package C k E pu pr d"
  shows "adoption_permission_invariant P d"
    "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    "\<exists>test\<in>system_definitions P. (\<lambda>t. (d,t)\<in>positive_meaning P)=
      saturate_observation adoption_context_presents (\<lambda>t. (test,t)\<in>positive_meaning P)"
  using permission.profile_permission[OF package profile]
  by (simp_all only: adoption_invariant_as_presented)

theorem admitted_permission:
  assumes package: "native_package_at E pu pr P" and source: "program_entry_value_presents E pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  shows "adoption_permission_invariant P d"
    "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    "\<exists>test\<in>system_definitions P. (\<lambda>t. (d,t)\<in>positive_meaning P)=
      saturate_observation adoption_context_presents (\<lambda>t. (test,t)\<in>positive_meaning P)"
  using permission.admitted_permission[OF package source checked]
  by (simp_all only: adoption_invariant_as_presented)

theorem native_adoption_with_checked_permission:
  assumes package: "native_package_at E pu pr P" and application: "native_application_at E au ar d t I K"
    and source: "program_entry_value_presents E pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    and presented: "adoption_value_presents A G purpose t"
  shows "native_adoption_judgment_at E pu pr au ar A G purpose \<longleftrightarrow>
    (d,t)\<in>positive_meaning P"
  using admitted_permission(1)[OF package source checked] presented
  by (simp only: native_adoption_with_reads[OF package application]; simp)

theorem certified_adoption_with_checked_permission:
  assumes package: "native_package_at E pu pr P" and application: "native_application_at E au ar d t I K"
    and source: "program_entry_value_presents E pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    and presented: "adoption_value_presents A G purpose t"
  shows "certified_adoption_at E pu pr au ar root A G purpose \<longleftrightarrow>
    native_replay_at E pu pr au ar root {}"
  using admitted_permission(1)[OF package source checked] presented
  by (simp only: certified_adoption_with_reads[OF package application]; simp)

theorem checked_permission_conditions_discharged:
  assumes "native_package_at E pu pr P" "program_entry_value_presents E pu pr d p"
    "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  shows "remaining_obligations {q. observation_condition q}
    (program_invariance_obligations
      (presentation_transport adoption_context_presents adoption_context_presents) P d)={}"
  using admitted_permission(1)[OF assms]
  by (simp only: remaining_obligations_empty program_invariance_obligations_exact
    adoption_invariant_as_presented presented_program_observations)

theorem universal_admitted_policy:
  assumes test_entry: "test\<in>system_definitions R"
    and admission: "\<And>t. (test,t)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>a. adoption_context_presents a t)"
  shows "\<exists>F u Q d. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    d\<notin>system_definitions R \<and> system_definitions Q=insert d (system_definitions R) \<and>
    native_related_test_package C k F u [] d \<and> adoption_permission_invariant Q d \<and>
    (\<forall>t. schema_call_formed Q d t \<longleftrightarrow> term_formed t) \<and>
    (\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow> (\<exists>a. adoption_context_presents a t)) \<and>
    (\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>t.
      (schema_call_formed Q b t \<longleftrightarrow> schema_call_formed R b t) \<and>
      ((b,t)\<in>positive_meaning Q \<longleftrightarrow> (b,t)\<in>positive_meaning R))"
proof -
  obtain F u Q d where built:
    "closed_native_package_at F u [] Q" "native_package_environment F u []=F"
    "d\<notin>system_definitions R" "system_definitions Q=insert d (system_definitions R)"
    "native_related_test_package C k F u [] d" "presented_program_invariant adoption_context_presents Q d"
    "\<forall>t. schema_call_formed Q d t \<longleftrightarrow> term_formed t"
    "(\<lambda>t. (d,t)\<in>positive_meaning Q)=
      saturate_observation adoption_context_presents (\<lambda>t. (test,t)\<in>positive_meaning R)"
    "\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    "\<forall>b\<in>system_definitions R. \<forall>t.
      (schema_call_formed Q b t \<longleftrightarrow> schema_call_formed R b t) \<and>
      ((b,t)\<in>positive_meaning Q \<longleftrightarrow> (b,t)\<in>positive_meaning R)"
    using permission.candidate_completion[OF reference environment_included_refl entry test_entry] by blast
  have invariant: "adoption_permission_invariant Q d" using built(6) by (simp only: adoption_invariant_as_presented)
  have source: "(\<lambda>t. (test,t)\<in>positive_meaning R)=(\<lambda>t. \<exists>a. adoption_context_presents a t)"
    by (intro ext) (rule admission)
  have exact: "(d,t)\<in>positive_meaning Q \<longleftrightarrow> (\<exists>a. adoption_context_presents a t)" for t
    using fun_cong[OF built(8), of t]
    by (simp only: source presentation_admission_saturation[OF adoption_context_presentation_class])
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ d])
    (use built(1-5,7,9,10) invariant exact in blast)
qed

end

section \<open>A fixed native checker has constructed policies and actual certified calls\<close>

theorem fixed_native_adoption_permission_checker:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu R k c.
    \<exists>B :: local_address option artifact_environment. \<exists>bu T checker.
    closed_native_package_at C cu [] R \<and> environment_value_presents C c \<and> k\<in>system_definitions R \<and>
    (\<forall>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport adoption_context_presents adoption_context_presents p q) \<and>
    (\<forall>E pu pr P d p. native_package_at E pu pr P \<longrightarrow> program_entry_value_presents E pu pr d p \<longrightarrow>
      related_test_admission_result c (definition_site_value k) p \<longrightarrow> adoption_permission_invariant P d) \<and>
    closed_native_package_at B bu [] T \<and>
    (\<forall>p. term_formed p \<longrightarrow>
      (\<exists>H au I K. environment_formed H \<and> environment_included B H \<and> au\<notin>environment_uses B \<and>
        native_package_at H bu [] T \<and> native_application_at H au [] checker p I K \<and>
        native_package_environment H bu []=B \<and> native_application_formed H bu [] au [] \<and>
        (native_positive_holds H bu [] au [] \<longleftrightarrow> related_test_admission_result c (definition_site_value k) p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at H v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot H v s x \<longleftrightarrow> binds_slot B v s x))) \<and>
    (\<exists>F u Q d. closed_native_package_at F u [] Q \<and> adoption_permission_invariant Q d \<and>
      (\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
        related_test_admission_result c (definition_site_value k) p) \<and>
      (\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
        (\<exists>H au root I K. certified_adoption_at H u [] au [] root A G purpose \<and>
          native_package_at H u [] Q \<and> native_application_at H au [] d t I K \<and>
          native_package_environment H u []=native_package_environment F u [])))"
proof -
  obtain C :: "local_address option artifact_environment" and cu R k admit where reference:
    "closed_native_package_at C cu [] R" "{k,admit}\<subseteq>system_definitions R"
    "\<forall>t. (k,t)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. t=Pair_Term p q \<and> presentation_transport adoption_context_presents adoption_context_presents p q)"
    "\<forall>t. (admit,t)\<in>positive_meaning R \<longleftrightarrow> (\<exists>a. adoption_context_presents a t)"
    using native_adoption_value_reference by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at C cu [] R" using reference(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed C" using native_package_projection(1)[OF package]
    by (simp add: native_package_formed_def)
  obtain c where encoded: "environment_value_presents C c" using environment_value_presents_total[OF formed] by blast
  have entry: "k\<in>system_definitions R" and test: "admit\<in>system_definitions R" using reference(2) by blast+
  have comparison: "(k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport adoption_context_presents adoption_context_presents p q" for p q
    using reference(3)[rule_format, of "Pair_Term p q"] by simp
  interpret adoption: adoption_permission_admission C k c cu "[]" R
    by (rule adoption_permission_admission.intro[OF package encoded entry comparison])
  have sound: "adoption_permission_invariant P d"
    if "native_package_at E pu pr P" "program_entry_value_presents E pu pr d p"
      "related_test_admission_result c (definition_site_value k) p" for E pu pr P d p
    by (rule adoption.admitted_permission(1)[OF that(1,2)])
      (use that(3) in \<open>simp only: adoption.permission.checker.exact\<close>)
  obtain F u Q d where policy:
    "closed_native_package_at F u [] Q" "adoption_permission_invariant Q d"
    "\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow> (\<exists>a. adoption_context_presents a t)"
    "\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    using adoption.universal_admitted_policy[OF test reference(4)[rule_format]] by blast
  have candidate: "native_package_at F u [] Q" using policy(1) by (simp add: closed_native_package_at_def)
  have future: "\<exists>H au root I K. certified_adoption_at H u [] au [] root A G purpose \<and>
      native_package_at H u [] Q \<and> native_application_at H au [] d t I K \<and>
      native_package_environment H u []=native_package_environment F u []"
    if presented: "adoption_value_presents A G purpose t" for A G purpose t
  proof -
    have available: "\<exists>a. adoption_context_presents a t"
      by (rule exI[of _ "(A,G,purpose)"]) (use presented in \<open>simp only: adoption_context_fields\<close>)
    have truth: "(d,t)\<in>positive_meaning Q" using policy(3)[rule_format, of t] available by blast
    have adopted: "factor_adopts Q d A G purpose"
      using policy(2) presented truth by (auto simp: factor_adopts_def)
    show ?thesis by (rule certified_adoption_presentation_total[OF candidate adopted presented])
  qed
  obtain B :: "local_address option artifact_environment" and bu T checker where checked_program:
    "closed_native_package_at B bu [] T"
    "\<forall>p. term_formed p \<longrightarrow>
      (\<exists>H au I K. environment_formed H \<and> environment_included B H \<and> au\<notin>environment_uses B \<and>
        native_package_at H bu [] T \<and> native_application_at H au [] checker p I K \<and>
        native_package_environment H bu []=B \<and> native_application_formed H bu [] au [] \<and>
        (native_positive_holds H bu [] au [] \<longleftrightarrow> related_test_admission_result c (definition_site_value k) p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at H v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot H v s x \<longleftrightarrow> binds_slot B v s x))"
    using adoption.permission.checker.native_checker by (elim exE conjE) (rule that; assumption)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ R], rule exI[of _ k], rule exI[of _ c],
      rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ checker])
    (use reference(1) encoded entry comparison sound checked_program policy(1,2,4) future
      in \<open>simp only: adoption.permission.checker.exact; blast\<close>)
qed

text \<open>
  The same ordinary profile checker now admits adoption permissions against
  an independently compiled three-field comparator. Its semantic result
  discharges the original global invariance condition. The original actual
  package, entry, application, and presented subject stay fixed.

  Under that admission, closed replay is exactly the remaining certificate
  condition for the particular call. The construction exhibits one fixed
  checker and an admitted native policy with certified calls on every complete
  adoption presentation. Component totality supplies presentations for every
  formed authority, generation, and purpose; this is not finite sample coverage.

  The exhibited policy accepts the whole raw adoption domain. It supplies no
  generation-cause validity, publication, or currentness. Arbitrary original
  program invariance and native checking of the mathematical comparison,
  saturation, and class proofs remain separate obligations.
\<close>

end
