theory Factor_Permission_Completion
  imports Factor_Permission_Admission Factor_Program_Tests
begin

theorem presented_completion_truth_agreement:
  assumes class_contract: "presentation_class R D A"
    and completion: "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation R (\<lambda>z. (d,z)\<in>positive_meaning P)"
  shows "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      (\<lambda>z. A z \<and> (d,z)\<in>positive_meaning P) \<longleftrightarrow>
    rel_fun (presentation_transport R R) (=)
      (\<lambda>z. (d,z)\<in>positive_meaning P) (\<lambda>z. (d,z)\<in>positive_meaning P)"
  by (simp only: completion presentation_class.saturation_fixed_iff[OF class_contract])

section \<open>The same fixed reference completes every original finite test\<close>

locale presented_permission_completion = presented_permission_admission presents subject admissible C k c cu cr R
  for presents :: "'v \<Rightarrow> factor_term \<Rightarrow> bool" and subject admissible C k c cu cr R +
  fixes query :: "local_address option definition_site"
  assumes query_entry: "query\<in>system_definitions R"
    and query_meaning: "\<And>z. (query,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
begin

theorem represented_native_test_completion:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e test. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<noteq>test \<and> {e,test}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert e (insert test (system_definitions R)) \<and>
    native_related_test_package C k F u [] e \<and> presented_program_invariant presents Q e \<and>
    (\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R))"
proof -
  have cf: "environment_formed C" using environment_value_presents_formed[OF reference_value] by blast
  have ef: "environment_formed E" using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain p where source: "environment_value_presents E p" using environment_value_presents_total[OF ef] by blast
  obtain H tu v T where installed: "environment_formed H" "environment_included C H"
    "(tu,[])\<notin>system_definitions R" "native_package_at H v [] T"
    "system_definitions T=insert (tu,[]) (system_definitions R)"
    "\<forall>z. schema_call_formed T (tu,[]) z \<longleftrightarrow> term_formed z"
    "\<forall>z. ((tu,[]),z)\<in>positive_meaning T \<longleftrightarrow> (d,z)\<in>positive_meaning P"
    "\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed T b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning T \<longleftrightarrow> (b,z)\<in>positive_meaning R)"
    using native_program_test_total[OF reference query_entry query_meaning package source_entry source]
    by (elim exE conjE) (rule that; assumption)
  let ?test="(tu,[])"
  have members: "k\<in>system_definitions T" "?test\<in>system_definitions T"
    using installed(5) entry by auto
  obtain F u Q e where built: "closed_native_package_at F u [] Q" "native_package_environment F u []=F"
    "e\<notin>system_definitions T" "system_definitions Q=insert e (system_definitions T)"
    "native_related_test_package C k F u [] e"
    "\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z"
    "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (?test,z)\<in>positive_meaning T)"
    "\<forall>b\<in>system_definitions T. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed T b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning T)"
    using candidate_completion[OF installed(4,2) members] by blast
  have original: "(\<lambda>z. (?test,z)\<in>positive_meaning T)=(\<lambda>z. (d,z)\<in>positive_meaning P)"
    by (intro ext) (rule installed(7)[rule_format])
  have completion: "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
    using built(7) by (simp only: original)
  have boundary: "schema_call_formed Q e z \<longleftrightarrow> term_formed z" for z using built(6) by blast
  have invariant: "presented_program_invariant presents Q e" by (rule presented_program_from_saturation[OF class_contract value_formed boundary completion])
  have tested: "(?test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P" for z
    using built(8)[rule_format, OF members(2), of z] installed(7)[rule_format, of z] by blast
  have test_call: "schema_call_formed Q ?test z \<longleftrightarrow> term_formed z" for z
    using built(8)[rule_format, OF members(2), of z] installed(6)[rule_format, of z] by blast
  have accepted: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    if "program_entry_value_presents F u [] e p" for p
    using built(5) checker.on_presentations[OF reference_value refl, of "((F,(u,[])),e)" p] that by simp
  have retained: "(schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R)"
    if member: "b\<in>system_definitions R" for b z
  proof -
    have inside: "b\<in>system_definitions T" using member installed(5) by simp
    show ?thesis using built(8)[rule_format, OF inside, of z] installed(8)[rule_format, OF member, of z] by blast
  qed
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ e], rule exI[of _ ?test])
    (use built(1-5) installed(3,5) invariant boundary test_call tested completion accepted retained in auto)
qed

theorem program_test_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes formed: "schema_system_formed P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e test. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<noteq>test \<and> {e,test}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert e (insert test (system_definitions R)) \<and>
    native_related_test_package C k F u [] e \<and> presented_program_invariant presents Q e \<and>
    (\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R))"
proof -
  obtain g :: "'d\<Rightarrow>local_address option definition_site" and E pu P' where compiled:
    "inj_on g (system_definitions P)" "closed_native_package_at E pu [] P'"
    "system_alpha_variant (rename_system g P) P'"
    "positive_meaning P'=map_prod g id ` positive_meaning P"
    using program_compilation_total[OF formed] by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at E pu [] P'" using compiled(2) by (simp add: closed_native_package_at_def)
  have source_member: "g d\<in>system_definitions P'"
    using source_entry compiled(3) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have source_meaning: "(g d,z)\<in>positive_meaning P' \<longleftrightarrow> (d,z)\<in>positive_meaning P" for z
    by (rule compiled_system_meaning_at[OF compiled(1) source_entry compiled(4)])

  show ?thesis using represented_native_test_completion[OF package source_member]
    by (simp only: source_meaning)
qed

theorem native_test_completion:
  assumes package: "native_package_at E pu pr P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e test. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<noteq>test \<and> {e,test}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert e (insert test (system_definitions R)) \<and>
    native_related_test_package C k F u [] e \<and> presented_program_invariant presents Q e \<and>
    (\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R))"
  by (rule program_test_completion[OF native_package_system_formed[OF package] source_entry])

theorem program_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes formed: "schema_system_formed P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<in>system_definitions Q \<and> native_related_test_package C k F u [] e \<and>
    presented_program_invariant presents Q e \<and>
    (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k)))"
proof -
  obtain F u Q e test where built: "closed_native_package_at F u [] Q" "native_package_environment F u []=F"
    "system_definitions Q=insert e (insert test (system_definitions R))"
    "native_related_test_package C k F u [] e" "presented_program_invariant presents Q e"
    "\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z"
    "(\<lambda>z. (e,z)\<in>positive_meaning Q)=saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
    "\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    using program_test_completion[OF formed source_entry] by (elim exE conjE) (rule that; assumption)
  have member: "e\<in>system_definitions Q" by (simp only: built(3); simp)
  have call: "\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z" using built(6) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ e])
    (use built(1,2,4,5,7,8) member call in blast)
qed

corollary invariant_program_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes "schema_system_formed P" "d\<in>system_definitions P" "presented_program_invariant presents P d"
  shows "\<exists>F u Q e. closed_native_package_at F u [] Q \<and> presented_program_invariant presents Q e \<and>
    (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>a z. presents a z \<longrightarrow>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k)))"
proof -
  obtain F u Q e where built: "closed_native_package_at F u [] Q" "presented_program_invariant presents Q e"
    "\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z"
    "(\<lambda>z. (e,z)\<in>positive_meaning Q)=saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
    "\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    using program_completion[OF assms(1,2)] by blast
  have invariant: "rel_fun (presentation_transport presents presents) (=)
      (\<lambda>z. (d,z)\<in>positive_meaning P) (\<lambda>z. (d,z)\<in>positive_meaning P)"
    using assms(3) by (simp only: presented_program_observations; blast)
  have agreement: "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      (\<lambda>z. admissible z \<and> (d,z)\<in>positive_meaning P)"
    using invariant by (simp only: presented_completion_truth_agreement[OF class_contract built(4)])
  have pointwise: "(e,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P"
    if "presents a z" for a z
  proof -
    have admitted: "admissible z"
      by (rule presentation_class.presentation_boundary[OF class_contract that])
    show ?thesis using fun_cong[OF agreement, of z] by (simp only: admitted; simp)
  qed
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ e])
    (use built(1-3,5) pointwise in blast)
qed

theorem fixed_checker_completion_coverage:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu T entry.
    closed_native_package_at B bu [] T \<and>
    (\<forall>P :: ('a,'s,'d,'n) schema_system. \<forall>d. schema_system_formed P \<longrightarrow> d\<in>system_definitions P \<longrightarrow>
      (\<exists>F u Q e. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
        e\<in>system_definitions Q \<and> presented_program_invariant presents Q e \<and>
        (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
        (\<lambda>z. (e,z)\<in>positive_meaning Q)=
          saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
        (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
          (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
            native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
            native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
            native_positive_holds G bu [] au [] \<and>
            (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
            (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))))"
proof -
  obtain B :: "local_address option artifact_environment" and bu T entry where checker:
    "closed_native_package_at B bu [] T"
    "\<forall>p. term_formed p \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> related_test_admission_result c (definition_site_value k) p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x))"
    using checker.native_checker by (elim exE conjE) (rule that; assumption)
  show ?thesis
  proof (rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ entry], rule conjI[OF checker(1)],
      intro allI impI)
    fix P :: "('a,'s,'d,'n) schema_system" and d
    assume formed: "schema_system_formed P" and member: "d\<in>system_definitions P"
    obtain F u Q e where built: "closed_native_package_at F u [] Q" "native_package_environment F u []=F"
      "e\<in>system_definitions Q" "presented_program_invariant presents Q e"
      "\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z"
      "(\<lambda>z. (e,z)\<in>positive_meaning Q)=saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
      "\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
        (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
      using program_completion[OF formed member] by blast
    have future: "\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        native_positive_holds G bu [] au [] \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)"
      if present: "program_entry_value_presents F u [] e p" for p
    proof -
      have pf: "term_formed p" using program_entry_value_presents_formed[OF present] by blast
      have accepted: "related_test_admission_result c (definition_site_value k) p"
        using built(7)[rule_format, OF present] by (simp only: checker.exact)
      show ?thesis using checker(2)[rule_format, OF pf] accepted by blast
    qed
    show "\<exists>F u Q e. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
        e\<in>system_definitions Q \<and> presented_program_invariant presents Q e \<and>
        (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
        (\<lambda>z. (e,z)\<in>positive_meaning Q)=
          saturate_observation presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
        (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
          (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
            native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
            native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
            native_positive_holds G bu [] au [] \<and>
            (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
            (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))"
      by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ e])
        (use built(1-6) future in blast)
  qed
qed

end

text \<open>
  Completion is uniform over the independently supplied presentation class.
  The direct native construction quotes the supplied actual environment in
  the established presentation coordinates and its entry into a new test, then
  adds a related-witness clause. The abstract constructor compiles its source
  once and consumes that construction. The generic native wrapper retains
  arbitrary source-use types through the abstract constructor.
  Every original test and every complete resulting policy presentation is
  covered by the fixed checker, including tests with no positive calls.

  The new test and permission have variable interfaces. Their original test
  truth, completed truth, and retained reference meanings have separate exact
  equations. Agreement with the original truth requires truth invariance.
  Formation agreement remains a separate condition, even for an invariant
  original program. Completion does not replace that recorded program.
\<close>

end
