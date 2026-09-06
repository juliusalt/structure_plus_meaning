theory Factor_Report_Families
  imports Factor_Report_Patterns Factor_Pattern_Families
begin

section \<open>An actual interface pattern supplies every report argument\<close>

definition report_interface_pattern ::
  "local_address option definition_site option \<Rightarrow> local_address option definition_site option \<Rightarrow>
    bool\<times>bool \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "report_interface_pattern l r b p = pattern_substitute (\<lambda>_. p) (report_pattern l r b)"

lemma report_interface_pattern_formed:
  assumes "report_definition_formed l" "report_definition_formed r" "pattern_formed p"
  shows "pattern_formed (report_interface_pattern l r b p)"
  unfolding report_interface_pattern_def
  by (rule pattern_substitute_formed[OF report_pattern_formed[OF assms(1,2)]])
    (simp add: assms(3))

lemma report_interface_pattern_variables:
  assumes "l\<noteq>None \<or> r\<noteq>None"
  shows "pattern_variables (report_interface_pattern l r b p)=pattern_variables p"
  by (simp add: report_interface_pattern_def pattern_substitute_variables report_pattern_variables[OF assms])

lemma report_interface_pattern_instance:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
    "single_valued V"
  shows "pattern_instance V (report_interface_pattern l r b p) z \<longleftrightarrow>
    (\<exists>t. pattern_instance V p t \<and> z=judgment_report_term (report_endpoints l r t) b)"
  using assms by (cases l; cases r)
    (auto simp: report_interface_pattern_def report_pattern_def report_endpoints_def judgment_report_term_def
      octets_formed_def dest: pattern_instance_unique[OF assms(4)])

theorem report_interface_pattern_accepts:
  assumes left: "report_definition_formed l" and right: "report_definition_formed r"
    and nonempty: "l\<noteq>None \<or> r\<noteq>None"
  shows "pattern_accepts (report_interface_pattern l r b p) z \<longleftrightarrow>
    (\<exists>t. pattern_accepts p t \<and> z=judgment_report_term (report_endpoints l r t) b)"
proof
  assume accepts: "pattern_accepts (report_interface_pattern l r b p) z"
  obtain V where bound: "term_bindings_formed (pattern_variables (report_interface_pattern l r b p)) V"
    and inst: "pattern_instance V (report_interface_pattern l r b p) z"
    using accepts unfolding pattern_accepts_def by blast
  have sv: "single_valued V" using bound by (simp add: term_bindings_formed_def)
  obtain t where arg: "pattern_instance V p t" and shape: "z=judgment_report_term (report_endpoints l r t) b"
    using inst by (simp only: report_interface_pattern_instance[OF left right nonempty sv]) blast
  have tf: "term_formed t" by (rule pattern_instance_formed_term[OF bound arg])
  have admitted: "pattern_accepts p t"
    using bound arg tf by (auto simp: pattern_accepts_def report_interface_pattern_variables[OF nonempty])
  show "\<exists>t. pattern_accepts p t \<and> z=judgment_report_term (report_endpoints l r t) b"
    using admitted shape by blast
next
  assume "\<exists>t. pattern_accepts p t \<and> z=judgment_report_term (report_endpoints l r t) b"
  then obtain t where accepts: "pattern_accepts p t" and shape: "z=judgment_report_term (report_endpoints l r t) b"
    by blast
  obtain V where bound: "term_bindings_formed (pattern_variables p) V"
    and arg: "pattern_instance V p t" and tf: "term_formed t"
    using accepts by (auto simp: pattern_accepts_def)
  have sv: "single_valued V" using bound by (simp add: term_bindings_formed_def)
  have inst: "pattern_instance V (report_interface_pattern l r b p) z"
    using arg shape by (auto simp: report_interface_pattern_instance[OF left right nonempty sv])
  have formed: "term_formed z" using shape tf report_endpoints_term_formed[OF left right nonempty] by simp
  show "pattern_accepts (report_interface_pattern l r b p) z"
    using bound inst formed by (auto simp: pattern_accepts_def report_interface_pattern_variables[OF nonempty])
qed

section \<open>One finite family has a complete possibly infinite report relation\<close>

definition report_family_system ::
  "'a \<Rightarrow> 'c set \<Rightarrow> ('c \<Rightarrow> local_address option definition_site option) \<Rightarrow>
    ('c \<Rightarrow> local_address option definition_site option) \<Rightarrow> ('c \<Rightarrow> bool\<times>bool) \<Rightarrow>
    ('c \<Rightarrow> 'a term_pattern) \<Rightarrow> ('a,unit,unit,'c) schema_system" where
  "report_family_system a D l r b p =
    pattern_family_system a ((\<lambda>c. (c,report_interface_pattern (l c) (r c) (b c) (p c))) ` D)"

lemma report_family_system_formed:
  assumes "finite D" "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    "\<forall>c\<in>D. pattern_formed (p c)"
  shows "schema_system_formed (report_family_system a D l r b p)"
  unfolding report_family_system_def
  by (rule pattern_family_formed)
    (use assms in \<open>auto simp: single_valued_def intro: report_interface_pattern_formed\<close>)

lemma report_family_system_definitions [simp]:
  "system_definitions (report_family_system a D l r b p)={()}"
  by (simp add: report_family_system_def)

lemma report_family_system_call:
  assumes "finite D" "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    "\<forall>c\<in>D. pattern_formed (p c)"
  shows "schema_call_formed (report_family_system a D l r b p) () t \<longleftrightarrow> term_formed t"
  unfolding report_family_system_def
  by (rule pattern_family_call)
    (use report_family_system_formed[OF assms] in \<open>simp only: report_family_system_def\<close>)

theorem report_family_system_meaning:
  assumes finite: "finite D"
    and sites: "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    and nonempty: "\<forall>c\<in>D. l c\<noteq>None \<or> r c\<noteq>None"
    and patterns: "\<forall>c\<in>D. pattern_formed (p c)"
  shows "((),z)\<in>positive_meaning (report_family_system a D l r b p) \<longleftrightarrow>
    (\<exists>c\<in>D. \<exists>t. pattern_accepts (p c) t \<and> z=judgment_report_term (report_endpoints (l c) (r c) t) (b c))"
proof -
  have formed: "schema_system_formed
    (pattern_family_system a ((\<lambda>c. (c,report_interface_pattern (l c) (r c) (b c) (p c))) ` D))"
    using report_family_system_formed[OF finite sites patterns] by (simp only: report_family_system_def)
  have each: "pattern_accepts (report_interface_pattern (l c) (r c) (b c) (p c)) x \<longleftrightarrow>
    (\<exists>t. pattern_accepts (p c) t \<and> x=judgment_report_term (report_endpoints (l c) (r c) t) (b c))"
    if "c\<in>D" for c x
    by (rule report_interface_pattern_accepts) (use sites nonempty that in auto)
  show ?thesis
  proof
    assume holds: "((),z)\<in>positive_meaning (report_family_system a D l r b p)"
    then show "\<exists>c\<in>D. \<exists>t. pattern_accepts (p c) t \<and>
      z=judgment_report_term (report_endpoints (l c) (r c) t) (b c)"
      by (auto simp: report_family_system_def pattern_family_meaning[OF formed] each)
  next
    assume "\<exists>c\<in>D. \<exists>t. pattern_accepts (p c) t \<and>
      z=judgment_report_term (report_endpoints (l c) (r c) t) (b c)"
    then obtain c t where member: "c\<in>D" and accepts: "pattern_accepts (p c) t"
      and shape: "z=judgment_report_term (report_endpoints (l c) (r c) t) (b c)" by blast
    let ?q="report_interface_pattern (l c) (r c) (b c) (p c)"
    have row: "(c,?q)\<in>(\<lambda>c. (c,report_interface_pattern (l c) (r c) (b c) (p c))) ` D"
      by (rule rev_image_eqI[OF member]) simp
    have admitted: "pattern_accepts ?q z" using accepts shape by (auto simp: each[OF member])
    show "((),z)\<in>positive_meaning (report_family_system a D l r b p)"
      by (simp only: report_family_system_def pattern_family_meaning[OF formed],
          rule exI[of _ c], rule exI[of _ ?q]) (use row admitted in blast)
  qed
qed

theorem report_family_system_reports:
  assumes "finite D" "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    "\<forall>c\<in>D. l c\<noteq>None \<or> r c\<noteq>None" "\<forall>c\<in>D. pattern_formed (p c)"
  shows "program_judgment_reports (report_family_system a D l r b p) () =
    (\<Union>c\<in>D. (\<lambda>t. (report_endpoints (l c) (r c) t,b c)) ` {t. pattern_accepts (p c) t})"
  by (auto simp: program_judgment_reports_def report_family_system_meaning[OF assms])

theorem report_family_system_only:
  assumes "finite D" "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    "\<forall>c\<in>D. l c\<noteq>None \<or> r c\<noteq>None" "\<forall>c\<in>D. pattern_formed (p c)"
  shows "program_reports_only (report_family_system a D l r b p) ()"
  by (auto simp: program_reports_only_def report_family_system_meaning[OF assms])

theorem report_family_native:
  fixes a :: 'a and p :: "'c \<Rightarrow> 'a term_pattern"
  assumes finite: "finite D"
    and sites: "\<forall>c\<in>D. report_definition_formed (l c)" "\<forall>c\<in>D. report_definition_formed (r c)"
    and nonempty: "\<forall>c\<in>D. l c\<noteq>None \<or> r c\<noteq>None"
    and patterns: "\<forall>c\<in>D. pattern_formed (p c)"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> program_reports_only Q e \<and>
    program_judgment_reports Q e=
      (\<Union>c\<in>D. (\<lambda>t. (report_endpoints (l c) (r c) t,b c)) ` {t. pattern_accepts (p c) t}) \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>c\<in>D. \<exists>x. pattern_accepts (p c) x \<and>
          t=judgment_report_term (report_endpoints (l c) (r c) x) (b c)))))"
proof -
  let ?P="report_family_system a D l r b p"
  have formed: "schema_system_formed ?P" by (rule report_family_system_formed[OF finite sites patterns])
  have entry: "()\<in>system_definitions ?P" by simp
  have only: "program_reports_only ?P ()" by (rule report_family_system_only[OF finite sites nonempty patterns])
  obtain E :: "local_address option artifact_environment" and pu Q e where compiled:
    "closed_native_package_at E pu [] Q" "native_package_environment E pu []=E"
    "e\<in>system_definitions Q" "program_judgment_reports Q e=program_judgment_reports ?P ()"
    "program_reports_only Q e\<longleftrightarrow>program_reports_only ?P ()"
    "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      (native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed ?P () t) \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>((),t)\<in>positive_meaning ?P))"
    using program_judgment_reports_native[OF formed entry] by metis
  have reports: "program_judgment_reports Q e=
      (\<Union>c\<in>D. (\<lambda>t. (report_endpoints (l c) (r c) t,b c)) ` {t. pattern_accepts (p c) t})"
    using compiled(4) report_family_system_reports[OF finite sites nonempty patterns] by simp
  have outputs: "program_reports_only Q e" using compiled(5) only by blast
  have future: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>c\<in>D. \<exists>x. pattern_accepts (p c) x \<and>
          t=judgment_report_term (report_endpoints (l c) (r c) x) (b c))))"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    obtain F au I K where app:
      "environment_formed F" "environment_included E F" "native_package_at F pu [] Q"
      "native_package_environment F pu []=E" "native_application_at F au [] e t I K"
      "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed ?P () t"
      "native_positive_holds F pu [] au []\<longleftrightarrow>((),t)\<in>positive_meaning ?P"
      using compiled(6)[rule_format, OF tf] by blast
    have call: "native_application_formed F pu [] au []"
      using app(6) tf by (simp add: report_family_system_call[OF finite sites patterns])
    have meaning: "native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>c\<in>D. \<exists>x. pattern_accepts (p c) x \<and>
          t=judgment_report_term (report_endpoints (l c) (r c) x) (b c))"
      using app(7) by (simp add: report_family_system_meaning[OF finite sites nonempty patterns])
    show "\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>c\<in>D. \<exists>x. pattern_accepts (p c) x \<and>
          t=judgment_report_term (report_endpoints (l c) (r c) x) (b c)))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use app(1-5) call meaning in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ e])
    (use compiled(1-3) reports outputs future in blast)
qed

text \<open>
  Substitution reuses the existing report shape. Every present endpoint
  contains the same whole instance of the supplied interface pattern. Shared
  variables, nested pairs, exact payloads, and literal targets retain their
  ordinary meanings. No list of ground arguments is substituted for an
  interface.

  The program stores one finite identified clause family. Its parameters only
  supply the endpoint data, declarations, and patterns at those finite
  coordinates; their values elsewhere are irrelevant. Compilation fixes one
  closed program before any future query, with a complete output equation
  excluding every unrelated shape. Overlapping clauses need not give
  functional declarations; the separate coverage profile must establish that
  condition. Neither report generation nor its raw flags prove soundness.
\<close>

end
