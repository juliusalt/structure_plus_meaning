theory Factor_Report_Patterns
  imports Factor_Report_Programs Factor_Pattern_Programs
begin

section \<open>One ordinary pattern covers every formed argument at supplied sites\<close>

fun report_definition_formed :: "local_address option definition_site option \<Rightarrow> bool" where
  "report_definition_formed None=True"
| "report_definition_formed (Some d)=octets_formed (snd d)"

definition report_endpoints ::
  "local_address option definition_site option \<Rightarrow> local_address option definition_site option \<Rightarrow>
    factor_term \<Rightarrow> native_report_call option\<times>native_report_call option" where
  "report_endpoints l r t=(map_option (\<lambda>d. (d,t)) l,map_option (\<lambda>d. (d,t)) r)"

fun report_endpoint_pattern :: "local_address option definition_site option \<Rightarrow> unit term_pattern" where
  "report_endpoint_pattern None=Pattern_Payload []"
| "report_endpoint_pattern (Some d)=
    Pattern_Pair (exact_term_pattern (site_data_term (fst d) (snd d))) (Pattern_Variable ())"

definition report_pattern ::
  "local_address option definition_site option \<Rightarrow> local_address option definition_site option \<Rightarrow>
    bool\<times>bool \<Rightarrow> unit term_pattern" where
  "report_pattern l r b=
    Pattern_Pair (Pattern_Pair (report_endpoint_pattern l) (report_endpoint_pattern r))
      (exact_term_pattern (Pair_Term (report_boolean_term (fst b)) (report_boolean_term (snd b))))"

lemma report_pattern_formed:
  assumes "report_definition_formed l" "report_definition_formed r"
  shows "pattern_formed (report_pattern l r b)"
  using assms by (cases l; cases r) (auto simp: report_pattern_def octets_formed_def)

lemma report_pattern_variables:
  assumes "l\<noteq>None \<or> r\<noteq>None"
  shows "pattern_variables (report_pattern l r b)={()}"
  using assms by (cases l; cases r) (auto simp: report_pattern_def)

lemma report_endpoints_term_formed:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
  shows "term_formed (judgment_report_term (report_endpoints l r t) b) \<longleftrightarrow> term_formed t"
  using assms by (cases l; cases r) (auto simp: report_endpoints_def)

lemma report_pattern_instance:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
    "single_valued V"
  shows "pattern_instance V (report_pattern l r b) z \<longleftrightarrow>
    (\<exists>t. ((),t)\<in>V \<and> z=judgment_report_term (report_endpoints l r t) b)"
  using assms by (cases l; cases r)
    (auto simp: report_pattern_def report_endpoints_def judgment_report_term_def
      octets_formed_def single_valued_def)

theorem report_pattern_accepts:
  assumes left: "report_definition_formed l" and right: "report_definition_formed r"
    and nonempty: "l\<noteq>None \<or> r\<noteq>None"
  shows "pattern_accepts (report_pattern l r b) z \<longleftrightarrow>
    (\<exists>t. term_formed t \<and> z=judgment_report_term (report_endpoints l r t) b)"
proof
  assume accepts: "pattern_accepts (report_pattern l r b) z"
  obtain V where bindings: "term_bindings_formed (pattern_variables (report_pattern l r b)) V"
    and inst: "pattern_instance V (report_pattern l r b) z"
    using accepts unfolding pattern_accepts_def by blast
  have sv: "single_valued V" using bindings by (simp add: term_bindings_formed_def)
  obtain t where bound: "((),t)\<in>V" and code: "z=judgment_report_term (report_endpoints l r t) b"
    using inst by (auto simp: report_pattern_instance[OF left right nonempty sv])
  have tf: "term_formed t" using bindings bound by (auto simp: term_bindings_formed_def)
  show "\<exists>t. term_formed t \<and> z=judgment_report_term (report_endpoints l r t) b" using code tf by blast
next
  assume "\<exists>t. term_formed t \<and> z=judgment_report_term (report_endpoints l r t) b"
  then obtain t where tf: "term_formed t" and code: "z=judgment_report_term (report_endpoints l r t) b" by blast
  have bindings: "term_bindings_formed (pattern_variables (report_pattern l r b)) {((),t)}"
    using tf by (auto simp: report_pattern_variables[OF nonempty] term_bindings_formed_def
      single_valued_def rel_dom_def)
  have sv: "single_valued {((),t)}" by (simp add: single_valued_def)
  have inst: "pattern_instance {((),t)} (report_pattern l r b) z"
    using code by (auto simp: report_pattern_instance[OF left right nonempty sv])
  have formed: "term_formed z" using code tf report_endpoints_term_formed[OF left right nonempty] by simp
  show "pattern_accepts (report_pattern l r b) z"
    using bindings inst formed unfolding pattern_accepts_def by blast
qed

definition report_pattern_system ::
  "local_address option definition_site option \<Rightarrow> local_address option definition_site option \<Rightarrow>
    bool\<times>bool \<Rightarrow> (unit,unit,unit,unit) schema_system" where
  "report_pattern_system l r b=recognizer_system () (report_pattern l r b)"

lemma report_pattern_system_formed:
  assumes "report_definition_formed l" "report_definition_formed r"
  shows "schema_system_formed (report_pattern_system l r b)"
  unfolding report_pattern_system_def by (rule recognizer_system_formed[OF report_pattern_formed[OF assms]])

lemma report_pattern_system_definitions [simp]:
  "system_definitions (report_pattern_system l r b)={()}"
  by (auto simp: report_pattern_system_def recognizer_system_def system_definitions_def rel_dom_def)

lemma report_pattern_system_call:
  assumes "report_definition_formed l" "report_definition_formed r"
  shows "schema_call_formed (report_pattern_system l r b) () t \<longleftrightarrow> term_formed t"
  unfolding report_pattern_system_def by (rule recognizer_call_formed[OF report_pattern_formed[OF assms]])

theorem report_pattern_system_meaning:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
  shows "((),z)\<in>positive_meaning (report_pattern_system l r b) \<longleftrightarrow>
    (\<exists>t. term_formed t \<and> z=judgment_report_term (report_endpoints l r t) b)"
  unfolding report_pattern_system_def
  by (simp only: recognizer_positive_meaning[OF report_pattern_formed[OF assms(1,2)]]
    report_pattern_accepts[OF assms])

theorem report_pattern_system_reports:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
  shows "program_judgment_reports (report_pattern_system l r b) () =
    (\<lambda>t. (report_endpoints l r t,b)) ` {t. term_formed t}"
  by (auto simp: program_judgment_reports_def report_pattern_system_meaning[OF assms])

theorem report_pattern_system_only:
  assumes "report_definition_formed l" "report_definition_formed r" "l\<noteq>None \<or> r\<noteq>None"
  shows "program_reports_only (report_pattern_system l r b) ()"
  by (auto simp: program_reports_only_def report_pattern_system_meaning[OF assms])

theorem report_pattern_native:
  assumes sites: "report_definition_formed l" "report_definition_formed r"
    and nonempty: "l\<noteq>None \<or> r\<noteq>None"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> program_reports_only Q e \<and>
    program_judgment_reports Q e=(\<lambda>t. (report_endpoints l r t,b)) ` {t. term_formed t} \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>
        (\<exists>x. term_formed x \<and> t=judgment_report_term (report_endpoints l r x) b))))"
proof -
  let ?P="report_pattern_system l r b"
  have formed: "schema_system_formed ?P" by (rule report_pattern_system_formed[OF sites])
  have entry: "()\<in>system_definitions ?P" by simp
  have only: "program_reports_only ?P ()" by (rule report_pattern_system_only[OF sites nonempty])
  obtain E :: "local_address option artifact_environment" and pu Q e where compiled:
    "closed_native_package_at E pu [] Q" "native_package_environment E pu []=E"
    "e\<in>system_definitions Q" "program_judgment_reports Q e=program_judgment_reports ?P ()"
    "program_reports_only Q e\<longleftrightarrow>program_reports_only ?P ()"
    "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      (native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed ?P () t) \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>((),t)\<in>positive_meaning ?P))"
    using program_judgment_reports_native[OF formed entry]
    by metis
  have reports: "program_judgment_reports Q e=(\<lambda>t. (report_endpoints l r t,b)) ` {t. term_formed t}"
    using compiled(4) report_pattern_system_reports[OF sites nonempty, where b=b] by simp
  have outputs: "program_reports_only Q e" using compiled(5) only by blast
  have future: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>
        (\<exists>x. term_formed x \<and> t=judgment_report_term (report_endpoints l r x) b)))"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    obtain F au I K where app:
      "environment_formed F" "environment_included E F" "native_package_at F pu [] Q"
      "native_package_environment F pu []=E" "native_application_at F au [] e t I K"
      "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed ?P () t"
      "native_positive_holds F pu [] au []\<longleftrightarrow>((),t)\<in>positive_meaning ?P"
      using compiled(6)[rule_format, OF tf] by blast
    have call: "native_application_formed F pu [] au []"
      using app(6) tf by (simp add: report_pattern_system_call[OF sites])
    have meaning: "native_positive_holds F pu [] au []\<longleftrightarrow>
        (\<exists>x. term_formed x \<and> t=judgment_report_term (report_endpoints l r x) b)"
      using app(7) by (simp add: report_pattern_system_meaning[OF sites nonempty])
    show "\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>
        (\<exists>x. term_formed x \<and> t=judgment_report_term (report_endpoints l r x) b))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use app(1-5) call meaning in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ e])
    (use compiled(1-3) reports outputs future in blast)
qed

text \<open>
  The same variable appears at every present endpoint. Thus one ordinary
  premise-free clause describes every formed argument, with exact supplied
  definition coordinates and declaration fields. Either endpoint may be
  explicitly absent; both cannot be absent. No finite argument sample is used.

  The native theorem fixes one closed program before any future report or
  malformed candidate output is supplied. It proves the whole positive
  relation, including the no-extra condition, from the ordinary pattern rules.
  Declaration flags do not assert their own soundness or authorize amendment.
\<close>

end
