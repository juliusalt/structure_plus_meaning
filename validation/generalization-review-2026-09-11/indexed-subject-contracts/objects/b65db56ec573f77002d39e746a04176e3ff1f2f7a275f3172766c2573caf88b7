theory Factor_Report_Programs
  imports Factor_Comparison_Reports Factor_Coordinate_Values Factor_Compiled_Applications
begin

section \<open>Ordinary data for both endpoints and both declarations\<close>

type_synonym native_report_call = "local_address option definition_site\<times>factor_term"
type_synonym native_judgment_reports = "(native_report_call,native_report_call) correspondence_reports"

fun report_boolean_term :: "bool \<Rightarrow> factor_term" where
  "report_boolean_term False=Payload_Term []"
| "report_boolean_term True=Pair_Term (Payload_Term []) (Payload_Term [])"

lemma report_boolean_term_eq [simp]:
  "report_boolean_term b=report_boolean_term c \<longleftrightarrow> b=c"
  by (cases b; cases c) auto

lemma report_boolean_term_formed [simp]: "term_formed (report_boolean_term b)"
  by (cases b) (simp_all add: octets_formed_def)

fun report_call_term :: "native_report_call option \<Rightarrow> factor_term" where
  "report_call_term None=Payload_Term []"
| "report_call_term (Some x)=Pair_Term (site_data_term (fst (fst x)) (snd (fst x))) (snd x)"

fun report_call_formed :: "native_report_call option \<Rightarrow> bool" where
  "report_call_formed None=True"
| "report_call_formed (Some x)=(octets_formed (snd (fst x)) \<and> term_formed (snd x))"

lemma report_call_term_eq [simp]:
  "report_call_term x=report_call_term y \<longleftrightarrow> x=y"
  by (cases x; cases y) (auto simp: prod_eq_iff)

lemma report_call_term_formed [simp]:
  "term_formed (report_call_term x) \<longleftrightarrow> report_call_formed x"
  by (cases x) (auto simp: octets_formed_def)

definition judgment_report_term ::
  "(native_report_call option\<times>native_report_call option) \<Rightarrow> (bool\<times>bool) \<Rightarrow> factor_term" where
  "judgment_report_term q b =
    Pair_Term (Pair_Term (report_call_term (fst q)) (report_call_term (snd q)))
      (Pair_Term (report_boolean_term (fst b)) (report_boolean_term (snd b)))"

lemma judgment_report_term_eq [simp]:
  "judgment_report_term q b=judgment_report_term r c \<longleftrightarrow> q=r \<and> b=c"
  by (simp add: judgment_report_term_def prod_eq_iff)

lemma judgment_report_term_formed [simp]:
  "term_formed (judgment_report_term q b) \<longleftrightarrow>
    report_call_formed (fst q) \<and> report_call_formed (snd q)"
  by (simp add: judgment_report_term_def)

section \<open>A finite ordinary program may describe an infinite report relation\<close>

definition program_judgment_reports ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> native_judgment_reports" where
  "program_judgment_reports P d={(q,b). (d,judgment_report_term q b)\<in>positive_meaning P}"

definition program_reports_only :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "program_reports_only P d \<longleftrightarrow>
    (\<forall>t. (d,t)\<in>positive_meaning P \<longrightarrow> (\<exists>q b. t=judgment_report_term q b))"

lemma program_judgment_report_member [simp]:
  "(q,b)\<in>program_judgment_reports P d \<longleftrightarrow> (d,judgment_report_term q b)\<in>positive_meaning P"
  by (simp add: program_judgment_reports_def)

theorem program_judgment_reports_no_extra:
  assumes only: "program_reports_only P d"
  shows "{t. (d,t)\<in>positive_meaning P} =
    (\<lambda>(q,b). judgment_report_term q b) ` program_judgment_reports P d"
  using only by (auto simp: program_reports_only_def program_judgment_reports_def)

lemma program_judgment_report_formed:
  assumes "(q,b)\<in>program_judgment_reports P d"
  shows "report_call_formed (fst q) \<and> report_call_formed (snd q)"
proof -
  have positive: "(d,judgment_report_term q b)\<in>positive_meaning P" using assms by simp
  have "term_formed (judgment_report_term q b)"
    using schema_call_formed_target[OF positive_meaning_formed[OF positive]] by blast
  then show ?thesis by simp
qed

theorem program_judgment_reports_transport:
  assumes meaning: "\<And>t. (e,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  shows "program_judgment_reports Q e=program_judgment_reports P d"
    and "program_reports_only Q e \<longleftrightarrow> program_reports_only P d"
  by (simp_all add: program_judgment_reports_def program_reports_only_def meaning)

theorem program_judgment_reports_native:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes formed: "schema_system_formed P" and entry: "d\<in>system_definitions P"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> program_judgment_reports Q e=program_judgment_reports P d \<and>
    (program_reports_only Q e\<longleftrightarrow>program_reports_only P d) \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
      (native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed P d t) \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>(d,t)\<in>positive_meaning P)))"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site" and E pu Q where compiled:
    "inj_on g (system_definitions P)" "closed_native_package_at E pu [] Q"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g P) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning P"
    using program_compilation_total[OF formed] by metis
  have member: "g d\<in>system_definitions Q"
    using compiled(4) entry by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have meaning: "\<And>t. (g d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    by (rule compiled_system_meaning_at[OF compiled(1) entry compiled(5)])
  have boundary: "\<And>t. schema_call_formed Q (g d) t \<longleftrightarrow> schema_call_formed P d t"
    by (rule compiled_system_call_boundary[OF formed compiled(1,4) entry])
  have reports: "program_judgment_reports Q (g d)=program_judgment_reports P d"
    and only: "program_reports_only Q (g d)\<longleftrightarrow>program_reports_only P d"
    by (rule program_judgment_reports_transport[OF meaning])+
  have package: "native_package_at E pu [] Q" using compiled(2) by (simp add: closed_native_package_at_def)
  have future: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] (g d) t I K \<and>
      (native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed P d t) \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>(d,t)\<in>positive_meaning P))"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    show "\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] Q \<and>
      native_package_environment F pu []=E \<and> native_application_at F au [] (g d) t I K \<and>
      (native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed P d t) \<and>
      (native_positive_holds F pu [] au []\<longleftrightarrow>(d,t)\<in>positive_meaning P)"
      using native_application_extension_total[OF package member tf]
      by (auto simp only: compiled(3) boundary meaning)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g d"])
    (use compiled(2,3) member reports only future in blast)
qed

text \<open>
  These report constructors use the existing payload-and-pair term syntax.
  Coordinates retain their uses and addresses, relative to the two explicitly
  supplied comparison scopes. Literal argument targets remain exact operands;
  ordinary native application construction supplies any references they need.

  The report relation is derived from one entry of a finite ordinary program,
  rather than stored as an infinite table. The separate no-extra condition
  accounts for every positive output at that entry, including malformed output
  shapes. Compilation preserves that exact relation for every future argument.

  A reporting program describes submitted claims. Its clauses are not thereby
  rules of the predecessor's acceptance program. Checking coverage, preservation,
  and permission inside that predecessor remains a separate obligation.
\<close>

end
