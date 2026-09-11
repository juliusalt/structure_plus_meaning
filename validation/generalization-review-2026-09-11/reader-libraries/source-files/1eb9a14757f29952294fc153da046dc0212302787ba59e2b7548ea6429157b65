theory Factor_Application_Reading
  imports Factor_Prospective_Instantiation
begin

section \<open>The existing two-field application through empty-scope instantiation\<close>

abbreviation application_reading_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "application_reading_argument e u r d t i k \<equiv> term_quotation_argument e u r (Pair_Term d t) i k"

abbreviation application_reading_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "application_reading_pattern e u r d t i k \<equiv> term_quotation_pattern e u r (Pattern_Pair d t) i k"

abbreviation application_reading_result :: "factor_term \<Rightarrow> bool" where
  "application_reading_result z \<equiv> \<exists>E e u r du da t Is Ks.
    z=application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
    environment_value_presents E e \<and> distinct Is \<and> distinct Ks \<and>
    native_application_at E u r (du,da) t (set Is) (set Ks)"

lemma application_reading_result_at_source:
  assumes source: "environment_value_presents E e"
  shows "application_reading_result (application_reading_argument e u r d t i k) \<longleftrightarrow>
    (\<exists>v a du da Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> d=site_data_term du da \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> native_application_at E v a (du,da) t (set Is) (set Ks))"
proof
  assume admitted: "application_reading_result (application_reading_argument e u r d t i k)"
  obtain F v a du da Is Ks where parts: "environment_value_presents F e"
    "u=use_data_term v" "r=Payload_Term a" "d=site_data_term du da"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks" "native_application_at F v a (du,da) t (set Is) (set Ks)"
    using admitted by (simp only: factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>v a du da Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> d=site_data_term du da \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> native_application_at E v a (du,da) t (set Is) (set Ks)"
    by (rule exI[of _ v], rule exI[of _ a], rule exI[of _ du], rule exI[of _ da],
      rule exI[of _ Is], rule exI[of _ Ks]) (use parts same in auto)
next
  assume "\<exists>v a du da Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> d=site_data_term du da \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> native_application_at E v a (du,da) t (set Is) (set Ks)"
  then obtain v a du da Is Ks where parts:
    "u=use_data_term v" "r=Payload_Term a" "d=site_data_term du da"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks" "native_application_at E v a (du,da) t (set Is) (set Ks)" by blast
  show "application_reading_result (application_reading_argument e u r d t i k)"
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ v], rule exI[of _ a],
      rule exI[of _ du], rule exI[of _ da], rule exI[of _ t], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts source in auto)
qed

definition application_reading_schema :: "(nat,nat,nat) factor_schema" where
  "application_reading_schema=data_rule
    (application_reading_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,57,prospective_instantiation_pattern data_x data_y (Pattern_Payload []) (Pattern_Payload []) data_z data_w
      (Pattern_Variable 4) (Pattern_Payload []) (Pattern_Variable 5) (Pattern_Variable 6))}"

definition application_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "application_reading_system=add_view_definition prospective_instantiation_system 58 data_x {(0,application_reading_schema)}"

interpretation application_reading_view: positive_view prospective_instantiation_system 58 data_x "{(0,application_reading_schema)}"
  by (rule positive_view.intro)
    (auto simp: application_reading_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma application_reading_system_formed [simp]: "schema_system_formed application_reading_system"
  using application_reading_view.formed by (simp only: application_reading_system_def)

lemma application_reading_definitions [simp]:
  "system_definitions application_reading_system=insert 58 (system_definitions prospective_instantiation_system)"
  by (simp add: application_reading_system_def)

lemma application_reading_call:
  "schema_call_formed application_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions application_reading_system \<and> term_formed t"
  using added_variable_calls[OF prospective_instantiation_system_formed
    application_reading_system_formed[unfolded application_reading_system_def] prospective_instantiation_call]
  by (simp only: application_reading_system_def[symmetric])

lemma application_reading_old_meaning:
  assumes "d\<in>system_definitions prospective_instantiation_system"
  shows "(d,t)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning prospective_instantiation_system"
  using added_definition_preserves_old(2)[OF prospective_instantiation_system_formed
    application_reading_system_formed[unfolded application_reading_system_def], of d t] assms
  by (auto simp: application_reading_system_def)

lemma application_reading_clause [simp]:
  "((58,c),S)\<in>system_clauses application_reading_system \<longleftrightarrow> (c,S)\<in>{(0,application_reading_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses prospective_instantiation_system \<Longrightarrow>
    d\<in>system_definitions prospective_instantiation_system" for d c S
    using prospective_instantiation_system_formed unfolding schema_system_formed_def by blast
  have absent: "((58,c),S)\<notin>system_clauses prospective_instantiation_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: application_reading_system_def)
qed

lemma application_reading_previous_entry:
  "(57,t)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (57,t)\<in>positive_meaning prospective_instantiation_system"
  by (rule application_reading_old_meaning) simp

lemma application_reading_step:
  assumes child: "(57,prospective_instantiation_argument e u (Payload_Term []) (Payload_Term []) r d t
      (Payload_Term []) i k)\<in>positive_meaning prospective_instantiation_system"
  shows "(58,application_reading_argument e u r d t i k)\<in>positive_meaning application_reading_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed d" "term_formed t" "term_formed i" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF child]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then d
    else if n=4 then t else if n=5 then i else k"
  have result: "(58,evaluate_pattern ?h (schema_conclusion application_reading_schema))\<in>positive_meaning application_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed child in \<open>auto simp: application_reading_schema_def schema_variables_def
        application_reading_call application_reading_previous_entry\<close>)
  show ?thesis using result by (simp add: application_reading_schema_def)
qed

lemma application_reading_valuation:
  "(58,z)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6}. term_formed (h i)) \<and>
      z=application_reading_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (57,prospective_instantiation_argument (h 0) (h 1) (Payload_Term []) (Payload_Term []) (h 2) (h 3) (h 4)
        (Payload_Term []) (h 5) (h 6))\<in>positive_meaning prospective_instantiation_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: application_reading_schema_def schema_variables_def application_reading_call application_reading_previous_entry)

lemma application_reading_fields:
  "(58,z)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (\<exists>e u r d t i k. z=application_reading_argument e u r d t i k \<and>
      (57,prospective_instantiation_argument e u (Payload_Term []) (Payload_Term []) r d t (Payload_Term []) i k)
        \<in>positive_meaning prospective_instantiation_system)"
proof
  assume "(58,z)\<in>positive_meaning application_reading_system"
  then show "\<exists>e u r d t i k. z=application_reading_argument e u r d t i k \<and>
      (57,prospective_instantiation_argument e u (Payload_Term []) (Payload_Term []) r d t (Payload_Term []) i k)
        \<in>positive_meaning prospective_instantiation_system"
    by (auto simp: application_reading_valuation)
next
  assume "\<exists>e u r d t i k. z=application_reading_argument e u r d t i k \<and>
      (57,prospective_instantiation_argument e u (Payload_Term []) (Payload_Term []) r d t (Payload_Term []) i k)
        \<in>positive_meaning prospective_instantiation_system"
  then show "(58,z)\<in>positive_meaning application_reading_system" using application_reading_step by blast
qed

theorem application_reading_sound:
  assumes holds: "(58,z)\<in>positive_meaning application_reading_system"
  shows "application_reading_result z"
proof -
  obtain e u r d t i k where shape: "z=application_reading_argument e u r d t i k"
    and child: "(57,prospective_instantiation_argument e u (Payload_Term []) (Payload_Term []) r d t (Payload_Term []) i k)
      \<in>positive_meaning prospective_instantiation_system"
    using holds by (simp only: application_reading_fields) blast
  have empty_list: "Payload_Term []=data_list_term (map Payload_Term vs) \<longleftrightarrow> vs=[]" for vs
    by (cases vs) auto
  have empty_bindings: "term_bindings_formed {} B \<Longrightarrow> B={}" for B
    by (auto simp: term_bindings_formed_def rel_dom_def)
  obtain E v a du da p Is Ks where parts: "environment_value_presents E e"
    "u=use_data_term v" "r=Payload_Term a" "d=site_data_term du da"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)" "distinct Is" "distinct Ks"
    "prospective_call_at E v {} a (du,da) p (set Is) (set Ks)" "pattern_instance {} p t"
    using child by (simp only: prospective_instantiation_exact factor_term.inject)
      (auto simp: empty_list dest!: empty_bindings)
  have app: "native_application_at E v a (du,da) t (set Is) (set Ks)"
    using parts(9,10) by (simp only: native_application_empty_scope[where B="{}"]) blast
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ v], rule exI[of _ a],
      rule exI[of _ du], rule exI[of _ da], rule exI[of _ t], rule exI[of _ Is], rule exI[of _ Ks])
      (use shape parts app in auto)
qed

theorem application_reading_complete:
  assumes source: "environment_value_presents E e" and order: "distinct Is" "distinct Ks"
    and app: "native_application_at E u r (du,da) t (set Is) (set Ks)"
  shows "(58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning application_reading_system"
proof -
  obtain p where parts: "prospective_call_at E u {} r (du,da) p (set Is) (set Ks)" "pattern_instance {} p t"
    using app by (simp only: native_application_empty_scope[where B="{}"]) blast
  have unused: "pattern_variables p={}" using prospective_call_formed[OF parts(1)] by auto
  have child: "(57,prospective_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term []))
      (binding_rows_term []) (Payload_Term r) (site_data_term du da) t (data_list_term (map Payload_Term []))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning prospective_instantiation_system"
    by (simp only: prospective_instantiation_on_values[OF source])
      (use parts unused order in \<open>auto simp: term_bindings_formed_def rel_dom_def single_valued_def\<close>)
  show ?thesis using application_reading_step[OF child[simplified]] .
qed

theorem application_reading_exact:
  "(58,z)\<in>positive_meaning application_reading_system \<longleftrightarrow> application_reading_result z"
  using application_reading_sound application_reading_complete by blast

corollary application_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(58,application_reading_argument e u r d t i k)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (\<exists>v a du da Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> d=site_data_term du da \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Is \<and> distinct Ks \<and> native_application_at E v a (du,da) t (set Is) (set Ks))"
  by (simp only: application_reading_exact application_reading_result_at_source[OF source])

corollary application_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning application_reading_system
      \<longleftrightarrow> distinct Is \<and> distinct Ks \<and> native_application_at E u r (du,da) t (set Is) (set Ks)"
  by (subst application_reading_at_source[OF source])
    (auto simp: inj_eq[OF use_data_term_injective] data_list_term_injective injective_mapped_lists[OF payload_term_inj])

corollary application_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(58,application_reading_argument e u r d t i k)\<in>positive_meaning application_reading_system \<longleftrightarrow>
    (58,application_reading_argument f u r d t i k)\<in>positive_meaning application_reading_system"
  by (simp only: application_reading_at_source[OF assms(1)] application_reading_at_source[OF assms(2)])

corollary application_reading_orders:
  assumes source: "environment_value_presents E e" and same: "mset Is=mset Js" "mset Ks=mset Ls"
  shows "(58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning application_reading_system
      \<longleftrightarrow>
    (58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))\<in>positive_meaning application_reading_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)]
  by (simp only: application_reading_on_values[OF source])

corollary application_reading_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term du da) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning application_reading_system"
    and second: "(58,application_reading_argument e (use_data_term u) (Payload_Term r) (site_data_term eu ea) s
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))\<in>positive_meaning application_reading_system"
  shows "du=eu \<and> da=ea \<and> t=s \<and> mset Is=mset Js \<and> mset Ks=mset Ls"
proof -
  have left: "distinct Is \<and> distinct Ks \<and> native_application_at E u r (du,da) t (set Is) (set Ks)"
    using first by (simp only: application_reading_on_values[OF source])
  have right: "distinct Js \<and> distinct Ls \<and> native_application_at E u r (eu,ea) s (set Js) (set Ls)"
    using second by (simp only: application_reading_on_values[OF source])
  have first_app: "native_application_at E u r (du,da) t (set Is) (set Ks)" using left by blast
  have second_app: "native_application_at E u r (eu,ea) s (set Js) (set Ls)" using right by blast
  have same: "du=eu \<and> da=ea \<and> t=s \<and> set Is=set Js \<and> set Ks=set Ls"
    using native_application_unique[OF first_app second_app] by auto
  show ?thesis using left right same distinct_source_mset[of Is Js] distinct_source_mset[of Ks Ls] by auto
qed

section \<open>One closed native program precedes every future operand\<close>

abbreviation call_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "call_operation_result d t \<equiv>
    (d=57 \<and> prospective_instantiation_result t) \<or> (d=58 \<and> application_reading_result t)"

lemma call_operations_exact:
  assumes "d\<in>{57,58}"
  shows "(d,t)\<in>positive_meaning application_reading_system \<longleftrightarrow> call_operation_result d t"
proof (cases "d=57")
  case True
  then show ?thesis by (simp add: application_reading_previous_entry prospective_instantiation_exact)
next
  case False
  then have "d=58" using assms by auto
  then show ?thesis by (simp add: application_reading_exact)
qed

theorem native_call_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {57::nat,58} \<and>
    (\<forall>d\<in>{57,58}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> call_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions application_reading_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions application_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed application_reading_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning application_reading_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF application_reading_system_formed] by blast
  have sites: "inj_on g {57,58}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {57,58}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{57,58}" and tf: "term_formed t"
    have member: "d\<in>system_definitions application_reading_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed application_reading_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning application_reading_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> call_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member call_operations_exact[OF selected] in \<open>auto simp: application_reading_call\<close>)
  qed
qed

text \<open>
  Empty-scope prospective instantiation recovers the existing two-field
  application without adding a binder root. The equivalence is proved for
  every binding relation: an empty scope forces the quoted pattern to be
  ground, so its instance does not depend on those bindings.

  The ordinary application entry fixes the scope, table, and used-variable
  collection to their empty presentations. It checks exactly the raw
  application reading, retaining the actual resolved use and address, term,
  interior, and external slots. Callee definition formation, package membership,
  interface acceptance, and positive truth remain separate judgments.

  Both entries have exact all-term contracts and preserve every earlier
  meaning. One fixed closed native program contains two distinct sites before
  all future formed operands, retaining the same canonical environment.
\<close>

end
