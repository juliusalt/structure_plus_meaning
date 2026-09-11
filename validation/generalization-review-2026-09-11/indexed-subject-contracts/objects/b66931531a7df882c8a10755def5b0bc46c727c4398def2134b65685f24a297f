theory Factor_Related_Test_Admission
  imports Factor_Related_Test_Profiles Factor_Related_Test_References
    Factor_Environment_Inclusion_Contracts Factor_Component_Agreement
begin

section \<open>Whole reader components agree on the complete shared definitions\<close>

lemma related_test_environment_base_agreement:
  "systems_agree_on definition_call_admission_system environment_inclusion_system
    (system_definitions definition_call_admission_system)"
  by (rule environment_inclusion_definition_agreement)

lemma related_test_environment_package_agreement:
  "systems_agree_on package_membership_system environment_inclusion_system
    (system_definitions package_membership_system)"
  by (rule environment_inclusion_package_agreement)

lemma related_test_components_agreement:
  "systems_agree_on single_clause_reading_system environment_inclusion_system
    (system_definitions single_clause_reading_system\<inter>system_definitions environment_inclusion_system)"
proof (rule common_component_overlap_agreement[where B=definition_call_admission_system])
  show "systems_agree_on definition_call_admission_system single_clause_reading_system
      (system_definitions definition_call_admission_system\<inter>system_definitions single_clause_reading_system)"
    by (rule systems_agree_on_subdomain[OF single_clause_reading_base_agreement]) blast
  show "systems_agree_on definition_call_admission_system environment_inclusion_system
      (system_definitions definition_call_admission_system\<inter>system_definitions environment_inclusion_system)"
    by (rule systems_agree_on_subdomain[OF related_test_environment_base_agreement]) blast
  show "system_definitions single_clause_reading_system\<inter>system_definitions environment_inclusion_system
      \<subseteq>system_definitions definition_call_admission_system" by auto
qed

definition related_test_components_system :: "(nat,nat,nat,nat) schema_system" where
  "related_test_components_system=system_union single_clause_reading_system environment_inclusion_system"

lemma related_test_components_formed [simp]: "schema_system_formed related_test_components_system"
  unfolding related_test_components_system_def
  by (rule system_union_agree_formed[OF single_clause_reading_system_formed environment_inclusion_system_formed
    related_test_components_agreement])

lemma related_test_components_definitions [simp]:
  "system_definitions related_test_components_system=
    system_definitions single_clause_reading_system\<union>system_definitions environment_inclusion_system"
  by (simp add: related_test_components_system_def)

lemma related_test_components_bound:
  "system_definitions related_test_components_system\<subseteq>{..127}"
  using single_clause_reading_definition_bound by auto

lemma related_test_components_call:
  "schema_call_formed related_test_components_system d t \<longleftrightarrow>
    d\<in>system_definitions related_test_components_system \<and> term_formed t"
  using system_union_agree_call[OF single_clause_reading_system_formed environment_inclusion_system_formed
    related_test_components_agreement, of d t]
  by (simp only: related_test_components_system_def system_union_definitions
    single_clause_reading_call environment_inclusion_call Un_iff; blast)

lemma related_test_component_meanings:
  "(83,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(113,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  "(127,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system"
proof -
  have right: "(d,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning environment_inclusion_system"
    if "d\<in>system_definitions environment_inclusion_system" for d
    using system_union_agree_right_locality(2)[OF single_clause_reading_system_formed
      environment_inclusion_system_formed related_test_components_agreement that, of t]
    by (simp only: related_test_components_system_def)
  have membership: "(83,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
      (83,t)\<in>positive_meaning package_membership_system"
    by (rule whole_system_agreement_meaning[OF package_membership_system_formed
      environment_inclusion_system_formed related_test_environment_package_agreement]) simp
  show "(83,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system" using right[of 83] membership by auto
  show "(113,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system" by (rule right) simp
  show "(127,t)\<in>positive_meaning related_test_components_system \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system"
    using system_union_agree_left_locality(2)[OF single_clause_reading_system_formed
      environment_inclusion_system_formed related_test_components_agreement, of 127 t]
    by (simp add: related_test_components_system_def)
qed

definition related_test_admission_base :: "(nat,nat,nat,nat) schema_system" where
  "related_test_admission_base=rooted_system related_test_components_system {83,113,127}"

lemma related_test_admission_base_formed [simp]: "schema_system_formed related_test_admission_base"
  unfolding related_test_admission_base_def by (rule rooted_system_formed[OF related_test_components_formed])

lemma related_test_admission_base_roots: "{83,113,127}\<subseteq>system_definitions related_test_admission_base"
  unfolding related_test_admission_base_def by (rule rooted_system_roots[OF related_test_components_formed]) auto

lemma related_test_admission_base_bound: "system_definitions related_test_admission_base\<subseteq>{..127}"
  unfolding related_test_admission_base_def
  by (rule subset_trans[OF rooted_system_subdomain related_test_components_bound])

lemma related_test_admission_base_least:
  assumes "{83,113,127}\<subseteq>U" "system_dependency_closed related_test_components_system U"
  shows "system_definitions related_test_admission_base\<subseteq>U"
  unfolding related_test_admission_base_def by (rule rooted_system_least[OF related_test_components_formed _ assms]) auto

lemma related_test_admission_base_call:
  "schema_call_formed related_test_admission_base d t \<longleftrightarrow>
    d\<in>system_definitions related_test_admission_base \<and> term_formed t"
  unfolding related_test_admission_base_def
  by (rule rooted_system_variable_calls[OF related_test_components_formed related_test_components_call])

lemma related_test_admission_base_meaning:
  assumes "d\<in>system_definitions related_test_admission_base"
  shows "(d,t)\<in>positive_meaning related_test_admission_base \<longleftrightarrow>
    (d,t)\<in>positive_meaning related_test_components_system"
  using rooted_system_meaning_at[OF related_test_components_formed assms[unfolded related_test_admission_base_def]]
  by (simp only: related_test_admission_base_def)

section \<open>Four ordinary premises check the whole profile\<close>

abbreviation related_test_admission_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "related_test_admission_argument e u r d \<equiv> Pair_Term (Pair_Term e (Pair_Term u r)) d"

definition related_test_admission_schema :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_test_admission_schema c k=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))),
     (1,113,Pattern_Pair (exact_term_pattern c) (Pattern_Variable 5)),
     (2,113,Pattern_Pair data_x (Pattern_Variable 5)),
     (3,127,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair data_w (Pattern_Variable 4)))
       (related_test_reference_pattern (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
         (Pattern_Variable 9) (exact_term_pattern k) (Pattern_Variable 10)))}"

definition related_test_admission_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "related_test_admission_system c k=add_view_definition related_test_admission_base 264 data_x
    {(0,related_test_admission_schema c k)}"

abbreviation related_test_admission_result :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "related_test_admission_result c k p \<equiv> \<exists>C compare z. environment_value_presents C c \<and>
    k=definition_site_value compare \<and> related_test_package_domain C compare z \<and> program_entry_presents z p"

locale related_test_admission =
  fixes c k :: factor_term
  assumes fields: "term_formed c" "term_formed k"
begin

lemma schema_formed: "schema_formed (related_test_admission_schema c k)"
  using fields by (auto simp: related_test_admission_schema_def related_test_reference_pattern_def
    schema_formed_def single_valued_def octets_formed_def)

lemma dependencies: "schema_dependencies (related_test_admission_schema c k)={83,113,127}"
  by (simp add: related_test_admission_schema_def schema_dependencies_def rel_ran_image)

sublocale view: positive_view related_test_admission_base 264 data_x "{(0,related_test_admission_schema c k)}"
  by (rule positive_view.intro)
    (use related_test_admission_base_bound related_test_admission_base_roots schema_formed dependencies
      in \<open>auto simp: single_valued_def dest: subsetD\<close>)

lemma formed: "schema_system_formed (related_test_admission_system c k)"
  using view.formed by (simp only: related_test_admission_system_def)

lemma definitions [simp]: "system_definitions (related_test_admission_system c k)=
  insert 264 (system_definitions related_test_admission_base)"
  by (simp add: related_test_admission_system_def)

lemma calls: "schema_call_formed (related_test_admission_system c k) d t \<longleftrightarrow>
  d\<in>system_definitions (related_test_admission_system c k) \<and> term_formed t"
  using added_variable_calls[OF related_test_admission_base_formed view.formed related_test_admission_base_call]
  by (simp only: related_test_admission_system_def)

lemma old_meaning:
  assumes "d\<in>system_definitions related_test_admission_base"
  shows "(d,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (d,t)\<in>positive_meaning related_test_admission_base"
  using view.old_meaning[OF assms] by (simp only: related_test_admission_system_def)

lemma clause [simp]: "((264,n),S)\<in>system_clauses (related_test_admission_system c k) \<longleftrightarrow>
  n=0 \<and> S=related_test_admission_schema c k"
  using view.no_old_clause by (auto simp: related_test_admission_system_def)

lemma components:
  "(83,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(113,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  "(127,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system"
proof -
  have retained: "d\<in>system_definitions related_test_admission_base" if "d\<in>{83,113,127}" for d
    by (rule subsetD[OF related_test_admission_base_roots that])
  have agreement: "(d,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
      (d,t)\<in>positive_meaning related_test_components_system" if "d\<in>{83,113,127}" for d
    by (simp only: old_meaning[OF retained[OF that]] related_test_admission_base_meaning[OF retained[OF that]])
  show "(83,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
    using agreement[of 83] by (simp add: related_test_component_meanings)
  show "(113,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
    using agreement[of 113] by (simp add: related_test_component_meanings)
  show "(127,t)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system"
    using agreement[of 127] by (simp add: related_test_component_meanings)
qed

lemma valuation:
  "(264,p)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h j)) \<and>
      p=related_test_admission_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)) \<and>
      (83,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)))\<in>positive_meaning package_membership_system \<and>
      (113,Pair_Term c (h 5))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 0) (h 5))\<in>positive_meaning environment_inclusion_system \<and>
      (127,schema_reference_argument (h 5) (h 3) (h 4)
        (related_test_reference_value (h 6) (h 7) (h 8) (h 9) k (h 10)))\<in>positive_meaning single_clause_reading_system)"
proof -
  have ordinary: "schema_material_premises (related_test_admission_schema c k)={}"
    by (simp add: related_test_admission_schema_def)
  have accepts: "schema_call_formed (related_test_admission_system c k) 264
      (evaluate_pattern h (schema_conclusion (related_test_admission_schema c k)))"
    if "\<forall>a\<in>schema_variables (related_test_admission_schema c k). term_formed (h a)" for h
    using that fields by (auto simp: calls related_test_admission_schema_def
      related_test_reference_pattern_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    using fields apply (simp add: related_test_admission_schema_def related_test_reference_pattern_def
      related_test_reference_value_def schema_variables_def components conj_ac all_conj_distrib imp_conjL)
    done
qed

lemma step:
  assumes member: "(83,package_subject_argument e u r (Pair_Term du dr))\<in>positive_meaning package_membership_system"
    and fixed: "(113,Pair_Term c w)\<in>positive_meaning environment_inclusion_system"
    and source: "(113,Pair_Term e w)\<in>positive_meaning environment_inclusion_system"
    and read: "(127,schema_reference_argument w du dr (related_test_reference_value x y s t k test))
      \<in>positive_meaning single_clause_reading_system"
  shows "(264,related_test_admission_argument e u r (Pair_Term du dr))
    \<in>positive_meaning (related_test_admission_system c k)"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed du" "term_formed dr"
    "term_formed w" "term_formed x" "term_formed y" "term_formed s" "term_formed t" "term_formed test"
    using schema_call_formed_target[OF positive_meaning_formed[OF member]]
      schema_call_formed_target[OF positive_meaning_formed[OF read]]
    by (auto simp: related_test_reference_value_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then du
    else if j=4 then dr else if j=5 then w else if j=6 then x else if j=7 then y
    else if j=8 then s else if j=9 then t else test"
  show ?thesis by (simp only: valuation; rule exI[of _ ?h]) (use formed assms in auto)
qed

theorem sound:
  assumes holds: "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
  shows "related_test_admission_result c k p"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where shape:
    "p=related_test_admission_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4))"
    and reads:
      "(83,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)))\<in>positive_meaning package_membership_system"
      "(113,Pair_Term c (h 5))\<in>positive_meaning environment_inclusion_system"
      "(113,Pair_Term (h 0) (h 5))\<in>positive_meaning environment_inclusion_system"
      "(127,schema_reference_argument (h 5) (h 3) (h 4)
        (related_test_reference_value (h 6) (h 7) (h 8) (h 9) k (h 10)))\<in>positive_meaning single_clause_reading_system"
    using holds by (simp only: valuation) blast
  obtain E pu pr d P where source: "environment_value_presents E (h 0)"
    "h 1=use_data_term pu" "h 2=Payload_Term pr" "Pair_Term (h 3) (h 4)=definition_site_value d"
    "native_package_at E pu pr P" "d\<in>system_definitions P"
    using reads(1) by (simp only: package_membership_exact factor_term.inject) blast
  have entry: "h 3=use_data_term (fst d)" "h 4=Payload_Term (snd d)"
    using source(4) by (simp_all add: site_data_term_def)
  obtain C H where fixed: "environment_value_presents C c" "environment_value_presents H (h 5)"
    "environment_included C H"
    using reads(2) by (simp only: environment_inclusion_exact factor_term.inject) blast
  have common: "environment_formed C" "environment_formed H"
    using environment_value_presents_formed[OF fixed(1)] environment_value_presents_formed[OF fixed(2)] by blast+
  have included: "environment_included E H"
    using reads(3) by (simp only: environment_inclusion_on_values[OF source(1) fixed(2)])
  obtain S where actual: "native_single_clause_at H (fst d) (snd d) S"
    "schema_reference_presents S (related_test_reference_value (h 6) (h 7) (h 8) (h 9) k (h 10))"
    using reads(4) by (simp only: entry single_clause_reading_on_values[OF fixed(2)]) blast
  obtain x y s t compare test where roles: "k=definition_site_value compare" "x\<noteq>y" "s\<noteq>t"
    "S=related_test_clause x y s t compare test"
    using related_test_reference_recovers[OF actual(2)] by blast
  have profile: "native_related_test_at H (fst d) (snd d) compare test"
    using actual(1) roles(2-4) by (auto simp: native_related_test_at_def)
  have whole: "native_related_test_package C compare E pu pr d"
    unfolding native_related_test_package_def
    by (rule conjI[OF common(1)], rule exI[of _ P], rule exI[of _ H], rule exI[of _ test])
      (use source(5,6) common(2) fixed(3) included profile in blast)
  let ?z="((E,(pu,pr)),d)"
  have boundary: "program_entry_context_formed ?z"
    by (rule related_test_package_boundary[where C=C and k=compare]) (use whole in simp)
  have positions: "(pu,pr)\<in>environment_positions E" "d\<in>environment_positions E"
    using boundary by (auto simp: program_entry_context_formed_def)
  have encoded_context: "p=Pair_Term (Pair_Term (h 0) (site_data_term pu pr)) (site_data_term (fst d) (snd d))"
    using shape source(2-4) by (simp add: site_data_term_def)
  have presented: "program_entry_presents ?z p"
    by (rule iffD2[OF program_entry_presents_fields], rule conjI[OF positions(1)],
      rule conjI[OF positions(2)], rule exI[of _ "h 0"])
      (use source(1) encoded_context in blast)
  show ?thesis by (rule exI[of _ C], rule exI[of _ compare], rule exI[of _ ?z])
    (use fixed(1) roles(1) whole presented in simp)
qed

theorem complete:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
    and source: "environment_value_presents E e" and profile: "native_related_test_package C compare E pu pr d"
  shows "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<in>positive_meaning (related_test_admission_system c k)"
proof -
  obtain P H test where data: "native_package_at E pu pr P" "d\<in>system_definitions P"
    "environment_formed H" "environment_included C H" "environment_included E H"
    "native_related_test_at H (fst d) (snd d) compare test"
    using profile unfolding native_related_test_package_def by blast
  obtain x y s t where roles: "x\<noteq>y" "s\<noteq>t"
    and read: "native_single_clause_at H (fst d) (snd d) (related_test_clause x y s t compare test)"
    using data(6) by (auto simp: native_related_test_at_def)
  obtain a where schema: "native_schema_at H (fst d) a (related_test_clause x y s t compare test)"
    using native_single_clause_schema[OF read] by blast
  have addresses: "octets_formed x" "octets_formed y" "octets_formed s" "octets_formed t"
    "octets_formed (snd compare)" "octets_formed (snd test)"
    using native_schema_data_formed[OF schema] by (auto simp: schema_data_formed_def)
  let ?v="related_test_reference_value (Payload_Term x) (Payload_Term y) (Payload_Term s) (Payload_Term t)
    (definition_site_value compare) (definition_site_value test)"
  have report: "schema_reference_presents (related_test_clause x y s t compare test) ?v"
    by (rule related_test_reference_presents[OF roles addresses])
  obtain w where extension: "environment_value_presents H w"
    using environment_value_presents_total[OF data(3)] by blast
  have member: "(83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
      \<in>positive_meaning package_membership_system"
    by (rule package_membership_complete[OF source data(1,2)])
  have first: "(113,Pair_Term c w)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF fixed extension data(4)])
  have second: "(113,Pair_Term e w)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF source extension data(5)])
  have checked: "(127,schema_reference_argument w (use_data_term (fst d)) (Payload_Term (snd d))
      (related_test_reference_value (Payload_Term x) (Payload_Term y) (Payload_Term s) (Payload_Term t)
        k (definition_site_value test)))\<in>positive_meaning single_clause_reading_system"
    using single_clause_reading_complete[OF extension read report] by (simp only: encoded)
  show ?thesis using step[OF member[unfolded site_data_term_def] first second checked]
    by (simp only: site_data_term_def)
qed

theorem exact:
  "(264,p)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow> related_test_admission_result c k p"
proof
  show "(264,p)\<in>positive_meaning (related_test_admission_system c k) \<Longrightarrow> related_test_admission_result c k p"
    by (rule sound)
next
  assume "related_test_admission_result c k p"
  then obtain C compare z where parts: "environment_value_presents C c" "k=definition_site_value compare"
    "related_test_package_domain C compare z" "program_entry_presents z p" by blast
  obtain E pu pr d where shape: "z=((E,(pu,pr)),d)" by (cases z; auto split: prod.splits)
  have profile: "native_related_test_package C compare E pu pr d" using parts(3) by (simp only: shape fst_conv snd_conv)
  obtain e where source: "environment_value_presents E e"
    "p=related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)"
    using parts(4) by (simp only: shape program_entry_presents_fields site_data_term_def) blast
  show "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
    using complete[OF parts(1,2) source(1) profile] by (simp only: source(2))
qed

theorem on_presentations:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
    and source: "program_entry_presents z p"
  shows "(264,p)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    related_test_package_domain C compare z"
proof
  assume holds: "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
  obtain B other w where actual: "environment_value_presents B c" "k=definition_site_value other"
    "related_test_package_domain B other w" "program_entry_presents w p"
    using sound[OF holds] by blast
  have reference: "B=C" by (rule environment_value_presents_unique[OF actual(1) fixed])
  have entry: "other=compare" using actual(2) encoded by (metis definition_site_value_eq)
  have same_context: "w=z" by (rule program_entries.recovery[OF actual(4) source])
  show "related_test_package_domain C compare z" using actual(3) by (simp only: reference entry same_context)
next
  assume profile: "related_test_package_domain C compare z"
  show "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
    by (simp only: exact; rule exI[of _ C], rule exI[of _ compare], rule exI[of _ z])
      (use fixed encoded profile source in blast)
qed

theorem on_values:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
    and source: "environment_value_presents E e"
  shows "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
      \<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
    native_related_test_package C compare E pu pr d"
proof
  let ?p="related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)"
  assume holds: "(264,?p)\<in>positive_meaning (related_test_admission_system c k)"
  obtain B other w where actual: "environment_value_presents B c" "k=definition_site_value other"
    "related_test_package_domain B other w" "program_entry_presents w ?p"
    using sound[OF holds] by blast
  have reference: "B=C" by (rule environment_value_presents_unique[OF actual(1) fixed])
  have entry: "other=compare" using actual(2) encoded by (metis definition_site_value_eq)
  obtain f where source_record: "environment_value_presents (fst (fst w)) f"
    "?p=Pair_Term (Pair_Term f (site_data_term (fst (snd (fst w))) (snd (snd (fst w)))))
      (definition_site_value (snd w))"
    using actual(4) by (auto simp: program_entry_value_presents_def site_value_presents_def)
  have fields: "f=e" "fst (snd (fst w))=pu" "snd (snd (fst w))=pr" "snd w=d"
    using source_record(2) by (auto simp: site_data_term_def inj_eq[OF use_data_term_injective] prod_eq_iff)
  have present: "environment_value_presents (fst (fst w)) e" using source_record(1) fields(1) by simp
  have environment: "fst (fst w)=E" by (rule environment_value_presents_unique[OF present source])
  show "native_related_test_package C compare E pu pr d"
    using actual(3) by (simp only: reference entry environment fields(2-4))
next
  assume profile: "native_related_test_package C compare E pu pr d"
  show "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<in>positive_meaning (related_test_admission_system c k)"
    by (rule complete[OF fixed encoded source profile])
qed

theorem presentation_class:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
  shows "presentation_class (\<lambda>z p. related_test_package_domain C compare z \<and> program_entry_presents z p)
    (related_test_package_domain C compare) (\<lambda>p. (264,p)\<in>positive_meaning (related_test_admission_system c k))"
proof -
  have equation: "(264,p)\<in>positive_meaning (related_test_admission_system c k) \<longleftrightarrow>
      (\<exists>z. related_test_package_domain C compare z \<and> program_entry_presents z p)" for p
  proof
    assume holds: "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
    obtain B other z where actual: "environment_value_presents B c" "k=definition_site_value other"
      "related_test_package_domain B other z" "program_entry_presents z p"
      using sound[OF holds] by blast
    have reference: "B=C" by (rule environment_value_presents_unique[OF actual(1) fixed])
    have entry: "other=compare" using actual(2) encoded by (metis definition_site_value_eq)
    show "\<exists>z. related_test_package_domain C compare z \<and> program_entry_presents z p"
      by (rule exI[of _ z]) (use actual(3,4) reference entry in simp)
  next
    assume "\<exists>z. related_test_package_domain C compare z \<and> program_entry_presents z p"
    then obtain z where parts: "related_test_package_domain C compare z" "program_entry_presents z p" by blast
    show "(264,p)\<in>positive_meaning (related_test_admission_system c k)"
      using parts(1) by (simp only: on_presentations[OF fixed encoded parts(2)])
  qed
  have admission: "(\<lambda>p. \<exists>z. related_test_package_domain C compare z \<and> program_entry_presents z p)=
    (\<lambda>p. (264,p)\<in>positive_meaning (related_test_admission_system c k))"
    by (intro ext; simp only: equation)
  show ?thesis using related_test_package_presentation_class[of C compare] by (simp only: admission)
qed

theorem missing_entry_rejected:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
    and source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and missing: "d\<notin>system_definitions P"
  shows "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<notin>positive_meaning (related_test_admission_system c k)"
proof
  assume holds: "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<in>positive_meaning (related_test_admission_system c k)"
  have profile: "native_related_test_package C compare E pu pr d"
    using holds by (simp only: on_values[OF fixed encoded source])
  show False using native_related_test_package_witnesses[OF profile package] missing by blast
qed

theorem changed_definition_rejected:
  assumes fixed: "environment_value_presents C c" and encoded: "k=definition_site_value compare"
    and source: "environment_value_presents E e" and actual: "native_definition_at E (fst d) (snd d) q B"
    and changed: "\<not>(\<exists>i n x y s t test. x\<noteq>y \<and> s\<noteq>t \<and>
      q=Pattern_Variable i \<and> B={(n,related_test_clause x y s t compare test)})"
  shows "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<notin>positive_meaning (related_test_admission_system c k)"
proof
  assume holds: "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
    \<in>positive_meaning (related_test_admission_system c k)"
  have profile: "native_related_test_package C compare E pu pr d"
    using holds by (simp only: on_values[OF fixed encoded source])
  obtain H i n x y s t test where data: "environment_formed H" "environment_included E H"
    "x\<noteq>y" "s\<noteq>t"
    "native_definition_at H (fst d) (snd d) (Pattern_Variable i) {(n,related_test_clause x y s t compare test)}"
    using profile by (auto simp: native_related_test_package_def native_related_test_at_def native_single_clause_at_def)
  have copied: "native_definition_at H (fst d) (snd d) q B"
    by (rule native_definition_included[OF actual data(2,1)])
  show False using native_definition_unique[OF copied data(5)] data(3,4) changed by blast
qed

theorem native_checker:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu T entry.
    closed_native_package_at B bu [] T \<and>
    (\<forall>p. term_formed p \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> related_test_admission_result c k p) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and B :: "local_address option artifact_environment" and bu T
    where closed: "closed_native_package_at B bu [] T"
    and future: "\<forall>d\<in>system_definitions (related_test_admission_system c k). \<forall>p. term_formed p \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] (g d) p I K \<and>
        native_package_environment G bu []=B \<and>
        (native_application_formed G bu [] au [] \<longleftrightarrow> schema_call_formed (related_test_admission_system c k) d p) \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> (d,p)\<in>positive_meaning (related_test_admission_system c k)) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x))"
    using compiled_program_future_applications[OF formed] by blast
  have member: "264\<in>system_definitions (related_test_admission_system c k)" by simp
  have applications: "\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
      native_package_at G bu [] T \<and> native_application_at G au [] (g 264) p I K \<and>
      native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
      (native_positive_holds G bu [] au [] \<longleftrightarrow> related_test_admission_result c k p) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)"
    if "term_formed p" for p
    using future[rule_format, OF member that] that by (simp only: calls exact) auto
  show ?thesis by (rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ "g 264"])
    (use closed applications in blast)
qed

end

theorem related_test_admission_presentation_invariance:
  assumes fixed: "environment_value_presents C c" "environment_value_presents C c'"
    and coordinate: "term_formed (definition_site_value k)"
    and first: "program_entry_presents z p" and second: "program_entry_presents z q"
  shows "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k)) \<longleftrightarrow>
    (264,q)\<in>positive_meaning (related_test_admission_system c' (definition_site_value k))"
proof -
  have fields: "term_formed c" "term_formed c'"
    using environment_value_presents_formed[OF fixed(1)] environment_value_presents_formed[OF fixed(2)] by blast+
  interpret left: related_test_admission c "definition_site_value k" by (rule related_test_admission.intro[OF fields(1) coordinate])
  interpret right: related_test_admission c' "definition_site_value k" by (rule related_test_admission.intro[OF fields(2) coordinate])
  show ?thesis by (simp only: left.on_presentations[OF fixed(1) refl first] right.on_presentations[OF fixed(2) refl second])
qed

text \<open>
  Four actual ordinary premises check package membership, the whole two-premise
  definition, and inclusion of both the complete reference and candidate scopes
  in one formed common environment. The report's private coordinates and test
  callee are witnesses. Complete report recovery supplies their exact profile.

  One new definition uses the least dependency closure of three existing entries.
  Complete shared-definition agreement preserves their original clauses and
  meanings. Source and reference presentation choices preserve admission.
  Missing entries, changed interfaces, extra clauses, and altered profile syntax
  cannot pass the complete definition check. One compiled native program is
  fixed before all future submitted contexts; its complete scope is retained.

  Exactness is for the independently stated finite profile. The mathematical
  comparison contract supplies the separate global semantic consequence.
\<close>

end
