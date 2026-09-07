theory Factor_Package_Closure_Admission
  imports Factor_Definition_Callee_Inclusion
begin

section \<open>A finite checked bound characterizes the existing least closure\<close>

theorem native_package_finite_closed_bound:
  "native_package_formed E roots \<longleftrightarrow> environment_formed E \<and>
    (\<exists>U. finite U \<and> roots\<subseteq>U \<and>
      (\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U)))"
proof
  assume package: "native_package_formed E roots"
  let ?U="native_definition_sites E roots"
  have ef: "environment_formed E" using package by (simp add: native_package_formed_def)
  have finite: "finite ?U" by (rule native_package_sites(2)[OF package])
  have defined: "\<forall>d\<in>?U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U)"
  proof (intro ballI)
    fix d assume member: "d\<in>?U"
    obtain p C where raw: "native_definition_at E (fst d) (snd d) p C"
      using package member by (auto simp: native_package_formed_def)
    have closed: "schema_dependencies S\<subseteq>?U" if clause: "(c,S)\<in>C" for c S
    proof
      fix e assume dependency: "e\<in>schema_dependencies S"
      have edge: "(d,e)\<in>native_definition_edges E"
        using raw clause dependency by (auto simp: native_definition_edges_def)
      show "e\<in>?U" by (rule native_definition_step[OF member edge])
    qed
    show "\<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U)" using raw closed by blast
  qed
  show "environment_formed E \<and> (\<exists>U. finite U \<and> roots\<subseteq>U \<and>
    (\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U)))"
    using ef finite native_definition_roots[of roots E] defined by blast
next
  assume "environment_formed E \<and> (\<exists>U. finite U \<and> roots\<subseteq>U \<and>
    (\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U)))"
  then obtain U where ef: "environment_formed E" and roots: "roots\<subseteq>U"
    and defined: "\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U)" by blast
  have closed: "e\<in>U" if member: "d\<in>U" and edge: "(d,e)\<in>native_definition_edges E" for d e
  proof -
    obtain p C where raw: "native_definition_at E (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U" using defined member by blast
    obtain q D c S where dependency: "native_definition_at E (fst d) (snd d) q D"
      "(c,S)\<in>D" "e\<in>schema_dependencies S"
      using edge by (auto simp: native_definition_edges_def)
    have same: "C=D" using native_definition_unique[OF raw(1) dependency(1)] by blast
    show ?thesis using raw(2) dependency(2,3) same by blast
  qed
  have reached: "native_definition_sites E roots\<subseteq>U" by (rule native_definition_sites_least[OF roots closed])
  show "native_package_formed E roots" using ef defined reached by (force simp: native_package_formed_def)
qed

lemma native_definition_site_data_formed:
  assumes raw: "native_definition_at E u r p C"
  shows "term_formed (site_data_term u r)"
proof -
  obtain R ps i m where parts: "environment_formed E" "artifact_at E u R" "record_at R r ps [i,m]"
    using raw by (auto simp: native_definition_at_def)
  have rf: "exact_formed R" using parts(1,2) by (auto simp: environment_formed_def)
  have root: "r\<in>rra_carrier (object_structure R)" using parts(3) by (simp add: record_at_def)
  show ?thesis using rf root by (auto simp: exact_formed_def)
qed

section \<open>One ordinary clause hides the finite bound and checks every member\<close>

abbreviation package_closure_admission_result :: "factor_term \<Rightarrow> bool" where
  "package_closure_admission_result z \<equiv> \<exists>E e rs.
    z=Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)) \<and>
    environment_value_presents E e \<and> native_package_formed E (set rs)"

definition package_closure_admission_schema :: "(nat,nat,nat) factor_schema" where
  "package_closure_admission_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,26,data_x),(1,47,Pattern_Pair data_y data_z),
     (2,76,Pattern_Pair (Pattern_Pair data_x data_z) data_z)}"

definition package_closure_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "package_closure_admission_system=add_view_definition definition_callee_list_system 77 data_x {(0,package_closure_admission_schema)}"

lemma package_closure_admission_system_formed [simp]: "schema_system_formed package_closure_admission_system"
  unfolding package_closure_admission_system_def
  by (rule add_recursive_definition_formed[OF definition_callee_list_system_formed])
    (auto simp: package_closure_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_closure_admission_definitions [simp]:
  "system_definitions package_closure_admission_system=insert 77 (system_definitions definition_callee_list_system)"
  by (simp add: package_closure_admission_system_def)

lemma package_closure_admission_call:
  "schema_call_formed package_closure_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions package_closure_admission_system \<and> term_formed t"
  using added_variable_calls[OF definition_callee_list_system_formed
    package_closure_admission_system_formed[unfolded package_closure_admission_system_def] definition_callee_list_call]
  by (simp only: package_closure_admission_system_def[symmetric])

lemma package_closure_admission_old_meaning:
  assumes "d\<in>system_definitions definition_callee_list_system"
  shows "(d,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_callee_list_system"
  using added_definition_preserves_old(2)[OF definition_callee_list_system_formed
    package_closure_admission_system_formed[unfolded package_closure_admission_system_def], of d t] assms
  by (auto simp: package_closure_admission_system_def)

lemma package_closure_admission_clause [simp]:
  "((77,c),S)\<in>system_clauses package_closure_admission_system \<longleftrightarrow> (c,S)\<in>{(0,package_closure_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_callee_list_system \<Longrightarrow>
    d\<in>system_definitions definition_callee_list_system" for d c S
    using definition_callee_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((77,c),S)\<notin>system_clauses definition_callee_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_closure_admission_system_def)
qed

lemma package_closure_previous_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning definition_call_admission_system"
  using package_closure_admission_old_meaning[of d t] definition_callee_list_old_meaning[of d t]
    definition_callee_previous_meaning[OF assms, of t] assms by auto

lemma package_closure_admission_components:
  "(26,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
  "(47,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  using package_closure_previous_meaning[of 26 t] definition_call_admission_instantiation_meaning[of 26 t]
    schema_instantiation_pattern_meaning[of 26 t] pattern_instantiation_quotation_meaning[of 26 t]
    quotation_admission_projection_meaning[of 26 t] target_projection_environment_meaning[of 26 t]
    environment_identity_admission[of t]
    package_closure_admission_old_meaning[of 47 t] definition_callee_list_old_meaning[of 47 t]
    definition_callee_inclusion_components(7)[of t] package_closure_admission_old_meaning[of 76 t] by auto

lemma package_closure_admission_step:
  assumes source: "environment_value_presents E e"
    and roots: "(47,Pair_Term r w)\<in>positive_meaning data_subset_system"
    and bound: "(76,Pair_Term (Pair_Term e w) w)\<in>positive_meaning definition_callee_list_system"
  shows "(77,Pair_Term e r)\<in>positive_meaning package_closure_admission_system"
proof -
  have formed: "term_formed e" "term_formed r" "term_formed w"
    using environment_value_presents_formed[OF source]
      schema_call_formed_target[OF positive_meaning_formed[OF roots]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then r else w"
  have result: "(77,evaluate_pattern ?h (schema_conclusion package_closure_admission_schema))
      \<in>positive_meaning package_closure_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: package_closure_admission_schema_def schema_variables_def
        package_closure_admission_call package_closure_admission_components\<close>)
  show ?thesis using result by (simp add: package_closure_admission_schema_def)
qed

theorem package_closure_admission_sound:
  assumes holds: "(77,z)\<in>positive_meaning package_closure_admission_system"
  shows "package_closure_admission_result z"
proof -
  have consequence: "(77,z)\<in>schema_consequences package_closure_admission_system (positive_meaning package_closure_admission_system)"
    using holds positive_meaning_unfold[of package_closure_admission_system] by blast
  obtain n S h where clause: "((77,n),S)\<in>system_clauses package_closure_admission_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning package_closure_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=package_closure_admission_schema" using clause by simp
  have calls: "\<exists>E. environment_value_presents E (h 0)"
    "(47,Pair_Term (h 1) (h 2))\<in>positive_meaning data_subset_system"
    "(76,Pair_Term (Pair_Term (h 0) (h 2)) (h 2))\<in>positive_meaning definition_callee_list_system"
    using support by (auto simp: schema package_closure_admission_schema_def package_closure_admission_components)
  obtain E where source: "environment_value_presents E (h 0)" using calls(1) by blast
  obtain xs ys where bounds: "h 1=data_list_term xs" "h 2=data_list_term ys"
    "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
    using calls(2) by (auto simp: data_subset_exact)
  let ?P="\<lambda>d. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  have entries: "\<forall>x\<in>set ys. \<exists>u r p C. x=site_data_term u r \<and> native_definition_at E u r p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
    using calls(3) by (simp only: bounds(2) definition_callee_list_on_values[OF source bounds(4)])
  have checked: "\<forall>x\<in>set ys. \<exists>d. x=definition_site_value d \<and> ?P d"
  proof (intro ballI)
    fix x assume member: "x\<in>set ys"
    obtain u r p C where parts: "x=site_data_term u r" "native_definition_at E u r p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      using entries member by blast
    show "\<exists>d. x=definition_site_value d \<and> ?P d" by (rule exI[of _ "(u,r)"]) (use parts in auto)
  qed
  obtain ds where definitions: "ys=map (\<lambda>d. definition_site_value d) ds" "\<forall>d\<in>set ds. ?P d"
    using iffD1[OF list_range_restricted_witnesses checked] by blast
  have roots: "\<forall>x\<in>set xs. \<exists>d. x=definition_site_value d \<and> d\<in>set ds"
    using bounds(5) definitions(1) by auto
  obtain rs where root_sites: "xs=map (\<lambda>d. definition_site_value d) rs" "set rs\<subseteq>set ds"
    using iffD1[OF list_range_restricted_witnesses roots] by blast
  have defined: "\<forall>d\<in>set ds. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>set ds)"
    using definitions(2) by (simp add: definitions(1))
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have package: "native_package_formed E (set rs)"
    by (simp only: native_package_finite_closed_bound)
      (use ef root_sites(2) defined in \<open>auto intro!: exI[of _ "set ds"]\<close>)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ rs])
      (use source package conclusion bounds(1) root_sites(1) in \<open>simp add: schema package_closure_admission_schema_def\<close>)
qed

theorem package_closure_admission_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_formed E (set rs)"
  shows "(77,Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)))
    \<in>positive_meaning package_closure_admission_system"
proof -
  obtain U where bound: "finite U" "set rs\<subseteq>U"
    "\<forall>d\<in>U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>U)"
    using package by (simp only: native_package_finite_closed_bound) blast
  obtain ds where rows: "set ds=U" using finite_distinct_list[OF bound(1)] by blast
  let ?ys="map (\<lambda>d. definition_site_value d) ds"
  let ?xs="map (\<lambda>d. definition_site_value d) rs"
  have formed: "term_formed (definition_site_value d)" if "d\<in>U" for d
    using bound(3)[rule_format, OF that] native_definition_site_data_formed by blast
  have data: "data_elements ?ys" "data_elements ?xs" using formed bound(2) rows by auto
  have roots: "(47,Pair_Term (data_list_term ?xs) (data_list_term ?ys))\<in>positive_meaning data_subset_system"
    by (simp only: data_subset_lists) (use data rows bound(2) in auto)
  have checked: "(76,Pair_Term (Pair_Term e (data_list_term ?ys)) (data_list_term ?ys))
      \<in>positive_meaning definition_callee_list_system"
    by (simp only: definition_callee_list_at_sites[OF source data(1)])
      (use bound(3) rows in \<open>simp\<close>)
  show ?thesis by (rule package_closure_admission_step[OF source roots checked])
qed

theorem package_closure_admission_exact:
  "(77,z)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> package_closure_admission_result z"
  using package_closure_admission_sound package_closure_admission_complete by blast

corollary package_closure_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(77,Pair_Term e r)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow>
    (\<exists>rs. r=data_list_term (map (\<lambda>d. definition_site_value d) rs) \<and> native_package_formed E (set rs))"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: package_closure_admission_exact factor_term.inject) (use source unique in blast)
qed

corollary package_closure_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(77,Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)))
      \<in>positive_meaning package_closure_admission_system \<longleftrightarrow> native_package_formed E (set rs)"
  by (simp only: package_closure_admission_at_source[OF source] data_list_term_injective
    injective_mapped_lists[OF definition_site_value_injective]) blast

corollary package_closure_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(77,Pair_Term e r)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow>
    (77,Pair_Term f r)\<in>positive_meaning package_closure_admission_system"
  by (simp only: package_closure_admission_at_source[OF assms(1)] package_closure_admission_at_source[OF assms(2)])

corollary package_closure_admission_root_sets:
  assumes source: "environment_value_presents E e" and same: "set rs=set ss"
  shows "(77,Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)))\<in>positive_meaning package_closure_admission_system
    \<longleftrightarrow> (77,Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) ss)))\<in>positive_meaning package_closure_admission_system"
  by (simp only: package_closure_admission_on_values[OF source] same)

corollary package_closure_admission_empty:
  assumes source: "environment_value_presents E e"
  shows "(77,Pair_Term e (Payload_Term []))\<in>positive_meaning package_closure_admission_system"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have package: "native_package_formed E {}" using ef by (simp add: native_package_formed_def native_definition_sites_def)
  show ?thesis using package_closure_admission_complete[OF source, of "[]"] package by simp
qed

corollary package_closure_admission_rejects_unreadable_site:
  assumes source: "environment_value_presents E e" and reached: "d\<in>native_definition_sites E (set rs)"
    and missing: "\<not>(\<exists>p C. native_definition_at E (fst d) (snd d) p C)"
  shows "(77,Pair_Term e (data_list_term (map (\<lambda>d. definition_site_value d) rs)))\<notin>positive_meaning package_closure_admission_system"
  by (simp only: package_closure_admission_on_values[OF source])
    (use reached missing in \<open>auto simp: native_package_formed_def\<close>)

section \<open>Five fixed native entries precede all future operands\<close>

lemma package_closure_operation_components:
  "(73,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (73,t)\<in>positive_meaning schema_callee_inclusion_system"
  "(74,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (74,t)\<in>positive_meaning schema_callee_list_system"
  "(75,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (75,t)\<in>positive_meaning definition_callee_inclusion_system"
  "(76,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  using package_closure_admission_old_meaning[of 73 t] definition_callee_list_old_meaning[of 73 t]
    definition_callee_inclusion_old_meaning[of 73 t] schema_callee_list_old_meaning[of 73 t]
    package_closure_admission_old_meaning[of 74 t] definition_callee_list_old_meaning[of 74 t]
    definition_callee_inclusion_old_meaning[of 74 t]
    package_closure_admission_old_meaning[of 75 t] definition_callee_list_old_meaning[of 75 t]
    package_closure_admission_old_meaning[of 76 t] by auto

abbreviation package_closure_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "package_closure_operation_result d t \<equiv>
    (d=73 \<and> schema_callee_inclusion_result t) \<or> (d=74 \<and> schema_callee_list_result t) \<or>
    (d=75 \<and> definition_callee_inclusion_result t) \<or> (d=76 \<and> definition_callee_list_result t) \<or>
    (d=77 \<and> package_closure_admission_result t)"

lemma package_closure_operations_exact:
  assumes "d\<in>{73,74,75,76,77}"
  shows "(d,t)\<in>positive_meaning package_closure_admission_system \<longleftrightarrow> package_closure_operation_result d t"
proof -
  consider "d=73" | "d=74" | "d=75" | "d=76" | "d=77" using assms by auto
  then show ?thesis
    by cases (simp_all add: package_closure_operation_components schema_callee_inclusion_exact schema_callee_list_exact
      definition_callee_inclusion_exact definition_callee_list_exact package_closure_admission_exact)
qed

theorem native_package_closure_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {73::nat,74,75,76,77} \<and>
    (\<forall>d\<in>{73,74,75,76,77}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> package_closure_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions package_closure_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions package_closure_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed package_closure_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning package_closure_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF package_closure_admission_system_formed] by blast
  have sites: "inj_on g {73,74,75,76,77}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {73,74,75,76,77}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{73,74,75,76,77}" and tf: "term_formed t"
    have member: "d\<in>system_definitions package_closure_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed package_closure_admission_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning package_closure_admission_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> package_closure_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member package_closure_operations_exact[OF selected] in \<open>auto simp: package_closure_admission_call\<close>)
  qed
qed

text \<open>
  The argument contains the complete source presentation and supplied root-site
  list. The clause admits that environment, includes every root in one hidden
  finite bound, and checks every bound member and every callee of its complete
  actual clause family. Thus unrelated data cannot masquerade as a bound site.

  A successful bound contains the existing least root closure. Conversely that
  finite closure itself supplies a bound. Additional checked members, repeated
  entries, and enumeration order cannot change acceptance. The semantic package
  remains the actual least closure; the witness never replaces its definition
  domain or supplies a dispatcher. Each callee comes from its actual prospective
  citation. Cycles require no acyclicity assumption or traversal cut-off.

  All five entries have exact contracts over every term and preserve earlier
  meanings. The package entry permits every complete environment presentation
  and every list with the same root set. An empty root list still admits the
  environment, and an unreadable reached definition cannot be omitted.

  One fixed closed native program has five distinct sites before future formed
  operands and retains its canonical environment. It has seventy-eight
  definitions and one hundred and twenty-seven clauses. This entry takes
  supplied roots. The subsequent root-family reader and package admission
  compose it with actual package roots. Admitting calls at reached sites,
  complete admitted instances, finite evidence checking, the full transition
  protocol, reflection, and genesis remain required.
\<close>

end
