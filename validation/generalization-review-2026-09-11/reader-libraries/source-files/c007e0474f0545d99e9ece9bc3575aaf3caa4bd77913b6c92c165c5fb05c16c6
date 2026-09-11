theory Factor_Definition_Call_Admission
  imports Factor_Schema_Family_Admission
begin

section \<open>The actual definition admits the supplied interface operand\<close>

abbreviation definition_call_admission_result :: "factor_term \<Rightarrow> bool" where
  "definition_call_admission_result z \<equiv> \<exists>E e u r p C t.
    z=citation_observation_argument e (use_data_term u) (Payload_Term r) t \<and>
    environment_value_presents E e \<and> native_definition_at E u r p C \<and> pattern_accepts p t"

definition definition_call_admission_schema :: "(nat,nat,nat) factor_schema" where
  "definition_call_admission_schema=data_rule (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7),
         Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 8)])),
     (2,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 7) (Pattern_Variable 9)
       data_w (Pattern_Variable 10) (Pattern_Variable 11)),
     (3,71,source_root_pattern data_x data_y (Pattern_Variable 8)),
     (4,49,Pattern_Pair (data_list_pattern [data_z,Pattern_Variable 5,Pattern_Variable 6]) (Pattern_Variable 10)),
     (5,49,Pattern_Pair (data_list_pattern [data_z,Pattern_Variable 5,Pattern_Variable 6])
       (data_list_pattern [Pattern_Variable 8])),
     (6,49,Pattern_Pair (data_list_pattern [Pattern_Variable 8]) (Pattern_Variable 10))}"

definition definition_call_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "definition_call_admission_system=add_view_definition schema_family_admission_system 72 data_x {(0,definition_call_admission_schema)}"

lemma definition_call_admission_system_formed [simp]: "schema_system_formed definition_call_admission_system"
  unfolding definition_call_admission_system_def
  by (rule add_recursive_definition_formed[OF schema_family_admission_system_formed])
    (auto simp: definition_call_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma definition_call_admission_definitions [simp]:
  "system_definitions definition_call_admission_system=insert 72 (system_definitions schema_family_admission_system)"
  by (simp add: definition_call_admission_system_def)

lemma definition_call_admission_call:
  "schema_call_formed definition_call_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions definition_call_admission_system \<and> term_formed t"
  using added_variable_calls[OF schema_family_admission_system_formed
    definition_call_admission_system_formed[unfolded definition_call_admission_system_def] schema_family_admission_call]
  by (simp only: definition_call_admission_system_def[symmetric])

lemma definition_call_admission_old_meaning:
  assumes "d\<in>system_definitions schema_family_admission_system"
  shows "(d,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning schema_family_admission_system"
  using added_definition_preserves_old(2)[OF schema_family_admission_system_formed
    definition_call_admission_system_formed[unfolded definition_call_admission_system_def], of d t] assms
  by (auto simp: definition_call_admission_system_def)

lemma definition_call_admission_clause [simp]:
  "((72,c),S)\<in>system_clauses definition_call_admission_system \<longleftrightarrow> (c,S)\<in>{(0,definition_call_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses schema_family_admission_system \<Longrightarrow>
    d\<in>system_definitions schema_family_admission_system" for d c S
    using schema_family_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((72,c),S)\<notin>system_clauses schema_family_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: definition_call_admission_system_def)
qed

lemma definition_call_admission_instantiation_meaning:
  assumes "d\<in>system_definitions schema_instantiation_system"
  shows "(d,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning schema_instantiation_system"
  using definition_call_admission_old_meaning[of d t] schema_family_admission_previous_meaning[of d t]
    schema_admission_previous_meaning[OF assms, of t] assms by auto

lemma definition_call_admission_scoped_meaning:
  "(56,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    (56,t)\<in>positive_meaning scoped_instantiation_system"
  using definition_call_admission_instantiation_meaning[of 56 t] schema_instantiation_old_meaning[of 56 t]
    premise_family_instantiation_old_meaning[of 56 t] premise_rows_vector_meaning[of 56 t]
    vector_instantiation_old_meaning[of 56 t] row_values_old_meaning[of 56 t]
    application_reading_old_meaning[of 56 t] prospective_instantiation_old_meaning[of 56 t] by auto

lemma definition_call_admission_components:
  "(37,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(56,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (56,t)\<in>positive_meaning scoped_instantiation_system"
  "(71,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (71,t)\<in>positive_meaning schema_family_admission_system"
  "(49,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using definition_call_admission_instantiation_meaning[of 37 t] schema_instantiation_components(1)[of t]
    definition_call_admission_instantiation_meaning[of 34 t] schema_instantiation_components(2)[of t]
    definition_call_admission_scoped_meaning[of t] definition_call_admission_old_meaning[of 71 t]
    definition_call_admission_instantiation_meaning[of 49 t] schema_instantiation_components(7)[of t] by auto

lemma definition_call_admission_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p i,Pair_Term q m]))\<in>positive_meaning record_admission_system"
    and interface: "(56,scoped_instantiation_argument e u i b t j k)\<in>positive_meaning scoped_instantiation_system"
    and family: "(71,source_root_argument e u m)\<in>positive_meaning schema_family_admission_system"
    and outer_interface: "(49,Pair_Term (data_list_term [r,p,q]) j)\<in>positive_meaning payload_disjoint_system"
    and outer_family: "(49,Pair_Term (data_list_term [r,p,q]) (data_list_term [m]))\<in>positive_meaning payload_disjoint_system"
    and family_interface: "(49,Pair_Term (data_list_term [m]) j)\<in>positive_meaning payload_disjoint_system"
  shows "(72,citation_observation_argument e u r t)\<in>positive_meaning definition_call_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed t" "term_formed a"
    "term_formed p" "term_formed q" "term_formed i" "term_formed m" "term_formed b" "term_formed j" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF interface]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then t
    else if n=4 then a else if n=5 then p else if n=6 then q else if n=7 then i else if n=8 then m
    else if n=9 then b else if n=10 then j else k"
  have result: "(72,evaluate_pattern ?h (schema_conclusion definition_call_admission_schema))
      \<in>positive_meaning definition_call_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: definition_call_admission_schema_def schema_variables_def
        definition_call_admission_call definition_call_admission_components\<close>)
  show ?thesis using result by (simp add: definition_call_admission_schema_def)
qed

theorem definition_call_admission_sound:
  assumes holds: "(72,z)\<in>positive_meaning definition_call_admission_system"
  shows "definition_call_admission_result z"
proof -
  have consequence: "(72,z)\<in>schema_consequences definition_call_admission_system (positive_meaning definition_call_admission_system)"
    using holds positive_meaning_unfold[of definition_call_admission_system] by blast
  obtain n S h where clause: "((72,n),S)\<in>system_clauses definition_call_admission_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning definition_call_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=definition_call_admission_schema" using clause by simp
  have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 4) (h 2) (data_list_term [Pair_Term (h 5) (h 7),Pair_Term (h 6) (h 8)]))
      \<in>positive_meaning record_admission_system"
    "(56,scoped_instantiation_argument (h 0) (h 1) (h 7) (h 9) (h 3) (h 10) (h 11))
      \<in>positive_meaning scoped_instantiation_system"
    "(71,source_root_argument (h 0) (h 1) (h 8))\<in>positive_meaning schema_family_admission_system"
    "(49,Pair_Term (data_list_term [h 2,h 5,h 6]) (h 10))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [h 2,h 5,h 6]) (data_list_term [h 8]))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [h 8]) (h 10))\<in>positive_meaning payload_disjoint_system"
    using support by (auto simp: schema definition_call_admission_schema_def definition_call_admission_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 4)"
    using calls(1) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r a i b m where rec: "h 2=Payload_Term r" "h 5=Payload_Term a" "h 7=Payload_Term i"
    "h 6=Payload_Term b" "h 8=Payload_Term m" "record_at R r [a,b] [i,m]"
    using calls(2) by (simp only: record_admission_pair_fields[OF source(4)]) blast
  obtain xs p Is Ks where interface: "h 10=data_list_term (map Payload_Term Is)"
    "h 11=data_list_term (map Payload_Term Ks)" "scoped_pattern_at E u i p (set Is) (set Ks)"
    "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p (h 3)"
    using calls(3) by (simp only: source(2) rec(3) scoped_instantiation_at_source[OF source(1)]
      inj_eq[OF use_data_term_injective] factor_term.inject) blast
  obtain C where family: "native_schema_family_at E u m C"
    using calls(4) by (simp only: source(2) rec(5) schema_family_admission_on_values[OF source(1)]) blast
  have outer: "data_list_term [h 2,h 5,h 6]=data_list_term (map Payload_Term [r,a,b])"
    and root: "data_list_term [h 8]=data_list_term (map Payload_Term [m])"
    by (simp_all add: rec)
  have separation1: "set [r,a,b]\<inter>set Is={}"
    using calls(5) by (simp only: outer interface(1) payload_disjoint_lists)
  have separation2: "set [r,a,b]\<inter>{m}={}"
    using calls(6) by (simp only: outer root payload_disjoint_lists) auto
  have separation3: "m\<notin>set Is"
    using calls(7) by (simp only: root interface(1) payload_disjoint_lists) auto
  have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  have raw: "native_definition_at E u r p C"
    unfolding native_definition_at_def
    by (intro conjI, rule ef, rule exI[of _ R], rule exI[of _ "[a,b]"], rule exI[of _ i], rule exI[of _ m],
      rule exI[of _ "set Is"], rule exI[of _ "set Ks"])
      (use source(3) rec(6) interface(3) family separation1 separation2 separation3 in auto)
  have accepts: "pattern_accepts p (h 3)"
    using interface(4,5) pattern_instance_formed_term[OF interface(4,5)] by (auto simp: pattern_accepts_def)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ p],
      rule exI[of _ C], rule exI[of _ "h 3"])
      (use source rec raw accepts conclusion in \<open>simp add: schema definition_call_admission_schema_def\<close>)
qed

theorem definition_call_admission_complete:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
    and accepts: "pattern_accepts p t"
  shows "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
    \<in>positive_meaning definition_call_admission_system"
proof -
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    "insert r (set ps)\<inter>(I\<union>{m})={}" "m\<notin>I"
    using raw by (auto simp: native_definition_at_def)
  obtain B where bindings: "term_bindings_formed (pattern_variables p) B" "pattern_instance B p t"
    using accepts by (auto simp: pattern_accepts_def)
  have bf: "finite B" using bindings(1) by (simp add: term_bindings_formed_def)
  obtain xs where xs: "set xs=B" "distinct xs" using finite_distinct_list[OF bf] by blast
  have table: "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p t"
    using bindings xs(1) by simp_all
  obtain Is where Is: "set Is=I" "distinct Is"
    using finite_distinct_list[of I] scoped_pattern_formed[OF parts(3)] by blast
  obtain Ks where Ks: "set Ks=K" "distinct Ks"
    using finite_distinct_list[of K] scoped_pattern_formed[OF parts(3)] by blast
  have interface: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i)
      (binding_rows_term xs) t (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
    by (rule scoped_instantiation_complete[OF parts(3) source table(1) xs(2) Is(2) Ks(2) Is(1) Ks(1) table(2)])
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain material where presented: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  obtain a b where ports: "ps=[a,b]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  have ports_distinct: "distinct [r,a,b]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: ports)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term a) (Payload_Term i),Pair_Term (Payload_Term b) (Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF presented]) (use parts(2) in \<open>auto simp: ports\<close>)
  have family: "(71,source_root_argument e (use_data_term u) (Payload_Term m))\<in>positive_meaning schema_family_admission_system"
    by (rule schema_family_admission_complete[OF source parts(4)])
  have operands: "octets_formed r" "octets_formed a" "octets_formed b" "octets_formed m"
    "\<forall>x\<in>set Is. octets_formed x"
    using schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF interface]] by (auto simp: data_list_term_formed)
  have outer: "data_list_term [Payload_Term r,Payload_Term a,Payload_Term b]=data_list_term (map Payload_Term [r,a,b])"
    and root: "data_list_term [Payload_Term m]=data_list_term (map Payload_Term [m])" by simp_all
  have outer_interface: "(49,Pair_Term (data_list_term [Payload_Term r,Payload_Term a,Payload_Term b])
      (data_list_term (map Payload_Term Is)))\<in>positive_meaning payload_disjoint_system"
    by (simp only: outer payload_disjoint_lists) (use ports_distinct Is parts(5) operands in \<open>auto simp: ports\<close>)
  have outer_family: "(49,Pair_Term (data_list_term [Payload_Term r,Payload_Term a,Payload_Term b])
      (data_list_term [Payload_Term m]))\<in>positive_meaning payload_disjoint_system"
    by (simp only: outer root payload_disjoint_lists) (use ports_distinct parts(5) operands in \<open>auto simp: ports\<close>)
  have family_interface: "(49,Pair_Term (data_list_term [Payload_Term m])
      (data_list_term (map Payload_Term Is)))\<in>positive_meaning payload_disjoint_system"
    by (simp only: root payload_disjoint_lists) (use Is parts(6) operands in auto)
  show ?thesis
    by (rule definition_call_admission_step[OF lookup rec interface family outer_interface outer_family family_interface])
qed

theorem definition_call_admission_exact:
  "(72,z)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> definition_call_admission_result z"
  using definition_call_admission_sound definition_call_admission_complete by blast

corollary definition_call_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(72,citation_observation_argument e u r t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    (\<exists>v a p C. u=use_data_term v \<and> r=Payload_Term a \<and> native_definition_at E v a p C \<and> pattern_accepts p t)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: definition_call_admission_exact factor_term.inject) (use source unique in blast)
qed

corollary definition_call_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
      \<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    (\<exists>p C. native_definition_at E u r p C \<and> pattern_accepts p t)"
  by (simp only: definition_call_admission_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary definition_call_admission_at_definition:
  assumes source: "environment_value_presents E e" and raw: "native_definition_at E u r p C"
  shows "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
    \<in>positive_meaning definition_call_admission_system \<longleftrightarrow> pattern_accepts p t"
proof -
  have unique: "q=p \<and> D=C" if "native_definition_at E u r q D" for q D
    by (rule native_definition_unique[OF that raw])
  show ?thesis by (simp only: definition_call_admission_on_values[OF source]) (use raw unique in blast)
qed

corollary definition_call_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(72,citation_observation_argument e u r t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    (72,citation_observation_argument f u r t)\<in>positive_meaning definition_call_admission_system"
  by (simp only: definition_call_admission_at_source[OF assms(1)] definition_call_admission_at_source[OF assms(2)])

theorem definition_call_admission_inhabited:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>t. (72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
      \<in>positive_meaning definition_call_admission_system) \<longleftrightarrow>
    (\<exists>p C. native_definition_at E u r p C)"
proof
  assume "\<exists>t. (72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
    \<in>positive_meaning definition_call_admission_system"
  then show "\<exists>p C. native_definition_at E u r p C"
    by (simp only: definition_call_admission_on_values[OF source]) blast
next
  assume "\<exists>p C. native_definition_at E u r p C"
  then obtain p C where raw: "native_definition_at E u r p C" by blast
  have pf: "pattern_formed p" using native_definition_formed[OF raw] by blast
  obtain t where accepts: "pattern_accepts p t" using pattern_accepts_total[OF pf] by blast
  show "\<exists>t. (72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
    \<in>positive_meaning definition_call_admission_system"
    using definition_call_admission_complete[OF source raw accepts] by blast
qed

theorem definition_call_admission_in_program:
  assumes source: "environment_value_presents E e" and package: "native_package_formed E roots"
    and site: "(u,r)\<in>native_definition_sites E roots"
  shows "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) t)
      \<in>positive_meaning definition_call_admission_system \<longleftrightarrow>
    schema_call_formed (native_program E roots) (u,r) t"
proof -
  obtain p C where raw: "native_definition_at E u r p C"
    using package site by (auto simp: native_package_formed_def)
  have selected: "native_definition_at E (fst (u,r)) (snd (u,r)) p C" using raw by simp
  have interface: "((u,r),q)\<in>system_interfaces (native_program E roots) \<longleftrightarrow> q=p" for q
    by (rule native_program_complete_at(1)[OF site selected])
  show ?thesis
    by (simp only: definition_call_admission_at_definition[OF source raw] schema_call_formed_def
      native_program_formed[OF package] interface) blast
qed

section \<open>Four fixed native entries precede future source material\<close>

lemma definition_admission_components:
  "(69,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (69,t)\<in>positive_meaning schema_admission_system"
  "(70,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (70,t)\<in>positive_meaning schema_root_list_system"
  "(71,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> (71,t)\<in>positive_meaning schema_family_admission_system"
  using definition_call_admission_old_meaning[of 69 t] schema_family_admission_previous_meaning[of 69 t]
    definition_call_admission_old_meaning[of 70 t] schema_family_admission_components(4)[of t]
    definition_call_admission_old_meaning[of 71 t] by auto

abbreviation definition_admission_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "definition_admission_operation_result d t \<equiv>
    (d=69 \<and> schema_admission_result t) \<or> (d=70 \<and> schema_root_list_result t) \<or>
    (d=71 \<and> schema_family_admission_result t) \<or> (d=72 \<and> definition_call_admission_result t)"

lemma definition_admission_operations_exact:
  assumes "d\<in>{69,70,71,72}"
  shows "(d,t)\<in>positive_meaning definition_call_admission_system \<longleftrightarrow> definition_admission_operation_result d t"
proof -
  consider "d=69" | "d=70" | "d=71" | "d=72" using assms by auto
  then show ?thesis
    by cases (simp_all add: definition_admission_components schema_admission_exact schema_root_list_exact
      schema_family_admission_exact definition_call_admission_exact)
qed

theorem native_definition_admission_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {69::nat,70,71,72} \<and>
    (\<forall>d\<in>{69,70,71,72}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> definition_admission_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions definition_call_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions definition_call_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed definition_call_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning definition_call_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF definition_call_admission_system_formed] by blast
  have sites: "inj_on g {69,70,71,72}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {69,70,71,72}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{69,70,71,72}" and tf: "term_formed t"
    have member: "d\<in>system_definitions definition_call_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed definition_call_admission_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning definition_call_admission_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> definition_admission_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member definition_admission_operations_exact[OF selected] in \<open>auto simp: definition_call_admission_call\<close>)
  qed
qed

text \<open>
  The definition entry reads the actual two-field record, admits every
  clause, and instantiates the actual scoped interface at the supplied
  operand. Its three separation checks express exactly the existing
  definition grammar. They add no condition on the interface's external
  slots or on different clause interiors.

  Every formed native definition admits an operand, including definitions
  whose complete clause family is empty or whose clauses never hold.
  Within an already formed package and at an actual reached site, this
  entry agrees exactly with that program's call-formation judgment.
  Package formation and its complete callee closure remain separate.

  The four entries have exact contracts over every term and preserve all
  earlier meanings. Every complete environment presentation is permitted.
  One fixed closed native program supplies distinct sites before future
  formed operands and retains its canonical environment. It has seventy-three
  definitions and one hundred and twenty clauses. Native package admission,
  complete admitted instances, finite evidence checking, the full transition
  protocol, reflection, and genesis remain required.
\<close>

end
