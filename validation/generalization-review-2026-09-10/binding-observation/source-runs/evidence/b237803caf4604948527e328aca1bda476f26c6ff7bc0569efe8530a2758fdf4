theory Factor_Admitted_Instantiation
  imports Factor_Program_Call_List
begin

section \<open>A complete instance uses an actual package clause\<close>

abbreviation admitted_instantiation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "admitted_instantiation_argument e u r d c b t q \<equiv>
    package_subject_argument e u r (Pair_Term d (Pair_Term c (Pair_Term b (Pair_Term t q))))"

abbreviation admitted_instantiation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "admitted_instantiation_pattern e u r d c b t q \<equiv>
    package_subject_pattern e u r (Pattern_Pair d (Pattern_Pair c (Pattern_Pair b (Pattern_Pair t q))))"

abbreviation admitted_instantiation_result :: "factor_term \<Rightarrow> bool" where
  "admitted_instantiation_result z \<equiv> \<exists>E e u r d c xs t qs P.
    z=admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs) \<and>
    environment_value_presents E e \<and> distinct xs \<and> distinct qs \<and> native_package_at E u r P \<and>
    admitted_schema_instance P d c (set xs) t (set qs)"

definition admitted_instantiation_schema :: "(nat,nat,nat) factor_schema" where
  "admitted_instantiation_schema=data_rule
    (admitted_instantiation_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8))
    {(0,84,package_subject_pattern data_x data_y data_z
       (Pattern_Pair (Pattern_Pair data_w (Pattern_Variable 4)) (Pattern_Variable 7))),
     (1,81,citation_observation_pattern data_x data_w (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 9))),
     (2,68,schema_instantiation_pattern data_x data_w (Pattern_Variable 9) (Pattern_Variable 6)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 10)),
     (3,59,Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 11)),
     (4,86,package_subject_pattern data_x data_y data_z (Pattern_Variable 11))}"

definition admitted_instantiation_system :: "(nat,nat,nat,nat) schema_system" where
  "admitted_instantiation_system=add_view_definition program_call_list_system 87 data_x {(0,admitted_instantiation_schema)}"

lemma admitted_instantiation_system_formed [simp]: "schema_system_formed admitted_instantiation_system"
  unfolding admitted_instantiation_system_def
  by (rule add_recursive_definition_formed[OF program_call_list_system_formed])
    (auto simp: admitted_instantiation_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma admitted_instantiation_definitions [simp]:
  "system_definitions admitted_instantiation_system=insert 87 (system_definitions program_call_list_system)"
  by (simp add: admitted_instantiation_system_def)

lemma admitted_instantiation_call:
  "schema_call_formed admitted_instantiation_system d t \<longleftrightarrow>
    d\<in>system_definitions admitted_instantiation_system \<and> term_formed t"
  using added_variable_calls[OF program_call_list_system_formed
    admitted_instantiation_system_formed[unfolded admitted_instantiation_system_def] program_call_list_call]
  by (simp only: admitted_instantiation_system_def[symmetric])

lemma admitted_instantiation_old_meaning:
  assumes "d\<in>system_definitions program_call_list_system"
  shows "(d,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (d,t)\<in>positive_meaning program_call_list_system"
  using added_definition_preserves_old(2)[OF program_call_list_system_formed
    admitted_instantiation_system_formed[unfolded admitted_instantiation_system_def], of d t] assms
  by (auto simp: admitted_instantiation_system_def)

lemma admitted_instantiation_clause [simp]:
  "((87,c),S)\<in>system_clauses admitted_instantiation_system \<longleftrightarrow> (c,S)\<in>{(0,admitted_instantiation_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses program_call_list_system \<Longrightarrow>
    d\<in>system_definitions program_call_list_system" for d c S
    using program_call_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((87,c),S)\<notin>system_clauses program_call_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: admitted_instantiation_system_def)
qed

lemma admitted_instantiation_previous_meaning:
  assumes "d\<in>system_definitions package_admission_system"
  shows "(d,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_admission_system"
  using admitted_instantiation_old_meaning[of d t] program_call_list_previous_meaning[OF assms, of t] assms by auto

lemma admitted_instantiation_components:
  "(84,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (84,t)\<in>positive_meaning program_call_admission_system"
  "(81,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (81,t)\<in>positive_meaning definition_clause_reading_system"
  "(68,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (68,t)\<in>positive_meaning schema_material_checking_system"
  "(59,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(86,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (86,t)\<in>positive_meaning program_call_list_system"
  using admitted_instantiation_old_meaning[of 84 t] program_call_list_element[of t]
    admitted_instantiation_old_meaning[of 81 t] program_call_list_old_meaning[of 81 t]
    application_admission_old_meaning[of 81 t] program_call_admission_old_meaning[of 81 t]
    package_membership_old_meaning[of 81 t] definition_edge_reading_old_meaning[of 81 t]
    admitted_instantiation_previous_meaning[of 68 t] package_admission_previous_meaning[of 68 t]
    package_closure_previous_meaning[of 68 t] definition_call_admission_old_meaning[of 68 t]
    schema_family_admission_previous_meaning[of 68 t] schema_admission_old_meaning[of 68 t]
    admitted_instantiation_previous_meaning[of 59 t] package_admission_old_meaning[of 59 t]
    root_family_reading_components(3)[of t] admitted_instantiation_old_meaning[of 86 t] by auto

lemma admitted_instantiation_step:
  assumes head: "(84,package_subject_argument e pu pr (Pair_Term (Pair_Term u r) t))\<in>positive_meaning program_call_admission_system"
    and clause: "(81,citation_observation_argument e u r (Pair_Term c a))\<in>positive_meaning definition_clause_reading_system"
    and inst: "(68,schema_instantiation_argument e u a b t q m)\<in>positive_meaning schema_material_checking_system"
    and projection: "(59,Pair_Term q v)\<in>positive_meaning row_values_system"
    and calls: "(86,package_subject_argument e pu pr v)\<in>positive_meaning program_call_list_system"
  shows "(87,admitted_instantiation_argument e pu pr (Pair_Term u r) c b t q)\<in>positive_meaning admitted_instantiation_system"
proof -
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed u" "term_formed r" "term_formed c"
    "term_formed b" "term_formed t" "term_formed q" "term_formed a" "term_formed m" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF head]]
      schema_call_formed_target[OF positive_meaning_formed[OF clause]]
      schema_call_formed_target[OF positive_meaning_formed[OF inst]]
      schema_call_formed_target[OF positive_meaning_formed[OF projection]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then pu else if n=2 then pr else if n=3 then u
    else if n=4 then r else if n=5 then c else if n=6 then b else if n=7 then t
    else if n=8 then q else if n=9 then a else if n=10 then m else v"
  have result: "(87,evaluate_pattern ?h (schema_conclusion admitted_instantiation_schema))\<in>positive_meaning admitted_instantiation_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: admitted_instantiation_schema_def schema_variables_def
        admitted_instantiation_call admitted_instantiation_components\<close>)
  show ?thesis using result by (simp add: admitted_instantiation_schema_def)
qed

theorem admitted_instantiation_sound:
  assumes holds: "(87,z)\<in>positive_meaning admitted_instantiation_system"
  shows "admitted_instantiation_result z"
proof -
  have consequence: "(87,z)\<in>schema_consequences admitted_instantiation_system (positive_meaning admitted_instantiation_system)"
    using holds positive_meaning_unfold[of admitted_instantiation_system] by blast
  obtain n S h where clause: "((87,n),S)\<in>system_clauses admitted_instantiation_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning admitted_instantiation_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=admitted_instantiation_schema" using clause by simp
  have calls: "(84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (Pair_Term (h 3) (h 4)) (h 7)))
      \<in>positive_meaning program_call_admission_system"
    "(81,citation_observation_argument (h 0) (h 3) (h 4) (Pair_Term (h 5) (h 9)))\<in>positive_meaning definition_clause_reading_system"
    "(68,schema_instantiation_argument (h 0) (h 3) (h 9) (h 6) (h 7) (h 8) (h 10))\<in>positive_meaning schema_material_checking_system"
    "(59,Pair_Term (h 8) (h 11))\<in>positive_meaning row_values_system"
    "(86,package_subject_argument (h 0) (h 1) (h 2) (h 11))\<in>positive_meaning program_call_list_system"
    using support by (auto simp: schema admitted_instantiation_schema_def admitted_instantiation_components)
  obtain E u r c a where source: "environment_value_presents E (h 0)" "h 3=use_data_term u" "h 4=Payload_Term r"
    "h 5=Payload_Term c" "h 9=Payload_Term a"
    using calls(2) by (simp only: definition_clause_reading_exact factor_term.inject) blast
  have head: "(84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (definition_site_value (u,r)) (h 7)))
      \<in>positive_meaning program_call_admission_system"
    using calls(1) by (simp add: source(2,3) site_data_term_def)
  obtain pu pr P where package: "h 1=use_data_term pu" "h 2=Payload_Term pr" "native_package_at E pu pr P"
    "schema_call_formed P (u,r) (h 7)"
    using head by (simp only: program_call_admission_at_source[OF source(1)] definition_site_value_eq) blast
  have raw_instance: "(65,schema_instantiation_argument (h 0) (h 3) (h 9) (h 6) (h 7) (h 8) (h 10))
      \<in>positive_meaning schema_instantiation_system"
    using calls(3) by (simp only: schema_material_checking_fields)
  obtain xs T qs cs where fields: "h 6=binding_rows_term xs" "h 8=call_instance_rows_term qs" "h 10=binding_rows_term cs"
    "native_schema_at E u a T"
    using raw_instance by (simp only: source(2,5) schema_instantiation_at_source[OF source(1)]
      inj_eq[OF use_data_term_injective] factor_term.inject) blast
  have checked: "distinct xs" "distinct qs" "schema_instance T (set xs) (h 7) (set qs)" "schema_material_satisfied T (set xs)"
    using calls(3) by (auto simp only: source(2,5) fields(1-3) schema_material_checking_at_schema[OF source(1) fields(4)])
  have actual: "(81,citation_observation_argument (h 0) (use_data_term u) (Payload_Term r)
      (Pair_Term (Payload_Term c) (Payload_Term a)))\<in>positive_meaning definition_clause_reading_system"
    using calls(2) by (simp only: source)
  obtain pat C where defn: "native_definition_at E u r pat C" "(c,T)\<in>C"
    using definition_clause_reading_recovers[OF source(1) actual fields(4)] by blast
  have reached: "(u,r)\<in>native_definition_sites E (native_package_roots E pu pr)"
    using schema_call_formed_target[OF package(4)] native_package_projection(3)[OF package(3)]
    by (simp add: native_package_sites_def)
  have raw_definition: "native_definition_at E (fst (u,r)) (snd (u,r)) pat C" using defn(1) by simp
  have program_clause: "(((u,r),c),T)\<in>system_clauses P"
    using native_program_complete_at(2)[OF reached raw_definition, of c T] defn(2)
      native_package_projection(2)[OF package(3)] by simp
  have projection: "h 11=pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
    using calls(4) by (simp only: fields(2) call_instance_row_values)
  have children: "\<forall>s d t. (s,d,t)\<in>set qs \<longrightarrow> schema_call_formed P d t"
    using calls(5) by (simp only: package(1,2) projection program_call_list_at_calls[OF source(1) package(3)])
  have admitted: "admitted_schema_instance P (u,r) c (set xs) (h 7) (set qs)"
    using package(4) program_clause checked(3,4) children by (auto simp: admitted_schema_instance_def)
  show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ pu], rule exI[of _ pr],
    rule exI[of _ "(u,r)"], rule exI[of _ c], rule exI[of _ xs], rule exI[of _ "h 7"], rule exI[of _ qs], rule exI[of _ P])
    (use source package fields checked admitted conclusion in \<open>simp add: schema admitted_instantiation_schema_def site_data_term_def\<close>)
qed

theorem admitted_instantiation_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and order: "distinct xs" "distinct qs" and inst: "admitted_schema_instance P d c (set xs) t (set qs)"
  shows "(87,admitted_instantiation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
    (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system"
proof -
  obtain u r where site: "d=(u,r)" by (cases d)
  obtain S where parts: "schema_call_formed P (u,r) t" "(((u,r),c),S)\<in>system_clauses P"
    "schema_instance S (set xs) t (set qs)" "schema_material_satisfied S (set xs)"
    "\<forall>s f x. (s,f,x)\<in>set qs \<longrightarrow> schema_call_formed P f x"
    using inst by (auto simp: admitted_schema_instance_def site)
  obtain pat C where defn: "native_definition_at E u r pat C" "(c,S)\<in>C"
    using parts(2) native_package_projection(2)[OF package] by (auto simp: native_definition_graph_def)
  obtain a where clause: "(81,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (Payload_Term c) (Payload_Term a)))\<in>positive_meaning definition_clause_reading_system"
    and schema: "native_schema_at E u a S" using definition_clause_reading_total[OF source defn] by blast
  have bindings: "term_bindings_formed (schema_variables S) (set xs)" using parts(3) by (simp add: schema_instance_def)
  obtain cs where materials: "set cs=material_instance_relation (set xs) (schema_material_premises S)" "distinct cs"
    using finite_distinct_list[OF native_schema_material_instance_boundary(1)[OF schema bindings]] by blast
  have material: "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term a) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system"
    by (simp only: schema_material_checking_at_schema[OF source schema]) (use order materials parts(3,4) in blast)
  have head: "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (Pair_Term (use_data_term u) (Payload_Term r)) t))\<in>positive_meaning program_call_admission_system"
    using program_call_admission_complete[OF source package parts(1)] by (simp add: site_data_term_def)
  let ?v="pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
  have qf: "term_formed (call_instance_rows_term qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF material]] by auto
  have projection: "(59,Pair_Term (call_instance_rows_term qs) ?v)\<in>positive_meaning row_values_system"
    by (simp only: call_instance_row_values) (use qf in blast)
  have children: "(86,package_subject_argument e (use_data_term pu) (Payload_Term pr) ?v)\<in>positive_meaning program_call_list_system"
    by (simp only: program_call_list_at_calls[OF source package]) (use parts(5) in blast)
  show ?thesis using admitted_instantiation_step[OF head clause material projection children]
    by (simp add: site site_data_term_def)
qed

theorem admitted_instantiation_exact:
  "(87,z)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> admitted_instantiation_result z"
proof
  show "(87,z)\<in>positive_meaning admitted_instantiation_system \<Longrightarrow> admitted_instantiation_result z"
    by (rule admitted_instantiation_sound)
next
  assume "admitted_instantiation_result z"
  then obtain E e u r d c xs t qs P where parts:
    "z=admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs)"
    "environment_value_presents E e" "distinct xs" "distinct qs" "native_package_at E u r P"
    "admitted_schema_instance P d c (set xs) t (set qs)" by auto
  show "(87,z)\<in>positive_meaning admitted_instantiation_system"
    using admitted_instantiation_complete[OF parts(2,5,3,4,6)] by (simp only: parts(1))
qed

corollary admitted_instantiation_at_source:
  assumes source: "environment_value_presents E e"
  shows "(87,admitted_instantiation_argument e u r d c b t q)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow>
    (\<exists>v a f s xs qs P. u=use_data_term v \<and> r=Payload_Term a \<and> d=definition_site_value f \<and> c=Payload_Term s \<and>
      b=binding_rows_term xs \<and> q=call_instance_rows_term qs \<and> distinct xs \<and> distinct qs \<and>
      native_package_at E v a P \<and> admitted_schema_instance P f s (set xs) t (set qs))"
proof
  assume holds: "(87,admitted_instantiation_argument e u r d c b t q)\<in>positive_meaning admitted_instantiation_system"
  obtain F v a f s xs qs P where parts: "environment_value_presents F e" "u=use_data_term v" "r=Payload_Term a"
    "d=definition_site_value f" "c=Payload_Term s" "b=binding_rows_term xs" "q=call_instance_rows_term qs"
    "distinct xs" "distinct qs" "native_package_at F v a P" "admitted_schema_instance P f s (set xs) t (set qs)"
    using holds by (simp only: admitted_instantiation_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>v a f s xs qs P. u=use_data_term v \<and> r=Payload_Term a \<and> d=definition_site_value f \<and> c=Payload_Term s \<and>
    b=binding_rows_term xs \<and> q=call_instance_rows_term qs \<and> distinct xs \<and> distinct qs \<and>
    native_package_at E v a P \<and> admitted_schema_instance P f s (set xs) t (set qs)"
    using parts same by blast
next
  assume "\<exists>v a f s xs qs P. u=use_data_term v \<and> r=Payload_Term a \<and> d=definition_site_value f \<and> c=Payload_Term s \<and>
    b=binding_rows_term xs \<and> q=call_instance_rows_term qs \<and> distinct xs \<and> distinct qs \<and>
    native_package_at E v a P \<and> admitted_schema_instance P f s (set xs) t (set qs)"
  then obtain v a f s xs qs P where parts: "u=use_data_term v" "r=Payload_Term a" "d=definition_site_value f" "c=Payload_Term s"
    "b=binding_rows_term xs" "q=call_instance_rows_term qs" "distinct xs" "distinct qs" "native_package_at E v a P"
    "admitted_schema_instance P f s (set xs) t (set qs)" by blast
  show "(87,admitted_instantiation_argument e u r d c b t q)\<in>positive_meaning admitted_instantiation_system"
    using admitted_instantiation_complete[OF source parts(9,7,8,10)] by (simp only: parts(1-6))
qed

corollary admitted_instantiation_on_values:
  assumes source: "environment_value_presents E e"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> (\<exists>P. native_package_at E u r P \<and> admitted_schema_instance P d c (set xs) t (set qs))"
  by (simp only: admitted_instantiation_at_source[OF source] inj_eq[OF use_data_term_injective]
    definition_site_value_eq factor_term.inject binding_rows_term_injective call_instance_rows_term_injective
    call_instance_rows_map_injective) blast

corollary admitted_instantiation_at_package:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system
    \<longleftrightarrow> distinct xs \<and> distinct qs \<and> admitted_schema_instance P d c (set xs) t (set qs)"
proof -
  have unique: "Q=P" if "native_package_at E u r Q" for Q
    by (rule native_package_unique[OF that package])
  show ?thesis by (simp only: admitted_instantiation_on_values[OF source]) (use package unique in blast)
qed

corollary admitted_instantiation_at_clause:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and clause: "((d,c),S)\<in>system_clauses P"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> schema_call_formed P d t \<and> schema_instance S (set xs) t (set qs) \<and>
    schema_material_satisfied S (set xs) \<and> (\<forall>s f x. (s,f,x)\<in>set qs \<longrightarrow> schema_call_formed P f x)"
proof -
  have functional: "single_valued (system_clauses P)"
    using native_package_system_formed[OF package] by (simp add: schema_system_formed_def)
  have unique: "T=S" if "((d,c),T)\<in>system_clauses P" for T
    by (rule single_valued_outputs[OF functional that clause])
  show ?thesis by (simp only: admitted_instantiation_at_package[OF source package] admitted_schema_instance_def)
    (use clause unique in blast)
qed

corollary admitted_instantiation_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(87,admitted_instantiation_argument e u r d c b t q)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow>
    (87,admitted_instantiation_argument f u r d c b t q)\<in>positive_meaning admitted_instantiation_system"
  by (simp only: admitted_instantiation_at_source[OF assms(1)] admitted_instantiation_at_source[OF assms(2)])

corollary admitted_instantiation_orders:
  assumes source: "environment_value_presents E e" and same: "mset xs=mset ys" "mset qs=mset rs"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow>
    (87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term ys) t (call_instance_rows_term rs))\<in>positive_meaning admitted_instantiation_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)]
  by (simp only: admitted_instantiation_on_values[OF source])

corollary admitted_instantiation_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system"
    and second: "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) v (call_instance_rows_term rs))\<in>positive_meaning admitted_instantiation_system"
  shows "t=v \<and> mset qs=mset rs"
proof -
  obtain P where left: "native_package_at E u r P" "admitted_schema_instance P d c (set xs) t (set qs)" "distinct qs"
    using first by (simp only: admitted_instantiation_on_values[OF source]) blast
  have right: "admitted_schema_instance P d c (set xs) v (set rs)" "distinct rs"
    using second by (auto simp only: admitted_instantiation_at_package[OF source left(1)])
  have same: "t=v \<and> set qs=set rs" by (rule admitted_instance_unique[OF left(2) right(1)])
  show ?thesis using same left(3) right(2) distinct_source_mset[of qs rs] by auto
qed

corollary admitted_instantiation_rejects_changed_sockets:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and clause: "((d,c),S)\<in>system_clauses P" and changed: "rel_dom (set qs)\<noteq>rel_dom (schema_premises S)"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<notin>positive_meaning admitted_instantiation_system"
  by (simp only: admitted_instantiation_at_clause[OF source package clause])
    (use changed schema_instance_socket_boundary in blast)

corollary admitted_instantiation_rejects_unsatisfied_material:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and clause: "((d,c),S)\<in>system_clauses P" and missing: "\<not>schema_material_satisfied S (set xs)"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<notin>positive_meaning admitted_instantiation_system"
  by (simp only: admitted_instantiation_at_clause[OF source package clause]) (use missing in blast)

corollary admitted_instantiation_rejects_unformed_callee:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and member: "(s,f,x)\<in>set qs" and missing: "\<not>schema_call_formed P f x"
  shows "(87,admitted_instantiation_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      (Payload_Term c) (binding_rows_term xs) t (call_instance_rows_term qs))\<notin>positive_meaning admitted_instantiation_system"
proof -
  obtain v a where site: "f=(v,a)" by (cases f)
  show ?thesis by (simp only: admitted_instantiation_at_package[OF source package])
    (use member missing in \<open>auto simp: admitted_schema_instance_def site\<close>)
qed

section \<open>Seven fixed native entries precede all future operands\<close>

lemma call_admission_operation_components:
  "(81,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (81,t)\<in>positive_meaning definition_clause_reading_system"
  "(82,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(83,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(84,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (84,t)\<in>positive_meaning program_call_admission_system"
  "(85,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (85,t)\<in>positive_meaning application_admission_system"
  "(86,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> (86,t)\<in>positive_meaning program_call_list_system"
  using admitted_instantiation_components(2)[of t]
    admitted_instantiation_old_meaning[of 82 t] program_call_list_old_meaning[of 82 t]
    application_admission_old_meaning[of 82 t] program_call_admission_old_meaning[of 82 t] package_membership_old_meaning[of 82 t]
    admitted_instantiation_old_meaning[of 83 t] program_call_list_old_meaning[of 83 t]
    application_admission_old_meaning[of 83 t] program_call_admission_old_meaning[of 83 t]
    admitted_instantiation_components(1)[of t] admitted_instantiation_old_meaning[of 85 t]
    program_call_list_old_meaning[of 85 t] admitted_instantiation_old_meaning[of 86 t] by auto

abbreviation call_admission_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "call_admission_operation_result d t \<equiv>
    (d=81 \<and> definition_clause_reading_result t) \<or> (d=82 \<and> definition_edge_reading_result t) \<or>
    (d=83 \<and> package_membership_result t) \<or> (d=84 \<and> program_call_admission_result t) \<or>
    (d=85 \<and> application_admission_result t) \<or> (d=86 \<and> program_call_list_result t) \<or>
    (d=87 \<and> admitted_instantiation_result t)"

lemma call_admission_operations_exact:
  assumes "d\<in>{81,82,83,84,85,86,87}"
  shows "(d,t)\<in>positive_meaning admitted_instantiation_system \<longleftrightarrow> call_admission_operation_result d t"
proof -
  consider "d=81" | "d=82" | "d=83" | "d=84" | "d=85" | "d=86" | "d=87" using assms by auto
  then show ?thesis by cases
    (simp_all add: call_admission_operation_components definition_clause_reading_exact definition_edge_reading_exact
      package_membership_exact program_call_admission_exact application_admission_exact program_call_list_exact admitted_instantiation_exact)
qed

theorem native_call_admission_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {81::nat,82,83,84,85,86,87} \<and>
    (\<forall>d\<in>{81,82,83,84,85,86,87}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> call_admission_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions admitted_instantiation_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions admitted_instantiation_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed admitted_instantiation_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning admitted_instantiation_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF admitted_instantiation_system_formed] by blast
  have sites: "inj_on g {81,82,83,84,85,86,87}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {81,82,83,84,85,86,87}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{81,82,83,84,85,86,87}" and tf: "term_formed t"
    have member: "d\<in>system_definitions admitted_instantiation_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed admitted_instantiation_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning admitted_instantiation_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> call_admission_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member call_admission_operations_exact[OF selected] in \<open>auto simp: admitted_instantiation_call\<close>)
  qed
qed

text \<open>
  The complete instance is tied to an actual clause socket of a reached
  definition in the actual package. One shared substitution instantiates
  its head and every ordinary and material premise. Every material row is
  checked before its complete list is hidden. The head and all prospective
  calls satisfy the same package's actual interfaces.

  This is exactly admitted_schema_instance, with complete distinct binding
  and call-row presentations. Every such presentation is admitted whenever
  that raw relation holds. It does not assert unconditional existence for
  a clause whose interfaces or material conditions prevent an instance.
  Given the bindings, admitted results are unique up to row enumeration.
  Missing or extra call sockets, unsatisfied material conditions, and
  unformed prospective calls cannot be omitted from the check.

  All seven entries have exact contracts over every term and preserve earlier
  meanings. Source presentation order does not change their answers. The
  instantiated operands may include any formed literal targets. One fixed
  closed native program has seven distinct sites before all future formed
  operands and retains its canonical environment. It has eighty-eight
  definitions and one hundred and forty clauses. Finite correctness evidence
  checking, the full transition protocol, reflection, and genesis remain
  required.
\<close>

end
