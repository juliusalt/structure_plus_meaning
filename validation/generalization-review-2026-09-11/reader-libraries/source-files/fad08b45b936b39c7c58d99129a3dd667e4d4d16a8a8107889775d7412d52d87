theory Factor_Premise_Family_Instantiation
  imports Factor_Premise_Row_Instantiation
begin

section \<open>The actual complete family and its two instantiated projections\<close>

abbreviation premise_family_instantiation_result :: "factor_term \<Rightarrow> bool" where
  "premise_family_instantiation_result z \<equiv> \<exists>E e u Vs xs r A C qs cs Us.
    z=premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)) \<and>
    environment_value_presents E e \<and> distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and>
    term_bindings_formed (set Vs) (set xs) \<and> distinct qs \<and> distinct cs \<and> distinct Us \<and>
    native_premise_family_at E u (set Vs) r A C \<and>
    set qs=call_instance_relation (set xs) A \<and> set cs=material_instance_relation (set xs) C \<and>
    set Us=premise_family_variables A C"

definition premise_family_instantiation_schema :: "(nat,nat,nat) factor_schema" where
  "premise_family_instantiation_schema=data_rule
    (premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4)
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 8)),
     (1,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4)) (Pattern_Variable 9)),
     (2,63,premise_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 9)
       (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))}"

definition premise_family_instantiation_system :: "(nat,nat,nat,nat) schema_system" where
  "premise_family_instantiation_system=add_view_definition premise_rows_system 64 data_x {(0,premise_family_instantiation_schema)}"

lemma premise_family_instantiation_system_formed [simp]: "schema_system_formed premise_family_instantiation_system"
  unfolding premise_family_instantiation_system_def
  by (rule add_recursive_definition_formed[OF premise_rows_system_formed])
    (auto simp: premise_family_instantiation_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma premise_family_instantiation_definitions [simp]:
  "system_definitions premise_family_instantiation_system=insert 64 (system_definitions premise_rows_system)"
  by (simp add: premise_family_instantiation_system_def)

lemma premise_family_instantiation_call:
  "schema_call_formed premise_family_instantiation_system d t \<longleftrightarrow>
    d\<in>system_definitions premise_family_instantiation_system \<and> term_formed t"
  using added_variable_calls[OF premise_rows_system_formed
    premise_family_instantiation_system_formed[unfolded premise_family_instantiation_system_def] premise_rows_call]
  by (simp only: premise_family_instantiation_system_def[symmetric])

lemma premise_family_instantiation_old_meaning:
  assumes "d\<in>system_definitions premise_rows_system"
  shows "(d,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> (d,t)\<in>positive_meaning premise_rows_system"
  using added_definition_preserves_old(2)[OF premise_rows_system_formed
    premise_family_instantiation_system_formed[unfolded premise_family_instantiation_system_def], of d t] assms
  by (auto simp: premise_family_instantiation_system_def)

lemma premise_family_instantiation_clause [simp]:
  "((64,c),S)\<in>system_clauses premise_family_instantiation_system \<longleftrightarrow> (c,S)\<in>{(0,premise_family_instantiation_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses premise_rows_system \<Longrightarrow> d\<in>system_definitions premise_rows_system" for d c S
    using premise_rows_system_formed unfolding schema_system_formed_def by blast
  have absent: "((64,c),S)\<notin>system_clauses premise_rows_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: premise_family_instantiation_system_def)
qed

lemma premise_family_instantiation_components:
  "(37,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(32,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(63,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> (63,t)\<in>positive_meaning premise_rows_system"
  using premise_family_instantiation_old_meaning[of 37 t] premise_rows_vector_meaning[of 37 t]
    vector_instantiation_pattern_meaning[of 37 t] pattern_instantiation_components(6)[of t]
    premise_family_instantiation_old_meaning[of 32 t] premise_rows_vector_meaning[of 32 t]
    vector_instantiation_pattern_meaning[of 32 t] pattern_instantiation_old_meaning[of 32 t]
    binder_admission_components(2)[of t] premise_family_instantiation_old_meaning[of 63 t] by auto

lemma premise_family_instantiation_step:
  assumes source: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and family: "(32,rooted_rows_argument a r rows)\<in>positive_meaning family_admission_system"
    and body: "(63,premise_instantiation_argument e u v b rows q c w)\<in>positive_meaning premise_rows_system"
  shows "(64,premise_instantiation_argument e u v b r q c w)\<in>positive_meaning premise_family_instantiation_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed v" "term_formed b" "term_formed r"
    "term_formed q" "term_formed c" "term_formed w" "term_formed a" "term_formed rows"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF family]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then v else if n=3 then b
    else if n=4 then r else if n=5 then q else if n=6 then c else if n=7 then w else if n=8 then a else rows"
  have result: "(64,evaluate_pattern ?h (schema_conclusion premise_family_instantiation_schema))\<in>positive_meaning premise_family_instantiation_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: premise_family_instantiation_schema_def schema_variables_def
        premise_family_instantiation_call premise_family_instantiation_components\<close>)
  show ?thesis using result by (simp add: premise_family_instantiation_schema_def)
qed

theorem premise_family_instantiation_sound:
  assumes holds: "(64,z)\<in>positive_meaning premise_family_instantiation_system"
  shows "premise_family_instantiation_result z"
proof -
  have consequence: "(64,z)\<in>schema_consequences premise_family_instantiation_system (positive_meaning premise_family_instantiation_system)"
    using holds positive_meaning_unfold[of premise_family_instantiation_system] by blast
  obtain n S h where clause: "((64,n),S)\<in>system_clauses premise_family_instantiation_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning premise_family_instantiation_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=premise_family_instantiation_schema" using clause by simp
  have calls:
    "(37,artifact_lookup_argument (h 0) (h 1) (h 8))\<in>positive_meaning artifact_lookup_system"
    "(32,rooted_rows_argument (h 8) (h 4) (h 9))\<in>positive_meaning family_admission_system"
    "(63,premise_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 9) (h 5) (h 6) (h 7))\<in>positive_meaning premise_rows_system"
    using support by (auto simp: schema premise_family_instantiation_schema_def premise_family_instantiation_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 8)"
    using calls(1) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r rs where family: "h 4=Payload_Term r" "h 9=data_list_term (map address_pair_data rs)"
    "distinct rs" "family_at R r (set rs)"
    using calls(2) by (simp only: family_admission_at_source[OF source(4)]) blast
  obtain Vs xs qs cs Us where parts: "h 2=data_list_term (map Payload_Term Vs)" "h 3=binding_rows_term xs"
    "h 5=call_instance_rows_term qs" "h 6=binding_rows_term cs" "h 7=data_list_term (map Payload_Term Us)"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    "distinct Us" "instantiated_premise_rows E u (set Vs) (set xs) rs qs cs (set Us)"
    using calls(3)
    by (simp only: premise_rows_exact premise_rows_result_at_source[OF source(1)] source(2) family(2)
        inj_eq[OF use_data_term_injective] data_list_term_injective injective_mapped_lists[OF address_pair_data_injective])
      blast
  have environment: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  have single: "single_valued (set xs)" using parts(9) by (simp add: term_bindings_formed_def)
  obtain A C where native: "native_premise_family_at E u (set Vs) r A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    "set Us=premise_family_variables A C"
    using instantiated_premise_rows_family[OF environment source(3) family(4,3) single parts(11)] by blast
  have keys: "distinct (map fst rs)" using family(3,4) by (simp add: distinct_keys_iff family_at_def)
  have order: "distinct qs" "distinct cs" using instantiated_premise_rows_distinct[OF parts(11) keys] by auto
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ Vs], rule exI[of _ xs], rule exI[of _ r], rule exI[of _ A], rule exI[of _ C], rule exI[of _ qs], rule exI[of _ cs], rule exI[of _ Us])
      (use conclusion source family parts native order in \<open>simp add: schema premise_family_instantiation_schema_def\<close>)
qed

theorem premise_family_instantiation_complete:
  assumes source: "environment_value_presents E e"
    and table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    and family: "native_premise_family_at E u (set Vs) r A C"
    and calls: "set qs=call_instance_relation (set xs) A" and materials: "set cs=material_instance_relation (set xs) C"
    and order: "distinct qs" "distinct cs" "distinct Us" and used: "set Us=premise_family_variables A C"
  shows "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system"
proof -
  have bindings: "term_bindings_formed (set Vs) (set xs)" using table by (simp only: binding_admission_on_values; blast)
  obtain R rs where rows: "artifact_at E u R" "family_at R r (set rs)" "distinct rs"
    "instantiated_premise_rows E u (set Vs) (set xs) rs qs cs (premise_family_variables A C)"
    using native_family_instantiated_rows[OF family bindings calls materials order(1,2)] by blast
  have environment: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have formed: "exact_formed R" using environment rows(1) by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF formed] by blast
  have keys: "\<forall>s\<in>rel_dom (set rs). octets_formed s"
    using family_interior_in_carrier[OF rows(2)] formed by (auto simp: exact_formed_def)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using rows(1) presented by (simp only: artifact_lookup_at_source[OF source]) blast
  have actual: "(32,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data rs)))\<in>positive_meaning family_admission_system"
    by (simp only: family_admission_rows[OF presented]) (use rows(2,3) in blast)
  have body: "(63,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (data_list_term (map address_pair_data rs)) (call_instance_rows_term qs) (binding_rows_term cs)
      (data_list_term (map Payload_Term Us)))\<in>positive_meaning premise_rows_system"
    by (rule premise_rows_complete[OF source table rows(4) keys order(3) used])
  show ?thesis by (rule premise_family_instantiation_step[OF lookup actual body])
qed

theorem premise_family_instantiation_exact:
  "(64,z)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> premise_family_instantiation_result z"
proof
  show "(64,z)\<in>positive_meaning premise_family_instantiation_system \<Longrightarrow> premise_family_instantiation_result z"
    by (rule premise_family_instantiation_sound)
next
  assume "premise_family_instantiation_result z"
  then obtain E e u Vs xs r A C qs cs Us where parts:
    "z=premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us))"
    "environment_value_presents E e" "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a"
    "term_bindings_formed (set Vs) (set xs)" "distinct qs" "distinct cs" "distinct Us"
    "native_premise_family_at E u (set Vs) r A C" "set qs=call_instance_relation (set xs) A"
    "set cs=material_instance_relation (set xs) C" "set Us=premise_family_variables A C" by blast
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use parts(3-6) in blast)
  show "(64,z)\<in>positive_meaning premise_family_instantiation_system"
    using premise_family_instantiation_complete[OF parts(2) table parts(10-12,7-9,13)] parts(1) by simp
qed

corollary premise_family_instantiation_at_source:
  assumes source: "environment_value_presents E e"
  shows "(64,premise_instantiation_argument e u v b r q c w)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow>
    (\<exists>a Vs xs l A C qs cs Us. u=use_data_term a \<and> v=data_list_term (map Payload_Term Vs) \<and> b=binding_rows_term xs \<and>
      r=Payload_Term l \<and> q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> w=data_list_term (map Payload_Term Us) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct qs \<and> distinct cs \<and> distinct Us \<and> native_premise_family_at E a (set Vs) l A C \<and>
      set qs=call_instance_relation (set xs) A \<and> set cs=material_instance_relation (set xs) C \<and>
      set Us=premise_family_variables A C)"
proof
  assume holds: "(64,premise_instantiation_argument e u v b r q c w)\<in>positive_meaning premise_family_instantiation_system"
  obtain F a Vs xs l A C qs cs Us where parts: "environment_value_presents F e"
    "u=use_data_term a" "v=data_list_term (map Payload_Term Vs)" "b=binding_rows_term xs" "r=Payload_Term l"
    "q=call_instance_rows_term qs" "c=binding_rows_term cs" "w=data_list_term (map Payload_Term Us)"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    "distinct qs" "distinct cs" "distinct Us" "native_premise_family_at F a (set Vs) l A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    "set Us=premise_family_variables A C"
    using holds by (simp only: premise_family_instantiation_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>a Vs xs l A C qs cs Us. u=use_data_term a \<and> v=data_list_term (map Payload_Term Vs) \<and> b=binding_rows_term xs \<and>
      r=Payload_Term l \<and> q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> w=data_list_term (map Payload_Term Us) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct qs \<and> distinct cs \<and> distinct Us \<and> native_premise_family_at E a (set Vs) l A C \<and>
      set qs=call_instance_relation (set xs) A \<and> set cs=material_instance_relation (set xs) C \<and>
      set Us=premise_family_variables A C"
    by (rule exI[of _ a], rule exI[of _ Vs], rule exI[of _ xs], rule exI[of _ l], rule exI[of _ A], rule exI[of _ C], rule exI[of _ qs], rule exI[of _ cs], rule exI[of _ Us]) (use parts same in auto)
next
  assume "\<exists>a Vs xs l A C qs cs Us. u=use_data_term a \<and> v=data_list_term (map Payload_Term Vs) \<and> b=binding_rows_term xs \<and>
      r=Payload_Term l \<and> q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> w=data_list_term (map Payload_Term Us) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct qs \<and> distinct cs \<and> distinct Us \<and> native_premise_family_at E a (set Vs) l A C \<and>
      set qs=call_instance_relation (set xs) A \<and> set cs=material_instance_relation (set xs) C \<and>
      set Us=premise_family_variables A C"
  then obtain a Vs xs l A C qs cs Us where parts:
    "u=use_data_term a" "v=data_list_term (map Payload_Term Vs)" "b=binding_rows_term xs" "r=Payload_Term l"
    "q=call_instance_rows_term qs" "c=binding_rows_term cs" "w=data_list_term (map Payload_Term Us)"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    "distinct qs" "distinct cs" "distinct Us" "native_premise_family_at E a (set Vs) l A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    "set Us=premise_family_variables A C" by blast
  show "(64,premise_instantiation_argument e u v b r q c w)\<in>positive_meaning premise_family_instantiation_system"
    by (simp only: premise_family_instantiation_exact, rule exI[of _ E], rule exI[of _ e], rule exI[of _ a], rule exI[of _ Vs], rule exI[of _ xs], rule exI[of _ l], rule exI[of _ A], rule exI[of _ C], rule exI[of _ qs], rule exI[of _ cs], rule exI[of _ Us]) (use parts source in auto)
qed

corollary premise_family_instantiation_on_values:
  assumes source: "environment_value_presents E e"
  shows "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow>
    distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
    distinct qs \<and> distinct cs \<and> distinct Us \<and>
    (\<exists>A C. native_premise_family_at E u (set Vs) r A C \<and>
      set qs=call_instance_relation (set xs) A \<and> set cs=material_instance_relation (set xs) C \<and>
      set Us=premise_family_variables A C)"
  by (subst premise_family_instantiation_at_source[OF source],
    simp only: binding_rows_term_injective call_instance_rows_term_injective call_instance_rows_map_injective
      inj_eq[OF use_data_term_injective] factor_term.inject)
    (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj])

corollary premise_family_instantiation_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(64,premise_instantiation_argument e u v b r q c w)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow>
    (64,premise_instantiation_argument f u v b r q c w)\<in>positive_meaning premise_family_instantiation_system"
  by (simp only: premise_family_instantiation_at_source[OF assms(1)] premise_family_instantiation_at_source[OF assms(2)])

corollary premise_family_instantiation_orders:
  assumes source: "environment_value_presents E e"
    and same: "mset Vs=mset Ws" "mset xs=mset ys" "mset qs=mset qs'" "mset cs=mset cs'" "mset Us=mset Us'"
  shows "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow>
    (64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Ws)) (binding_rows_term ys)
      (Payload_Term r) (call_instance_rows_term qs') (binding_rows_term cs') (data_list_term (map Payload_Term Us')))
      \<in>positive_meaning premise_family_instantiation_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)]
    mset_eq_imp_distinct_iff[OF same(3)] mset_eq_imp_distinct_iff[OF same(4)] mset_eq_imp_distinct_iff[OF same(5)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)] mset_eq_setD[OF same(3)] mset_eq_setD[OF same(4)] mset_eq_setD[OF same(5)]
  by (simp only: premise_family_instantiation_on_values[OF source])

corollary premise_family_instantiation_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system"
    and second: "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs') (binding_rows_term cs') (data_list_term (map Payload_Term Us')))
      \<in>positive_meaning premise_family_instantiation_system"
  shows "mset qs=mset qs' \<and> mset cs=mset cs' \<and> mset Us=mset Us'"
proof -
  obtain A C where left: "distinct qs" "distinct cs" "distinct Us" "native_premise_family_at E u (set Vs) r A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    "set Us=premise_family_variables A C"
    using first by (simp only: premise_family_instantiation_on_values[OF source]) blast
  obtain D F where right: "distinct qs'" "distinct cs'" "distinct Us'" "native_premise_family_at E u (set Vs) r D F"
    "set qs'=call_instance_relation (set xs) D" "set cs'=material_instance_relation (set xs) F"
    "set Us'=premise_family_variables D F"
    using second by (simp only: premise_family_instantiation_on_values[OF source]) blast
  have same: "A=D" "C=F" using native_premise_family_unique[OF left(4) right(4)] by auto
  show ?thesis using left right same distinct_source_mset[OF left(1), of qs']
    distinct_source_mset[OF left(2), of cs'] distinct_source_mset[OF left(3), of Us'] by auto
qed

theorem premise_family_instantiation_socket_boundary:
  assumes source: "environment_value_presents E e" and artifact: "artifact_at E u R" and raw: "family_at R r M"
    and holds: "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system"
  shows "single_valued (set qs) \<and> single_valued (set cs) \<and>
    rel_dom (set qs)\<inter>rel_dom (set cs)={} \<and> rel_dom (set qs)\<union>rel_dom (set cs)=rel_dom M"
proof -
  obtain A C where parts: "term_bindings_formed (set Vs) (set xs)" "native_premise_family_at E u (set Vs) r A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    using holds by (simp only: premise_family_instantiation_on_values[OF source]) blast
  obtain S N where reading: "environment_formed E" "artifact_at E u S" "family_at S r N"
    "single_valued (socket_sum A C)" "rel_dom (socket_sum A C)=rel_dom N"
    using parts(2) by (auto simp: native_premise_family_at_def)
  have same: "S=R" by (rule environment_artifact_unique[OF reading(1,2) artifact])
  have actual: "family_at R r N" using reading(3) same by simp
  have rows: "N=M" by (rule family_at_unique[OF actual raw])
  show ?thesis using native_family_instance_boundaries[OF parts(2,1)] parts(3,4) reading(4,5) rows
    by (auto simp: socket_sum_single_valued)
qed

corollary premise_family_instantiation_omitted_or_extra_socket:
  assumes "environment_value_presents E e" "artifact_at E u R" "family_at R r M"
    "rel_dom (set qs)\<union>rel_dom (set cs)\<noteq>rel_dom M"
  shows "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<notin>positive_meaning premise_family_instantiation_system"
  using premise_family_instantiation_socket_boundary[OF assms(1-3)] assms(4) by blast

theorem premise_family_instantiation_total:
  assumes source: "environment_value_presents E e"
    and table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    and family: "native_premise_family_at E u (set Vs) r A C"
  shows "\<exists>qs cs Us. (64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (binding_rows_term xs)
      (Payload_Term r) (call_instance_rows_term qs) (binding_rows_term cs) (data_list_term (map Payload_Term Us)))
      \<in>positive_meaning premise_family_instantiation_system"
proof -
  have bindings: "term_bindings_formed (set Vs) (set xs)" using table by (simp only: binding_admission_on_values; blast)
  have finite: "finite (call_instance_relation (set xs) A)" "finite (material_instance_relation (set xs) C)"
    using native_family_instance_boundaries[OF family bindings] by auto
  have source_finite: "finite A" "finite C" using native_premise_family_formed[OF family] by auto
  have first: "finite (\<Union>(s,d,p)\<in>A. pattern_variables p)"
    by (rule finite_UN_I[OF source_finite(1)]) (auto split: prod.splits)
  have second: "finite (\<Union>(s,M)\<in>C. material_variables M)"
    by (rule finite_UN_I[OF source_finite(2)]) (auto split: prod.splits)
  have variables: "finite (premise_family_variables A C)" using first second by (simp add: premise_family_variables_def)
  obtain qs where calls: "distinct qs" "set qs=call_instance_relation (set xs) A"
    using finite_distinct_list[OF finite(1)] by blast
  obtain cs where materials: "distinct cs" "set cs=material_instance_relation (set xs) C"
    using finite_distinct_list[OF finite(2)] by blast
  obtain Us where used: "distinct Us" "set Us=premise_family_variables A C"
    using finite_distinct_list[OF variables] by blast
  show ?thesis using premise_family_instantiation_complete[OF source table family calls(2) materials(2) calls(1) materials(1) used] by blast
qed

section \<open>One fixed native program before every future operand\<close>

abbreviation premise_instantiation_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "premise_instantiation_operation_result d t \<equiv>
    (d=63 \<and> premise_rows_result t) \<or> (d=64 \<and> premise_family_instantiation_result t)"

lemma premise_instantiation_operations_exact:
  assumes "d\<in>{63,64}"
  shows "(d,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> premise_instantiation_operation_result d t"
proof -
  consider (rows) "d=63" | (family) "d=64" using assms by auto
  then show ?thesis
  proof cases
    case rows
    have old: "(63,t)\<in>positive_meaning premise_family_instantiation_system \<longleftrightarrow> (63,t)\<in>positive_meaning premise_rows_system"
      by (rule premise_family_instantiation_old_meaning) simp
    show ?thesis by (simp add: rows old premise_rows_exact)
  next
    case family
    show ?thesis by (simp add: family premise_family_instantiation_exact)
  qed
qed

theorem native_premise_instantiation_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {63::nat,64} \<and>
    (\<forall>d\<in>{63,64}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> premise_instantiation_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions premise_family_instantiation_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions premise_family_instantiation_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed premise_family_instantiation_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning premise_family_instantiation_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF premise_family_instantiation_system_formed] by blast
  have sites: "inj_on g {63,64}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {63,64}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{63,64}" and tf: "term_formed t"
    have member: "d\<in>system_definitions premise_family_instantiation_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed premise_family_instantiation_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning premise_family_instantiation_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> premise_instantiation_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member premise_instantiation_operations_exact[OF selected] in \<open>auto simp: premise_family_instantiation_call\<close>)
  qed
qed

text \<open>
  The actual artifact and complete family root are checked before its rows
  are instantiated under the common scope and substitution. Empty families
  retain this source and root boundary. Call and material roles are recovered
  from their different actual record shapes; the output contains two ordinary
  row collections and no added discriminator or pattern codec.

  Every socket remains present exactly once in its corresponding projection.
  Distinct sockets remain distinct when their endpoints or resulting values
  agree. Different premise interiors may overlap wherever the existing family
  grammar permits it. Used variables are collected by membership, including
  variables shared across premises. Material satisfaction remains separate.

  Both entries have exact contracts over every term and preserve all earlier
  meanings. The family entry accepts every complete source presentation and
  independent scope, table, call-row, material-row, and variable-use order.
  Its output collections are unique up to enumeration and total for every
  valid family with complete formed bindings. Missing and extra sockets are
  rejected. One fixed closed native program supplies two distinct sites before
  all future formed operands and retains its canonical environment. It has
  sixty-five definitions and one hundred and ten clauses. Schema and package
  admission, finite evidence checking, and the complete amendment protocol
  remain separate work.
\<close>

end
