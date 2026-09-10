theory Factor_Schema_Instantiation
  imports Factor_Premise_Family_Instantiation
begin

section \<open>The actual schema and all of its instantiated operands\<close>

abbreviation schema_instantiation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "schema_instantiation_argument e u r b t q c \<equiv>
    citation_observation_argument e u r (Pair_Term b (Pair_Term t (Pair_Term q c)))"

abbreviation schema_instantiation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "schema_instantiation_pattern e u r b t q c \<equiv>
    citation_observation_pattern e u r (Pattern_Pair b (Pattern_Pair t (Pattern_Pair q c)))"

abbreviation schema_instantiation_result :: "factor_term \<Rightarrow> bool" where
  "schema_instantiation_result z \<equiv> \<exists>E e u r xs S t qs cs.
    z=schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs) \<and>
    environment_value_presents E e \<and> distinct xs \<and> distinct qs \<and> distinct cs \<and>
    native_schema_at E u r S \<and> schema_instance S (set xs) t (set qs) \<and>
    set cs=material_instance_relation (set xs) (schema_material_premises S)"

lemma native_schema_material_instance_boundary:
  assumes source: "native_schema_at E u r S" and bindings: "term_bindings_formed (schema_variables S) B"
  shows "finite (material_instance_relation B (schema_material_premises S))"
    "single_valued (material_instance_relation B (schema_material_premises S))"
    "rel_dom (material_instance_relation B (schema_material_premises S))=rel_dom (schema_material_premises S)"
    "\<forall>s\<in>rel_dom (schema_material_premises S). octets_formed s"
proof -
  obtain m where family: "native_premise_family_at E u (schema_variables S) m
      (schema_premises S) (schema_material_premises S)"
    using source by (auto simp: native_schema_at_def)
  show "finite (material_instance_relation B (schema_material_premises S))"
    "single_valued (material_instance_relation B (schema_material_premises S))"
    "rel_dom (material_instance_relation B (schema_material_premises S))=rel_dom (schema_material_premises S)"
    using native_family_instance_boundaries[OF family bindings] by auto
  obtain R M where parts: "environment_formed E" "artifact_at E u R" "family_at R m M"
    "rel_dom (socket_sum (schema_premises S) (schema_material_premises S))=rel_dom M"
    using family by (auto simp: native_premise_family_at_def)
  have formed: "exact_formed R" using parts(1,2) by (auto simp: environment_formed_def)
  show "\<forall>s\<in>rel_dom (schema_material_premises S). octets_formed s"
    using family_interior_in_carrier[OF parts(3)] parts(4)[unfolded socket_sum_domain] formed
    by (auto simp: exact_formed_def)
qed

section \<open>One ordinary clause checks the complete three-field schema\<close>

definition schema_instantiation_schema :: "(nat,nat,nat) factor_schema" where
  "schema_instantiation_schema=data_rule
    (schema_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 7)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 11),
         Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12),Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 13)])),
     (2,54,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 11)) (Pattern_Variable 14)),
     (3,55,pattern_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w
       (Pattern_Variable 12) (Pattern_Variable 4) (Pattern_Variable 15) (Pattern_Variable 16) (Pattern_Variable 17)),
     (4,64,premise_instantiation_pattern data_x data_y (Pattern_Variable 14) data_w
       (Pattern_Variable 13) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 18)),
     (5,48,collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 18) (Pattern_Variable 14)),
     (6,49,Pattern_Pair (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9,Pattern_Variable 10])
       (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 14))),
     (7,49,Pattern_Pair (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9,Pattern_Variable 10]) (Pattern_Variable 16)),
     (8,49,Pattern_Pair (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9,Pattern_Variable 10])
       (data_list_pattern [Pattern_Variable 13])),
     (9,49,Pattern_Pair (data_list_pattern [Pattern_Variable 11]) (Pattern_Variable 16)),
     (10,49,Pattern_Pair (data_list_pattern [Pattern_Variable 11]) (data_list_pattern [Pattern_Variable 13])),
     (11,49,Pattern_Pair (data_list_pattern [Pattern_Variable 13]) (Pattern_Variable 16))}"

definition schema_instantiation_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_instantiation_system=add_view_definition premise_family_instantiation_system 65 data_x {(0,schema_instantiation_schema)}"

lemma schema_instantiation_system_formed [simp]: "schema_system_formed schema_instantiation_system"
  unfolding schema_instantiation_system_def
  by (rule add_recursive_definition_formed[OF premise_family_instantiation_system_formed])
    (auto simp: schema_instantiation_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_instantiation_definitions [simp]:
  "system_definitions schema_instantiation_system=insert 65 (system_definitions premise_family_instantiation_system)"
  by (simp add: schema_instantiation_system_def)

lemma schema_instantiation_call:
  "schema_call_formed schema_instantiation_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_instantiation_system \<and> term_formed t"
  using added_variable_calls[OF premise_family_instantiation_system_formed
    schema_instantiation_system_formed[unfolded schema_instantiation_system_def] premise_family_instantiation_call]
  by (simp only: schema_instantiation_system_def[symmetric])

lemma schema_instantiation_old_meaning:
  assumes "d\<in>system_definitions premise_family_instantiation_system"
  shows "(d,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning premise_family_instantiation_system"
  using added_definition_preserves_old(2)[OF premise_family_instantiation_system_formed
    schema_instantiation_system_formed[unfolded schema_instantiation_system_def], of d t] assms
  by (auto simp: schema_instantiation_system_def)

lemma schema_instantiation_clause [simp]:
  "((65,c),S)\<in>system_clauses schema_instantiation_system \<longleftrightarrow> (c,S)\<in>{(0,schema_instantiation_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses premise_family_instantiation_system \<Longrightarrow>
    d\<in>system_definitions premise_family_instantiation_system" for d c S
    using premise_family_instantiation_system_formed unfolding schema_system_formed_def by blast
  have absent: "((65,c),S)\<notin>system_clauses premise_family_instantiation_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_instantiation_system_def)
qed

lemma schema_instantiation_pattern_meaning:
  assumes "d\<in>system_definitions pattern_instantiation_system"
  shows "(d,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning pattern_instantiation_system"
  using schema_instantiation_old_meaning[of d t] premise_family_instantiation_old_meaning[of d t]
    premise_rows_vector_meaning[of d t] vector_instantiation_pattern_meaning[OF assms, of t] assms by auto

lemma schema_instantiation_components:
  "(37,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(54,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (54,t)\<in>positive_meaning binder_admission_system"
  "(55,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (55,t)\<in>positive_meaning pattern_instantiation_system"
  "(64,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (64,t)\<in>positive_meaning premise_family_instantiation_system"
  "(48,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (48,t)\<in>positive_meaning data_union_system"
  "(49,t)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using schema_instantiation_pattern_meaning[of 37 t] pattern_instantiation_components(6)[of t]
    schema_instantiation_pattern_meaning[of 34 t] pattern_instantiation_components(7)[of t]
    schema_instantiation_pattern_meaning[of 54 t] pattern_instantiation_old_meaning[of 54 t]
    schema_instantiation_pattern_meaning[of 55 t] schema_instantiation_old_meaning[of 64 t]
    schema_instantiation_pattern_meaning[of 48 t] pattern_instantiation_components(10)[of t]
    schema_instantiation_pattern_meaning[of 49 t] pattern_instantiation_components(4)[of t] by auto

lemma schema_instantiation_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p b,Pair_Term q c,Pair_Term s m]))\<in>positive_meaning record_admission_system"
    and scope_read: "(54,rooted_rows_argument a b v)\<in>positive_meaning binder_admission_system"
    and head: "(55,pattern_instantiation_argument e u v table c t w i k)\<in>positive_meaning pattern_instantiation_system"
    and body: "(64,premise_instantiation_argument e u v table m calls materials j)\<in>positive_meaning premise_family_instantiation_system"
    and variables: "(48,collection_join_argument w j v)\<in>positive_meaning data_union_system"
    and outer_binder: "(49,Pair_Term (data_list_term [r,p,q,s]) (Pair_Term b v))\<in>positive_meaning payload_disjoint_system"
    and outer_head: "(49,Pair_Term (data_list_term [r,p,q,s]) i)\<in>positive_meaning payload_disjoint_system"
    and outer_family: "(49,Pair_Term (data_list_term [r,p,q,s]) (data_list_term [m]))\<in>positive_meaning payload_disjoint_system"
    and binder_head: "(49,Pair_Term (data_list_term [b]) i)\<in>positive_meaning payload_disjoint_system"
    and binder_family: "(49,Pair_Term (data_list_term [b]) (data_list_term [m]))\<in>positive_meaning payload_disjoint_system"
    and family_head: "(49,Pair_Term (data_list_term [m]) i)\<in>positive_meaning payload_disjoint_system"
  shows "(65,schema_instantiation_argument e u r table t calls materials)\<in>positive_meaning schema_instantiation_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed table" "term_formed t"
    "term_formed calls" "term_formed materials" "term_formed a" "term_formed p" "term_formed q" "term_formed s"
    "term_formed b" "term_formed c" "term_formed m" "term_formed v" "term_formed w"
    "term_formed i" "term_formed k" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF head]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]]
      schema_call_formed_target[OF positive_meaning_formed[OF variables]]
      schema_call_formed_target[OF positive_meaning_formed[OF outer_binder]]
      schema_call_formed_target[OF positive_meaning_formed[OF outer_head]]
      schema_call_formed_target[OF positive_meaning_formed[OF outer_family]]
      schema_call_formed_target[OF positive_meaning_formed[OF binder_head]]
      schema_call_formed_target[OF positive_meaning_formed[OF binder_family]]
      schema_call_formed_target[OF positive_meaning_formed[OF family_head]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then table
    else if n=4 then t else if n=5 then calls else if n=6 then materials else if n=7 then a else if n=8 then p
    else if n=9 then q else if n=10 then s else if n=11 then b else if n=12 then c else if n=13 then m
    else if n=14 then v else if n=15 then w else if n=16 then i else if n=17 then k else j"
  have result: "(65,evaluate_pattern ?h (schema_conclusion schema_instantiation_schema))\<in>positive_meaning schema_instantiation_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: schema_instantiation_schema_def schema_variables_def
        schema_instantiation_call schema_instantiation_components\<close>)
  show ?thesis using result by (simp add: schema_instantiation_schema_def)
qed

theorem schema_instantiation_sound:
  assumes holds: "(65,z)\<in>positive_meaning schema_instantiation_system"
  shows "schema_instantiation_result z"
proof -
  have consequence: "(65,z)\<in>schema_consequences schema_instantiation_system (positive_meaning schema_instantiation_system)"
    using holds positive_meaning_unfold[of schema_instantiation_system] by blast
  obtain n S h where clause: "((65,n),S)\<in>system_clauses schema_instantiation_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning schema_instantiation_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=schema_instantiation_schema" using clause by simp
  have calls:
    "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 7) (h 2) (data_list_term [Pair_Term (h 8) (h 11),Pair_Term (h 9) (h 12),Pair_Term (h 10) (h 13)]))\<in>positive_meaning record_admission_system"
    "(54,rooted_rows_argument (h 7) (h 11) (h 14))\<in>positive_meaning binder_admission_system"
    "(55,pattern_instantiation_argument (h 0) (h 1) (h 14) (h 3) (h 12) (h 4) (h 15) (h 16) (h 17))\<in>positive_meaning pattern_instantiation_system"
    "(64,premise_instantiation_argument (h 0) (h 1) (h 14) (h 3) (h 13) (h 5) (h 6) (h 18))\<in>positive_meaning premise_family_instantiation_system"
    "(48,collection_join_argument (h 15) (h 18) (h 14))\<in>positive_meaning data_union_system"
    "(49,Pair_Term (data_list_term [(h 2),(h 8),(h 9),(h 10)]) (Pair_Term (h 11) (h 14)))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [(h 2),(h 8),(h 9),(h 10)]) (h 16))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [(h 2),(h 8),(h 9),(h 10)]) (data_list_term [(h 13)]))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [(h 11)]) (h 16))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [(h 11)]) (data_list_term [(h 13)]))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term [(h 13)]) (h 16))\<in>positive_meaning payload_disjoint_system"
    using support by (auto simp: schema schema_instantiation_schema_def schema_instantiation_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 7)"
    using calls(1) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r p b q c s m where rec: "h 2=Payload_Term r" "h 8=Payload_Term p" "h 11=Payload_Term b"
    "h 9=Payload_Term q" "h 12=Payload_Term c" "h 10=Payload_Term s" "h 13=Payload_Term m"
    "record_at R r [p,q,s] [b,c,m]"
    using calls(2) by (simp only: record_admission_three_fields[OF source(4)]) blast
  obtain Vs where scope_read: "h 14=data_list_term (map Payload_Term Vs)" "distinct Vs" "binder_scope_at R b (set Vs)"
    using calls(3) by (simp only: rec(3) binder_admission_at_source[OF source(4)] factor_term.inject) auto
  obtain xs ptn Us Is Ks where table: "h 3=binding_rows_term xs" "distinct xs" "term_bindings_formed (set Vs) (set xs)"
    and head: "h 15=data_list_term (map Payload_Term Us)" "h 16=data_list_term (map Payload_Term Is)"
    "h 17=data_list_term (map Payload_Term Ks)" "distinct Us" "distinct Is" "distinct Ks"
    "pattern_quoted_at E u (set Vs) c ptn (set Is) (set Ks)" "pattern_variables ptn=set Us"
    "pattern_instance (set xs) ptn (h 4)"
    using calls(4)
    by (simp only: source(2) rec(5) scope_read(1) pattern_instantiation_at_source[OF source(1)]
      data_list_term_injective injective_mapped_lists[OF payload_term_inj] factor_term.inject)
      (auto simp: inj_eq[OF use_data_term_injective])
  obtain A C qs cs Ws where body: "h 5=call_instance_rows_term qs" "h 6=binding_rows_term cs"
    "h 18=data_list_term (map Payload_Term Ws)" "distinct qs" "distinct cs" "distinct Ws"
    "native_premise_family_at E u (set Vs) m A C"
    "set qs=call_instance_relation (set xs) A" "set cs=material_instance_relation (set xs) C"
    "set Ws=premise_family_variables A C"
    using calls(5)
    by (simp only: source(2) rec(7) scope_read(1) table(1)
      premise_family_instantiation_at_source[OF source(1)] binding_rows_term_injective
      inj_eq[OF use_data_term_injective] factor_term.inject)
      (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj])
  have variables: "set Vs=pattern_variables ptn\<union>premise_family_variables A C"
    using calls(6) by (simp only: head(1) body(3) scope_read(1) data_union_payload_lists) (use head(8) body(10) in blast)
  have lists: "data_list_term [h 2,h 8,h 9,h 10]=data_list_term (map Payload_Term [r,p,q,s])"
    "Pair_Term (h 11) (h 14)=data_list_term (map Payload_Term (b#Vs))"
    "data_list_term [h 11]=data_list_term (map Payload_Term [b])"
    "data_list_term [h 13]=data_list_term (map Payload_Term [m])"
    by (simp_all add: rec scope_read(1))
  have separated: "insert r (set [p,q,s])\<inter>(insert b (set Vs)\<union>set Is\<union>{m})={}"
    "insert b (set Vs)\<inter>set Is={}" "b\<noteq>m" "m\<notin>set Is"
    using calls(7-12) pattern_quoted_boundary[OF head(7)]
    by (simp_all only: lists head(2) payload_disjoint_lists) auto
  let ?S="\<lparr>schema_conclusion=ptn,schema_premises=A,schema_material_premises=C\<rparr>"
  have scope: "set Vs=schema_variables ?S"
    using variables by (simp add: schema_variables_def premise_family_variables_def Un_assoc)
  have environment: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  have raw: "native_schema_at E u r ?S"
    unfolding native_schema_at_def
    by (rule conjI, rule environment, rule exI[of _ R], rule exI[of _ "[p,q,s]"], rule exI[of _ b],
      rule exI[of _ c], rule exI[of _ m], rule exI[of _ "set Vs"], rule exI[of _ "set Is"], rule exI[of _ "set Ks"])
      (use source(3) rec(8) scope_read(3) head(7) body(7) scope separated in auto)
  have formed: "schema_formed ?S" by (rule native_schema_formed[OF raw])
  have bindings: "term_bindings_formed (schema_variables ?S) (set xs)" using table(3) scope by simp
  have inst: "schema_instance ?S (set xs) (h 4) (set qs)"
    using formed bindings head(9) body(8)
    by (simp add: schema_instance_def schema_premise_instance_relation_iff[OF formed bindings])
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ xs],
      rule exI[of _ ?S], rule exI[of _ "h 4"], rule exI[of _ qs], rule exI[of _ cs])
      (use conclusion source rec table body raw inst in \<open>simp add: schema schema_instantiation_schema_def\<close>)
qed

theorem schema_instantiation_complete:
  assumes raw: "native_schema_at E u r S" and source: "environment_value_presents E e"
    and inst: "schema_instance S (set xs) t (set qs)"
    and order: "distinct xs" "distinct qs" "distinct cs"
    and materials: "set cs=material_instance_relation (set xs) (schema_material_premises S)"
  shows "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
proof -
  obtain R ps b c m V I K where parts: "artifact_at E u R" "record_at R r ps [b,c,m]"
    "binder_scope_at R b V" "pattern_quoted_at E u V c (schema_conclusion S) I K"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
    "V=schema_variables S" "insert r (set ps)\<inter>(insert b V\<union>I\<union>{m})={}"
    "insert b V\<inter>I={}" "b\<noteq>m" "m\<notin>I"
    using raw by (auto simp: native_schema_at_def)
  have environment: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have formed: "exact_formed R" using environment parts(1) by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF formed] by blast
  obtain p q s where ports: "ps=[p,q,s]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  obtain Vs where vs: "set Vs=V" "distinct Vs"
    using finite_distinct_list[OF binder_scope_properties(1)[OF parts(3)]] by blast
  obtain Us where us: "set Us=pattern_variables (schema_conclusion S)" "distinct Us"
    using finite_distinct_list[of "pattern_variables (schema_conclusion S)"] by auto
  obtain Is Ks where metadata: "set Is=I" "distinct Is" "set Ks=K" "distinct Ks"
    using finite_distinct_list[of I] finite_distinct_list[of K] pattern_quoted_boundary[OF parts(4)] by blast
  have body_subset: "premise_family_variables (schema_premises S) (schema_material_premises S)\<subseteq>V"
    by (auto simp: parts(6) schema_variables_def premise_family_variables_def)
  have body_finite: "finite (premise_family_variables (schema_premises S) (schema_material_premises S))"
    by (rule finite_subset[OF body_subset binder_scope_properties(1)[OF parts(3)]])
  obtain Ws where ws: "set Ws=premise_family_variables (schema_premises S) (schema_material_premises S)" "distinct Ws"
    using finite_distinct_list[OF body_finite] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using parts(1) presented by (simp only: artifact_lookup_at_source[OF source]) blast
  have rec: "(34,rooted_rows_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term p) (Payload_Term b),Pair_Term (Payload_Term q) (Payload_Term c),
        Pair_Term (Payload_Term s) (Payload_Term m)]))\<in>positive_meaning record_admission_system"
    by (simp only: record_admission_three_fields[OF presented]) (use parts(2) ports in auto)
  have scope_read: "(54,rooted_rows_argument a (Payload_Term b) (data_list_term (map Payload_Term Vs)))
      \<in>positive_meaning binder_admission_system"
    by (simp only: binder_admission_on_values[OF presented]) (use parts(3) vs in auto)
  have scope_bytes: "\<forall>a\<in>set Vs. octets_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF scope_read]] by (auto simp: data_list_term_formed)
  have bindings: "term_bindings_formed (schema_variables S) (set xs)"
    and head_instance: "pattern_instance (set xs) (schema_conclusion S) t"
    and premise_instance: "schema_premise_instance S (set xs) (set qs)"
    using inst by (auto simp: schema_instance_def)
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use order(1) vs scope_bytes bindings parts(6) in auto)
  have head: "(55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term c) t (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning pattern_instantiation_system"
    by (rule pattern_instantiation_complete[OF parts(4) source table vs(1) us(2) metadata(2,4) us(1) metadata(1,3) head_instance])
  have single: "single_valued (set xs)" using bindings by (simp add: term_bindings_formed_def)
  have calls: "set qs=call_instance_relation (set xs) (schema_premises S)"
    by (rule schema_premise_instance_relation[OF single premise_instance])
  have body: "(64,premise_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term m) (call_instance_rows_term qs) (binding_rows_term cs)
      (data_list_term (map Payload_Term Ws)))\<in>positive_meaning premise_family_instantiation_system"
    by (rule premise_family_instantiation_complete[OF source table _ calls materials order(2,3) ws(2,1)])
      (use parts(5) vs(1) in simp)
  have operands: "octets_formed r" "octets_formed p" "octets_formed q" "octets_formed s"
    "octets_formed b" "octets_formed m" "\<forall>a\<in>set Vs\<union>set Us\<union>set Is\<union>set Ws. octets_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF head]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]]
    by (auto simp: data_list_term_formed)
  have union: "set Vs=set Us\<union>set Ws"
    by (simp add: vs(1) parts(6) us(1) ws(1) schema_variables_def premise_family_variables_def Un_assoc)
  have variables: "(48,collection_join_argument (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Ws)) (data_list_term (map Payload_Term Vs)))\<in>positive_meaning data_union_system"
    by (simp only: data_union_payload_lists) (use operands union in auto)
  have outer_distinct: "distinct [r,p,q,s]"
    using record_at_preserves_socket_occurrences[OF parts(2)] ports by auto
  have binder_distinct: "distinct (b#Vs)"
    using binder_scope_properties(3)[OF parts(3)] vs by auto
  have separated:
    "(49,Pair_Term (data_list_term (map Payload_Term [r,p,q,s])) (data_list_term (map Payload_Term (b#Vs))))
      \<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term (map Payload_Term [r,p,q,s])) (data_list_term (map Payload_Term Is)))
      \<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term (map Payload_Term [r,p,q,s])) (data_list_term (map Payload_Term [m])))
      \<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term (map Payload_Term [b])) (data_list_term (map Payload_Term Is)))
      \<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term (map Payload_Term [b])) (data_list_term (map Payload_Term [m])))
      \<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (data_list_term (map Payload_Term [m])) (data_list_term (map Payload_Term Is)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp_all only: payload_disjoint_lists)
      (use parts(7-10) ports vs(1) metadata(1,2) outer_distinct binder_distinct operands in auto)
  show ?thesis by (rule schema_instantiation_step[OF lookup rec scope_read head body variables])
    (use separated in simp_all)
qed

theorem schema_instantiation_exact:
  "(65,z)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow> schema_instantiation_result z"
proof
  show "(65,z)\<in>positive_meaning schema_instantiation_system \<Longrightarrow> schema_instantiation_result z"
    by (rule schema_instantiation_sound)
next
  assume "schema_instantiation_result z"
  then obtain E e u r xs S t qs cs where parts:
    "z=schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs)"
    "environment_value_presents E e" "distinct xs" "distinct qs" "distinct cs"
    "native_schema_at E u r S" "schema_instance S (set xs) t (set qs)"
    "set cs=material_instance_relation (set xs) (schema_material_premises S)" by blast
  show "(65,z)\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_complete[OF parts(6,2,7,3-5,8)] parts(1) by simp
qed

corollary schema_instantiation_at_source:
  assumes source: "environment_value_presents E e"
  shows "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    (\<exists>a l xs S qs cs. u=use_data_term a \<and> r=Payload_Term l \<and> b=binding_rows_term xs \<and>
      q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> distinct xs \<and> distinct qs \<and> distinct cs \<and>
      native_schema_at E a l S \<and> schema_instance S (set xs) t (set qs) \<and>
      set cs=material_instance_relation (set xs) (schema_material_premises S))"
proof
  assume holds: "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system"
  obtain F a l xs S qs cs where parts: "environment_value_presents F e" "u=use_data_term a"
    "r=Payload_Term l" "b=binding_rows_term xs" "q=call_instance_rows_term qs" "c=binding_rows_term cs"
    "distinct xs" "distinct qs" "distinct cs" "native_schema_at F a l S"
    "schema_instance S (set xs) t (set qs)" "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using holds by (simp only: schema_instantiation_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>a l xs S qs cs. u=use_data_term a \<and> r=Payload_Term l \<and> b=binding_rows_term xs \<and>
      q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> distinct xs \<and> distinct qs \<and> distinct cs \<and>
      native_schema_at E a l S \<and> schema_instance S (set xs) t (set qs) \<and>
      set cs=material_instance_relation (set xs) (schema_material_premises S)"
    by (rule exI[of _ a], rule exI[of _ l], rule exI[of _ xs], rule exI[of _ S], rule exI[of _ qs], rule exI[of _ cs])
      (use parts same in auto)
next
  assume "\<exists>a l xs S qs cs. u=use_data_term a \<and> r=Payload_Term l \<and> b=binding_rows_term xs \<and>
      q=call_instance_rows_term qs \<and> c=binding_rows_term cs \<and> distinct xs \<and> distinct qs \<and> distinct cs \<and>
      native_schema_at E a l S \<and> schema_instance S (set xs) t (set qs) \<and>
      set cs=material_instance_relation (set xs) (schema_material_premises S)"
  then obtain a l xs S qs cs where parts: "u=use_data_term a" "r=Payload_Term l" "b=binding_rows_term xs"
    "q=call_instance_rows_term qs" "c=binding_rows_term cs" "distinct xs" "distinct qs" "distinct cs"
    "native_schema_at E a l S" "schema_instance S (set xs) t (set qs)"
    "set cs=material_instance_relation (set xs) (schema_material_premises S)" by blast
  show "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_complete[OF parts(9) source parts(10,6-8,11)] parts(1-5) by simp
qed

corollary schema_instantiation_on_values:
  assumes source: "environment_value_presents E e"
  shows "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> distinct cs \<and>
    (\<exists>S. native_schema_at E u r S \<and> schema_instance S (set xs) t (set qs) \<and>
      set cs=material_instance_relation (set xs) (schema_material_premises S))"
  by (simp only: schema_instantiation_at_source[OF source] call_instance_rows_term_injective
    binding_rows_term_injective call_instance_rows_map_injective inj_eq[OF use_data_term_injective] factor_term.inject)
    blast

corollary schema_instantiation_at_schema:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
  shows "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> distinct cs \<and> schema_instance S (set xs) t (set qs) \<and>
    set cs=material_instance_relation (set xs) (schema_material_premises S)"
proof -
  have unique: "T=S" if "native_schema_at E u r T" for T
    by (rule native_schema_unique[OF that raw])
  show ?thesis
    by (simp only: schema_instantiation_on_values[OF source]) (use raw unique in blast)
qed

corollary schema_instantiation_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    (65,schema_instantiation_argument f u r b t q c)\<in>positive_meaning schema_instantiation_system"
  by (simp only: schema_instantiation_at_source[OF assms(1)] schema_instantiation_at_source[OF assms(2)])

corollary schema_instantiation_orders:
  assumes source: "environment_value_presents E e" and same: "mset xs=mset ys" "mset qs=mset qs'" "mset cs=mset cs'"
  shows "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system \<longleftrightarrow>
    (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) t
      (call_instance_rows_term qs') (binding_rows_term cs'))\<in>positive_meaning schema_instantiation_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)] mset_eq_imp_distinct_iff[OF same(3)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)] mset_eq_setD[OF same(3)]
  by (simp only: schema_instantiation_on_values[OF source])

corollary schema_instantiation_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    and second: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) v
      (call_instance_rows_term qs') (binding_rows_term cs'))\<in>positive_meaning schema_instantiation_system"
  shows "t=v \<and> mset qs=mset qs' \<and> mset cs=mset cs'"
proof -
  obtain S where left: "native_schema_at E u r S" "distinct qs" "distinct cs"
    "schema_instance S (set xs) t (set qs)" "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using first by (simp only: schema_instantiation_on_values[OF source]) blast
  have right: "distinct qs'" "distinct cs'" "schema_instance S (set xs) v (set qs')"
    "set cs'=material_instance_relation (set xs) (schema_material_premises S)"
    using iffD1[OF schema_instantiation_at_schema[OF source left(1)] second] by auto
  have same: "t=v" "set qs=set qs'" using schema_instance_unique[OF left(4) right(3)] by auto
  show ?thesis using same left right distinct_source_mset[OF left(2), of qs'] distinct_source_mset[OF left(3), of cs'] by auto
qed

theorem schema_instantiation_total:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and bindings: "term_bindings_formed (schema_variables S) (set xs)" and order: "distinct xs"
  shows "\<exists>t qs cs. (65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
proof -
  have formed: "schema_formed S" by (rule native_schema_formed[OF raw])
  obtain t Q where inst: "schema_instance S (set xs) t Q" using schema_instance_exists[OF formed bindings] by blast
  have finite: "finite Q" using inst by (simp add: schema_instance_def schema_premise_instance_def)
  obtain qs where qs: "set qs=Q" "distinct qs" using finite_distinct_list[OF finite] by blast
  obtain cs where cs: "set cs=material_instance_relation (set xs) (schema_material_premises S)" "distinct cs"
    using finite_distinct_list[OF native_schema_material_instance_boundary(1)[OF raw bindings]] by blast
  have actual: "schema_instance S (set xs) t (set qs)" using inst qs(1) by simp
  show ?thesis by (rule exI[of _ t], rule exI[of _ qs], rule exI[of _ cs])
    (rule schema_instantiation_complete[OF raw source actual order qs(2) cs(2,1)])
qed

theorem schema_instantiation_socket_boundary:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and holds: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
  shows "single_valued (set qs) \<and> single_valued (set cs) \<and>
    rel_dom (set qs)=rel_dom (schema_premises S) \<and> rel_dom (set cs)=rel_dom (schema_material_premises S) \<and>
    rel_dom (set qs)\<inter>rel_dom (set cs)={}"
proof -
  have inst: "schema_instance S (set xs) t (set qs)"
    and rows: "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using iffD1[OF schema_instantiation_at_schema[OF source raw] holds] by auto
  have bindings: "term_bindings_formed (schema_variables S) (set xs)" using inst by (simp add: schema_instance_def)
  have formed: "schema_formed S" by (rule native_schema_formed[OF raw])
  show ?thesis using schema_instance_socket_boundary[OF inst]
    native_schema_material_instance_boundary(2,3)[OF raw bindings] rows formed by (auto simp: schema_formed_def)
qed

corollary schema_instantiation_missing_or_extra_socket:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and changed: "rel_dom (set qs)\<noteq>rel_dom (schema_premises S) \<or> rel_dom (set cs)\<noteq>rel_dom (schema_material_premises S)"
  shows "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<notin>positive_meaning schema_instantiation_system"
  using schema_instantiation_socket_boundary[OF source raw] changed by blast

text \<open>
  The entry reads the actual three-field record, binder family, conclusion,
  and complete mixed premise family. The substitution domain is exactly the
  variables used across the conclusion and both premise roles. Unused
  declarations, missing bindings, and extra bindings cannot pass. Every
  prospective call and material operand is instantiated under that same table.

  Separation is exactly the existing schema grammar. The outer record is
  disjoint from its binder interior, conclusion interior, and family root.
  The binder root and family root are distinct, and both are outside the
  conclusion interior. No disjointness between the family root and the
  declared variables, between different premise interiors, or against extra
  external slots is introduced. No aggregate interior is exported because
  the existing schema judgment specifies no such aggregate.

  The contract is exact over every term, accepts every source presentation
  and independent substitution and output order, and has a unique conclusion
  and unique socket projections up to enumeration. Every valid native schema
  with complete formed bindings has an instance. Material satisfaction and
  the formation and truth of prospective calls remain separate judgments.
\<close>

end
