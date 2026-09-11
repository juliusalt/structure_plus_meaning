theory Factor_Record_Instantiation
  imports Factor_Vector_Instantiation
begin

section \<open>Complete ordered rows supply sockets and pattern roots\<close>

lemma address_rows_pair_list:
  "data_list_term (map address_pair_data xs)=pair_list_term (map (\<lambda>(a,b). (Payload_Term a,Payload_Term b)) xs)"
  by (induction xs) (auto simp: address_pair_data_def split: prod.splits)

lemma address_row_keys:
  "(51,Pair_Term (data_list_term (map address_pair_data xs)) k)\<in>positive_meaning row_keys_system \<longleftrightarrow>
    term_formed (data_list_term (map address_pair_data xs)) \<and> k=data_list_term (map Payload_Term (map fst xs))"
  by (simp only: address_rows_pair_list row_keys_at_rows) (simp add: comp_def split_def)

lemma address_row_values:
  "(59,Pair_Term (data_list_term (map address_pair_data xs)) v)\<in>positive_meaning row_values_system \<longleftrightarrow>
    term_formed (data_list_term (map address_pair_data xs)) \<and> v=data_list_term (map Payload_Term (map snd xs))"
  by (simp only: address_rows_pair_list row_values_at_rows) (simp add: comp_def split_def)

abbreviation record_instantiation_result :: "factor_term \<Rightarrow> bool" where
  "record_instantiation_result z \<equiv> \<exists>E e u Vs xs r ps ts Us Is Ks.
    z=pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts) (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
    environment_value_presents E e \<and> distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and>
    term_bindings_formed (set Vs) (set xs) \<and> distinct Us \<and> distinct Is \<and> distinct Ks \<and>
    pattern_record_at E u (set Vs) r ps (set Is) (set Ks) \<and>
    pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts"

lemma record_instantiation_result_at_source:
  assumes source: "environment_value_presents E e"
  shows "record_instantiation_result (pattern_instantiation_argument e u v b r t w i k) \<longleftrightarrow>
    (\<exists>q Vs xs a ps ts Us Is Ks. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and>
      b=binding_rows_term xs \<and> r=Payload_Term a \<and> t=data_list_term ts \<and> w=data_list_term (map Payload_Term Us) \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct Us \<and> distinct Is \<and> distinct Ks \<and> pattern_record_at E q (set Vs) a ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts)"
proof
  assume admitted: "record_instantiation_result (pattern_instantiation_argument e u v b r t w i k)"
  obtain F q Vs xs a ps ts Us Is Ks where parts: "environment_value_presents F e"
    "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)" "b=binding_rows_term xs" "r=Payload_Term a" "t=data_list_term ts"
    "w=data_list_term (map Payload_Term Us)" "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    "distinct Us" "distinct Is" "distinct Ks" "pattern_record_at F q (set Vs) a ps (set Is) (set Ks)"
    "pattern_forest_variables ps=set Us" "list_all2 (pattern_instance (set xs)) ps ts"
    using admitted by (simp only: factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>q Vs xs a ps ts Us Is Ks. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and>
      b=binding_rows_term xs \<and> r=Payload_Term a \<and> t=data_list_term ts \<and> w=data_list_term (map Payload_Term Us) \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct Us \<and> distinct Is \<and> distinct Ks \<and> pattern_record_at E q (set Vs) a ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts"
    by (rule exI[of _ q], rule exI[of _ Vs], rule exI[of _ xs], rule exI[of _ a], rule exI[of _ ps], rule exI[of _ ts],
      rule exI[of _ Us], rule exI[of _ Is], rule exI[of _ Ks]) (use parts same in auto)
next
  assume "\<exists>q Vs xs a ps ts Us Is Ks. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and>
      b=binding_rows_term xs \<and> r=Payload_Term a \<and> t=data_list_term ts \<and> w=data_list_term (map Payload_Term Us) \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct Us \<and> distinct Is \<and> distinct Ks \<and> pattern_record_at E q (set Vs) a ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts"
  then obtain q Vs xs a ps ts Us Is Ks where parts:
    "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)" "b=binding_rows_term xs" "r=Payload_Term a" "t=data_list_term ts"
    "w=data_list_term (map Payload_Term Us)" "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    "distinct Us" "distinct Is" "distinct Ks" "pattern_record_at E q (set Vs) a ps (set Is) (set Ks)"
    "pattern_forest_variables ps=set Us" "list_all2 (pattern_instance (set xs)) ps ts" by blast
  show "record_instantiation_result (pattern_instantiation_argument e u v b r t w i k)"
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ q], rule exI[of _ Vs], rule exI[of _ xs],
      rule exI[of _ a], rule exI[of _ ps], rule exI[of _ ts], rule exI[of _ Us], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts source in auto)
qed

lemma record_instantiation_result_on_context:
  assumes source: "environment_value_presents E e"
  shows "record_instantiation_result (pattern_instantiation_argument e (use_data_term u)
      (data_list_term (map Payload_Term Vs)) (binding_rows_term xs) (Payload_Term r) (data_list_term ts) w i k) \<longleftrightarrow>
    distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
    (\<exists>ps Us Is Ks. w=data_list_term (map Payload_Term Us) \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Us \<and> distinct Is \<and> distinct Ks \<and> pattern_record_at E u (set Vs) r ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts)"
  by (subst record_instantiation_result_at_source[OF source],
    simp only: binding_rows_term_injective inj_eq[OF use_data_term_injective] factor_term.inject)
    (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj])

section \<open>The actual record and its complete vector instance\<close>

definition record_instantiation_schema :: "(nat,nat,nat) factor_schema" where
  "record_instantiation_schema=data_rule
    (pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4)
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 9)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 4)) (Pattern_Variable 10)),
     (2,51,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)),
     (3,59,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 12)),
     (4,60,pattern_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 12)
       (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 13) (Pattern_Variable 8)),
     (5,46,collection_join_pattern (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 11))
       (Pattern_Variable 13) (Pattern_Variable 14)),
     (6,6,Pattern_Pair (Pattern_Variable 14) (Pattern_Variable 7)),
     (7,49,Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)),
     (8,49,Pattern_Pair (Pattern_Variable 7) data_z)}"

definition record_instantiation_system :: "(nat,nat,nat,nat) schema_system" where
  "record_instantiation_system=add_view_definition vector_instantiation_system 61 data_x {(0,record_instantiation_schema)}"

lemma record_instantiation_system_formed [simp]: "schema_system_formed record_instantiation_system"
  unfolding record_instantiation_system_def
  by (rule add_recursive_definition_formed[OF vector_instantiation_system_formed])
    (auto simp: record_instantiation_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma record_instantiation_definitions [simp]:
  "system_definitions record_instantiation_system=insert 61 (system_definitions vector_instantiation_system)"
  by (simp add: record_instantiation_system_def)

lemma record_instantiation_call:
  "schema_call_formed record_instantiation_system d t \<longleftrightarrow>
    d\<in>system_definitions record_instantiation_system \<and> term_formed t"
  using added_variable_calls[OF vector_instantiation_system_formed
    record_instantiation_system_formed[unfolded record_instantiation_system_def] vector_instantiation_call]
  by (simp only: record_instantiation_system_def[symmetric])

lemma record_instantiation_old_meaning:
  assumes "d\<in>system_definitions vector_instantiation_system"
  shows "(d,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning vector_instantiation_system"
  using added_definition_preserves_old(2)[OF vector_instantiation_system_formed
    record_instantiation_system_formed[unfolded record_instantiation_system_def], of d t] assms
  by (auto simp: record_instantiation_system_def)

lemma record_instantiation_clause [simp]:
  "((61,c),S)\<in>system_clauses record_instantiation_system \<longleftrightarrow> (c,S)\<in>{(0,record_instantiation_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses vector_instantiation_system \<Longrightarrow>
    d\<in>system_definitions vector_instantiation_system" for d c S
    using vector_instantiation_system_formed unfolding schema_system_formed_def by blast
  have absent: "((61,c),S)\<notin>system_clauses vector_instantiation_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: record_instantiation_system_def)
qed

lemma record_instantiation_components:
  "(37,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(51,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(59,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(60,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (60,t)\<in>positive_meaning vector_instantiation_system"
  "(46,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(6,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(49,t)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using record_instantiation_old_meaning[of 37 t] vector_instantiation_pattern_meaning[of 37 t] pattern_instantiation_components(6)[of t]
    record_instantiation_old_meaning[of 34 t] vector_instantiation_pattern_meaning[of 34 t] pattern_instantiation_components(7)[of t]
    record_instantiation_old_meaning[of 51 t] vector_instantiation_pattern_meaning[of 51 t]
    pattern_instantiation_old_meaning[of 51 t] binder_admission_old_meaning[of 51 t]
    diagonal_rows_old_meaning[of 51 t] binding_admission_old_meaning[of 51 t]
    record_instantiation_old_meaning[of 59 t] vector_instantiation_old_meaning[of 59 t]
    record_instantiation_old_meaning[of 60 t]
    record_instantiation_old_meaning[of 46 t] vector_instantiation_components(3)[of t]
    record_instantiation_old_meaning[of 6 t] vector_instantiation_components(4)[of t]
    record_instantiation_old_meaning[of 49 t] vector_instantiation_components(6)[of t] by auto

lemma record_instantiation_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r rows)\<in>positive_meaning record_admission_system"
    and keys: "(51,Pair_Term rows ports)\<in>positive_meaning row_keys_system"
    and roots: "(59,Pair_Term rows rs)\<in>positive_meaning row_values_system"
    and body: "(60,pattern_instantiation_argument e u v b rs t w bi k)\<in>positive_meaning vector_instantiation_system"
    and joined: "(46,collection_join_argument (Pair_Term r ports) bi j)\<in>positive_meaning data_append_system"
    and interior: "(6,Pair_Term j i)\<in>positive_meaning bag_comparison_system"
    and boundary: "(49,Pair_Term i k)\<in>positive_meaning payload_disjoint_system"
    and scope: "(49,Pair_Term i v)\<in>positive_meaning payload_disjoint_system"
  shows "(61,pattern_instantiation_argument e u v b r t w i k)\<in>positive_meaning record_instantiation_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed v" "term_formed b" "term_formed r"
    "term_formed t" "term_formed w" "term_formed i" "term_formed k" "term_formed a"
    "term_formed rows" "term_formed ports" "term_formed rs" "term_formed bi" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF keys]]
      schema_call_formed_target[OF positive_meaning_formed[OF roots]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]]
      schema_call_formed_target[OF positive_meaning_formed[OF joined]]
      schema_call_formed_target[OF positive_meaning_formed[OF interior]]
      schema_call_formed_target[OF positive_meaning_formed[OF boundary]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then v else if n=3 then b
    else if n=4 then r else if n=5 then t else if n=6 then w else if n=7 then i
    else if n=8 then k else if n=9 then a else if n=10 then rows else if n=11 then ports
    else if n=12 then rs else if n=13 then bi else j"
  have result: "(61,evaluate_pattern ?h (schema_conclusion record_instantiation_schema))\<in>positive_meaning record_instantiation_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: record_instantiation_schema_def schema_variables_def
        record_instantiation_call record_instantiation_components\<close>)
  show ?thesis using result by (simp add: record_instantiation_schema_def)
qed

theorem record_instantiation_sound:
  assumes holds: "(61,z)\<in>positive_meaning record_instantiation_system"
  shows "record_instantiation_result z"
proof -
  have consequence: "(61,z)\<in>schema_consequences record_instantiation_system (positive_meaning record_instantiation_system)"
    using holds positive_meaning_unfold[of record_instantiation_system] by blast
  obtain c S h where clause: "((61,c),S)\<in>system_clauses record_instantiation_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning record_instantiation_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=record_instantiation_schema" using clause by simp
  have calls:
    "(37,artifact_lookup_argument (h 0) (h 1) (h 9))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 9) (h 4) (h 10))\<in>positive_meaning record_admission_system"
    "(51,Pair_Term (h 10) (h 11))\<in>positive_meaning row_keys_system"
    "(59,Pair_Term (h 10) (h 12))\<in>positive_meaning row_values_system"
    "(60,pattern_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 12) (h 5) (h 6) (h 13) (h 8))
      \<in>positive_meaning vector_instantiation_system"
    "(46,collection_join_argument (Pair_Term (h 4) (h 11)) (h 13) (h 14))\<in>positive_meaning data_append_system"
    "(6,Pair_Term (h 14) (h 7))\<in>positive_meaning bag_comparison_system"
    "(49,Pair_Term (h 7) (h 8))\<in>positive_meaning payload_disjoint_system"
    "(49,Pair_Term (h 7) (h 2))\<in>positive_meaning payload_disjoint_system"
    using support by (auto simp: schema record_instantiation_schema_def record_instantiation_components)
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 9)"
    using calls(1) by (auto simp: artifact_lookup_exact)
  obtain r rows where rec: "h 4=Payload_Term r" "h 10=data_list_term (map address_pair_data rows)"
    "record_at R r (map fst rows) (map snd rows)"
    using calls(2) by (simp only: record_admission_at_source[OF source(4)]) blast
  have keys: "h 11=data_list_term (map Payload_Term (map fst rows))"
    using calls(3) by (simp only: rec(2) address_row_keys; blast)
  have roots: "h 12=data_list_term (map Payload_Term (map snd rows))"
    using calls(4) by (simp only: rec(2) address_row_values; blast)
  obtain Vs xs ps ts Us Js Ks where shared:
    "h 2=data_list_term (map Payload_Term Vs)" "h 3=binding_rows_term xs"
    "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a" "term_bindings_formed (set Vs) (set xs)"
    and body: "h 5=data_list_term ts" "h 6=data_list_term (map Payload_Term Us)"
    "h 13=data_list_term (map Payload_Term Js)" "h 8=data_list_term (map Payload_Term Ks)"
    "distinct Us" "distinct Js" "distinct Ks"
    "pattern_vector_at E u (set Vs) (map snd rows) ps (set Js) (set Ks)"
    "pattern_forest_variables ps=set Us" "list_all2 (pattern_instance (set xs)) ps ts"
    using calls(5)
    by (simp only: vector_instantiation_at_source[OF source(1)] source(2) roots
        inj_eq[OF use_data_term_injective] data_list_term_injective injective_mapped_lists[OF payload_term_inj]) blast
  obtain Is where boundary: "h 7=data_list_term (map Payload_Term Is)" "distinct Is" "set Is\<inter>set Ks={}"
    using calls(8) by (auto simp: payload_disjoint_exact body(4)
      data_list_term_injective injective_mapped_lists[OF payload_term_inj])
  have separate_scope: "set Is\<inter>set Vs={}"
    using calls(9) by (simp only: boundary(1) shared(1) payload_disjoint_lists)
  have joined_call: "(46,collection_join_argument (data_list_term (map Payload_Term (r#map fst rows)))
      (data_list_term (map Payload_Term Js)) (h 14))\<in>positive_meaning data_append_system"
    using calls(6) by (simp add: rec(1) keys body(3))
  have joined: "h 14=data_list_term (map Payload_Term (r#map fst rows@Js))"
    using joined_call by (simp only: data_append_at_lists) auto
  have comparison: "mset (r#map fst rows@Js)=mset Is"
    using calls(7) by (simp only: joined boundary(1) bag_comparison_lists injective_mapped_multisets[OF payload_term_inj])
  have ports: "distinct (map fst rows)" "r\<notin>set (map fst rows)"
    using record_at_preserves_socket_occurrences[OF rec(3)] by auto
  have separation: "insert r (set (map fst rows))\<inter>set Js={}"
    "set Is=insert r (set (map fst rows)\<union>set Js)"
    using quotation_interior_lists[OF ports body(6), of "[]" Is] boundary(2) comparison by auto
  have ef: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  have reading: "pattern_record_at E u (set Vs) r ps (set Is) (set Ks)"
    unfolding pattern_record_at_def
    by (rule conjI[OF ef], rule exI[of _ R], rule exI[of _ "map fst rows"],
      rule exI[of _ "map snd rows"], rule exI[of _ "set Js"])
      (use source rec body separation boundary separate_scope in auto)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ Vs], rule exI[of _ xs],
      rule exI[of _ r], rule exI[of _ ps], rule exI[of _ ts],
      rule exI[of _ Us], rule exI[of _ Is], rule exI[of _ Ks])
      (use conclusion source shared rec body boundary reading in \<open>auto simp: schema record_instantiation_schema_def\<close>)
qed

theorem record_instantiation_complete:
  assumes source: "environment_value_presents E e"
    and table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    and rec: "pattern_record_at E u (set Vs) r ps (set Is) (set Ks)"
    and order: "distinct Us" "distinct Is" "distinct Ks"
    and used: "set Us=pattern_forest_variables ps" and inst: "list_all2 (pattern_instance (set xs)) ps ts"
  shows "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts) (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning record_instantiation_system"
proof -
  obtain R ports roots J where parts: "environment_formed E" "artifact_at E u R" "record_at R r ports roots"
    "pattern_vector_at E u (set Vs) roots ps J (set Ks)" "insert r (set ports)\<inter>J={}"
    "set Is=insert r (set ports\<union>J)" "set Is\<inter>(set Ks\<union>set Vs)={}"
    using rec by (auto simp: pattern_record_at_def)
  have rf: "exact_formed R" using parts(1,2) by (auto simp: environment_formed_def)
  obtain a where presented: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lengths: "length ports=length roots" and distinct: "distinct ports" "r\<notin>set ports"
    using record_at_preserves_socket_occurrences[OF parts(3)] by auto
  let ?rows="zip ports roots"
  have projections: "map fst ?rows=ports" "map snd ?rows=roots" using lengths by (simp_all add: map_fst_zip map_snd_zip)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using source parts(2) presented by (auto simp: artifact_lookup_exact)
  have record_read: "(34,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data ?rows)))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_rows[OF presented] projections) (rule parts(3))
  have rows_formed: "term_formed (data_list_term (map address_pair_data ?rows))"
    using schema_call_formed_target[OF positive_meaning_formed[OF record_read]] by auto
  have keys: "(51,Pair_Term (data_list_term (map address_pair_data ?rows)) (data_list_term (map Payload_Term ports)))
      \<in>positive_meaning row_keys_system"
    by (simp only: address_row_keys projections) (use rows_formed in blast)
  have root_values: "(59,Pair_Term (data_list_term (map address_pair_data ?rows)) (data_list_term (map Payload_Term roots)))
      \<in>positive_meaning row_values_system"
    by (simp only: address_row_values projections) (use rows_formed in blast)
  have finite: "finite J" using pattern_vector_boundary[OF parts(4)] by blast
  obtain Js where js: "set Js=J" "distinct Js" using finite_distinct_list[OF finite] by blast
  have body: "(60,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (data_list_term (map Payload_Term roots)) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning vector_instantiation_system"
    by (rule vector_instantiation_complete[OF parts(4) source table refl order(1) js(2) order(3) used js(1) refl inst])
  have formed: "term_formed (Payload_Term r)" "term_formed (data_list_term (map Payload_Term ports))"
    "term_formed (data_list_term (map Payload_Term Js))" "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF record_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF keys]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]] by auto
  have data: "data_elements (map Payload_Term (r#ports))" "data_elements (map Payload_Term Js)"
    "data_elements (map Payload_Term Is)" "data_elements (map Payload_Term Ks)"
    using formed parts(6) js(1) by (auto simp: data_list_term_formed)
  have scope_properties: "distinct Vs" "\<forall>a\<in>set Vs. octets_formed a"
    using table[unfolded binding_admission_on_values] by auto
  have comparison: "mset (r#ports@Js)=mset Is"
    using quotation_interior_lists[OF distinct js(2), of "[]" Is] order(2) parts(5,6) js(1) by auto
  let ?j="data_list_term (map Payload_Term (r#ports@Js))"
  have joined_list: "(46,collection_join_argument (data_list_term (map Payload_Term (r#ports)))
      (data_list_term (map Payload_Term Js)) ?j)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use data in auto)
  have joined: "(46,collection_join_argument (Pair_Term (Payload_Term r) (data_list_term (map Payload_Term ports)))
      (data_list_term (map Payload_Term Js)) ?j)\<in>positive_meaning data_append_system"
    using joined_list by simp
  have interior: "(6,Pair_Term ?j (data_list_term (map Payload_Term Is)))\<in>positive_meaning bag_comparison_system"
    by (simp only: bag_comparison_lists injective_mapped_multisets[OF payload_term_inj]) (use data comparison in auto)
  have boundary: "(49,Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp only: payload_disjoint_lists) (use data order parts(7) in auto)
  have scope: "(49,Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Vs)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp only: payload_disjoint_lists) (use data scope_properties order(2) parts(7) in auto)
  show ?thesis by (rule record_instantiation_step[OF lookup record_read keys root_values body joined interior boundary scope])
qed

theorem record_instantiation_exact:
  "(61,z)\<in>positive_meaning record_instantiation_system \<longleftrightarrow> record_instantiation_result z"
proof
  show "(61,z)\<in>positive_meaning record_instantiation_system \<Longrightarrow> record_instantiation_result z"
    by (rule record_instantiation_sound)
next
  assume admitted: "record_instantiation_result z"
  obtain E e u Vs xs r ps ts Us Is Ks where parts:
    "z=pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks))"
    "environment_value_presents E e" "distinct Vs" "distinct xs" "\<forall>a\<in>set Vs. octets_formed a"
    "term_bindings_formed (set Vs) (set xs)" "distinct Us" "distinct Is" "distinct Ks"
    "pattern_record_at E u (set Vs) r ps (set Is) (set Ks)" "pattern_forest_variables ps=set Us"
    "list_all2 (pattern_instance (set xs)) ps ts" using admitted by blast
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))
      \<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use parts(3-6) in blast)
  show "(61,z)\<in>positive_meaning record_instantiation_system"
    using record_instantiation_complete[OF parts(2) table parts(10,7-9) parts(11)[symmetric] parts(12)]
    by (simp only: parts(1))
qed

corollary record_instantiation_at_source:
  assumes source: "environment_value_presents E e"
  shows "(61,pattern_instantiation_argument e u v b r t w i k)\<in>positive_meaning record_instantiation_system \<longleftrightarrow>
    (\<exists>q Vs xs a ps ts Us Is Ks. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and>
      b=binding_rows_term xs \<and> r=Payload_Term a \<and> t=data_list_term ts \<and>
      w=data_list_term (map Payload_Term Us) \<and> i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
      distinct Us \<and> distinct Is \<and> distinct Ks \<and> pattern_record_at E q (set Vs) a ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts)"
  by (simp only: record_instantiation_exact record_instantiation_result_at_source[OF source])

corollary record_instantiation_on_values:
  assumes source: "environment_value_presents E e"
  shows "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system \<longleftrightarrow>
    distinct Vs \<and> distinct xs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> term_bindings_formed (set Vs) (set xs) \<and>
    distinct Us \<and> distinct Is \<and> distinct Ks \<and>
    (\<exists>ps. pattern_record_at E u (set Vs) r ps (set Is) (set Ks) \<and>
      pattern_forest_variables ps=set Us \<and> list_all2 (pattern_instance (set xs)) ps ts)"
  by (subst record_instantiation_exact, subst record_instantiation_result_on_context[OF source])
    (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj])

corollary record_instantiation_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(61,pattern_instantiation_argument e u v b r t w i k)\<in>positive_meaning record_instantiation_system \<longleftrightarrow>
    (61,pattern_instantiation_argument f u v b r t w i k)\<in>positive_meaning record_instantiation_system"
  by (simp only: record_instantiation_at_source[OF assms(1)] record_instantiation_at_source[OF assms(2)])

corollary record_instantiation_orders:
  assumes source: "environment_value_presents E e"
    and same: "mset Vs=mset Ws" "mset xs=mset ys" "mset Us=mset Zs" "mset Is=mset Js" "mset Ks=mset Ls"
  shows "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system \<longleftrightarrow>
    (61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Ws))
      (binding_rows_term ys) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Zs)) (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))
      \<in>positive_meaning record_instantiation_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)]
    mset_eq_imp_distinct_iff[OF same(3)] mset_eq_imp_distinct_iff[OF same(4)] mset_eq_imp_distinct_iff[OF same(5)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)] mset_eq_setD[OF same(3)] mset_eq_setD[OF same(4)] mset_eq_setD[OF same(5)]
  by (simp only: record_instantiation_on_values[OF source])

corollary record_instantiation_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
    and second: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term us)
      (data_list_term (map Payload_Term Ws)) (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))
      \<in>positive_meaning record_instantiation_system"
  shows "ts=us \<and> mset Us=mset Ws \<and> mset Is=mset Js \<and> mset Ks=mset Ls"
proof -
  obtain ps where left: "term_bindings_formed (set Vs) (set xs)" "distinct Us" "distinct Is" "distinct Ks"
    "pattern_record_at E u (set Vs) r ps (set Is) (set Ks)" "pattern_forest_variables ps=set Us"
    "list_all2 (pattern_instance (set xs)) ps ts"
    using first by (simp only: record_instantiation_on_values[OF source]) blast
  obtain qs where right: "distinct Ws" "distinct Js" "distinct Ls"
    "pattern_record_at E u (set Vs) r qs (set Js) (set Ls)" "pattern_forest_variables qs=set Ws"
    "list_all2 (pattern_instance (set xs)) qs us"
    using second by (simp only: record_instantiation_on_values[OF source]) blast
  have same: "ps=qs" "set Is=set Js" "set Ks=set Ls" using pattern_record_unique[OF left(5) right(4)] by auto
  have variables: "set Us=set Ws" using same(1) left(6) right(5) by simp
  have single: "single_valued (set xs)" using left(1) by (simp add: term_bindings_formed_def)
  have other: "list_all2 (pattern_instance (set xs)) ps us" using same(1) right(6) by simp
  have terms: "ts=us" by (rule instantiated_pattern_list_unique[OF single left(7) other])
  show ?thesis using terms variables same(2,3) left(2-4) right(1-3)
    distinct_source_mset[OF left(2), of Ws] distinct_source_mset[OF left(3), of Js] distinct_source_mset[OF left(4), of Ls] by auto
qed

theorem record_instantiation_total:
  assumes source: "environment_value_presents E e"
    and table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))\<in>positive_meaning binding_admission_system"
    and rec: "pattern_record_at E u (set Vs) r ps (set Is) (set Ks)"
    and order: "distinct Us" "distinct Is" "distinct Ks" and used: "set Us=pattern_forest_variables ps"
  shows "\<exists>!ts. (61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
proof -
  have formed: "\<forall>p\<in>set ps. pattern_formed p" and scope: "pattern_forest_variables ps\<subseteq>set Vs"
    using pattern_record_formed[OF rec] by (auto simp: pattern_forest_variables_def)
  have domain: "rel_dom (set xs)=set Vs"
    using table by (simp only: binding_admission_on_values) (auto simp: term_bindings_formed_def)
  obtain ts where inst: "list_all2 (pattern_instance (set xs)) ps ts"
    using instantiated_pattern_list_exists[OF formed, where B="set xs"] scope domain by blast
  have positive: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
    by (rule record_instantiation_complete[OF source table rec order used inst])
  show ?thesis
  proof (rule ex1I[of _ ts])
    show "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term ts)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system" by (rule positive)
  next
    fix us
    assume other: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (data_list_term us)
      (data_list_term (map Payload_Term Us)) (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
    show "us=ts" using record_instantiation_result_unique[OF source positive other] by simp
  qed
qed

text \<open>
  The actual record determines every socket and field root in represented
  order. Complete row projections supply both lists to the vector reader.
  Even an empty record retains its source artifact and root check.

  The record and socket occurrences are counted together with the vector
  interior, and the whole interior is separate from external slots and the
  declared scope. Used variables and slots come unchanged from the vector.
  Its complete-table admission needs no repeated enclosing check.

  The exact contract covers every term and every complete environment,
  scope, table, and metadata presentation. Ordered field results and metadata
  sets are unique, and every valid record with complete formed bindings has
  one result. This structural reading does not evaluate a material equation.
\<close>

end
