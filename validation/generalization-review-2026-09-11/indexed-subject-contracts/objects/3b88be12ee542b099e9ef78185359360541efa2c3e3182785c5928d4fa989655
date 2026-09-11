theory Factor_Schema_Slot_Reading
  imports Factor_Premise_Slot_Reading
begin

section \<open>The actual binder, head, and premise-family endpoints\<close>

abbreviation schema_slot_reading_result :: "factor_term \<Rightarrow> bool" where
  "schema_slot_reading_result z \<equiv> \<exists>E e u r k.
    z=citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k) \<and>
    environment_value_presents E e \<and> k\<in>native_schema_slots E u r"

definition schema_conclusion_slot_schema :: "(nat,nat,nat) factor_schema" where
  "schema_conclusion_slot_schema=data_rule
    (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 10)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 7),
         Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8),Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 9)])),
     (2,54,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 7)) (Pattern_Variable 11)),
     (3,55,pattern_instantiation_pattern data_x data_y (Pattern_Variable 11) (Pattern_Variable 12)
       (Pattern_Variable 8) (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 16)),
     (4,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 16) (Pattern_Variable 17)))}"

definition schema_premise_slot_schema :: "(nat,nat,nat) factor_schema" where
  "schema_premise_slot_schema=data_rule
    (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 10)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 7),
         Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8),Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 9)])),
     (2,54,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 7)) (Pattern_Variable 11)),
     (3,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 9)) (Pattern_Variable 12)),
     (4,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14))
       (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 15))),
     (5,103,scope_slot_pattern data_x data_y (Pattern_Variable 11) (Pattern_Variable 14) data_w)}"

definition schema_slot_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "schema_slot_reading_clauses={(0,schema_conclusion_slot_schema),(1,schema_premise_slot_schema)}"

definition schema_slot_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_slot_reading_system=add_view_definition premise_slot_reading_system 104 data_x schema_slot_reading_clauses"

lemma schema_slot_reading_system_formed [simp]: "schema_system_formed schema_slot_reading_system"
  unfolding schema_slot_reading_system_def
  by (rule add_recursive_definition_formed[OF premise_slot_reading_system_formed])
    (auto simp: schema_slot_reading_clauses_def schema_conclusion_slot_schema_def schema_premise_slot_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_slot_reading_definitions [simp]:
  "system_definitions schema_slot_reading_system=insert 104 (system_definitions premise_slot_reading_system)"
  by (simp add: schema_slot_reading_system_def)

lemma schema_slot_reading_call:
  "schema_call_formed schema_slot_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_slot_reading_system \<and> term_formed t"
  using added_variable_calls[OF premise_slot_reading_system_formed
    schema_slot_reading_system_formed[unfolded schema_slot_reading_system_def] premise_slot_reading_call]
  by (simp only: schema_slot_reading_system_def[symmetric])

lemma schema_slot_reading_old_meaning:
  assumes "d\<in>system_definitions premise_slot_reading_system"
  shows "(d,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning premise_slot_reading_system"
  using added_definition_preserves_old(2)[OF premise_slot_reading_system_formed
    schema_slot_reading_system_formed[unfolded schema_slot_reading_system_def], of d t] assms
  by (auto simp: schema_slot_reading_system_def)

lemma schema_slot_reading_clause [simp]:
  "((104,c),S)\<in>system_clauses schema_slot_reading_system \<longleftrightarrow> (c,S)\<in>schema_slot_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses premise_slot_reading_system \<Longrightarrow>
    d\<in>system_definitions premise_slot_reading_system" for d c S
    using premise_slot_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((104,c),S)\<notin>system_clauses premise_slot_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_slot_reading_system_def)
qed

lemma schema_slot_reading_components:
  "(37,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(54,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (54,t)\<in>positive_meaning binder_admission_system"
  "(55,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (55,t)\<in>positive_meaning pattern_instantiation_system"
  "(32,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(5,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(103,t)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> (103,t)\<in>positive_meaning premise_slot_reading_system"
  using schema_slot_reading_old_meaning[of 37 t] premise_slot_reading_pattern_meaning[of 37 t]
    pattern_instantiation_components(6)[of t]
    schema_slot_reading_old_meaning[of 34 t] premise_slot_reading_pattern_meaning[of 34 t]
    pattern_instantiation_components(7)[of t]
    schema_slot_reading_old_meaning[of 54 t] premise_slot_reading_pattern_meaning[of 54 t]
    pattern_instantiation_old_meaning[of 54 t]
    schema_slot_reading_old_meaning[of 55 t] premise_slot_reading_pattern_meaning[of 55 t]
    schema_slot_reading_old_meaning[of 32 t] premise_slot_reading_pattern_meaning[of 32 t]
    pattern_instantiation_old_meaning[of 32 t] binder_admission_components(2)[of t]
    schema_slot_reading_old_meaning[of 5 t] premise_slot_reading_components(3)[of t]
    schema_slot_reading_old_meaning[of 103 t] by auto

lemma schema_conclusion_slot_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p b,Pair_Term q c,Pair_Term s m]))
      \<in>positive_meaning record_admission_system"
    and scope: "(54,rooted_rows_argument a b v)\<in>positive_meaning binder_admission_system"
    and reading: "(55,pattern_instantiation_argument e u v table c t w i ks)\<in>positive_meaning pattern_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term k (Pair_Term ks rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed k" "term_formed p" "term_formed q" "term_formed s" "term_formed b" "term_formed c" "term_formed m" "term_formed a" "term_formed v" "term_formed table" "term_formed t" "term_formed w" "term_formed i" "term_formed ks" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope]]
      schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then k else if j=4 then p else if j=5 then q else if j=6 then s else if j=7 then b else if j=8 then c else if j=9 then m else if j=10 then a else if j=11 then v else if j=12 then table else if j=13 then t else if j=14 then w else if j=15 then i else if j=16 then ks else rest"
  have result: "(104,evaluate_pattern ?h (schema_conclusion schema_conclusion_slot_schema))\<in>positive_meaning schema_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use lookup rec scope reading member formed in \<open>auto simp: schema_slot_reading_clauses_def schema_conclusion_slot_schema_def
        schema_variables_def schema_slot_reading_call schema_slot_reading_components\<close>)
  show ?thesis using result by (simp add: schema_conclusion_slot_schema_def)
qed

lemma schema_premise_slot_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p b,Pair_Term q c,Pair_Term s m]))
      \<in>positive_meaning record_admission_system"
    and scope: "(54,rooted_rows_argument a b v)\<in>positive_meaning binder_admission_system"
    and reading: "(32,rooted_rows_argument a m rows)\<in>positive_meaning family_admission_system"
    and selected: "selected_data_member (Pair_Term socket root) rows"
    and needed: "(103,scope_slot_argument e u v root k)\<in>positive_meaning premise_slot_reading_system"
  shows "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term (Pair_Term socket root) (Pair_Term rows rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed k" "term_formed p" "term_formed q" "term_formed s" "term_formed b" "term_formed c" "term_formed m" "term_formed a" "term_formed v" "term_formed rows" "term_formed socket" "term_formed root" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope]]
      schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]]
      schema_call_formed_target[OF positive_meaning_formed[OF needed]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then k else if j=4 then p else if j=5 then q else if j=6 then s else if j=7 then b else if j=8 then c else if j=9 then m else if j=10 then a else if j=11 then v else if j=12 then rows else if j=13 then socket else if j=14 then root else rest"
  have result: "(104,evaluate_pattern ?h (schema_conclusion schema_premise_slot_schema))\<in>positive_meaning schema_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use lookup rec scope reading member needed formed in \<open>auto simp: schema_slot_reading_clauses_def schema_premise_slot_schema_def
        schema_variables_def schema_slot_reading_call schema_slot_reading_components\<close>)
  show ?thesis using result by (simp add: schema_premise_slot_schema_def)
qed

theorem schema_slot_reading_sound:
  assumes holds: "(104,z)\<in>positive_meaning schema_slot_reading_system"
  shows "schema_slot_reading_result z"
proof -
  have consequence: "(104,z)\<in>schema_consequences schema_slot_reading_system (positive_meaning schema_slot_reading_system)"
    using holds positive_meaning_unfold[of schema_slot_reading_system] by blast
  obtain cl S h where clause: "((104,cl),S)\<in>system_clauses schema_slot_reading_system"
    and head: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning schema_slot_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have alternatives: "S=schema_conclusion_slot_schema \<or> S=schema_premise_slot_schema"
    using clause by (auto simp: schema_slot_reading_clauses_def)
  have lookup: "(37,artifact_lookup_argument (h 0) (h 1) (h 10))\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument (h 10) (h 2)
      (data_list_term [Pair_Term (h 4) (h 7),Pair_Term (h 5) (h 8),Pair_Term (h 6) (h 9)]))
      \<in>positive_meaning record_admission_system"
    and owned_scope: "(54,rooted_rows_argument (h 10) (h 7) (h 11))\<in>positive_meaning binder_admission_system"
    using support alternatives
    by (auto simp: schema_conclusion_slot_schema_def schema_premise_slot_schema_def schema_slot_reading_components)
  obtain E u R where source: "environment_value_presents E (h 0)" and use: "h 1=use_data_term u"
    and art: "artifact_at E u R" and artifact_value: "artifact_value_presents R (h 10)"
    using lookup by (auto simp: artifact_lookup_exact)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain r p b q c s m where fields: "h 2=Payload_Term r" "h 7=Payload_Term b"
    "h 8=Payload_Term c" "h 9=Payload_Term m" and raw_record: "record_at R r [p,q,s] [b,c,m]"
    using rec by (simp only: record_admission_three_fields[OF artifact_value]) blast
  obtain Vs where scope: "h 11=data_list_term (map Payload_Term Vs)" "distinct Vs" "binder_scope_at R b (set Vs)"
    using owned_scope by (auto simp: fields(2) binder_admission_at_source[OF artifact_value])
  have result_slot: "\<exists>j. h 3=Payload_Term j \<and> j\<in>native_schema_slots E u r"
    using alternatives
  proof
    assume schema: "S=schema_conclusion_slot_schema"
    have reading: "(55,pattern_instantiation_argument (h 0) (h 1) (h 11) (h 12) (h 8) (h 13) (h 14) (h 15) (h 16))
        \<in>positive_meaning pattern_instantiation_system"
      and selected: "selected_data_member (h 3) (h 16)"
      using support by (auto simp: schema schema_conclusion_slot_schema_def schema_slot_reading_components)
    obtain pat Is Ks where quote: "pattern_quoted_at E u (set Vs) c pat (set Is) (set Ks)"
      and slots: "h 16=data_list_term (map Payload_Term Ks)"
      using reading[unfolded use fields scope(1)]
      by (auto simp: pattern_instantiation_at_source[OF source]
        inj_eq[OF use_data_term_injective] data_list_term_injective injective_mapped_lists[OF payload_term_inj])
    obtain j where member: "h 3=Payload_Term j" "j\<in>set Ks"
      using selected by (auto simp: slots selected_data_member_exact data_list_term_injective)
    have needed: "j\<in>native_schema_slots E u r"
      by (simp only: native_schema_slots_from_fields[OF ef art raw_record scope(3)])
        (use quote member(2) in \<open>auto simp: pattern_slots_def\<close>)
    show ?thesis using member(1) needed by blast
  next
    assume schema: "S=schema_premise_slot_schema"
    have reading: "(32,rooted_rows_argument (h 10) (h 9) (h 12))\<in>positive_meaning family_admission_system"
      and selected: "selected_data_member (Pair_Term (h 13) (h 14)) (h 12)"
      and child: "(103,scope_slot_argument (h 0) (h 1) (h 11) (h 14) (h 3))\<in>positive_meaning premise_slot_reading_system"
      using support by (auto simp: schema schema_premise_slot_schema_def schema_slot_reading_components)
    obtain a where endpoint: "h 14=Payload_Term a" "a\<in>family_endpoints E u m"
      using reading[unfolded fields(4)] selected family_endpoint_observation[OF ef art artifact_value, of m "h 14"] by blast
    have needed_at: "\<exists>j. h 3=Payload_Term j \<and> j\<in>native_premise_slots E u (set Vs) a"
      using child[unfolded use scope(1) endpoint(1)]
      by (auto simp: premise_slot_reading_at_source[OF source]
        inj_eq[OF use_data_term_injective] data_list_term_injective injective_mapped_lists[OF payload_term_inj])
    then obtain j where member: "h 3=Payload_Term j" "j\<in>native_premise_slots E u (set Vs) a" by blast
    have needed: "j\<in>native_schema_slots E u r"
      by (simp only: native_schema_slots_from_fields[OF ef art raw_record scope(3)])
        (use endpoint(2) member(2) in \<open>auto simp: native_premise_family_slots_def\<close>)
    show ?thesis using member(1) needed by blast
  qed
  obtain j where member: "h 3=Payload_Term j" "j\<in>native_schema_slots E u r" using result_slot by blast
  have shape: "z=citation_observation_argument (h 0) (h 1) (h 2) (h 3)"
    using head alternatives by (auto simp: schema_conclusion_slot_schema_def schema_premise_slot_schema_def)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ j])
      (use source use fields(1) member shape in auto)
qed

theorem schema_slot_reading_complete:
  assumes source: "environment_value_presents E e" and slot: "k\<in>native_schema_slots E u r"
  shows "(104,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
    \<in>positive_meaning schema_slot_reading_system"
proof -
  obtain R ps b c m V where art: "artifact_at E u R" and raw_record: "record_at R r ps [b,c,m]"
    and owned_scope: "binder_scope_at R b V" and member: "k\<in>pattern_slots E u V c \<union> native_premise_family_slots E u V m"
    using slot by (auto simp: native_schema_slots_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef art by (simp add: environment_formed_def)
  obtain a where artifact_value: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using art artifact_value by (auto simp: artifact_lookup_at_source[OF source])
  have length: "length ps=Suc (Suc (Suc 0))" using record_at_preserves_socket_occurrences[OF raw_record] by simp
  obtain p q s where ports: "ps=[p,q,s]"
    using length by (auto simp only: length_Suc_conv length_0_conv)
  have rec: "(34,rooted_rows_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term p) (Payload_Term b),Pair_Term (Payload_Term q) (Payload_Term c),
        Pair_Term (Payload_Term s) (Payload_Term m)]))\<in>positive_meaning record_admission_system"
    using raw_record by (simp only: record_admission_three_fields[OF artifact_value]) (auto simp: ports)
  obtain Vs where order: "distinct Vs" "set Vs=V"
    using finite_distinct_list[OF binder_scope_properties(1)[OF owned_scope]] by blast
  have scope: "(54,rooted_rows_argument a (Payload_Term b) (data_list_term (map Payload_Term Vs)))
      \<in>positive_meaning binder_admission_system"
    using owned_scope order by (simp add: binder_admission_on_values[OF artifact_value])
  have bytes: "\<forall>x\<in>set Vs. octets_formed x"
    using schema_call_formed_target[OF positive_meaning_formed[OF scope]] by (auto simp: data_list_term_formed)
  show ?thesis
  proof (cases "k\<in>pattern_slots E u V c")
    case True
    obtain p I K where quote: "pattern_quoted_at E u (set Vs) c p I K" and chosen: "k\<in>K"
      using True order(2) by (auto simp: pattern_slots_def)
    obtain table t w i ks where reading:
      "(55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
        table (Payload_Term c) t w i ks)\<in>positive_meaning pattern_instantiation_system"
      and selected: "selected_data_member (Payload_Term k) ks"
      by (rule pattern_slot_observation[OF quote source order(1) bytes chosen]) blast
    show ?thesis by (rule schema_conclusion_slot_step[OF lookup rec scope reading selected])
  next
    case False
    obtain root where endpoint: "root\<in>family_endpoints E u m"
      and needed: "k\<in>native_premise_slots E u (set Vs) root"
      using member False order(2) by (auto simp: native_premise_family_slots_def)
    obtain rows socket where reading: "(32,rooted_rows_argument a (Payload_Term m) rows)\<in>positive_meaning family_admission_system"
      and selected: "selected_data_member (Pair_Term socket (Payload_Term root)) rows"
      using family_endpoint_observation[OF ef art artifact_value, of m "Payload_Term root"] endpoint by blast
    have child: "(103,scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
        (Payload_Term root) (Payload_Term k))\<in>positive_meaning premise_slot_reading_system"
      by (rule premise_slot_reading_complete[OF source order(1) bytes needed])
    show ?thesis by (rule schema_premise_slot_step[OF lookup rec scope reading selected child])
  qed
qed

theorem schema_slot_reading_exact:
  "(104,z)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> schema_slot_reading_result z"
  using schema_slot_reading_sound schema_slot_reading_complete by blast

corollary schema_slot_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow>
    (\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_schema_slots E q a)"
proof
  assume holds: "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system"
  obtain F q a j where fields: "u=use_data_term q" "r=Payload_Term a" "k=Payload_Term j"
    and other_source: "environment_value_presents F e" and slot: "j\<in>native_schema_slots F q a"
    using holds by (auto simp: schema_slot_reading_exact)
  have same: "F=E" by (rule environment_value_presents_unique[OF other_source source])
  show "\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_schema_slots E q a"
    by (rule exI[of _ q], rule exI[of _ a], rule exI[of _ j]) (use fields slot same in auto)
next
  assume "\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_schema_slots E q a"
  then obtain q a j where fields: "u=use_data_term q" "r=Payload_Term a" "k=Payload_Term j"
    and slot: "j\<in>native_schema_slots E q a" by blast
  show "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system"
    using schema_slot_reading_complete[OF source slot] by (simp only: fields)
qed

corollary schema_slot_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(104,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
      \<in>positive_meaning schema_slot_reading_system \<longleftrightarrow> k\<in>native_schema_slots E u r"
  by (simp add: schema_slot_reading_at_source[OF source] inj_eq[OF use_data_term_injective])

corollary schema_slot_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(104,citation_observation_argument e u r k)\<in>positive_meaning schema_slot_reading_system \<longleftrightarrow>
    (104,citation_observation_argument f u r k)\<in>positive_meaning schema_slot_reading_system"
  by (simp only: schema_slot_reading_at_source[OF assms(1)] schema_slot_reading_at_source[OF assms(2)])

corollary schema_slot_reading_bound:
  assumes source: "environment_value_presents E e"
    and reading: "(104,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
      \<in>positive_meaning schema_slot_reading_system"
  shows "(u,k)\<in>rel_dom (environment_bindings E)"
  using reading by (simp only: schema_slot_reading_on_values[OF source]) (rule native_schema_slots_bound)

text \<open>
  Both branches recover the actual three-field record and binder. A demanded
  slot comes from the conclusion pattern or a premise at an actual family
  endpoint. This recognizes the existing slot projection even when another
  part of the enclosing schema fails admission. Whole-schema formation and
  instance validity remain separate judgments.
\<close>

end
