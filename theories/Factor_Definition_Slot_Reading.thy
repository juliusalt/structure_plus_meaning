theory Factor_Definition_Slot_Reading
  imports Factor_Schema_Slot_Reading
begin

section \<open>The interface and every actual schema-family endpoint\<close>

abbreviation definition_slot_reading_result :: "factor_term \<Rightarrow> bool" where
  "definition_slot_reading_result z \<equiv> \<exists>E e u r k.
    z=citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k) \<and>
    environment_value_presents E e \<and> k\<in>native_definition_slots E u r"

definition definition_interface_slot_schema :: "(nat,nat,nat) factor_schema" where
  "definition_interface_slot_schema=data_rule
    (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 8)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 6),
         Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7)])),
     (2,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 6) (Pattern_Variable 9)
       (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)),
     (3,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 12) (Pattern_Variable 13)))}"

definition definition_schema_slot_schema :: "(nat,nat,nat) factor_schema" where
  "definition_schema_slot_schema=data_rule
    (citation_observation_pattern data_x data_y data_z data_w)
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 8)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 6),
         Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7)])),
     (2,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 7)) (Pattern_Variable 9)),
     (3,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11))
       (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12))),
     (4,104,citation_observation_pattern data_x data_y (Pattern_Variable 11) data_w)}"

definition definition_slot_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "definition_slot_reading_clauses={(0,definition_interface_slot_schema),(1,definition_schema_slot_schema)}"

definition definition_slot_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "definition_slot_reading_system=add_view_definition schema_slot_reading_system 105 data_x definition_slot_reading_clauses"

lemma definition_slot_reading_system_formed [simp]: "schema_system_formed definition_slot_reading_system"
  unfolding definition_slot_reading_system_def
  by (rule add_recursive_definition_formed[OF schema_slot_reading_system_formed])
    (auto simp: definition_slot_reading_clauses_def definition_interface_slot_schema_def definition_schema_slot_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma definition_slot_reading_definitions [simp]:
  "system_definitions definition_slot_reading_system=insert 105 (system_definitions schema_slot_reading_system)"
  by (simp add: definition_slot_reading_system_def)

lemma definition_slot_reading_call:
  "schema_call_formed definition_slot_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions definition_slot_reading_system \<and> term_formed t"
  using added_variable_calls[OF schema_slot_reading_system_formed
    definition_slot_reading_system_formed[unfolded definition_slot_reading_system_def] schema_slot_reading_call]
  by (simp only: definition_slot_reading_system_def[symmetric])

lemma definition_slot_reading_old_meaning:
  assumes "d\<in>system_definitions schema_slot_reading_system"
  shows "(d,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning schema_slot_reading_system"
  using added_definition_preserves_old(2)[OF schema_slot_reading_system_formed
    definition_slot_reading_system_formed[unfolded definition_slot_reading_system_def], of d t] assms
  by (auto simp: definition_slot_reading_system_def)

lemma definition_slot_reading_clause [simp]:
  "((105,c),S)\<in>system_clauses definition_slot_reading_system \<longleftrightarrow> (c,S)\<in>definition_slot_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses schema_slot_reading_system \<Longrightarrow>
    d\<in>system_definitions schema_slot_reading_system" for d c S
    using schema_slot_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((105,c),S)\<notin>system_clauses schema_slot_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: definition_slot_reading_system_def)
qed

lemma definition_slot_reading_scoped:
  "(56,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (56,t)\<in>positive_meaning scoped_instantiation_system"
  using definition_slot_reading_old_meaning[of 56 t] schema_slot_reading_old_meaning[of 56 t]
    premise_slot_reading_material_meaning[of 56 t] material_instantiation_old_meaning[of 56 t]
    record_instantiation_old_meaning[of 56 t] vector_instantiation_old_meaning[of 56 t]
    row_values_old_meaning[of 56 t] application_reading_old_meaning[of 56 t]
    prospective_instantiation_old_meaning[of 56 t] by auto

lemma definition_slot_reading_components:
  "(37,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(5,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(104,t)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> (104,t)\<in>positive_meaning schema_slot_reading_system"
  using definition_slot_reading_old_meaning[of 37 t] schema_slot_reading_components(1)[of t]
    definition_slot_reading_old_meaning[of 34 t] schema_slot_reading_components(2)[of t]
    definition_slot_reading_old_meaning[of 32 t] schema_slot_reading_components(5)[of t]
    definition_slot_reading_old_meaning[of 5 t] schema_slot_reading_components(6)[of t]
    definition_slot_reading_old_meaning[of 104 t] by auto

lemma definition_interface_slot_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p i,Pair_Term q m]))
      \<in>positive_meaning record_admission_system"
    and reading: "(56,scoped_instantiation_argument e u i b t w ks)\<in>positive_meaning scoped_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term k (Pair_Term ks rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed k" "term_formed p" "term_formed q"
    "term_formed i" "term_formed m" "term_formed a" "term_formed b" "term_formed t" "term_formed w" "term_formed ks" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then k else if j=4 then p
    else if j=5 then q else if j=6 then i else if j=7 then m else if j=8 then a else if j=9 then b
    else if j=10 then t else if j=11 then w else if j=12 then ks else rest"
  have result: "(105,evaluate_pattern ?h (schema_conclusion definition_interface_slot_schema))\<in>positive_meaning definition_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use lookup rec reading member formed in \<open>auto simp: definition_slot_reading_clauses_def definition_interface_slot_schema_def
        schema_variables_def definition_slot_reading_call definition_slot_reading_components definition_slot_reading_scoped\<close>)
  show ?thesis using result by (simp add: definition_interface_slot_schema_def)
qed

lemma definition_schema_slot_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p i,Pair_Term q m]))
      \<in>positive_meaning record_admission_system"
    and reading: "(32,rooted_rows_argument a m rows)\<in>positive_meaning family_admission_system"
    and selected: "selected_data_member (Pair_Term socket root) rows"
    and needed: "(104,citation_observation_argument e u root k)\<in>positive_meaning schema_slot_reading_system"
  shows "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term (Pair_Term socket root) (Pair_Term rows rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed k" "term_formed p" "term_formed q"
    "term_formed i" "term_formed m" "term_formed a" "term_formed rows" "term_formed socket" "term_formed root" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]]
      schema_call_formed_target[OF positive_meaning_formed[OF needed]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then k else if j=4 then p
    else if j=5 then q else if j=6 then i else if j=7 then m else if j=8 then a else if j=9 then rows
    else if j=10 then socket else if j=11 then root else rest"
  have result: "(105,evaluate_pattern ?h (schema_conclusion definition_schema_slot_schema))\<in>positive_meaning definition_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use lookup rec reading member needed formed in \<open>auto simp: definition_slot_reading_clauses_def definition_schema_slot_schema_def
        schema_variables_def definition_slot_reading_call definition_slot_reading_components\<close>)
  show ?thesis using result by (simp add: definition_schema_slot_schema_def)
qed

theorem definition_slot_reading_sound:
  assumes holds: "(105,z)\<in>positive_meaning definition_slot_reading_system"
  shows "definition_slot_reading_result z"
proof -
  have consequence: "(105,z)\<in>schema_consequences definition_slot_reading_system (positive_meaning definition_slot_reading_system)"
    using holds positive_meaning_unfold[of definition_slot_reading_system] by blast
  obtain cl S h where clause: "((105,cl),S)\<in>system_clauses definition_slot_reading_system"
    and head: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning definition_slot_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have alternatives: "S=definition_interface_slot_schema \<or> S=definition_schema_slot_schema"
    using clause by (auto simp: definition_slot_reading_clauses_def)
  have lookup: "(37,artifact_lookup_argument (h 0) (h 1) (h 8))\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument (h 8) (h 2)
      (data_list_term [Pair_Term (h 4) (h 6),Pair_Term (h 5) (h 7)]))\<in>positive_meaning record_admission_system"
    using support alternatives
    by (auto simp: definition_interface_slot_schema_def definition_schema_slot_schema_def definition_slot_reading_components)
  obtain E u R where source: "environment_value_presents E (h 0)" and use: "h 1=use_data_term u"
    and art: "artifact_at E u R" and artifact_value: "artifact_value_presents R (h 8)"
    using lookup by (auto simp: artifact_lookup_exact)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain r p i q m where fields: "h 2=Payload_Term r" "h 6=Payload_Term i" "h 7=Payload_Term m"
    and raw_record: "record_at R r [p,q] [i,m]"
    using rec by (simp only: record_admission_pair_fields[OF artifact_value]) blast
  have result_slot: "\<exists>j. h 3=Payload_Term j \<and> j\<in>native_definition_slots E u r"
    using alternatives
  proof
    assume schema: "S=definition_interface_slot_schema"
    have reading: "(56,scoped_instantiation_argument (h 0) (h 1) (h 6) (h 9) (h 10) (h 11) (h 12))
        \<in>positive_meaning scoped_instantiation_system"
      and selected: "selected_data_member (h 3) (h 12)"
      using support by (auto simp: schema definition_interface_slot_schema_def definition_slot_reading_components definition_slot_reading_scoped)
    obtain pat Is Ks where quote: "scoped_pattern_at E u i pat (set Is) (set Ks)"
      and slots: "h 12=data_list_term (map Payload_Term Ks)"
      using reading[unfolded use fields]
      by (auto simp: scoped_instantiation_at_source[OF source] inj_eq[OF use_data_term_injective])
    obtain j where member: "h 3=Payload_Term j" "j\<in>set Ks"
      using selected by (auto simp: slots selected_data_member_exact data_list_term_injective)
    have needed: "j\<in>native_definition_slots E u r"
      by (simp only: native_definition_slots_from_fields[OF ef art raw_record])
        (use quote member(2) in \<open>auto simp: scoped_pattern_slots_def\<close>)
    show ?thesis using member(1) needed by blast
  next
    assume schema: "S=definition_schema_slot_schema"
    have reading: "(32,rooted_rows_argument (h 8) (h 7) (h 9))\<in>positive_meaning family_admission_system"
      and selected: "selected_data_member (Pair_Term (h 10) (h 11)) (h 9)"
      and child: "(104,citation_observation_argument (h 0) (h 1) (h 11) (h 3))\<in>positive_meaning schema_slot_reading_system"
      using support by (auto simp: schema definition_schema_slot_schema_def definition_slot_reading_components)
    obtain a where endpoint: "h 11=Payload_Term a" "a\<in>family_endpoints E u m"
      using reading[unfolded fields(3)] selected family_endpoint_observation[OF ef art artifact_value, of m "h 11"] by blast
    obtain j where member: "h 3=Payload_Term j" "j\<in>native_schema_slots E u a"
      using child[unfolded use endpoint(1)]
      by (auto simp: schema_slot_reading_at_source[OF source] inj_eq[OF use_data_term_injective])
    have needed: "j\<in>native_definition_slots E u r"
      by (simp only: native_definition_slots_from_fields[OF ef art raw_record])
        (use endpoint(2) member(2) in \<open>auto simp: native_schema_family_slots_def\<close>)
    show ?thesis using member(1) needed by blast
  qed
  obtain j where member: "h 3=Payload_Term j" "j\<in>native_definition_slots E u r" using result_slot by blast
  have shape: "z=citation_observation_argument (h 0) (h 1) (h 2) (h 3)"
    using head alternatives by (auto simp: definition_interface_slot_schema_def definition_schema_slot_schema_def)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ j])
      (use source use fields(1) member shape in auto)
qed

theorem definition_slot_reading_complete:
  assumes source: "environment_value_presents E e" and slot: "k\<in>native_definition_slots E u r"
  shows "(105,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
    \<in>positive_meaning definition_slot_reading_system"
proof -
  obtain R ps i m where art: "artifact_at E u R" and raw_record: "record_at R r ps [i,m]"
    and member: "k\<in>scoped_pattern_slots E u i \<union> native_schema_family_slots E u m"
    using slot by (auto simp: native_definition_slots_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef art by (simp add: environment_formed_def)
  obtain a where artifact_value: "artifact_value_presents R a" using artifact_value_presents_total[OF rf] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using art artifact_value by (auto simp: artifact_lookup_at_source[OF source])
  have length: "length ps=Suc (Suc 0)" using record_at_preserves_socket_occurrences[OF raw_record] by simp
  obtain p q where ports: "ps=[p,q]" using length by (auto simp only: length_Suc_conv length_0_conv)
  have rec: "(34,rooted_rows_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term p) (Payload_Term i),Pair_Term (Payload_Term q) (Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    using raw_record by (simp only: record_admission_pair_fields[OF artifact_value]) (auto simp: ports)
  show ?thesis
  proof (cases "k\<in>scoped_pattern_slots E u i")
    case True
    obtain pat I K where quote: "scoped_pattern_at E u i pat I K" and chosen: "k\<in>K"
      using True by (auto simp: scoped_pattern_slots_def)
    obtain b t w ks where reading: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i) b t w ks)
        \<in>positive_meaning scoped_instantiation_system" and selected: "selected_data_member (Payload_Term k) ks"
      by (rule scoped_slot_observation[OF quote source chosen]) blast
    show ?thesis by (rule definition_interface_slot_step[OF lookup rec reading selected])
  next
    case False
    obtain root where endpoint: "root\<in>family_endpoints E u m" and needed: "k\<in>native_schema_slots E u root"
      using member False by (auto simp: native_schema_family_slots_def)
    obtain rows socket where reading: "(32,rooted_rows_argument a (Payload_Term m) rows)\<in>positive_meaning family_admission_system"
      and selected: "selected_data_member (Pair_Term socket (Payload_Term root)) rows"
      using family_endpoint_observation[OF ef art artifact_value, of m "Payload_Term root"] endpoint by blast
    have child: "(104,citation_observation_argument e (use_data_term u) (Payload_Term root) (Payload_Term k))
        \<in>positive_meaning schema_slot_reading_system"
      by (rule schema_slot_reading_complete[OF source needed])
    show ?thesis by (rule definition_schema_slot_step[OF lookup rec reading selected child])
  qed
qed

theorem definition_slot_reading_exact:
  "(105,z)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> definition_slot_reading_result z"
  using definition_slot_reading_sound definition_slot_reading_complete by blast

corollary definition_slot_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow>
    (\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_definition_slots E q a)"
proof
  assume holds: "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system"
  obtain F q a j where fields: "u=use_data_term q" "r=Payload_Term a" "k=Payload_Term j"
    and other_source: "environment_value_presents F e" and slot: "j\<in>native_definition_slots F q a"
    using holds by (auto simp: definition_slot_reading_exact)
  have same: "F=E" by (rule environment_value_presents_unique[OF other_source source])
  show "\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_definition_slots E q a"
    by (rule exI[of _ q], rule exI[of _ a], rule exI[of _ j]) (use fields slot same in auto)
next
  assume "\<exists>q a j. u=use_data_term q \<and> r=Payload_Term a \<and> k=Payload_Term j \<and> j\<in>native_definition_slots E q a"
  then obtain q a j where fields: "u=use_data_term q" "r=Payload_Term a" "k=Payload_Term j"
    and slot: "j\<in>native_definition_slots E q a" by blast
  show "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system"
    using definition_slot_reading_complete[OF source slot] by (simp only: fields)
qed

corollary definition_slot_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(105,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
      \<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> k\<in>native_definition_slots E u r"
  by (simp add: definition_slot_reading_at_source[OF source] inj_eq[OF use_data_term_injective])

corollary definition_slot_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(105,citation_observation_argument e u r k)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow>
    (105,citation_observation_argument f u r k)\<in>positive_meaning definition_slot_reading_system"
  by (simp only: definition_slot_reading_at_source[OF assms(1)] definition_slot_reading_at_source[OF assms(2)])

corollary definition_slot_reading_bound:
  assumes source: "environment_value_presents E e"
    and reading: "(105,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term k))
      \<in>positive_meaning definition_slot_reading_system"
  shows "(u,k)\<in>rel_dom (environment_bindings E)"
  using reading by (simp only: definition_slot_reading_on_values[OF source]) (rule native_definition_slots_bound)

section \<open>Three fixed native entries before every future operand\<close>

abbreviation slot_reading_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "slot_reading_operation_result d z \<equiv>
    (d=103 \<and> premise_slot_reading_result z) \<or>
    (d=104 \<and> schema_slot_reading_result z) \<or>
    (d=105 \<and> definition_slot_reading_result z)"

lemma slot_reading_operations_exact:
  assumes "d\<in>{103,104,105}"
  shows "(d,z)\<in>positive_meaning definition_slot_reading_system \<longleftrightarrow> slot_reading_operation_result d z"
proof -
  consider (premise_entry) "d=103" | (schema_entry) "d=104" | (definition_entry) "d=105"
    using assms by auto
  then show ?thesis
  proof cases
    case premise_entry
    then show ?thesis by (simp add: definition_slot_reading_old_meaning schema_slot_reading_old_meaning premise_slot_reading_exact)
  next
    case schema_entry
    then show ?thesis by (simp add: definition_slot_reading_components(5) schema_slot_reading_exact)
  next
    case definition_entry
    then show ?thesis by (simp add: definition_slot_reading_exact)
  qed
qed

theorem native_slot_reading_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {103::nat,104,105} \<and>
    (\<forall>d\<in>{103,104,105}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> slot_reading_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions definition_slot_reading_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions definition_slot_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed definition_slot_reading_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning definition_slot_reading_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF definition_slot_reading_system_formed] by blast
  have sites: "inj_on g {103,104,105}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {103,104,105}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{103,104,105}" and tf: "term_formed t"
    have member: "d\<in>system_definitions definition_slot_reading_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed definition_slot_reading_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning definition_slot_reading_system"
      using future[rule_format, OF member tf] by blast
    have app_formed: "native_application_formed F pu [] au []"
      using parts(7) tf member by (simp add: definition_slot_reading_call)
    have meaning: "native_positive_holds F pu [] au [] \<longleftrightarrow> slot_reading_operation_result d t"
      by (simp only: parts(8) slot_reading_operations_exact[OF selected])
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> slot_reading_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts(1-6) app_formed meaning in blast)
  qed
qed

text \<open>
  The two-field record fixes the interface and schema family. A slot is read
  from its actual scoped interface or an actual schema endpoint, preserving
  the existing partial projection independently of complete definition
  admission. Every reported slot is bound in the same represented environment.

  These three entries add six ordinary clauses. Their all-term contracts
  preserve every complete environment presentation and all prior meanings.
  One fixed closed native program supplies three distinct sites before any
  future formed argument, with its canonical environment unchanged.
\<close>

end
