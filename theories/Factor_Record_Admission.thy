theory Factor_Record_Admission
  imports Factor_Family_Admission RRA_Record_Chains
begin

section \<open>An ordinary recursion follows every complete successor head\<close>

definition socket_chain_last_schema :: "(nat,nat,nat) factor_schema" where
  "socket_chain_last_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y)
      (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Payload [])))
    {(0,29,headed_material_pattern data_x data_z (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload [])),
     (1,3,Pattern_Pair data_z data_y)}"

definition socket_chain_step_schema :: "(nat,nat,nat) factor_schema" where
  "socket_chain_step_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y)
      (Pattern_Pair (Pattern_Pair data_z data_w)
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6))))
    {(0,29,headed_material_pattern data_x data_z
        (Pattern_Pair (Pattern_Pair data_z (Pattern_Variable 4)) (Pattern_Payload []))
        (Pattern_Payload []) (Pattern_Payload [])),
     (1,3,Pattern_Pair data_z data_y),
     (2,33,Pattern_Pair (Pattern_Pair data_x data_y)
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6)))}"

definition socket_chain_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "socket_chain_clauses={(0,context_list_nil_schema),(1,socket_chain_last_schema),(2,socket_chain_step_schema)}"

definition socket_chain_system :: "(nat,nat,nat,nat) schema_system" where
  "socket_chain_system=add_view_definition family_admission_system 33 data_x socket_chain_clauses"

lemma socket_chain_system_formed [simp]: "schema_system_formed socket_chain_system"
  unfolding socket_chain_system_def
  by (rule add_recursive_definition_formed[OF family_admission_system_formed])
    (auto simp: socket_chain_clauses_def context_list_nil_schema_def socket_chain_last_schema_def socket_chain_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma socket_chain_definitions [simp]:
  "system_definitions socket_chain_system=insert 33 (system_definitions family_admission_system)"
  by (simp add: socket_chain_system_def)

lemma socket_chain_call:
  "schema_call_formed socket_chain_system d t \<longleftrightarrow>
    d\<in>system_definitions socket_chain_system \<and> term_formed t"
  using added_variable_calls[OF family_admission_system_formed
    socket_chain_system_formed[unfolded socket_chain_system_def] family_admission_call]
  by (simp only: socket_chain_system_def[symmetric])

lemma socket_chain_old_meaning:
  assumes "d\<in>system_definitions family_admission_system"
  shows "(d,t)\<in>positive_meaning socket_chain_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning family_admission_system"
  using added_definition_preserves_old(2)[OF family_admission_system_formed
    socket_chain_system_formed[unfolded socket_chain_system_def], of d t] assms
  by (auto simp: socket_chain_system_def)

lemma socket_chain_clause [simp]:
  "((33,c),S)\<in>system_clauses socket_chain_system \<longleftrightarrow> (c,S)\<in>socket_chain_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses family_admission_system \<Longrightarrow>
    d\<in>system_definitions family_admission_system" for d c S
    using family_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((33,c),S)\<notin>system_clauses family_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: socket_chain_system_def)
qed

lemma socket_chain_components:
  "(29,t)\<in>positive_meaning socket_chain_system \<longleftrightarrow>
    (29,t)\<in>positive_meaning headed_material_system"
  "(3,t)\<in>positive_meaning socket_chain_system \<longleftrightarrow>
    (3,t)\<in>positive_meaning headed_material_system"
  using socket_chain_old_meaning[of 29 t] socket_chain_old_meaning[of 3 t]
    family_admission_headed_meaning[of 29 t] family_admission_headed_meaning[of 3 t] by auto

lemma socket_chain_valuation:
  "(33,t)\<in>positive_meaning socket_chain_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=Pair_Term (h 0) (Payload_Term [])) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=rooted_rows_argument (h 0) (h 1) (data_list_term [Pair_Term (h 2) (h 3)]) \<and>
      (29,headed_material_argument (h 0) (h 2) (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 2) (h 1))\<in>positive_meaning headed_material_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
      term_formed (h 4) \<and> term_formed (h 5) \<and> term_formed (h 6) \<and>
      t=rooted_rows_argument (h 0) (h 1)
        (Pair_Term (Pair_Term (h 2) (h 3)) (Pair_Term (Pair_Term (h 4) (h 5)) (h 6))) \<and>
      (29,headed_material_argument (h 0) (h 2) (data_list_term [Pair_Term (h 2) (h 4)])
        (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 2) (h 1))\<in>positive_meaning headed_material_system \<and>
      (33,rooted_rows_argument (h 0) (h 1) (Pair_Term (Pair_Term (h 4) (h 5)) (h 6)))
        \<in>positive_meaning socket_chain_system)"
proof -
  have ordinary: "\<And>c S. ((33,c),S)\<in>system_clauses socket_chain_system \<Longrightarrow>
    schema_material_premises S={}"
    by (auto simp: socket_chain_clauses_def context_list_nil_schema_def
      socket_chain_last_schema_def socket_chain_step_schema_def)
  have member: "33\<in>system_definitions socket_chain_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning socket_chain_system)"
  have valuation: "(33,t)\<in>positive_meaning socket_chain_system \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>socket_chain_clauses \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=socket_chain_system and d=33 and t=t, OF ordinary]
    by (simp only: socket_chain_clause socket_chain_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>socket_chain_clauses \<and> P S) \<longleftrightarrow>
    P context_list_nil_schema \<or> P socket_chain_last_schema \<or> P socket_chain_step_schema"
    for P :: "(nat,nat,nat) factor_schema \<Rightarrow> bool"
    by (auto simp: socket_chain_clauses_def)
  have nil: "?A context_list_nil_schema h \<longleftrightarrow>
    term_formed (h 0) \<and> t=Pair_Term (h 0) (Payload_Term [])" for h
    by (auto simp: context_list_nil_schema_def schema_variables_def octets_formed_def)
  have last: "?A socket_chain_last_schema h \<longleftrightarrow>
    term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
    t=rooted_rows_argument (h 0) (h 1) (data_list_term [Pair_Term (h 2) (h 3)]) \<and>
    (29,headed_material_argument (h 0) (h 2) (Payload_Term []) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system \<and>
    (3,Pair_Term (h 2) (h 1))\<in>positive_meaning headed_material_system" for h
    by (auto simp: socket_chain_last_schema_def schema_variables_def socket_chain_components octets_formed_def)
  have step: "?A socket_chain_step_schema h \<longleftrightarrow>
    term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and> term_formed (h 3) \<and>
    term_formed (h 4) \<and> term_formed (h 5) \<and> term_formed (h 6) \<and>
    t=rooted_rows_argument (h 0) (h 1)
      (Pair_Term (Pair_Term (h 2) (h 3)) (Pair_Term (Pair_Term (h 4) (h 5)) (h 6))) \<and>
    (29,headed_material_argument (h 0) (h 2) (data_list_term [Pair_Term (h 2) (h 4)])
      (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
    (3,Pair_Term (h 2) (h 1))\<in>positive_meaning headed_material_system \<and>
    (33,rooted_rows_argument (h 0) (h 1) (Pair_Term (Pair_Term (h 4) (h 5)) (h 6)))
      \<in>positive_meaning socket_chain_system" for h
    by (auto simp: socket_chain_step_schema_def schema_variables_def socket_chain_components)
  show ?thesis by (subst valuation) (simp only: clauses nil last step)
qed

lemma socket_chain_nil:
  "(33,rooted_rows_argument a r (Payload_Term []))\<in>positive_meaning socket_chain_system
    \<longleftrightarrow> term_formed a \<and> term_formed r"
proof
  assume holds: "(33,rooted_rows_argument a r (Payload_Term []))\<in>positive_meaning socket_chain_system"
  show "term_formed a \<and> term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by auto
next
  assume formed: "term_formed a \<and> term_formed r"
  show "(33,rooted_rows_argument a r (Payload_Term []))\<in>positive_meaning socket_chain_system"
    by (rule iffD2[OF socket_chain_valuation], intro disjI1 exI[of _ "\<lambda>_. Pair_Term a r"])
      (use formed in simp)
qed

lemma socket_chain_last:
  "(33,rooted_rows_argument a r (data_list_term [Pair_Term p x]))\<in>positive_meaning socket_chain_system
    \<longleftrightarrow> term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system"
proof
  assume holds: "(33,rooted_rows_argument a r (data_list_term [Pair_Term p x]))\<in>positive_meaning socket_chain_system"
  show "term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system"
    using iffD1[OF socket_chain_valuation holds] by auto
next
  assume parts: "term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
      (29,headed_material_argument a p (Payload_Term []) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term p r)\<in>positive_meaning headed_material_system"
  show "(33,rooted_rows_argument a r (data_list_term [Pair_Term p x]))\<in>positive_meaning socket_chain_system"
    by (rule iffD2[OF socket_chain_valuation], rule disjI2, rule disjI1,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then r else if i=2 then p else x"])
      (use parts in simp)
qed

lemma socket_chain_step:
  "(33,rooted_rows_argument a r (Pair_Term (Pair_Term p x) (Pair_Term (Pair_Term q y) tail)))
    \<in>positive_meaning socket_chain_system \<longleftrightarrow>
    term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
    term_formed q \<and> term_formed y \<and> term_formed tail \<and>
    (29,headed_material_argument a p (data_list_term [Pair_Term p q]) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system \<and>
    (3,Pair_Term p r)\<in>positive_meaning headed_material_system \<and>
    (33,rooted_rows_argument a r (Pair_Term (Pair_Term q y) tail))\<in>positive_meaning socket_chain_system"
proof
  assume holds: "(33,rooted_rows_argument a r (Pair_Term (Pair_Term p x) (Pair_Term (Pair_Term q y) tail)))
    \<in>positive_meaning socket_chain_system"
  show "term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
    term_formed q \<and> term_formed y \<and> term_formed tail \<and>
    (29,headed_material_argument a p (data_list_term [Pair_Term p q]) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system \<and>
    (3,Pair_Term p r)\<in>positive_meaning headed_material_system \<and>
    (33,rooted_rows_argument a r (Pair_Term (Pair_Term q y) tail))\<in>positive_meaning socket_chain_system"
    using iffD1[OF socket_chain_valuation holds] by auto
next
  assume parts: "term_formed a \<and> term_formed r \<and> term_formed p \<and> term_formed x \<and>
    term_formed q \<and> term_formed y \<and> term_formed tail \<and>
    (29,headed_material_argument a p (data_list_term [Pair_Term p q]) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system \<and>
    (3,Pair_Term p r)\<in>positive_meaning headed_material_system \<and>
    (33,rooted_rows_argument a r (Pair_Term (Pair_Term q y) tail))\<in>positive_meaning socket_chain_system"
  show "(33,rooted_rows_argument a r (Pair_Term (Pair_Term p x) (Pair_Term (Pair_Term q y) tail)))
    \<in>positive_meaning socket_chain_system"
    by (rule iffD2[OF socket_chain_valuation], rule disjI2, rule disjI2,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then r else if i=2 then p else if i=3 then x
        else if i=4 then q else if i=5 then y else tail"])
      (use parts in simp)
qed

theorem socket_chain_rows:
  assumes source: "artifact_value_presents R a" and root: "octets_formed r"
    and data: "data_elements (map address_pair_data xs)"
  shows "(33,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
    \<in>positive_meaning socket_chain_system \<longleftrightarrow> record_socket_chain R r (map fst xs)"
  using data
proof (induction xs)
  case Nil
  show ?case using artifact_value_presents_formed[OF source] root by (simp add: socket_chain_nil)
next
  case (Cons z xs)
  obtain p x where first: "z=(p,x)" by (cases z) auto
  have af: "term_formed a" using artifact_value_presents_formed[OF source] by simp
  have fields: "data_elements (map address_pair_data (z#xs))" by (rule Cons.prems)
  have pf: "octets_formed p" and xf: "octets_formed x"
    using fields by (auto simp: first address_pair_data_def)
  have tail_data: "data_elements (map address_pair_data xs)" using fields by simp
  have tail: "(33,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning socket_chain_system \<longleftrightarrow> record_socket_chain R r (map fst xs)"
    by (rule Cons.IH[OF tail_data])
  show ?case
  proof (cases xs)
    case Nil
    show ?thesis using af root pf xf
      by (simp add: first Nil address_pair_data_def socket_chain_last[simplified]
        headed_material_no_data[OF source, of p "[]", simplified] headed_material_inequality conj_ac)
  next
    case (Cons z' ys)
    obtain q y where second: "z'=(q,y)" by (cases z') auto
    have qf: "octets_formed q" and yf: "octets_formed y"
      and rest: "term_formed (data_list_term (map address_pair_data ys))"
      using fields by (auto simp: first Cons second address_pair_data_def data_list_term_formed)
    have encode: "address_pair_data (u,v)=Pair_Term (Payload_Term u) (Payload_Term v)" for u v
      by (simp add: address_pair_data_def)
    have material: "(29,headed_material_argument a (Payload_Term p)
        (data_list_term [Pair_Term (Payload_Term p) (Payload_Term q)]) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<longleftrightarrow>
      p\<in>rra_carrier (object_structure R) \<and> headed_incidence (object_structure R) p={(p,q)} \<and>
      restrict_basis {p} (object_data R)=empty_basis"
      using headed_material_no_data[OF source, of p "[(p,q)]"] by (simp add: address_pair_data_def)
    have tail_iff: "(33,rooted_rows_argument a (Payload_Term r)
        (Pair_Term (Pair_Term (Payload_Term q) (Payload_Term y)) (data_list_term (map address_pair_data ys))))
        \<in>positive_meaning socket_chain_system \<longleftrightarrow> record_socket_chain R r (q#map fst ys)"
      using tail by (simp add: Cons second encode)
    show ?thesis
      by (simp add: first Cons second encode socket_chain_step[simplified]
        material[simplified] tail_iff af root pf xf qf yf rest headed_material_inequality conj_ac)
  qed
qed

section \<open>The complete root rows must have exactly that represented order\<close>

definition record_admission_schema :: "(nat,nat,nat) factor_schema" where
  "record_admission_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,29,headed_material_pattern data_x data_y data_z (Pattern_Payload []) (Pattern_Payload [])),
     (1,33,Pattern_Pair (Pattern_Pair data_x data_y) data_z)}"

definition record_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "record_admission_system=add_view_definition socket_chain_system 34 data_x {(0,record_admission_schema)}"

lemma record_admission_system_formed [simp]: "schema_system_formed record_admission_system"
  unfolding record_admission_system_def
  by (rule add_recursive_definition_formed[OF socket_chain_system_formed])
    (auto simp: record_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma record_admission_definitions [simp]:
  "system_definitions record_admission_system=insert 34 (system_definitions socket_chain_system)"
  by (simp add: record_admission_system_def)

lemma record_admission_call:
  "schema_call_formed record_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions record_admission_system \<and> term_formed t"
  using added_variable_calls[OF socket_chain_system_formed
    record_admission_system_formed[unfolded record_admission_system_def] socket_chain_call]
  by (simp only: record_admission_system_def[symmetric])

lemma record_admission_old_meaning:
  assumes "d\<in>system_definitions socket_chain_system"
  shows "(d,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning socket_chain_system"
  using added_definition_preserves_old(2)[OF socket_chain_system_formed
    record_admission_system_formed[unfolded record_admission_system_def], of d t] assms
  by (auto simp: record_admission_system_def)

lemma record_admission_clause [simp]:
  "((34,c),S)\<in>system_clauses record_admission_system \<longleftrightarrow> (c,S)\<in>{(0,record_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses socket_chain_system \<Longrightarrow>
    d\<in>system_definitions socket_chain_system" for d c S
    using socket_chain_system_formed unfolding schema_system_formed_def by blast
  have absent: "((34,c),S)\<notin>system_clauses socket_chain_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: record_admission_system_def)
qed

lemma record_admission_components:
  "(29,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (29,t)\<in>positive_meaning headed_material_system"
  "(33,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (33,t)\<in>positive_meaning socket_chain_system"
  using record_admission_old_meaning[of 29 t] socket_chain_components(1)[of t]
    record_admission_old_meaning[of 33 t] by auto

lemma record_admission_family:
  "(32,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (32,t)\<in>positive_meaning family_admission_system"
  using record_admission_old_meaning[of 32 t] socket_chain_old_meaning[of 32 t] by auto

lemma record_admission_valuation:
  "(34,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=rooted_rows_argument (h 0) (h 1) (h 2) \<and>
      (29,headed_material_argument (h 0) (h 1) (h 2) (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (33,rooted_rows_argument (h 0) (h 1) (h 2))\<in>positive_meaning socket_chain_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: record_admission_schema_def schema_variables_def record_admission_call record_admission_components)

lemma record_admission_fields:
  "(34,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (33,rooted_rows_argument a k m)\<in>positive_meaning socket_chain_system)"
proof
  assume "(34,t)\<in>positive_meaning record_admission_system"
  then show "\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (33,rooted_rows_argument a k m)\<in>positive_meaning socket_chain_system"
    by (auto simp: record_admission_valuation)
next
  assume "\<exists>a k m. t=rooted_rows_argument a k m \<and>
      (29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
        \<in>positive_meaning headed_material_system \<and>
      (33,rooted_rows_argument a k m)\<in>positive_meaning socket_chain_system"
  then obtain a k m where parts: "t=rooted_rows_argument a k m"
    "(29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
    "(33,rooted_rows_argument a k m)\<in>positive_meaning socket_chain_system" by blast
  have formed: "term_formed a" "term_formed k" "term_formed m"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by auto
  show "(34,t)\<in>positive_meaning record_admission_system"
    by (simp only: record_admission_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then k else m"])
      (use parts formed in auto)
qed

theorem record_admission_exact:
  "(34,t)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> record_at R r (map fst xs) (map snd xs))"
proof
  assume holds: "(34,t)\<in>positive_meaning record_admission_system"
  obtain a k m where input: "t=rooted_rows_argument a k m"
    and headed: "(29,headed_material_argument a k m (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
    and chain: "(33,rooted_rows_argument a k m)\<in>positive_meaning socket_chain_system"
    using holds by (auto simp: record_admission_fields)
  obtain R r xs where source: "artifact_value_presents R a"
    and shape: "k=Payload_Term r" "m=data_list_term (map address_pair_data xs)"
    and root: "r\<in>rra_carrier (object_structure R)"
    and head: "headed_incidence (object_structure R) r=set xs"
    and root_data: "restrict_basis {r} (object_data R)=empty_basis"
    using headed by (auto simp: headed_material_empty_exact[simplified])
  have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
  have address: "octets_formed r" using rf root by (auto simp: exact_formed_def)
  have rows: "data_elements (map address_pair_data xs)" by (rule headed_rows_data[OF rf, where r=r]) (simp add: head)
  have path: "record_socket_chain R r (map fst xs)"
    using chain by (simp add: shape socket_chain_rows[OF source address rows])
  have read: "record_at R r (map fst xs) (map snd xs)"
    using rf root head root_data path by (simp add: record_at_socket_chain exact_formed_def zip_map_fst_snd)
  show "\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> record_at R r (map fst xs) (map snd xs)"
    using input source shape read by blast
next
  assume "\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
      artifact_value_presents R a \<and> record_at R r (map fst xs) (map snd xs)"
  then obtain R a r xs where input: "t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs))"
    and source: "artifact_value_presents R a" and read: "record_at R r (map fst xs) (map snd xs)" by blast
  have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
  have root: "r\<in>rra_carrier (object_structure R)" and head: "headed_incidence (object_structure R) r=set xs"
    and root_data: "restrict_basis {r} (object_data R)=empty_basis" and path: "record_socket_chain R r (map fst xs)"
    using read by (auto simp: record_at_socket_chain zip_map_fst_snd)
  have address: "octets_formed r" using rf root by (auto simp: exact_formed_def)
  have rows: "data_elements (map address_pair_data xs)" by (rule headed_rows_data[OF rf, where r=r]) (simp add: head)
  have distinct: "distinct xs"
    using record_socket_chain_distinct[OF path] by (simp add: distinct_keys_iff)
  have headed: "(29,headed_material_argument a (Payload_Term r) (data_list_term (map address_pair_data xs))
      (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
    using root distinct head root_data by (simp add: headed_material_no_data[OF source, simplified])
  have chain: "(33,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning socket_chain_system"
    using path by (simp add: socket_chain_rows[OF source address rows])
  show "(34,t)\<in>positive_meaning record_admission_system"
    by (simp only: record_admission_fields, intro exI[of _ a] exI[of _ "Payload_Term r"]
      exI[of _ "data_list_term (map address_pair_data xs)"]) (use input headed chain in blast)
qed

corollary record_admission_at_source:
  assumes source: "artifact_value_presents R a"
  shows "(34,rooted_rows_argument a k m)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (\<exists>r xs. k=Payload_Term r \<and> m=data_list_term (map address_pair_data xs) \<and>
      record_at R r (map fst xs) (map snd xs))"
  using artifact_value_presents_unique[OF _ source]
  by (auto simp: record_admission_exact intro: source)

corollary record_admission_rows:
  assumes source: "artifact_value_presents R a"
  shows "(34,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
    \<in>positive_meaning record_admission_system \<longleftrightarrow> record_at R r (map fst xs) (map snd xs)"
  by (simp add: record_admission_at_source[OF source] data_list_term_injective
    injective_mapped_lists[OF address_pair_data_injective])

corollary record_admission_order_unique:
  assumes source: "artifact_value_presents R a"
    and first: "(34,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning record_admission_system"
    and second: "(34,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data ys)))
      \<in>positive_meaning record_admission_system"
  shows "xs=ys"
proof -
  have left: "record_at R r (map fst xs) (map snd xs)"
    and right: "record_at R r (map fst ys) (map snd ys)"
    using first second by (simp_all add: record_admission_rows[OF source])
  have same: "map fst xs=map fst ys \<and> map snd xs=map snd ys"
    by (rule record_at_unique[OF left right])
  have "zip (map fst xs) (map snd xs)=zip (map fst ys) (map snd ys)" using same by simp
  then show ?thesis by (simp add: zip_map_fst_snd)
qed

corollary record_admission_presentation_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R b"
  shows "(34,rooted_rows_argument a k m)\<in>positive_meaning record_admission_system \<longleftrightarrow>
    (34,rooted_rows_argument b k m)\<in>positive_meaning record_admission_system"
  by (simp only: record_admission_at_source[OF assms(1)] record_admission_at_source[OF assms(2)])

section \<open>One closed native package supplies both grammar entries\<close>

theorem native_family_record_checking:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q df dr.
    df\<noteq>dr \<and> closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] df t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
            artifact_value_presents R a \<and> distinct xs \<and> family_at R r (set xs))))) \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] dr t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>R a r xs. t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
            artifact_value_presents R a \<and> record_at R r (map fst xs) (map snd xs)))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions record_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions record_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed record_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning record_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF record_admission_system_formed] by blast
  let ?future="\<lambda>d test. \<forall>t. term_formed t \<longrightarrow>
    (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> test t))"
  have entry: "?future (g d) (\<lambda>t. (d,t)\<in>positive_meaning record_admission_system)"
    if member: "d\<in>system_definitions record_admission_system" for d
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning record_admission_system)"
      using future[rule_format, OF member tf]
      by (simp only: record_admission_call member tf simp_thms) blast
  qed
  have family: "?future (g 32) (\<lambda>t. \<exists>R a r xs.
    t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
    artifact_value_presents R a \<and> distinct xs \<and> family_at R r (set xs))"
    using entry[of 32] by (simp add: record_admission_family family_admission_exact)
  have record_calls: "?future (g 34) (\<lambda>t. \<exists>R a r xs.
    t=rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)) \<and>
    artifact_value_presents R a \<and> record_at R r (map fst xs) (map snd xs))"
    using entry[of 34] by (simp add: record_admission_exact)
  have separate: "g 32\<noteq>g 34" using inj_onD[OF injective, of 32 34] by auto
  show ?thesis by (intro exI[of _ E] exI[of _ pu] exI[of _ Q] exI[of _ "g 32"] exI[of _ "g 34"])
    (use separate closed family record_calls in blast)
qed

text \<open>
  The record entry combines complete root material with a finite traversal
  of actual successor heads. It has no separate key-uniqueness premise:
  the terminating deterministic chain already proves distinct sockets.
  The root graph fixes every endpoint; repeated endpoints remain valid.

  Soundness and completeness cover every input term and the entire existing
  relative record grammar. At a fixed root the ordered row result is unique.
  Source artifact presentations remain interchangeable, while changing row
  order must still pass the represented successor path.

  Family and record are distinct actual definition sites in one native
  package fixed before all future formed arguments. Every constructed
  application retains its canonical program environment. The full program
  has thirty-five definitions and sixty-two clauses. Citation, higher
  grammar, correctness evidence, and protocol admission remain separate.
\<close>

end
