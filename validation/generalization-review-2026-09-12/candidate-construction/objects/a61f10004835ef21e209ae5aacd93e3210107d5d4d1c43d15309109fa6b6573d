theory Factor_Interpreter_Admission
  imports Factor_Scope_Admission Factor_Scope_Interpreters
begin

section \<open>The reference scope and its two entries are fixed in the checker\<close>

abbreviation interpreter_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "interpreter_argument e pu pr f qu qr a b \<equiv>
    Pair_Term (source_root_argument e pu pr) (package_subject_argument f qu qr (Pair_Term a b))"

abbreviation interpreter_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "interpreter_pattern e pu pr f qu qr a b \<equiv>
    Pattern_Pair (source_root_pattern e pu pr) (package_subject_pattern f qu qr (Pattern_Pair a b))"

abbreviation interpreter_admission_result :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "interpreter_admission_result c a0 b0 t \<equiv> \<exists>C ka kb E e pu pr F f qu qr a b.
    environment_value_presents C c \<and> a0=definition_site_value ka \<and> b0=definition_site_value kb \<and>
    t=interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
      (definition_site_value a) (definition_site_value b) \<and>
    environment_value_presents E e \<and> environment_value_presents F f \<and>
    native_scope_interpreter_at C ka kb E pu pr F qu qr a b"

definition interpreter_admission_schema :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat) factor_schema" where
  "interpreter_admission_schema c a0 b0=data_rule
    (interpreter_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)))
    {(0,80,source_root_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2)),
     (1,83,package_subject_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))),
     (2,83,package_subject_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))),
     (3,116,scope_forwarding_pattern (Pattern_Variable 12) (Pattern_Variable 6) (Pattern_Variable 7) (exact_term_pattern a0) (Pattern_Variable 10) (Pattern_Variable 1) (Pattern_Variable 2)),
     (4,116,scope_forwarding_pattern (Pattern_Variable 12) (Pattern_Variable 8) (Pattern_Variable 9) (exact_term_pattern b0) (Pattern_Variable 11) (Pattern_Variable 1) (Pattern_Variable 2)),
     (5,113,Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 10)),
     (6,113,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 0)),
     (7,113,Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 11)),
     (8,113,Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 0)),
     (9,113,Pattern_Pair (exact_term_pattern c) (Pattern_Variable 12)),
     (10,113,Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 12))}"

definition interpreter_admission_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "interpreter_admission_system c a0 b0=add_view_definition scope_forwarding_system 117 data_x
    {(0,interpreter_admission_schema c a0 b0)}"

locale interpreter_admission =
  fixes c a0 b0 :: factor_term
  assumes fields: "term_formed c" "term_formed a0" "term_formed b0"
begin

lemma formed: "schema_system_formed (interpreter_admission_system c a0 b0)"
  unfolding interpreter_admission_system_def
  by (rule add_recursive_definition_formed[OF scope_forwarding_system_formed])
    (use fields in \<open>auto simp: interpreter_admission_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def\<close>)

lemma definitions [simp]:
  "system_definitions (interpreter_admission_system c a0 b0)=insert 117 (system_definitions scope_forwarding_system)"
  by (simp add: interpreter_admission_system_def)

lemma calls:
  "schema_call_formed (interpreter_admission_system c a0 b0) d t \<longleftrightarrow>
    d\<in>system_definitions (interpreter_admission_system c a0 b0) \<and> term_formed t"
  using added_variable_calls[OF scope_forwarding_system_formed
    formed[unfolded interpreter_admission_system_def] scope_forwarding_call]
  by (simp only: interpreter_admission_system_def[symmetric])

lemma old_meaning:
  assumes "d\<in>system_definitions scope_forwarding_system"
  shows "(d,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (d,t)\<in>positive_meaning scope_forwarding_system"
  using added_definition_preserves_old(2)[OF scope_forwarding_system_formed
    formed[unfolded interpreter_admission_system_def], of d t] assms
  by (auto simp: interpreter_admission_system_def)

lemma clause [simp]:
  "((117,n),S)\<in>system_clauses (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (n,S)\<in>{(0,interpreter_admission_schema c a0 b0)}"
proof -
  have owned: "((d,n),S)\<in>system_clauses scope_forwarding_system \<Longrightarrow>
    d\<in>system_definitions scope_forwarding_system" for d n S
    using scope_forwarding_system_formed unfolding schema_system_formed_def by blast
  have absent: "((117,n),S)\<notin>system_clauses scope_forwarding_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: interpreter_admission_system_def)
qed

lemma package_meaning:
  assumes "d\<in>system_definitions package_membership_system"
  shows "(d,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_membership_system"
  using assms
  by (simp add: old_meaning scope_forwarding_old_meaning native_positive_admission_old_meaning
    positive_query_old_meaning environment_inclusion_old_meaning artifact_inclusion_old_meaning
    replay_admission_old_meaning retention_admission_old_meaning
    replay_slot_list_old_meaning replay_source_list_old_meaning
    replay_slot_reading_old_meaning replay_source_reading_old_meaning
    definition_slot_reading_old_meaning schema_slot_reading_old_meaning
    premise_slot_reading_old_meaning derivation_admission_old_meaning
    proof_claim_checking_old_meaning keyed_row_join_old_meaning row_qualification_old_meaning
    proof_graph_membership_old_meaning proof_graph_admission_old_meaning
    proof_bound_checking_old_meaning proof_link_checking_old_meaning proof_node_reading_old_meaning
    discharge_table_reading_old_meaning binding_table_reading_old_meaning site_link_vector_old_meaning
    application_vector_old_meaning site_link_reading_old_meaning site_citation_reading_old_meaning
    admitted_instantiation_old_meaning program_call_list_old_meaning application_admission_old_meaning
    program_call_admission_old_meaning)

lemma components:
  "(80,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (80,t)\<in>positive_meaning package_admission_system"
  "(83,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(116,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (116,t)\<in>positive_meaning scope_forwarding_system"
  "(113,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  using package_meaning[of 80 t] package_membership_components(1)[of t]
    package_meaning[of 83 t] old_meaning[of 116 t] old_meaning[of 113 t]
    scope_forwarding_old_meaning[of 113 t] native_positive_admission_old_meaning[of 113 t]
    positive_query_components(2)[of t] by auto

lemma valuation:
  "(117,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}. term_formed (h j)) \<and>
      t=interpreter_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)) (Pair_Term (h 8) (h 9)) \<and>
      (80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system \<and>
      (83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)))\<in>positive_meaning package_membership_system \<and>
      (83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 8) (h 9)))\<in>positive_meaning package_membership_system \<and>
      (116,scope_forwarding_argument (h 12) (h 6) (h 7) a0 (h 10) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system \<and>
      (116,scope_forwarding_argument (h 12) (h 8) (h 9) b0 (h 11) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system \<and>
      (113,Pair_Term (h 0) (h 10))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 10) (h 0))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 0) (h 11))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 11) (h 0))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term c (h 12))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 3) (h 12))\<in>positive_meaning environment_inclusion_system)"
proof -
  have family: "((117,n),S)\<in>system_clauses (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    n=0 \<and> S=interpreter_admission_schema c a0 b0" for n S by simp
  have ordinary: "schema_material_premises (interpreter_admission_schema c a0 b0)={}"
    by (simp add: interpreter_admission_schema_def)
  have boundary: "schema_call_formed (interpreter_admission_system c a0 b0) 117
      (evaluate_pattern h (schema_conclusion (interpreter_admission_schema c a0 b0)))"
    if assignment: "\<forall>a\<in>schema_variables (interpreter_admission_schema c a0 b0). term_formed (h a)" for h
    using assignment fields by (auto simp: calls interpreter_admission_schema_def schema_variables_def)
  have variables: "schema_variables (interpreter_admission_schema c a0 b0)={0,1,2,3,4,5,6,7,8,9,10,11,12}"
    by (auto simp: interpreter_admission_schema_def schema_variables_def)
  have head: "evaluate_pattern h (schema_conclusion (interpreter_admission_schema c a0 b0))=interpreter_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)) (Pair_Term (h 8) (h 9))" for h
    by (simp add: interpreter_admission_schema_def)
  have support: "(\<forall>s d p. (s,d,p)\<in>schema_premises (interpreter_admission_schema c a0 b0) \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning (interpreter_admission_system c a0 b0)) \<longleftrightarrow>
      (80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system \<and>
      (83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)))\<in>positive_meaning package_membership_system \<and>
      (83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 8) (h 9)))\<in>positive_meaning package_membership_system \<and>
      (116,scope_forwarding_argument (h 12) (h 6) (h 7) a0 (h 10) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system \<and>
      (116,scope_forwarding_argument (h 12) (h 8) (h 9) b0 (h 11) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system \<and>
      (113,Pair_Term (h 0) (h 10))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 10) (h 0))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 0) (h 11))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 11) (h 0))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term c (h 12))\<in>positive_meaning environment_inclusion_system \<and>
      (113,Pair_Term (h 3) (h 12))\<in>positive_meaning environment_inclusion_system" for h
  proof -
    have rows: "(\<forall>s d p. (s,d,p)\<in>schema_premises (interpreter_admission_schema c a0 b0) \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning (interpreter_admission_system c a0 b0)) \<longleftrightarrow>
      (\<forall>(s,d,p)\<in>schema_premises (interpreter_admission_schema c a0 b0).
        (d,evaluate_pattern h p)\<in>positive_meaning (interpreter_admission_system c a0 b0))"
      by (auto split: prod.splits)
    show ?thesis by (simp only: rows) (simp add: interpreter_admission_schema_def components)
  qed
  note equation=ordinary_single_clause_valuation[OF family ordinary boundary, where t=t]
  show ?thesis by (rule equation[unfolded variables head support])
qed

lemma step:
  assumes reads:
     "(80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system"
     "(83,package_subject_argument f qu qr (Pair_Term au ar))\<in>positive_meaning package_membership_system"
     "(83,package_subject_argument f qu qr (Pair_Term bu br))\<in>positive_meaning package_membership_system"
     "(116,scope_forwarding_argument v au ar a0 x pu pr)\<in>positive_meaning scope_forwarding_system"
     "(116,scope_forwarding_argument v bu br b0 y pu pr)\<in>positive_meaning scope_forwarding_system"
     "(113,Pair_Term e x)\<in>positive_meaning environment_inclusion_system"
     "(113,Pair_Term x e)\<in>positive_meaning environment_inclusion_system"
     "(113,Pair_Term e y)\<in>positive_meaning environment_inclusion_system"
     "(113,Pair_Term y e)\<in>positive_meaning environment_inclusion_system"
     "(113,Pair_Term c v)\<in>positive_meaning environment_inclusion_system"
     "(113,Pair_Term f v)\<in>positive_meaning environment_inclusion_system"
  shows "(117,interpreter_argument e pu pr f qu qr (Pair_Term au ar) (Pair_Term bu br))
    \<in>positive_meaning (interpreter_admission_system c a0 b0)"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then f else if j=4 then qu else if j=5 then qr else if j=6 then au else if j=7 then ar else if j=8 then bu else if j=9 then br else if j=10 then x else if j=11 then y else v"
  have data: "term_formed e" "term_formed pu" "term_formed pr" "term_formed f" "term_formed qu" "term_formed qr" "term_formed au" "term_formed ar" "term_formed bu" "term_formed br" "term_formed x" "term_formed y" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(3)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(4)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(5)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(6)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(7)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(8)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(9)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(10)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(11)]] by auto
  show ?thesis by (simp only: valuation, rule exI[of _ ?h]) (use reads data in auto)
qed

section \<open>Admission recovers the complete structural interpreter profile\<close>

theorem sound:
  assumes holds: "(117,t)\<in>positive_meaning (interpreter_admission_system c a0 b0)"
  shows "interpreter_admission_result c a0 b0 t"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where shape: "t=interpreter_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)) (Pair_Term (h 8) (h 9))"
    and reads:
    "(80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system"
    "(83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 6) (h 7)))\<in>positive_meaning package_membership_system"
    "(83,package_subject_argument (h 3) (h 4) (h 5) (Pair_Term (h 8) (h 9)))\<in>positive_meaning package_membership_system"
    "(116,scope_forwarding_argument (h 12) (h 6) (h 7) a0 (h 10) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system"
    "(116,scope_forwarding_argument (h 12) (h 8) (h 9) b0 (h 11) (h 1) (h 2))\<in>positive_meaning scope_forwarding_system"
    "(113,Pair_Term (h 0) (h 10))\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term (h 10) (h 0))\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term (h 0) (h 11))\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term (h 11) (h 0))\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term c (h 12))\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term (h 3) (h 12))\<in>positive_meaning environment_inclusion_system"
    using holds by (simp only: valuation) blast
  obtain E pu pr P where old: "environment_value_presents E (h 0)"
    "h 1=use_data_term pu" "h 2=Payload_Term pr" "native_package_at E pu pr P"
    using reads(1) by (simp only: package_admission_exact factor_term.inject) blast
  obtain F qu qr Q a where candidate: "environment_value_presents F (h 3)"
    "h 4=use_data_term qu" "h 5=Payload_Term qr" "Pair_Term (h 6) (h 7)=definition_site_value a"
    "native_package_at F qu qr Q" "a\<in>system_definitions Q"
    using reads(2) by (simp only: package_membership_exact factor_term.inject) blast
  obtain b Q' where other: "Pair_Term (h 8) (h 9)=definition_site_value b"
    "native_package_at F qu qr Q'" "b\<in>system_definitions Q'"
    using reads(3) by (simp only: candidate(2,3) package_membership_at_source[OF candidate(1)]
      factor_term.inject inj_eq[OF use_data_term_injective]) blast
  have same_program: "Q'=Q" by (rule native_package_unique[OF other(2) candidate(5)])
  have member: "b\<in>system_definitions Q" using other(3) same_program by simp
  obtain C H where reference: "environment_value_presents C c" "environment_value_presents H (h 12)"
    "environment_included C H"
    using reads(10) by (simp only: environment_inclusion_exact factor_term.inject) blast
  have hf: "environment_formed H" and cf: "environment_formed C"
    using environment_value_presents_formed[OF reference(2)] environment_value_presents_formed[OF reference(1)] by auto
  have included: "environment_included F H"
    using reads(11) by (simp only: environment_inclusion_on_values[OF candidate(1) reference(2)])
  obtain A where left: "environment_value_presents A (h 10)" "environment_included E A"
    using reads(6) by (simp only: environment_inclusion_at_source[OF old(1)]) blast
  have left_back: "environment_included A E"
    using reads(7) by (simp only: environment_inclusion_on_values[OF left(1) old(1)])
  have left_same: "A=E" by (rule environment_included_antisym[OF left_back left(2)])
  have x: "environment_value_presents E (h 10)" using left(1) left_same by simp
  obtain B where right: "environment_value_presents B (h 11)" "environment_included E B"
    using reads(8) by (simp only: environment_inclusion_at_source[OF old(1)]) blast
  have right_back: "environment_included B E"
    using reads(9) by (simp only: environment_inclusion_on_values[OF right(1) old(1)])
  have right_same: "B=E" by (rule environment_included_antisym[OF right_back right(2)])
  have y: "environment_value_presents E (h 11)" using right(1) right_same by simp
  have ac: "h 6=use_data_term (fst a)" "h 7=Payload_Term (snd a)"
    using candidate(4) by (simp_all add: site_data_term_def)
  have bc: "h 8=use_data_term (fst b)" "h 9=Payload_Term (snd b)"
    using other(1) by (simp_all add: site_data_term_def)
  obtain H' ka where first: "environment_value_presents H' (h 12)" "a0=definition_site_value ka"
    "native_scope_forwarding_at H' (fst a) (snd a) ka (h 10) (use_data_term pu) (Payload_Term pr)"
    using reads(4)[unfolded ac old(2,3)]
    by (simp only: scope_forwarding_exact factor_term.inject inj_eq[OF use_data_term_injective]) blast
  have first_environment: "H'=H" by (rule environment_value_presents_unique[OF first(1) reference(2)])
  have first_read: "native_scope_forwarding_at H (fst a) (snd a) ka (h 10) (use_data_term pu) (Payload_Term pr)"
    using first(3) first_environment by simp
  obtain H'' kb where second: "environment_value_presents H'' (h 12)" "b0=definition_site_value kb"
    "native_scope_forwarding_at H'' (fst b) (snd b) kb (h 11) (use_data_term pu) (Payload_Term pr)"
    using reads(5)[unfolded bc old(2,3)]
    by (simp only: scope_forwarding_exact factor_term.inject inj_eq[OF use_data_term_injective]) blast
  have second_environment: "H''=H" by (rule environment_value_presents_unique[OF second(1) reference(2)])
  have second_read: "native_scope_forwarding_at H (fst b) (snd b) kb (h 11) (use_data_term pu) (Payload_Term pr)"
    using second(3) second_environment by simp
  have profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
    unfolding native_scope_interpreter_at_def
    by (rule conjI[OF cf], rule exI[of _ P], rule exI[of _ Q], rule exI[of _ H],
        rule exI[of _ "h 10"], rule exI[of _ "h 11"])
      (use old(4) candidate(5,6) member hf reference(3) included x y first_read second_read in blast)
  show ?thesis by (rule exI[of _ C], rule exI[of _ ka], rule exI[of _ kb], rule exI[of _ E],
      rule exI[of _ "h 0"], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ F],
      rule exI[of _ "h 3"], rule exI[of _ qu], rule exI[of _ qr], rule exI[of _ a], rule exI[of _ b])
    (use reference(1) first(2) second(2) shape old(1-3) candidate(1-4) other(1) profile in simp)
qed

theorem complete:
  assumes reference: "environment_value_presents C c" and entries: "a0=definition_site_value ka" "b0=definition_site_value kb"
    and source: "environment_value_presents E e" and target: "environment_value_presents F f"
    and profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
  shows "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
    (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0)"
proof -
  obtain P Q where packages: "native_package_at E pu pr P" "native_package_at F qu qr Q"
    using profile unfolding native_scope_interpreter_at_def by blast
  obtain H x y where data: "a\<in>system_definitions Q" "b\<in>system_definitions Q"
    "environment_formed H" "environment_included C H" "environment_included F H"
    "environment_value_presents E x" "environment_value_presents E y"
    "native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr)"
    "native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr)"
    using native_scope_interpreter_witnesses[OF profile packages(2)] by blast
  obtain v where extension: "environment_value_presents H v"
    using environment_value_presents_total[OF data(3)] by blast
  have old: "(80,source_root_argument e (use_data_term pu) (Payload_Term pr))\<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source packages(1)])
  have a: "(83,package_subject_argument f (use_data_term qu) (Payload_Term qr) (definition_site_value a))
    \<in>positive_meaning package_membership_system"
    by (rule package_membership_complete[OF target packages(2) data(1)])
  have b: "(83,package_subject_argument f (use_data_term qu) (Payload_Term qr) (definition_site_value b))
    \<in>positive_meaning package_membership_system"
    by (rule package_membership_complete[OF target packages(2) data(2)])
  have first: "(116,scope_forwarding_argument v (use_data_term (fst a)) (Payload_Term (snd a))
      a0 x (use_data_term pu) (Payload_Term pr))\<in>positive_meaning scope_forwarding_system"
    using scope_forwarding_complete[OF extension data(8)] by (simp only: entries)
  have second: "(116,scope_forwarding_argument v (use_data_term (fst b)) (Payload_Term (snd b))
      b0 y (use_data_term pu) (Payload_Term pr))\<in>positive_meaning scope_forwarding_system"
    using scope_forwarding_complete[OF extension data(9)] by (simp only: entries)
  have ex: "(113,Pair_Term e x)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF source data(6) environment_included_refl])
  have xe: "(113,Pair_Term x e)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF data(6) source environment_included_refl])
  have ey: "(113,Pair_Term e y)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF source data(7) environment_included_refl])
  have ye: "(113,Pair_Term y e)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF data(7) source environment_included_refl])
  have cv: "(113,Pair_Term c v)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF reference extension data(4)])
  have fv: "(113,Pair_Term f v)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF target extension data(5)])
  show ?thesis using step[OF old a[unfolded site_data_term_def] b[unfolded site_data_term_def]
      first second ex xe ey ye cv fv] by (simp only: site_data_term_def)
qed

theorem exact:
  "(117,t)\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow> interpreter_admission_result c a0 b0 t"
  using sound complete by blast

theorem on_values:
  assumes reference: "environment_value_presents C c" and entries: "a0=definition_site_value ka" "b0=definition_site_value kb"
    and source: "environment_value_presents E e" and target: "environment_value_presents F f"
  shows "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
      (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0) \<longleftrightarrow>
    native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
proof -
  have reference_unique: "D=C" if "environment_value_presents D c" for D
    by (rule environment_value_presents_unique[OF that reference])
  have source_unique: "D=E" if "environment_value_presents D e" for D
    by (rule environment_value_presents_unique[OF that source])
  have target_unique: "D=F" if "environment_value_presents D f" for D
    by (rule environment_value_presents_unique[OF that target])
  show ?thesis
    by (simp only: exact; simp only: entries factor_term.inject inj_eq[OF use_data_term_injective] definition_site_value_eq)
      (use reference source target reference_unique source_unique target_unique in blast)
qed

theorem correctness:
  assumes reference_value: "environment_value_presents C c" and encoded: "a0=definition_site_value ka" "b0=definition_site_value kb"
    and reference: "native_package_at C cu cr R"
    and entries: "ka\<in>system_definitions R" "kb\<in>system_definitions R" and distinct: "ka\<noteq>kb"
    and admission: "\<forall>z. (ka,z)\<in>positive_meaning R \<longleftrightarrow> program_call_admission_result z"
    and meaning: "\<forall>z. (kb,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
    and source: "environment_value_presents E e" "native_package_at E pu pr P"
    and target: "environment_value_presents F f" "native_package_at F qu qr Q"
    and checked: "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
      (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0)"
  shows "program_interpretation P Q a b \<and> a\<noteq>b"
proof -
  have profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
    using checked by (simp only: on_values[OF reference_value encoded source(1) target(1)])
  show ?thesis using native_scope_interpreter_correct[OF reference entries admission meaning profile source(2) target(2)]
    native_scope_interpreter_distinct[OF profile distinct] by blast
qed

theorem missing_entry_rejected:
  assumes reference: "environment_value_presents C c" and entries: "a0=definition_site_value ka" "b0=definition_site_value kb"
    and source: "environment_value_presents E e"
    and target: "environment_value_presents F f" "native_package_at F qu qr Q"
    and missing: "a\<notin>system_definitions Q \<or> b\<notin>system_definitions Q"
  shows "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
    (definition_site_value a) (definition_site_value b))\<notin>positive_meaning (interpreter_admission_system c a0 b0)"
proof
  assume holds: "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
    (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0)"
  have profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
    using holds by (simp only: on_values[OF reference entries source target(1)])
  show False using native_scope_interpreter_witnesses[OF profile target(2)] missing by blast
qed

theorem total:
  assumes reference_value: "environment_value_presents C c" and encoded: "a0=definition_site_value ka" "b0=definition_site_value kb"
    and reference: "native_package_at C cu cr R"
    and entries: "ka\<in>system_definitions R" "kb\<in>system_definitions R"
    and source: "native_package_at E pu pr P"
  shows "\<exists>F qu Q a b. closed_native_package_at F qu [] Q \<and> native_package_environment F qu []=F \<and>
    a\<noteq>b \<and> {a,b}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert b (insert a (system_definitions R)) \<and>
    (\<forall>e f. environment_value_presents E e \<longrightarrow> environment_value_presents F f \<longrightarrow>
      (117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term [])
        (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0))"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF source] by (simp add: native_package_formed_def)
  obtain x where presentation: "environment_value_presents E x" using environment_value_presents_total[OF ef] by blast
  obtain F qu Q a b where built: "closed_native_package_at F qu [] Q" "native_package_environment F qu []=F"
    "native_scope_interpreter_at C ka kb E pu pr F qu [] a b"
    "a\<noteq>b" "{a,b}\<inter>system_definitions R={}"
    "system_definitions Q=insert b (insert a (system_definitions R))"
    using native_scope_interpreter_total[OF reference entries source presentation presentation]
    by (elim exE conjE) (rule that; assumption)
  have accepted: "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term [])
        (definition_site_value a) (definition_site_value b))\<in>positive_meaning (interpreter_admission_system c a0 b0)"
    if "environment_value_presents E e" "environment_value_presents F f" for e f
    by (rule complete[OF reference_value encoded that built(3)])
  show ?thesis by (rule exI[of _ F], rule exI[of _ qu], rule exI[of _ Q], rule exI[of _ a], rule exI[of _ b])
    (use built(1,2,4-6) accepted in blast)
qed

section \<open>One native checker precedes all future inputs\<close>

theorem native_checker:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu T d.
    closed_native_package_at B bu [] T \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] d t I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> interpreter_admission_result c a0 b0 t) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>R. artifact_at G v R \<longleftrightarrow> artifact_at B v R) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>k w. binds_slot G v k w \<longleftrightarrow> binds_slot B v k w)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and B :: "local_address option artifact_environment" and bu T
    where closed: "closed_native_package_at B bu [] T"
    and future: "\<forall>d\<in>system_definitions (interpreter_admission_system c a0 b0). \<forall>t. term_formed t \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] (g d) t I K \<and>
        native_package_environment G bu []=B \<and>
        (native_application_formed G bu [] au [] \<longleftrightarrow> schema_call_formed (interpreter_admission_system c a0 b0) d t) \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning (interpreter_admission_system c a0 b0)) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>R. artifact_at G v R \<longleftrightarrow> artifact_at B v R) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>k w. binds_slot G v k w \<longleftrightarrow> binds_slot B v k w))"
    using compiled_program_future_applications[OF formed] by (elim exE conjE) (rule that; assumption)
  have member: "117\<in>system_definitions (interpreter_admission_system c a0 b0)" by simp
  show ?thesis by (rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ "g 117"])
    (use closed future[rule_format, OF member] in \<open>auto simp: calls exact\<close>)
qed

end

section \<open>Complete presentations preserve admission, including the fixed configuration\<close>

theorem interpreter_admission_presentation_invariance:
  assumes reference: "environment_value_presents C c" "environment_value_presents C c'"
    and entries: "term_formed (definition_site_value ka)" "term_formed (definition_site_value kb)"
    and source: "environment_value_presents E e" "environment_value_presents E e'"
    and target: "environment_value_presents F f" "environment_value_presents F f'"
  shows "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
      (definition_site_value a) (definition_site_value b))
        \<in>positive_meaning (interpreter_admission_system c (definition_site_value ka) (definition_site_value kb)) \<longleftrightarrow>
    (117,interpreter_argument e' (use_data_term pu) (Payload_Term pr) f' (use_data_term qu) (Payload_Term qr)
      (definition_site_value a) (definition_site_value b))
        \<in>positive_meaning (interpreter_admission_system c' (definition_site_value ka) (definition_site_value kb))"
proof -
  have fields: "term_formed c" "term_formed c'"
    using environment_value_presents_formed[OF reference(1)] environment_value_presents_formed[OF reference(2)] by auto
  interpret left: interpreter_admission c "definition_site_value ka" "definition_site_value kb"
    by (rule interpreter_admission.intro[OF fields(1) entries])
  interpret right: interpreter_admission c' "definition_site_value ka" "definition_site_value kb"
    by (rule interpreter_admission.intro[OF fields(2) entries])
  show ?thesis by (simp only: left.on_values[OF reference(1) refl refl source(1) target(1)]
    right.on_values[OF reference(2) refl refl source(2) target(2)])
qed

section \<open>A proved reference and its native admission program exist before every source\<close>

theorem fixed_native_interpreter_admission:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu R ka kb c.
    \<exists>B :: local_address option artifact_environment. \<exists>bu T d.
    closed_native_package_at C cu [] R \<and> environment_value_presents C c \<and> ka\<noteq>kb \<and>
    (\<forall>E pu pr P F qu qr Q e f a b.
      native_package_at E pu pr P \<longrightarrow> native_package_at F qu qr Q \<longrightarrow>
      environment_value_presents E e \<longrightarrow> environment_value_presents F f \<longrightarrow>
      (117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
        (definition_site_value a) (definition_site_value b))
          \<in>positive_meaning (interpreter_admission_system c (definition_site_value ka) (definition_site_value kb)) \<longrightarrow>
      program_interpretation P Q a b \<and> a\<noteq>b) \<and>
    (\<forall>E pu pr P. native_package_at E pu pr P \<longrightarrow>
      (\<exists>F qu Q a b. closed_native_package_at F qu [] Q \<and> native_package_environment F qu []=F \<and>
        a\<noteq>b \<and> {a,b}\<inter>system_definitions R={} \<and>
        system_definitions Q=insert b (insert a (system_definitions R)) \<and>
        (\<forall>e f. environment_value_presents E e \<longrightarrow> environment_value_presents F f \<longrightarrow>
          (117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term [])
            (definition_site_value a) (definition_site_value b))
              \<in>positive_meaning (interpreter_admission_system c (definition_site_value ka) (definition_site_value kb))))) \<and>
    closed_native_package_at B bu [] T \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] d t I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow>
          interpreter_admission_result c (definition_site_value ka) (definition_site_value kb) t) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>k w. binds_slot G v k w \<longleftrightarrow> binds_slot B v k w)))"
proof -
  obtain C :: "local_address option artifact_environment" and cu R ka kb where reference:
    "closed_native_package_at C cu [] R" "ka\<noteq>kb"
    "ka\<in>system_definitions R" "kb\<in>system_definitions R"
    "\<forall>z. (ka,z)\<in>positive_meaning R \<longleftrightarrow> program_call_admission_result z"
    "\<forall>z. (kb,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
    using native_program_reflection by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at C cu [] R" using reference(1) by (simp add: closed_native_package_at_def)
  have cf: "environment_formed C"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain c where presentation: "environment_value_presents C c" using environment_value_presents_total[OF cf] by blast
  have positions: "ka\<in>environment_positions C" "kb\<in>environment_positions C"
    by (rule native_package_entry_position[OF package reference(3)], rule native_package_entry_position[OF package reference(4)])
  have fields: "term_formed c" "term_formed (definition_site_value ka)" "term_formed (definition_site_value kb)"
    using environment_value_presents_formed[OF presentation]
      environment_position_address[OF cf positions(1)] environment_position_address[OF cf positions(2)] by auto
  interpret checker: interpreter_admission c "definition_site_value ka" "definition_site_value kb"
    by (rule interpreter_admission.intro[OF fields])
  have correct: "program_interpretation P Q a b \<and> a\<noteq>b"
    if "native_package_at E pu pr P" "native_package_at F qu qr Q"
      "environment_value_presents E e" "environment_value_presents F f"
      "(117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term qr)
        (definition_site_value a) (definition_site_value b))
          \<in>positive_meaning (interpreter_admission_system c (definition_site_value ka) (definition_site_value kb))"
    for E pu pr P F qu qr Q e f a b
    by (rule checker.correctness[OF presentation refl refl package reference(3,4,2,5,6) that(3,1,4,2,5)])
  have total: "\<exists>F qu Q a b. closed_native_package_at F qu [] Q \<and> native_package_environment F qu []=F \<and>
        a\<noteq>b \<and> {a,b}\<inter>system_definitions R={} \<and>
        system_definitions Q=insert b (insert a (system_definitions R)) \<and>
        (\<forall>e f. environment_value_presents E e \<longrightarrow> environment_value_presents F f \<longrightarrow>
          (117,interpreter_argument e (use_data_term pu) (Payload_Term pr) f (use_data_term qu) (Payload_Term [])
            (definition_site_value a) (definition_site_value b))
              \<in>positive_meaning (interpreter_admission_system c (definition_site_value ka) (definition_site_value kb)))"
    if "native_package_at E pu pr P" for E pu pr P
    by (rule checker.total[OF presentation refl refl package reference(3,4) that])
  obtain B :: "local_address option artifact_environment" and bu T d where compiled:
    "closed_native_package_at B bu [] T"
    "\<forall>t. term_formed t \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] T \<and> native_application_at G au [] d t I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow>
          interpreter_admission_result c (definition_site_value ka) (definition_site_value kb) t) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>k w. binds_slot G v k w \<longleftrightarrow> binds_slot B v k w))"
    using checker.native_checker by (elim exE conjE) (rule that; assumption)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ R], rule exI[of _ ka], rule exI[of _ kb],
      rule exI[of _ c], rule exI[of _ B], rule exI[of _ bu], rule exI[of _ T], rule exI[of _ d])
    (use reference(1,2) presentation correct total compiled in blast)
qed

text \<open>
  The checker adds one ordinary definition with eleven identified premises.
  They admit the old package, establish both memberships in the actual candidate
  package, inspect both complete forwarding definitions, compare the complete
  internal source presentations in both directions, and retain the reference
  and candidate environments in a common formed extension. That extension is
  private finite evidence; it cannot select a smaller old domain or alter either
  retained scope. The reference environment and both callee coordinates are
  literals fixed in the checker before any submitted source or candidate.

  The all-term admission equation is exact for the structural profile. Complete
  presentation choices preserve it for the source, candidate, and fixed reference
  environment. Existing ordinary entries retain their meanings. Missing candidate
  entries are rejected, and distinct reference roles force distinct admitted
  entries. Every native source package has a closed candidate in this class.

  The final theorem obtains the reference from the previously proved universal
  interpreter, then fixes one native admission program before every future input.
  Admission entails exact historical formation and truth for all arguments.
  Its active checking rules remain those of that fixed program; candidate clauses
  are inspected as data. This is a sufficient correctness class. Full transition
  admission, the remaining reflection strata, and genesis remain separate joins.
\<close>

end
