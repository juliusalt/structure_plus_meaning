theory Factor_Citation_Admission
  imports Factor_Target_Admission Factor_Citation_Values
begin

section \<open>Complete headed observations expose exact operands\<close>

lemma headed_material_one_row_exact:
  "(29,headed_material_argument a k (data_list_term [Pair_Term p x]) (Payload_Term []) (Payload_Term []))
    \<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>R r u v. artifact_value_presents R a \<and> k=Payload_Term r \<and>
      p=Payload_Term u \<and> x=Payload_Term v \<and> r\<in>rra_carrier (object_structure R) \<and>
      headed_incidence (object_structure R) r={(u,v)} \<and> restrict_basis {r} (object_data R)=empty_basis)"
  by (simp only: headed_material_empty_exact[simplified] data_list_term_injective)
    (auto simp: map_eq_Cons_conv Cons_eq_map_conv address_pair_data_def)

lemma headed_material_two_rows_exact:
  "(29,headed_material_argument a k (data_list_term [Pair_Term p x,Pair_Term q y])
      (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>R r u v w z. artifact_value_presents R a \<and> k=Payload_Term r \<and>
      p=Payload_Term u \<and> x=Payload_Term v \<and> q=Payload_Term w \<and> y=Payload_Term z \<and>
      r\<in>rra_carrier (object_structure R) \<and> (u,v)\<noteq>(w,z) \<and>
      headed_incidence (object_structure R) r={(u,v),(w,z)} \<and> restrict_basis {r} (object_data R)=empty_basis)"
  by (simp only: headed_material_empty_exact[simplified] data_list_term_injective)
    (auto simp: map_eq_Cons_conv Cons_eq_map_conv address_pair_data_def)

lemma headed_material_leaf_value:
  assumes source: "artifact_value_presents R a"
  shows "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [x]))
    \<in>positive_meaning headed_material_system \<longleftrightarrow>
    (\<exists>r v. k=Payload_Term r \<and> x=Payload_Term v \<and> payload_leaf_at R r v)"
proof
  assume holds: "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [x]))
    \<in>positive_meaning headed_material_system"
  obtain r where root: "k=Payload_Term r"
    and material: "headed_material_presents R r (Payload_Term []) (Payload_Term []) (data_list_term [x])"
    using holds by (auto simp: headed_material_at_source[OF source])
  obtain F where encoded: "data_list_term [x]=data_list_term (map Payload_Term F)"
    using material by (auto simp: headed_material_presents_def)
  obtain v where x: "x=Payload_Term v"
    using encoded by (simp only: data_list_term_injective) (auto simp: map_eq_Cons_conv Cons_eq_map_conv)
  have leaf: "payload_leaf_at R r v"
    using holds by (simp add: root x headed_material_leaf[OF source, simplified])
  show "\<exists>r v. k=Payload_Term r \<and> x=Payload_Term v \<and> payload_leaf_at R r v"
    using root x leaf by blast
next
  assume "\<exists>r v. k=Payload_Term r \<and> x=Payload_Term v \<and> payload_leaf_at R r v"
  then show "(29,headed_material_argument a k (Payload_Term []) (Payload_Term []) (data_list_term [x]))
    \<in>positive_meaning headed_material_system"
    by (auto simp: headed_material_leaf[OF source, simplified])
qed

section \<open>Four ordinary clauses recover the existing citation geometry\<close>

abbreviation citation_admission_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "citation_admission_argument a r c i \<equiv> Pair_Term (Pair_Term a r) (Pair_Term c i)"

abbreviation citation_admission_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern" where
  "citation_admission_pattern a r c i \<equiv> Pattern_Pair (Pattern_Pair a r) (Pattern_Pair c i)"

definition citation_local_schema :: "(nat,nat,nat) factor_schema" where
  "citation_local_schema=data_rule
    (citation_admission_pattern data_x data_y
      (Pattern_Pair (Pattern_Payload []) (Pattern_Pair data_z (Pattern_Payload [])))
      (Pattern_Pair data_y (Pattern_Payload [])))
    {(0,29,headed_material_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Payload [])) (Pattern_Payload []) (Pattern_Payload []))}"

definition citation_local_whole_schema :: "(nat,nat,nat) factor_schema" where
  "citation_local_whole_schema=data_rule
    (citation_admission_pattern data_x data_y
      (Pattern_Pair (Pattern_Payload []) (Pattern_Payload [])) (Pattern_Pair data_y (Pattern_Payload [])))
    {(0,29,headed_material_pattern data_x data_y (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload []))}"

definition citation_external_whole_schema :: "(nat,nat,nat) factor_schema" where
  "citation_external_whole_schema=data_rule
    (citation_admission_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_z (Pattern_Payload [])) (Pattern_Payload []))
      (Pattern_Pair data_y (Pattern_Payload [])))
    {(0,29,headed_material_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_z data_z) (Pattern_Payload [])) (Pattern_Payload []) (Pattern_Payload [])),
     (1,3,Pattern_Pair data_y data_z)}"

definition citation_external_schema :: "(nat,nat,nat) factor_schema" where
  "citation_external_schema=data_rule
    (citation_admission_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_z (Pattern_Payload []))
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Payload []))) (Pattern_Variable 5))
    {(0,29,headed_material_pattern data_x data_y
      (Pattern_Pair (Pattern_Pair data_y data_z)
        (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Payload []))) (Pattern_Payload []) (Pattern_Payload [])),
     (1,29,headed_material_pattern data_x data_w (Pattern_Payload []) (Pattern_Payload [])
       (Pattern_Pair (Pattern_Variable 4) (Pattern_Payload []))),
     (2,3,Pattern_Pair data_y data_z),(3,3,Pattern_Pair data_y data_w),(4,3,Pattern_Pair data_z data_w),
     (5,6,Pattern_Pair (Pattern_Pair data_y (Pattern_Pair data_w (Pattern_Payload []))) (Pattern_Variable 5))}"

definition citation_admission_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "citation_admission_clauses={(0,citation_local_schema),(1,citation_local_whole_schema),
    (2,citation_external_whole_schema),(3,citation_external_schema)}"

definition citation_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "citation_admission_system=add_view_definition target_admission_system 36 data_x citation_admission_clauses"

lemma citation_admission_system_formed [simp]: "schema_system_formed citation_admission_system"
  unfolding citation_admission_system_def
  by (rule add_recursive_definition_formed[OF target_admission_system_formed])
    (auto simp: citation_admission_clauses_def citation_local_schema_def citation_local_whole_schema_def
      citation_external_whole_schema_def citation_external_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma citation_admission_definitions [simp]:
  "system_definitions citation_admission_system=insert 36 (system_definitions target_admission_system)"
  by (simp add: citation_admission_system_def)

lemma citation_admission_call:
  "schema_call_formed citation_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions citation_admission_system \<and> term_formed t"
  using added_variable_calls[OF target_admission_system_formed
    citation_admission_system_formed[unfolded citation_admission_system_def] target_admission_call]
  by (simp only: citation_admission_system_def[symmetric])

lemma citation_admission_old_meaning:
  assumes "d\<in>system_definitions target_admission_system"
  shows "(d,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_admission_system"
  using added_definition_preserves_old(2)[OF target_admission_system_formed
    citation_admission_system_formed[unfolded citation_admission_system_def], of d t] assms
  by (auto simp: citation_admission_system_def)

lemma citation_admission_clause [simp]:
  "((36,c),S)\<in>system_clauses citation_admission_system \<longleftrightarrow> (c,S)\<in>citation_admission_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses target_admission_system \<Longrightarrow>
    d\<in>system_definitions target_admission_system" for d c S
    using target_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((36,c),S)\<notin>system_clauses target_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: citation_admission_system_def)
qed

lemma citation_admission_components:
  "(29,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (29,t)\<in>positive_meaning headed_material_system"
  "(3,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (3,t)\<in>positive_meaning headed_material_system"
  "(6,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (6,t)\<in>positive_meaning bag_comparison_system"
  "(35,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow> (\<exists>x. target_value_presents x t)"
  using citation_admission_old_meaning[of 29 t] citation_admission_old_meaning[of 3 t]
    citation_admission_old_meaning[of 6 t] citation_admission_old_meaning[of 35 t]
    target_admission_headed_meaning[of 29 t] target_admission_headed_meaning[of 3 t]
    target_admission_headed_meaning[of 6 t] headed_material_components(3)[of t] target_admission_exact[of t] by auto

lemma citation_admission_valuation:
  "(36,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (data_list_term [h 2])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (Payload_Term [])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (Payload_Term [])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 2) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (data_list_term [h 4])) (h 5) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2),Pair_Term (h 2) (h 3)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
      (29,headed_material_argument (h 0) (h 3) (Payload_Term []) (Payload_Term []) (data_list_term [h 4]))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 3))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 2) (h 3))\<in>positive_meaning headed_material_system \<and>
      (6,Pair_Term (data_list_term [h 1,h 3]) (h 5))\<in>positive_meaning bag_comparison_system)"
proof -
  have ordinary: "\<And>c S. ((36,c),S)\<in>system_clauses citation_admission_system \<Longrightarrow>
    schema_material_premises S={}"
    by (auto simp: citation_admission_clauses_def citation_local_schema_def citation_local_whole_schema_def
      citation_external_whole_schema_def citation_external_schema_def)
  have member: "36\<in>system_definitions citation_admission_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning citation_admission_system)"
  have valuation: "(36,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>citation_admission_clauses \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=citation_admission_system and d=36 and t=t, OF ordinary]
    by (simp only: citation_admission_clause citation_admission_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>citation_admission_clauses \<and> P S) \<longleftrightarrow>
    P citation_local_schema \<or> P citation_local_whole_schema \<or>
    P citation_external_whole_schema \<or> P citation_external_schema" for P
    by (auto simp: citation_admission_clauses_def)
  have premise_family: "(\<forall>s d p. (s,d,p)\<in>A \<longrightarrow> P s d p) \<longleftrightarrow>
    (\<forall>z\<in>A. P (fst z) (fst (snd z)) (snd (snd z)))"
    for A :: "(nat\<times>nat\<times>nat term_pattern) set" and P
    by (auto split: prod.splits)
  have local: "?A citation_local_schema h \<longleftrightarrow>
    (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (data_list_term [h 2])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system" for h
    by (auto simp: citation_local_schema_def schema_variables_def citation_admission_components octets_formed_def)
  have local_whole: "?A citation_local_whole_schema h \<longleftrightarrow>
    (\<forall>i\<in>{0,1}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (Payload_Term [])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system" for h
    by (auto simp: citation_local_whole_schema_def schema_variables_def citation_admission_components octets_formed_def)
  have external_whole: "?A citation_external_whole_schema h \<longleftrightarrow>
    (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (Payload_Term [])) (data_list_term [h 1]) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 2) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system" for h
    by (auto simp: citation_external_whole_schema_def schema_variables_def citation_admission_components octets_formed_def)
  have external: "?A citation_external_schema h \<longleftrightarrow>
    (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (data_list_term [h 4])) (h 5) \<and>
      (29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2),Pair_Term (h 2) (h 3)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system \<and>
      (29,headed_material_argument (h 0) (h 3) (Payload_Term []) (Payload_Term []) (data_list_term [h 4]))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 1) (h 3))\<in>positive_meaning headed_material_system \<and>
      (3,Pair_Term (h 2) (h 3))\<in>positive_meaning headed_material_system \<and>
      (6,Pair_Term (data_list_term [h 1,h 3]) (h 5))\<in>positive_meaning bag_comparison_system" for h
    by (simp only: premise_family)
      (auto simp: citation_external_schema_def schema_variables_def citation_admission_components octets_formed_def)
  show ?thesis by (subst valuation) (simp only: clauses local local_whole external_whole external)
qed

theorem citation_admission_sound:
  assumes holds: "(36,t)\<in>positive_meaning citation_admission_system"
  shows "\<exists>R a r c xs. t=citation_admission_argument a (Payload_Term r) (citation_data_term c)
      (data_list_term (map Payload_Term xs)) \<and> artifact_value_presents R a \<and>
      distinct xs \<and> citation_at R r c (set xs)"
proof -
  consider (local) h where "(\<forall>i\<in>({0,1,2}::nat set). term_formed (h i))"
      "t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (data_list_term [h 2])) (data_list_term [h 1])"
      "(29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
    | (local_whole) h where "(\<forall>i\<in>({0,1}::nat set). term_formed (h i))"
      "t=citation_admission_argument (h 0) (h 1) (Pair_Term (Payload_Term []) (Payload_Term [])) (data_list_term [h 1])"
      "(29,headed_material_argument (h 0) (h 1) (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
    | (external_whole) h where "(\<forall>i\<in>({0,1,2}::nat set). term_formed (h i))"
      "t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (Payload_Term [])) (data_list_term [h 1])"
      "(29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 2) (h 2)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system"
    | (external) h where "(\<forall>i\<in>({0,1,2,3,4,5}::nat set). term_formed (h i))"
      "t=citation_admission_argument (h 0) (h 1) (Pair_Term (data_list_term [h 2]) (data_list_term [h 4])) (h 5)"
      "(29,headed_material_argument (h 0) (h 1) (data_list_term [Pair_Term (h 1) (h 2),Pair_Term (h 2) (h 3)]) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
      "(29,headed_material_argument (h 0) (h 3) (Payload_Term []) (Payload_Term []) (data_list_term [h 4]))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (h 1) (h 2))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (h 1) (h 3))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (h 2) (h 3))\<in>positive_meaning headed_material_system"
      "(6,Pair_Term (data_list_term [h 1,h 3]) (h 5))\<in>positive_meaning bag_comparison_system"
    using holds by (auto simp: citation_admission_valuation)
  then show ?thesis
  proof cases
    case (local h)
    obtain R r v where source: "artifact_value_presents R (h 0)"
      and root: "h 1=Payload_Term r" and literal: "h 2=Payload_Term v"
      and fields: "r\<in>rra_carrier (object_structure R)"
        "headed_incidence (object_structure R) r={(r,v)}" "restrict_basis {r} (object_data R)=empty_basis"
      using local(3) by (auto simp: headed_material_one_row_exact[simplified])
    have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
    have read: "citation_at R r (Local v) {r}"
      using rf fields by (simp add: citation_at_def raw_local_citation_iff)
    show ?thesis by (intro exI[of _ R] exI[of _ "h 0"] exI[of _ r] exI[of _ "Local v"] exI[of _ "[r]"])
      (use local(2) source root literal read in auto)
  next
    case (local_whole h)
    obtain R r where source: "artifact_value_presents R (h 0)" and root: "h 1=Payload_Term r"
      and fields: "r\<in>rra_carrier (object_structure R)"
        "headed_incidence (object_structure R) r={}" "restrict_basis {r} (object_data R)=empty_basis"
      using local_whole(3) by (auto simp: headed_material_empty_exact[simplified]
        data_list_term_injective[where xs="[]", simplified])
    have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
    have read: "citation_at R r Local_Whole {r}"
      using rf fields by (simp add: citation_at_def raw_local_whole_citation_iff)
    show ?thesis by (intro exI[of _ R] exI[of _ "h 0"] exI[of _ r] exI[of _ Local_Whole] exI[of _ "[r]"])
      (use local_whole(2) source root read in auto)
  next
    case (external_whole h)
    obtain R r k where source: "artifact_value_presents R (h 0)"
      and root: "h 1=Payload_Term r" and slot: "h 2=Payload_Term k"
      and fields: "r\<in>rra_carrier (object_structure R)"
        "headed_incidence (object_structure R) r={(k,k)}" "restrict_basis {r} (object_data R)=empty_basis"
      using external_whole(3) by (auto simp: headed_material_one_row_exact[simplified])
    have separate: "r\<noteq>k"
      using external_whole(4) root slot by (auto simp: headed_material_inequality)
    have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
    have read: "citation_at R r (External_Whole k) {r}"
      using rf fields separate by (simp add: citation_at_def raw_external_whole_citation_iff)
    show ?thesis by (intro exI[of _ R] exI[of _ "h 0"] exI[of _ r] exI[of _ "External_Whole k"] exI[of _ "[r]"])
      (use external_whole(2) source root slot read in auto)
  next
    case (external h)
    obtain R r k d where source: "artifact_value_presents R (h 0)"
      and positions: "h 1=Payload_Term r" "h 2=Payload_Term k" "h 3=Payload_Term d"
      and fields: "r\<in>rra_carrier (object_structure R)"
        "headed_incidence (object_structure R) r={(r,k),(k,d)}" "restrict_basis {r} (object_data R)=empty_basis"
      using external(3) by (auto simp: headed_material_two_rows_exact[simplified])
    obtain v where literal: "h 4=Payload_Term v" and leaf: "payload_leaf_at R d v"
      using external(4) by (auto simp: positions headed_material_leaf_value[OF source, simplified])
    have separate: "distinct [r,k,d]"
      using external(5-7) positions by (auto simp: headed_material_inequality)
    have rf: "exact_formed R" using artifact_value_presents_formed[OF source] by simp
    have read: "citation_at R r (External k v) {r,d}"
      using rf fields separate leaf
      by (auto simp: citation_at_def raw_external_citation_iff payload_leaf_at_def)
    have data: "data_elements (map Payload_Term [r,d])" using external(1) positions by auto
    have comparison: "(6,Pair_Term (data_list_term (map Payload_Term [r,d])) (h 5))
      \<in>positive_meaning bag_comparison_system"
      using external(8) positions by simp
    obtain xs where enumeration: "h 5=data_list_term (map Payload_Term xs)" "mset [r,d]=mset xs"
      using comparison by (simp only: bag_comparison_encoded[OF payload_term_inj data]) blast
    have interior: "distinct xs" "set xs={r,d}"
      using enumeration(2) separate distinct_source_mset[of "[r,d]" xs] by auto
    show ?thesis by (intro exI[of _ R] exI[of _ "h 0"] exI[of _ r] exI[of _ "External k v"] exI[of _ xs])
      (use external(2) source positions literal read enumeration(1) interior in auto)
  qed
qed

lemma citation_singleton_interior:
  assumes "distinct xs" "set xs={r}"
  shows "xs=[r]"
proof (cases xs)
  case Nil then show ?thesis using assms(2) by simp
next
  case (Cons x tail)
  have root: "x=r" using assms(2) Cons by auto
  have subset: "set tail\<subseteq>{r}" using assms(2) Cons by auto
  have absent: "r\<notin>set tail" using assms(1) Cons root by simp
  have empty: "set tail={}"
  proof (rule equals0I)
    fix y assume member: "y\<in>set tail"
    have "y\<in>{r}" by (rule subsetD[OF subset member])
    then have "y=r" by simp
    then show False using member absent by simp
  qed
  show ?thesis using Cons root empty by simp
qed

theorem citation_admission_complete:
  assumes source: "artifact_value_presents R a" and distinct: "distinct xs"
    and read: "citation_at R r c (set xs)"
  shows "(36,citation_admission_argument a (Payload_Term r) (citation_data_term c)
    (data_list_term (map Payload_Term xs)))\<in>positive_meaning citation_admission_system"
proof -
  have af: "term_formed a" and rf: "exact_formed R" using artifact_value_presents_formed[OF source] by auto
  have root: "r\<in>rra_carrier (object_structure R)" and root_data: "restrict_basis {r} (object_data R)=empty_basis"
    using read by (auto simp: citation_at_def)
  have rformed: "octets_formed r" using rf root by (auto simp: exact_formed_def)
  have cformed: "term_formed (citation_data_term c)" by (rule citation_data_formed_at[OF read])
  have addresses: "\<forall>x\<in>set xs. octets_formed x"
    using citation_interior_in_carrier[OF read] rf by (auto simp: exact_formed_def)
  have iformed: "term_formed (data_list_term (map Payload_Term xs))"
    using addresses by (simp add: data_list_term_formed)
  show ?thesis
  proof (cases c)
    case (Local v)
    have fields: "headed_incidence (object_structure R) r={(r,v)}" "set xs={r}"
      using read by (auto simp: Local citation_at_def raw_local_citation_iff)
    have xs: "xs=[r]" by (rule citation_singleton_interior[OF distinct fields(2)])
    have vformed: "octets_formed v" using cformed by (simp add: Local)
    have headed: "(29,headed_material_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term r) (Payload_Term v)]) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
      using headed_material_no_data[OF source, of r "[(r,v)]"] root root_data fields(1)
      by (simp add: address_pair_data_def)
    show ?thesis by (simp only: citation_admission_valuation, rule disjI1,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then Payload_Term r else Payload_Term v"])
      (use af rformed vformed headed in \<open>auto simp: Local xs octets_formed_def\<close>)
  next
    case Local_Whole
    have fields: "headed_incidence (object_structure R) r={}" "set xs={r}"
      using read by (auto simp: Local_Whole citation_at_def raw_local_whole_citation_iff)
    have xs: "xs=[r]" by (rule citation_singleton_interior[OF distinct fields(2)])
    have headed: "(29,headed_material_argument a (Payload_Term r)
      (Payload_Term []) (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
      using headed_material_no_data[OF source, of r "[]"] root root_data fields(1) by simp
    show ?thesis by (simp only: citation_admission_valuation, rule disjI2, rule disjI1,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else Payload_Term r"])
      (use af rformed headed in \<open>auto simp: Local_Whole xs octets_formed_def\<close>)
  next
    case (External_Whole k)
    have fields: "r\<noteq>k" "headed_incidence (object_structure R) r={(k,k)}" "set xs={r}"
      using read by (auto simp: External_Whole citation_at_def raw_external_whole_citation_iff)
    have xs: "xs=[r]" by (rule citation_singleton_interior[OF distinct fields(3)])
    have kformed: "octets_formed k" using cformed by (simp add: External_Whole)
    have headed: "(29,headed_material_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term k) (Payload_Term k)]) (Payload_Term []) (Payload_Term []))
      \<in>positive_meaning headed_material_system"
      using headed_material_no_data[OF source, of r "[(k,k)]"] root root_data fields(2)
      by (simp add: address_pair_data_def)
    have apart: "(3,Pair_Term (Payload_Term r) (Payload_Term k))\<in>positive_meaning headed_material_system"
      using fields(1) rformed kformed by (simp add: headed_material_inequality)
    show ?thesis by (simp only: citation_admission_valuation, rule disjI2, rule disjI2, rule disjI1,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then Payload_Term r else Payload_Term k"])
      (use af rformed kformed headed apart in \<open>auto simp: External_Whole xs octets_formed_def\<close>)
  next
    case (External k v)
    obtain d where fields: "distinct [r,k,d]" "headed_incidence (object_structure R) r={(r,k),(k,d)}"
      "headed_incidence (object_structure R) d={}" "payload_at R d v" "set xs={r,d}"
      using read by (auto simp: External citation_at_def raw_external_citation_iff)
    have formed: "octets_formed k" "octets_formed v" "octets_formed d"
      using cformed addresses fields(5) by (auto simp: External)
    have headed: "(29,headed_material_argument a (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term r) (Payload_Term k),Pair_Term (Payload_Term k) (Payload_Term d)])
      (Payload_Term []) (Payload_Term []))\<in>positive_meaning headed_material_system"
      using headed_material_no_data[OF source, of r "[(r,k),(k,d)]"] root root_data fields(1,2)
      by (simp add: address_pair_data_def)
    have leaf: "payload_leaf_at R d v" using rf fields(3,4) by (simp add: payload_leaf_at_def exact_formed_def)
    have payload: "(29,headed_material_argument a (Payload_Term d)
      (Payload_Term []) (Payload_Term []) (data_list_term [Payload_Term v]))
      \<in>positive_meaning headed_material_system"
      using leaf by (simp add: headed_material_leaf[OF source, simplified])
    have apart: "(3,Pair_Term (Payload_Term r) (Payload_Term k))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (Payload_Term r) (Payload_Term d))\<in>positive_meaning headed_material_system"
      "(3,Pair_Term (Payload_Term k) (Payload_Term d))\<in>positive_meaning headed_material_system"
      using fields(1) rformed formed by (auto simp: headed_material_inequality)
    have multisets: "mset [r,d]=mset xs"
      using fields(1,5) distinct set_eq_iff_mset_eq_distinct[of "[r,d]" xs] by auto
    have mapped: "mset (map Payload_Term [r,d])=mset (map Payload_Term xs)"
      using arg_cong[OF multisets, of "image_mset Payload_Term"] by simp
    have comparison: "(6,Pair_Term (data_list_term [Payload_Term r,Payload_Term d])
      (data_list_term (map Payload_Term xs)))\<in>positive_meaning bag_comparison_system"
      by (simp only: bag_comparison_lists) (use mapped addresses rformed formed in auto)
    show ?thesis by (simp only: citation_admission_valuation, rule disjI2, rule disjI2, rule disjI2,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then Payload_Term r else if i=2 then Payload_Term k
        else if i=3 then Payload_Term d else if i=4 then Payload_Term v else data_list_term (map Payload_Term xs)"])
      (use af rformed formed iformed headed payload apart comparison in \<open>auto simp: External octets_formed_def\<close>)
  qed
qed

theorem citation_admission_exact:
  "(36,t)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (\<exists>R a r c xs. t=citation_admission_argument a (Payload_Term r) (citation_data_term c)
      (data_list_term (map Payload_Term xs)) \<and> artifact_value_presents R a \<and>
      distinct xs \<and> citation_at R r c (set xs))"
  using citation_admission_sound citation_admission_complete by blast

corollary citation_admission_at_source:
  assumes source: "artifact_value_presents R a"
  shows "(36,citation_admission_argument a k c i)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (\<exists>r d xs. k=Payload_Term r \<and> c=citation_data_term d \<and> i=data_list_term (map Payload_Term xs) \<and>
      distinct xs \<and> citation_at R r d (set xs))"
proof
  assume holds: "(36,citation_admission_argument a k c i)\<in>positive_meaning citation_admission_system"
  obtain S r d xs where fields: "k=Payload_Term r" "c=citation_data_term d"
    "i=data_list_term (map Payload_Term xs)" "artifact_value_presents S a"
    "distinct xs" "citation_at S r d (set xs)"
    using holds by (auto simp: citation_admission_exact)
  have same: "S=R" by (rule artifact_value_presents_unique[OF fields(4) source])
  show "\<exists>r d xs. k=Payload_Term r \<and> c=citation_data_term d \<and>
    i=data_list_term (map Payload_Term xs) \<and> distinct xs \<and> citation_at R r d (set xs)"
    using fields same by blast
next
  assume "\<exists>r d xs. k=Payload_Term r \<and> c=citation_data_term d \<and>
    i=data_list_term (map Payload_Term xs) \<and> distinct xs \<and> citation_at R r d (set xs)"
  then obtain r d xs where fields: "k=Payload_Term r" "c=citation_data_term d"
    "i=data_list_term (map Payload_Term xs)" "distinct xs" "citation_at R r d (set xs)" by blast
  show "(36,citation_admission_argument a k c i)\<in>positive_meaning citation_admission_system"
    using citation_admission_complete[OF source fields(4,5)] by (simp only: fields(1-3))
qed

corollary citation_admission_rows:
  assumes source: "artifact_value_presents R a"
  shows "(36,citation_admission_argument a (Payload_Term r) (citation_data_term c)
    (data_list_term (map Payload_Term xs)))\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    distinct xs \<and> citation_at R r c (set xs)"
  by (auto simp: citation_admission_at_source[OF source] data_list_term_injective
    injective_mapped_lists[OF payload_term_inj] dest: injD[OF citation_data_term_injective])

corollary citation_admission_result_unique:
  assumes source: "artifact_value_presents R a"
    and first: "(36,citation_admission_argument a k c i)\<in>positive_meaning citation_admission_system"
    and second: "(36,citation_admission_argument a k d j)\<in>positive_meaning citation_admission_system"
  shows "c=d \<and> (6,Pair_Term i j)\<in>positive_meaning bag_comparison_system"
proof -
  obtain r b xs where left: "k=Payload_Term r" "c=citation_data_term b"
    "i=data_list_term (map Payload_Term xs)" "distinct xs" "citation_at R r b (set xs)"
    using first by (auto simp: citation_admission_at_source[OF source])
  obtain e ys where right: "d=citation_data_term e"
    "j=data_list_term (map Payload_Term ys)" "distinct ys" "citation_at R r e (set ys)"
    using second left(1) by (auto simp: citation_admission_at_source[OF source])
  have same: "b=e" "set xs=set ys" by (rule citation_at_unique[OF left(5) right(4)])+
  have multisets: "mset xs=mset ys"
    using left(4) right(3) same(2) set_eq_iff_mset_eq_distinct[of xs ys] by auto
  have formed: "term_formed i" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF first]]
      schema_call_formed_target[OF positive_meaning_formed[OF second]] by auto
  show ?thesis using left(2,3) right(1,2) same(1) formed multisets
    by (simp add: bag_comparison_lists data_list_term_formed injective_mapped_multisets[OF payload_term_inj])
qed

corollary citation_admission_presentation_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R b"
  shows "(36,citation_admission_argument a k c i)\<in>positive_meaning citation_admission_system \<longleftrightarrow>
    (36,citation_admission_argument b k c i)\<in>positive_meaning citation_admission_system"
  by (simp only: citation_admission_at_source[OF assms(1)] citation_admission_at_source[OF assms(2)])

section \<open>One native package admits target data and citation readings\<close>

theorem native_target_citation_checking:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q dt dc.
    dt\<noteq>dc \<and> closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] dt t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (\<exists>x. target_value_presents x t)))) \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] dc t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>R a r c xs. t=citation_admission_argument a (Payload_Term r) (citation_data_term c)
            (data_list_term (map Payload_Term xs)) \<and> artifact_value_presents R a \<and>
            distinct xs \<and> citation_at R r c (set xs)))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions citation_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions citation_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed citation_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning citation_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF citation_admission_system_formed] by blast
  let ?future="\<lambda>d test. \<forall>t. term_formed t \<longrightarrow>
    (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> test t))"
  have entry: "?future (g d) (\<lambda>t. (d,t)\<in>positive_meaning citation_admission_system)"
    if member: "d\<in>system_definitions citation_admission_system" for d
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning citation_admission_system)"
      using future[rule_format, OF member tf]
      by (simp only: citation_admission_call member tf simp_thms) blast
  qed
  have target: "?future (g 35) (\<lambda>t. \<exists>x. target_value_presents x t)"
    using entry[of 35] by (simp add: citation_admission_components)
  have citation: "?future (g 36) (\<lambda>t. \<exists>R a r c xs. t=citation_admission_argument a (Payload_Term r) (citation_data_term c)
      (data_list_term (map Payload_Term xs)) \<and> artifact_value_presents R a \<and>
      distinct xs \<and> citation_at R r c (set xs))"
    using entry[of 36] by (simp add: citation_admission_exact)
  have separate: "g 35\<noteq>g 36" using inj_onD[OF injective, of 35 36] by auto
  show ?thesis by (intro exI[of _ E] exI[of _ pu] exI[of _ Q] exI[of _ "g 35"] exI[of _ "g 36"])
    (use separate closed target citation in blast)
qed

text \<open>
  The complete root head selects one of the four existing citation shapes.
  Ordinary material and inequality calls check its exact geometry, including
  the external address leaf and its one functional payload. Local targets
  may coincide with the root. External slots and the address leaf retain the
  grammar's pairwise separation. Incoming incidence and material elsewhere
  remain in the complete source without invalidating a relative reading.

  The result carries two independent optional opaque operands and a complete
  interior enumeration. The interior is checked against the actual root and
  leaf, with every order accepted and repetition rejected. Quotation and
  pattern composition use this interior separately from exposed slots.

  Exactness covers all input terms, including malformed proposed readings.
  Each source presentation yields the same recovered citation and interior
  set. Target and citation admission occupy distinct actual sites in one
  closed native package fixed before all future formed arguments. Every
  constructed application preserves its canonical program environment.

  These six ordinary clauses extend the existing program to thirty-seven
  definitions and sixty-eight clauses. Citation interpretation, higher
  grammar, finite correctness evidence, reflection, and the complete
  internal transition protocol remain separate obligations.
\<close>

end
