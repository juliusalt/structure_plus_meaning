theory Factor_Material_Data_Projection
  imports Factor_Artifact_Comparison
begin

section \<open>Recovering addresses from the observed carrier rows\<close>

abbreviation material_projection_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "material_projection_argument a x y \<equiv> Pair_Term a (Pair_Term x y)"

definition atom_lookup_here_schema :: "(nat,nat,nat) factor_schema" where
  "atom_lookup_here_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
      (Pattern_Pair data_y data_x)) {}"

definition atom_lookup_later_schema :: "(nat,nat,nat) factor_schema" where
  "atom_lookup_later_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,8,Pattern_Pair data_y (Pattern_Pair data_z data_w))}"

definition atom_lookup_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "atom_lookup_clauses={(0,atom_lookup_here_schema),(1,atom_lookup_later_schema)}"

definition atom_lookup_system :: "(nat,nat,nat,nat) schema_system" where
  "atom_lookup_system=add_view_definition artifact_comparison_system 8 data_x atom_lookup_clauses"

definition material_projection_empty_schema :: "(nat,nat,nat) factor_schema" where
  "material_projection_empty_schema=data_rule
    (Pattern_Pair data_x
      (Pattern_Pair (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Payload []))) {}"

definition material_projection_address_schema :: "(nat,nat,nat) factor_schema" where
  "material_projection_address_schema=data_rule
    (Pattern_Pair data_x (Pattern_Pair data_y data_z))
    {(0,8,Pattern_Pair data_x (Pattern_Pair data_y data_z))}"

definition material_projection_payload_schema :: "(nat,nat,nat) factor_schema" where
  "material_projection_payload_schema=data_rule
    (Pattern_Pair data_x (Pattern_Pair data_y data_y))
    {(0,1,data_list_pattern [data_y])}"

definition material_projection_pair_schema :: "(nat,nat,nat) factor_schema" where
  "material_projection_pair_schema=data_rule
    (Pattern_Pair data_x
      (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4))))
    {(0,9,Pattern_Pair data_x (Pattern_Pair data_y data_w)),
     (1,9,Pattern_Pair data_x (Pattern_Pair data_z (Pattern_Variable 4)))}"

definition material_projection_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "material_projection_clauses={(0,material_projection_empty_schema),(1,material_projection_address_schema),
    (2,material_projection_payload_schema),(3,material_projection_pair_schema)}"

definition material_data_system :: "(nat,nat,nat,nat) schema_system" where
  "material_data_system=add_view_definition atom_lookup_system 9 data_x material_projection_clauses"

lemmas atom_lookup_schema_defs = atom_lookup_here_schema_def atom_lookup_later_schema_def
lemmas material_projection_schema_defs = material_projection_empty_schema_def
  material_projection_address_schema_def material_projection_payload_schema_def material_projection_pair_schema_def

lemma atom_lookup_system_formed [simp]: "schema_system_formed atom_lookup_system"
  unfolding atom_lookup_system_def
  by (rule add_recursive_definition_formed[OF artifact_comparison_system_formed])
    (auto simp: atom_lookup_clauses_def atom_lookup_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma atom_lookup_definitions [simp]: "system_definitions atom_lookup_system={0,1,2,3,4,5,6,7,8}"
  by (auto simp: atom_lookup_system_def)

lemma material_data_system_formed [simp]: "schema_system_formed material_data_system"
  unfolding material_data_system_def
  by (rule add_recursive_definition_formed[OF atom_lookup_system_formed])
    (auto simp: material_projection_clauses_def material_projection_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma material_data_definitions [simp]: "system_definitions material_data_system={0,1,2,3,4,5,6,7,8,9}"
  by (auto simp: material_data_system_def)

lemma material_data_call:
  "schema_call_formed material_data_system d t \<longleftrightarrow> d\<in>{0,1,2,3,4,5,6,7,8,9} \<and> term_formed t"
proof -
  have previous: "schema_call_formed bag_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions bag_comparison_system \<and> term_formed t"
    by (simp add: bag_comparison_call)
  have comparison: "schema_call_formed artifact_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_comparison_system \<and> term_formed t"
    using added_variable_calls[OF bag_comparison_system_formed
      artifact_comparison_system_formed[unfolded artifact_comparison_system_def] previous]
    by (simp only: artifact_comparison_system_def[symmetric])
  have lookup: "schema_call_formed atom_lookup_system d t \<longleftrightarrow>
    d\<in>system_definitions atom_lookup_system \<and> term_formed t"
    using added_variable_calls[OF artifact_comparison_system_formed
      atom_lookup_system_formed[unfolded atom_lookup_system_def] comparison]
    by (simp only: atom_lookup_system_def[symmetric])
  have result: "schema_call_formed material_data_system d t \<longleftrightarrow>
    d\<in>system_definitions material_data_system \<and> term_formed t"
    using added_variable_calls[OF atom_lookup_system_formed
      material_data_system_formed[unfolded material_data_system_def] lookup]
    by (simp only: material_data_system_def[symmetric])
  show ?thesis using result by simp
qed

lemma atom_lookup_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7}"
  shows "(d,t)\<in>positive_meaning atom_lookup_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_comparison_system"
  using added_definition_preserves_old(2)[OF artifact_comparison_system_formed
    atom_lookup_system_formed[unfolded atom_lookup_system_def], of d t] assms
  by (auto simp: atom_lookup_system_def)

lemma material_data_previous_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8}"
  shows "(d,t)\<in>positive_meaning material_data_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning atom_lookup_system"
  using added_definition_preserves_old(2)[OF atom_lookup_system_formed
    material_data_system_formed[unfolded material_data_system_def], of d t] assms
  by (auto simp: material_data_system_def)

theorem material_data_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7}"
  shows "(d,t)\<in>positive_meaning material_data_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_comparison_system"
  using material_data_previous_meaning[of d t] atom_lookup_old_meaning[OF assms, of t] assms by auto

lemma material_data_payload:
  "(1,data_list_term [t])\<in>positive_meaning material_data_system \<longleftrightarrow>
    (\<exists>b. octets_formed b \<and> t=Payload_Term b)"
  using material_data_old_meaning[of 1 "data_list_term [t]"]
    artifact_comparison_old_meaning[of 1 "data_list_term [t]"]
    bag_comparison_old_meaning[of 1 "data_list_term [t]"]
    data_comparison_payloads[of "data_list_term [t]"] payload_recognition_exact[of t] by auto

lemma material_data_carrier:
  assumes formed: "exact_formed R" and inside: "set A\<subseteq>rra_carrier (object_structure R)"
  shows "(0,Pair_Term (enumeration_term (map (atom_term R) A)) t)\<in>positive_meaning material_data_system
    \<longleftrightarrow> t=data_list_term (map Payload_Term A)"
proof -
  have old: "(0,x)\<in>positive_meaning material_data_system \<longleftrightarrow>
    (0,x)\<in>positive_meaning distinct_payloads_system" for x
    using material_data_old_meaning[of 0 x] artifact_comparison_old_meaning[of 0 x]
      bag_comparison_old_meaning[of 0 x] data_comparison_old_meaning[of 0 x]
      data_recognition_old_meaning[of 0 x] by auto
  show ?thesis by (simp only: old carrier_projection_positive_exact
    carrier_payload_projection_material[OF formed inside])
qed

lemma material_data_new_clauses [simp]:
  "((8,c),S)\<in>system_clauses material_data_system \<longleftrightarrow> (c,S)\<in>atom_lookup_clauses"
  "((9,c),S)\<in>system_clauses material_data_system \<longleftrightarrow> (c,S)\<in>material_projection_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses artifact_comparison_system \<Longrightarrow>
    d\<in>system_definitions artifact_comparison_system" for d c S
    using artifact_comparison_system_formed unfolding schema_system_formed_def by blast
  have absent: "d\<in>{8,9} \<Longrightarrow> ((d,c),S)\<notin>system_clauses artifact_comparison_system" for d c S
    by (auto dest: owned)
  show "((8,c),S)\<in>system_clauses material_data_system \<longleftrightarrow> (c,S)\<in>atom_lookup_clauses"
    "((9,c),S)\<in>system_clauses material_data_system \<longleftrightarrow> (c,S)\<in>material_projection_clauses"
    using absent by (auto simp: material_data_system_def atom_lookup_system_def)
qed

lemma material_data_rule:
  assumes clause: "((d,c),S)\<in>system_clauses material_data_system"
    and ordinary: "schema_material_premises S={}"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning material_data_system"
  shows "(d,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning material_data_system"
proof -
  have sf: "schema_formed S" and member: "d\<in>system_definitions material_data_system"
    using clause material_data_system_formed by (auto simp: schema_system_formed_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed material_data_system d (evaluate_pattern f (schema_conclusion S))"
    using member tf by (simp add: material_data_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF clause ordinary assignment call support])
qed

lemma atom_lookup_equation:
  "(8,material_projection_argument a x y)\<in>positive_meaning material_data_system \<longleftrightarrow>
    (\<exists>r. a=Pair_Term (Pair_Term y x) r \<and> term_formed a) \<or>
    (\<exists>h r. a=Pair_Term h r \<and> term_formed h \<and>
      (8,material_projection_argument r x y)\<in>positive_meaning material_data_system)"
proof
  assume holds: "(8,material_projection_argument a x y)\<in>positive_meaning material_data_system"
  have consequence: "(8,material_projection_argument a x y)\<in>
    schema_consequences material_data_system (positive_meaning material_data_system)"
    using holds positive_meaning_unfold[of material_data_system] by blast
  obtain c S v where clause: "((8,c),S)\<in>system_clauses material_data_system"
    and assignment: "\<forall>i\<in>schema_variables S. term_formed (v i)"
    and head: "material_projection_argument a x y=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning material_data_system"
    using schema_consequences_valuationD[OF consequence] by blast
  show "(\<exists>r. a=Pair_Term (Pair_Term y x) r \<and> term_formed a) \<or>
    (\<exists>h r. a=Pair_Term h r \<and> term_formed h \<and>
      (8,material_projection_argument r x y)\<in>positive_meaning material_data_system)"
    using clause assignment head support
    by (auto simp: atom_lookup_clauses_def atom_lookup_schema_defs schema_variables_def)
next
  assume alternatives: "(\<exists>r. a=Pair_Term (Pair_Term y x) r \<and> term_formed a) \<or>
    (\<exists>h r. a=Pair_Term h r \<and> term_formed h \<and>
      (8,material_projection_argument r x y)\<in>positive_meaning material_data_system)"
  then show "(8,material_projection_argument a x y)\<in>positive_meaning material_data_system"
  proof
    assume "\<exists>r. a=Pair_Term (Pair_Term y x) r \<and> term_formed a"
    then obtain r where shape: "a=Pair_Term (Pair_Term y x) r"
      and formed: "term_formed x" "term_formed y" "term_formed r" by auto
    let ?v="\<lambda>i::nat. if i=0 then y else if i=1 then x else r"
    have result: "(8,evaluate_pattern ?v (schema_conclusion atom_lookup_here_schema))\<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=0])
        (use formed in \<open>auto simp: atom_lookup_clauses_def atom_lookup_here_schema_def schema_variables_def\<close>)
    show ?thesis using result by (simp add: shape atom_lookup_here_schema_def)
  next
    assume "\<exists>h r. a=Pair_Term h r \<and> term_formed h \<and>
      (8,material_projection_argument r x y)\<in>positive_meaning material_data_system"
    then obtain h r where shape: "a=Pair_Term h r" and hf: "term_formed h"
      and child: "(8,material_projection_argument r x y)\<in>positive_meaning material_data_system" by blast
    have formed: "term_formed r" "term_formed x" "term_formed y"
      using positive_meaning_formed[OF child] by (auto simp: material_data_call)
    let ?v="\<lambda>i::nat. if i=0 then h else if i=1 then r else if i=2 then x else y"
    have result: "(8,evaluate_pattern ?v (schema_conclusion atom_lookup_later_schema))\<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=1])
        (use formed hf child in \<open>auto simp: atom_lookup_clauses_def atom_lookup_later_schema_def schema_variables_def\<close>)
    show ?thesis using result by (simp add: shape atom_lookup_later_schema_def)
  qed
qed

lemma material_atoms_formed:
  assumes "exact_formed R" "set A\<subseteq>rra_carrier (object_structure R)"
  shows "term_formed (enumeration_term (map (atom_term R) A))"
  using assms by (auto simp: enumeration_term_formed atom_term_formed)

theorem atom_lookup_exact:
  assumes formed: "exact_formed R" and inside: "set A\<subseteq>rra_carrier (object_structure R)"
  shows "(8,material_projection_argument (enumeration_term (map (atom_term R) A)) x y)
    \<in>positive_meaning material_data_system \<longleftrightarrow>
    (\<exists>a\<in>set A. x=occurrence_term R a \<and> y=Payload_Term a)"
  using inside
proof (induction A)
  case Nil
  then show ?case by (subst atom_lookup_equation) simp
next
  case (Cons a A)
  have member: "a\<in>rra_carrier (object_structure R)" and tail: "set A\<subseteq>rra_carrier (object_structure R)"
    using Cons.prems by auto
  have address: "octets_formed a" using formed member by (auto simp: exact_formed_def)
  have af: "term_formed (enumeration_term (map (atom_term R) A))"
    by (rule material_atoms_formed[OF formed tail])
  show ?case
    by (subst atom_lookup_equation)
      (simp add: atom_term_def occurrence_term_formed formed member address af Cons.IH[OF tail]; blast)
qed

section \<open>One recursive conversion for all observed fields\<close>

lemma material_projection_equation:
  "(9,material_projection_argument a x y)\<in>positive_meaning material_data_system \<longleftrightarrow>
    term_formed a \<and>
    ((x=enumeration_term [] \<and> y=data_list_term []) \<or>
     (8,material_projection_argument a x y)\<in>positive_meaning material_data_system \<or>
     (\<exists>b. octets_formed b \<and> x=Payload_Term b \<and> y=Payload_Term b) \<or>
     (\<exists>x1 x2 y1 y2. x=Pair_Term x1 x2 \<and> y=Pair_Term y1 y2 \<and>
       (9,material_projection_argument a x1 y1)\<in>positive_meaning material_data_system \<and>
       (9,material_projection_argument a x2 y2)\<in>positive_meaning material_data_system))"
proof
  assume holds: "(9,material_projection_argument a x y)\<in>positive_meaning material_data_system"
  have af: "term_formed a" using positive_meaning_formed[OF holds] by (simp add: material_data_call)
  have consequence: "(9,material_projection_argument a x y)\<in>
    schema_consequences material_data_system (positive_meaning material_data_system)"
    using holds positive_meaning_unfold[of material_data_system] by blast
  obtain c S v where clause: "((9,c),S)\<in>system_clauses material_data_system"
    and head: "material_projection_argument a x y=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning material_data_system"
    using schema_consequences_valuationD[OF consequence] by blast
  show "term_formed a \<and>
    ((x=enumeration_term [] \<and> y=data_list_term []) \<or>
     (8,material_projection_argument a x y)\<in>positive_meaning material_data_system \<or>
     (\<exists>b. octets_formed b \<and> x=Payload_Term b \<and> y=Payload_Term b) \<or>
     (\<exists>x1 x2 y1 y2. x=Pair_Term x1 x2 \<and> y=Pair_Term y1 y2 \<and>
       (9,material_projection_argument a x1 y1)\<in>positive_meaning material_data_system \<and>
       (9,material_projection_argument a x2 y2)\<in>positive_meaning material_data_system))"
    using af clause head support
    by (auto simp: material_projection_clauses_def material_projection_schema_defs material_data_payload[simplified]; blast)
next
  assume parts: "term_formed a \<and>
    ((x=enumeration_term [] \<and> y=data_list_term []) \<or>
     (8,material_projection_argument a x y)\<in>positive_meaning material_data_system \<or>
     (\<exists>b. octets_formed b \<and> x=Payload_Term b \<and> y=Payload_Term b) \<or>
     (\<exists>x1 x2 y1 y2. x=Pair_Term x1 x2 \<and> y=Pair_Term y1 y2 \<and>
       (9,material_projection_argument a x1 y1)\<in>positive_meaning material_data_system \<and>
       (9,material_projection_argument a x2 y2)\<in>positive_meaning material_data_system))"
  have af: "term_formed a" using parts by blast
  consider (empty) "x=enumeration_term []" "y=data_list_term []"
    | (address) "(8,material_projection_argument a x y)\<in>positive_meaning material_data_system"
    | (payload) b where "octets_formed b" "x=Payload_Term b" "y=Payload_Term b"
    | (pair) x1 x2 y1 y2 where "x=Pair_Term x1 x2" "y=Pair_Term y1 y2"
      "(9,material_projection_argument a x1 y1)\<in>positive_meaning material_data_system"
      "(9,material_projection_argument a x2 y2)\<in>positive_meaning material_data_system"
    using parts by blast
  then show "(9,material_projection_argument a x y)\<in>positive_meaning material_data_system"
  proof cases
    case empty
    have result: "(9,evaluate_pattern (\<lambda>i::nat. a) (schema_conclusion material_projection_empty_schema))
      \<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=0])
        (use af in \<open>auto simp: material_projection_clauses_def material_projection_empty_schema_def schema_variables_def\<close>)
    show ?thesis using result empty by (simp add: material_projection_empty_schema_def)
  next
    case address
    have formed: "term_formed x" "term_formed y"
      using positive_meaning_formed[OF address] by (auto simp: material_data_call)
    let ?v="\<lambda>i::nat. if i=0 then a else if i=1 then x else y"
    have result: "(9,evaluate_pattern ?v (schema_conclusion material_projection_address_schema))
      \<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=1])
        (use af formed address in \<open>auto simp: material_projection_clauses_def material_projection_address_schema_def schema_variables_def\<close>)
    show ?thesis using result by (simp add: material_projection_address_schema_def)
  next
    case (payload b)
    have recognized: "(1,data_list_term [Payload_Term b])\<in>positive_meaning material_data_system"
      using payload(1) by (simp add: material_data_payload[simplified])
    let ?v="\<lambda>i::nat. if i=0 then a else Payload_Term b"
    have result: "(9,evaluate_pattern ?v (schema_conclusion material_projection_payload_schema))
      \<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=2])
        (use af payload(1) recognized in \<open>auto simp: material_projection_clauses_def material_projection_payload_schema_def schema_variables_def\<close>)
    show ?thesis using result payload by (simp add: material_projection_payload_schema_def)
  next
    case (pair x1 x2 y1 y2)
    have formed: "term_formed x1" "term_formed x2" "term_formed y1" "term_formed y2"
      using positive_meaning_formed[OF pair(3)] positive_meaning_formed[OF pair(4)]
      by (auto simp: material_data_call)
    let ?v="\<lambda>i::nat. if i=0 then a else if i=1 then x1 else if i=2 then x2 else if i=3 then y1 else y2"
    have result: "(9,evaluate_pattern ?v (schema_conclusion material_projection_pair_schema))
      \<in>positive_meaning material_data_system"
      by (rule material_data_rule[where c=3])
        (use af formed pair(3,4) in \<open>auto simp: material_projection_clauses_def material_projection_pair_schema_def schema_variables_def\<close>)
    show ?thesis using result pair(1,2) by (simp add: material_projection_pair_schema_def)
  qed
qed

lemma material_projection_empty:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (enumeration_term []) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=data_list_term []"
proof -
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have af: "term_formed (enumeration_term (map (atom_term R) A))"
    by (rule material_atoms_formed[OF formed inside])
  show ?thesis
    by (subst material_projection_equation)
      (auto simp: af atom_lookup_exact[OF formed inside] occurrence_term_def)
qed

lemma material_projection_occurrence:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and member: "a\<in>rra_carrier (object_structure R)"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (occurrence_term R a) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=Payload_Term a"
proof -
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have af: "term_formed (enumeration_term (map (atom_term R) A))"
    by (rule material_atoms_formed[OF formed inside])
  show ?thesis
    by (subst material_projection_equation)
      (auto simp: af atom_lookup_exact[OF formed inside] occurrence_term_def atoms member)
qed

lemma material_projection_payload:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and payload: "octets_formed b"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (Payload_Term b) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=Payload_Term b"
proof -
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have af: "term_formed (enumeration_term (map (atom_term R) A))"
    by (rule material_atoms_formed[OF formed inside])
  show ?thesis
    by (subst material_projection_equation)
      (auto simp: af payload atom_lookup_exact[OF formed inside] occurrence_term_def)
qed

lemma material_projection_pair:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (Pair_Term x y) t)\<in>positive_meaning material_data_system \<longleftrightarrow>
    (\<exists>u v. t=Pair_Term u v \<and>
      (9,material_projection_argument (enumeration_term (map (atom_term R) A)) x u)\<in>positive_meaning material_data_system \<and>
      (9,material_projection_argument (enumeration_term (map (atom_term R) A)) y v)\<in>positive_meaning material_data_system)"
proof -
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have af: "term_formed (enumeration_term (map (atom_term R) A))"
    by (rule material_atoms_formed[OF formed inside])
  show ?thesis
    by (subst material_projection_equation)
      (auto simp: af atom_lookup_exact[OF formed inside] occurrence_term_def)
qed

lemma material_projection_enumeration:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and each: "\<forall>x\<in>set xs. \<forall>t.
      (9,material_projection_argument (enumeration_term (map (atom_term R) A)) (g x) t)\<in>positive_meaning material_data_system
      \<longleftrightarrow> t=f x"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (enumeration_term (map g xs)) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=data_list_term (map f xs)"
  using each
  by (induction xs arbitrary: t)
    (auto simp: material_projection_empty[OF formed atoms, simplified] material_projection_pair[OF formed atoms])

lemma material_projection_incidence:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and entry: "term_formed (incidence_term R e)"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (incidence_term R e) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=incidence_data e"
proof -
  obtain a b c where shape: "e=(a,b,c)" by (cases e) auto
  have members: "a\<in>rra_carrier (object_structure R)" "b\<in>rra_carrier (object_structure R)"
    "c\<in>rra_carrier (object_structure R)"
    using entry by (auto simp: shape incidence_term_def occurrence_term_formed)
  show ?thesis
    by (simp add: shape incidence_term_def incidence_data_def address_pair_data_def
      material_projection_pair[OF formed atoms] material_projection_occurrence[OF formed atoms members(1)]
      material_projection_occurrence[OF formed atoms members(2)] material_projection_occurrence[OF formed atoms members(3)])
qed

lemma material_projection_attachment:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and entry: "term_formed (attachment_term R z)"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (attachment_term R z) t)\<in>positive_meaning material_data_system \<longleftrightarrow> t=address_pair_data z"
proof -
  obtain a b where shape: "z=(a,b)" by (cases z) auto
  have member: "a\<in>rra_carrier (object_structure R)" and payload: "octets_formed b"
    using entry by (auto simp: shape attachment_term_def occurrence_term_formed)
  show ?thesis
    by (simp add: shape attachment_term_def address_pair_data_def
      material_projection_pair[OF formed atoms] material_projection_occurrence[OF formed atoms member]
      material_projection_payload[OF formed atoms payload])
qed

theorem material_projection_incidence_list:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and entries: "term_formed (enumeration_term (map (incidence_term R) E))"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (enumeration_term (map (incidence_term R) E)) t)\<in>positive_meaning material_data_system
    \<longleftrightarrow> t=data_list_term (map incidence_data E)"
  by (rule material_projection_enumeration[OF formed atoms])
    (use entries in \<open>auto simp: enumeration_term_formed material_projection_incidence[OF formed atoms]\<close>)

theorem material_projection_attachment_list:
  assumes formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    and entries: "term_formed (enumeration_term (map (attachment_term R) B))"
  shows "(9,material_projection_argument (enumeration_term (map (atom_term R) A))
    (enumeration_term (map (attachment_term R) B)) t)\<in>positive_meaning material_data_system
    \<longleftrightarrow> t=data_list_term (map address_pair_data B)"
  by (rule material_projection_enumeration[OF formed atoms])
    (use entries in \<open>auto simp: enumeration_term_formed material_projection_attachment[OF formed atoms]\<close>)

text \<open>
  Two ordinary definitions recover addresses and convert observed terms.
  Lookup may use any matching carrier row. Against a complete observation,
  that row supplies exactly the original address of the occurrence anchor.
  Conversion replaces the observation's empty terminator, preserves complete
  opaque payloads, and converts both children of each pair. Incidence and
  attachment fields therefore use the same recursive definition. Their exact
  results preserve enumeration order, every endpoint, and every repeated entry.

  The equations characterize the existing positive meaning of six displayed
  clauses. They introduce no semantic callback, independent traversal rule,
  or permission to activate definitions in a material operand. Lookup alone
  does not validate its unexamined tail; the complete material observation
  supplies that boundary when these definitions support artifact admission.
\<close>

end
