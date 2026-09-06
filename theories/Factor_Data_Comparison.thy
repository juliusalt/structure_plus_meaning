theory Factor_Data_Comparison
  imports Factor_Distinct_Payloads Factor_View_Definitions Factor_Rule_Instances
begin

section \<open>Ordinary recursive definitions over the existing payload program\<close>

abbreviation data_rule :: "nat term_pattern \<Rightarrow>
  (nat \<times> (nat \<times> nat term_pattern)) set \<Rightarrow> (nat,nat,nat) factor_schema" where
  "data_rule h B \<equiv> \<lparr>schema_conclusion=h, schema_premises=B, schema_material_premises={}\<rparr>"

abbreviation data_x :: "nat term_pattern" where "data_x \<equiv> Pattern_Variable 0"
abbreviation data_y :: "nat term_pattern" where "data_y \<equiv> Pattern_Variable 1"
abbreviation data_z :: "nat term_pattern" where "data_z \<equiv> Pattern_Variable 2"
abbreviation data_w :: "nat term_pattern" where "data_w \<equiv> Pattern_Variable 3"

fun data_list_pattern :: "'a term_pattern list \<Rightarrow> 'a term_pattern" where
  "data_list_pattern []=Pattern_Payload []"
| "data_list_pattern (p#ps)=Pattern_Pair p (data_list_pattern ps)"

lemma evaluate_data_list_pattern [simp]:
  "evaluate_pattern f (data_list_pattern ps)=data_list_term (map (evaluate_pattern f) ps)"
  by (induction ps) auto

definition data_payload_schema :: "(nat,nat,nat) factor_schema" where
  "data_payload_schema=data_rule data_x {(0,1,data_list_pattern [data_x])}"

definition data_pair_schema :: "(nat,nat,nat) factor_schema" where
  "data_pair_schema=data_rule (Pattern_Pair data_x data_y) {(0,2,data_x),(1,2,data_y)}"

definition data_recognition_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "data_recognition_clauses={(0,data_payload_schema),(1,data_pair_schema)}"

definition data_recognition_system :: "(nat,nat,nat,nat) schema_system" where
  "data_recognition_system=add_view_definition distinct_payloads_system 2 data_x data_recognition_clauses"

definition data_payload_difference_schema :: "(nat,nat,nat) factor_schema" where
  "data_payload_difference_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,1,data_list_pattern [data_x,data_y])}"

definition data_left_leaf_schema :: "(nat,nat,nat) factor_schema" where
  "data_left_leaf_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_z))
    {(0,1,data_list_pattern [data_x]),(1,2,data_y),(2,2,data_z)}"

definition data_right_leaf_schema :: "(nat,nat,nat) factor_schema" where
  "data_right_leaf_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,2,data_x),(1,2,data_y),(2,1,data_list_pattern [data_z])}"

definition data_left_difference_schema :: "(nat,nat,nat) factor_schema" where
  "data_left_difference_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,3,Pattern_Pair data_x data_z),(1,2,data_y),(2,2,data_w)}"

definition data_right_difference_schema :: "(nat,nat,nat) factor_schema" where
  "data_right_difference_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,2,data_x),(1,2,data_z),(2,3,Pattern_Pair data_y data_w)}"

definition data_comparison_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "data_comparison_clauses={(0,data_payload_difference_schema),(1,data_left_leaf_schema),
    (2,data_right_leaf_schema),(3,data_left_difference_schema),(4,data_right_difference_schema)}"

definition data_comparison_system :: "(nat,nat,nat,nat) schema_system" where
  "data_comparison_system=add_view_definition data_recognition_system 3 data_x data_comparison_clauses"

lemmas data_recognition_schema_defs = data_payload_schema_def data_pair_schema_def
lemmas data_comparison_schema_defs = data_payload_difference_schema_def data_left_leaf_schema_def
  data_right_leaf_schema_def data_left_difference_schema_def data_right_difference_schema_def

lemma data_recognition_system_formed [simp]: "schema_system_formed data_recognition_system"
  unfolding data_recognition_system_def
  by (rule add_recursive_definition_formed[OF distinct_payloads_system_formed])
    (auto simp: data_recognition_clauses_def data_recognition_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_recognition_definitions [simp]: "system_definitions data_recognition_system={0,1,2}"
  by (auto simp: data_recognition_system_def)

lemma data_comparison_system_formed [simp]: "schema_system_formed data_comparison_system"
  unfolding data_comparison_system_def
  by (rule add_recursive_definition_formed[OF data_recognition_system_formed])
    (auto simp: data_comparison_clauses_def data_comparison_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_comparison_definitions [simp]: "system_definitions data_comparison_system={0,1,2,3}"
  by (auto simp: data_comparison_system_def)

lemma data_recognition_call:
  "schema_call_formed data_recognition_system d t \<longleftrightarrow> d\<in>{0,1,2} \<and> term_formed t"
  by (simp only: schema_call_formed_def data_recognition_system_formed)
    (auto simp: data_recognition_system_def distinct_payloads_system_def)

lemma data_comparison_call:
  "schema_call_formed data_comparison_system d t \<longleftrightarrow> d\<in>{0,1,2,3} \<and> term_formed t"
  by (simp only: schema_call_formed_def data_comparison_system_formed)
    (auto simp: data_comparison_system_def data_recognition_system_def distinct_payloads_system_def)

theorem data_recognition_old_meaning:
  assumes "d\<in>{0,1}"
  shows "(d,t)\<in>positive_meaning data_recognition_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning distinct_payloads_system"
  using added_definition_preserves_old(2)[OF distinct_payloads_system_formed
    data_recognition_system_formed[unfolded data_recognition_system_def], of d t] assms
  by (auto simp: data_recognition_system_def)

theorem data_comparison_old_meaning:
  assumes "d\<in>{0,1,2}"
  shows "(d,t)\<in>positive_meaning data_comparison_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_recognition_system"
  using added_definition_preserves_old(2)[OF data_recognition_system_formed
    data_comparison_system_formed[unfolded data_comparison_system_def], of d t] assms
  by (auto simp: data_comparison_system_def)

lemma data_comparison_payloads:
  "(1,t)\<in>positive_meaning data_comparison_system \<longleftrightarrow>
    (1,t)\<in>positive_meaning distinct_payloads_system"
  using data_comparison_old_meaning[of 1 t] data_recognition_old_meaning[of 1 t] by auto

lemma data_recognition_rule:
  assumes clause: "(c,S)\<in>data_recognition_clauses"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning data_recognition_system"
  shows "(2,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning data_recognition_system"
proof -
  have selected: "((2,c),S)\<in>system_clauses data_recognition_system"
    using clause by (simp add: data_recognition_system_def)
  have sf: "schema_formed S" and ordinary: "schema_material_premises S={}"
    using clause by (auto simp: data_recognition_clauses_def data_recognition_schema_defs
      schema_formed_def single_valued_def rel_dom_def octets_formed_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed data_recognition_system 2 (evaluate_pattern f (schema_conclusion S))"
    using tf by (simp add: data_recognition_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF selected ordinary assignment call support])
qed

lemma data_comparison_rule:
  assumes clause: "(c,S)\<in>data_comparison_clauses"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning data_comparison_system"
  shows "(3,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning data_comparison_system"
proof -
  have selected: "((3,c),S)\<in>system_clauses data_comparison_system"
    using clause by (simp add: data_comparison_system_def)
  have sf: "schema_formed S" and ordinary: "schema_material_premises S={}"
    using clause by (auto simp: data_comparison_clauses_def data_comparison_schema_defs
      schema_formed_def single_valued_def rel_dom_def octets_formed_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed data_comparison_system 3 (evaluate_pattern f (schema_conclusion S))"
    using tf by (simp add: data_comparison_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF selected ordinary assignment call support])
qed

section \<open>Recognition is exact on every future term\<close>

theorem data_recognition_sound:
  assumes holds: "(2,t)\<in>positive_meaning data_recognition_system"
  shows "term_formed t \<and> self_contained_term t"
proof -
  have invariant: "(2::nat)=2 \<longrightarrow> self_contained_term t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=2 \<longrightarrow> self_contained_term t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses data_recognition_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed data_recognition_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning data_recognition_system \<and>
        (e=2 \<longrightarrow> self_contained_term (evaluate_pattern f p))"
    show "d=2 \<longrightarrow> self_contained_term (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=2"
      then have cases: "S=data_payload_schema \<or> S=data_pair_schema"
        using clause by (auto simp: data_recognition_system_def data_recognition_clauses_def distinct_payloads_system_def)
      then show "self_contained_term (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=data_payload_schema"
        have leaf: "(1,data_list_term [f 0])\<in>positive_meaning data_recognition_system"
          using support schema by (auto simp: data_payload_schema_def)
        have "\<exists>v. octets_formed v \<and> f 0=Payload_Term v"
          using leaf data_recognition_old_meaning[of 1 "data_list_term [f 0]"]
            payload_recognition_exact[of "f 0"] by auto
        then show ?thesis by (simp add: schema data_payload_schema_def) auto
      next
        assume schema: "S=data_pair_schema"
        then show ?thesis using support by (auto simp: data_pair_schema_def)
      qed
    qed
  qed
  have tf: "term_formed t"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by blast
  show ?thesis using invariant tf by simp
qed

theorem data_recognition_complete:
  assumes "term_formed t" "self_contained_term t"
  shows "(2,t)\<in>positive_meaning data_recognition_system"
  using assms
proof (induction t)
  case (Target_Term x)
  then show ?case by simp
next
  case (Payload_Term v)
  have old: "(1,data_list_term [Payload_Term v])\<in>positive_meaning distinct_payloads_system"
    using payload_recognition_exact[of "Payload_Term v"] Payload_Term.prems by auto
  have support: "(1,data_list_term [Payload_Term v])\<in>positive_meaning data_recognition_system"
    using old data_recognition_old_meaning[of 1 "data_list_term [Payload_Term v]"] by auto
  have result: "(2,evaluate_pattern (\<lambda>_. Payload_Term v) (schema_conclusion data_payload_schema))
    \<in>positive_meaning data_recognition_system"
    by (rule data_recognition_rule[where c=0])
      (use Payload_Term.prems support in \<open>auto simp: data_recognition_clauses_def data_payload_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: data_payload_schema_def)
next
  case (Pair_Term x y)
  have children: "(2,x)\<in>positive_meaning data_recognition_system" "(2,y)\<in>positive_meaning data_recognition_system"
    using Pair_Term.IH Pair_Term.prems by auto
  let ?f="\<lambda>a::nat. if a=0 then x else y"
  have result: "(2,evaluate_pattern ?f (schema_conclusion data_pair_schema))\<in>positive_meaning data_recognition_system"
    by (rule data_recognition_rule[where c=1])
      (use Pair_Term.prems children in \<open>auto simp: data_recognition_clauses_def data_pair_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: data_pair_schema_def)
qed

theorem data_recognition_exact:
  "(2,t)\<in>positive_meaning data_recognition_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using data_recognition_sound data_recognition_complete by blast

lemma data_comparison_recognizes:
  "(2,t)\<in>positive_meaning data_comparison_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using data_comparison_old_meaning[of 2 t] data_recognition_exact[of t] by auto

section \<open>Structural inequality has an exact complete data domain\<close>

theorem data_comparison_sound:
  assumes holds: "(3,t)\<in>positive_meaning data_comparison_system"
  shows "\<exists>x y. t=Pair_Term x y \<and> term_formed x \<and> term_formed y \<and>
    self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y"
proof -
  have invariant: "(3::nat)=3 \<longrightarrow> (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t.
    d=3 \<longrightarrow> (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses data_comparison_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed data_comparison_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning data_comparison_system \<and>
        (e=3 \<longrightarrow> (\<exists>x y. evaluate_pattern f p=Pair_Term x y \<and>
          self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y))"
    show "d=3 \<longrightarrow> (\<exists>x y. evaluate_pattern f (schema_conclusion S)=Pair_Term x y \<and>
      self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)"
    proof
      assume "d=3"
      then have cases: "S=data_payload_difference_schema \<or> S=data_left_leaf_schema \<or>
        S=data_right_leaf_schema \<or> S=data_left_difference_schema \<or> S=data_right_difference_schema"
        using clause by (auto simp: data_comparison_system_def data_comparison_clauses_def
          data_recognition_system_def data_recognition_clauses_def distinct_payloads_system_def)
      have leaf: "\<And>x. (1,data_list_term [x])\<in>positive_meaning data_comparison_system \<Longrightarrow>
        \<exists>v. octets_formed v \<and> x=Payload_Term v"
        using data_comparison_payloads payload_recognition_exact by blast
      have unequal: "\<And>x y. (1,data_list_term [x,y])\<in>positive_meaning data_comparison_system \<Longrightarrow>
        self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y"
      proof -
        fix x y assume "(1,data_list_term [x,y])\<in>positive_meaning data_comparison_system"
        then have old: "(1,data_list_term [x,y])\<in>positive_meaning distinct_payloads_system"
          using data_comparison_payloads by blast
        show "self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y"
          using distinct_payload_term_list_sound[OF old] by auto
      qed
      have data: "\<And>x. (2,x)\<in>positive_meaning data_comparison_system \<Longrightarrow> self_contained_term x"
        using data_comparison_recognizes by blast
      consider (payload) "S=data_payload_difference_schema"
        | (left_leaf) "S=data_left_leaf_schema" | (right_leaf) "S=data_right_leaf_schema"
        | (left_child) "S=data_left_difference_schema" | (right_child) "S=data_right_difference_schema"
        using cases by blast
      then show "\<exists>x y. evaluate_pattern f (schema_conclusion S)=Pair_Term x y \<and>
        self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y"
      proof cases
        case payload
        have checked: "(1,data_list_term [f 0,f 1])\<in>positive_meaning data_comparison_system"
          using support payload by (auto simp: data_payload_difference_schema_def)
        have result: "self_contained_term (f 0) \<and> self_contained_term (f 1) \<and> f 0\<noteq>f 1"
          by (rule unequal[OF checked])
        show ?thesis using result payload by (auto simp: data_payload_difference_schema_def)
      next
        case left_leaf
        have checked: "(1,data_list_term [f 0])\<in>positive_meaning data_comparison_system"
          and children: "(2,f 1)\<in>positive_meaning data_comparison_system" "(2,f 2)\<in>positive_meaning data_comparison_system"
          using support left_leaf by (auto simp: data_left_leaf_schema_def)
        obtain v where shape: "f 0=Payload_Term v" using leaf[OF checked] by blast
        have formed: "self_contained_term (f 1)" "self_contained_term (f 2)"
          by (rule data[OF children(1)], rule data[OF children(2)])
        show ?thesis using shape formed left_leaf by (auto simp: data_left_leaf_schema_def)
      next
        case right_leaf
        have checked: "(1,data_list_term [f 2])\<in>positive_meaning data_comparison_system"
          and children: "(2,f 0)\<in>positive_meaning data_comparison_system" "(2,f 1)\<in>positive_meaning data_comparison_system"
          using support right_leaf by (auto simp: data_right_leaf_schema_def)
        obtain v where shape: "f 2=Payload_Term v" using leaf[OF checked] by blast
        have formed: "self_contained_term (f 0)" "self_contained_term (f 1)"
          by (rule data[OF children(1)], rule data[OF children(2)])
        show ?thesis using shape formed right_leaf by (auto simp: data_right_leaf_schema_def)
      next
        case left_child
        have difference: "self_contained_term (f 0) \<and> self_contained_term (f 2) \<and> f 0\<noteq>f 2"
          and children: "(2,f 1)\<in>positive_meaning data_comparison_system" "(2,f 3)\<in>positive_meaning data_comparison_system"
          using support left_child by (auto simp: data_left_difference_schema_def)
        have formed: "self_contained_term (f 1)" "self_contained_term (f 3)"
          by (rule data[OF children(1)], rule data[OF children(2)])
        show ?thesis using difference formed left_child by (auto simp: data_left_difference_schema_def)
      next
        case right_child
        have difference: "self_contained_term (f 1) \<and> self_contained_term (f 3) \<and> f 1\<noteq>f 3"
          and children: "(2,f 0)\<in>positive_meaning data_comparison_system" "(2,f 2)\<in>positive_meaning data_comparison_system"
          using support right_child by (auto simp: data_right_difference_schema_def)
        have formed: "self_contained_term (f 0)" "self_contained_term (f 2)"
          by (rule data[OF children(1)], rule data[OF children(2)])
        show ?thesis using difference formed right_child by (auto simp: data_right_difference_schema_def)
      qed
    qed
  qed
  have tf: "term_formed t" using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by blast
  show ?thesis using invariant tf by auto
qed

theorem data_comparison_complete:
  assumes xf: "term_formed x" and xc: "self_contained_term x"
    and yf: "term_formed y" and yc: "self_contained_term y" and different: "x\<noteq>y"
  shows "(3,Pair_Term x y)\<in>positive_meaning data_comparison_system"
  using xf xc yf yc different
proof (induction x arbitrary: y)
  case (Target_Term t)
  then show ?case by simp
next
  case (Payload_Term a)
  note outer=Payload_Term.prems
  have af: "octets_formed a" using outer by simp
  have leaf: "(1,data_list_term [Payload_Term a])\<in>positive_meaning data_comparison_system"
    using data_comparison_payloads[of "data_list_term [Payload_Term a]"]
      payload_recognition_exact[of "Payload_Term a"] af by auto
  show ?case
  proof (cases y)
    case (Target_Term t)
    then show ?thesis using outer by simp
  next
    case (Payload_Term b)
    have pair: "(1,data_list_term [Payload_Term a,Payload_Term b])\<in>positive_meaning data_comparison_system"
      using outer Payload_Term unequal_payloads_exact[of a b]
        data_comparison_payloads[of "data_list_term [Payload_Term a,Payload_Term b]"] by auto
    let ?f="\<lambda>i::nat. if i=0 then Payload_Term a else Payload_Term b"
    have result: "(3,evaluate_pattern ?f (schema_conclusion data_payload_difference_schema))
      \<in>positive_meaning data_comparison_system"
      by (rule data_comparison_rule[where c=0])
        (use pair outer Payload_Term in \<open>auto simp: data_comparison_clauses_def data_payload_difference_schema_def schema_variables_def\<close>)
    show ?thesis using result Payload_Term by (simp add: data_payload_difference_schema_def)
  next
    case (Pair_Term b c)
    have children: "(2,b)\<in>positive_meaning data_comparison_system" "(2,c)\<in>positive_meaning data_comparison_system"
      using outer Pair_Term data_comparison_recognizes[of b] data_comparison_recognizes[of c] by auto
    let ?f="\<lambda>i::nat. if i=0 then Payload_Term a else if i=1 then b else c"
    have result: "(3,evaluate_pattern ?f (schema_conclusion data_left_leaf_schema))\<in>positive_meaning data_comparison_system"
      by (rule data_comparison_rule[where c=1])
        (use leaf children outer Pair_Term in \<open>auto simp: data_comparison_clauses_def data_left_leaf_schema_def schema_variables_def\<close>)
    show ?thesis using result Pair_Term by (simp add: data_left_leaf_schema_def)
  qed
next
  case (Pair_Term a b)
  note outer=Pair_Term.prems
  note IH=Pair_Term.IH
  have af: "term_formed a" and bf: "term_formed b" and ac: "self_contained_term a" and bc: "self_contained_term b"
    using outer by auto
  have left: "(2,a)\<in>positive_meaning data_comparison_system" and right: "(2,b)\<in>positive_meaning data_comparison_system"
    using af bf ac bc data_comparison_recognizes[of a] data_comparison_recognizes[of b] by auto
  show ?case
  proof (cases y)
    case (Target_Term t)
    then show ?thesis using outer by simp
  next
    case (Payload_Term c)
    have leaf: "(1,data_list_term [Payload_Term c])\<in>positive_meaning data_comparison_system"
      using outer Payload_Term data_comparison_payloads[of "data_list_term [Payload_Term c]"]
        payload_recognition_exact[of "Payload_Term c"] by auto
    let ?f="\<lambda>i::nat. if i=0 then a else if i=1 then b else Payload_Term c"
    have result: "(3,evaluate_pattern ?f (schema_conclusion data_right_leaf_schema))\<in>positive_meaning data_comparison_system"
      by (rule data_comparison_rule[where c=2])
        (use leaf left right outer Payload_Term in \<open>auto simp: data_comparison_clauses_def data_right_leaf_schema_def schema_variables_def\<close>)
    show ?thesis using result Payload_Term by (simp add: data_right_leaf_schema_def)
  next
    case (Pair_Term c e)
    have cf: "term_formed c" and ef: "term_formed e" and cc: "self_contained_term c" and ec: "self_contained_term e"
      using outer Pair_Term by auto
    have other_left: "(2,c)\<in>positive_meaning data_comparison_system" and other_right: "(2,e)\<in>positive_meaning data_comparison_system"
      using cf ef cc ec data_comparison_recognizes[of c] data_comparison_recognizes[of e] by auto
    let ?f="\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then c else e"
    show ?thesis
    proof (cases "a=c")
      case False
      have child: "(3,Pair_Term a c)\<in>positive_meaning data_comparison_system"
        by (rule IH(1)[OF af ac cf cc False])
      have result: "(3,evaluate_pattern ?f (schema_conclusion data_left_difference_schema))\<in>positive_meaning data_comparison_system"
        by (rule data_comparison_rule[where c=3])
          (use child right other_right af bf cf ef in \<open>auto simp: data_comparison_clauses_def data_left_difference_schema_def schema_variables_def\<close>)
      show ?thesis using result Pair_Term by (simp add: data_left_difference_schema_def)
    next
      case True
      have unequal: "b\<noteq>e" using outer Pair_Term True by auto
      have child: "(3,Pair_Term b e)\<in>positive_meaning data_comparison_system"
        by (rule IH(2)[OF bf bc ef ec unequal])
      have result: "(3,evaluate_pattern ?f (schema_conclusion data_right_difference_schema))\<in>positive_meaning data_comparison_system"
        by (rule data_comparison_rule[where c=4])
          (use child left other_left af bf cf ef in \<open>auto simp: data_comparison_clauses_def data_right_difference_schema_def schema_variables_def\<close>)
      show ?thesis using result Pair_Term by (simp add: data_right_difference_schema_def)
    qed
  qed
qed

theorem data_comparison_exact:
  "(3,t)\<in>positive_meaning data_comparison_system \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> term_formed x \<and> term_formed y \<and>
      self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)"
  using data_comparison_sound data_comparison_complete by blast

theorem native_data_inequality:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d. closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
      au\<notin>environment_uses E \<and> native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions data_comparison_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed data_comparison_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning data_comparison_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF data_comparison_system_formed] by blast
  have member: "3\<in>system_definitions data_comparison_system" by simp
  have every: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
      au\<notin>environment_uses E \<and> native_package_at F pu [] Q \<and> native_application_at F au [] (g 3) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)))"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g 3) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed data_comparison_system 3 t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (3,t)\<in>positive_meaning data_comparison_system"
      using future[rule_format, OF member tf] by blast
    have call: "native_application_formed F pu [] au []"
      using parts(7) tf data_comparison_call[of 3 t] by simp
    have truth: "native_positive_holds F pu [] au [] \<longleftrightarrow>
      (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y)"
      using parts(8) data_comparison_exact[of t] tf by auto
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 3) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (\<exists>x y. t=Pair_Term x y \<and> self_contained_term x \<and> self_contained_term y \<and> x\<noteq>y))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts(1-6) call truth in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 3"])
    (use closed every in blast)
qed

text \<open>
  The two new definitions extend the existing payload program through explicit
  finite clause families. Self-calls use the same positive least fixed point.
  Old definitions retain their complete interfaces, clauses, and meanings.
  The first new definition judges data formation by ordinary truth. Its true
  calls are exactly the payload-and-pair terms used for complete artifact,
  environment, generation, and certificate data. All four application
  interfaces continue to admit every formed term.

  Inequality examines a differing payload, a leaf-versus-pair shape, or a
  differing child. Every other child must still satisfy data formation. Thus a
  difference cannot admit an arbitrary unexamined external target. The converse
  proof covers every pair of different formed data terms by finite structural
  induction. Native compilation fixes one closed program for all future terms.

  This is exact comparison of the supplied data terms. Different complete
  enumerations of one artifact can be different terms; no structural identity
  or semantic equality of their represented subjects is inferred from that
  difference. Extensional collection comparison requires its own definition.
\<close>

end
