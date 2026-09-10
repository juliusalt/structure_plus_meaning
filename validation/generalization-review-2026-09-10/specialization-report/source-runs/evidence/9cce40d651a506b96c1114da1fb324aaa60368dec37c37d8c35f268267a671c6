theory Factor_Related_Lists
  imports Factor_List_Profiles
begin

section \<open>Corresponding sequences retain one shared context\<close>

abbreviation context_relation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "context_relation_argument a x y \<equiv> Pair_Term a (Pair_Term x y)"

abbreviation context_relation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "context_relation_pattern a x y \<equiv> Pattern_Pair a (Pattern_Pair x y)"

definition related_list_nil_schema :: "(nat,nat,nat) factor_schema" where
  "related_list_nil_schema=data_rule
    (context_relation_pattern data_x (Pattern_Payload []) (Pattern_Payload [])) {}"

definition related_list_step_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_list_step_schema element list=data_rule
    (context_relation_pattern data_x (Pattern_Pair data_y data_z)
      (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,element,context_relation_pattern data_x data_y data_w),
      (1,list,context_relation_pattern data_x data_z (Pattern_Variable 4))}"

definition related_list_clauses ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "related_list_clauses element list=
    {(0,related_list_nil_schema),(1,related_list_step_schema element list)}"

locale related_list_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and element_site list_site :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((list_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>related_list_clauses element_site list_site"
    and call: "\<And>t. schema_call_formed P list_site t \<longleftrightarrow> term_formed t"
begin

abbreviation related where
  "related a x y \<equiv> (element_site,context_relation_argument a x y)\<in>positive_meaning P"

lemma element_formed:
  assumes "related a x y"
  shows "term_formed a \<and> term_formed x \<and> term_formed y"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by auto

lemma rule:
  assumes clause: "(c,S)\<in>related_list_clauses element_site list_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(list_site,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((list_site,c),S)\<in>system_clauses P" using clause by (simp add: family)
  have sf: "schema_formed S" using member system_formed by (auto simp: schema_system_formed_def)
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P list_site (evaluate_pattern f (schema_conclusion S))"
    using tf by (simp add: call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

theorem sound:
  assumes holds: "(list_site,t)\<in>positive_meaning P"
  shows "\<exists>a xs ys. t=context_relation_argument a (data_list_term xs) (data_list_term ys) \<and>
    term_formed a \<and> list_all2 (related a) xs ys"
proof -
  let ?Q="\<lambda>t. \<exists>a xs ys. t=context_relation_argument a (data_list_term xs) (data_list_term ys) \<and>
    term_formed a \<and> list_all2 (related a) xs ys"
  have invariant: "list_site=list_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=list_site \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and head: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and>
        (e=list_site \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=list_site \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=list_site"
      then have cases: "S=related_list_nil_schema \<or> S=related_list_step_schema element_site list_site"
        using clause by (auto simp: family related_list_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=related_list_nil_schema"
        have formed: "term_formed (f 0)"
          using assignment by (simp add: schema related_list_nil_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "[]"] exI[of _ "[]"])
          (use formed in \<open>simp add: schema related_list_nil_schema_def\<close>)
      next
        assume schema: "S=related_list_step_schema element_site list_site"
        have first: "related (f 0) (f 1) (f 3)"
          using support schema by (auto simp: related_list_step_schema_def)
        obtain xs ys where tail: "f 2=data_list_term xs" "f 4=data_list_term ys"
          "term_formed (f 0)" "list_all2 (related (f 0)) xs ys"
          using support[rule_format, of 1 list_site
            "context_relation_pattern data_x data_z (Pattern_Variable 4)"] schema
          by (auto simp: related_list_step_schema_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "f 1#xs"] exI[of _ "f 3#ys"])
          (use first tail in \<open>simp add: schema related_list_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem complete:
  assumes formed: "term_formed a" and related: "list_all2 (related a) xs ys"
  shows "(list_site,context_relation_argument a (data_list_term xs) (data_list_term ys))\<in>positive_meaning P"
  using related
proof (induction xs arbitrary: ys)
  case Nil
  have empty: "ys=[]" using Nil.prems by simp
  have result: "(list_site,evaluate_pattern (\<lambda>_. a) (schema_conclusion related_list_nil_schema))
      \<in>positive_meaning P"
    by (rule rule[where c=0])
      (use formed in \<open>auto simp: related_list_clauses_def related_list_nil_schema_def schema_variables_def\<close>)
  show ?case using result empty by (simp add: related_list_nil_schema_def)
next
  case (Cons x xs)
  obtain y zs where parts: "ys=y#zs" "related a x y" "list_all2 (related a) xs zs"
    using Cons.prems by (auto simp: list_all2_Cons1)
  have tail: "(list_site,context_relation_argument a (data_list_term xs) (data_list_term zs))
      \<in>positive_meaning P" by (rule Cons.IH[OF parts(3)])
  have terms: "term_formed x" "term_formed y" "term_formed (data_list_term xs)" "term_formed (data_list_term zs)"
    using element_formed[OF parts(2)] schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?f="\<lambda>i::nat. if i=0 then a else if i=1 then x else if i=2 then data_list_term xs
    else if i=3 then y else data_list_term zs"
  have result: "(list_site,evaluate_pattern ?f
      (schema_conclusion (related_list_step_schema element_site list_site)))\<in>positive_meaning P"
    by (rule rule[where c=1])
      (use formed terms parts(2) tail in
        \<open>auto simp: related_list_clauses_def related_list_step_schema_def schema_variables_def\<close>)
  show ?case using result parts(1) by (simp add: related_list_step_schema_def)
qed

theorem exact:
  "(list_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>a xs ys. t=context_relation_argument a (data_list_term xs) (data_list_term ys) \<and>
      term_formed a \<and> list_all2 (related a) xs ys)"
  using sound complete by blast

corollary lists:
  "(list_site,context_relation_argument a (data_list_term xs) (data_list_term ys))\<in>positive_meaning P \<longleftrightarrow>
    term_formed a \<and> list_all2 (related a) xs ys"
  by (auto simp: exact data_list_term_injective)

theorem readings:
  assumes first: "list_all2 R xs ps" and second: "list_all2 S ys qs" and formed: "term_formed a"
    and compare: "\<And>x y p q. R x p \<Longrightarrow> S y q \<Longrightarrow> related a p q \<longleftrightarrow> C x y"
  shows "(list_site,context_relation_argument a (data_list_term ps) (data_list_term qs))\<in>positive_meaning P
    \<longleftrightarrow> list_all2 C xs ys"
proof -
  have element: "rel_fun R (rel_fun S (=)) C (related a)"
    using compare by (simp add: rel_fun_def)
  have lifted: "rel_fun (list_all2 R) (rel_fun (list_all2 S) (=))
      (list_all2 C) (list_all2 (related a))"
    using list.rel_transfer[where Sa=R and Sc=S] element by (auto simp: rel_fun_def)
  have correspondence: "list_all2 C xs ys=list_all2 (related a) ps qs"
    by (rule rel_funD[OF rel_funD[OF lifted first] second])
  show ?thesis by (simp only: lists formed correspondence simp_thms)
qed

end

text \<open>
  The clauses implement sequence correspondence through an actual callee.
  Every pair of elements has the same context and its own recursive support.
  The final empty boundaries agree; the empty case still requires a formed
  context. No element admission or self-containment is inferred from that
  empty case. Such properties follow from the selected element contract.

  The all-term theorem permits the callee to share a positive dependency
  cycle with the traversal. Once that callee's local reading equations are
  proved, the reading theorem transports the complete list relation without
  repeating its native meaning proof at each use.
\<close>

end
