theory Factor_List_Folds
  imports Factor_List_Profiles Factor_Data_List_Operations List_Relation_Folds
begin

section \<open>Two ordinary clauses implement the general right fold\<close>

definition list_fold_nil_schema :: "(nat,nat,nat) factor_schema" where
  "list_fold_nil_schema=data_rule
    (collection_join_pattern data_x (Pattern_Payload []) data_x) {}"

definition list_fold_step_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "list_fold_step_schema step recursive=data_rule
    (collection_join_pattern data_x (Pattern_Pair data_y data_z) data_w)
    {(0,recursive,collection_join_pattern data_x data_z (Pattern_Variable 4)),
     (1,step,collection_join_pattern data_y (Pattern_Variable 4) data_w)}"

definition list_fold_clauses ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "list_fold_clauses step recursive=
    {(0,list_fold_nil_schema),(1,list_fold_step_schema step recursive)}"

locale list_fold_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and step_site fold_site :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((fold_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>list_fold_clauses step_site fold_site"
    and call: "\<And>t. schema_call_formed P fold_site t \<longleftrightarrow> term_formed t"
begin

abbreviation step where
  "step x a y \<equiv> (step_site,collection_join_argument x a y)\<in>positive_meaning P"

lemma step_formed:
  assumes "step x a y"
  shows "term_formed x \<and> term_formed a \<and> term_formed y"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by auto

lemma rule:
  assumes clause: "(c,S)\<in>list_fold_clauses step_site fold_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning P"
  shows "(fold_site,evaluate_pattern h (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((fold_site,c),S)\<in>system_clauses P" using clause by (simp add: family)
  have schema: "schema_formed S" using system_formed member by (auto simp: schema_system_formed_def)
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: list_fold_clauses_def list_fold_nil_schema_def list_fold_step_schema_def)
  have formed: "term_formed (evaluate_pattern h (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use schema assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P fold_site (evaluate_pattern h (schema_conclusion S))"
    using formed by (simp add: call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

theorem sound:
  assumes holds: "(fold_site,t)\<in>positive_meaning P"
  shows "\<exists>z xs y. t=collection_join_argument z (data_list_term xs) y \<and>
    term_formed z \<and> fold_relation step xs z y"
proof -
  let ?Q="\<lambda>t. \<exists>z xs y. t=collection_join_argument z (data_list_term xs) y \<and>
    term_formed z \<and> fold_relation step xs z y"
  have invariant: "fold_site=fold_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=fold_site \<longrightarrow> ?Q t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and head: "schema_call_formed P d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning P \<and>
        (e=fold_site \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=fold_site \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=fold_site"
      then have alternatives: "S=list_fold_nil_schema \<or> S=list_fold_step_schema step_site fold_site"
        using clause by (auto simp: family list_fold_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=list_fold_nil_schema"
        have formed: "term_formed (h 0)"
          using assignment by (simp add: schema list_fold_nil_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "h 0"] exI[of _ "[]"] exI[of _ "h 0"])
          (use formed in \<open>simp add: schema list_fold_nil_schema_def\<close>)
      next
        assume schema: "S=list_fold_step_schema step_site fold_site"
        obtain xs where tail: "h 2=data_list_term xs" "term_formed (h 0)"
          "fold_relation step xs (h 0) (h 4)"
          using support[rule_format, of 0 fold_site "collection_join_pattern data_x data_z (Pattern_Variable 4)"]
          by (auto simp: schema list_fold_step_schema_def)
        have first: "step (h 1) (h 4) (h 3)"
          using support by (auto simp: schema list_fold_step_schema_def)
        show ?thesis by (intro exI[of _ "h 0"] exI[of _ "h 1#xs"] exI[of _ "h 3"])
          (use tail first in \<open>auto simp: schema list_fold_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem complete:
  assumes seed: "term_formed z" and relation: "fold_relation step xs z y"
  shows "(fold_site,collection_join_argument z (data_list_term xs) y)\<in>positive_meaning P"
  using relation
proof (induction xs arbitrary: y)
  case Nil
  have same: "y=z" using Nil.prems by simp
  have result: "(fold_site,evaluate_pattern (\<lambda>_. z) (schema_conclusion list_fold_nil_schema))\<in>positive_meaning P"
    by (rule rule[where c=0])
      (use seed in \<open>auto simp: list_fold_clauses_def list_fold_nil_schema_def schema_variables_def\<close>)
  show ?case using result same by (simp add: list_fold_nil_schema_def)
next
  case (Cons x xs)
  obtain a where tail: "fold_relation step xs z a" and first: "step x a y"
    using Cons.prems by auto
  have recursive: "(fold_site,collection_join_argument z (data_list_term xs) a)\<in>positive_meaning P"
    by (rule Cons.IH[OF tail])
  have formed: "term_formed x" "term_formed a" "term_formed y" "term_formed (data_list_term xs)"
    using step_formed[OF first] schema_call_formed_target[OF positive_meaning_formed[OF recursive]] by auto
  let ?h="\<lambda>i::nat. if i=0 then z else if i=1 then x else if i=2 then data_list_term xs else if i=3 then y else a"
  have result: "(fold_site,evaluate_pattern ?h (schema_conclusion (list_fold_step_schema step_site fold_site)))
      \<in>positive_meaning P"
    by (rule rule[where c=1])
      (use seed formed recursive first in
        \<open>auto simp: list_fold_clauses_def list_fold_step_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: list_fold_step_schema_def)
qed

theorem exact:
  "(fold_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>z xs y. t=collection_join_argument z (data_list_term xs) y \<and>
      term_formed z \<and> fold_relation step xs z y)"
  using sound complete by blast

corollary at_list:
  "(fold_site,collection_join_argument z (data_list_term xs) y)\<in>positive_meaning P \<longleftrightarrow>
    term_formed z \<and> fold_relation step xs z y"
  by (auto simp: exact data_list_term_injective)

theorem encoded:
  assumes seed: "E z" "term_formed (g z)"
    and element: "\<And>a p q. E a \<Longrightarrow>
      step p (g a) q \<longleftrightarrow> (\<exists>x. D x \<and> p=h x \<and> q=g (f x a))"
    and closed: "\<And>x a. D x \<Longrightarrow> E a \<Longrightarrow> E (f x a)"
  shows "(fold_site,collection_join_argument (g z) p q)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. D x) \<and> p=data_list_term (map h xs) \<and> q=g (foldr f xs z))"
proof -
  have relation: "fold_relation step ps (g z) q \<longleftrightarrow>
      (\<exists>xs. (\<forall>x\<in>set xs. D x) \<and> ps=map h xs \<and> q=g (foldr f xs z))" for ps q
    by (rule fold_relation_encoded[where E=E and D=D and f=f and g=g and h=h])
      (use seed(1) element closed in auto)
  show ?thesis using seed(2) by (auto simp: exact relation)
qed

end

text \<open>
  The tail and the step have separate premise sockets and share the actual
  intermediate result. The all-term contract refers to the callee's complete
  meaning in the same system, so it also permits a shared positive dependency
  cycle. No external operation is added to the consequence mechanism.

  Consumers use the relational fold contract or its encoded specialization.
  The native recursive proof is established once. The empty case checks only
  formation of the copied seed and does not imply any uncalled step admission.
\<close>

end
