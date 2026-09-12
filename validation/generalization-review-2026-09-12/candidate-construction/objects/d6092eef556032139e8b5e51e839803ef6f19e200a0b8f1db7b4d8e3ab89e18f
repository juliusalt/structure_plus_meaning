theory Factor_SK
  imports Factor_SK_Program SK_Reduction Factor_Derivation
begin

section \<open>Faithful finite SK arguments\<close>

fun sk_value :: "sk_term \<Rightarrow> factor_term" where
  "sk_value SK_S=Payload_Term []"
| "sk_value SK_K=Payload_Term [0]"
| "sk_value (SK_App x y)=Pair_Term (sk_value x) (sk_value y)"

lemma sk_value_formed [simp]: "term_formed (sk_value t)"
  by (induction t) (auto simp: octets_formed_def)

lemma sk_value_injective [simp]: "sk_value t=sk_value u \<longleftrightarrow> t=u"
  by (induction t arbitrary: u) (case_tac u; auto)+

lemma sk_value_has_no_literal_slots [simp]: "term_literal_bindings (sk_value t)={}"
  by (induction t) auto

theorem sk_quotation_total:
  "term_quoted_at (term_environment (sk_value t)) None [] (sk_value t)
      (term_syntax_interior (sk_value t)) {} \<and>
    environment_closed (term_environment (sk_value t)) {None} {}"
  using term_quotation_closed_total[OF sk_value_formed, of t] by simp

section \<open>The external specification bounds the ordinary least fixed point\<close>

definition sk_expected_calls :: "(nat \<times> factor_term) set" where
  "sk_expected_calls = {(d,t).
    (d=0 \<and> (\<exists>x. t=sk_value x)) \<or>
    (d=1 \<and> (\<exists>x y. t=Pair_Term (sk_value x) (sk_value y) \<and> sk_step x y)) \<or>
    (d=2 \<and> (\<exists>x y. t=Pair_Term (sk_value x) (sk_value y) \<and> sk_reduces x y))}"

lemma sk_expected_reads:
  "(0,t)\<in>sk_expected_calls \<longleftrightarrow> (\<exists>x. t=sk_value x)"
  "(1,t)\<in>sk_expected_calls \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term (sk_value x) (sk_value y) \<and> sk_step x y)"
  "(2,t)\<in>sk_expected_calls \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term (sk_value x) (sk_value y) \<and> sk_reduces x y)"
  by (auto simp: sk_expected_calls_def)

lemma sk_expected_values:
  "(0,sk_value t)\<in>sk_expected_calls"
  "(1,Pair_Term (sk_value t) (sk_value u))\<in>sk_expected_calls \<longleftrightarrow> sk_step t u"
  "(2,Pair_Term (sk_value t) (sk_value u))\<in>sk_expected_calls \<longleftrightarrow> sk_reduces t u"
  by (auto simp: sk_expected_calls_def)

lemma sk_expected_s: "(0,Payload_Term [])\<in>sk_expected_calls"
  using sk_expected_values(1)[of SK_S] by simp

lemma sk_expected_k: "(0,Payload_Term [0])\<in>sk_expected_calls"
  using sk_expected_values(1)[of SK_K] by simp

lemma sk_expected_app:
  assumes "(0,x)\<in>sk_expected_calls" "(0,y)\<in>sk_expected_calls"
  shows "(0,Pair_Term x y)\<in>sk_expected_calls"
  using assms by (auto simp: sk_expected_calls_def; metis sk_value.simps(3))

lemma sk_expected_k_step:
  assumes "(0,x)\<in>sk_expected_calls" "(0,y)\<in>sk_expected_calls"
  shows "(1,Pair_Term (Pair_Term (Pair_Term (Payload_Term [0]) x) y) x)\<in>sk_expected_calls"
proof -
  obtain a b where args: "x=sk_value a" "y=sk_value b"
    using assms by (auto simp: sk_expected_calls_def)
  have reduction: "sk_step (SK_App (SK_App SK_K a) b) a" by (rule sk_step.k)
  have encoded: "(1,Pair_Term (sk_value (SK_App (SK_App SK_K a) b)) (sk_value a))\<in>sk_expected_calls"
    using sk_expected_values(2)[of "SK_App (SK_App SK_K a) b" a] reduction by blast
  show ?thesis using encoded args by simp
qed

lemma sk_expected_s_step:
  assumes "(0,x)\<in>sk_expected_calls" "(0,y)\<in>sk_expected_calls" "(0,z)\<in>sk_expected_calls"
  shows "(1,Pair_Term (Pair_Term (Pair_Term (Pair_Term (Payload_Term []) x) y) z)
    (Pair_Term (Pair_Term x z) (Pair_Term y z)))\<in>sk_expected_calls"
proof -
  obtain a b c where args: "x=sk_value a" "y=sk_value b" "z=sk_value c"
    using assms by (auto simp: sk_expected_calls_def)
  have reduction: "sk_step (SK_App (SK_App (SK_App SK_S a) b) c) (SK_App (SK_App a c) (SK_App b c))"
    by (rule sk_step.s)
  have encoded: "(1,Pair_Term (sk_value (SK_App (SK_App (SK_App SK_S a) b) c))
    (sk_value (SK_App (SK_App a c) (SK_App b c))))\<in>sk_expected_calls"
    using sk_expected_values(2)[of "SK_App (SK_App (SK_App SK_S a) b) c" "SK_App (SK_App a c) (SK_App b c)"]
      reduction by blast
  show ?thesis using encoded args by simp
qed

lemma sk_expected_left:
  assumes "(1,Pair_Term x y)\<in>sk_expected_calls" "(0,z)\<in>sk_expected_calls"
  shows "(1,Pair_Term (Pair_Term x z) (Pair_Term y z))\<in>sk_expected_calls"
proof -
  obtain a b c where args: "x=sk_value a" "y=sk_value b" "z=sk_value c" and step: "sk_step a b"
    using assms by (auto simp: sk_expected_calls_def)
  have reduction: "sk_step (SK_App a c) (SK_App b c)" by (rule sk_step.left[OF step])
  have encoded: "(1,Pair_Term (sk_value (SK_App a c)) (sk_value (SK_App b c)))\<in>sk_expected_calls"
    using sk_expected_values(2)[of "SK_App a c" "SK_App b c"] reduction by blast
  show ?thesis using encoded args by simp
qed

lemma sk_expected_right:
  assumes "(1,Pair_Term x y)\<in>sk_expected_calls" "(0,z)\<in>sk_expected_calls"
  shows "(1,Pair_Term (Pair_Term z x) (Pair_Term z y))\<in>sk_expected_calls"
proof -
  obtain a b c where args: "x=sk_value a" "y=sk_value b" "z=sk_value c" and step: "sk_step a b"
    using assms by (auto simp: sk_expected_calls_def)
  have reduction: "sk_step (SK_App c a) (SK_App c b)" by (rule sk_step.right[OF step])
  have encoded: "(1,Pair_Term (sk_value (SK_App c a)) (sk_value (SK_App c b)))\<in>sk_expected_calls"
    using sk_expected_values(2)[of "SK_App c a" "SK_App c b"] reduction by blast
  show ?thesis using encoded args by simp
qed

lemma sk_expected_refl:
  assumes "(0,x)\<in>sk_expected_calls"
  shows "(2,Pair_Term x x)\<in>sk_expected_calls"
  using assms by (auto simp: sk_expected_calls_def)

lemma sk_expected_trans:
  assumes "(1,Pair_Term x y)\<in>sk_expected_calls" "(2,Pair_Term y z)\<in>sk_expected_calls"
  shows "(2,Pair_Term x z)\<in>sk_expected_calls"
  using assms by (auto simp: sk_expected_calls_def; meson r_into_rtranclp rtranclp_trans)

lemmas sk_expected_rules = sk_expected_s sk_expected_k sk_expected_app sk_expected_k_step
  sk_expected_s_step sk_expected_left sk_expected_right sk_expected_refl sk_expected_trans

lemma sk_expected_closed:
  "schema_consequences sk_system sk_expected_calls \<subseteq> sk_expected_calls"
proof
  fix call assume member: "call\<in>schema_consequences sk_system sk_expected_calls"
  obtain d t where shape: "call=(d,t)" by (cases call) auto
  have named: "(d,t)\<in>schema_consequences sk_system sk_expected_calls" using member shape by simp
  obtain c S f where clause: "((d,c),S)\<in>system_clauses sk_system"
    and head: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>sk_expected_calls"
    using named
    by (subst (asm) schema_consequences_valuation[OF sk_system_formed sk_system_observation_free]) blast
  have "(d,t)\<in>sk_expected_calls"
    using clause head support
    by (auto simp: sk_system_def sk_clause_defs; blast intro: sk_expected_rules[simplified])
  then show "call\<in>sk_expected_calls" using shape by simp
qed

theorem sk_program_sound: "positive_meaning sk_system \<subseteq> sk_expected_calls"
  by (rule positive_meaning_least[OF sk_expected_closed])

section \<open>Every external reduction is generated by the actual clauses\<close>

definition sk_assignment :: "sk_term \<Rightarrow> sk_term \<Rightarrow> sk_term \<Rightarrow> nat \<Rightarrow> factor_term" where
  "sk_assignment x y z a=sk_value (if a=0 then x else if a=1 then y else z)"

lemma sk_assignment_formed [simp]: "term_formed (sk_assignment x y z a)"
  by (simp add: sk_assignment_def)

lemma sk_term_positive: "(0,sk_value t)\<in>positive_meaning sk_system"
proof (induction t)
  case SK_S
  show ?case using sk_positive_rule[OF sk_clause_members(1), where f="sk_assignment SK_S SK_S SK_S"]
    by (simp add: sk_clause_defs schema_variables_def)
next
  case SK_K
  show ?case using sk_positive_rule[OF sk_clause_members(2), where f="sk_assignment SK_K SK_K SK_K"]
    by (simp add: sk_clause_defs schema_variables_def octets_formed_def)
next
  case (SK_App x y)
  show ?case using SK_App.IH sk_positive_rule[OF sk_clause_members(3), where f="sk_assignment x y SK_S"]
    by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def)
qed

lemma sk_k_positive:
  "(1,Pair_Term (sk_value (SK_App (SK_App SK_K x) y)) (sk_value x))\<in>positive_meaning sk_system"
  using sk_positive_rule[OF sk_clause_members(4), where f="sk_assignment x y SK_S"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def sk_term_positive)

lemma sk_s_positive:
  "(1,Pair_Term (sk_value (SK_App (SK_App (SK_App SK_S x) y) z))
    (sk_value (SK_App (SK_App x z) (SK_App y z))))\<in>positive_meaning sk_system"
  using sk_positive_rule[OF sk_clause_members(5), where f="sk_assignment x y z"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def sk_term_positive)

lemma sk_left_positive:
  assumes "(1,Pair_Term (sk_value x) (sk_value y))\<in>positive_meaning sk_system"
  shows "(1,Pair_Term (sk_value (SK_App x z)) (sk_value (SK_App y z)))\<in>positive_meaning sk_system"
  using assms sk_positive_rule[OF sk_clause_members(6), where f="sk_assignment x y z"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def sk_term_positive)

lemma sk_right_positive:
  assumes "(1,Pair_Term (sk_value x) (sk_value y))\<in>positive_meaning sk_system"
  shows "(1,Pair_Term (sk_value (SK_App z x)) (sk_value (SK_App z y)))\<in>positive_meaning sk_system"
  using assms sk_positive_rule[OF sk_clause_members(7), where f="sk_assignment x y z"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def sk_term_positive)

theorem sk_step_positive:
  assumes "sk_step t u"
  shows "(1,Pair_Term (sk_value t) (sk_value u))\<in>positive_meaning sk_system"
  using assms by (induction rule: sk_step.induct)
    (blast intro: sk_k_positive sk_s_positive sk_left_positive sk_right_positive)+

lemma sk_refl_positive:
  "(2,Pair_Term (sk_value x) (sk_value x))\<in>positive_meaning sk_system"
  using sk_positive_rule[OF sk_clause_members(8), where f="sk_assignment x SK_S SK_S"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def sk_term_positive)

lemma sk_trans_positive:
  assumes "(1,Pair_Term (sk_value x) (sk_value y))\<in>positive_meaning sk_system"
    "(2,Pair_Term (sk_value y) (sk_value z))\<in>positive_meaning sk_system"
  shows "(2,Pair_Term (sk_value x) (sk_value z))\<in>positive_meaning sk_system"
  using assms sk_positive_rule[OF sk_clause_members(9), where f="sk_assignment x y z"]
  by (auto simp: sk_clause_defs schema_variables_def sk_assignment_def)

theorem sk_reduction_positive:
  assumes "sk_reduces t u"
  shows "(2,Pair_Term (sk_value t) (sk_value u))\<in>positive_meaning sk_system"
  using assms by (induction rule: converse_rtranclp_induct)
    (auto intro: sk_refl_positive sk_trans_positive sk_step_positive)

theorem sk_program_exact: "positive_meaning sk_system=sk_expected_calls"
  using sk_program_sound sk_term_positive sk_step_positive sk_reduction_positive
  by (auto simp: sk_expected_calls_def)

theorem sk_term_adequate:
  "(0,t)\<in>positive_meaning sk_system \<longleftrightarrow> (\<exists>x. t=sk_value x)"
  by (simp only: sk_program_exact sk_expected_reads)

theorem sk_step_adequate:
  "(1,Pair_Term (sk_value t) (sk_value u))\<in>positive_meaning sk_system \<longleftrightarrow> sk_step t u"
  by (simp only: sk_program_exact sk_expected_values)

theorem sk_reduction_adequate:
  "(2,Pair_Term (sk_value t) (sk_value u))\<in>positive_meaning sk_system \<longleftrightarrow> sk_reduces t u"
  by (simp only: sk_program_exact sk_expected_values)

theorem sk_reduction_certificate_adequate:
  "sk_reduces t u \<longleftrightarrow>
    (\<exists>tree. checks_schema_proof sk_system tree 2 (Pair_Term (sk_value t) (sk_value u)))"
  using sk_reduction_adequate[of t u] schema_proof_adequate[of 2 "Pair_Term (sk_value t) (sk_value u)" sk_system]
  by blast

text \<open>
  The expected calls are an external specification used only in the adequacy
  proof. They are not a branch of Factor meaning. Closure under each of the
  nine actual clauses gives soundness by leastness; independent induction on
  SK syntax and reduction gives completeness. The exact equation also rejects
  non-SK arguments and unintended calls, rather than only comparing true cases.

  Every source term has a finite closed quotation with no external literal
  bindings. Finite reduction certificates are the generic schema proofs
  already proved sound and complete for every positive program.
\<close>

end
