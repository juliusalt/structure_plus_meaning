theory SK_Lambda_Termination
  imports SK_Lambda_Interpretation Lambda_Confluence Lambda_Termination
begin

section \<open>Preservation and reflection of lambda termination\<close>

definition sk_head_normal :: "sk_term \<Rightarrow> bool" where
  "sk_head_normal t \<longleftrightarrow> t=SK_S \<or> t=SK_K \<or>
    (\<exists>p. t=SK_App SK_K p) \<or> (\<exists>p. t=SK_App SK_S p) \<or>
    (\<exists>p q. t=SK_App (SK_App SK_S p) q)"

lemma sk_abstraction_head_normal:
  "sk_head_normal (evaluate_open_sk f (sk_abstract p))"
  by (induction p rule: sk_abstract.induct) (auto simp: sk_head_normal_def)

lemma compiled_lambda_abstraction_head_normal:
  "sk_head_normal (compile_lambda_closure (Lambda_Closure (Lambda_Abstraction p) e))"
  by (simp add: sk_abstraction_head_normal)

lemma sk_head_normal_interpretation:
  assumes "sk_head_normal t"
  shows "\<exists>b. lambda_reduces (interpret_sk t) (Lambda_Abstraction b)"
proof -
  have k: "\<And>p. \<exists>b. lambda_reduces (Lambda_Application lambda_k p) (Lambda_Abstraction b)"
    using lambda_k_head by blast
  have s: "\<And>p. \<exists>b. lambda_reduces (Lambda_Application lambda_s p) (Lambda_Abstraction b)"
    using lambda_s_head by blast
  have ss: "\<And>p q. \<exists>b. lambda_reduces
    (Lambda_Application (Lambda_Application lambda_s p) q) (Lambda_Abstraction b)"
    using lambda_s_head_two by blast
  show ?thesis using assms k s ss
    by (auto simp: sk_head_normal_def lambda_s_def lambda_k_def)
qed

lemma lambda_reduction_abstraction_shape:
  assumes "lambda_reduces (Lambda_Abstraction p) q"
  shows "\<exists>b. q=Lambda_Abstraction b"
  using assms by (induction rule: rtranclp_induct) auto

theorem compiled_lambda_termination_reflection:
  assumes closed: "lambda_scoped 0 p"
    and reduction: "sk_reduces (compile_lambda_closure (Lambda_Closure p e)) t"
    and result: "sk_head_normal t"
  shows "\<exists>v. lambda_evaluates (Lambda_Closure p []) v"
proof -
  let ?source = "interpret_sk (compile_lambda_closure (Lambda_Closure p e))"
  have source: "lambda_reduces ?source p"
    by (rule closed_lambda_compilation_interpretation[OF closed])
  have interpreted: "lambda_reduces ?source (interpret_sk t)"
    by (rule sk_reduction_interpretation[OF reduction])
  obtain b where abstraction: "lambda_reduces (interpret_sk t) (Lambda_Abstraction b)"
    using sk_head_normal_interpretation[OF result] by blast
  have target: "lambda_reduces ?source (Lambda_Abstraction b)"
    by (rule rtranclp_trans[OF interpreted abstraction])
  obtain q where joined: "lambda_reduces p q" "lambda_reduces (Lambda_Abstraction b) q"
    using confluentpD[OF lambda_confluent source target] by blast
  obtain c where shape: "q=Lambda_Abstraction c"
    using lambda_reduction_abstraction_shape[OF joined(2)] by blast
  have "lambda_reduces p (Lambda_Abstraction c)" using joined(1) by (simp only: shape)
  then show ?thesis using closed_lambda_termination_iff[OF closed] by blast
qed

theorem lambda_evaluation_reaches_sk_head:
  assumes "lambda_evaluates c v"
  shows "\<exists>t. sk_reduces (compile_lambda_closure c) t \<and> sk_head_normal t"
proof -
  obtain p e where shape: "v=Lambda_Closure (Lambda_Abstraction p) e"
    using lambda_evaluation_value[OF assms] by blast
  have head: "sk_head_normal (compile_lambda_closure v)"
    by (simp only: shape compiled_lambda_abstraction_head_normal)
  show ?thesis using lambda_evaluation_compiles[OF assms] head by blast
qed

theorem lambda_sk_termination_iff:
  assumes "lambda_scoped 0 p"
  shows "(\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
    (\<exists>t. sk_reduces (compile_lambda_closure (Lambda_Closure p [])) t \<and> sk_head_normal t)"
  using lambda_evaluation_reaches_sk_head
    compiled_lambda_termination_reflection[OF assms, where e="[]"] by blast

text \<open>
  An SK head is S or K with fewer arguments than its contraction rule requires.
  Its arguments may still reduce. Every compiled source abstraction has this
  shape, and the interpretation of every such SK head beta-reduces to a source
  abstraction. Source confluence and standardization then reflect termination
  for every closed untyped source term.

  Together with compilation of finite evaluations, this proves equivalence of
  source evaluator termination and finite SK reduction to a head. The source
  calculus and evaluator were defined independently of this compiler and of
  Factor meaning. No assumption of source termination appears in reflection.
  Equality with the literal source result is not required by this observation.
\<close>

end
