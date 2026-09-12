theory SK_Lambda_Reflection
  imports SK_Lambda_Interpretation SK_Lambda_Results Lambda_Confluence
begin

section \<open>Recovering normal source observations from compiled reduction\<close>

theorem compiled_lambda_normal_result_reflection:
  assumes closed: "lambda_scoped 0 p"
    and target: "sk_reduces (compile_lambda_closure (Lambda_Closure p e)) t"
    and result: "lambda_reduces (interpret_sk t) q"
    and normal: "\<And>r. \<not> lambda_beta q r"
  shows "lambda_reduces p q"
proof -
  have source: "lambda_reduces
    (interpret_sk (compile_lambda_closure (Lambda_Closure p e))) p"
    by (rule closed_lambda_compilation_interpretation[OF closed])
  have compiled: "lambda_reduces
    (interpret_sk (compile_lambda_closure (Lambda_Closure p e))) q"
    by (rule rtranclp_trans[OF sk_reduction_interpretation[OF target] result])
  show ?thesis by (rule lambda_reduction_to_normal[OF source compiled normal])
qed

fun lambda_natural :: "nat \<Rightarrow> lambda_term" where
  "lambda_natural 0=lambda_s"
| "lambda_natural (Suc n)=Lambda_Abstraction (lambda_natural n)"

lemma lambda_natural_closed: "lambda_scoped 0 (lambda_natural n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "lambda_lift (lambda_natural n) 0=lambda_natural n"
    by (rule lambda_closed_lift[OF Suc.IH])
  moreover have "lambda_scoped (Suc 0) (lambda_lift (lambda_natural n) 0)"
    by (rule lambda_lift_scoped[OF Suc.IH]) simp
  ultimately show ?case by simp
qed

lemma lambda_natural_has_no_step: "\<not> lambda_beta (lambda_natural n) p"
  by (induction n arbitrary: p) (auto simp: lambda_s_def)

lemma lambda_natural_size: "size (lambda_natural n)=size lambda_s+n"
  by (induction n) simp_all

lemma lambda_natural_injective: "lambda_natural m=lambda_natural n \<longleftrightarrow> m=n"
proof
  assume "lambda_natural m=lambda_natural n"
  then have "size (lambda_natural m)=size (lambda_natural n)" by simp
  then show "m=n" by (simp add: lambda_natural_size)
next
  assume "m=n" then show "lambda_natural m=lambda_natural n" by simp
qed

lemma sk_natural_interpretation:
  "lambda_reduces (interpret_sk (sk_natural n)) (lambda_natural n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have head: "lambda_reduces (Lambda_Application lambda_k (interpret_sk (sk_natural n)))
    (Lambda_Abstraction (interpret_sk (sk_natural n)))"
    using lambda_k_head[of "interpret_sk (sk_natural n)"]
    by (simp add: interpret_sk_closed)
  have tail: "lambda_reduces (Lambda_Abstraction (interpret_sk (sk_natural n)))
    (Lambda_Abstraction (lambda_natural n))"
    by (rule lambda_reduces_under[OF Suc.IH])
  show ?case using rtranclp_trans[OF head tail] by simp
qed

abbreviation lambda_observe :: "lambda_term \<Rightarrow> lambda_term" where
  "lambda_observe p \<equiv> Lambda_Application (Lambda_Application p lambda_k) lambda_s"

lemma lambda_observe_reduction:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (lambda_observe p) (lambda_observe q)"
  by (rule lambda_reduces_left, rule lambda_reduces_left, rule assms)

theorem compiled_lambda_numeric_result_reflection:
  assumes closed: "lambda_scoped 0 p"
    and result: "sk_reduces
      (sk_observe (compile_lambda_closure (Lambda_Closure p e))) (sk_natural n)"
  shows "lambda_reduces (lambda_observe p) (lambda_natural n)"
proof -
  let ?c = "compile_lambda_closure (Lambda_Closure p e)"
  have source: "lambda_reduces (interpret_sk (sk_observe ?c)) (lambda_observe p)"
    using lambda_observe_reduction[OF closed_lambda_compilation_interpretation[OF closed], of e]
    by simp
  have compiled: "lambda_reduces (interpret_sk (sk_observe ?c)) (lambda_natural n)"
    by (rule rtranclp_trans[OF sk_reduction_interpretation[OF result] sk_natural_interpretation])
  show ?thesis by (rule lambda_reduction_to_normal[OF source compiled lambda_natural_has_no_step])
qed

theorem lambda_numeral_observation:
  "lambda_reduces (lambda_observe (lambda_numeral n)) (lambda_natural n)"
  using compiled_lambda_numeric_result_reflection[OF lambda_numeral_closed[of n],
    where e="[]" and n=n] compiled_numeral_observation[of n]
  by (simp only: sk_numeral_def)

text \<open>
  A compiled SK result with a normal lambda interpretation is reachable from
  the closed source term itself. Numeric observation applies the source to
  the explicit K and S lambda terms. Every canonical SK numeric answer
  therefore gives that same observation in the source beta relation, without
  assuming a source evaluation first. Its normal output has a distinct syntax
  for every number. This implication does not assert that every beta-equivalent
  representation compiles to the same raw SK normal form, or that the closure
  evaluator returns literal numeral syntax.
\<close>

end
