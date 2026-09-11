theory SK_Lambda_Results
  imports SK_Numerals
begin

section \<open>Exact numeric results of compiled lambda evaluations\<close>

abbreviation sk_observe :: "sk_term \<Rightarrow> sk_term" where
  "sk_observe t \<equiv> SK_App (SK_App t SK_K) SK_S"

lemma sk_observe_reduction:
  assumes "sk_reduces t u"
  shows "sk_reduces (sk_observe t) (sk_observe u)"
  by (rule sk_reduces_left, rule sk_reduces_left, rule assms)

lemma lambda_numeric_evaluation_compiles:
  assumes "lambda_evaluates (Lambda_Closure p []) (Lambda_Closure (lambda_numeral n) e)"
  shows "sk_reduces (compile_lambda_closure (Lambda_Closure p [])) (sk_numeral n)"
proof -
  have result: "compile_lambda_closure (Lambda_Closure (lambda_numeral n) e)=sk_numeral n"
    using closed_lambda_closure_environment[OF lambda_numeral_closed[of n], of e "[]"]
    by (simp only: sk_numeral_def)
  show ?thesis using lambda_evaluation_compiles[OF assms] by (simp only: result)
qed

theorem lambda_numeric_observation:
  assumes "lambda_evaluates (Lambda_Closure p []) (Lambda_Closure (lambda_numeral n) e)"
  shows "sk_reduces (sk_observe (compile_lambda_closure (Lambda_Closure p []))) (sk_natural n)"
  by (rule rtranclp_trans[OF sk_observe_reduction[OF lambda_numeric_evaluation_compiles[OF assms]]
    compiled_numeral_observation])

theorem lambda_numeric_observation_exact:
  assumes "lambda_evaluates (Lambda_Closure p []) (Lambda_Closure (lambda_numeral n) e)"
  shows "sk_reduces (sk_observe (compile_lambda_closure (Lambda_Closure p []))) (sk_natural m)
    \<longleftrightarrow> n=m"
proof
  assume reduction: "sk_reduces (sk_observe (compile_lambda_closure (Lambda_Closure p []))) (sk_natural m)"
  have "sk_natural n=sk_natural m"
    by (rule sk_normal_result_unique[OF lambda_numeric_observation[OF assms] reduction
      sk_natural_has_no_step sk_natural_has_no_step])
  then show "n=m" by (simp add: sk_natural_injective)
next
  assume "n=m"
  then show "sk_reduces (sk_observe (compile_lambda_closure (Lambda_Closure p []))) (sk_natural m)"
    using lambda_numeric_observation[OF assms] by simp
qed

theorem total_lambda_function_compiles:
  assumes closed: "lambda_scoped 0 p"
    and computes: "\<And>n. \<exists>e. lambda_evaluates
      (Lambda_Closure (Lambda_Application p (lambda_numeral n)) [])
      (Lambda_Closure (lambda_numeral (f n)) e)"
  shows "\<forall>n. lambda_scoped 0 (Lambda_Application p (lambda_numeral n))"
    "\<forall>n m. sk_reduces
      (sk_observe (SK_App (compile_lambda_closure (Lambda_Closure p [])) (sk_numeral n)))
      (sk_natural m) \<longleftrightarrow> f n=m"
proof -
  show "\<forall>n. lambda_scoped 0 (Lambda_Application p (lambda_numeral n))"
    using closed by (simp add: lambda_numeral_closed)
  show "\<forall>n m. sk_reduces
    (sk_observe (SK_App (compile_lambda_closure (Lambda_Closure p [])) (sk_numeral n)))
    (sk_natural m) \<longleftrightarrow> f n=m"
  proof (intro allI)
    fix n m
    obtain e where evaluation: "lambda_evaluates
      (Lambda_Closure (Lambda_Application p (lambda_numeral n)) [])
      (Lambda_Closure (lambda_numeral (f n)) e)"
      using computes[of n] by blast
    show "sk_reduces
      (sk_observe (SK_App (compile_lambda_closure (Lambda_Closure p [])) (sk_numeral n)))
      (sk_natural m) \<longleftrightarrow> f n=m"
      using lambda_numeric_observation_exact[OF evaluation, of m]
      by (simp only: compile_lambda_application sk_numeral_def)
  qed
qed

text \<open>
  Closed numeral syntax ignores every captured environment entry. Whenever a
  source evaluation returns such a numeral, the compiled observation has exactly
  the corresponding numeric result under arbitrary SK reduction choices.
  Consequently every total numeric function with the stated independent lambda
  evaluator witness has a finite SK implementation with exact numeric answers.
  No behavior on a source computation without a numeric result is inferred.
\<close>

end
