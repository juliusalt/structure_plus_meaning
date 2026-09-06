theory SK_Lambda_Compilation
  imports SK_Abstraction Lambda_Closures
begin

section \<open>Compilation of lambda closures into finite SK terms\<close>

fun compile_lambda :: "lambda_term \<Rightarrow> open_sk" where
  "compile_lambda (Lambda_Variable n)=Open_Variable n"
| "compile_lambda (Lambda_Application p q)=Open_Application (compile_lambda p) (compile_lambda q)"
| "compile_lambda (Lambda_Abstraction p)=sk_abstract (compile_lambda p)"

theorem lambda_compilation_scope:
  "(\<forall>k\<in>open_sk_variables (compile_lambda p). k<n) \<longleftrightarrow> lambda_scoped n p"
  by (induction p arbitrary: n) (auto simp: sk_abstract_scope)

lemma closed_lambda_compilation:
  "lambda_scoped 0 p \<longleftrightarrow> open_sk_variables (compile_lambda p)={}"
  using lambda_compilation_scope[of p 0] by auto

fun sk_environment :: "sk_term list \<Rightarrow> nat \<Rightarrow> sk_term" where
  "sk_environment [] n=SK_S"
| "sk_environment (x#xs) 0=x"
| "sk_environment (x#xs) (Suc n)=sk_environment xs n"

lemma sk_environment_nth:
  "n<length xs \<Longrightarrow> sk_environment xs n=xs!n"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) auto
qed

lemma sk_environment_cons:
  "sk_environment (x#xs)=case_nat x (sk_environment xs)"
  by (rule ext) (rename_tac n, case_tac n, simp_all)

fun compile_lambda_closure :: "lambda_closure \<Rightarrow> sk_term" where
  "compile_lambda_closure (Lambda_Closure p e)=
    evaluate_open_sk (sk_environment (map compile_lambda_closure e)) (compile_lambda p)"

lemma lambda_compilation_environment_agreement:
  assumes "lambda_scoped (length e) p"
    "\<And>n. n<length e \<Longrightarrow> f n=e!n"
  shows "evaluate_open_sk f (compile_lambda p)=evaluate_open_sk (sk_environment e) (compile_lambda p)"
proof (rule evaluate_open_sk_agreement)
  fix n
  assume "n\<in>open_sk_variables (compile_lambda p)"
  then have "n<length e" using assms(1) lambda_compilation_scope[of p "length e"] by blast
  then show "f n=sk_environment e n" using assms(2) sk_environment_nth by simp
qed

lemma closed_lambda_closure_environment:
  assumes "lambda_scoped 0 p"
  shows "compile_lambda_closure (Lambda_Closure p e)=compile_lambda_closure (Lambda_Closure p f)"
proof -
  have empty: "open_sk_variables (compile_lambda p)={}"
    using assms closed_lambda_compilation by blast
  show ?thesis
    unfolding compile_lambda_closure.simps
    by (rule evaluate_open_sk_agreement) (use empty in auto)
qed

lemma compile_lambda_variable:
  assumes "n<length e"
  shows "compile_lambda_closure (Lambda_Closure (Lambda_Variable n) e)=compile_lambda_closure (e!n)"
  using assms by (simp add: sk_environment_nth)

lemma compile_lambda_application:
  "compile_lambda_closure (Lambda_Closure (Lambda_Application p q) e)=
    SK_App (compile_lambda_closure (Lambda_Closure p e)) (compile_lambda_closure (Lambda_Closure q e))"
  by simp

lemma compile_lambda_beta:
  "sk_reduces
    (SK_App (compile_lambda_closure (Lambda_Closure (Lambda_Abstraction p) e))
      (compile_lambda_closure a))
    (compile_lambda_closure (Lambda_Closure p (a#e)))"
  using sk_abstraction_application[of "sk_environment (map compile_lambda_closure e)"
    "compile_lambda p" "compile_lambda_closure a"]
  by (simp add: sk_environment_cons)

theorem lambda_evaluation_compiles:
  assumes "lambda_evaluates c v"
  shows "sk_reduces (compile_lambda_closure c) (compile_lambda_closure v)"
  using assms
proof (induction rule: lambda_evaluates.induct)
  case (abstraction p e)
  then show ?case by simp
next
  case (variable n e v)
  then show ?case by (simp only: compile_lambda_variable)
next
  case (application p e b f q v)
  have head: "sk_reduces
    (SK_App (compile_lambda_closure (Lambda_Closure p e)) (compile_lambda_closure (Lambda_Closure q e)))
    (SK_App (compile_lambda_closure (Lambda_Closure (Lambda_Abstraction b) f))
      (compile_lambda_closure (Lambda_Closure q e)))"
    by (rule sk_reduces_left[OF application.IH(1)])
  have beta: "sk_reduces
    (SK_App (compile_lambda_closure (Lambda_Closure (Lambda_Abstraction b) f))
      (compile_lambda_closure (Lambda_Closure q e)))
    (compile_lambda_closure (Lambda_Closure b (Lambda_Closure q e#f)))"
    by (rule compile_lambda_beta)
  show ?case
    unfolding compile_lambda_application
    by (rule rtranclp_trans[OF head], rule rtranclp_trans[OF beta application.IH(2)])
qed

corollary closed_lambda_evaluation_compiles:
  assumes "lambda_scoped 0 p" "lambda_evaluates (Lambda_Closure p []) v"
  shows "open_sk_variables (compile_lambda p)={}"
    "lambda_closure_formed v"
    "sk_reduces (compile_lambda_closure (Lambda_Closure p [])) (compile_lambda_closure v)"
proof -
  show "open_sk_variables (compile_lambda p)={}"
    using assms(1) closed_lambda_compilation by blast
  have formed: "lambda_closure_formed (Lambda_Closure p [])" using assms(1) by simp
  show "lambda_closure_formed v"
    by (rule lambda_evaluation_preserves_formation[OF assms(2) formed])
  show "sk_reduces (compile_lambda_closure (Lambda_Closure p [])) (compile_lambda_closure v)"
    by (rule lambda_evaluation_compiles[OF assms(2)])
qed

text \<open>
  The compiler is a finite recursive calculation on terms and captured closures.
  The total lookup function uses S outside a supplied list; the scope and
  environment-agreement theorems prove that a formed source term never consults
  that default. Every finite source evaluation is preserved as an actual finite
  SK reduction. This theorem alone makes no termination-reflection claim.
\<close>

end
