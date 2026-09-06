theory Lambda_Closure_Interpretation
  imports Lambda_Reduction
begin

section \<open>Closing source terms with their finite captured environments\<close>

fun lambda_close :: "lambda_term \<Rightarrow> lambda_term list \<Rightarrow> nat \<Rightarrow> lambda_term" where
  "lambda_close p [] k=p"
| "lambda_close p (q#e) k=lambda_close (lambda_substitute p q k) e k"

lemma lambda_close_application:
  "lambda_close (Lambda_Application p q) e k=
    Lambda_Application (lambda_close p e k) (lambda_close q e k)"
  by (induction e arbitrary: p q) simp_all

lemma lambda_close_abstraction:
  assumes "list_all (lambda_scoped 0) e"
  shows "lambda_close (Lambda_Abstraction p) e k=
    Lambda_Abstraction (lambda_close p e (Suc k))"
  using assms by (induction e arbitrary: p k) auto

lemma lambda_close_closed:
  assumes "lambda_scoped 0 p"
  shows "lambda_close p e k=p"
  using assms by (induction e) auto

lemma lambda_close_variable:
  assumes "n<length e" "list_all (lambda_scoped 0) e"
  shows "lambda_close (Lambda_Variable (n+k)) e k=e!n"
  using assms
proof (induction e arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons q e)
  then show ?case by (cases n)
    (auto simp: lambda_close_closed lambda_substitute.simps(1))
qed

lemma lambda_close_scoped:
  assumes "lambda_scoped (length e+n) p" "list_all (lambda_scoped 0) e"
  shows "lambda_scoped n (lambda_close p e n)"
  using assms
proof (induction e arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons q e)
  have source: "lambda_scoped (Suc (length e+n)) p" using Cons.prems(1) by simp
  have argument: "lambda_scoped (length e+n) q"
    by (rule lambda_scoped_mono[of 0]) (use Cons.prems(2) in auto)
  have substituted: "lambda_scoped (length e+n) (lambda_substitute p q n)"
    by (rule lambda_substitute_scoped[OF source argument]) simp
  have rest: "list_all (lambda_scoped 0) e" using Cons.prems(2) by simp
  show ?case using Cons.IH[OF substituted rest] by simp
qed

lemma lambda_closed_substitutions_commute:
  assumes "lambda_scoped 0 q" "lambda_scoped 0 r"
  shows "lambda_substitute (lambda_substitute p q (Suc k)) r k=
    lambda_substitute (lambda_substitute p r k) q k"
  using lambda_substitution_composition[where i=k and j=k and p=p and u=r and v=q]
  by (simp add: assms)

lemma lambda_close_substitute:
  assumes "list_all (lambda_scoped 0) e" "lambda_scoped 0 q"
  shows "lambda_substitute (lambda_close p e (Suc k)) q k=
    lambda_close (lambda_substitute p q k) e k"
  using assms by (induction e arbitrary: p)
    (auto simp: lambda_closed_substitutions_commute)

fun interpret_lambda_closure :: "lambda_closure \<Rightarrow> lambda_term" where
  "interpret_lambda_closure (Lambda_Closure p e)=
    lambda_close p (map interpret_lambda_closure e) 0"

lemma lambda_closure_interpretation_closed:
  assumes "lambda_closure_formed c"
  shows "lambda_scoped 0 (interpret_lambda_closure c)"
  using assms by (induction c)
    (auto simp: list_all_iff intro: lambda_close_scoped)

lemma lambda_closure_environment_closed:
  assumes "list_all lambda_closure_formed e"
  shows "list_all (lambda_scoped 0) (map interpret_lambda_closure e)"
  using assms by (auto simp: list_all_iff intro: lambda_closure_interpretation_closed)

lemma lambda_closure_variable_interpretation:
  assumes index: "n<length e" and formed: "list_all lambda_closure_formed e"
  shows "interpret_lambda_closure (Lambda_Closure (Lambda_Variable n) e)=
    interpret_lambda_closure (e!n)"
  using lambda_close_variable[where n=n and e="map interpret_lambda_closure e" and k=0]
    lambda_closure_environment_closed[OF formed] index by simp

lemma lambda_closure_application_interpretation:
  "interpret_lambda_closure (Lambda_Closure (Lambda_Application p q) e)=
    Lambda_Application (interpret_lambda_closure (Lambda_Closure p e))
      (interpret_lambda_closure (Lambda_Closure q e))"
  by (simp add: lambda_close_application)

lemma lambda_closure_abstraction_interpretation:
  assumes "list_all lambda_closure_formed e"
  shows "interpret_lambda_closure (Lambda_Closure (Lambda_Abstraction p) e)=
    Lambda_Abstraction (lambda_close p (map interpret_lambda_closure e) (Suc 0))"
  using lambda_closure_environment_closed[OF assms] by (simp add: lambda_close_abstraction)

lemma lambda_closure_beta_interpretation:
  assumes environment: "list_all lambda_closure_formed e"
    and argument: "lambda_closure_formed a"
  shows "lambda_reduces
    (Lambda_Application (interpret_lambda_closure (Lambda_Closure (Lambda_Abstraction p) e))
      (interpret_lambda_closure a))
    (interpret_lambda_closure (Lambda_Closure p (a#e)))"
proof -
  have closed_environment: "list_all (lambda_scoped 0) (map interpret_lambda_closure e)"
    by (rule lambda_closure_environment_closed[OF environment])
  have closed_argument: "lambda_scoped 0 (interpret_lambda_closure a)"
    by (rule lambda_closure_interpretation_closed[OF argument])
  show ?thesis using lambda_contract_reduces[
    of "lambda_close p (map interpret_lambda_closure e) (Suc 0)" "interpret_lambda_closure a"]
    by (simp add: lambda_close_abstraction lambda_close_substitute
      closed_environment closed_argument)
qed

lemma lambda_closure_body_interpretation:
  assumes "list_all lambda_closure_formed e" "lambda_closure_formed a"
  shows "interpret_lambda_closure (Lambda_Closure p (a#e))=
    lambda_substitute (lambda_close p (map interpret_lambda_closure e) (Suc 0))
      (interpret_lambda_closure a) 0"
  using lambda_closure_environment_closed[OF assms(1)]
    lambda_closure_interpretation_closed[OF assms(2)]
  by (simp add: lambda_close_substitute)

theorem lambda_evaluation_beta_interpretation:
  assumes "lambda_evaluates c v" "lambda_closure_formed c"
  shows "lambda_reduces (interpret_lambda_closure c) (interpret_lambda_closure v)"
  using assms
proof (induction rule: lambda_evaluates.induct)
  case (abstraction p e)
  then show ?case by simp
next
  case (variable n e v)
  have environment: "list_all lambda_closure_formed e" using variable.prems by simp
  have formed: "lambda_closure_formed (e!n)"
    using environment variable.hyps(1) by (auto simp: list_all_iff)
  have reduction: "lambda_reduces (interpret_lambda_closure (e!n)) (interpret_lambda_closure v)"
    by (rule variable.IH[OF formed])
  show ?case using reduction
    by (simp only: lambda_closure_variable_interpretation[OF variable.hyps(1) environment])
next
  case (application p e b f q v)
  have function_formed: "lambda_closure_formed (Lambda_Closure p e)"
    and argument: "lambda_closure_formed (Lambda_Closure q e)"
    using application.prems by simp_all
  have value_formed: "lambda_closure_formed (Lambda_Closure (Lambda_Abstraction b) f)"
    by (rule lambda_evaluation_preserves_formation[OF application.hyps(1) function_formed])
  have environment: "list_all lambda_closure_formed f" using value_formed by simp
  have body: "lambda_closure_formed (Lambda_Closure b (Lambda_Closure q e#f))"
    using value_formed argument by simp
  have head: "lambda_reduces
    (Lambda_Application (interpret_lambda_closure (Lambda_Closure p e))
      (interpret_lambda_closure (Lambda_Closure q e)))
    (Lambda_Application (interpret_lambda_closure (Lambda_Closure (Lambda_Abstraction b) f))
      (interpret_lambda_closure (Lambda_Closure q e)))"
    by (rule lambda_reduces_left[OF application.IH(1)[OF function_formed]])
  have beta: "lambda_reduces
    (Lambda_Application (interpret_lambda_closure (Lambda_Closure (Lambda_Abstraction b) f))
      (interpret_lambda_closure (Lambda_Closure q e)))
    (interpret_lambda_closure (Lambda_Closure b (Lambda_Closure q e#f)))"
    by (rule lambda_closure_beta_interpretation[OF environment argument])
  have tail: "lambda_reduces
    (interpret_lambda_closure (Lambda_Closure b (Lambda_Closure q e#f)))
    (interpret_lambda_closure v)"
    by (rule application.IH(2)[OF body])
  show ?case
    unfolding lambda_closure_application_interpretation
    by (rule rtranclp_trans[OF head], rule rtranclp_trans[OF beta tail])
qed

corollary closed_lambda_evaluation_beta:
  assumes "lambda_scoped 0 p" "lambda_evaluates (Lambda_Closure p []) v"
  shows "lambda_reduces p (interpret_lambda_closure v)"
  using lambda_evaluation_beta_interpretation[OF assms(2)] assms(1) by simp

text \<open>
  Closing substitutes the entries of a finite captured environment at the
  stated binder depth. Every formed closure yields a closed lambda term.
  Lookup agrees with that substitution, and applying an evaluated abstraction
  agrees with extending its captured environment by the argument closure.
  Every finite closure evaluation therefore has a beta reduction directly in
  the source calculus. This interpretation and its proof use neither SK nor
  Factor. The converse termination argument is still a separate obligation.
\<close>

end
