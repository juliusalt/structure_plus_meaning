theory Lambda_Closures
  imports Main
begin

section \<open>An independent lambda-calculus evaluator\<close>

datatype lambda_term =
    Lambda_Variable nat
  | Lambda_Application lambda_term lambda_term
  | Lambda_Abstraction lambda_term

fun lambda_scoped :: "nat \<Rightarrow> lambda_term \<Rightarrow> bool" where
  "lambda_scoped n (Lambda_Variable k)=(k<n)"
| "lambda_scoped n (Lambda_Application p q)=(lambda_scoped n p \<and> lambda_scoped n q)"
| "lambda_scoped n (Lambda_Abstraction p)=lambda_scoped (Suc n) p"

lemma lambda_scoped_mono:
  assumes "lambda_scoped n p" "n\<le>m"
  shows "lambda_scoped m p"
  using assms by (induction p arbitrary: n m) auto

datatype lambda_closure = Lambda_Closure lambda_term "lambda_closure list"

fun lambda_closure_formed :: "lambda_closure \<Rightarrow> bool" where
  "lambda_closure_formed (Lambda_Closure p e)=
    (lambda_scoped (length e) p \<and> list_all lambda_closure_formed e)"

inductive lambda_evaluates :: "lambda_closure \<Rightarrow> lambda_closure \<Rightarrow> bool" where
  abstraction: "lambda_evaluates
    (Lambda_Closure (Lambda_Abstraction p) e)
    (Lambda_Closure (Lambda_Abstraction p) e)"
| variable: "n<length e \<Longrightarrow> lambda_evaluates (e!n) v \<Longrightarrow>
    lambda_evaluates (Lambda_Closure (Lambda_Variable n) e) v"
| application:
    "lambda_evaluates (Lambda_Closure p e) (Lambda_Closure (Lambda_Abstraction b) f) \<Longrightarrow>
    lambda_evaluates (Lambda_Closure b (Lambda_Closure q e#f)) v \<Longrightarrow>
    lambda_evaluates (Lambda_Closure (Lambda_Application p q) e) v"

lemma lambda_evaluation_value:
  assumes "lambda_evaluates c v"
  shows "\<exists>p e. v=Lambda_Closure (Lambda_Abstraction p) e"
  using assms by (induction rule: lambda_evaluates.induct) auto

theorem lambda_evaluation_preserves_formation:
  assumes "lambda_evaluates c v" "lambda_closure_formed c"
  shows "lambda_closure_formed v"
  using assms
proof (induction rule: lambda_evaluates.induct)
  case (abstraction p e)
  then show ?case .
next
  case (variable n e v)
  have "lambda_closure_formed (e!n)"
    using variable.hyps(1) variable.prems by (auto simp: list_all_iff)
  then show ?case by (rule variable.IH)
next
  case (application p e b f q v)
  have head: "lambda_closure_formed (Lambda_Closure (Lambda_Abstraction b) f)"
    by (rule application.IH(1)) (use application.prems in simp)
  have body: "lambda_closure_formed (Lambda_Closure b (Lambda_Closure q e#f))"
    using head application.prems by simp
  show ?case by (rule application.IH(2)[OF body])
qed

theorem lambda_evaluation_deterministic:
  assumes "lambda_evaluates c v" "lambda_evaluates c w"
  shows "v=w"
  using assms
proof (induction arbitrary: w rule: lambda_evaluates.induct)
  case (abstraction p e)
  from abstraction.prems show ?case by (cases rule: lambda_evaluates.cases) auto
next
  case (variable n e v)
  from variable.prems have lookup: "lambda_evaluates (e!n) w"
    by (cases rule: lambda_evaluates.cases) auto
  show ?case by (rule variable.IH[OF lookup])
next
  case (application p e b f q v)
  from application.prems obtain b' f' where
    head: "lambda_evaluates (Lambda_Closure p e) (Lambda_Closure (Lambda_Abstraction b') f')"
    and body: "lambda_evaluates (Lambda_Closure b' (Lambda_Closure q e#f')) w"
    by (cases rule: lambda_evaluates.cases) auto
  have "Lambda_Closure (Lambda_Abstraction b) f=Lambda_Closure (Lambda_Abstraction b') f'"
    by (rule application.IH(1)[OF head])
  then have "b=b'" "f=f'" by auto
  then show ?case using application.IH(2) body by blast
qed

text \<open>
  A variable selects an explicitly captured closure by its de Bruijn index.
  Application evaluates the function and passes the unevaluated argument as a
  closure. Evaluation stops at an abstraction. All environments are finite
  closure trees; formation rules out an index beyond its captured environment.
  Neither SK nor Factor participates in this source evaluation relation.
\<close>

end
