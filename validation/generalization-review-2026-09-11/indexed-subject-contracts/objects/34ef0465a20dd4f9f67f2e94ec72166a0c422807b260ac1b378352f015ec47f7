theory Lambda_Termination
  imports Lambda_Standardization Lambda_Head_Evaluation
begin

section \<open>Reduction to an abstraction and actual evaluator termination\<close>

inductive lambda_head_step :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  contract: "lambda_head_step (Lambda_Application (Lambda_Abstraction p) q)
    (lambda_substitute p q 0)"
| left: "lambda_head_step p q \<Longrightarrow>
    lambda_head_step (Lambda_Application p r) (Lambda_Application q r)"

abbreviation lambda_head_reduces :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  "lambda_head_reduces \<equiv> rtranclp lambda_head_step"

lemma lambda_head_step_beta:
  "lambda_head_step p q \<Longrightarrow> lambda_beta p q"
  by (induction rule: lambda_head_step.induct) auto

lemma lambda_head_step_apps:
  "lambda_head_step p q \<Longrightarrow>
    lambda_head_step (lambda_apps p ps) (lambda_apps q ps)"
  by (induction ps rule: rev_induct) (auto intro: lambda_head_step.left)

lemma lambda_head_step_evaluation_backward:
  assumes "lambda_head_step p q" "lambda_head_evaluates q v"
  shows "lambda_head_evaluates p v"
  using assms
proof (induction arbitrary: v rule: lambda_head_step.induct)
  case (contract p q)
  then show ?case
    by (auto intro: lambda_head_evaluates.application lambda_head_evaluates.abstraction)
next
  case (left p q r)
  from left.prems obtain b where head: "lambda_head_evaluates q (Lambda_Abstraction b)"
    and tail: "lambda_head_evaluates (lambda_substitute b r 0) v"
    by (cases rule: lambda_head_evaluates.cases) auto
  have "lambda_head_evaluates p (Lambda_Abstraction b)" by (rule left.IH[OF head])
  then show ?case using tail by (rule lambda_head_evaluates.application)
qed

lemma lambda_head_reduction_evaluation_backward:
  assumes "lambda_head_reduces p q" "lambda_head_evaluates q v"
  shows "lambda_head_evaluates p v"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: lambda_head_step_evaluation_backward)

lemma lambda_standard_abstraction_head:
  assumes "lambda_standard p q" "q=Lambda_Abstraction r"
  shows "\<exists>b. lambda_head_reduces p (Lambda_Abstraction b)"
  using assms
proof (induction arbitrary: r rule: lambda_standard.induct)
  case (variable ps qs n)
  then show ?case by simp
next
  case (abstraction p q ps qs)
  from abstraction.prems have empty: "qs=[]" by simp
  from abstraction(3) have related: "listrelp lambda_standard ps qs"
    by (rule lambda_listrel_conj_left)
  from related empty have "ps=[]" by (cases rule: listrelp.cases) auto
  then show ?case by auto
next
  case (beta p q ps s)
  from beta.IH[OF beta.prems] obtain b where
    tail: "lambda_head_reduces (lambda_apps (lambda_substitute p q 0) ps) (Lambda_Abstraction b)"
    by blast
  have head: "lambda_head_step (lambda_apps (Lambda_Application (Lambda_Abstraction p) q) ps)
    (lambda_apps (lambda_substitute p q 0) ps)"
    by (rule lambda_head_step_apps, rule lambda_head_step.contract)
  have "lambda_head_reduces (lambda_apps (Lambda_Application (Lambda_Abstraction p) q) ps)
    (Lambda_Abstraction b)" by (rule converse_rtranclp_into_rtranclp[OF head tail])
  then show ?case by blast
qed

theorem lambda_reduction_to_abstraction_evaluates:
  assumes "lambda_reduces p (Lambda_Abstraction q)"
  shows "\<exists>b. lambda_head_evaluates p (Lambda_Abstraction b)"
proof -
  have standard: "lambda_standard p (Lambda_Abstraction q)"
    by (rule lambda_reduction_standard[OF assms])
  obtain b where head: "lambda_head_reduces p (Lambda_Abstraction b)"
    using lambda_standard_abstraction_head[OF standard refl] by blast
  have "lambda_head_evaluates p (Lambda_Abstraction b)"
    by (rule lambda_head_reduction_evaluation_backward[OF head lambda_head_evaluates.abstraction])
  then show ?thesis by blast
qed

lemma lambda_head_evaluation_beta:
  assumes "lambda_head_evaluates p v"
  shows "lambda_reduces p v"
  using assms
proof (induction rule: lambda_head_evaluates.induct)
  case (abstraction p)
  then show ?case by simp
next
  case (application p b q v)
  have head: "lambda_reduces (Lambda_Application p q)
    (Lambda_Application (Lambda_Abstraction b) q)"
    by (rule lambda_reduces_left[OF application.IH(1)])
  show ?case by (rule rtranclp_trans[OF head],
    rule rtranclp_trans[OF lambda_contract_reduces application.IH(2)])
qed

theorem lambda_closure_termination_iff:
  assumes formed: "lambda_closure_formed c"
  shows "(\<exists>v. lambda_evaluates c v) \<longleftrightarrow>
    (\<exists>b. lambda_reduces (interpret_lambda_closure c) (Lambda_Abstraction b))"
proof
  assume "\<exists>v. lambda_evaluates c v"
  then obtain v where evaluation: "lambda_evaluates c v" by blast
  have head: "lambda_head_evaluates (interpret_lambda_closure c) (interpret_lambda_closure v)"
    by (rule lambda_evaluation_head_interpretation[OF evaluation formed])
  then obtain b where result: "interpret_lambda_closure v=Lambda_Abstraction b"
    using lambda_head_evaluation_value by blast
  have "lambda_reduces (interpret_lambda_closure c) (Lambda_Abstraction b)"
    using lambda_head_evaluation_beta[OF head] by (simp only: result)
  then show "\<exists>b. lambda_reduces (interpret_lambda_closure c) (Lambda_Abstraction b)"
    by (rule exI)
next
  assume "\<exists>b. lambda_reduces (interpret_lambda_closure c) (Lambda_Abstraction b)"
  then obtain b where reduction: "lambda_reduces (interpret_lambda_closure c) (Lambda_Abstraction b)"
    by blast
  obtain q where head: "lambda_head_evaluates (interpret_lambda_closure c) (Lambda_Abstraction q)"
    using lambda_reduction_to_abstraction_evaluates[OF reduction] by blast
  show "\<exists>v. lambda_evaluates c v"
    using lambda_head_evaluation_closure[OF head formed refl] by blast
qed

corollary closed_lambda_termination_iff:
  assumes "lambda_scoped 0 p"
  shows "(\<exists>v. lambda_evaluates (Lambda_Closure p []) v) \<longleftrightarrow>
    (\<exists>b. lambda_reduces p (Lambda_Abstraction b))"
  using lambda_closure_termination_iff[of "Lambda_Closure p []"] assms by simp

text \<open>
  A head step contracts the first applied abstraction and never descends into
  arguments or abstraction bodies. Every such step is an existing beta step.
  Standardization shows that any beta reduction ending in an abstraction has
  a finite head reduction ending in an abstraction. Evaluation is preserved
  backward along this head reduction.

  The resulting equivalence covers every formed captured closure. It derives
  evaluator termination from an independently given beta reduction, without an
  evaluator witness as a premise. The eventual body need not equal the body
  of the supplied beta reduct, since full beta reduction also enters bodies.
\<close>

end
