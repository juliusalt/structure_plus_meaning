theory Lambda_Reduction
  imports Lambda_Substitution
begin

section \<open>Independent beta reduction, including abstraction bodies\<close>

inductive lambda_beta :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  contract [simp, intro!]: "lambda_beta (Lambda_Application (Lambda_Abstraction p) q)
    (lambda_substitute p q 0)"
| left [simp, intro!]: "lambda_beta p q \<Longrightarrow>
    lambda_beta (Lambda_Application p r) (Lambda_Application q r)"
| right [simp, intro!]: "lambda_beta p q \<Longrightarrow>
    lambda_beta (Lambda_Application r p) (Lambda_Application r q)"
| under [simp, intro!]: "lambda_beta p q \<Longrightarrow>
    lambda_beta (Lambda_Abstraction p) (Lambda_Abstraction q)"

abbreviation lambda_reduces :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  "lambda_reduces \<equiv> rtranclp lambda_beta"

inductive_cases lambda_beta_elims [elim!]:
  "lambda_beta (Lambda_Variable n) p"
  "lambda_beta (Lambda_Abstraction p) q"
  "lambda_beta (Lambda_Application p q) r"

lemma lambda_contract_reduces:
  "lambda_reduces (Lambda_Application (Lambda_Abstraction p) q)
    (lambda_substitute p q 0)"
  by (rule r_into_rtranclp, rule lambda_beta.contract)

lemma lambda_reduces_left:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (Lambda_Application p r) (Lambda_Application q r)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma lambda_reduces_right:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (Lambda_Application r p) (Lambda_Application r q)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma lambda_reduces_application:
  assumes "lambda_reduces p q" "lambda_reduces r s"
  shows "lambda_reduces (Lambda_Application p r) (Lambda_Application q s)"
  using lambda_reduces_left[OF assms(1), of r] lambda_reduces_right[OF assms(2), of q]
  by (rule rtranclp_trans)

lemma lambda_reduces_under:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (Lambda_Abstraction p) (Lambda_Abstraction q)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl)

theorem lambda_beta_scope:
  assumes "lambda_beta p q" "lambda_scoped n p"
  shows "lambda_scoped n q"
  using assms by (induction arbitrary: n rule: lambda_beta.induct)
    (auto intro: lambda_substitute_scoped)

lemma lambda_reduction_scope:
  assumes "lambda_reduces p q" "lambda_scoped n p"
  shows "lambda_scoped n q"
  using assms by (induction rule: rtranclp_induct) (auto intro: lambda_beta_scope)

lemma lambda_beta_substitute [simp]:
  assumes "lambda_beta p q"
  shows "lambda_beta (lambda_substitute p t i) (lambda_substitute q t i)"
  using assms by (induction arbitrary: t i rule: lambda_beta.induct)
    (simp_all add: lambda_substitution_composition[symmetric])

lemma lambda_reduces_substitute:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (lambda_substitute p t i) (lambda_substitute q t i)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma lambda_beta_lift [simp]:
  assumes "lambda_beta p q"
  shows "lambda_beta (lambda_lift p i) (lambda_lift q i)"
  using assms by (induction arbitrary: i rule: lambda_beta.induct) auto

lemma lambda_reduces_lift:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (lambda_lift p i) (lambda_lift q i)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma lambda_beta_argument_substitute:
  assumes "lambda_beta p q"
  shows "lambda_reduces (lambda_substitute t p i) (lambda_substitute t q i)"
  using assms by (induction t arbitrary: p q i)
    (auto simp: lambda_substitute.simps(1)
      intro: r_into_rtranclp lambda_reduces_application lambda_reduces_under)

lemma lambda_reduces_argument_substitute:
  assumes "lambda_reduces p q"
  shows "lambda_reduces (lambda_substitute t p i) (lambda_substitute t q i)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_trans lambda_beta_argument_substitute)

text \<open>
  This relation uses the same source lambda terms as the closure evaluator.
  It contracts capture-avoiding beta redexes in either application position
  and under abstractions. Its definition is independent of SK compilation,
  Factor truth, and the closure evaluator's result relation.
\<close>

end
