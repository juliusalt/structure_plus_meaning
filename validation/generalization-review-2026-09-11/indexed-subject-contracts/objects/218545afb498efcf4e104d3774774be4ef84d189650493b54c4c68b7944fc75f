theory SK_Lambda_Interpretation
  imports SK_Lambda_Compilation Lambda_Reduction
begin

section \<open>Interpreting the finite SK compiler in its source calculus\<close>

definition lambda_k :: lambda_term where
  "lambda_k=Lambda_Abstraction (Lambda_Abstraction (Lambda_Variable 1))"

definition lambda_s :: lambda_term where
  "lambda_s=Lambda_Abstraction (Lambda_Abstraction (Lambda_Abstraction
    (Lambda_Application (Lambda_Application (Lambda_Variable 2) (Lambda_Variable 0))
      (Lambda_Application (Lambda_Variable 1) (Lambda_Variable 0)))))"

lemma lambda_k_closed [simp]: "lambda_scoped 0 lambda_k"
  by (simp add: lambda_k_def)

lemma lambda_s_closed [simp]: "lambda_scoped 0 lambda_s"
  by (simp add: lambda_s_def)

lemma lambda_k_head:
  "lambda_reduces (Lambda_Application lambda_k p)
    (Lambda_Abstraction (lambda_lift p 0))"
  using lambda_contract_reduces[of "Lambda_Abstraction (Lambda_Variable 1)" p]
  by (simp add: lambda_k_def)

lemma lambda_k_application:
  "lambda_reduces (Lambda_Application (Lambda_Application lambda_k p) q) p"
proof -
  have head: "lambda_reduces (Lambda_Application (Lambda_Application lambda_k p) q)
    (Lambda_Application (Lambda_Abstraction (lambda_lift p 0)) q)"
    by (rule lambda_reduces_left[OF lambda_k_head])
  have tail: "lambda_reduces
    (Lambda_Application (Lambda_Abstraction (lambda_lift p 0)) q) p"
    using lambda_contract_reduces[of "lambda_lift p 0" q] by simp
  show ?thesis by (rule rtranclp_trans[OF head tail])
qed

lemma lambda_s_head:
  "lambda_reduces (Lambda_Application lambda_s p)
    (Lambda_Abstraction (Lambda_Abstraction
      (Lambda_Application
        (Lambda_Application (lambda_lift (lambda_lift p 0) 0) (Lambda_Variable 0))
        (Lambda_Application (Lambda_Variable 1) (Lambda_Variable 0)))))"
  using lambda_contract_reduces[of
    "Lambda_Abstraction (Lambda_Abstraction
      (Lambda_Application (Lambda_Application (Lambda_Variable 2) (Lambda_Variable 0))
        (Lambda_Application (Lambda_Variable 1) (Lambda_Variable 0))))" p]
  by (simp add: lambda_s_def lambda_substitute.simps(1))

lemma lambda_substitute_twice_lifted:
  "lambda_substitute (lambda_lift (lambda_lift p 0) 0)
    (lambda_lift q 0) (Suc 0)=lambda_lift p 0"
  using lambda_lift_substitute_below[where i=0 and j=0 and p="lambda_lift p 0" and q=q]
  by simp

lemma lambda_s_head_two:
  "lambda_reduces (Lambda_Application (Lambda_Application lambda_s p) q)
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application (lambda_lift p 0) (Lambda_Variable 0))
      (Lambda_Application (lambda_lift q 0) (Lambda_Variable 0))))"
proof -
  let ?b = "Lambda_Application
    (Lambda_Application (lambda_lift (lambda_lift p 0) 0) (Lambda_Variable 0))
    (Lambda_Application (Lambda_Variable 1) (Lambda_Variable 0))"
  have head: "lambda_reduces (Lambda_Application (Lambda_Application lambda_s p) q)
    (Lambda_Application (Lambda_Abstraction (Lambda_Abstraction ?b)) q)"
    by (rule lambda_reduces_left[OF lambda_s_head])
  have tail: "lambda_reduces
    (Lambda_Application (Lambda_Abstraction (Lambda_Abstraction ?b)) q)
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application (lambda_lift p 0) (Lambda_Variable 0))
      (Lambda_Application (lambda_lift q 0) (Lambda_Variable 0))))"
    using lambda_contract_reduces[of "Lambda_Abstraction ?b" q]
    by (simp add: lambda_substitute_twice_lifted)
  show ?thesis by (rule rtranclp_trans[OF head tail])
qed

lemma lambda_s_application:
  "lambda_reduces
    (Lambda_Application (Lambda_Application (Lambda_Application lambda_s p) q) r)
    (Lambda_Application (Lambda_Application p r) (Lambda_Application q r))"
proof -
  let ?b = "Lambda_Application
    (Lambda_Application (lambda_lift p 0) (Lambda_Variable 0))
    (Lambda_Application (lambda_lift q 0) (Lambda_Variable 0))"
  have head: "lambda_reduces
    (Lambda_Application (Lambda_Application (Lambda_Application lambda_s p) q) r)
    (Lambda_Application (Lambda_Abstraction ?b) r)"
    by (rule lambda_reduces_left[OF lambda_s_head_two])
  have tail: "lambda_reduces (Lambda_Application (Lambda_Abstraction ?b) r)
    (Lambda_Application (Lambda_Application p r) (Lambda_Application q r))"
    using lambda_contract_reduces[of ?b r] by simp
  show ?thesis by (rule rtranclp_trans[OF head tail])
qed

fun interpret_sk :: "sk_term \<Rightarrow> lambda_term" where
  "interpret_sk SK_S=lambda_s"
| "interpret_sk SK_K=lambda_k"
| "interpret_sk (SK_App p q)=Lambda_Application (interpret_sk p) (interpret_sk q)"

fun interpret_open_sk :: "open_sk \<Rightarrow> lambda_term" where
  "interpret_open_sk Open_S=lambda_s"
| "interpret_open_sk Open_K=lambda_k"
| "interpret_open_sk (Open_Variable n)=Lambda_Variable n"
| "interpret_open_sk (Open_Application p q)=
    Lambda_Application (interpret_open_sk p) (interpret_open_sk q)"

lemma interpret_sk_closed: "lambda_scoped 0 (interpret_sk p)"
  by (induction p) simp_all

lemma closed_open_sk_interpretation:
  assumes "open_sk_variables p={}"
  shows "interpret_sk (evaluate_open_sk f p)=interpret_open_sk p"
  using assms by (induction p) auto

theorem sk_step_interpretation:
  assumes "sk_step p q"
  shows "lambda_reduces (interpret_sk p) (interpret_sk q)"
  using assms by (induction rule: sk_step.induct)
    (auto intro: lambda_k_application lambda_s_application
      lambda_reduces_left lambda_reduces_right)

theorem sk_reduction_interpretation:
  assumes "sk_reduces p q"
  shows "lambda_reduces (interpret_sk p) (interpret_sk q)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_trans sk_step_interpretation)

lemma lambda_sk_identity_interpretation:
  "lambda_reduces (Lambda_Application (Lambda_Application lambda_s lambda_k) lambda_k)
    (Lambda_Abstraction (Lambda_Variable 0))"
proof -
  have head: "lambda_reduces
    (Lambda_Application (Lambda_Application lambda_s lambda_k) lambda_k)
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application lambda_k (Lambda_Variable 0))
      (Lambda_Application lambda_k (Lambda_Variable 0))))"
    using lambda_s_head_two[of lambda_k lambda_k] by simp
  have tail: "lambda_reduces
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application lambda_k (Lambda_Variable 0))
      (Lambda_Application lambda_k (Lambda_Variable 0))))
    (Lambda_Abstraction (Lambda_Variable 0))"
    by (rule lambda_reduces_under[OF lambda_k_application])
  show ?thesis by (rule rtranclp_trans[OF head tail])
qed

lemma lambda_lifted_abstraction_application:
  assumes "lambda_reduces p (Lambda_Abstraction q)"
  shows "lambda_reduces (Lambda_Application (lambda_lift p 0) (Lambda_Variable 0)) q"
proof -
  have lifted: "lambda_reduces (lambda_lift p 0)
    (Lambda_Abstraction (lambda_lift q (Suc 0)))"
    using lambda_reduces_lift[OF assms, of 0] by simp
  have head: "lambda_reduces (Lambda_Application (lambda_lift p 0) (Lambda_Variable 0))
    (Lambda_Application (Lambda_Abstraction (lambda_lift q (Suc 0))) (Lambda_Variable 0))"
    by (rule lambda_reduces_left[OF lifted])
  have tail: "lambda_reduces
    (Lambda_Application (Lambda_Abstraction (lambda_lift q (Suc 0))) (Lambda_Variable 0)) q"
    using lambda_contract_reduces[of "lambda_lift q (Suc 0)" "Lambda_Variable 0"] by simp
  show ?thesis by (rule rtranclp_trans[OF head tail])
qed

theorem sk_abstraction_interpretation:
  "lambda_reduces (interpret_open_sk (sk_abstract p))
    (Lambda_Abstraction (interpret_open_sk p))"
proof (induction p rule: sk_abstract.induct)
  case 1
  then show ?case using lambda_k_head[of lambda_s] by simp
next
  case 2
  then show ?case using lambda_k_head[of lambda_k] by simp
next
  case 3
  then show ?case using lambda_sk_identity_interpretation by simp
next
  case (4 n)
  then show ?case using lambda_k_head[of "Lambda_Variable n"] by simp
next
  case application: (5 p q)
  let ?p = "interpret_open_sk (sk_abstract p)"
  let ?q = "interpret_open_sk (sk_abstract q)"
  have head: "lambda_reduces (Lambda_Application (Lambda_Application lambda_s ?p) ?q)
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application (lambda_lift ?p 0) (Lambda_Variable 0))
      (Lambda_Application (lambda_lift ?q 0) (Lambda_Variable 0))))"
    by (rule lambda_s_head_two)
  have tail: "lambda_reduces
    (Lambda_Abstraction (Lambda_Application
      (Lambda_Application (lambda_lift ?p 0) (Lambda_Variable 0))
      (Lambda_Application (lambda_lift ?q 0) (Lambda_Variable 0))))
    (Lambda_Abstraction (Lambda_Application (interpret_open_sk p) (interpret_open_sk q)))"
    by (rule lambda_reduces_under, rule lambda_reduces_application,
      rule lambda_lifted_abstraction_application[OF application.IH(1)],
      rule lambda_lifted_abstraction_application[OF application.IH(2)])
  show ?case using rtranclp_trans[OF head tail] by simp
qed

theorem lambda_compilation_interpretation:
  "lambda_reduces (interpret_open_sk (compile_lambda p)) p"
proof (induction p)
  case (Lambda_Variable n)
  then show ?case by simp
next
  case (Lambda_Application p q)
  show ?case using lambda_reduces_application[OF Lambda_Application.IH] by simp
next
  case (Lambda_Abstraction p)
  have head: "lambda_reduces (interpret_open_sk (sk_abstract (compile_lambda p)))
    (Lambda_Abstraction (interpret_open_sk (compile_lambda p)))"
    by (rule sk_abstraction_interpretation)
  have tail: "lambda_reduces (Lambda_Abstraction (interpret_open_sk (compile_lambda p)))
    (Lambda_Abstraction p)"
    by (rule lambda_reduces_under[OF Lambda_Abstraction.IH])
  show ?case using rtranclp_trans[OF head tail] by simp
qed

theorem closed_lambda_compilation_interpretation:
  assumes "lambda_scoped 0 p"
  shows "lambda_reduces (interpret_sk (compile_lambda_closure (Lambda_Closure p e))) p"
proof -
  have empty: "open_sk_variables (compile_lambda p)={}"
    using assms closed_lambda_compilation by blast
  have same: "interpret_sk (compile_lambda_closure (Lambda_Closure p e))=
    interpret_open_sk (compile_lambda p)"
    by (simp only: compile_lambda_closure.simps closed_open_sk_interpretation[OF empty])
  show ?thesis by (simp only: same lambda_compilation_interpretation)
qed

text \<open>
  The interpretation gives S and K their closed lambda definitions and
  preserves ordered application. Every SK step becomes a finite beta reduction.
  Independently, bracket abstraction and the term compiler reduce back to their
  source terms after interpretation. These are reduction theorems, rather than
  a definition of source truth through the compiler. They do not yet identify
  beta reduction with termination of the closure evaluator.
\<close>

end
