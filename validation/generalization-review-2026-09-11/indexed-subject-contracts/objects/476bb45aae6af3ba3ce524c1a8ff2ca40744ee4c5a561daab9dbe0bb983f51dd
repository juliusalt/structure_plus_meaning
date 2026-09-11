theory SK_Numerals
  imports SK_Lambda_Compilation SK_Confluence
begin

section \<open>Compiled Church numerals with distinct normal outputs\<close>

fun lambda_iteration :: "nat \<Rightarrow> lambda_term" where
  "lambda_iteration 0=Lambda_Variable 0"
| "lambda_iteration (Suc n)=Lambda_Application (Lambda_Variable 1) (lambda_iteration n)"

definition lambda_numeral :: "nat \<Rightarrow> lambda_term" where
  "lambda_numeral n=Lambda_Abstraction (Lambda_Abstraction (lambda_iteration n))"

lemma lambda_iteration_scoped: "lambda_scoped (Suc (Suc 0)) (lambda_iteration n)"
  by (induction n) auto

lemma lambda_numeral_closed: "lambda_scoped 0 (lambda_numeral n)"
  by (simp add: lambda_numeral_def lambda_iteration_scoped)

fun sk_iteration :: "sk_term \<Rightarrow> sk_term \<Rightarrow> nat \<Rightarrow> sk_term" where
  "sk_iteration f x 0=x"
| "sk_iteration f x (Suc n)=SK_App f (sk_iteration f x n)"

lemma compile_lambda_iteration:
  "evaluate_open_sk g (compile_lambda (lambda_iteration n))=sk_iteration (g 1) (g 0) n"
  by (induction n) auto

definition sk_numeral :: "nat \<Rightarrow> sk_term" where
  "sk_numeral n=compile_lambda_closure (Lambda_Closure (lambda_numeral n) [])"

theorem sk_numeral_application:
  "sk_reduces (SK_App (SK_App (sk_numeral n) f) x) (sk_iteration f x n)"
proof -
  let ?body = "compile_lambda (lambda_iteration n)"
  let ?e = "sk_environment []"
  let ?v = "evaluate_open_sk (case_nat f ?e) (sk_abstract ?body)"
  have first: "sk_reduces (SK_App (sk_numeral n) f) ?v"
    using sk_abstraction_application[of ?e "sk_abstract ?body" f]
    by (simp add: sk_numeral_def lambda_numeral_def)
  have second: "sk_reduces (SK_App ?v x) (sk_iteration f x n)"
    using sk_abstraction_application[of "case_nat f ?e" ?body x]
    by (simp add: compile_lambda_iteration)
  show ?thesis by (rule rtranclp_trans[OF sk_reduces_left[OF first] second])
qed

fun sk_natural :: "nat \<Rightarrow> sk_term" where
  "sk_natural 0=SK_S"
| "sk_natural (Suc n)=SK_App SK_K (sk_natural n)"

lemma sk_natural_injective: "sk_natural m=sk_natural n \<longleftrightarrow> m=n"
  by (induction m arbitrary: n; case_tac n) simp_all

lemma sk_natural_has_no_step: "\<not> sk_step (sk_natural n) t"
  by (induction n arbitrary: t)
    (auto simp: sk_step_application_iff sk_s_has_no_step sk_k_has_no_step)

lemma sk_natural_reduces_only_to_itself:
  "sk_reduces (sk_natural n) t \<longleftrightarrow> t=sk_natural n"
proof
  assume "sk_reduces (sk_natural n) t"
  then show "t=sk_natural n"
    by (induction rule: rtranclp_induct) (auto simp: sk_natural_has_no_step)
next
  assume "t=sk_natural n"
  then show "sk_reduces (sk_natural n) t" by simp
qed

lemma sk_natural_reduction_iff:
  "sk_reduces (sk_natural m) (sk_natural n) \<longleftrightarrow> m=n"
  by (simp add: sk_natural_reduces_only_to_itself sk_natural_injective eq_commute)

lemma sk_natural_iteration: "sk_iteration SK_K SK_S n=sk_natural n"
  by (induction n) auto

theorem compiled_numeral_observation:
  "sk_reduces (SK_App (SK_App (sk_numeral n) SK_K) SK_S) (sk_natural n)"
  using sk_numeral_application[of n SK_K SK_S] by (simp add: sk_natural_iteration)

theorem compiled_numeral_observation_exact:
  "sk_reduces (SK_App (SK_App (sk_numeral n) SK_K) SK_S) (sk_natural m)
    \<longleftrightarrow> n=m"
proof
  assume reduction: "sk_reduces (SK_App (SK_App (sk_numeral n) SK_K) SK_S) (sk_natural m)"
  have "sk_natural n=sk_natural m"
    by (rule sk_normal_result_unique[OF compiled_numeral_observation reduction
      sk_natural_has_no_step sk_natural_has_no_step])
  then show "n=m" by (simp add: sk_natural_injective)
next
  assume "n=m"
  then show "sk_reduces (SK_App (SK_App (sk_numeral n) SK_K) SK_S) (sk_natural m)"
    by (simp add: compiled_numeral_observation)
qed

theorem sk_numeral_injective: "sk_numeral n=sk_numeral m \<longleftrightarrow> n=m"
proof
  assume "sk_numeral n=sk_numeral m"
  then have "sk_reduces (SK_App (SK_App (sk_numeral n) SK_K) SK_S) (sk_natural m)"
    using compiled_numeral_observation[of m] by simp
  then show "n=m" by (simp add: compiled_numeral_observation_exact)
next
  assume "n=m"
  then show "sk_numeral n=sk_numeral m" by simp
qed

text \<open>
  Church numerals are closed terms of the independently defined lambda calculus.
  Their compiled application performs every finite number of iterations.
  Applying a numeral to the stated constructor and base produces a distinct
  normal SK term for each natural number. Confluence proves that a compiled
  numeral cannot produce a different numeral output. Zero is S and successor
  adds one partial K application. These choices are test arguments to the
  existing calculus; they add no arithmetic rule to SK or Factor meaning.
\<close>

end
