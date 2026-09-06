theory SK_Abstraction
  imports SK_Reduction
begin

section \<open>Finite open combinators and bracket abstraction\<close>

datatype open_sk =
    Open_S
  | Open_K
  | Open_Variable nat
  | Open_Application open_sk open_sk

fun open_sk_variables :: "open_sk \<Rightarrow> nat set" where
  "open_sk_variables Open_S={}"
| "open_sk_variables Open_K={}"
| "open_sk_variables (Open_Variable n)={n}"
| "open_sk_variables (Open_Application p q)=open_sk_variables p \<union> open_sk_variables q"

lemma open_sk_variables_finite: "finite (open_sk_variables p)"
  by (induction p) auto

fun evaluate_open_sk :: "(nat \<Rightarrow> sk_term) \<Rightarrow> open_sk \<Rightarrow> sk_term" where
  "evaluate_open_sk f Open_S=SK_S"
| "evaluate_open_sk f Open_K=SK_K"
| "evaluate_open_sk f (Open_Variable n)=f n"
| "evaluate_open_sk f (Open_Application p q)=SK_App (evaluate_open_sk f p) (evaluate_open_sk f q)"

lemma evaluate_open_sk_agreement:
  assumes "\<And>n. n\<in>open_sk_variables p \<Longrightarrow> f n=g n"
  shows "evaluate_open_sk f p=evaluate_open_sk g p"
  using assms by (induction p) auto

fun sk_abstract :: "open_sk \<Rightarrow> open_sk" where
  "sk_abstract Open_S=Open_Application Open_K Open_S"
| "sk_abstract Open_K=Open_Application Open_K Open_K"
| "sk_abstract (Open_Variable 0)=
    Open_Application (Open_Application Open_S Open_K) Open_K"
| "sk_abstract (Open_Variable (Suc n))=Open_Application Open_K (Open_Variable n)"
| "sk_abstract (Open_Application p q)=
    Open_Application (Open_Application Open_S (sk_abstract p)) (sk_abstract q)"

lemma sk_abstract_variables:
  "n\<in>open_sk_variables (sk_abstract p) \<longleftrightarrow> Suc n\<in>open_sk_variables p"
  by (induction p rule: sk_abstract.induct) auto

lemma sk_abstract_scope:
  "(\<forall>k\<in>open_sk_variables (sk_abstract p). k<n) \<longleftrightarrow>
    (\<forall>k\<in>open_sk_variables p. k<Suc n)"
proof
  assume bounded: "\<forall>k\<in>open_sk_variables (sk_abstract p). k<n"
  show "\<forall>k\<in>open_sk_variables p. k<Suc n"
  proof (intro ballI)
    fix k
    assume "k\<in>open_sk_variables p"
    then show "k<Suc n" using bounded by (cases k) (auto simp: sk_abstract_variables)
  qed
next
  assume "\<forall>k\<in>open_sk_variables p. k<Suc n"
  then show "\<forall>k\<in>open_sk_variables (sk_abstract p). k<n"
    by (auto simp: sk_abstract_variables)
qed

theorem sk_abstraction_application:
  "sk_reduces (SK_App (evaluate_open_sk f (sk_abstract p)) x)
    (evaluate_open_sk (case_nat x f) p)"
proof (induction p arbitrary: f x)
  case Open_S
  then show ?case by (auto intro: r_into_rtranclp sk_step.k)
next
  case Open_K
  then show ?case by (auto intro: r_into_rtranclp sk_step.k)
next
  case (Open_Variable n)
  then show ?case
    by (cases n) (auto simp: sk_identity_def[symmetric]
      intro: sk_identity_reduces r_into_rtranclp sk_step.k)
next
  case (Open_Application p q)
  have first: "sk_reduces
    (SK_App (SK_App (SK_App SK_S (evaluate_open_sk f (sk_abstract p)))
      (evaluate_open_sk f (sk_abstract q))) x)
    (SK_App (SK_App (evaluate_open_sk f (sk_abstract p)) x)
      (SK_App (evaluate_open_sk f (sk_abstract q)) x))"
    by (rule r_into_rtranclp, rule sk_step.s)
  have rest: "sk_reduces
    (SK_App (SK_App (evaluate_open_sk f (sk_abstract p)) x)
      (SK_App (evaluate_open_sk f (sk_abstract q)) x))
    (SK_App (evaluate_open_sk (case_nat x f) p) (evaluate_open_sk (case_nat x f) q))"
    by (rule sk_reduces_application[OF Open_Application.IH(1) Open_Application.IH(2)])
  show ?case using rtranclp_trans[OF first rest] by simp
qed

text \<open>
  Indices and ordered application belong to this external computation model.
  Abstraction removes index zero and lowers every remaining free index.
  Its application law follows from the independently defined K and S rules.
  Evaluation depends only on the finite set of variables actually present.
\<close>

end
