theory Lambda_Confluence
  imports Lambda_Reduction "HOL-Library.Confluence"
begin

section \<open>Confluence of the independent source calculus\<close>

inductive lambda_parallel :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  variable [simp, intro!]: "lambda_parallel (Lambda_Variable n) (Lambda_Variable n)"
| abstraction [simp, intro!]: "lambda_parallel p q \<Longrightarrow>
    lambda_parallel (Lambda_Abstraction p) (Lambda_Abstraction q)"
| application [simp, intro!]: "lambda_parallel p p' \<Longrightarrow> lambda_parallel q q' \<Longrightarrow>
    lambda_parallel (Lambda_Application p q) (Lambda_Application p' q')"
| contract [simp, intro!]: "lambda_parallel p p' \<Longrightarrow> lambda_parallel q q' \<Longrightarrow>
    lambda_parallel (Lambda_Application (Lambda_Abstraction p) q) (lambda_substitute p' q' 0)"

inductive_cases lambda_parallel_elims [elim!]:
  "lambda_parallel (Lambda_Variable n) p"
  "lambda_parallel (Lambda_Abstraction p) (Lambda_Abstraction q)"
  "lambda_parallel (Lambda_Application (Lambda_Abstraction p) q) r"
  "lambda_parallel (Lambda_Application p q) r"
  "lambda_parallel (Lambda_Abstraction p) q"

lemma lambda_parallel_variable [simp]:
  "lambda_parallel (Lambda_Variable n) p \<longleftrightarrow> p=Lambda_Variable n"
  by blast

lemma lambda_parallel_reflexive [simp]: "lambda_parallel p p"
  by (induction p) simp_all

lemma lambda_beta_is_parallel:
  assumes "lambda_beta p q"
  shows "lambda_parallel p q"
  using assms by (induction rule: lambda_beta.induct) auto

lemma lambda_parallel_reduces:
  assumes "lambda_parallel p q"
  shows "lambda_reduces p q"
  using assms
proof (induction rule: lambda_parallel.induct)
  case (variable n)
  then show ?case by simp
next
  case (abstraction p q)
  show ?case by (rule lambda_reduces_under[OF abstraction.IH])
next
  case (application p p' q q')
  show ?case by (rule lambda_reduces_application[OF application.IH])
next
  case (contract p p' q q')
  have head_reduction: "lambda_reduces (Lambda_Application (Lambda_Abstraction p) q)
    (Lambda_Application (Lambda_Abstraction p') q')"
    by (rule lambda_reduces_application[OF lambda_reduces_under[OF contract.IH(1)] contract.IH(2)])
  show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF head_reduction lambda_beta.contract])
qed

lemma lambda_parallel_lift [simp]:
  "lambda_parallel p q \<Longrightarrow> lambda_parallel (lambda_lift p n) (lambda_lift q n)"
  by (induction p arbitrary: q n) fastforce+

lemma lambda_parallel_substitute:
  "lambda_parallel s s' \<Longrightarrow> lambda_parallel t t' \<Longrightarrow>
    lambda_parallel (lambda_substitute t s n) (lambda_substitute t' s' n)"
  apply (induction t arbitrary: s s' t' n)
    apply (simp add: lambda_substitute.simps(1))
   apply (erule lambda_parallel_elims)
    apply simp
   apply (simp add: lambda_substitution_composition[symmetric])
   apply (fastforce intro!: lambda_parallel_lift)
  apply fastforce
  done

fun lambda_develop :: "lambda_term \<Rightarrow> lambda_term" where
  "lambda_develop (Lambda_Variable n)=Lambda_Variable n"
| "lambda_develop (Lambda_Application (Lambda_Variable n) q)=
    Lambda_Application (Lambda_Variable n) (lambda_develop q)"
| "lambda_develop (Lambda_Application (Lambda_Application p q) r)=
    Lambda_Application (lambda_develop (Lambda_Application p q)) (lambda_develop r)"
| "lambda_develop (Lambda_Application (Lambda_Abstraction p) q)=
    lambda_substitute (lambda_develop p) (lambda_develop q) 0"
| "lambda_develop (Lambda_Abstraction p)=Lambda_Abstraction (lambda_develop p)"

lemma lambda_parallel_development:
  "lambda_parallel p q \<Longrightarrow> lambda_parallel q (lambda_develop p)"
  by (induction p arbitrary: q rule: lambda_develop.induct)
    (auto intro: lambda_parallel_substitute)

lemma lambda_parallel_confluent: "confluentp lambda_parallel"
proof (rule strong_confluentp_imp_confluentp, rule strong_confluentpI)
  fix x y z
  assume xy: "lambda_parallel x y" and xz: "lambda_parallel x z"
  have left: "rtranclp lambda_parallel y (lambda_develop x)"
    by (rule r_into_rtranclp, rule lambda_parallel_development[OF xy])
  have right: "lambda_parallel z (lambda_develop x)"
    by (rule lambda_parallel_development[OF xz])
  show "\<exists>u. rtranclp lambda_parallel y u \<and> reflclp lambda_parallel z u"
    using left right by (auto intro: exI[of _ "lambda_develop x"])
qed

lemma lambda_reduces_parallel:
  assumes "lambda_reduces p q"
  shows "rtranclp lambda_parallel p q"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl lambda_beta_is_parallel)

lemma lambda_parallel_closure_reduces:
  assumes "rtranclp lambda_parallel p q"
  shows "lambda_reduces p q"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_trans lambda_parallel_reduces)

theorem lambda_confluent: "confluentp lambda_beta"
proof (rule confluentpI)
  fix x y z
  assume xy: "lambda_reduces x y" and xz: "lambda_reduces x z"
  obtain u where "rtranclp lambda_parallel y u" "rtranclp lambda_parallel z u"
    using confluentpD[OF lambda_parallel_confluent
      lambda_reduces_parallel[OF xy] lambda_reduces_parallel[OF xz]] by blast
  then show "\<exists>u. lambda_reduces y u \<and> lambda_reduces z u"
    using lambda_parallel_closure_reduces by blast
qed

lemma lambda_irreducible_reduction:
  assumes "\<And>q. \<not> lambda_beta p q" "lambda_reduces p r"
  shows "r=p"
  using assms(2) by (induction rule: rtranclp_induct) (auto simp: assms(1))

theorem lambda_reduction_to_normal:
  assumes "lambda_reduces t p" "lambda_reduces t q" "\<And>r. \<not> lambda_beta q r"
  shows "lambda_reduces p q"
proof -
  obtain r where pr: "lambda_reduces p r" and qr: "lambda_reduces q r"
    using confluentpD[OF lambda_confluent assms(1,2)] by blast
  have "r=q" by (rule lambda_irreducible_reduction[OF assms(3) qr])
  then show ?thesis using pr by simp
qed

text \<open>
  Parallel substitution and complete development follow the proof method in
  Tobias Nipkow's HOL/Proofs/Lambda/ParRed.thy (1995). The independently defined
  beta relation and all proofs here use this repository's existing lambda
  syntax. Confluence does not assume a compiler or any internal truth relation.
\<close>

end
