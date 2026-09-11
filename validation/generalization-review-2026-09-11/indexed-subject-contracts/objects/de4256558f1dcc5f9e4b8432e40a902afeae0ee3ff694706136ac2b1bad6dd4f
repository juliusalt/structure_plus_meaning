theory Lambda_Substitution
  imports Lambda_Closures
begin

section \<open>Capture-avoiding substitution over the same lambda syntax\<close>

fun lambda_lift :: "lambda_term \<Rightarrow> nat \<Rightarrow> lambda_term" where
  "lambda_lift (Lambda_Variable i) k=
    (if i<k then Lambda_Variable i else Lambda_Variable (Suc i))"
| "lambda_lift (Lambda_Application p q) k=
    Lambda_Application (lambda_lift p k) (lambda_lift q k)"
| "lambda_lift (Lambda_Abstraction p) k=Lambda_Abstraction (lambda_lift p (Suc k))"

fun lambda_substitute :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> nat \<Rightarrow> lambda_term" where
  "lambda_substitute (Lambda_Variable i) q k=
    (if k<i then Lambda_Variable (i-1) else if i=k then q else Lambda_Variable i)"
| "lambda_substitute (Lambda_Application p r) q k=
    Lambda_Application (lambda_substitute p q k) (lambda_substitute r q k)"
| "lambda_substitute (Lambda_Abstraction p) q k=
    Lambda_Abstraction (lambda_substitute p (lambda_lift q 0) (Suc k))"

declare lambda_substitute.simps(1)[simp del]

lemma lambda_substitute_equal [simp]:
  "lambda_substitute (Lambda_Variable k) q k=q"
  by (simp add: lambda_substitute.simps(1))

lemma lambda_substitute_greater [simp]:
  "k<i \<Longrightarrow> lambda_substitute (Lambda_Variable i) q k=Lambda_Variable (i-1)"
  by (simp add: lambda_substitute.simps(1))

lemma lambda_substitute_less [simp]:
  "i<k \<Longrightarrow> lambda_substitute (Lambda_Variable i) q k=Lambda_Variable i"
  by (simp add: lambda_substitute.simps(1))

lemma lambda_lift_lift:
  "i<Suc k \<Longrightarrow>
    lambda_lift (lambda_lift p i) (Suc k)=lambda_lift (lambda_lift p k) i"
  by (induction p arbitrary: i k) auto

lemma lambda_lift_substitute [simp]:
  "j<Suc i \<Longrightarrow>
    lambda_lift (lambda_substitute p q j) i=
      lambda_substitute (lambda_lift p (Suc i)) (lambda_lift q i) j"
  by (induction p arbitrary: i j q)
    (simp_all add: diff_Suc lambda_substitute.simps(1) lambda_lift_lift split: nat.split)

lemma lambda_lift_substitute_below:
  "i<Suc j \<Longrightarrow>
    lambda_lift (lambda_substitute p q j) i=
      lambda_substitute (lambda_lift p i) (lambda_lift q i) (Suc j)"
  apply (induction p arbitrary: i j q)
  apply (simp_all add: lambda_substitute.simps(1) lambda_lift_lift)
  apply arith
  done

lemma lambda_substitute_lift [simp]:
  "lambda_substitute (lambda_lift p k) q k=p"
  by (induction p arbitrary: k q) simp_all

lemma lambda_substitute_shifted_variable [simp]:
  "lambda_substitute (lambda_lift p (Suc k)) (Lambda_Variable k) k=p"
  by (induction p arbitrary: k) (auto simp: lambda_substitute.simps(1))

lemma lambda_substitution_composition:
  "i<Suc j \<Longrightarrow>
    lambda_substitute (lambda_substitute p (lambda_lift v i) (Suc j))
      (lambda_substitute u v j) i=
    lambda_substitute (lambda_substitute p u i) v j"
  by (induction p arbitrary: i j u v)
    (simp_all add: diff_Suc lambda_substitute.simps(1)
      lambda_lift_lift[symmetric] lambda_lift_substitute_below split: nat.split)

lemma lambda_lift_above_scope:
  assumes "lambda_scoped n p" "n\<le>k"
  shows "lambda_lift p k=p"
  using assms by (induction p arbitrary: n k) auto

lemma lambda_closed_lift [simp]:
  "lambda_scoped 0 p \<Longrightarrow> lambda_lift p k=p"
  by (rule lambda_lift_above_scope) auto

lemma lambda_substitute_above_scope:
  assumes "lambda_scoped n p" "n\<le>k"
  shows "lambda_substitute p q k=p"
  using assms by (induction p arbitrary: n k q)
    (auto simp: lambda_substitute.simps(1))

lemma lambda_closed_substitute [simp]:
  "lambda_scoped 0 p \<Longrightarrow> lambda_substitute p q k=p"
  by (rule lambda_substitute_above_scope) auto

lemma lambda_lift_scoped:
  assumes "lambda_scoped n p" "i\<le>n"
  shows "lambda_scoped (Suc n) (lambda_lift p i)"
  using assms by (induction p arbitrary: n i) auto

lemma lambda_substitute_scoped:
  assumes "lambda_scoped (Suc n) p" "lambda_scoped n q" "i\<le>n"
  shows "lambda_scoped n (lambda_substitute p q i)"
  using assms
proof (induction p arbitrary: n q i)
  case (Lambda_Variable k)
  then show ?case by (auto simp: lambda_substitute.simps(1))
next
  case (Lambda_Application p r)
  then show ?case by auto
next
  case (Lambda_Abstraction p)
  have body: "lambda_scoped (Suc (Suc n)) p" using Lambda_Abstraction.prems(1) by simp
  have argument: "lambda_scoped (Suc n) (lambda_lift q 0)"
    by (rule lambda_lift_scoped[OF Lambda_Abstraction.prems(2)]) simp
  have index: "Suc i\<le>Suc n" using Lambda_Abstraction.prems(3) by simp
  show ?case using Lambda_Abstraction.IH[OF body argument index] by simp
qed

text \<open>
  Lifting and substitution operate on the existing de Bruijn syntax. The
  substitution equations and composition argument follow the method in
  Tobias Nipkow's Isabelle development HOL/Proofs/Lambda/Lambda.thy (1995);
  the proofs here are checked over this repository's source datatype.
  No representation of SK or Factor is used in these equations.
\<close>

end
