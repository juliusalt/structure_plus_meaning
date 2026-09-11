theory SK_Confluence
  imports SK_Reduction "HOL-Library.Confluence"
begin

section \<open>Parallel reduction and unique normal results\<close>

inductive sk_parallel :: "sk_term \<Rightarrow> sk_term \<Rightarrow> bool" where
  s_atom: "sk_parallel SK_S SK_S"
| k_atom: "sk_parallel SK_K SK_K"
| application: "sk_parallel p p' \<Longrightarrow> sk_parallel q q' \<Longrightarrow>
    sk_parallel (SK_App p q) (SK_App p' q')"
| k: "sk_parallel x x' \<Longrightarrow> sk_parallel (SK_App (SK_App SK_K x) y) x'"
| s: "sk_parallel x x' \<Longrightarrow> sk_parallel y y' \<Longrightarrow> sk_parallel z z' \<Longrightarrow>
    sk_parallel (SK_App (SK_App (SK_App SK_S x) y) z)
      (SK_App (SK_App x' z') (SK_App y' z'))"

lemma sk_parallel_reflexive: "sk_parallel t t"
  by (induction t) (auto intro: sk_parallel.intros)

lemma sk_parallel_s_iff: "sk_parallel SK_S t \<longleftrightarrow> t=SK_S"
  by (auto elim: sk_parallel.cases intro: sk_parallel.s_atom)

lemma sk_parallel_k_iff: "sk_parallel SK_K t \<longleftrightarrow> t=SK_K"
  by (auto elim: sk_parallel.cases intro: sk_parallel.k_atom)

lemma sk_parallel_application_iff:
  "sk_parallel (SK_App p q) t \<longleftrightarrow>
    (\<exists>p' q'. sk_parallel p p' \<and> sk_parallel q q' \<and> t=SK_App p' q') \<or>
    (\<exists>x x'. p=SK_App SK_K x \<and> sk_parallel x x' \<and> t=x') \<or>
    (\<exists>x y x' y' z'. p=SK_App (SK_App SK_S x) y \<and>
      sk_parallel x x' \<and> sk_parallel y y' \<and> sk_parallel q z' \<and>
      t=SK_App (SK_App x' z') (SK_App y' z'))"
proof
  assume "sk_parallel (SK_App p q) t"
  then show "(\<exists>p' q'. sk_parallel p p' \<and> sk_parallel q q' \<and> t=SK_App p' q') \<or>
    (\<exists>x x'. p=SK_App SK_K x \<and> sk_parallel x x' \<and> t=x') \<or>
    (\<exists>x y x' y' z'. p=SK_App (SK_App SK_S x) y \<and>
      sk_parallel x x' \<and> sk_parallel y y' \<and> sk_parallel q z' \<and>
      t=SK_App (SK_App x' z') (SK_App y' z'))"
    by (cases rule: sk_parallel.cases) auto
next
  assume "(\<exists>p' q'. sk_parallel p p' \<and> sk_parallel q q' \<and> t=SK_App p' q') \<or>
    (\<exists>x x'. p=SK_App SK_K x \<and> sk_parallel x x' \<and> t=x') \<or>
    (\<exists>x y x' y' z'. p=SK_App (SK_App SK_S x) y \<and>
      sk_parallel x x' \<and> sk_parallel y y' \<and> sk_parallel q z' \<and>
      t=SK_App (SK_App x' z') (SK_App y' z'))"
  then show "sk_parallel (SK_App p q) t" by (auto intro: sk_parallel.intros)
qed

lemma sk_parallel_k_partial:
  "sk_parallel (SK_App SK_K x) t \<longleftrightarrow>
    (\<exists>x'. t=SK_App SK_K x' \<and> sk_parallel x x')"
  by (auto simp: sk_parallel_application_iff sk_parallel_k_iff)

lemma sk_parallel_s_partial:
  "sk_parallel (SK_App SK_S x) t \<longleftrightarrow>
    (\<exists>x'. t=SK_App SK_S x' \<and> sk_parallel x x')"
  by (auto simp: sk_parallel_application_iff sk_parallel_s_iff)

lemma sk_parallel_s_partial_two:
  "sk_parallel (SK_App (SK_App SK_S x) y) t \<longleftrightarrow>
    (\<exists>x' y'. t=SK_App (SK_App SK_S x') y' \<and> sk_parallel x x' \<and> sk_parallel y y')"
  by (auto simp: sk_parallel_application_iff sk_parallel_s_iff)

lemma sk_step_is_parallel:
  assumes "sk_step t u"
  shows "sk_parallel t u"
  using assms by (induction rule: sk_step.induct)
    (auto intro: sk_parallel.intros sk_parallel_reflexive)

lemma sk_parallel_reduces:
  assumes "sk_parallel t u"
  shows "sk_reduces t u"
  using assms
proof (induction rule: sk_parallel.induct)
  case s_atom
  then show ?case by simp
next
  case k_atom
  then show ?case by simp
next
  case (application p p' q q')
  show ?case by (rule sk_reduces_application[OF application.IH])
next
  case (k x x' y)
  have first: "sk_reduces (SK_App (SK_App SK_K x) y) x"
    by (rule r_into_rtranclp, rule sk_step.k)
  show ?case by (rule rtranclp_trans[OF first k.IH])
next
  case (s x x' y y' z z')
  have first: "sk_reduces (SK_App (SK_App (SK_App SK_S x) y) z)
    (SK_App (SK_App x z) (SK_App y z))"
    by (rule r_into_rtranclp, rule sk_step.s)
  have rest: "sk_reduces (SK_App (SK_App x z) (SK_App y z))
    (SK_App (SK_App x' z') (SK_App y' z'))"
    by (rule sk_reduces_application[OF sk_reduces_application[OF s.IH(1) s.IH(3)]
      sk_reduces_application[OF s.IH(2) s.IH(3)]])
  show ?case by (rule rtranclp_trans[OF first rest])
qed

fun sk_develop :: "sk_term \<Rightarrow> sk_term" where
  "sk_develop SK_S=SK_S"
| "sk_develop SK_K=SK_K"
| "sk_develop (SK_App (SK_App SK_K x) y)=sk_develop x"
| "sk_develop (SK_App (SK_App (SK_App SK_S x) y) z)=
    SK_App (SK_App (sk_develop x) (sk_develop z)) (SK_App (sk_develop y) (sk_develop z))"
| "sk_develop (SK_App p q)=SK_App (sk_develop p) (sk_develop q)"

lemma sk_develop_nonredex:
  assumes "\<not> (\<exists>x. p=SK_App SK_K x)" "\<not> (\<exists>x y. p=SK_App (SK_App SK_S x) y)"
  shows "sk_develop (SK_App p q)=SK_App (sk_develop p) (sk_develop q)"
proof (cases p)
  case SK_S
  then show ?thesis by simp
next
  case SK_K
  then show ?thesis by simp
next
  case outer: (SK_App a b)
  show ?thesis
  proof (cases a)
    case SK_S
    then show ?thesis using outer by simp
  next
    case SK_K
    then show ?thesis using outer assms(1) by blast
  next
    case middle: (SK_App c d)
    show ?thesis
    proof (cases c)
      case SK_S
      then show ?thesis using outer middle assms(2) by blast
    next
      case SK_K
      then show ?thesis using outer middle by simp
    next
      case (SK_App e f)
      then show ?thesis using outer middle by simp
    qed
  qed
qed

lemma sk_parallel_development:
  assumes "sk_parallel t u"
  shows "sk_parallel u (sk_develop t)"
  using assms
proof (induction rule: sk_parallel.induct)
  case s_atom
  then show ?case by (simp add: sk_parallel_s_iff)
next
  case k_atom
  then show ?case by (simp add: sk_parallel_k_iff)
next
  case (application p p' q q')
  show ?case
  proof (cases "\<exists>x. p=SK_App SK_K x")
    case True
    then obtain x where p: "p=SK_App SK_K x" by blast
    obtain x' where p': "p'=SK_App SK_K x'"
      using application.hyps(1) p by (auto simp: sk_parallel_k_partial)
    have x: "sk_parallel x' (sk_develop x)"
      using application.IH(1) by (auto simp: p p' sk_parallel_k_partial)
    show ?thesis using sk_parallel.k[OF x, of q'] by (simp add: p p')
  next
    case no_k: False
    show ?thesis
    proof (cases "\<exists>x y. p=SK_App (SK_App SK_S x) y")
      case True
      then obtain x y where p: "p=SK_App (SK_App SK_S x) y" by blast
      obtain x' y' where p': "p'=SK_App (SK_App SK_S x') y'"
        using application.hyps(1) p by (auto simp: sk_parallel_s_partial_two)
      have x: "sk_parallel x' (sk_develop x)" and y: "sk_parallel y' (sk_develop y)"
        using application.IH(1) by (auto simp: p p' sk_parallel_s_partial_two)
      show ?thesis using sk_parallel.s[OF x y application.IH(2)] by (simp add: p p')
    next
      case False
      show ?thesis
        using sk_parallel.application[OF application.IH] sk_develop_nonredex[OF no_k False, of q]
        by simp
    qed
  qed
next
  case (k x x' y)
  then show ?case by simp
next
  case (s x x' y y' z z')
  then show ?case by (auto intro: sk_parallel.application)
qed

lemma sk_parallel_confluent: "confluentp sk_parallel"
proof (rule strong_confluentp_imp_confluentp, rule strong_confluentpI)
  fix x y z
  assume xy: "sk_parallel x y" and xz: "sk_parallel x z"
  have left: "rtranclp sk_parallel y (sk_develop x)"
    by (rule r_into_rtranclp, rule sk_parallel_development[OF xy])
  have right: "sk_parallel z (sk_develop x)" by (rule sk_parallel_development[OF xz])
  show "\<exists>u. rtranclp sk_parallel y u \<and> reflclp sk_parallel z u"
    using left right by (auto intro: exI[of _ "sk_develop x"])
qed

lemma sk_reduces_parallel:
  assumes "sk_reduces t u"
  shows "rtranclp sk_parallel t u"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl sk_step_is_parallel)

lemma sk_parallel_closure_reduces:
  assumes "rtranclp sk_parallel t u"
  shows "sk_reduces t u"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_trans sk_parallel_reduces)

theorem sk_confluent: "confluentp sk_step"
proof (rule confluentpI)
  fix x y z
  assume xy: "sk_reduces x y" and xz: "sk_reduces x z"
  obtain u where "rtranclp sk_parallel y u" "rtranclp sk_parallel z u"
    using confluentpD[OF sk_parallel_confluent sk_reduces_parallel[OF xy] sk_reduces_parallel[OF xz]]
    by blast
  then show "\<exists>u. sk_reduces y u \<and> sk_reduces z u"
    using sk_parallel_closure_reduces by blast
qed

theorem sk_normal_result_unique:
  assumes "sk_reduces t u" "sk_reduces t v" "\<And>w. \<not> sk_step u w" "\<And>w. \<not> sk_step v w"
  shows "u=v"
proof -
  obtain w where uw: "sk_reduces u w" and vw: "sk_reduces v w"
    using confluentpD[OF sk_confluent assms(1,2)] by blast
  have "w=u" using uw by (induction rule: rtranclp_induct) (auto simp: assms(3))
  moreover have "w=v" using vw by (induction rule: rtranclp_induct) (auto simp: assms(4))
  ultimately show ?thesis by simp
qed

text \<open>
  Parallel reduction is an auxiliary relation for the confluence proof.
  Its finite closure is exactly ordinary SK reduction. Complete development
  joins every pair of parallel reducts, so two ordinary reductions to normal
  results must agree. These proof devices add no reduction rule to the calculus.
\<close>

end
