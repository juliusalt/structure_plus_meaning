theory SK_Reduction
  imports Main
begin

section \<open>An external combinatory reduction relation\<close>

datatype sk_term = SK_S | SK_K | SK_App sk_term sk_term

inductive sk_step :: "sk_term \<Rightarrow> sk_term \<Rightarrow> bool" where
  k: "sk_step (SK_App (SK_App SK_K x) y) x"
| s: "sk_step (SK_App (SK_App (SK_App SK_S x) y) z)
    (SK_App (SK_App x z) (SK_App y z))"
| left: "sk_step x y \<Longrightarrow> sk_step (SK_App x z) (SK_App y z)"
| right: "sk_step x y \<Longrightarrow> sk_step (SK_App z x) (SK_App z y)"

abbreviation sk_reduces :: "sk_term \<Rightarrow> sk_term \<Rightarrow> bool" where
  "sk_reduces \<equiv> rtranclp sk_step"

lemma sk_reduces_left:
  assumes "sk_reduces x y"
  shows "sk_reduces (SK_App x z) (SK_App y z)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl sk_step.left)

lemma sk_reduces_right:
  assumes "sk_reduces x y"
  shows "sk_reduces (SK_App z x) (SK_App z y)"
  using assms by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl sk_step.right)

lemma sk_reduces_application:
  assumes "sk_reduces x y" "sk_reduces z w"
  shows "sk_reduces (SK_App x z) (SK_App y w)"
  using sk_reduces_left[OF assms(1), of z] sk_reduces_right[OF assms(2), of y]
  by (rule rtranclp_trans)

definition sk_identity :: sk_term where
  "sk_identity=SK_App (SK_App SK_S SK_K) SK_K"

theorem sk_identity_reduces:
  "sk_reduces (SK_App sk_identity x) x"
proof -
  have first: "sk_step (SK_App sk_identity x) (SK_App (SK_App SK_K x) (SK_App SK_K x))"
    unfolding sk_identity_def by (rule sk_step.s)
  have second: "sk_step (SK_App (SK_App SK_K x) (SK_App SK_K x)) x" by (rule sk_step.k)
  show ?thesis using first second by (meson rtranclp.rtrancl_into_rtrancl r_into_rtranclp)
qed

lemma sk_s_has_no_step: "\<not> sk_step SK_S t"
  by (auto elim: sk_step.cases)

lemma sk_k_has_no_step: "\<not> sk_step SK_K t"
  by (auto elim: sk_step.cases)

lemma sk_step_application_iff:
  "sk_step (SK_App p q) t \<longleftrightarrow>
    (\<exists>p'. sk_step p p' \<and> t=SK_App p' q) \<or>
    (\<exists>q'. sk_step q q' \<and> t=SK_App p q') \<or>
    (\<exists>x. p=SK_App SK_K x \<and> t=x) \<or>
    (\<exists>x y. p=SK_App (SK_App SK_S x) y \<and> t=SK_App (SK_App x q) (SK_App y q))"
  by (auto elim: sk_step.cases intro: sk_step.intros)

lemma sk_s_reduces_only_to_itself: "sk_reduces SK_S t \<longleftrightarrow> t=SK_S"
proof
  assume "sk_reduces SK_S t"
  then show "t=SK_S" by (induction rule: rtranclp_induct) (auto simp: sk_s_has_no_step)
next
  assume "t=SK_S" then show "sk_reduces SK_S t" by simp
qed

theorem sk_identity_composition_reduces:
  "sk_reduces (SK_App (SK_App sk_identity sk_identity) x) x"
proof -
  have head_reduction: "sk_reduces (SK_App (SK_App sk_identity sk_identity) x) (SK_App sk_identity x)"
    by (rule sk_reduces_left[OF sk_identity_reduces])
  show ?thesis using head_reduction sk_identity_reduces[of x] by (rule rtranclp_trans)
qed

text \<open>
  This external relation defines the adequacy target independently of Factor.
  Application has its ordinary ordered arguments. Context rules permit reduction
  in either argument, and finite computation is reflexive transitive closure.
\<close>

end
