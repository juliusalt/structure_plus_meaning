theory Right_Ordered_Terms
  imports Ordered_Term_Comparison
begin

section \<open>Terms are ordered at the right of a pair first\<close>

text \<open>
  Every collection notion of the native programs passes its context as the left component of its
  argument, so the calls of one evaluation share their left components. A key ordered at the right
  component of a pair first tells two calls of one context apart where they differ, and only equal
  calls are compared completely. The order is the order of the mirrored term, which exchanges the
  components of every pair; the mirror is injective, so the order is linear, and it is computed on
  the term itself without constructing the mirror.
\<close>

fun mirror_term :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "mirror_term (Finite_Pair a b)=Finite_Pair (mirror_term b) (mirror_term a)"
| "mirror_term (Finite_Payload v)=Finite_Payload v"
| "mirror_term (Finite_Target t)=Finite_Target t"

lemma mirror_term_mirror [simp]: "mirror_term (mirror_term t)=t"
  by (induction t) simp_all

lemma mirror_term_injective: "mirror_term t=mirror_term u \<longleftrightarrow> t=u"
  by (metis mirror_term_mirror)

datatype right_ordered_term = Right_Ordered_Term finite_factor_term

fun unright_term :: "right_ordered_term \<Rightarrow> finite_factor_term" where
  "unright_term (Right_Ordered_Term t)=t"

definition right_order_key :: "right_ordered_term \<Rightarrow> ordered_factor_term" where
  "right_order_key x=Ordered_Factor_Term (mirror_term (unright_term x))"

lemma right_order_key_injective: "right_order_key x=right_order_key y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: right_order_key_def mirror_term_injective)

instantiation right_ordered_term :: linorder
begin

definition "x\<le>y \<longleftrightarrow> right_order_key x\<le>right_order_key y"
definition "x<y \<longleftrightarrow> right_order_key x<right_order_key y"

instance
  by standard
    (auto simp: less_eq_right_ordered_term_def less_right_ordered_term_def
      less_le_not_le right_order_key_injective
      intro: order_trans dest: order_antisym)

end

fun finite_term_compare_right :: "finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> linear_comparison" where
  "finite_term_compare_right (Finite_Payload v) (Finite_Payload w)=compare_address v w"
| "finite_term_compare_right (Finite_Target (Finite_Whole a)) (Finite_Target (Finite_Whole b))=compare_artifacts a b"
| "finite_term_compare_right (Finite_Target (Finite_Anchor a r)) (Finite_Target (Finite_Anchor b s))=
    (case compare_artifacts a b of Linear_Equal \<Rightarrow> compare_address r s | c \<Rightarrow> c)"
| "finite_term_compare_right (Finite_Pair t u) (Finite_Pair t' u')=
    (case finite_term_compare_right u u' of Linear_Equal \<Rightarrow> finite_term_compare_right t t' | c \<Rightarrow> c)"
| "finite_term_compare_right t u=compare_natural (finite_term_tag t) (finite_term_tag u)"

lemma finite_term_tag_mirror [simp]: "finite_term_tag (mirror_term t)=finite_term_tag t"
  by (cases t rule: finite_term_tag.cases) simp_all

lemma finite_term_compare_right_mirror:
  "finite_term_compare_right t u=finite_term_compare (mirror_term t) (mirror_term u)"
  by (induction t u rule: finite_term_compare_right.induct) (auto split: linear_comparison.split)

lemma less_eq_right_ordered_term_code [code]:
  "Right_Ordered_Term t\<le>Right_Ordered_Term u \<longleftrightarrow> finite_term_compare_right t u\<noteq>Linear_Greater"
  by (simp add: less_eq_right_ordered_term_def right_order_key_def finite_term_compare_right_mirror
    less_eq_ordered_factor_term_structural_code)

lemma less_right_ordered_term_code [code]:
  "Right_Ordered_Term t<Right_Ordered_Term u \<longleftrightarrow> finite_term_compare_right t u=Linear_Less"
  by (simp add: less_right_ordered_term_def right_order_key_def finite_term_compare_right_mirror
    less_ordered_factor_term_structural_code)

lemma equal_right_ordered_term_code [code]:
  "HOL.equal (Right_Ordered_Term t) (Right_Ordered_Term u) \<longleftrightarrow> finite_term_compare_right t u=Linear_Equal"
proof -
  have "HOL.equal (Right_Ordered_Term t) (Right_Ordered_Term u) \<longleftrightarrow>
      HOL.equal (Ordered_Factor_Term (mirror_term t)) (Ordered_Factor_Term (mirror_term u))"
    by (simp add: equal_eq mirror_term_injective)
  also have "\<dots> \<longleftrightarrow> finite_term_compare (mirror_term t) (mirror_term u)=Linear_Equal"
    by (rule equal_ordered_factor_term_structural_code)
  finally show ?thesis by (simp only: finite_term_compare_right_mirror)
qed

end
