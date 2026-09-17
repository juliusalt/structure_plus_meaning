theory Ordered_Term_Comparison
  imports Ordered_Finite_Terms Ordered_Artifact_Comparison
begin

section \<open>Executable terms compare structurally in their key order\<close>

lemma compare_linear_option:
  "compare_linear (None::'a::linorder option) None=Linear_Equal"
  "compare_linear (Some x) (Some y)=compare_linear x y"
  by (simp_all add: compare_linear_def)

lemma compare_linear_ordered_artifact:
  "compare_linear (Ordered_Complete_Artifact a) (Ordered_Complete_Artifact b)=compare_artifacts a b"
  by (auto simp: compare_linear_def less_ordered_complete_artifact_def finite_artifact_rows_injective
    compare_artifacts_rows)

fun finite_term_tag :: "finite_factor_term \<Rightarrow> nat" where
  "finite_term_tag (Finite_Payload v)=0"
| "finite_term_tag (Finite_Target (Finite_Whole a))=1"
| "finite_term_tag (Finite_Target (Finite_Anchor a r))=2"
| "finite_term_tag (Finite_Pair t u)=3"

fun finite_term_compare :: "finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> linear_comparison" where
  "finite_term_compare (Finite_Payload v) (Finite_Payload w)=compare_address v w"
| "finite_term_compare (Finite_Target (Finite_Whole a)) (Finite_Target (Finite_Whole b))=compare_artifacts a b"
| "finite_term_compare (Finite_Target (Finite_Anchor a r)) (Finite_Target (Finite_Anchor b s))=
    (case compare_artifacts a b of Linear_Equal \<Rightarrow> compare_address r s | c \<Rightarrow> c)"
| "finite_term_compare (Finite_Pair t u) (Finite_Pair t' u')=
    (case finite_term_compare t t' of Linear_Equal \<Rightarrow> finite_term_compare u u' | c \<Rightarrow> c)"
| "finite_term_compare t u=compare_natural (finite_term_tag t) (finite_term_tag u)"

lemma finite_term_key_tag: "\<exists>a v rest. finite_term_key t=(finite_term_tag t,a,v)#rest"
  by (cases t rule: finite_term_key.cases) simp_all

lemma finite_term_compare_distinct_tags:
  assumes "finite_term_tag t\<noteq>finite_term_tag u"
  shows "compare_linear (finite_term_key t@xs) (finite_term_key u@ys)=compare_natural (finite_term_tag t) (finite_term_tag u)"
proof -
  obtain a v rest where t: "finite_term_key t=(finite_term_tag t,a,v)#rest" using finite_term_key_tag by blast
  obtain b w rest' where u: "finite_term_key u=(finite_term_tag u,b,w)#rest'" using finite_term_key_tag by blast
  have "compare_linear (finite_term_tag t) (finite_term_tag u)\<noteq>Linear_Equal"
    using assms by (simp add: compare_linear_cases)
  then show ?thesis
    by (simp add: t u compare_linear_prefix compare_linear_pair compare_natural_linear split: linear_comparison.split)
qed

theorem finite_term_compare_keys:
  "compare_linear (finite_term_key t@xs) (finite_term_key u@ys)=
    (case finite_term_compare t u of Linear_Equal \<Rightarrow> compare_linear xs ys | c \<Rightarrow> c)"
proof (induction t arbitrary: u xs ys rule: finite_term_key.induct)
  case (1 v)
  show ?case
  proof (cases u rule: finite_term_key.cases)
    case (1 w)
    then show ?thesis
      by (simp add: compare_linear_prefix compare_linear_pair compare_linear_option compare_address_linear
        split: linear_comparison.split)
  qed (simp_all add: finite_term_compare_distinct_tags[simplified] compare_linear_def compare_natural_def)
next
  case (2 a)
  show ?case
  proof (cases u rule: finite_term_key.cases)
    case (2 b)
    then show ?thesis
      by (simp add: compare_linear_prefix compare_linear_pair compare_linear_option compare_linear_ordered_artifact
        split: linear_comparison.split)
  qed (simp_all add: finite_term_compare_distinct_tags[simplified] compare_linear_def compare_natural_def)
next
  case (3 a r)
  show ?case
  proof (cases u rule: finite_term_key.cases)
    case (3 b s)
    then show ?thesis
      by (simp add: compare_linear_prefix compare_linear_pair compare_linear_option compare_linear_ordered_artifact
        compare_address_linear split: linear_comparison.split)
  qed (simp_all add: finite_term_compare_distinct_tags[simplified] compare_linear_def compare_natural_def)
next
  case (4 t1 t2)
  show ?case
  proof (cases u rule: finite_term_key.cases)
    case (4 u1 u2)
    have "compare_linear (finite_term_key (Finite_Pair t1 t2)@xs) (finite_term_key u@ys)=
        compare_linear (finite_term_key t1@(finite_term_key t2@xs)) (finite_term_key u1@(finite_term_key u2@ys))"
      by (simp add: 4 compare_linear_prefix)
    also have "\<dots>=(case finite_term_compare t1 u1 of Linear_Equal \<Rightarrow>
        compare_linear (finite_term_key t2@xs) (finite_term_key u2@ys) | c \<Rightarrow> c)"
      by (rule "4.IH"(1))
    also have "\<dots>=(case finite_term_compare t1 u1 of Linear_Equal \<Rightarrow>
        (case finite_term_compare t2 u2 of Linear_Equal \<Rightarrow> compare_linear xs ys | c \<Rightarrow> c) | c \<Rightarrow> c)"
      by (cases "finite_term_compare t1 u1") (simp_all add: "4.IH"(2))
    finally show ?thesis by (simp add: 4 split: linear_comparison.split)
  qed (simp_all add: finite_term_compare_distinct_tags[simplified] compare_linear_def compare_natural_def)
qed

corollary finite_term_compare_order:
  "finite_term_compare t u=compare_linear (finite_term_key t) (finite_term_key u)"
  using finite_term_compare_keys[of t "[]" u "[]"] by (simp split: linear_comparison.split)

lemma less_eq_ordered_factor_term_structural_code [code]:
  "Ordered_Factor_Term t\<le>Ordered_Factor_Term u \<longleftrightarrow> finite_term_compare t u\<noteq>Linear_Greater"
  by (auto simp: finite_term_compare_order compare_linear_def less_eq_ordered_factor_term_def)

lemma less_ordered_factor_term_structural_code [code]:
  "Ordered_Factor_Term t<Ordered_Factor_Term u \<longleftrightarrow> finite_term_compare t u=Linear_Less"
  by (auto simp: finite_term_compare_order compare_linear_def less_ordered_factor_term_def)

lemma equal_ordered_factor_term_structural_code [code]:
  "HOL.equal (Ordered_Factor_Term t) (Ordered_Factor_Term u) \<longleftrightarrow> finite_term_compare t u=Linear_Equal"
  by (auto simp: finite_term_compare_order compare_linear_def equal_eq finite_term_key_injective)

text \<open>
  The prefix key of a term is prefix-free, so comparing two keys that continue
  with arbitrary further atoms is decided within the first differing subterm.
  The structural comparison therefore returns exactly the order of the complete
  keys: payloads and anchors as addresses, artifacts by their canonical fields,
  and pairs component by component. It stops at the first difference and lists
  the fields of compared artifacts only until they differ. The canonical order,
  every presented collection and every word are unchanged.
\<close>

end
