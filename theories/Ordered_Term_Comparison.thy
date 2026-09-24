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

text \<open>
  The structural comparison is the prefix-key comparison of the plain view
  (\<open>Prefix_Key_Comparisons\<close>): its one-level equation holds by cases on both terms, and the
  notion gives its order, its equality and the code equations.
\<close>

lemma finite_term_compare_node:
  "finite_term_compare t u=(case compare_linear (hd (finite_term_key t)) (hd (finite_term_key u)) of
      Linear_Equal \<Rightarrow> compare_listed finite_term_compare (finite_term_children t) (finite_term_children u)
    | c \<Rightarrow> c)"
  by (cases t rule: finite_term_key.cases; cases u rule: finite_term_key.cases)
    (simp_all add: compare_linear_pair compare_linear_option compare_linear_ordered_artifact
      compare_address_linear compare_natural_linear compare_linear_cases split: linear_comparison.split)

interpretation finite_term_comparison: prefix_key_comparison "\<lambda>t. hd (finite_term_key t)"
  finite_term_children finite_term_key finite_term_compare
  by (intro_locales; ((rule finite_term_keys.prefix_key_axioms prefix_key_comparison_axioms.intro
    finite_term_compare_node finite_term_keys.key_node finite_term_keys.head_arity
    finite_term_keys.node_determined) | assumption)+)

theorem finite_term_compare_keys:
  "compare_linear (finite_term_key t@xs) (finite_term_key u@ys)=
    (case finite_term_compare t u of Linear_Equal \<Rightarrow> compare_linear xs ys | c \<Rightarrow> c)"
  by (rule finite_term_comparison.compare_keys)

corollary finite_term_compare_order:
  "finite_term_compare t u=compare_linear (finite_term_key t) (finite_term_key u)"
  by (rule finite_term_comparison.compare_order)

lemma less_eq_ordered_factor_term_structural_code [code]:
  "Ordered_Factor_Term t\<le>Ordered_Factor_Term u \<longleftrightarrow> finite_term_compare t u\<noteq>Linear_Greater"
  by (simp only: less_eq_ordered_factor_term_def ordered_factor_term_key.simps
    finite_term_comparison.key_less_eq)

lemma less_ordered_factor_term_structural_code [code]:
  "Ordered_Factor_Term t<Ordered_Factor_Term u \<longleftrightarrow> finite_term_compare t u=Linear_Less"
  by (simp only: less_ordered_factor_term_def ordered_factor_term_key.simps finite_term_comparison.key_less)

lemma equal_ordered_factor_term_structural_code [code]:
  "HOL.equal (Ordered_Factor_Term t) (Ordered_Factor_Term u) \<longleftrightarrow> finite_term_compare t u=Linear_Equal"
  by (simp only: equal_eq ordered_factor_term.inject finite_term_comparison.compare_equal)

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
