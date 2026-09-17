theory Linear_Comparisons
  imports "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

section \<open>A linear comparison has three outcomes\<close>

datatype linear_comparison = Linear_Less | Linear_Equal | Linear_Greater

definition compare_linear :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> linear_comparison" where
  "compare_linear x y=(if x<y then Linear_Less else if x=y then Linear_Equal else Linear_Greater)"

lemma compare_linear_cases:
  "compare_linear x y=Linear_Less \<longleftrightarrow> x<y"
  "compare_linear x y=Linear_Equal \<longleftrightarrow> x=y"
  "compare_linear x y=Linear_Greater \<longleftrightarrow> y<x"
  by (auto simp: compare_linear_def)

lemma compare_linear_order:
  "x\<le>y \<longleftrightarrow> compare_linear x y\<noteq>Linear_Greater"
  "x<y \<longleftrightarrow> compare_linear x y=Linear_Less"
  by (auto simp: compare_linear_def)

lemma compare_linear_same [simp]: "compare_linear x x=Linear_Equal"
  by (simp add: compare_linear_def)

lemma compare_linear_prefix:
  "compare_linear (x#xs) (y#ys)=(case compare_linear x y of Linear_Equal \<Rightarrow> compare_linear xs ys | c \<Rightarrow> c)"
  by (cases x y rule: linorder_cases) (auto simp: compare_linear_def)

lemma compare_linear_ends:
  "compare_linear ([]::'a::linorder list) []=Linear_Equal"
  "compare_linear [] (y#ys)=Linear_Less"
  "compare_linear (x#xs) []=Linear_Greater"
  by (simp_all add: compare_linear_def)

lemma compare_linear_pair:
  "compare_linear (a,b) (c,d)=(case compare_linear a c of Linear_Equal \<Rightarrow> compare_linear b d | r \<Rightarrow> r)"
  by (cases a c rule: linorder_cases) (auto simp: compare_linear_def)

section \<open>Comparisons compose through listings and pairs\<close>

fun compare_listed :: "('a \<Rightarrow> 'a \<Rightarrow> linear_comparison) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> linear_comparison" where
  "compare_listed c [] []=Linear_Equal"
| "compare_listed c [] (y#ys)=Linear_Less"
| "compare_listed c (x#xs) []=Linear_Greater"
| "compare_listed c (x#xs) (y#ys)=(case c x y of Linear_Equal \<Rightarrow> compare_listed c xs ys | r \<Rightarrow> r)"

lemma compare_listed_linear:
  assumes same: "\<And>x y. c x y=compare_linear x y"
  shows "compare_listed c xs ys=compare_linear xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by (cases ys) (simp_all only: compare_listed.simps compare_linear_ends)
next
  case (Cons x xs)
  note previous=Cons.IH
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis by (simp only: compare_listed.simps compare_linear_ends)
  next
    case (Cons y zs)
    have head: "c x y=compare_linear x y" by (rule same)
    show ?thesis
      by (simp only: \<open>ys=y#zs\<close> compare_listed.simps compare_linear_prefix head previous)
  qed
qed

definition compare_paired ::
  "('a \<Rightarrow> 'a \<Rightarrow> linear_comparison) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> linear_comparison) \<Rightarrow> 'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> linear_comparison" where
  "compare_paired c d p q=(case c (fst p) (fst q) of Linear_Equal \<Rightarrow> d (snd p) (snd q) | r \<Rightarrow> r)"

lemma compare_paired_linear:
  assumes "\<And>x y. c x y=compare_linear x y" and "\<And>x y. d x y=compare_linear x y"
  shows "compare_paired c d p q=compare_linear p q"
  by (cases p; cases q) (simp only: compare_paired_def compare_linear_pair assms fst_conv snd_conv)

definition compare_natural :: "nat \<Rightarrow> nat \<Rightarrow> linear_comparison" where
  "compare_natural m n=(if m<n then Linear_Less else if n<m then Linear_Greater else Linear_Equal)"

lemma compare_natural_linear: "compare_natural m n=compare_linear m n"
  by (auto simp: compare_natural_def compare_linear_def)

definition compare_address :: "nat list \<Rightarrow> nat list \<Rightarrow> linear_comparison" where
  "compare_address=compare_listed compare_natural"

lemma compare_address_linear: "compare_address xs ys=compare_linear xs ys"
  by (simp only: compare_address_def compare_listed_linear compare_natural_linear)

text \<open>
  A comparison returns whether its first value is less than, equal to or greater
  than its second under the existing linear order. Listings compare
  lexicographically and pairs by their first and then their second component, so
  one pass decides each composite comparison and stops at the first difference.
  Each composite comparison equals the existing lexicographic comparison of its
  complete values; no order, value or outcome changes.
\<close>

end
