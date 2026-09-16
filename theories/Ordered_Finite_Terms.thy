theory Ordered_Finite_Terms
  imports Ordered_Complete_Artifacts
    Factor_Executable_Terms "HOL-Library.Option_ord"
begin

section \<open>Executable terms are ordered by an injective prefix key\<close>

type_synonym finite_term_atom = "nat \<times> ordered_complete_artifact option \<times> octets"

fun finite_term_key :: "finite_factor_term \<Rightarrow> finite_term_atom list" where
  "finite_term_key (Finite_Payload v)=[(0,None,v)]"
| "finite_term_key (Finite_Target (Finite_Whole a))=[(1,Some (Ordered_Complete_Artifact a),[])]"
| "finite_term_key (Finite_Target (Finite_Anchor a r))=[(2,Some (Ordered_Complete_Artifact a),r)]"
| "finite_term_key (Finite_Pair t u)=(3,None,[])#finite_term_key t@finite_term_key u"

lemma finite_term_key_nonempty: "finite_term_key t\<noteq>[]"
  by (cases t rule: finite_term_key.cases) simp_all

lemma finite_term_key_prefix:
  "finite_term_key t@xs=finite_term_key u@ys \<Longrightarrow> t=u \<and> xs=ys"
proof (induction t arbitrary: u xs ys rule: finite_term_key.induct)
  case (1 v)
  then show ?case by (cases u rule: finite_term_key.cases) auto
next
  case (2 a)
  then show ?case by (cases u rule: finite_term_key.cases) auto
next
  case (3 a r)
  then show ?case by (cases u rule: finite_term_key.cases) auto
next
  case (4 t1 t2)
  show ?case
  proof (cases u rule: finite_term_key.cases)
    case (4 u1 u2)
    have tail: "finite_term_key t1@(finite_term_key t2@xs)=finite_term_key u1@(finite_term_key u2@ys)"
      using "4.prems" by (simp add: 4)
    have first: "t1=u1" and rest: "finite_term_key t2@xs=finite_term_key u2@ys"
      using "4.IH"(1)[OF tail] by simp_all
    have second: "t2=u2" and final: "xs=ys" using "4.IH"(2)[OF rest] by simp_all
    show ?thesis using first second final by (simp add: 4)
  qed (use "4.prems" in auto)
qed

lemma finite_term_key_injective: "finite_term_key t=finite_term_key u \<longleftrightarrow> t=u"
  using finite_term_key_prefix[of t "[]" u "[]"] by auto

datatype ordered_factor_term = Ordered_Factor_Term finite_factor_term

fun ordered_factor_term_key where
  "ordered_factor_term_key (Ordered_Factor_Term t)=finite_term_key t"

fun unordered_factor_term where
  "unordered_factor_term (Ordered_Factor_Term t)=t"

lemma ordered_factor_term_key_injective:
  "ordered_factor_term_key x=ordered_factor_term_key y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: finite_term_key_injective)

instantiation ordered_factor_term :: linorder
begin

definition "x\<le>y \<longleftrightarrow> ordered_factor_term_key x\<le>ordered_factor_term_key y"
definition "x<y \<longleftrightarrow> ordered_factor_term_key x<ordered_factor_term_key y"

instance
  by standard
    (auto simp: less_eq_ordered_factor_term_def less_ordered_factor_term_def
      less_le_not_le ordered_factor_term_key_injective
      intro: order_trans dest: order_antisym)

end

export_code Ordered_Factor_Term unordered_factor_term "(\<le>) :: ordered_factor_term \<Rightarrow> _"
  checking SML

text \<open>The wrapper retains the complete term. Its order compares a prefix key
  whose atoms are payloads, ordered complete artifacts with their anchors, and
  pair markers; the key determines the term, so the order is linear.\<close>

end
