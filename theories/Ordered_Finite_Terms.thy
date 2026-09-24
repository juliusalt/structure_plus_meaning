theory Ordered_Finite_Terms
  imports Ordered_Complete_Artifacts Prefix_Key_Comparisons
    Factor_Executable_Terms "HOL-Library.Option_ord"
begin

section \<open>Executable terms are ordered by an injective prefix key\<close>

type_synonym finite_term_atom = "nat \<times> ordered_complete_artifact option \<times> octets"

fun finite_term_key :: "finite_factor_term \<Rightarrow> finite_term_atom list" where
  "finite_term_key (Finite_Payload v)=[(0,None,v)]"
| "finite_term_key (Finite_Target (Finite_Whole a))=[(1,Some (Ordered_Complete_Artifact a),[])]"
| "finite_term_key (Finite_Target (Finite_Anchor a r))=[(2,Some (Ordered_Complete_Artifact a),r)]"
| "finite_term_key (Finite_Pair t u)=(3,None,[])#finite_term_key t@finite_term_key u"

text \<open>
  The plain view of a term: its head is the first atom of its key, and a pair's children are its two
  components, left first; a payload or a target has none. The key is a prefix key of this view
  (\<open>Prefix_Key_Comparisons\<close>), so it is prefix-free and injective.
\<close>

fun finite_term_children :: "finite_factor_term \<Rightarrow> finite_factor_term list" where
  "finite_term_children (Finite_Pair t u)=[t,u]"
| "finite_term_children (Finite_Payload v)=[]"
| "finite_term_children (Finite_Target a)=[]"

interpretation finite_term_keys: prefix_key "\<lambda>t. hd (finite_term_key t)" finite_term_children finite_term_key
proof unfold_locales
  fix t u :: finite_factor_term
  show "finite_term_key t=hd (finite_term_key t)#concat (map finite_term_key (finite_term_children t))"
    by (cases t rule: finite_term_key.cases) simp_all
  show "hd (finite_term_key t)=hd (finite_term_key u) \<Longrightarrow>
      length (finite_term_children t)=length (finite_term_children u)"
    by (cases t rule: finite_term_key.cases; cases u rule: finite_term_key.cases) simp_all
  show "hd (finite_term_key t)=hd (finite_term_key u) \<Longrightarrow>
      finite_term_children t=finite_term_children u \<Longrightarrow> t=u"
    by (cases t rule: finite_term_key.cases; cases u rule: finite_term_key.cases) simp_all
qed

lemma finite_term_key_nonempty: "finite_term_key t\<noteq>[]"
  by (rule finite_term_keys.key_nonempty)

lemma finite_term_key_prefix:
  "finite_term_key t@xs=finite_term_key u@ys \<Longrightarrow> t=u \<and> xs=ys"
  by (rule finite_term_keys.key_prefix)

lemma finite_term_key_injective: "finite_term_key t=finite_term_key u \<longleftrightarrow> t=u"
  by (rule finite_term_keys.key_injective)

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
