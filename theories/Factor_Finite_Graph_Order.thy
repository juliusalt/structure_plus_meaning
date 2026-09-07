theory Factor_Finite_Graph_Order
  imports Bootstrap_Finite_Closure
begin

section \<open>A finite list witnesses descent without assigning ranks to nodes\<close>

fun children_follow :: "('a\<times>'a) set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "children_follow R [] \<longleftrightarrow> True"
| "children_follow R (x#xs) \<longleftrightarrow>
    x\<notin>set xs \<and> (\<forall>y. (y,x)\<in>R \<longrightarrow> y\<in>set xs) \<and> children_follow R xs"

lemma children_follow_distinct:
  "children_follow R xs \<Longrightarrow> distinct xs"
  by (induction xs) auto

lemma children_follow_closed:
  assumes order: "children_follow R xs" and parent: "x\<in>set xs" and edge: "(y,x)\<in>R"
  shows "y\<in>set xs"
  using order parent by (induction xs) (use edge in auto)

lemma children_follow_cong:
  assumes same: "\<And>x y. x\<in>set xs \<Longrightarrow> (y,x)\<in>R \<longleftrightarrow> (y,x)\<in>S"
  shows "children_follow R xs \<longleftrightarrow> children_follow S xs"
  using same by (induction xs) auto

lemma children_follow_wellfounded:
  assumes order: "children_follow R xs"
  shows "wf (R \<inter> (set xs\<times>set xs))"
  using order
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have fresh: "x\<notin>set xs" and tail: "children_follow R xs" using Cons.prems by auto
  have old: "wf (R \<inter> (set xs\<times>set xs))" by (rule Cons.IH[OF tail])
  have new_subset: "set xs\<times>{x} \<subseteq> measure (\<lambda>y. if y=x then 1 else 0)"
    using fresh by auto
  have new: "wf (set xs\<times>{x})" by (rule wf_subset[OF wf_measure new_subset])
  have separated: "Domain (R \<inter> (set xs\<times>set xs)) \<inter> Range (set xs\<times>{x})={}"
    using fresh by auto
  have union: "wf ((R \<inter> (set xs\<times>set xs)) \<union> (set xs\<times>{x}))"
    by (rule wf_Un[OF old new separated])
  have subset: "R \<inter> (set (x#xs)\<times>set (x#xs)) \<subseteq>
    (R \<inter> (set xs\<times>set xs)) \<union> (set xs\<times>{x})"
    using children_follow_closed[OF tail] fresh Cons.prems by auto
  show ?case by (rule wf_subset[OF union subset])
qed

theorem finite_closed_graph_order:
  assumes finite: "finite A"
    and closed: "\<And>x y. x\<in>A \<Longrightarrow> (y,x)\<in>R \<Longrightarrow> y\<in>A"
    and descent: "wf (R \<inter> (A\<times>A))"
  shows "\<exists>xs. set xs=A \<and> children_follow R xs"
  using finite closed descent
proof (induction A rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "A={}")
    case True
    then show ?thesis by (rule_tac x="[]" in exI) simp
  next
    case False
    have finite_edges: "finite (R \<inter> (A\<times>A))"
      by (rule finite_subset[of _ "A\<times>A"]) (use psubset.hyps in auto)
    have reverse: "wf ((R \<inter> (A\<times>A))\<inverse>)"
      by (rule finite_acyclic_wf_converse[OF finite_edges wf_acyclic[OF psubset.prems(2)]])
    obtain x where member: "x\<in>A" and maximal:
      "\<And>y. (y,x)\<in>(R \<inter> (A\<times>A))\<inverse> \<Longrightarrow> y\<notin>A"
      by (rule wfE_min'[OF reverse False]) (rule that; assumption)
    let ?B="A-{x}"
    have smaller: "?B \<subset> A" using member by blast
    have closed_tail: "y\<in>?B" if parent: "z\<in>?B" and edge: "(y,z)\<in>R" for y z
    proof -
      have inside: "y\<in>A" by (rule psubset.prems(1)[OF _ edge]) (use parent in auto)
      have other: "y\<noteq>x" using maximal[of z] parent edge member by auto
      show ?thesis using inside other by simp
    qed
    have tail_wf: "wf (R \<inter> (?B\<times>?B))"
      by (rule wf_subset[OF psubset.prems(2)]) auto
    have ordered_tail: "\<exists>xs. set xs=?B \<and> children_follow R xs"
    proof (rule psubset.IH[OF smaller])
      fix z y assume parent: "z\<in>?B" and edge: "(y,z)\<in>R"
      show "y\<in>?B" by (rule closed_tail[OF parent edge])
    next
      show "wf (R \<inter> (?B\<times>?B))" by (rule tail_wf)
    qed
    obtain xs where tail: "set xs=?B" "children_follow R xs" using ordered_tail by blast
    have children: "\<forall>y. (y,x)\<in>R \<longrightarrow> y\<in>set xs"
    proof (intro allI impI)
      fix y assume edge: "(y,x)\<in>R"
      have inside: "y\<in>A" by (rule psubset.prems(1)[OF member edge])
      have other: "y\<noteq>x" using maximal[of x] member edge by auto
      show "y\<in>set xs" using inside other tail(1) by simp
    qed
    show ?thesis by (rule exI[of _ "x#xs"]) (use member tail children in auto)
  qed
qed

section \<open>Restricting to exactly the predecessors of a root\<close>

lemma root_predecessors_least:
  assumes root: "root\<in>A" and closed: "\<And>x y. x\<in>A \<Longrightarrow> (y,x)\<in>R \<Longrightarrow> y\<in>A"
  shows "{x. (x,root)\<in>R\<^sup>*}\<subseteq>A"
proof -
  have path: "(x,y)\<in>R\<^sup>* \<Longrightarrow> y\<in>A \<longrightarrow> x\<in>A" for x y
    by (induction rule: rtrancl_induct) (use closed in blast)+
  show ?thesis using path root by blast
qed

lemma root_predecessors_closed:
  assumes parent: "(x,root)\<in>R\<^sup>*" and edge: "(y,x)\<in>R"
  shows "(y,root)\<in>R\<^sup>*"
  by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] parent])

lemma root_predecessors_path:
  assumes path: "(x,root)\<in>R\<^sup>*"
  shows "(x,root)\<in>(R \<inter> ({y. (y,root)\<in>R\<^sup>*}\<times>{y. (y,root)\<in>R\<^sup>*}))\<^sup>*"
  using path
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step x y)
  have inside: "(x,root)\<in>R\<^sup>*"
    by (rule root_predecessors_closed[OF step.hyps(2) step.hyps(1)])
  have edge: "(x,y)\<in>R \<inter> ({z. (z,root)\<in>R\<^sup>*}\<times>{z. (z,root)\<in>R\<^sup>*})"
    using step.hyps inside by auto
  show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] step.IH])
qed

text \<open>
  The list order is only an existential witness. Every child lies in its
  parent's strict tail, while different parents may refer to the same child.
  Every finite closed acyclic relation has such a list. Restriction to the
  root's actual predecessor closure retains every edge at each retained
  parent and excludes unrelated nodes.
\<close>

end
