theory Presentation_Closure
  imports Presentation_Relations
begin

section \<open>Presentation of every member of a subject family\<close>

definition presented_set ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'p set" where
  "presented_set presents X = {p. \<exists>a\<in>X. presents a p}"

lemma presented_set_mono:
  assumes "X\<subseteq>Y"
  shows "presented_set R X\<subseteq>presented_set R Y"
  using assms by (auto simp: presented_set_def)

lemma presented_set_empty [simp]: "presented_set R {}={}"
  by (simp add: presented_set_def)

lemma presented_set_union:
  "presented_set R (\<Union>Xs) = (\<Union>X\<in>Xs. presented_set R X)"
  by (auto simp: presented_set_def)

context presentation_class
begin

theorem set_recovery:
  assumes "X\<subseteq>{a. subject a}" "Y\<subseteq>{a. subject a}"
  shows "presented_set presents X=presented_set presents Y \<longleftrightarrow> X=Y"
proof
  assume same: "presented_set presents X=presented_set presents Y"
  show "X=Y"
  proof (rule set_eqI)
    fix a
    have forward: "a\<in>Y" if member: "a\<in>X"
    proof -
      have domain: "subject a" using assms(1) member by blast
      obtain p where read: "presents a p" using total[OF domain] by blast
      have "p\<in>presented_set presents Y" using same member read by (auto simp: presented_set_def)
      then show ?thesis using read recovery by (auto simp: presented_set_def; blast)
    qed
    have backward: "a\<in>X" if member: "a\<in>Y"
    proof -
      have domain: "subject a" using assms(2) member by blast
      obtain p where read: "presents a p" using total[OF domain] by blast
      have "p\<in>presented_set presents X" using same member read by (auto simp: presented_set_def)
      then show ?thesis using read recovery by (auto simp: presented_set_def; blast)
    qed
    show "a\<in>X \<longleftrightarrow> a\<in>Y" using forward backward by blast
  qed
next
  assume "X=Y"
  then show "presented_set presents X=presented_set presents Y" by simp
qed

end

section \<open>Exact consequence transport gives exact least fixed points\<close>

theorem presented_least_fixed_point_on:
  fixes F :: "'a set \<Rightarrow> 'a set" and G :: "'p set \<Rightarrow> 'p set"
  assumes semantic_mono: "mono F" and presentation_mono: "mono G"
    and boundary: "\<And>X. X\<subseteq>D \<Longrightarrow> F X\<subseteq>D"
    and step: "\<And>X. X\<subseteq>D \<Longrightarrow> G (presented_set R X)=presented_set R (F X)"
  shows "lfp G=presented_set R (lfp F)"
proof (rule equalityI)
  have bounded: "lfp F\<subseteq>D"
    by (rule lfp_lowerbound, rule boundary) (rule subset_refl)
  have fixed: "G (presented_set R (lfp F))=presented_set R (lfp F)"
    by (simp only: step[OF bounded] lfp_unfold[OF semantic_mono, symmetric])
  show "lfp G\<subseteq>presented_set R (lfp F)"
    by (rule lfp_lowerbound) (use fixed in simp)
next
  let ?safe="{a\<in>D. \<forall>p. R a p \<longrightarrow> p\<in>lfp G}"
  have bounded: "?safe\<subseteq>D" by blast
  have supported: "presented_set R ?safe\<subseteq>lfp G"
    by (auto simp: presented_set_def)
  have consequences: "G (presented_set R ?safe)\<subseteq>lfp G"
    using monoD[OF presentation_mono supported]
    by (simp only: lfp_unfold[OF presentation_mono, symmetric])
  have image_closed: "presented_set R (F ?safe)\<subseteq>lfp G"
    using consequences by (simp only: step[OF bounded])
  have closed: "F ?safe\<subseteq>?safe"
    using image_closed boundary[OF bounded]
    by (auto simp: presented_set_def)
  have least: "lfp F\<subseteq>?safe" by (rule lfp_lowerbound) (rule closed)
  show "presented_set R (lfp F)\<subseteq>lfp G"
    using least by (auto simp: presented_set_def)
qed

corollary presented_least_fixed_point:
  fixes F :: "'a set \<Rightarrow> 'a set" and G :: "'p set \<Rightarrow> 'p set"
  assumes semantic_mono: "mono F" and presentation_mono: "mono G"
    and step: "\<And>X. G (presented_set R X)=presented_set R (F X)"
  shows "lfp G=presented_set R (lfp F)"
  by (rule presented_least_fixed_point_on[where D=UNIV, OF semantic_mono presentation_mono])
    (use step in auto)

text \<open>
  A recursive presentation is justified at the consequence operators before
  taking their least fixed points. The hypothesis compares every presented
  support family in a proved closed domain, so it covers recursive calls and
  shared witnesses. Separately described completed meanings do not supply
  the required consequence equation.

  This theorem is a proof rule. It inserts no predicate into a native semantic
  operator. A concrete recursive reader must establish the consequence equation
  for its actual clauses. Class totality and recovery separately determine
  whether the lifted family covers and distinguishes all required subjects.
\<close>

end
