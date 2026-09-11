theory Obligation_Reductions
  imports Bootstrap_Relations
begin

section \<open>Remaining conditions retain their actual occurrences\<close>

definition remaining_obligations ::
  "'a set \<Rightarrow> ('i \<times> 'a) set \<Rightarrow> ('i \<times> 'a) set" where
  "remaining_obligations K H = {(i,a)\<in>H. a\<notin>K}"

lemma remaining_obligations_member [simp]:
  "(i,a)\<in>remaining_obligations K H \<longleftrightarrow> (i,a)\<in>H \<and> a\<notin>K"
  by (simp add: remaining_obligations_def)

lemma remaining_obligations_values:
  "rel_ran (remaining_obligations K H)=rel_ran H-K"
  by (auto simp: rel_ran_def)

lemma remaining_obligations_empty:
  "remaining_obligations K H={} \<longleftrightarrow> rel_ran H\<subseteq>K"
  by (auto simp: remaining_obligations_def rel_ran_def)

lemma remaining_obligations_finite:
  "finite H \<Longrightarrow> finite (remaining_obligations K H)"
  by (rule finite_subset[of _ H]) (auto simp: remaining_obligations_def)

lemma remaining_obligations_functional:
  "single_valued H \<Longrightarrow> single_valued (remaining_obligations K H)"
  by (auto simp: single_valued_def)

lemma remaining_obligations_accumulate:
  "remaining_obligations L (remaining_obligations K H)=remaining_obligations (K\<union>L) H"
  by (auto simp: remaining_obligations_def)

lemma remaining_obligations_antimono:
  "K\<subseteq>L \<Longrightarrow> remaining_obligations L H\<subseteq>remaining_obligations K H"
  by (auto simp: remaining_obligations_def)

lemma remaining_obligations_rekey:
  "remaining_obligations K (map_prod h id ` H)=
    map_prod h id ` remaining_obligations K H"
  by (auto simp: remaining_obligations_def)

section \<open>Substitution qualifies every new condition by its parent occurrence\<close>

definition obligation_substitution ::
  "('i \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> ('j \<times> 'b) set) \<Rightarrow> (('i \<times> 'j) \<times> 'b) set" where
  "obligation_substitution H F = {((i,j),b). \<exists>a. (i,a)\<in>H \<and> (j,b)\<in>F a}"

lemma obligation_substitution_member [simp]:
  "((i,j),b)\<in>obligation_substitution H F \<longleftrightarrow>
    (\<exists>a. (i,a)\<in>H \<and> (j,b)\<in>F a)"
  by (simp add: obligation_substitution_def)

lemma obligation_substitution_values:
  "rel_ran (obligation_substitution H F)=(\<Union>a\<in>rel_ran H. rel_ran (F a))"
  by (auto simp: rel_ran_def)

lemma obligation_substitution_finite:
  assumes "finite H" "\<And>a. a\<in>rel_ran H \<Longrightarrow> finite (F a)"
  shows "finite (obligation_substitution H F)"
proof -
  have shape: "obligation_substitution H F=
      (\<Union>(i,a)\<in>H. (\<lambda>(j,b). ((i,j),b)) ` F a)"
    by (auto simp: obligation_substitution_def)
  show ?thesis unfolding shape
    by (rule finite_UN_I[OF assms(1)]) (use assms(2) in auto)
qed

lemma obligation_substitution_functional:
  assumes "single_valued H"
    "\<And>a. a\<in>rel_ran H \<Longrightarrow> single_valued (F a)"
  shows "single_valued (obligation_substitution H F)"
  using assms by (auto simp: single_valued_def rel_ran_def; blast)

lemma obligation_substitution_associative:
  "(\<lambda>(((i,j),k),a). ((i,(j,k)),a)) `
      obligation_substitution (obligation_substitution H F) G =
    obligation_substitution H (\<lambda>a. obligation_substitution (F a) G)"
  by (force simp: obligation_substitution_def image_iff split: prod.splits)

lemma substitution_keeps_equal_conditions_separate:
  assumes "i\<noteq>j" "(k,b)\<in>F a"
  shows "((i,k),b)\<in>obligation_substitution {(i,a),(j,a)} F \<and>
    ((j,k),b)\<in>obligation_substitution {(i,a),(j,a)} F \<and> (i,k)\<noteq>(j,k)"
  using assms by auto

section \<open>A reduction relates independently stated requirements and conditions\<close>

definition obligation_reduction ::
  "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> ('i \<times> 'b) set) \<Rightarrow> bool" where
  "obligation_reduction D P Q F \<longleftrightarrow>
    (\<forall>a\<in>D. rel_ran (F a)\<subseteq>{b. Q b} \<longrightarrow> P a)"

definition exact_obligation_reduction ::
  "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> ('i \<times> 'b) set) \<Rightarrow> bool" where
  "exact_obligation_reduction D P Q F \<longleftrightarrow>
    (\<forall>a\<in>D. P a \<longleftrightarrow> rel_ran (F a)\<subseteq>{b. Q b})"

lemma exact_obligation_reduction_sound:
  "exact_obligation_reduction D P Q F \<Longrightarrow> obligation_reduction D P Q F"
  by (auto simp: exact_obligation_reduction_def obligation_reduction_def)

lemma obligation_reduction_discharge:
  assumes "obligation_reduction D P Q F" "a\<in>D"
    "\<And>i b. (i,b)\<in>F a \<Longrightarrow> Q b"
  shows "P a"
  using assms by (auto simp: obligation_reduction_def rel_ran_def)

theorem obligation_reduction_specialization:
  assumes "obligation_reduction D P Q F" "f ` E\<subseteq>D"
  shows "obligation_reduction E (P\<circ>f) Q (F\<circ>f)"
  using assms by (auto simp: obligation_reduction_def)

theorem exact_obligation_reduction_specialization:
  assumes "exact_obligation_reduction D P Q F" "f ` E\<subseteq>D"
  shows "exact_obligation_reduction E (P\<circ>f) Q (F\<circ>f)"
  using assms by (auto simp: exact_obligation_reduction_def)

theorem obligation_reduction_compose:
  assumes first: "obligation_reduction D P Q F"
    and second: "obligation_reduction E Q T G"
    and boundary: "\<And>a. a\<in>D \<Longrightarrow> rel_ran (F a)\<subseteq>E"
  shows "obligation_reduction D P T (\<lambda>a. obligation_substitution (F a) G)"
  using assms
  by (auto simp: obligation_reduction_def obligation_substitution_values; blast)

theorem exact_obligation_reduction_compose:
  assumes first: "exact_obligation_reduction D P Q F"
    and second: "exact_obligation_reduction E Q T G"
    and boundary: "\<And>a. a\<in>D \<Longrightarrow> rel_ran (F a)\<subseteq>E"
  shows "exact_obligation_reduction D P T (\<lambda>a. obligation_substitution (F a) G)"
  using assms
  by (auto simp: exact_obligation_reduction_def obligation_substitution_values; blast)

theorem obligation_reduction_residual:
  assumes "obligation_reduction D P Q F" "K\<subseteq>{b. Q b}"
  shows "obligation_reduction D P Q (\<lambda>a. remaining_obligations K (F a))"
  using assms
  by (auto simp: obligation_reduction_def remaining_obligations_values; blast)

theorem exact_obligation_reduction_residual:
  assumes "exact_obligation_reduction D P Q F" "K\<subseteq>{b. Q b}"
  shows "exact_obligation_reduction D P Q (\<lambda>a. remaining_obligations K (F a))"
  using assms
  by (auto simp: exact_obligation_reduction_def remaining_obligations_values; blast)

theorem reduced_requirement_complete:
  assumes "obligation_reduction D P Q F" "a\<in>D" "K\<subseteq>{b. Q b}"
    "remaining_obligations K (F a)={}"
  shows "P a"
  using assms
  by (auto simp: obligation_reduction_def remaining_obligations_empty)

theorem a_sufficient_reduction_need_not_be_exact:
  "obligation_reduction UNIV (\<lambda>_::unit. True) id (\<lambda>_. {((),False)}) \<and>
    \<not>exact_obligation_reduction UNIV (\<lambda>_::unit. True) id (\<lambda>_. {((),False)})"
  by (auto simp: obligation_reduction_def exact_obligation_reduction_def rel_ran_def subset_iff)

text \<open>
  An obligation is a condition at an identified occurrence. Its truth and the
  requirement it may establish are specified before the reduction. Substitution
  retains both parent and child occurrences; equal conditions at different
  places do not merge. Sound reductions give sufficient conditions. Exact
  reductions additionally reflect the requirement and support counterexamples.

  The general family may be infinite, as when one theorem covers every instance
  of a rule schema. Finite supplied accounts separately prove finiteness and
  functionality. A quantified family is not an executable finite enumeration.
  Specialization requires actual domain coverage; residual removal requires
  established conditions. Neither operation changes the original requirement.
\<close>

end
