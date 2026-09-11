theory Conjunction_Investigation
  imports Conjunction_Development Method_Investigation
begin

section \<open>Concatenation exposes another independent decomposition of the same meaning\<close>

definition concatenating_conjunction_rules :: "'a list \<Rightarrow> (nat\<times>'a list) set \<Rightarrow> bool" where
  "concatenating_conjunction_rules q H \<longleftrightarrow>
    (q=[] \<and> H={}) \<or>
    (\<exists>xs ys. q=xs@ys \<and> H={(0,xs),(1,ys)}) \<or>
    (\<exists>xs a. a\<in>set xs \<and> q=[a] \<and> H={(0,xs)})"

theorem concatenating_conjunction_sound:
  "inference_sound (\<lambda>xs. set xs\<subseteq>A) concatenating_conjunction_rules"
  by (auto simp: inference_sound_def concatenating_conjunction_rules_def rel_ran_image)

lemma binary_conjunction_is_a_concatenation:
  "binary_conjunction_rules q H \<Longrightarrow> concatenating_conjunction_rules q H"
proof -
  assume rule: "binary_conjunction_rules q H"
  have empty: "concatenating_conjunction_rules [] {}"
    by (simp add: concatenating_conjunction_rules_def)
  have introduction: "concatenating_conjunction_rules (a#xs) {(0,[a]),(1,xs)}" for a xs
    unfolding concatenating_conjunction_rules_def
    by (rule disjI2, rule disjI1, rule exI[of _ "[a]"], rule exI[of _ xs]) simp
  have projection: "a\<in>set xs \<Longrightarrow> concatenating_conjunction_rules [a] {(0,xs)}" for a xs
    by (auto simp: concatenating_conjunction_rules_def)
  show ?thesis using rule empty introduction projection
    by (auto simp only: binary_conjunction_rules_def)
qed

lemma concatenating_conjunction_local_bound:
  "concatenating_conjunction_rules q H \<Longrightarrow> card H\<le>2"
  by (auto simp: concatenating_conjunction_rules_def)

lemma concatenating_conjunction_collect:
  assumes "\<And>a. a\<in>set xs \<Longrightarrow> [a]\<in>inference_closure concatenating_conjunction_rules K"
  shows "xs\<in>inference_closure concatenating_conjunction_rules K"
  using assms
proof (induction xs)
  case Nil
  show ?case by (rule inference_closure_step[where H="{}"])
    (simp_all add: single_valued_def concatenating_conjunction_rules_def)
next
  case (Cons a xs)
  have head: "[a]\<in>inference_closure concatenating_conjunction_rules K" by (rule Cons.prems) simp
  have tail: "xs\<in>inference_closure concatenating_conjunction_rules K"
    by (rule Cons.IH) (use Cons.prems in auto)
  have rule: "concatenating_conjunction_rules (a#xs) {(0,[a]),(1,xs)}"
    by (rule binary_conjunction_is_a_concatenation) (auto simp: binary_conjunction_rules_def)
  show ?case by (rule inference_closure_step[where H="{(0,[a]),(1,xs)}"])
    (use head tail rule in \<open>auto simp: single_valued_def rel_ran_image\<close>)
qed

lemma concatenating_conjunction_project:
  assumes "xs\<in>inference_closure concatenating_conjunction_rules K" "a\<in>set xs"
  shows "[a]\<in>inference_closure concatenating_conjunction_rules K"
  by (rule inference_closure_step[where H="{(0,xs)}"])
    (use assms in \<open>auto simp: single_valued_def concatenating_conjunction_rules_def rel_ran_def\<close>)

theorem concatenating_conjunction_closure:
  "xs\<in>inference_closure concatenating_conjunction_rules K \<longleftrightarrow>
    set xs\<subseteq>(\<Union>ys\<in>K. set ys)"
  by (rule conjunction_closure_characterization[OF concatenating_conjunction_sound
    concatenating_conjunction_collect concatenating_conjunction_project])

lemma concatenating_conjunction_bounded_closure:
  "inference_closure (bounded_inferences 2 concatenating_conjunction_rules) K=
    inference_closure concatenating_conjunction_rules K"
  by (rule bounded_inferences_complete) (rule concatenating_conjunction_local_bound, assumption)

theorem concatenation_preserves_complete_two_premise_capability:
  "inference_capability 2 concatenating_conjunction_rules=inference_capability 2 binary_conjunction_rules"
  by (auto simp: inference_capability_def concatenating_conjunction_bounded_closure
    binary_conjunction_bounded_closure concatenating_conjunction_closure binary_conjunction_closure)

section \<open>Every finite list has a balanced construction; immediate width remains two\<close>

lemma concatenation_round:
  assumes "xs\<in>inference_rounds concatenating_conjunction_rules K n"
    "ys\<in>inference_rounds concatenating_conjunction_rules K n"
  shows "xs@ys\<in>inference_rounds concatenating_conjunction_rules K (Suc n)"
  by (rule inference_rounds_step[where H="{(0,xs),(1,ys)}"])
    (use assms in \<open>auto simp: single_valued_def concatenating_conjunction_rules_def rel_ran_image\<close>)

lemma empty_conjunction_round:
  "[]\<in>inference_rounds concatenating_conjunction_rules K (Suc n)"
  by (rule inference_rounds_step[where H="{}"])
    (simp_all add: single_valued_def concatenating_conjunction_rules_def)

theorem arbitrary_lists_have_balanced_rounds:
  assumes "length xs\<le>2^n" "\<And>a. a\<in>set xs \<Longrightarrow> [a]\<in>K"
  shows "xs\<in>inference_rounds concatenating_conjunction_rules K (Suc n)"
proof -
  have balanced: "\<forall>xs. length xs\<le>2^n \<longrightarrow>
      (\<forall>a\<in>set xs. [a]\<in>K) \<longrightarrow>
      xs\<in>inference_rounds concatenating_conjunction_rules K (Suc n)" for n
  proof (induction n)
    case 0
    show ?case
    proof (intro allI impI)
      fix xs assume bound: "length xs\<le>2^0" and atoms: "\<forall>a\<in>set xs. [a]\<in>K"
      have empty: "[]\<in>inference_rounds concatenating_conjunction_rules K (Suc 0)"
        by (rule empty_conjunction_round)
      have seeds: "K\<subseteq>inference_rounds concatenating_conjunction_rules K (Suc 0)"
        by (rule inference_rounds_seed)
      show "xs\<in>inference_rounds concatenating_conjunction_rules K (Suc 0)"
        using bound atoms empty seeds by (cases xs) auto
    qed
  next
    case (Suc n)
    show ?case
    proof (intro allI impI)
      fix xs assume bound: "length xs\<le>2^(Suc n)" and atoms: "\<forall>a\<in>set xs. [a]\<in>K"
      let ?xs="take (2^n) xs"
      let ?ys="drop (2^n) xs"
      have first_bound: "length ?xs\<le>2^n" by simp
      have total: "length xs\<le>2^n+2^n" using bound by (simp add: power_Suc mult_2)
      have second_bound: "length ?ys\<le>2^n" using total by (simp only: length_drop; arith)
      have first: "?xs\<in>inference_rounds concatenating_conjunction_rules K (Suc n)"
        using Suc.IH first_bound atoms by (meson set_take_subset subsetD)
      have second: "?ys\<in>inference_rounds concatenating_conjunction_rules K (Suc n)"
        using Suc.IH second_bound atoms by (meson set_drop_subset subsetD)
      show "xs\<in>inference_rounds concatenating_conjunction_rules K (Suc (Suc n))"
        using concatenation_round[OF first second] by simp
    qed
  qed
  show ?thesis using balanced[of n] assms by blast
qed

theorem repeated_conjunction_balanced_rounds:
  "replicate (2^n) a\<in>inference_rounds concatenating_conjunction_rules {[a]} n"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have composed: "replicate (2^n) a@replicate (2^n) a\<in>
      inference_rounds concatenating_conjunction_rules {[a]} (Suc n)"
    by (rule concatenation_round[OF Suc.IH Suc.IH])
  show ?case using composed by (simp add: power_Suc mult_2 replicate_add)
qed

theorem binary_conjunction_round_length:
  assumes "K\<subseteq>{xs. length xs\<le>m}" "1\<le>m"
  shows "inference_rounds binary_conjunction_rules K n\<subseteq>{xs. length xs\<le>m+n}"
  using assms
  by (induction n) (auto simp: inference_consequences_def binary_conjunction_rules_def rel_ran_image)

lemma two_power_exceeds_linear_rounds:
  "2\<le>n \<Longrightarrow> n+1<2^n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n<2")
    case True
    have "n=1" using True Suc.prems by arith
    then show ?thesis by simp
  next
    case False
    have previous: "n+1<2^n" by (rule Suc.IH) (use False in arith)
    show ?thesis using previous by (simp add: power_Suc mult_2; arith)
  qed
qed

theorem arbitrarily_deep_gains_remain_after_width_completeness:
  assumes "2\<le>n"
  shows "replicate (2^n) a\<in>inference_rounds concatenating_conjunction_rules {[a]} n \<and>
    replicate (2^n) a\<notin>inference_rounds binary_conjunction_rules {[a]} n"
proof -
  have bound: "inference_rounds binary_conjunction_rules {[a]} n\<subseteq>{xs. length xs\<le>1+n}"
    by (rule binary_conjunction_round_length) auto
  show ?thesis using repeated_conjunction_balanced_rounds[of n a]
    two_power_exceeds_linear_rounds[OF assms] bound by auto
qed

lemma binary_two_premise_rounds:
  "inference_rounds (bounded_inferences 2 binary_conjunction_rules) K n=
    inference_rounds binary_conjunction_rules K n"
  by (rule bounded_inferences_rounds_complete) (rule binary_conjunction_local_bound, assumption)

lemma concatenating_two_premise_rounds:
  "inference_rounds (bounded_inferences 2 concatenating_conjunction_rules) K n=
    inference_rounds concatenating_conjunction_rules K n"
  by (rule bounded_inferences_rounds_complete) (rule concatenating_conjunction_local_bound, assumption)

theorem concatenating_conjunction_rounds_strict:
  "inference_round_capability 2
      (binary_conjunction_rules :: unit list \<Rightarrow> (nat\<times>unit list) set \<Rightarrow> bool)
    \<subset>inference_round_capability 2 concatenating_conjunction_rules"
proof -
  have stages: "inference_rounds (bounded_inferences 2 binary_conjunction_rules) K n\<subseteq>
      inference_rounds (bounded_inferences 2 concatenating_conjunction_rules) K n" for K n
    by (rule inference_rounds_rule_mono)
      (auto simp: bounded_inferences_def intro: binary_conjunction_is_a_concatenation)
  have included: "inference_round_capability 2 binary_conjunction_rules\<subseteq>
      inference_round_capability 2 concatenating_conjunction_rules"
    using stages by (auto simp: inference_round_capability_def)
  have gained: "(2,{[()]},replicate 4 ())\<in>inference_round_capability 2 concatenating_conjunction_rules"
    using repeated_conjunction_balanced_rounds[of 2 "()"]
    by (simp add: inference_round_capability_def concatenating_two_premise_rounds)
  have missing: "(2,{[()]},replicate 4 ())\<notin>inference_round_capability 2 binary_conjunction_rules"
    using arbitrarily_deep_gains_remain_after_width_completeness[of 2 "()"]
    by (simp add: inference_round_capability_def binary_two_premise_rounds)
  show ?thesis using included gained missing by blast
qed

section \<open>The richer evidence changes the observation method and directs a candidate\<close>

theorem width_only_observations_miss_a_relevant_comparison:
  "(concatenating_conjunction_rules,
      binary_conjunction_rules :: unit list \<Rightarrow> (nat\<times>unit list) set \<Rightarrow> bool)
    \<in>comparison_failures conjunction_methods
      (\<lambda>R S. inference_round_refines (bounded_inferences 2 R) (bounded_inferences 2 S))
      {False} (inference_depth_observations 2)"
proof -
  have first: "concatenating_conjunction_rules\<in>conjunction_methods"
    by (simp add: conjunction_methods_def concatenating_conjunction_sound)
  have second: "binary_conjunction_rules\<in>conjunction_methods"
    by (simp add: conjunction_methods_def binary_conjunction_sound)
  have equal: "candidate_profile {False} (inference_depth_observations 2) concatenating_conjunction_rules=
      candidate_profile {False} (inference_depth_observations 2) binary_conjunction_rules"
    by (auto simp: candidate_profile_def inference_depth_observations_def
      concatenation_preserves_complete_two_premise_capability)
  have different: "\<not>inference_round_refines (bounded_inferences 2 concatenating_conjunction_rules)
      (bounded_inferences 2 (binary_conjunction_rules :: unit list \<Rightarrow> (nat\<times>unit list) set \<Rightarrow> bool))"
    using concatenating_conjunction_rounds_strict by (auto simp: inference_round_capability_comparison[symmetric])
  show ?thesis by (simp add: comparison_failures_def first second equal different)
qed

theorem a_complete_width_method_has_a_named_depth_opportunity:
  defines "R \<equiv> binary_conjunction_rules :: unit list \<Rightarrow> (nat\<times>unit list) set \<Rightarrow> bool"
    and "S \<equiv> concatenating_conjunction_rules"
  shows "complete_candidate conjunction_methods (inference_capability 2) R \<and>
    (S,(True,Inr (2,{[()]},replicate 4 ())))\<in>
      candidate_opportunities conjunction_methods {True} (inference_depth_observations 2) R"
proof -
  have complete: "complete_candidate conjunction_methods (inference_capability 2) R"
    by (simp only: R_def; rule binary_conjunction_complete_candidate)
  have member: "S\<in>conjunction_methods"
    by (simp add: S_def conjunction_methods_def concatenating_conjunction_sound)
  have first: "(2,{[()]},replicate 4 ())\<in>inference_round_capability 2 S"
    using repeated_conjunction_balanced_rounds[of 2 "()"]
    by (simp add: S_def inference_round_capability_def concatenating_two_premise_rounds)
  have second: "(2,{[()]},replicate 4 ())\<notin>inference_round_capability 2 R"
    using arbitrarily_deep_gains_remain_after_width_completeness[of 2 "()"]
    by (simp add: R_def inference_round_capability_def binary_two_premise_rounds)
  show ?thesis using complete member first second
    by (auto simp: candidate_opportunities_def candidate_losses_def inference_depth_observations_def)
qed

text \<open>
  List concatenation is an independently meaningful decomposition. Head-tail
  introduction is one of its specializations. Both methods have the same
  complete conditional conjunction capability with two immediate premises,
  over the original semantics for all predicates and all finite lists.

  Their dependency rounds differ. Every finite list can be assembled through
  balanced splits. Repeated lists of length two to the n use n rounds, while
  the head-tail method starting from singleton facts cannot exceed length
  n plus one at that round. The strict gap persists for every n at least two.
  Equal conditions still occupy the two distinct introduction sockets.

  Thus the earlier infinite-scope completeness theorem remains true for its
  stated observation and still leaves a witnessed useful development. The
  generic failure account identifies the omitted round distinction. The
  same opportunity account identifies the candidate and the exact use to
  preserve. Round observations retain the earlier conditional capability,
  so the richer comparison need not duplicate that information.
\<close>

end
