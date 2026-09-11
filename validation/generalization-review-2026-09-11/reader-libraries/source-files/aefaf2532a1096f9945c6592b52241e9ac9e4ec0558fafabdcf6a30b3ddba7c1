theory Method_Investigation
  imports Candidate_Investigation Inference_Rounds Method_Development
begin

section \<open>Observation selection is itself a method candidate\<close>

definition observation_discriminations where
  "observation_discriminations C F observe=
    {(c,d). c\<in>C \<and> d\<in>C \<and>
      \<not>candidate_profile F observe c\<subseteq>candidate_profile F observe d}"

lemma observation_discriminations_mono:
  assumes "F\<subseteq>G"
  shows "observation_discriminations C F observe\<subseteq>observation_discriminations C G observe"
  using assms by (auto simp: observation_discriminations_def candidate_profile_comparison; blast)

theorem basis_selection_uses_the_same_candidate_comparison:
  assumes whole: "comparison_basis C relation U observe" and included: "F\<subseteq>U"
  shows "comparison_basis C relation F observe \<longleftrightarrow>
    complete_candidate (Pow U) (\<lambda>G. observation_discriminations C G observe) F"
proof -
  have characterized: "comparison_basis C relation F observe \<longleftrightarrow>
      observation_discriminations C F observe=observation_discriminations C U observe"
  proof
    assume part: "comparison_basis C relation F observe"
    have scalar: "candidate_profile F observe c\<subseteq>candidate_profile F observe d \<longleftrightarrow>
        candidate_profile U observe c\<subseteq>candidate_profile U observe d"
      if "c\<in>C" "d\<in>C" for c d
      using comparison_basis_at[OF part that] comparison_basis_at[OF whole that] by blast
    show "observation_discriminations C F observe=observation_discriminations C U observe"
      using scalar by (auto simp: observation_discriminations_def)
  next
    assume same: "observation_discriminations C F observe=observation_discriminations C U observe"
    show "comparison_basis C relation F observe"
      unfolding comparison_basis_def
    proof (intro ballI)
      fix c d assume first: "c\<in>C" and second: "d\<in>C"
      have membership: "(c,d)\<in>observation_discriminations C F observe \<longleftrightarrow>
          (c,d)\<in>observation_discriminations C U observe"
        by (simp only: same)
      have scalar: "candidate_profile F observe c\<subseteq>candidate_profile F observe d \<longleftrightarrow>
          candidate_profile U observe c\<subseteq>candidate_profile U observe d"
        using membership first second by (simp add: observation_discriminations_def)
      show "relation c d \<longleftrightarrow> candidate_profile F observe c\<subseteq>candidate_profile F observe d"
        using comparison_basis_at[OF whole first second] scalar by blast
    qed
  qed
  have covered: "complete_candidate (Pow U) (\<lambda>G. observation_discriminations C G observe) F \<longleftrightarrow>
      observation_discriminations C F observe=observation_discriminations C U observe"
  proof
    assume complete: "complete_candidate (Pow U) (\<lambda>G. observation_discriminations C G observe) F"
    have upper: "observation_discriminations C U observe\<subseteq>observation_discriminations C F observe"
      using complete by (simp add: complete_candidate_def)
    show "observation_discriminations C F observe=observation_discriminations C U observe"
      by (rule subset_antisym[OF observation_discriminations_mono[OF included] upper])
  next
    assume same: "observation_discriminations C F observe=observation_discriminations C U observe"
    have every: "observation_discriminations C G observe\<subseteq>observation_discriminations C F observe"
      if "G\<in>Pow U" for G
    proof -
      have subset: "G\<subseteq>U" using that by simp
      show ?thesis by (simp only: same; rule observation_discriminations_mono[OF subset])
    qed
    show "complete_candidate (Pow U) (\<lambda>G. observation_discriminations C G observe) F"
      using included every by (simp add: complete_candidate_def)
  qed
  show ?thesis by (simp only: characterized covered)
qed

definition basis_obligations where
  "basis_obligations C F=graph_map (C\<times>C) (\<lambda>z. (F,z))"

definition basis_condition where
  "basis_condition relation observe z \<longleftrightarrow>
    (relation (fst (snd z)) (snd (snd z)) \<longleftrightarrow>
      candidate_profile (fst z) observe (fst (snd z))\<subseteq>
        candidate_profile (fst z) observe (snd (snd z)))"

theorem observation_method_evaluation_reduction:
  "exact_obligation_reduction UNIV (\<lambda>F. comparison_basis C relation F observe)
    (basis_condition relation observe) (basis_obligations C)"
  by (auto simp: exact_obligation_reduction_def comparison_basis_def
    basis_obligations_def graph_map_ran image_subset_iff basis_condition_def)

theorem observation_method_failure_residual:
  assumes "comparison_observations_sound C relation F observe"
  shows "remaining_obligations {z. basis_condition relation observe z} (basis_obligations C F)=
    graph_map (comparison_failures C relation F observe) (\<lambda>z. (F,z))"
  using assms by (auto simp: remaining_obligations_def basis_obligations_def
    basis_condition_def graph_map_def comparison_failures_def comparison_observations_sound_def
    candidate_profile_comparison; blast)

theorem guided_observation_method_assessment:
  assumes sound: "inference_sound (basis_condition relation observe) R"
    and known: "K\<subseteq>{z. basis_condition relation observe z}"
    and settled: "remaining_obligations
      (inference_closure (guided_inferences R K (rel_ran (basis_obligations C F))) K)
      (basis_obligations C F)={}"
  shows "comparison_basis C relation F observe"
proof -
  have residual: "remaining_obligations (inference_closure R K) (basis_obligations C F)={}"
    using settled by (simp only: guided_goal_residual_exact[OF subset_refl])
  show ?thesis
    by (rule reduced_requirement_complete[OF
      exact_obligation_reduction_sound[OF observation_method_evaluation_reduction]
      UNIV_I inference_closure_sound[OF sound known] residual])
qed

theorem a_missing_facet_improves_the_observation_method:
  assumes whole: "comparison_basis C relation U observe" and included: "F\<subseteq>U"
    and failure: "(c,d)\<in>comparison_failures C relation F observe"
  shows "\<exists>f\<in>U-F. observation_discriminations C F observe\<subset>
    observation_discriminations C (insert f F) observe"
proof -
  obtain f w where outside: "f\<in>U-F" and first: "w\<in>observe f c" and second: "w\<notin>observe f d"
    using omitted_facet_has_a_witness[OF whole included failure] by blast
  have grows: "observation_discriminations C F observe\<subseteq>
      observation_discriminations C (insert f F) observe"
    by (rule observation_discriminations_mono[OF subset_insertI])
  have old: "(c,d)\<notin>observation_discriminations C F observe"
    using failure by (auto simp: comparison_failures_def observation_discriminations_def)
  have fresh: "(c,d)\<in>observation_discriminations C (insert f F) observe"
    using failure first second by (auto simp: comparison_failures_def observation_discriminations_def
      candidate_profile_comparison)
  show ?thesis by (rule bexI[of _ f]) (use outside grows old fresh in blast)+
qed

section \<open>A covering method names the representative for every alternative\<close>

definition frontier_covering where
  "frontier_covering C ability frontier h \<longleftrightarrow>
    frontier\<subseteq>C \<and> (\<forall>c\<in>C. h c\<in>frontier \<and> ability c\<subseteq>ability (h c))"

theorem candidate_cover_has_a_covering_method:
  "candidate_cover C ability frontier \<longleftrightarrow> (\<exists>h. frontier_covering C ability frontier h)"
proof
  assume cover: "candidate_cover C ability frontier"
  let ?h="\<lambda>c. SOME d. d\<in>frontier \<and> ability c\<subseteq>ability d"
  have selected: "?h c\<in>frontier \<and> ability c\<subseteq>ability (?h c)" if "c\<in>C" for c
    by (rule someI_ex) (use cover that in \<open>auto simp: candidate_cover_def\<close>)
  show "\<exists>h. frontier_covering C ability frontier h"
    by (rule exI[of _ ?h]) (use cover selected in \<open>simp add: frontier_covering_def candidate_cover_def\<close>)
next
  assume "\<exists>h. frontier_covering C ability frontier h"
  then show "candidate_cover C ability frontier"
    by (auto simp: frontier_covering_def candidate_cover_def)
qed

definition covering_obligations where
  "covering_obligations C frontier h=graph_map C (\<lambda>c. (frontier,c,h c))"

definition covering_condition where
  "covering_condition ability z \<longleftrightarrow>
    snd (snd z)\<in>fst z \<and> ability (fst (snd z))\<subseteq>ability (snd (snd z))"

theorem covering_method_evaluation_reduction:
  assumes boundary: "frontier\<subseteq>C"
  shows "exact_obligation_reduction UNIV (frontier_covering C ability frontier)
    (covering_condition ability) (covering_obligations C frontier)"
  using boundary by (auto simp: exact_obligation_reduction_def frontier_covering_def
    covering_obligations_def covering_condition_def graph_map_ran image_subset_iff)

theorem guided_covering_method_assessment:
  assumes boundary: "frontier\<subseteq>C"
    and sound: "inference_sound (covering_condition ability) R"
    and known: "K\<subseteq>{z. covering_condition ability z}"
    and settled: "remaining_obligations
      (inference_closure (guided_inferences R K (rel_ran (covering_obligations C frontier h))) K)
      (covering_obligations C frontier h)={}"
  shows "frontier_covering C ability frontier h"
proof -
  have residual: "remaining_obligations (inference_closure R K) (covering_obligations C frontier h)={}"
    using settled by (simp only: guided_goal_residual_exact[OF subset_refl])
  show ?thesis
    by (rule reduced_requirement_complete[where a=h, OF
      exact_obligation_reduction_sound[OF covering_method_evaluation_reduction[where ability=ability, OF boundary]]
      UNIV_I inference_closure_sound[OF sound known] residual])
qed

theorem an_uncovered_alternative_retains_its_comparison_reason:
  assumes alternative: "c\<in>C"
    and missed: "h c\<notin>frontier \<or> \<not>ability c\<subseteq>ability (h c)"
  shows "(c,(frontier,c,h c))\<in>remaining_obligations {z. covering_condition ability z}
    (covering_obligations C frontier h)"
  using assms by (simp add: covering_obligations_def graph_map_member covering_condition_def)

theorem investigated_stopping:
  assumes current: "c\<in>C" and boundary: "frontier\<subseteq>C"
    and basis_rules: "inference_sound (basis_condition relation observe) RB"
    and basis_known: "KB\<subseteq>{z. basis_condition relation observe z}"
    and basis_settled: "remaining_obligations
      (inference_closure (guided_inferences RB KB (rel_ran (basis_obligations C F))) KB)
      (basis_obligations C F)={}"
    and covering_rules: "inference_sound (covering_condition (candidate_profile F observe)) RC"
    and covering_known: "KC\<subseteq>{z. covering_condition (candidate_profile F observe) z}"
    and covering_settled: "remaining_obligations
      (inference_closure (guided_inferences RC KC (rel_ran (covering_obligations C frontier h))) KC)
      (covering_obligations C frontier h)={}"
    and comparison_rules: "inference_sound (profile_condition observe) RP"
    and comparison_known: "KP\<subseteq>{z. profile_condition observe z}"
    and comparison_settled: "remaining_obligations
      (inference_closure (guided_inferences RP KP (rel_ran (frontier_obligations F observe frontier c))) KP)
      (frontier_obligations F observe frontier c)={}"
  shows "\<forall>d\<in>C. relation d c"
proof -
  have basis: "comparison_basis C relation F observe"
    by (rule guided_observation_method_assessment[OF basis_rules basis_known basis_settled])
  have covering: "frontier_covering C (candidate_profile F observe) frontier h"
    by (rule guided_covering_method_assessment[OF boundary covering_rules covering_known covering_settled])
  have cover: "candidate_cover C (candidate_profile F observe) frontier"
    using covering by (simp only: candidate_cover_has_a_covering_method; blast)
  show ?thesis by (rule guided_frontier_assessment[OF basis cover comparison_rules
    comparison_known current comparison_settled])
qed

section \<open>A dependency-sensitive method comparison exposes its own conditions\<close>

definition round_comparison_condition where
  "round_comparison_condition z \<longleftrightarrow>
    fst (snd z)\<in>inference_rounds (fst z) (rel_ran (snd (snd z))) 1"

theorem round_method_comparison_reduction:
  "exact_obligation_reduction UNIV (\<lambda>z. inference_round_refines (fst z) (snd z))
    round_comparison_condition (\<lambda>z. comparison_obligations (fst z) (snd z))"
proof -
  have occurrences: "rel_ran (comparison_obligations R S)\<subseteq>{z. test z} \<longleftrightarrow>
      (\<forall>a H. finite H \<longrightarrow> single_valued H \<longrightarrow> R a H \<longrightarrow> test (S,a,H))"
    for R S test
    by (auto simp: comparison_obligations_def rel_ran_def; blast)
  show ?thesis
    by (simp only: exact_obligation_reduction_def occurrences inference_round_refines_iff_rules
      round_comparison_condition_def fst_conv snd_conv; simp)
qed

theorem round_observation_basis:
  "comparison_basis C
    (\<lambda>R S. inference_round_refines (bounded_inferences k R) (bounded_inferences k S))
    {True} (inference_depth_observations k)"
  by (simp only: comparison_basis_def candidate_profile_comparison inference_depth_observation_comparison; simp)

theorem round_and_conditional_observation_basis:
  "comparison_basis C
    (\<lambda>R S. inference_round_refines (bounded_inferences k R) (bounded_inferences k S))
    {False,True} (inference_depth_observations k)"
  by (simp only: comparison_basis_def candidate_profile_comparison rounds_already_retain_conditional_capability; simp)

theorem an_installed_shortcut_retains_an_establishment_obligation:
  defines "R \<equiv> (\<lambda>a::nat. \<lambda>H::(unit\<times>nat) set.
    (a=1 \<and> H={((),0)}) \<or> (a=2 \<and> H={((),1)}))"
  shows "inference_refines (derived_inferences R) R \<and>
    2\<in>inference_rounds R {0} 2 \<and> 2\<notin>inference_rounds R {0} 1 \<and>
    2\<in>inference_rounds (derived_inferences R) {0} 1 \<and>
    \<not>inference_round_refines (derived_inferences R) R"
proof -
  have singleton: "single_valued {((),b)}" and ran: "rel_ran {((),b)}={b}" for b::nat
    by (auto simp: single_valued_def rel_ran_def)
  have consequences: "inference_consequences R A=
      {a. (a=1 \<and> 0\<in>A) \<or> (a=2 \<and> 1\<in>A)}" for A
    by (auto simp: inference_consequences_def R_def singleton ran)
  have first: "inference_rounds R {0} 1={0,1}"
    by (auto simp: consequences)
  have second: "inference_rounds R {0} 2={0,1,2}"
    by (auto simp: numeral_2_eq_2 consequences)
  have original: "2\<in>inference_closure R {0}"
    using second inference_rounds_inside_closure[of R "{0}" 2] by blast
  have shortcut: "derived_inferences R 2 {((),0)}"
    using original by (simp add: derived_inferences_def rel_ran_image)
  have later: "2\<in>inference_rounds (derived_inferences R) {0} 1"
  proof -
    have "2\<in>inference_rounds (derived_inferences R) {0} (Suc 0)"
      by (rule inference_rounds_step[where H="{((),0)}"])
        (use shortcut in \<open>auto simp: singleton ran\<close>)
    then show ?thesis by simp
  qed
  have different: "\<not>inference_round_refines (derived_inferences R) R"
  proof
    assume comparison: "inference_round_refines (derived_inferences R) R"
    have included: "inference_rounds (derived_inferences R) {0} 1\<subseteq>inference_rounds R {0} 1"
      using comparison by (simp only: inference_round_refines_def; blast)
    have "2\<in>inference_rounds R {0} 1" by (rule subsetD[OF included later])
    then show False by (simp only: first; simp)
  qed
  have establishment: "2\<in>inference_rounds R {0} 2 \<and> 2\<notin>inference_rounds R {0} 1"
    by (simp only: first second; simp)
  show ?thesis using derived_method_conservative[of R] establishment later different by blast
qed

text \<open>
  Selecting observations is itself a candidate method. Its capability is the
  set of actual candidate comparisons it can distinguish. The existing
  complete-candidate criterion characterizes adequate selections from an
  independently adequate family. A missing-facet witness strictly improves
  that capability; the choice is not justified by adding another label.

  The adequacy question has an exact identified obligation family and uses
  the same demand, inference, and residual evaluator as ordinary candidates.
  A covering method also names the representative for every alternative and
  supplies the actual membership and preservation conditions. The combined
  stopping theorem investigates observation adequacy, coverage, and final
  comparisons through the same mechanism, with their separate soundness and
  established-evidence boundaries. A supplied frontier is never its own proof
  of complete scope.

  Conditional capability and dependency-sensitive capability also have
  explicit local comparison reductions. The latter retains the former, so
  storing both is unnecessary for that particular comparison question.

  Derived-rule completion illustrates why setup remains separate. A shortcut
  can shorten a later use while requiring an earlier two-round establishment.
  Its ordinary conservativity proof does not establish preservation of every
  dependency budget. The richer method exposes that missing condition.
\<close>

end
