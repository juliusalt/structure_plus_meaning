theory Presentation_Investigation
  imports Method_Investigation Presentation_Development
begin

section \<open>Input availability and complete outputs are different observations\<close>

definition reader_inclusion where
  "reader_inclusion operation following \<longleftrightarrow>
    (\<forall>p q. operation p q \<longrightarrow> following p q)"

definition reader_observations where
  "reader_observations f operation=
    (if f then Inr ` {(p,q). operation p q} else Inl ` {p. \<exists>q. operation p q})"

lemma reader_output_comparison:
  "candidate_profile {True} reader_observations operation\<subseteq>
      candidate_profile {True} reader_observations following \<longleftrightarrow>
    reader_inclusion operation following"
  by (auto simp: candidate_profile_comparison reader_observations_def reader_inclusion_def)

lemma reader_all_observation_comparison:
  "candidate_profile {False,True} reader_observations operation\<subseteq>
      candidate_profile {False,True} reader_observations following \<longleftrightarrow>
    reader_inclusion operation following"
  by (auto simp: candidate_profile_comparison reader_observations_def reader_inclusion_def; blast)

theorem reader_output_basis:
  "comparison_basis C reader_inclusion {True} reader_observations"
  by (simp only: comparison_basis_def reader_output_comparison; simp)

theorem reader_complete_observation_basis:
  "comparison_basis C reader_inclusion {False,True} reader_observations"
  by (simp only: comparison_basis_def reader_all_observation_comparison; simp)

context presentation_class
begin

definition reader_candidates where
  "reader_candidates={operation. presented_function_witness presents subject admissible
    presents subject admissible id operation}"

abbreviation copy_reader where
  "copy_reader \<equiv> \<lambda>p q. admissible p \<and> q=p"

abbreviation complete_reader where
  "complete_reader \<equiv> presentation_transport presents presents"

abbreviation completed_reader where
  "completed_reader operation \<equiv> \<lambda>p r. \<exists>q. operation p q \<and>
    presentation_transport presents presents q r"

lemma reader_candidate_contract:
  "operation\<in>reader_candidates \<Longrightarrow>
    presented_function_witness presents subject admissible presents subject admissible id operation"
  by (simp add: reader_candidates_def)

lemma copy_reader_candidate:
  "copy_reader\<in>reader_candidates"
  using literal_copy_witness[OF presentation_class_axioms] by (simp add: reader_candidates_def)

lemma complete_reader_contract:
  "presented_function_contract presents subject admissible presents subject admissible id complete_reader"
  by (rule presentation_identity_function[OF presentation_class_axioms presentation_class_axioms])

lemma complete_reader_candidate:
  "complete_reader\<in>reader_candidates"
  using presented_function_contract.witness[OF complete_reader_contract]
  by (simp add: reader_candidates_def)

lemma reader_candidate_input_observation:
  assumes "operation\<in>reader_candidates"
  shows "reader_observations False operation=Inl ` {p. admissible p}"
  using presented_function_witness.input_exact[OF reader_candidate_contract[OF assms]]
  by (simp add: reader_observations_def)

theorem every_witness_is_complete_for_input_coverage:
  assumes "operation\<in>reader_candidates"
  shows "complete_candidate reader_candidates (candidate_profile {False} reader_observations) operation"
proof -
  have measured: "candidate_profile {False} reader_observations following\<subseteq>
      candidate_profile {False} reader_observations operation" if "following\<in>reader_candidates" for following
    by (simp only: candidate_profile_comparison;
      simp add: reader_candidate_input_observation[OF that] reader_candidate_input_observation[OF assms])
  show ?thesis using assms measured by (simp add: complete_candidate_def)
qed

lemma reader_candidate_below_complete:
  assumes "operation\<in>reader_candidates"
  shows "reader_inclusion operation complete_reader"
proof -
  interpret operation: presented_function_witness presents subject admissible
    presents subject admissible id operation
    by (rule reader_candidate_contract[OF assms])
  show ?thesis
  proof (unfold reader_inclusion_def, intro allI impI)
    fix p q assume run: "operation p q"
    obtain a where source: "presents a p" using admitted[OF operation.input_boundary[OF run]] by blast
    have target: "presents a q" using operation.sound[OF source run] by simp
    show "complete_reader p q" using source target by (auto simp: presentation_transport_def)
  qed
qed

theorem complete_reader_covers_every_witness:
  "complete_candidate reader_candidates (candidate_profile {True} reader_observations) complete_reader"
  using complete_reader_candidate reader_candidate_below_complete
  by (simp add: complete_candidate_def reader_output_comparison)

theorem complete_reader_explains_its_whole_scope_cover:
  "frontier_covering reader_candidates (candidate_profile {True} reader_observations)
    {complete_reader} (\<lambda>_. complete_reader)"
  using complete_reader_candidate reader_candidate_below_complete
  by (simp add: frontier_covering_def reader_output_comparison)

lemma unique_presentations_make_all_witnesses_equal:
  assumes unique: "\<And>a p q. presents a p \<Longrightarrow> presents a q \<Longrightarrow> p=q"
    and first: "operation\<in>reader_candidates" and second: "following\<in>reader_candidates"
  shows "reader_inclusion operation following"
proof -
  interpret operation: presented_function_witness presents subject admissible
    presents subject admissible id operation by (rule reader_candidate_contract[OF first])
  interpret following: presented_function_witness presents subject admissible
    presents subject admissible id following by (rule reader_candidate_contract[OF second])
  show ?thesis
  proof (unfold reader_inclusion_def, intro allI impI)
    fix p q assume run: "operation p q"
    have allowed: "admissible p" by (rule operation.input_boundary[OF run])
    obtain a where source: "presents a p" using admitted[OF allowed] by blast
    have target: "presents a q" using operation.sound[OF source run] by simp
    have equal: "p=q" by (rule unique[OF source target])
    obtain r where result: "following p r" using following.total[OF allowed] by blast
    have presented: "presents a r" using following.sound[OF source result] by simp
    have same: "p=r" by (rule unique[OF source presented])
    show "following p q" using result equal same by simp
  qed
qed

theorem input_coverage_is_adequate_exactly_when_presentations_are_unique:
  "comparison_basis reader_candidates reader_inclusion {False} reader_observations \<longleftrightarrow>
    (\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> p=q)"
proof
  assume basis: "comparison_basis reader_candidates reader_inclusion {False} reader_observations"
  have measured: "candidate_profile {False} reader_observations complete_reader\<subseteq>
      candidate_profile {False} reader_observations copy_reader"
    using every_witness_is_complete_for_input_coverage[OF copy_reader_candidate]
      complete_reader_candidate by (auto simp: complete_candidate_def)
  have inclusion: "reader_inclusion complete_reader copy_reader"
    using measured by (simp only: comparison_basis_at[OF basis complete_reader_candidate copy_reader_candidate, symmetric])
  show "\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> p=q"
    using inclusion by (auto simp: reader_inclusion_def presentation_transport_def)
next
  assume unique: "\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> p=q"
  have same: "reader_inclusion operation following"
    if "operation\<in>reader_candidates" "following\<in>reader_candidates" for operation following
    by (rule unique_presentations_make_all_witnesses_equal[OF _ that]) (use unique in blast)
  have measured: "candidate_profile {False} reader_observations operation\<subseteq>
      candidate_profile {False} reader_observations following"
    if "operation\<in>reader_candidates" "following\<in>reader_candidates" for operation following
    using every_witness_is_complete_for_input_coverage[OF that(2)] that(1)
    by (simp add: complete_candidate_def)
  show "comparison_basis reader_candidates reader_inclusion {False} reader_observations"
    using same measured by (simp add: comparison_basis_def)
qed

theorem nonunique_presentations_supply_the_missing_facet_and_use:
  assumes first: "presents a p" and second: "presents a q" and distinct: "p\<noteq>q"
  shows "(complete_reader,copy_reader)\<in>
      comparison_failures reader_candidates reader_inclusion {False} reader_observations"
    "(True,Inr (p,q))\<in>candidate_losses {True} reader_observations complete_reader copy_reader"
proof -
  have complete: "complete_reader p q" using first second by (auto simp: presentation_transport_def)
  have missing: "\<not>copy_reader p q" using distinct by simp
  have measured: "candidate_profile {False} reader_observations complete_reader\<subseteq>
      candidate_profile {False} reader_observations copy_reader"
    using every_witness_is_complete_for_input_coverage[OF copy_reader_candidate]
      complete_reader_candidate by (auto simp: complete_candidate_def)
  show "(complete_reader,copy_reader)\<in>
      comparison_failures reader_candidates reader_inclusion {False} reader_observations"
    using complete_reader_candidate copy_reader_candidate complete missing measured
    by (auto simp: comparison_failures_def reader_inclusion_def)
  show "(True,Inr (p,q))\<in>candidate_losses {True} reader_observations complete_reader copy_reader"
    using complete missing by (auto simp: reader_observations_def)
qed

theorem witness_completion_recovers_the_whole_reader:
  assumes "operation\<in>reader_candidates"
  shows "completed_reader operation=complete_reader"
    and "completed_reader operation\<in>reader_candidates"
proof -
  have contract: "presented_function_contract presents subject admissible presents subject admissible id
      (completed_reader operation)"
    by (rule presented_function_witness.completion[OF reader_candidate_contract[OF assms]])
  interpret completed: presented_function_contract presents subject admissible
    presents subject admissible id "completed_reader operation" by (rule contract)
  show "completed_reader operation=complete_reader"
  proof (rule ext, rule ext)
    fix p q
    have exact: "completed_reader operation p q \<longleftrightarrow>
      presented_relation presents presents (\<lambda>a b. b=id a) p q"
      by (rule completed.exact)
    have meaning: "presented_relation presents presents (\<lambda>a b. b=id a) p q \<longleftrightarrow>
        complete_reader p q"
      by (auto simp: presented_relation_def presentation_transport_def)
    show "completed_reader operation p q=complete_reader p q"
      using exact meaning by blast
  qed
  show "completed_reader operation\<in>reader_candidates"
    using presented_function_contract.witness[OF contract] by (simp add: reader_candidates_def)
qed

theorem a_missing_output_directs_a_complete_preserving_candidate:
  assumes candidate: "operation\<in>reader_candidates"
    and first: "presents a p" and second: "presents a q" and missing: "\<not>operation p q"
  shows "completed_reader operation\<in>
    attainment_candidates reader_candidates (candidate_profile {True} reader_observations)
      (insert (True,Inr (p,q)) (candidate_profile {True} reader_observations operation))"
    "candidate_profile {True} reader_observations operation\<subset>
      candidate_profile {True} reader_observations (completed_reader operation)"
proof -
  have member: "completed_reader operation\<in>reader_candidates"
    by (rule witness_completion_recovers_the_whole_reader(2)[OF candidate])
  have included: "candidate_profile {True} reader_observations operation\<subseteq>
      candidate_profile {True} reader_observations (completed_reader operation)"
    by (simp only: witness_completion_recovers_the_whole_reader(1)[OF candidate] reader_output_comparison;
      rule reader_candidate_below_complete[OF candidate])
  have full: "complete_reader p q" using first second by (auto simp: presentation_transport_def)
  have equation: "completed_reader operation p q=complete_reader p q"
    by (rule cong[OF cong[OF witness_completion_recovers_the_whole_reader(1)[OF candidate] refl] refl])
  have run: "completed_reader operation p q" using full equation by simp
  have attained: "(True,Inr (p,q))\<in>candidate_profile {True} reader_observations (completed_reader operation)"
    using run by (auto simp: reader_observations_def intro: imageI)
  have result: "completed_reader operation\<in>
    attainment_candidates reader_candidates (candidate_profile {True} reader_observations)
      (insert (True,Inr (p,q)) (candidate_profile {True} reader_observations operation))"
    using member included attained by (simp add: attainment_candidates_def)
  show "completed_reader operation\<in>
    attainment_candidates reader_candidates (candidate_profile {True} reader_observations)
      (insert (True,Inr (p,q)) (candidate_profile {True} reader_observations operation))"
    by (rule result)
  have absent: "(True,Inr (p,q))\<notin>candidate_profile {True} reader_observations operation"
    using missing by (auto simp: reader_observations_def image_iff)
  show "candidate_profile {True} reader_observations operation\<subset>
      candidate_profile {True} reader_observations (completed_reader operation)"
    by (rule conjunct1[OF a_missing_use_directs_a_preserving_improvement[OF absent result]])
qed

theorem the_same_evaluator_justifies_the_output_basis:
  "complete_candidate (Pow {False,True})
    (\<lambda>F. observation_discriminations reader_candidates F reader_observations) {True}"
  by (simp only: basis_selection_uses_the_same_candidate_comparison[OF reader_complete_observation_basis,
      of "{True}", simplified, symmetric]; rule reader_output_basis)

end

text \<open>
  The candidate domain contains every sound total identity witness for an
  independently fixed complete presentation class. Input availability is
  identical throughout that whole domain. It therefore makes every candidate
  complete for that observation, although some readers omit compatible outputs.

  The exact adequacy criterion is presentation uniqueness. If that condition
  holds, input coverage suffices for the stated reader comparison. Otherwise,
  two actual presentations supply the missing output witness and the failed
  comparison. This evidence directs the existing witness-completion construction,
  which preserves the current reader and attains every compatible output.

  Output observations alone already determine input availability. They form
  an adequate basis without duplicating the weaker facet. Their selection is
  itself evaluated by the same candidate machinery. These conclusions concern
  complete reader inclusion; native availability, establishment size, and other
  meaningful questions still need their own observation and scope contracts.
\<close>

end
