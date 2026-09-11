theory Presentation_Completion
  imports Presentation_Contracts Observation_Invariance
begin

section \<open>Completion observes some equivalent presentation\<close>

definition saturate_observation ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> bool" where
  "saturate_observation R test p \<longleftrightarrow>
    (\<exists>q. presentation_transport R R p q \<and> test q)"

lemma saturate_observation_disjunction:
  "saturate_observation R (\<lambda>p. P p \<or> Q p)=
    (\<lambda>p. saturate_observation R P p \<or> saturate_observation R Q p)"
  by (intro ext) (auto simp: saturate_observation_def)

context presentation_class
begin

lemma saturation_at:
  assumes read: "presents a p"
  shows "saturate_observation presents test p \<longleftrightarrow>
    (\<exists>q. presents a q \<and> test q)"
  using read recovery by (auto simp: saturate_observation_def presentation_transport_def; blast)

lemma saturation_boundary:
  "saturate_observation presents test p \<Longrightarrow> admissible p"
  using presentation_boundary by (auto simp: saturate_observation_def presentation_transport_def)

lemma saturation_extends:
  assumes "admissible p" "test p"
  shows "saturate_observation presents test p"
  using admitted[OF assms(1)] assms(2)
  by (auto simp: saturate_observation_def presentation_transport_def)

theorem saturation_invariant:
  "rel_fun (presentation_transport presents presents) (=)
    (saturate_observation presents test) (saturate_observation presents test)"
  by (auto simp: rel_fun_def presentation_transport_def saturation_at)

theorem saturation_fixed_iff:
  "saturate_observation presents test=(\<lambda>p. admissible p \<and> test p) \<longleftrightarrow>
    rel_fun (presentation_transport presents presents) (=) test test"
proof
  assume fixed: "saturate_observation presents test=(\<lambda>p. admissible p \<and> test p)"
  show "rel_fun (presentation_transport presents presents) (=) test test"
    using saturation_invariant[of test] presentation_boundary
    by (auto simp: fixed rel_fun_def presentation_transport_def)
next
  assume invariant: "rel_fun (presentation_transport presents presents) (=) test test"
  show "saturate_observation presents test=(\<lambda>p. admissible p \<and> test p)"
  proof (rule ext, rule iffI)
    fix p assume completed: "saturate_observation presents test p"
    have boundary: "admissible p" by (rule saturation_boundary[OF completed])
    have truth: "test p" using completed invariant
      by (auto simp: saturate_observation_def rel_fun_def)
    show "admissible p \<and> test p" using boundary truth by blast
  next
    fix p assume "admissible p \<and> test p"
    then show "saturate_observation presents test p" by (intro saturation_extends) auto
  qed
qed

theorem saturation_idempotent:
  "saturate_observation presents (saturate_observation presents test)=
    saturate_observation presents test"
  using saturation_fixed_iff[of "saturate_observation presents test"] saturation_invariant[of test]
    saturation_boundary[of test] by (auto simp: fun_eq_iff)

theorem saturation_least:
  assumes invariant: "rel_fun (presentation_transport presents presents) (=) Q Q"
  shows "(\<forall>p. saturate_observation presents P p \<longrightarrow> Q p) \<longleftrightarrow>
    (\<forall>p. admissible p \<longrightarrow> P p \<longrightarrow> Q p)"
  using invariant saturation_extends[of _ P] presentation_boundary
  by (auto simp: saturate_observation_def presentation_transport_def rel_fun_def; blast)

section \<open>An intended meaning remains an independent condition\<close>

theorem saturation_sound_iff:
  "(\<forall>a p. presents a p \<longrightarrow> saturate_observation presents test p \<longrightarrow> M a) \<longleftrightarrow>
    (\<forall>a p. presents a p \<longrightarrow> test p \<longrightarrow> M a)"
  using saturation_extends presentation_boundary by (auto simp: saturation_at; blast)

theorem saturation_meaning_iff:
  "saturate_observation presents test=presented_predicate presents M \<longleftrightarrow>
    (\<forall>a. subject a \<longrightarrow> (M a \<longleftrightarrow> (\<exists>q. presents a q \<and> test q)))"
proof
  assume exact: "saturate_observation presents test=presented_predicate presents M"
  show "\<forall>a. subject a \<longrightarrow> (M a \<longleftrightarrow> (\<exists>q. presents a q \<and> test q))"
  proof (intro allI impI)
    fix a assume "subject a"
    then obtain p where read: "presents a p" using total by blast
    show "M a \<longleftrightarrow> (\<exists>q. presents a q \<and> test q)"
      using saturation_at[OF read, of test] predicate_at[OF read, of M] exact by simp
  qed
next
  assume meaning: "\<forall>a. subject a \<longrightarrow> (M a \<longleftrightarrow> (\<exists>q. presents a q \<and> test q))"
  show "saturate_observation presents test=presented_predicate presents M"
    using meaning subject_boundary
    by (intro ext) (auto simp: saturate_observation_def presentation_transport_def presented_predicate_def; blast)
qed

theorem saturation_evaluation_reduction:
  "exact_obligation_reduction UNIV
    (\<lambda>test. saturate_observation presents test=(\<lambda>p. admissible p \<and> test p))
    observation_condition (observation_obligations (presentation_transport presents presents))"
  by (simp add: exact_obligation_reduction_def saturation_fixed_iff observation_obligations_exact)

end

theorem completion_can_change_an_observation:
  "saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True) id False \<and>
    \<not>id False \<and>
    \<not>rel_fun (presentation_transport (\<lambda>_::unit. \<lambda>_::bool. True)
      (\<lambda>_::unit. \<lambda>_::bool. True)) (=) id id"
  by (auto simp: saturate_observation_def presentation_transport_def rel_fun_def)

theorem separate_completions_need_not_have_a_common_witness:
  "saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True) id False \<and>
    saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True) Not False \<and>
    \<not>saturate_observation (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>p. p \<and> \<not>p) False"
  by (auto simp: saturate_observation_def presentation_transport_def)

text \<open>
  Existential completion is the least invariant extension on the entire
  admitted domain. It is idempotent. Agreement with the original observation
  is exactly its invariance condition, evaluated through the same identified
  obligation reduction as every other candidate. Completion alone proves no
  independently intended meaning: soundness and coverage of true subjects
  retain their own exact criteria.

  Separate completed tests can use incompatible witnesses. Their conjunction
  is therefore not substituted for a single completed conjunction. Neither
  completion nor its mathematical contract supplies a native predicate or
  rewrites the actual program named in an existing cause.
\<close>

end
