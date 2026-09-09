theory Factor_Recorded_Construction_Obligations
  imports Factor_Construction_Invariance Factor_Recorded_Cause
begin

section \<open>The actual program and call determine the construction judgment\<close>

theorem construction_judgment_at_account:
  assumes package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "construction_judgment_at F pu pr au ar (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)
    \<longleftrightarrow> construction_account_presents a t \<and> construction_permission_invariant P d \<and>
      (d,t)\<in>positive_meaning P"
proof
  let ?xs="fst (fst a)" and ?B="snd (fst a)" and ?W="snd a" and ?R="construction_account_output a"
  assume judged: "construction_judgment_at F pu pr au ar ?xs ?B ?W ?R"
  have claim: "construction_claim_presents ?xs ?B ?W ?R t" and allowed: "factor_constructs P d ?xs ?B ?W ?R"
    using construction_judgment_with_reads[OF package app] judged by blast+
  have built: "source_constructs ?xs ?B ?W ?R" and coords: "construction_coordinates_formed ?B ?W"
    and invariant: "construction_permission_invariant P d" using allowed by (auto simp: factor_constructs_def)
  have read: "construction_account_presents a t"
    using built coords claim by (simp add: construction_account_presents_def)
  have truth: "(d,t)\<in>positive_meaning P"
    using factor_construction_at_presentation[OF built coords invariant claim] allowed by blast
  show "construction_account_presents a t \<and> construction_permission_invariant P d \<and> (d,t)\<in>positive_meaning P"
    using read invariant truth by blast
next
  let ?xs="fst (fst a)" and ?B="snd (fst a)" and ?W="snd a" and ?R="construction_account_output a"
  assume parts: "construction_account_presents a t \<and> construction_permission_invariant P d \<and> (d,t)\<in>positive_meaning P"
  have claim: "construction_claim_presents ?xs ?B ?W ?R t"
    and built: "source_constructs ?xs ?B ?W ?R" and coords: "construction_coordinates_formed ?B ?W"
    using parts by (auto simp: construction_account_presents_def)
  have allowed: "factor_constructs P d ?xs ?B ?W ?R"
    using parts built coords claim by (auto simp: factor_constructs_def)
  show "construction_judgment_at F pu pr au ar ?xs ?B ?W ?R"
    using construction_judgment_with_reads[OF package app] claim allowed by blast
qed

section \<open>Five independently meaningful conditions retain their positions\<close>

definition recorded_construction_obligations where
  "recorded_construction_obligations F pu pr au ar G P d t a =
    {(0::nat,F=native_judgment_environment F pu pr au ar),
     (1,generation_payload G=Whole_Artifact (construction_account_output a)),
     (2,construction_account_presents a t),
     (3,construction_permission_invariant P d),
     (4,(d,t)\<in>positive_meaning P)}"

lemma recorded_construction_obligations_formed:
  "finite (recorded_construction_obligations F pu pr au ar G P d t a)"
  "single_valued (recorded_construction_obligations F pu pr au ar G P d t a)"
  "card (recorded_construction_obligations F pu pr au ar G P d t a)=5"
  by (auto simp: recorded_construction_obligations_def single_valued_def)

theorem recorded_construction_obligation_reduction:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "exact_obligation_reduction UNIV
    (\<lambda>a. recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a))
    id (recorded_construction_obligations F pu pr au ar G P d t)"
  by (auto simp: exact_obligation_reduction_def recorded_construction_cause_with_scope[OF scope]
    construction_judgment_at_account[OF package app] recorded_construction_obligations_def rel_ran_def subset_iff)

theorem recorded_construction_residual_exact:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)
    \<longleftrightarrow> remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)={}"
  using recorded_construction_obligation_reduction[OF scope package app,
    unfolded exact_obligation_reduction_def, rule_format, where a=a]
  by (auto simp: remaining_obligations_empty)

theorem recorded_construction_from_local_permission:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    and minimal: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact (construction_account_output a)"
    and account: "construction_account_presents a t" and truth: "(d,t)\<in>positive_meaning P"
    and local: "\<And>i c. (i,c)\<in>construction_permission_obligations P d \<Longrightarrow> observation_condition c"
  shows "recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
proof -
  have invariant: "construction_permission_invariant P d" by (rule construction_permission_local_discharge[OF local])
  have empty: "remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)={}"
    using minimal payload account invariant truth by (auto simp: recorded_construction_obligations_def remaining_obligations_def)
  show ?thesis by (rule reduced_requirement_complete[OF exact_obligation_reduction_sound[
      OF recorded_construction_obligation_reduction[OF scope package app]], where K="{True}" and a=a])
    (use empty in auto)
qed

theorem a_positive_call_leaves_the_global_permission_obligation:
  assumes minimal: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact (construction_account_output a)"
    and account: "construction_account_presents a t" and truth: "(d,t)\<in>positive_meaning P"
  shows "remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)=
    remaining_obligations {True} {(3::nat,construction_permission_invariant P d)}"
  using assms by (auto simp: recorded_construction_obligations_def remaining_obligations_def)

theorem a_noninvariant_positive_cause_is_rejected:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    and noninvariant: "\<not>construction_permission_invariant P d"
  shows "\<not>recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    and "(3,False)\<in>remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)"
proof -
  show residual: "(3,False)\<in>remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)"
    using noninvariant by (simp add: recorded_construction_obligations_def)
  show "\<not>recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    using recorded_construction_residual_exact[OF scope package app] residual by blast
qed

theorem altered_payload_remains_a_false_condition:
  assumes "generation_payload G\<noteq>Whole_Artifact (construction_account_output a)"
  shows "(1,False)\<in>remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)"
  using assms by (simp add: recorded_construction_obligations_def)

theorem extra_recorded_scope_remains_a_false_condition:
  assumes "F\<noteq>native_judgment_environment F pu pr au ar"
  shows "(0,False)\<in>remaining_obligations {True} (recorded_construction_obligations F pu pr au ar G P d t a)"
  using assms by (simp add: recorded_construction_obligations_def)

text \<open>
  The already read recorded scope, actual native package, and actual application
  are premises of this reduction. Its five conditions concern least scope,
  the exact payload, the complete account, global permission invariance, and
  positive truth. Their distinct positions survive equal Boolean values.
  Pieces and output remain derived from the account's original basis.

  The local permission reduction discharges the fourth condition through its
  independently proved complete generator. It does not replace the actual
  program in the recorded scope. Truth of the supplied call leaves that global
  condition outstanding. Wrong payloads and nonminimal scopes remain false
  conditions even when permission is established.

  These are exact mathematical reductions for the existing cause judgment.
  The five-position family is finite, but evaluating arbitrary global
  permission truth is not thereby a terminating operation. Native checking of
  its mathematical admission evidence, and the resulting general recorded
  construction checker, remain distinct work under O-85.
\<close>

end
