theory Factor_Native_SK
  imports Factor_SK Factor_Compiled_Applications Factor_Replay
begin

section \<open>One closed native package for every future SK computation\<close>

theorem sk_native_program_total:
  "\<exists>g :: nat \<Rightarrow> local_address option definition_site. \<exists>E pu Q.
    inj_on g {0,1,2} \<and> closed_native_package_at E pu [] Q \<and>
    (\<forall>d\<in>{0,1,2}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>sk_expected_calls) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
  using compiled_program_future_applications[OF sk_system_formed]
  by (simp add: sk_program_exact)

theorem sk_native_reduction_certificates:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t u. \<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (sk_reduces t u \<longleftrightarrow>
        (\<exists>H root. native_package_at H pu [] Q \<and>
          native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
          native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
          native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
          environment_included (native_judgment_environment F pu [] au []) H)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q where injective: "inj_on g {0,1,2}"
    and package: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>{0,1,2}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>sk_expected_calls) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using sk_native_program_total by (elim exE conjE) (erule meta_allE)
  have reductions: "\<forall>t u. \<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu [] Q \<and>
    native_application_at F au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K \<and>
    native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
    (sk_reduces t u \<longleftrightarrow>
      (\<exists>H root. native_package_at H pu [] Q \<and>
        native_application_at H au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
        native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
        environment_included (native_judgment_environment F pu [] au []) H))"
  proof (intro allI)
    fix t u
    have formed: "term_formed (Pair_Term (sk_value t) (sk_value u))" by simp
    obtain F au I K where ff: "environment_formed F" and included: "environment_included E F"
      and source: "native_package_at F pu [] Q"
        "native_application_at F au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K"
      and canonical: "native_package_environment F pu []=E"
      and call: "native_application_formed F pu [] au []"
      and truth: "native_positive_holds F pu [] au [] \<longleftrightarrow>
        (2,Pair_Term (sk_value t) (sk_value u))\<in>sk_expected_calls"
      using future[rule_format, of 2 "Pair_Term (sk_value t) (sk_value u)"] formed by auto
    have exact: "sk_reduces t u \<longleftrightarrow>
      (\<exists>H root. native_package_at H pu [] Q \<and>
        native_application_at H au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
        native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
        environment_included (native_judgment_environment F pu [] au []) H)"
      using native_replay_exact_call_adequate[OF source] truth sk_expected_values(3)[of t u] canonical by simp
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (sk_reduces t u \<longleftrightarrow>
        (\<exists>H root. native_package_at H pu [] Q \<and>
          native_application_at H au [] (g 2) (Pair_Term (sk_value t) (sk_value u)) I K \<and>
          native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
          native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
          environment_included (native_judgment_environment F pu [] au []) H))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
         (use ff included source canonical call exact in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 2"])
    (use package reductions in blast)
qed

theorem sk_native_reduction_replay_iff:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t u. sk_reduces t u \<longleftrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E))"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d where
    package: "closed_native_package_at E pu [] Q"
    and computations: "\<forall>t u. \<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (sk_reduces t u \<longleftrightarrow>
        (\<exists>H root. native_package_at H pu [] Q \<and>
          native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
          native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
          native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
          environment_included (native_judgment_environment F pu [] au []) H))"
    using sk_native_reduction_certificates by blast
  have each: "\<forall>t u. sk_reduces t u \<longleftrightarrow>
    (\<exists>H au I K root. native_package_at H pu [] Q \<and>
      native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
      native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
  proof (intro allI)
    fix t u
    obtain F au I K where source: "native_package_at F pu [] Q"
      "native_application_at F au [] d (Pair_Term (sk_value t) (sk_value u)) I K"
      and canonical: "native_package_environment F pu []=E"
      and exact: "sk_reduces t u \<longleftrightarrow>
        (\<exists>H root. native_package_at H pu [] Q \<and>
          native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
          native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E \<and>
          native_judgment_environment H pu [] au []=native_judgment_environment F pu [] au [] \<and>
          environment_included (native_judgment_environment F pu [] au []) H)"
      using computations[rule_format, of t u] by blast
    have meaning: "sk_reduces t u \<longleftrightarrow>
      (d,Pair_Term (sk_value t) (sk_value u))\<in>positive_meaning Q"
      using exact native_replay_exact_call_adequate[OF source]
        native_positive_holds_with_reads[OF source] by (simp only: canonical)
    show "sk_reduces t u \<longleftrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
    proof
      assume "sk_reduces t u"
      then show "\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E"
        using exact by blast
    next
      assume "\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E"
      then obtain H bu J L root where target: "native_package_at H pu [] Q"
        "native_application_at H bu [] d (Pair_Term (sk_value t) (sk_value u)) J L"
        and certificate: "native_replay_at H pu [] bu [] root {}" by blast
      have positive: "native_positive_holds H pu [] bu []"
        by (rule native_replay_closed_sound[OF certificate])
      show "sk_reduces t u" using meaning positive native_positive_holds_with_reads[OF target] by blast
    qed
  qed
  show ?thesis using package each by blast
qed

theorem sk_native_reductions_realized:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t u. sk_reduces t u \<longrightarrow>
      (\<exists>H au I K root. native_package_at H pu [] Q \<and>
        native_application_at H au [] d (Pair_Term (sk_value t) (sk_value u)) I K \<and>
        native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E))"
  using sk_native_reduction_replay_iff by blast

theorem native_identity_composition_certificate:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>x. \<exists>H au I K root. native_package_at H pu [] Q \<and>
      native_application_at H au [] d
        (Pair_Term (sk_value (SK_App (SK_App sk_identity sk_identity) x)) (sk_value x)) I K \<and>
      native_replay_at H pu [] au [] root {} \<and> native_package_environment H pu []=E)"
  using sk_native_reductions_realized sk_identity_composition_reduces by blast

text \<open>
  The compiler constructs one finite closed package before any of its future
  arguments are chosen. Its three distinct native definition sites preserve
  exactly the external term, step, and finite-reduction relations. Every old
  artifact and binding, and the canonical program environment, are preserved.

  Reduction is equivalent to a closed native replay that recovers the same
  exact program and call and preserves its minimal judgment scope. The composed
  identity computation supplies a concrete family of compiled computations.
  This branch establishes SK adequacy; universality requires the separate
  translation of an independently defined computation model into SK.
\<close>

end
