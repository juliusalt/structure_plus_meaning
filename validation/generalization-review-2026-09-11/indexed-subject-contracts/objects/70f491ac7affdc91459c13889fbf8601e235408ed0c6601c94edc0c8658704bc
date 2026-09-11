theory Factor_Certified_Continuation
  imports Factor_Replay Factor_Native_Continuation
begin

section \<open>Replay certifies continuation under its actual program\<close>

definition certified_continuation_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "certified_continuation_at E pu pr au ar root S T U C cu cr \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
      native_replay_at E pu pr au ar root {})"

lemma certified_continuation_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "certified_continuation_at E pu pr au ar root S T U C cu cr\<longleftrightarrow>
    continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
    native_replay_at E pu pr au ar root {}"
proof
  assume "certified_continuation_at E pu pr au ar root S T U C cu cr"
  then obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "continuation_permission_invariant Q e" "continuation_value_presents S T U C cu cr v"
    "native_replay_at E pu pr au ar root {}"
    unfolding certified_continuation_at_def by blast
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
      native_replay_at E pu pr au ar root {}"
    using other(3-5) programs calls by simp
next
  assume "continuation_permission_invariant P d \<and> continuation_value_presents S T U C cu cr t \<and>
      native_replay_at E pu pr au ar root {}"
  then show "certified_continuation_at E pu pr au ar root S T U C cu cr"
    using package app unfolding certified_continuation_at_def by blast
qed

theorem certified_continuation_sound:
  assumes certified: "certified_continuation_at E pu pr au ar root S T U C cu cr"
  shows "native_continuation_at E pu pr au ar S T U C cu cr"
proof -
  obtain P d t I K where parts: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "continuation_permission_invariant P d" "continuation_value_presents S T U C cu cr t"
    "native_replay_at E pu pr au ar root {}"
    using certified unfolding certified_continuation_at_def by blast
  have positive: "native_positive_holds E pu pr au ar" by (rule native_replay_closed_sound[OF parts(5)])
  have meaning: "(d,t)\<in>positive_meaning P"
    using native_positive_holds_with_reads[OF parts(1,2)] positive by blast
  show ?thesis using parts(1-4) meaning unfolding native_continuation_at_def by blast
qed

theorem certified_continuation_exact_join:
  "certified_continuation_at E pu pr au ar root S T U C cu cr\<longleftrightarrow>
    native_continuation_at E pu pr au ar S T U C cu cr \<and> native_replay_at E pu pr au ar root {}"
proof
  assume certified: "certified_continuation_at E pu pr au ar root S T U C cu cr"
  show "native_continuation_at E pu pr au ar S T U C cu cr \<and> native_replay_at E pu pr au ar root {}"
    using certified_continuation_sound[OF certified] certified unfolding certified_continuation_at_def by blast
next
  assume "native_continuation_at E pu pr au ar S T U C cu cr \<and> native_replay_at E pu pr au ar root {}"
  then show "certified_continuation_at E pu pr au ar root S T U C cu cr"
    unfolding native_continuation_at_def certified_continuation_at_def by blast
qed

theorem certified_continuation_requires_admission:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and inadmissible: "\<not>continuation_permission_invariant P d"
  shows "\<not>certified_continuation_at E pu pr au ar root S T U C cu cr"
  using certified_continuation_with_reads[OF package app] inadmissible by blast

theorem certified_continuation_subject_unique:
  assumes first: "certified_continuation_at E pu pr au ar root S T U C cu cr"
    and second: "certified_continuation_at E qu qr au ar other V W X D du dr"
  shows "S=V \<and> T=W \<and> U=X \<and> C=D \<and> cu=du \<and> cr=dr"
  by (rule native_continuation_subject_unique[OF certified_continuation_sound[OF first]
      certified_continuation_sound[OF second]])

section \<open>Every continuation has a certificate preserving its exact judgment scope\<close>

theorem certified_continuation_exact_call_adequate:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_continuation_at E pu pr au ar S T U C cu cr\<longleftrightarrow>
    (\<exists>H root. certified_continuation_at H pu pr au ar root S T U C cu cr \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H)"
proof
  assume permitted: "native_continuation_at E pu pr au ar S T U C cu cr"
  have positive: "native_positive_holds E pu pr au ar" by (rule native_continuation_truth[OF permitted])
  obtain H root where target: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and replay: "native_replay_at H pu pr au ar root {}"
    and exact: "native_package_environment H pu pr=native_package_environment E pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
      "environment_included (native_judgment_environment E pu pr au ar) H"
    using native_replay_exact_call_adequate[OF package app] positive by blast
  have same: "native_continuation_at H pu pr au ar S T U C cu cr\<longleftrightarrow>
      native_continuation_at E pu pr au ar S T U C cu cr"
    by (simp only: native_continuation_with_reads[OF target] native_continuation_with_reads[OF package app])
  have certified: "certified_continuation_at H pu pr au ar root S T U C cu cr"
    using certified_continuation_exact_join[of H pu pr au ar root S T U C cu cr] same permitted replay by blast
  show "\<exists>H root. certified_continuation_at H pu pr au ar root S T U C cu cr \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H"
    using certified target exact by blast
next
  assume "\<exists>H root. certified_continuation_at H pu pr au ar root S T U C cu cr \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H"
  then obtain H root where target: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and certified: "certified_continuation_at H pu pr au ar root S T U C cu cr" by blast
  have permitted: "native_continuation_at H pu pr au ar S T U C cu cr"
    by (rule certified_continuation_sound[OF certified])
  show "native_continuation_at E pu pr au ar S T U C cu cr"
    using permitted by (simp only: native_continuation_with_reads[OF target] native_continuation_with_reads[OF package app])
qed

corollary native_continuation_certification_total:
  fixes E :: "local_address option artifact_environment"
  assumes permitted: "native_continuation_at E pu pr au ar S T U C cu cr"
  shows "\<exists>H root. certified_continuation_at H pu pr au ar root S T U C cu cr \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using permitted unfolding native_continuation_at_def by blast
  show ?thesis using certified_continuation_exact_call_adequate[OF reads] permitted by blast
qed

theorem certified_continuation_presentation_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and permitted: "factor_continues P d S T U C cu cr"
    and present: "continuation_value_presents S T U C cu cr t"
  shows "\<exists>H au root I K. certified_continuation_at H pu pr au [] root S T U C cu cr \<and>
    native_package_at H pu pr P \<and> native_application_at H au [] d t I K \<and>
    native_package_environment H pu pr=native_package_environment E pu pr"
proof -
  have invariant: "continuation_permission_invariant P d" using permitted by (simp add: factor_continues_def)
  have positive: "(d,t)\<in>positive_meaning P"
    using factor_continuation_at_presentation[OF invariant present] permitted by blast
  have member: "d\<in>system_definitions P"
    using schema_call_formed_target[OF positive_meaning_formed[OF positive]] by blast
  obtain F au I K where future: "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_continuation_at F pu pr au [] S T U C cu cr"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_continuation_application_total[OF package member invariant present] permitted by blast
  obtain H root where certificate: "certified_continuation_at H pu pr au [] root S T U C cu cr"
    "native_package_at H pu pr P" "native_application_at H au [] d t I K"
    "native_package_environment H pu pr=native_package_environment F pu pr"
    using certified_continuation_exact_call_adequate[OF future(1,2)] future(3) by blast
  have canonical: "native_package_environment H pu pr=native_package_environment E pu pr"
    using certificate(4) future(4) by simp
  show ?thesis
    by (rule exI[of _ H], rule exI[of _ au], rule exI[of _ root], rule exI[of _ I], rule exI[of _ K])
       (use certificate(1-3) canonical in blast)
qed

section \<open>Certified advancement retains the separate structural result\<close>

definition certified_advance_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "certified_advance_at E pu pr au ar root S T U C cu cr \<longleftrightarrow>
    transact S T (Applied U) \<and> certified_continuation_at E pu pr au ar root S T U C cu cr"

theorem certified_advance_exact_join:
  "certified_advance_at E pu pr au ar root S T U C cu cr\<longleftrightarrow>
    native_advance_at E pu pr au ar S T U C cu cr \<and> native_replay_at E pu pr au ar root {}"
  by (auto simp: certified_advance_at_def certified_continuation_exact_join native_advance_at_def)

theorem native_advance_certification_total:
  fixes E :: "local_address option artifact_environment"
  assumes advance: "native_advance_at E pu pr au ar S T U C cu cr"
  shows "\<exists>H root. certified_advance_at H pu pr au ar root S T U C cu cr \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  have trans: "transact S T (Applied U)" and permission: "native_continuation_at E pu pr au ar S T U C cu cr"
    using advance by (auto simp: native_advance_at_def)
  obtain H root where certified: "certified_continuation_at H pu pr au ar root S T U C cu cr"
    and exact: "native_package_environment H pu pr=native_package_environment E pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
    using native_continuation_certification_total[OF permission] by blast
  have joined: "certified_advance_at H pu pr au ar root S T U C cu cr"
    using trans certified by (simp add: certified_advance_at_def)
  show ?thesis using joined exact by blast
qed

text \<open>
  Replay establishes the ordinary continuation decision under its actual
  program. The separate invariance obligation still applies to every complete
  subject presentation. Every permitted call has a retained certificate with
  exactly the same program and minimal judgment environment. Every complete
  permitted future presentation also has an actual certified native call.

  Certified advancement additionally checks structural transaction success.
  The submitted material in the argument and this judgment's replay certificate
  have distinct roles. Neither its quotation nor this replay supplies an
  authority decision, a foundation amendment protocol, or native checking of
  policy-admission evidence.
\<close>

end
