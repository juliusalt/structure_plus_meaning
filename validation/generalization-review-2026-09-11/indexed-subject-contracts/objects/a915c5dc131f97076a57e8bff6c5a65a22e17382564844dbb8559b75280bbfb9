theory Factor_Certified_Authority
  imports Factor_Replay Factor_Native_Authority Factor_Authority_Scopes
begin

section \<open>Replay certifies the adoption decision under its actual program\<close>

definition certified_adoption_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "certified_adoption_at E pu pr au ar root A G p \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      adoption_permission_invariant P d \<and> adoption_value_presents A G p t \<and>
      native_replay_at E pu pr au ar root {})"

lemma certified_adoption_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "certified_adoption_at E pu pr au ar root A G p\<longleftrightarrow>
    adoption_permission_invariant P d \<and> adoption_value_presents A G p t \<and>
    native_replay_at E pu pr au ar root {}"
proof
  assume "certified_adoption_at E pu pr au ar root A G p"
  then obtain Q e v J L where other: "native_package_at E pu pr Q" "native_application_at E au ar e v J L"
    "adoption_permission_invariant Q e" "adoption_value_presents A G p v"
    "native_replay_at E pu pr au ar root {}"
    unfolding certified_adoption_at_def by blast
  have programs: "Q=P" by (rule native_package_unique[OF other(1) package])
  have calls: "e=d \<and> v=t" using native_application_unique[OF other(2) app] by blast
  show "adoption_permission_invariant P d \<and> adoption_value_presents A G p t \<and>
      native_replay_at E pu pr au ar root {}"
    using other(3-5) programs calls by simp
next
  assume "adoption_permission_invariant P d \<and> adoption_value_presents A G p t \<and>
      native_replay_at E pu pr au ar root {}"
  then show "certified_adoption_at E pu pr au ar root A G p"
    using package app unfolding certified_adoption_at_def by blast
qed

theorem certified_adoption_sound:
  assumes certified: "certified_adoption_at E pu pr au ar root A G p"
  shows "native_adoption_judgment_at E pu pr au ar A G p"
proof -
  obtain P d t I K where parts: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "adoption_permission_invariant P d" "adoption_value_presents A G p t"
    "native_replay_at E pu pr au ar root {}"
    using certified unfolding certified_adoption_at_def by blast
  have positive: "native_positive_holds E pu pr au ar" by (rule native_replay_closed_sound[OF parts(5)])
  have meaning: "(d,t)\<in>positive_meaning P"
    using native_positive_holds_with_reads[OF parts(1,2)] positive by blast
  show ?thesis using parts(1-4) meaning unfolding native_adoption_judgment_at_def by blast
qed

theorem certified_adoption_exact_join:
  "certified_adoption_at E pu pr au ar root A G p\<longleftrightarrow>
    native_adoption_judgment_at E pu pr au ar A G p \<and> native_replay_at E pu pr au ar root {}"
proof
  assume certified: "certified_adoption_at E pu pr au ar root A G p"
  show "native_adoption_judgment_at E pu pr au ar A G p \<and> native_replay_at E pu pr au ar root {}"
    using certified_adoption_sound[OF certified] certified unfolding certified_adoption_at_def by blast
next
  assume "native_adoption_judgment_at E pu pr au ar A G p \<and> native_replay_at E pu pr au ar root {}"
  then show "certified_adoption_at E pu pr au ar root A G p"
    unfolding native_adoption_judgment_at_def certified_adoption_at_def by blast
qed

theorem certified_adoption_requires_admission:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and inadmissible: "\<not>adoption_permission_invariant P d"
  shows "\<not>certified_adoption_at E pu pr au ar root A G p"
  using certified_adoption_with_reads[OF package app] inadmissible by blast

theorem certified_adoption_subject_unique:
  assumes first: "certified_adoption_at E pu pr au ar root A G p"
    and second: "certified_adoption_at E qu qr au ar other B H v"
  shows "A=B \<and> G=H \<and> p=v"
  by (rule native_adoption_subject_unique[OF certified_adoption_sound[OF first]
      certified_adoption_sound[OF second]])

section \<open>Every adoption has a certificate preserving its exact judgment scope\<close>

theorem certified_adoption_exact_call_adequate:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_adoption_judgment_at E pu pr au ar A G p\<longleftrightarrow>
    (\<exists>H root. certified_adoption_at H pu pr au ar root A G p \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H)"
proof
  assume adopted: "native_adoption_judgment_at E pu pr au ar A G p"
  have positive: "native_positive_holds E pu pr au ar" by (rule native_adoption_truth[OF adopted])
  obtain H root where target: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and replay: "native_replay_at H pu pr au ar root {}"
    and exact: "native_package_environment H pu pr=native_package_environment E pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
      "environment_included (native_judgment_environment E pu pr au ar) H"
    using native_replay_exact_call_adequate[OF package app] positive by blast
  have same: "native_adoption_judgment_at H pu pr au ar A G p\<longleftrightarrow>
      native_adoption_judgment_at E pu pr au ar A G p"
    by (simp only: native_adoption_with_reads[OF target] native_adoption_with_reads[OF package app])
  have certified: "certified_adoption_at H pu pr au ar root A G p"
    using certified_adoption_exact_join[of H pu pr au ar root A G p] same adopted replay by blast
  show "\<exists>H root. certified_adoption_at H pu pr au ar root A G p \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H"
    using certified target exact by blast
next
  assume "\<exists>H root. certified_adoption_at H pu pr au ar root A G p \<and>
      native_package_at H pu pr P \<and> native_application_at H au ar d t I K \<and>
      native_package_environment H pu pr=native_package_environment E pu pr \<and>
      native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar \<and>
      environment_included (native_judgment_environment E pu pr au ar) H"
  then obtain H root where target: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and certified: "certified_adoption_at H pu pr au ar root A G p" by blast
  have adopted: "native_adoption_judgment_at H pu pr au ar A G p"
    by (rule certified_adoption_sound[OF certified])
  show "native_adoption_judgment_at E pu pr au ar A G p"
    using adopted by (simp only: native_adoption_with_reads[OF target] native_adoption_with_reads[OF package app])
qed

corollary native_adoption_certification_total:
  fixes E :: "local_address option artifact_environment"
  assumes adopted: "native_adoption_judgment_at E pu pr au ar A G p"
  shows "\<exists>H root. certified_adoption_at H pu pr au ar root A G p \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using adopted unfolding native_adoption_judgment_at_def by blast
  show ?thesis using certified_adoption_exact_call_adequate[OF reads] adopted by blast
qed

theorem certified_adoption_presentation_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and adopted: "factor_adopts P d A G p"
    and present: "adoption_value_presents A G p t"
  shows "\<exists>H au root I K. certified_adoption_at H pu pr au [] root A G p \<and>
    native_package_at H pu pr P \<and> native_application_at H au [] d t I K \<and>
    native_package_environment H pu pr=native_package_environment E pu pr"
proof -
  have invariant: "adoption_permission_invariant P d" using adopted by (simp add: factor_adopts_def)
  have positive: "(d,t)\<in>positive_meaning P"
    using factor_adoption_at_presentation[OF invariant present] adopted by blast
  have member: "d\<in>system_definitions P"
    using schema_call_formed_target[OF positive_meaning_formed[OF positive]] by blast
  obtain F au I K where future: "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_adoption_judgment_at F pu pr au [] A G p"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_adoption_application_total[OF package member invariant present] adopted by blast
  obtain H root where certificate: "certified_adoption_at H pu pr au [] root A G p"
    "native_package_at H pu pr P" "native_application_at H au [] d t I K"
    "native_package_environment H pu pr=native_package_environment F pu pr"
    using certified_adoption_exact_call_adequate[OF future(1,2)] future(3) by blast
  have canonical: "native_package_environment H pu pr=native_package_environment E pu pr"
    using certificate(4) future(4) by simp
  show ?thesis
    by (rule exI[of _ H], rule exI[of _ au], rule exI[of _ root], rule exI[of _ I], rule exI[of _ K])
       (use certificate(1-3) canonical in blast)
qed

section \<open>Currentness adds the same exact publication frame\<close>

definition certified_current_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> exact_target \<Rightarrow> 'v artifact_environment \<Rightarrow> 'v \<Rightarrow> local_address \<Rightarrow>
    exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "certified_current_at E pu pr au ar proof_root A F v root l G p \<longleftrightarrow>
    native_current E pu pr au ar A F v root l G p \<and> native_replay_at E pu pr au ar proof_root {}"

theorem certified_current_exact_join:
  "certified_current_at E pu pr au ar proof_root A F v root l G p\<longleftrightarrow>
    certified_adoption_at E pu pr au ar proof_root A G p \<and>
    (\<exists>P. publication_environment_closed F v root P \<and> snapshot_lookup (publication_snapshot P) l=Some G)"
  by (auto simp: certified_current_at_def certified_adoption_exact_join native_current_def)

theorem native_current_certification_total:
  fixes E :: "local_address option artifact_environment"
  assumes current: "native_current E pu pr au ar A F v root l G p"
  shows "\<exists>H proof_root. certified_current_at H pu pr au ar proof_root A F v root l G p \<and>
    native_package_environment H pu pr=native_package_environment E pu pr \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  have adopted: "native_adoption_judgment_at E pu pr au ar A G p"
    and frame: "\<exists>P. publication_environment_closed F v root P \<and>
      snapshot_lookup (publication_snapshot P) l=Some G"
    using current by (auto simp: native_current_def)
  obtain H proof_root where certified: "certified_adoption_at H pu pr au ar proof_root A G p"
    and exact: "native_package_environment H pu pr=native_package_environment E pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment E pu pr au ar"
    using native_adoption_certification_total[OF adopted] by blast
  have current_cert: "certified_current_at H pu pr au ar proof_root A F v root l G p"
    using certified_current_exact_join[of H pu pr au ar proof_root A F v root l G p] certified frame by blast
  show ?thesis using current_cert exact by blast
qed

text \<open>
  A closed replay establishes the ordinary adoption decision. Its exact join
  retains the separate presentation-invariance admission condition. Changing
  proof roots cannot change the subject, and a proof of a serialized call
  cannot substitute for admission over all subject presentations.

  Every adopted call and every admitted future presentation has a retained
  certificate under the same exact program environment. Certifying an existing
  call also preserves its entire minimal judgment environment. Currentness
  retains its separate closed publication frame. These certificates concern
  the adoption decision; generation-cause validity is a different judgment.
\<close>

end
