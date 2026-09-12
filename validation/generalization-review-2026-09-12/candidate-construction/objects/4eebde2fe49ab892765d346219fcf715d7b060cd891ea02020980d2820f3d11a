theory Factor_Current_Acceptance_Certificates
  imports Factor_Native_Amendment Factor_Replay_Scopes
begin

section \<open>Closed replay of the predecessor's actual acceptance invocation\<close>

definition current_acceptance_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_target \<Rightarrow> bool" where
  "current_acceptance_certificate C q R s H c \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F au ar root.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      replay_scope_quoted_at R s F pu pr au ar root {} \<and> current_accepts_at C q F au ar H c)"

theorem current_acceptance_certificate_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "current_acceptance_certificate C q R s H c \<longleftrightarrow> current_accepts_at C q F au ar H c"
proof
  assume "current_acceptance_certificate C q R s H c"
  then obtain M qu qr bu br other where recorded:
    "replay_scope_quoted_at R s M qu qr bu br other {}" "current_accepts_at C q M bu br H c"
    unfolding current_acceptance_certificate_def by blast
  have same: "M=F \<and> bu=au \<and> br=ar" using replay_scope_whole_unique[OF recorded(1) scope] by blast
  show "current_accepts_at C q F au ar H c" using recorded(2) same by simp
next
  assume "current_accepts_at C q F au ar H c"
  then show "current_acceptance_certificate C q R s H c"
    using current scope unfolding current_acceptance_certificate_def by blast
qed

theorem current_acceptance_certificate_subject_unique:
  assumes first: "current_acceptance_certificate C q R s G c"
    and second: "current_acceptance_certificate D r R a H k"
  shows "s=a \<and> G=H \<and> c=k"
proof -
  obtain F pu pr au ar root where left: "replay_scope_quoted_at R s F pu pr au ar root {}"
    "current_accepts_at C q F au ar G c"
    using first unfolding current_acceptance_certificate_def by blast
  obtain M qu qr bu br other where right: "replay_scope_quoted_at R a M qu qr bu br other {}"
    "current_accepts_at D r M bu br H k"
    using second unfolding current_acceptance_certificate_def by blast
  have same: "s=a \<and> F=M \<and> au=bu \<and> ar=br" using replay_scope_whole_unique[OF left(1) right(1)] by blast
  have accepted: "current_accepts_at D r F au ar H k" using right(2) same by simp
  show ?thesis using same current_acceptance_subject_unique[OF left(2) accepted] by blast
qed

theorem current_acceptance_certificate_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "current_acceptance_certificate C q R s H c"
  shows "\<exists>F au ar root t I K.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu pr P \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au ar d t I K \<and>
    current_accepts_at C q F au ar H c"
proof -
  obtain A' l' G' p' E' pu' pr' Q e F au ar root where recorded:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q e"
    "replay_scope_quoted_at R s F pu' pr' au ar root {}" "current_accepts_at C q F au ar H c"
    using certificate unfolding current_acceptance_certificate_def by blast
  have roots: "pu=pu' \<and> pr=pr'" using current_entry_scope_unique[OF current recorded(1)] by blast
  have scope: "replay_scope_quoted_at R s F pu pr au ar root {}" using recorded(2) roots by simp
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E"
    using current_acceptance_program_scope[OF current recorded(3)] by auto
  obtain e t I K where app: "native_application_at F au ar e t I K"
    using recorded(3) unfolding current_accepts_at_def by blast
  have selected: "e=d" by (rule current_acceptance_requires_selected_entry[OF current app recorded(3)])
  show ?thesis using scope program app selected recorded(3) by blast
qed

theorem current_acceptance_certificate_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v tail"
    and certificate: "current_acceptance_certificate C q R s H c"
  shows "\<exists>F au ar root t I K J.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar d t I K \<and>
    native_schema_graph_at F root J \<and> schema_graph_derives (positioned_program P) J root d t {} \<and>
    amendment_permission_invariant P d \<and> amendment_value_presents D qu qr bu br N v tail H c t"
proof -
  obtain F au ar root t I K where recorded:
    "replay_scope_quoted_at R s F pu pr au ar root {}"
    "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_application_at F au ar d t I K"
    "current_accepts_at C q F au ar H c"
    using current_acceptance_certificate_program[OF current certificate] by blast
  have replay: "native_replay_at F pu pr au ar root {}" using recorded(1) by (simp add: replay_scope_quoted_at_def)
  obtain J where graph: "native_schema_graph_at F root J" using replay unfolding native_replay_at_def by blast
  have derivation: "schema_graph_derives (positioned_program P) J root d t {}"
    using native_replay_with_reads[OF recorded(4,6) graph] replay by blast
  have fields: "amendment_permission_invariant P d" "amendment_value_presents D qu qr bu br N v tail H c t"
    using current_acceptance_with_reads[OF current frame recorded(2,3,6)] recorded(7) by blast+
  show ?thesis using recorded(1,4-6) graph derivation fields by blast
qed

section \<open>Every acceptance has a record with its original complete call scope\<close>

theorem current_acceptance_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and accepted: "current_accepts_at C q F au ar H c"
  shows "\<exists>R M root. current_acceptance_certificate C q R [] H c \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and>
    native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_positive_holds F pu pr au ar"
    using current_acceptance_program_scope[OF current accepted] by auto
  obtain e t I K where call: "native_application_at F au ar e t I K"
    using accepted unfolding current_accepts_at_def by blast
  have selected: "e=d" by (rule current_acceptance_requires_selected_entry[OF current call accepted])
  have app: "native_application_at F au ar d t I K" using call selected by simp
  obtain D qu qr bu br N v tail where scope:
    "current_scope_quoted_at C q D qu qr bu br A N v tail l G p"
    using current_entry_scope_frame[OF current] by blast
  have frame: "current_frame_quoted_at C q D qu qr bu br N v tail"
    using scope by (simp add: current_scope_quoted_at_def)
  obtain R M root where recorded: "replay_scope_quoted_at R [] M pu pr au ar root {}"
    and reads: "native_package_at M pu pr P" "native_application_at M au ar d t I K"
    and exact: "native_package_environment M pu pr=native_package_environment F pu pr"
      "native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
    using positive_judgment_has_recorded_replay[OF program(3) app program(5)] by blast
  have mf: "environment_formed M" using replay_scope_formed[OF recorded] by blast
  have canonical: "native_package_environment M pu pr=E" using exact(1) program(4) by simp
  have included: "environment_included E M"
    using native_package_environment_included[of M pu pr] canonical by simp
  have retained: "current_accepts_at C q M au ar H c"
    using accepted by (simp only: current_acceptance_with_reads[OF current frame program(1,2) app]
      current_acceptance_with_reads[OF current frame mf included reads(2)])
  have certificate: "current_acceptance_certificate C q R [] H c"
    using current_acceptance_certificate_with_scope[OF current recorded] retained by blast
  show ?thesis using certificate recorded canonical exact(2) by blast
qed

theorem current_acceptance_certificate_presentation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v tail"
    and permitted: "factor_accepts P d D qu qr bu br N v tail H c"
    and present: "amendment_value_presents D qu qr bu br N v tail H c t"
  shows "\<exists>R F au root I K. current_acceptance_certificate C q R [] H c \<and>
    replay_scope_quoted_at R [] F pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au [] d t I K"
proof -
  have invariant: "amendment_permission_invariant P d" using permitted by (simp add: factor_accepts_def)
  obtain M au I K where app: "native_application_at M au [] d t I K"
    and allowed: "current_accepts_at C q M au [] H c"
    using current_acceptance_application_total[OF current frame invariant present] permitted by blast
  obtain R F root where certificate: "current_acceptance_certificate C q R [] H c"
    "replay_scope_quoted_at R [] F pu pr au [] root {}" "native_package_environment F pu pr=E"
    "native_judgment_environment F pu pr au []=native_judgment_environment M pu pr au []"
    using current_acceptance_certification_total[OF current allowed] by blast
  have package: "native_package_at M pu pr P" using current_acceptance_program_scope[OF current allowed] by blast
  have original: "native_application_at (native_judgment_environment M pu pr au []) au [] d t I K"
    by (rule native_judgment_environment_recovers(2)[OF package app])
  have kept: "native_application_at (native_judgment_environment F pu pr au []) au [] d t I K"
    using original certificate(4) by simp
  have ff: "environment_formed F" using replay_scope_formed[OF certificate(2)] by blast
  have call: "native_application_at F au [] d t I K"
    by (rule native_application_included[OF kept native_judgment_environment_included ff])
  show ?thesis using certificate(1-3) call by blast
qed

text \<open>
  The proof records the program site recovered from the actual current frame.
  Its closed native graph derives the amendment call at that frame's selected
  entry. The call contains both predecessor scopes, the complete candidate,
  and the exact submitted certificate target. The successor contributes data
  to this argument and no clauses to the derivation.

  Every acceptance can acquire such a record while retaining its exact
  program and minimal judgment environment. Every permitted complete argument
  has an actual recorded call with that argument. The whole proof record fixes
  the candidate and certificate; it need not fix the presentation artifact
  used to display the current frame. Acceptance and its proof remain distinct
  from the checks required of the submitted transition material.
\<close>

end
