theory Factor_Current_Certificates
  imports Factor_Current_Continuation Factor_Replay_Scopes Factor_Certified_Continuation
begin

section \<open>The recorded proof belongs to the current continuation invocation\<close>

definition current_continuation_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_continuation_certificate C q R s S T U B bu br \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F au ar root.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      replay_scope_quoted_at R s F pu pr au ar root {} \<and>
      current_continues_at C q F au ar S T U B bu br)"

theorem current_continuation_certificate_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "current_continuation_certificate C q R s S T U B bu br \<longleftrightarrow>
    current_continues_at C q F au ar S T U B bu br"
proof
  assume "current_continuation_certificate C q R s S T U B bu br"
  then obtain H qu qr cu cr other where recorded:
    "replay_scope_quoted_at R s H qu qr cu cr other {}"
    "current_continues_at C q H cu cr S T U B bu br"
    unfolding current_continuation_certificate_def by blast
  have same: "H=F \<and> cu=au \<and> cr=ar" using replay_scope_whole_unique[OF recorded(1) scope] by blast
  show "current_continues_at C q F au ar S T U B bu br" using recorded(2) same by simp
next
  assume "current_continues_at C q F au ar S T U B bu br"
  then show "current_continuation_certificate C q R s S T U B bu br"
    using current scope unfolding current_continuation_certificate_def by blast
qed

theorem current_continuation_certificate_subject_unique:
  assumes first: "current_continuation_certificate C q R s S T U B bu br"
    and second: "current_continuation_certificate D r R a V W X M mu mr"
  shows "s=a \<and> S=V \<and> T=W \<and> U=X \<and> B=M \<and> bu=mu \<and> br=mr"
proof -
  obtain F pu pr au ar root where left: "replay_scope_quoted_at R s F pu pr au ar root {}"
    "current_continues_at C q F au ar S T U B bu br"
    using first unfolding current_continuation_certificate_def by blast
  obtain H qu qr cu cr other where right: "replay_scope_quoted_at R a H qu qr cu cr other {}"
    "current_continues_at D r H cu cr V W X M mu mr"
    using second unfolding current_continuation_certificate_def by blast
  have same: "s=a \<and> F=H \<and> au=cu \<and> ar=cr"
    using replay_scope_whole_unique[OF left(1) right(1)] by blast
  have other: "current_continues_at D r F au ar V W X M mu mr" using right(2) same by simp
  show ?thesis using same current_continuation_subject_unique[OF left(2) other] by blast
qed

theorem current_continuation_certificate_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "current_continuation_certificate C q R s S T U B bu br"
  shows "\<exists>F au ar root t I K.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu pr P \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au ar d t I K \<and>
    certified_continuation_at F pu pr au ar root S T U B bu br"
proof -
  obtain A' l' G' p' E' pu' pr' Q e F au ar root where recorded:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q e"
    "replay_scope_quoted_at R s F pu' pr' au ar root {}"
    "current_continues_at C q F au ar S T U B bu br"
    using certified unfolding current_continuation_certificate_def by blast
  have roots: "pu=pu' \<and> pr=pr'" using current_entry_scope_unique[OF current recorded(1)] by blast
  have scope: "replay_scope_quoted_at R s F pu pr au ar root {}" using recorded(2) roots by simp
  have replay: "native_replay_at F pu pr au ar root {}" using scope by (simp add: replay_scope_quoted_at_def)
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_continuation_at F pu pr au ar S T U B bu br"
    using current_continuation_program_scope[OF current recorded(3)] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_continuation_at_scope[OF current] recorded(3) by blast
  have proved: "certified_continuation_at F pu pr au ar root S T U B bu br"
    using program(5) replay by (simp add: certified_continuation_exact_join)
  show ?thesis using scope program app proved by blast
qed

theorem current_continuation_certificate_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "current_continuation_certificate C q R s S T U B bu br"
  shows "\<exists>F au ar root t I K H.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar d t I K \<and>
    native_schema_graph_at F root H \<and> schema_graph_derives (positioned_program P) H root d t {} \<and>
    continuation_permission_invariant P d \<and> continuation_value_presents S T U B bu br t"
proof -
  obtain F au ar root t I K where recorded:
    "replay_scope_quoted_at R s F pu pr au ar root {}"
    "native_package_at F pu pr P" "native_package_environment F pu pr=E"
    "native_application_at F au ar d t I K"
    "certified_continuation_at F pu pr au ar root S T U B bu br"
    using current_continuation_certificate_program[OF current certified] by blast
  have replay: "native_replay_at F pu pr au ar root {}"
    using recorded(1) by (simp add: replay_scope_quoted_at_def)
  obtain H where graph: "native_schema_graph_at F root H"
    using replay unfolding native_replay_at_def by blast
  have derived: "schema_graph_derives (positioned_program P) H root d t {}"
    using native_replay_with_reads[OF recorded(2,4) graph] replay by blast
  have fields: "continuation_permission_invariant P d" "continuation_value_presents S T U B bu br t"
    using certified_continuation_with_reads[OF recorded(2,4)] recorded(5) by blast+
  show ?thesis using recorded(1-4) graph derived fields by blast
qed

section \<open>Certification preserves the current entry and its complete call scope\<close>

theorem current_continuation_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_continues_at C q F au ar S T U B bu br"
  shows "\<exists>R H root. current_continuation_certificate C q R [] S T U B bu br \<and>
    replay_scope_quoted_at R [] H pu pr au ar root {} \<and>
    native_package_environment H pu pr=E \<and>
    native_judgment_environment H pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have program: "environment_formed F" "environment_included E F" "native_package_at F pu pr P"
    "native_package_environment F pu pr=E" "native_positive_holds F pu pr au ar"
    using current_continuation_program_scope[OF current permitted] by auto
  obtain t I K where app: "native_application_at F au ar d t I K"
    using current_continuation_at_scope[OF current] permitted by blast
  obtain R H root where recorded: "replay_scope_quoted_at R [] H pu pr au ar root {}"
    and reads: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and exact: "native_package_environment H pu pr=native_package_environment F pu pr"
      "native_judgment_environment H pu pr au ar=native_judgment_environment F pu pr au ar"
    using positive_judgment_has_recorded_replay[OF program(3) app program(5)] by blast
  have hf: "environment_formed H"
    using replay_scope_formed[OF recorded] by blast
  have canonical: "native_package_environment H pu pr=E" using exact(1) program(4) by simp
  have included: "environment_included E H"
    using native_package_environment_included[of H pu pr] canonical by simp
  have retained: "current_continues_at C q H au ar S T U B bu br"
    using permitted by (simp only: current_continuation_with_reads[OF current program(1,2) app]
      current_continuation_with_reads[OF current hf included reads(2)])
  have certified: "current_continuation_certificate C q R [] S T U B bu br"
    using current_continuation_certificate_with_scope[OF current recorded] retained by blast
  show ?thesis using certified recorded canonical exact(2) by blast
qed

theorem current_continuation_certificate_presentation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_continues P d S T U B bu br"
    and present: "continuation_value_presents S T U B bu br t"
  shows "\<exists>R F au root I K. current_continuation_certificate C q R [] S T U B bu br \<and>
    replay_scope_quoted_at R [] F pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au [] d t I K"
proof -
  have invariant: "continuation_permission_invariant P d" using permitted by (simp add: factor_continues_def)
  obtain H au I K where call: "native_application_at H au [] d t I K"
    and allowed: "current_continues_at C q H au [] S T U B bu br"
    using current_continuation_application_total[OF current invariant present] permitted by blast
  obtain R F root where certificate: "current_continuation_certificate C q R [] S T U B bu br"
    "replay_scope_quoted_at R [] F pu pr au [] root {}" "native_package_environment F pu pr=E"
    "native_judgment_environment F pu pr au []=native_judgment_environment H pu pr au []"
    using current_continuation_certification_total[OF current allowed] by blast
  have old_package: "native_package_at H pu pr P"
    using current_continuation_program_scope[OF current allowed] by blast
  have old_call: "native_application_at (native_judgment_environment H pu pr au []) au [] d t I K"
    by (rule native_judgment_environment_recovers(2)[OF old_package call])
  have kept: "native_application_at (native_judgment_environment F pu pr au []) au [] d t I K"
    using old_call certificate(4) by simp
  have ff: "environment_formed F"
    using replay_scope_formed[OF certificate(2)] by blast
  have app: "native_application_at F au [] d t I K"
    by (rule native_application_included[OF kept native_judgment_environment_included ff])
  show ?thesis using certificate(1-3) app by blast
qed

definition current_advance_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_advance_certificate C q R s S T U B bu br \<longleftrightarrow>
    transact S T (Applied U) \<and> current_continuation_certificate C q R s S T U B bu br"

lemma current_advance_certificate_conflict:
  assumes "transact S T (Conflict observations)"
  shows "\<not>current_advance_certificate C q R s S T U B bu br"
  using assms by (auto simp: current_advance_certificate_def transact_conflict_iff transact_applied_iff)

lemma current_advance_certificate_no_extra_change:
  assumes "current_advance_certificate C q R s S T U B bu br" "l\<notin>changed_loci T"
  shows "snapshot_lookup U l=snapshot_lookup S l"
  using assms successful_transaction_no_extra_change by (auto simp: current_advance_certificate_def)

text \<open>
  The proof's program site is the one recovered from the current frame.
  Quotation and closed replay cannot substitute a different program or a
  different entry. The whole artifact determines the quotation root and the
  complete continuation subject.

  Every current continuation has a recorded replay preserving its exact
  program and minimal call scope. The call's submitted material precedes this
  proof record; it need not contain a quotation of its own proof. Advancement
  still requires the independent successful transaction. A complete amendment
  must additionally bind the continuation selection, both publications, the
  successor frame, and the remaining certificate material.
\<close>

end
