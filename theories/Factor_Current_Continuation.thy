theory Factor_Current_Continuation
  imports Factor_Native_Continuation Factor_Amendment
begin

section \<open>Continuation uses the entry selected by its actual current frame\<close>

definition current_continues_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> selection_snapshot \<Rightarrow>
    structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d t I K.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      environment_formed F \<and> environment_included E F \<and>
      native_application_at F au ar d t I K \<and>
      native_continuation_at F pu pr au ar S T U B bu br)"

theorem current_continuation_at_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>
    environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    native_continuation_at F pu pr au ar S T U B bu br"
proof
  assume "current_continues_at C q F au ar S T U B bu br"
  then obtain A' l' G' p' E' pu' pr' Q e t I K where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' Q e"
    "environment_formed F" "environment_included E' F" "native_application_at F au ar e t I K"
    "native_continuation_at F pu' pr' au ar S T U B bu br"
    unfolding current_continues_at_def by blast
  have same: "E=E' \<and> pu=pu' \<and> pr=pr' \<and> d=e"
    using current_entry_scope_unique[OF current other(1)] by blast
  show "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    native_continuation_at F pu pr au ar S T U B bu br"
    using other(2-5) same by blast
next
  assume "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    native_continuation_at F pu pr au ar S T U B bu br"
  then show "current_continues_at C q F au ar S T U B bu br"
    using current unfolding current_continues_at_def by blast
qed

theorem current_continuation_with_reads:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>
    continuation_permission_invariant P d \<and> continuation_value_presents S T U B bu br t \<and>
    (d,t)\<in>positive_meaning P"
proof -
  have package: "native_package_at F pu pr P"
    by (rule current_entry_scope_future_application(1)[OF current formed included app])
  have exists: "\<exists>t I K. native_application_at F au ar d t I K" using app by blast
  show ?thesis
    by (simp only: current_continuation_at_scope[OF current] formed included exists
      native_continuation_with_reads[OF package app] simp_thms)
qed

theorem current_continuation_at_presentation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
    and invariant: "continuation_permission_invariant P d"
    and present: "continuation_value_presents S T U B bu br t"
  shows "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>factor_continues P d S T U B bu br"
    and "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>native_positive_holds F pu pr au ar"
proof -
  have exact: "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (simp only: current_continuation_with_reads[OF current formed included app] invariant present simp_thms)
  show "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>factor_continues P d S T U B bu br"
    by (simp only: exact factor_continuation_at_presentation[OF invariant present])
  show "current_continues_at C q F au ar S T U B bu br \<longleftrightarrow>native_positive_holds F pu pr au ar"
    by (simp only: exact current_entry_scope_future_application(4)[OF current formed included app])
qed

theorem current_continuation_requires_selected_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and app: "native_application_at F au ar e t I K"
    and permitted: "current_continues_at C q F au ar S T U B bu br"
  shows "e=d"
proof -
  obtain x J L where chosen: "native_application_at F au ar d x J L"
    using current_continuation_at_scope[OF current] permitted by blast
  show ?thesis using native_application_unique[OF app chosen] by blast
qed

theorem current_continuation_program_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_continues_at C q F au ar S T U B bu br"
  shows "environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
    native_continuation_at F pu pr au ar S T U B bu br \<and> native_positive_holds F pu pr au ar"
proof -
  obtain t I K where parts: "environment_formed F" "environment_included E F"
    "native_application_at F au ar d t I K" "native_continuation_at F pu pr au ar S T U B bu br"
    using current_continuation_at_scope[OF current] permitted by blast
  show ?thesis using parts current_entry_scope_future_application(1,2)[OF current parts(1-3)]
    native_continuation_truth[OF parts(4)] by blast
qed

theorem current_continuation_subject_unique:
  assumes first: "current_continues_at C q F au ar S T U B bu br"
    and second: "current_continues_at D r F au ar V W X M mu mr"
  shows "S=V \<and> T=W \<and> U=X \<and> B=M \<and> bu=mu \<and> br=mr"
proof -
  obtain pu pr qu qr where truth:
    "native_continuation_at F pu pr au ar S T U B bu br"
    "native_continuation_at F qu qr au ar V W X M mu mr"
    using first second unfolding current_continues_at_def by blast
  show ?thesis by (rule native_continuation_subject_unique[OF truth])
qed

section \<open>All future complete presentations use the same program\<close>

theorem current_continuation_application_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and invariant: "continuation_permission_invariant P d"
    and present: "continuation_value_presents S T U B bu br t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and> native_package_environment F pu pr=E \<and>
    (native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t) \<and>
    (current_continues_at C q F au [] S T U B bu br\<longleftrightarrow>factor_continues P d S T U B bu br) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w)"
proof -
  have closed: "closed_native_package_at E pu pr P" and fixed: "native_package_environment E pu pr=E"
    and member: "d\<in>system_definitions P" using current_entry_scope_closed[OF current] by auto
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  obtain F au I K where future: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t"
    "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w"
    using native_continuation_application_total[OF package member invariant present] by blast
  have permission: "current_continues_at C q F au [] S T U B bu br\<longleftrightarrow>factor_continues P d S T U B bu br"
    by (rule current_continuation_at_presentation(1)[OF current future(1,2,5) invariant present])
  have canonical: "native_package_environment F pu pr=E" using future(6) fixed by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
    (use future canonical permission in blast)
qed

theorem current_continuation_presentations_agree:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and first: "environment_formed F" "environment_included E F" "native_application_at F au ar d t I K"
    and second: "environment_formed M" "environment_included E M" "native_application_at M cu cr d w J L"
    and invariant: "continuation_permission_invariant P d"
    and left: "continuation_value_presents S T U B bu br t"
    and right: "continuation_value_presents S T U B bu br w"
  shows "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M pu pr cu cr"
    and "current_continues_at C q F au ar S T U B bu br\<longleftrightarrow>current_continues_at C q M cu cr S T U B bu br"
proof -
  show "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M pu pr cu cr"
    using current_entry_scope_future_application(3)[OF current first]
      current_entry_scope_future_application(3)[OF current second]
      continuation_permission_invariantD(1)[OF invariant left right] by blast
  show "current_continues_at C q F au ar S T U B bu br\<longleftrightarrow>current_continues_at C q M cu cr S T U B bu br"
    by (simp only: current_continuation_at_presentation(1)[OF current first invariant left]
      current_continuation_at_presentation(1)[OF current second invariant right])
qed

text \<open>
  The current purpose selects the continuation entry. Its exact program scope
  determines the active meaning, and an auxiliary true call cannot replace
  the selected call. The finite prospective dependency closure is the one
  already derived for this same entry; it is independent of the submitted
  before, proposal, after, and material values.

  This relation does not yet identify the supplied snapshots with the
  currentness frame's publication or assert transaction success. Those are
  separate joins. Companion currentness can select a different continuation
  entry under the original adoption policy. Neither use changes which entry
  judges amendment acceptance.
\<close>

end
