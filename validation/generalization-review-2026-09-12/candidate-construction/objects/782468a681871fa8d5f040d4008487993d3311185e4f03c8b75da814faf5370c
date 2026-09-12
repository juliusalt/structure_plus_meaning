theory Factor_Transition_Selection
  imports Factor_Continuation_Envelopes Factor_Current_Acceptance_Certificates
begin

section \<open>The replayed material fixes the actual successor selection\<close>

definition transition_selection_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "transition_selection_certificate C q K H X \<longleftrightarrow>
    (\<exists>S T U B bu br M mu mr r A l p E pu pr P d.
      continuation_envelope C q K S T U B bu br \<and> successor_material_at B bu br X M mu mr \<and>
      current_entry_scope_quoted_at X r A l H p E pu pr P d \<and>
      current_snapshot_at X r U \<and> transact S T (Applied U))"

theorem transition_selection_certificate_unique:
  assumes first: "transition_selection_certificate C q K G X"
    and second: "transition_selection_certificate D r K H Y"
  shows "G=H \<and> X=Y"
proof -
  obtain S T U B bu br M mu mr x A l p E pu pr P d where left:
    "continuation_envelope C q K S T U B bu br" "successor_material_at B bu br X M mu mr"
    "current_entry_scope_quoted_at X x A l G p E pu pr P d"
    using first unfolding transition_selection_certificate_def by blast
  obtain V W Z N nu nr L lu lr y A' l' p' E' qu qr Q e where right:
    "continuation_envelope D r K V W Z N nu nr" "successor_material_at N nu nr Y L lu lr"
    "current_entry_scope_quoted_at Y y A' l' H p' E' qu qr Q e"
    using second unfolding transition_selection_certificate_def by blast
  have frames: "X=Y" using continuation_envelope_material_unique[OF left(1,2) right(1,2)] by blast
  have other: "current_entry_scope_quoted_at X y A' l' H p' E' qu qr Q e" using right(3) frames by simp
  have cores: "G=H" using current_entry_scope_whole_unique[OF left(3) other] by blast
  show ?thesis using frames cores by blast
qed

theorem transition_selection_certificate_at_envelope:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and certificate: "transition_selection_certificate C q K H X"
  shows "transact S T (Applied U) \<and>
    (\<exists>M mu mr r A l p E pu pr P d.
      successor_material_at B bu br X M mu mr \<and>
      current_entry_scope_quoted_at X r A l H p E pu pr P d \<and>
      current_snapshot_at X r U)"
proof -
  obtain V W Z N nu nr M mu mr r A l p E pu pr P d where other:
    "continuation_envelope C q K V W Z N nu nr" "successor_material_at N nu nr X M mu mr"
    "current_entry_scope_quoted_at X r A l H p E pu pr P d"
    "current_snapshot_at X r Z" "transact V W (Applied Z)"
    using certificate unfolding transition_selection_certificate_def by blast
  have same: "S=V \<and> T=W \<and> U=Z \<and> B=N \<and> bu=nu \<and> br=nr"
    by (rule continuation_envelope_subject_unique[OF envelope other(1)])
  show ?thesis using other(2-5) same by blast
qed

theorem transition_selection_certificate_with_material:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and current: "current_entry_scope_quoted_at X r A l H p E pu pr P d"
    and after: "current_snapshot_at X r U"
  shows "transition_selection_certificate C q K H X \<longleftrightarrow> transact S T (Applied U)"
proof
  assume "transition_selection_certificate C q K H X"
  then show "transact S T (Applied U)" using transition_selection_certificate_at_envelope[OF envelope] by blast
next
  assume "transact S T (Applied U)"
  then show "transition_selection_certificate C q K H X"
    using envelope body current after unfolding transition_selection_certificate_def by blast
qed

theorem transition_selection_certificate_published:
  assumes predecessor: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and certificate: "transition_selection_certificate C q K H X"
  shows "current_snapshot_at C q S \<and> snapshot_formed S \<and> snapshot_lookup S l=Some G \<and>
    transact S T (Applied U) \<and>
    (\<exists>r A' m z F qu qr Q e.
      current_entry_scope_quoted_at X r A' m H z F qu qr Q e \<and>
      current_snapshot_at X r U \<and> snapshot_formed U \<and> snapshot_lookup U m=Some H)"
proof -
  have before: "current_snapshot_at C q S" "snapshot_formed S" "snapshot_lookup S l=Some G"
    using continuation_envelope_before[OF predecessor envelope] by auto
  obtain r A' m z F qu qr Q e where successor:
    "current_entry_scope_quoted_at X r A' m H z F qu qr Q e" "current_snapshot_at X r U"
    and trans: "transact S T (Applied U)"
    using transition_selection_certificate_at_envelope[OF envelope certificate] by blast
  have selected: "snapshot_formed U \<and> snapshot_lookup U m=Some H"
    by (rule current_entry_selected_snapshot[OF successor])
  show ?thesis using before successor trans selected by blast
qed

theorem transition_selection_certificate_conflict:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and conflict: "transact S T (Conflict observations)"
  shows "\<not>transition_selection_certificate C q K H X"
  using transition_selection_certificate_at_envelope[OF envelope] conflict
  by (auto simp: transact_applied_iff transact_conflict_iff)

theorem transition_selection_certificate_no_extra_change:
  assumes envelope: "continuation_envelope C q K S T U B bu br"
    and certificate: "transition_selection_certificate C q K H X"
    and outside: "l\<notin>changed_loci T"
  shows "snapshot_lookup U l=snapshot_lookup S l"
  using transition_selection_certificate_at_envelope[OF envelope certificate]
    successful_transaction_no_extra_change[OF _ outside] by blast

section \<open>The predecessor accepts the exact envelope containing that selection\<close>

definition current_transition_selection_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_transition_selection_at C q F au ar H K X \<longleftrightarrow>
    current_accepts_at C q F au ar H (Whole_Artifact K) \<and> transition_selection_certificate C q K H X"

theorem current_transition_selection_subject_unique:
  assumes first: "current_transition_selection_at C q F au ar G K X"
    and second: "current_transition_selection_at D r F au ar H L Y"
  shows "G=H \<and> K=L \<and> X=Y"
proof -
  have accepted: "current_accepts_at C q F au ar G (Whole_Artifact K)"
    "current_accepts_at D r F au ar H (Whole_Artifact L)"
    using first second by (auto simp: current_transition_selection_at_def)
  have same: "G=H \<and> K=L" using current_acceptance_subject_unique[OF accepted] by simp
  have certificates: "transition_selection_certificate C q K G X"
    "transition_selection_certificate D r K H Y"
    using first second same by (auto simp: current_transition_selection_at_def)
  show ?thesis using same transition_selection_certificate_unique[OF certificates] by blast
qed

theorem current_transition_selection_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_selection_at C q F au ar H K X"
  shows "environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
    native_positive_holds F pu pr au ar"
  using transition current_acceptance_program_scope[OF current]
  unfolding current_transition_selection_at_def by blast

theorem current_transition_selection_preserves_artifact:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_selection_at C q F au ar H K X"
    and old: "artifact_at E u R" and present: "artifact_at F u S"
  shows "R=S"
proof -
  have formed: "environment_formed F" and included: "environment_included E F"
    using current_transition_selection_program[OF current transition] by auto
  have retained: "artifact_at F u R" by (rule included_artifact[OF included old])
  show ?thesis by (rule environment_artifact_unique[OF formed retained present])
qed

theorem current_transition_selection_preserves_binding:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_selection_at C q F au ar H K X"
    and old: "binds_slot E u k v" and present: "binds_slot F u k w"
  shows "v=w"
proof -
  have formed: "environment_formed F" and included: "environment_included E F"
    using current_transition_selection_program[OF current transition] by auto
  have retained: "binds_slot F u k v" by (rule included_binding[OF included old])
  show ?thesis by (rule environment_binding_unique[OF formed retained present])
qed

section \<open>Retained acceptance proof preserves this same selection\<close>

definition certified_transition_selection ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_transition_selection C q R s H K X \<longleftrightarrow>
    current_acceptance_certificate C q R s H (Whole_Artifact K) \<and>
    transition_selection_certificate C q K H X"

theorem certified_transition_selection_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "certified_transition_selection C q R s H K X \<longleftrightarrow>
    current_transition_selection_at C q F au ar H K X"
  by (simp only: certified_transition_selection_def current_transition_selection_at_def
    current_acceptance_certificate_with_scope[OF current scope])

theorem certified_transition_selection_sound:
  assumes "certified_transition_selection C q R s H K X"
  shows "\<exists>F au ar. current_transition_selection_at C q F au ar H K X"
  using assms unfolding certified_transition_selection_def current_acceptance_certificate_def
    current_transition_selection_at_def by blast

theorem current_transition_selection_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_selection_at C q F au ar H K X"
  shows "\<exists>R M root. certified_transition_selection C q R [] H K X \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and>
    native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have accepted: "current_accepts_at C q F au ar H (Whole_Artifact K)"
    and selection: "transition_selection_certificate C q K H X"
    using transition by (auto simp: current_transition_selection_at_def)
  show ?thesis using current_acceptance_certification_total[OF current accepted] selection
    unfolding certified_transition_selection_def by blast
qed

theorem certified_transition_selection_subject_unique:
  assumes first: "certified_transition_selection C q R s G K X"
    and second: "certified_transition_selection D r R a H L Y"
  shows "s=a \<and> G=H \<and> K=L \<and> X=Y"
proof -
  have accepted: "current_acceptance_certificate C q R s G (Whole_Artifact K)"
    "current_acceptance_certificate D r R a H (Whole_Artifact L)"
    using first second by (auto simp: certified_transition_selection_def)
  have same: "s=a \<and> G=H \<and> K=L"
    using current_acceptance_certificate_subject_unique[OF accepted] by simp
  have certificates: "transition_selection_certificate C q K G X"
    "transition_selection_certificate D r K H Y"
    using first second same by (auto simp: certified_transition_selection_def)
  show ?thesis using same transition_selection_certificate_unique[OF certificates] by blast
qed

text \<open>
  The accepted target contains the continuation frame and closed replay.
  That call contains the complete material scope; its selected data contains
  the exact successor frame and supporting scope. The successor frame must
  select the same candidate generation under its own actual authority, purpose,
  program, and publication. That publication's snapshot must be the successful
  transaction result. Every field on this path is uniquely recovered.

  This selection component allows the successor's authority, locus, purpose,
  and program to differ. The companion constraint applies within the
  predecessor, where the continuation proof uses its exact program. Neither
  the acceptance invocation nor its proof can rebind an existing predecessor
  artifact or slot. Certification retains the original minimal acceptance
  scope and the exact selected frame.

  These joins do not yet define a complete legitimate amendment. They impose
  no assembly validity, complete dependency evidence, comparison-report
  admission, explicit historical predecessor edge, or cross-version
  interpretation check on the supporting material. Each remains a separate
  requirement of the full protocol. Proving an ordinary accepting call is
  different from proving that its policy enforces that complete protocol.
\<close>

end
