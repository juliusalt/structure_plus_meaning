theory Factor_Transition_Accounts
  imports Factor_Transition_Selection Factor_Predecessor_Assembly Factor_Assembly_Support
begin

section \<open>Accepted material retains the actual assembly proof and historical edge\<close>

definition transition_account_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "transition_account_certificate C q K H X \<longleftrightarrow>
    transition_selection_certificate C q K H X \<and>
    (\<exists>A l G p E pu pr P d S T U B bu br M mu mr D r R s N nu nr xs B0 W Z.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and> G\<in>fset (generation_predecessors H) \<and>
      continuation_envelope C q K S T U B bu br \<and> successor_material_at B bu br X M mu mr \<and>
      assembly_support_at M mu mr D R N nu nr \<and>
      predecessor_assembly_certificate C q D r R s H xs B0 W Z)"

lemma transition_account_selection:
  assumes "transition_account_certificate C q K H X"
  shows "transition_selection_certificate C q K H X"
  using assms by (simp add: transition_account_certificate_def)

theorem transition_account_material_unique:
  assumes left: "continuation_envelope C q K S T U B bu br"
    "successor_material_at B bu br X M mu mr" "assembly_support_at M mu mr D R N nu nr"
    and right: "continuation_envelope C' q' K S' T' U' B' bu' br'"
    "successor_material_at B' bu' br' X' M' mu' mr'" "assembly_support_at M' mu' mr' D' R' N' nu' nr'"
  shows "X=X' \<and> D=D' \<and> R=R' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
proof -
  have same: "X=X' \<and> M=M' \<and> mu=mu' \<and> mr=mr'"
    by (rule continuation_envelope_material_unique[OF left(1,2) right(1,2)])
  have support: "assembly_support_at M mu mr D' R' N' nu' nr'" using right(3) same by simp
  show ?thesis using same assembly_support_at_unique[OF left(3) support] by blast
qed

theorem transition_account_history:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "transition_account_certificate C q K H X"
  shows "G\<in>fset (generation_predecessors H)" "size G<size H" "G\<noteq>H"
proof -
  obtain A' l' G' p' E' qu qr Q e where selected:
    "current_entry_scope_quoted_at C q A' l' G' p' E' qu qr Q e"
    and history: "G'\<in>fset (generation_predecessors H)"
    using certificate unfolding transition_account_certificate_def by blast
  have same: "G=G'" using current_entry_scope_unique[OF current selected] by blast
  show edge: "G\<in>fset (generation_predecessors H)" using history same by simp
  have predecessor: "(G,H)\<in>predecessor_edges" using edge by (simp add: predecessor_edges_def)
  show decrease: "size G<size H" by (rule predecessor_size_decreases[OF predecessor])
  show "G\<noteq>H" using decrease by auto
qed

theorem transition_account_with_material:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
  shows "transition_account_certificate C q K H X \<longleftrightarrow>
    transition_selection_certificate C q K H X \<and> G\<in>fset (generation_predecessors H) \<and>
    (\<exists>r s xs B0 W Z. predecessor_assembly_certificate C q D r R s H xs B0 W Z)"
proof
  assume certificate: "transition_account_certificate C q K H X"
  obtain S' T' U' B' bu' br' M' mu' mr' D' r R' s N' nu' nr' xs B0 W Z where fields:
    "continuation_envelope C q K S' T' U' B' bu' br'"
    "successor_material_at B' bu' br' X M' mu' mr'" "assembly_support_at M' mu' mr' D' R' N' nu' nr'"
    "predecessor_assembly_certificate C q D' r R' s H xs B0 W Z"
    using certificate unfolding transition_account_certificate_def by blast
  have same: "D=D' \<and> R=R'"
    using transition_account_material_unique[OF envelope body support fields(1-3)] by blast
  have actual: "predecessor_assembly_certificate C q D r R s H xs B0 W Z" using fields(4) same by simp
  show "transition_selection_certificate C q K H X \<and> G\<in>fset (generation_predecessors H) \<and>
    (\<exists>r s xs B0 W Z. predecessor_assembly_certificate C q D r R s H xs B0 W Z)"
    using transition_account_selection[OF certificate] transition_account_history(1)[OF current certificate] actual by blast
next
  assume parts: "transition_selection_certificate C q K H X \<and> G\<in>fset (generation_predecessors H) \<and>
    (\<exists>r s xs B0 W Z. predecessor_assembly_certificate C q D r R s H xs B0 W Z)"
  then obtain r s xs B0 W Z where selected: "transition_selection_certificate C q K H X"
    and history: "G\<in>fset (generation_predecessors H)"
    and assembled: "predecessor_assembly_certificate C q D r R s H xs B0 W Z" by blast
  show "transition_account_certificate C q K H X" unfolding transition_account_certificate_def
    by (rule conjI[OF selected], rule exI[of _ A], rule exI[of _ l], rule exI[of _ G], rule exI[of _ p],
        rule exI[of _ E], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ P], rule exI[of _ d],
        rule exI[of _ S], rule exI[of _ T], rule exI[of _ U], rule exI[of _ B], rule exI[of _ bu],
        rule exI[of _ br], rule exI[of _ M], rule exI[of _ mu], rule exI[of _ mr], rule exI[of _ D],
        rule exI[of _ r], rule exI[of _ R], rule exI[of _ s], rule exI[of _ N], rule exI[of _ nu],
        rule exI[of _ nr], rule exI[of _ xs], rule exI[of _ B0], rule exI[of _ W], rule exI[of _ Z])
       (use current history envelope body support assembled in blast)
qed

theorem transition_account_unique:
  assumes "transition_account_certificate C q K G X" "transition_account_certificate D r K H Y"
  shows "G=H \<and> X=Y"
  by (rule transition_selection_certificate_unique[OF transition_account_selection[OF assms(1)]
    transition_account_selection[OF assms(2)]])

theorem transition_account_recorded_cause:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and body: "successor_material_at B bu br X M mu mr"
    and support: "assembly_support_at M mu mr D R N nu nr"
    and certificate: "transition_account_certificate C q K H X"
    and gen: "generation_at V hu hr H"
  shows "\<exists>r s xs B0 W Z F au ar root.
    predecessor_assembly_certificate C q D r R s H xs B0 W Z \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and> native_package_environment F pu pr=E \<and>
    certified_recorded_cause_at V hu hr H F root xs B0 W Z \<and>
    generation_payload H=Whole_Artifact Z \<and>
    K2 (construction_assembly xs B0 W) \<and> Z=assembly_output (construction_assembly xs B0 W)"
proof -
  obtain r s xs B0 W Z where complete: "predecessor_assembly_certificate C q D r R s H xs B0 W Z"
    using certificate by (simp only: transition_account_with_material[OF current envelope body support]; blast)
  have account: "generation_payload H=Whole_Artifact Z"
    "K2 (construction_assembly xs B0 W)" "Z=assembly_output (construction_assembly xs B0 W)"
    using predecessor_assembly_certificate_account[OF complete] by auto
  show ?thesis using complete account predecessor_assembly_certificate_recorded_cause[OF current complete gen] by blast
qed

theorem transition_account_published:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
    and certificate: "transition_account_certificate C q K H X"
  shows "current_snapshot_at C q S \<and> snapshot_formed S \<and> snapshot_lookup S l=Some G \<and>
    transact S T (Applied U) \<and> G\<in>fset (generation_predecessors H) \<and>
    (\<exists>r A' m z F qu qr Q e.
      current_entry_scope_quoted_at X r A' m H z F qu qr Q e \<and>
      current_snapshot_at X r U \<and> snapshot_formed U \<and> snapshot_lookup U m=Some H)"
  using transition_selection_certificate_published[OF current envelope transition_account_selection[OF certificate]]
    transition_account_history(1)[OF current certificate] by blast

theorem transition_account_unchanged_generation_rejected:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "\<not>transition_account_certificate C q K G X"
  using transition_account_history(3)[OF current] by blast

theorem predecessor_assembly_support_total:
  assumes certificate: "predecessor_assembly_certificate C q D a R b H xs B0 W Z"
    and successor: "current_entry_scope_quoted_at X r A l H p E pu pr P d"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M B. assembly_support_at M None [] D R N nu nr \<and>
    successor_material_at B None [] X M None []"
proof -
  obtain A' l' G' p' E' qu qr Q e F au ar root where recorded:
    "current_entry_scope_quoted_at D a A' l' G' p' E' qu qr Q e"
    "replay_scope_quoted_at R b F qu qr au ar root {}"
    using certificate unfolding predecessor_assembly_certificate_def current_construction_certificate_def by blast
  have df: "exact_formed D" using current_entry_scope_formed[OF recorded(1)] by blast
  have rf: "exact_formed R" using replay_scope_formed[OF recorded(2)] by blast
  have xf: "exact_formed X" using current_entry_scope_formed[OF successor] by blast
  obtain M where support: "assembly_support_at M None [] D R N nu nr"
    using assembly_support_total[OF df rf remainder] by blast
  have mf: "environment_formed M" and site: "(None,[])\<in>environment_positions M"
    using assembly_support_at_formed[OF support] by auto
  obtain B where body: "successor_material_at B None [] X M None []"
    using successor_material_total[OF xf mf site] by blast
  show ?thesis using support body by blast
qed

section \<open>The actual amendment call accepts this same accounted candidate\<close>

definition current_transition_account_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_transition_account_at C q F au ar H K X \<longleftrightarrow>
    current_accepts_at C q F au ar H (Whole_Artifact K) \<and> transition_account_certificate C q K H X"

theorem current_transition_account_selection:
  assumes "current_transition_account_at C q F au ar H K X"
  shows "current_transition_selection_at C q F au ar H K X"
  using assms transition_account_selection
  unfolding current_transition_account_at_def current_transition_selection_at_def by blast

theorem current_transition_account_subject_unique:
  assumes "current_transition_account_at C q F au ar G K X" "current_transition_account_at D r F au ar H L Y"
  shows "G=H \<and> K=L \<and> X=Y"
  by (rule current_transition_selection_subject_unique[OF current_transition_account_selection[OF assms(1)]
    current_transition_account_selection[OF assms(2)]])

definition certified_transition_account ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_transition_account C q R s H K X \<longleftrightarrow>
    current_acceptance_certificate C q R s H (Whole_Artifact K) \<and> transition_account_certificate C q K H X"

theorem certified_transition_account_with_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "certified_transition_account C q R s H K X \<longleftrightarrow>
    current_transition_account_at C q F au ar H K X"
  by (simp only: certified_transition_account_def current_transition_account_at_def
    current_acceptance_certificate_with_scope[OF current scope])

theorem certified_transition_account_sound:
  assumes "certified_transition_account C q R s H K X"
  shows "\<exists>F au ar. current_transition_account_at C q F au ar H K X"
  using assms unfolding certified_transition_account_def current_acceptance_certificate_def
    current_transition_account_at_def by blast

theorem current_transition_account_certification_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and transition: "current_transition_account_at C q F au ar H K X"
  shows "\<exists>R M root. certified_transition_account C q R [] H K X \<and>
    replay_scope_quoted_at R [] M pu pr au ar root {} \<and> native_package_environment M pu pr=E \<and>
    native_judgment_environment M pu pr au ar=native_judgment_environment F pu pr au ar"
proof -
  have accepted: "current_accepts_at C q F au ar H (Whole_Artifact K)"
    and account: "transition_account_certificate C q K H X"
    using transition by (auto simp: current_transition_account_at_def)
  show ?thesis using current_acceptance_certification_total[OF current accepted] account
    unfolding certified_transition_account_def by blast
qed

theorem certified_transition_account_subject_unique:
  assumes first: "certified_transition_account C q R s G K X"
    and second: "certified_transition_account D r R a H L Y"
  shows "s=a \<and> G=H \<and> K=L \<and> X=Y"
proof -
  have accepted: "current_acceptance_certificate C q R s G (Whole_Artifact K)"
    "current_acceptance_certificate D r R a H (Whole_Artifact L)"
    using first second by (auto simp: certified_transition_account_def)
  have same: "s=a \<and> G=H \<and> K=L" using current_acceptance_certificate_subject_unique[OF accepted] by simp
  have certificates: "transition_account_certificate C q K G X" "transition_account_certificate D r K H Y"
    using first second same by (auto simp: certified_transition_account_def)
  show ?thesis using same transition_account_unique[OF certificates] by blast
qed

text \<open>
  The accepted envelope fixes the construction frame, its separate whole
  replay record, and the remaining complete supporting scope. That exact
  construction is admitted at a companion entry of the predecessor program.
  Its minimal call scope must be the candidate's recorded cause, and its
  output must be the candidate's payload.

  The actual current generation must also occur in the candidate's direct
  predecessor family. This is a separate historical condition; it neither
  reconstructs a construction input nor supplies a semantic dependency.
  The strict size theorem excludes selecting the same generation as its
  own successor. The exact successor frame and successful publication remain
  bound through the earlier selection component.

  Current acceptance and its closed replay retain the same accounted
  candidate and predecessor program. The remaining supporting scope still
  needs complete dependency evidence, comparison admission, and cross-version
  interpretation. This component does not claim a complete amendment protocol
  or prove that an ordinary accepting policy enforces these requirements.
\<close>

end
