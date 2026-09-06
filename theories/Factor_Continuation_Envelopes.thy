theory Factor_Continuation_Envelopes
  imports Factor_Predecessor_Continuation Factor_Transition_Values
begin

section \<open>The submitted whole artifact binds the continuation frame and proof\<close>

definition continuation_envelope ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "continuation_envelope C q K S T U B bu br \<longleftrightarrow>
    (\<exists>k D r R s. artifact_pair_quoted_at K k D R \<and>
      predecessor_continuation_certificate C q D r R s S T U B bu br)"

theorem continuation_envelope_with_pair:
  assumes pair: "artifact_pair_quoted_at K k D R"
  shows "continuation_envelope C q K S T U B bu br \<longleftrightarrow>
    (\<exists>r s. predecessor_continuation_certificate C q D r R s S T U B bu br)"
proof
  assume "continuation_envelope C q K S T U B bu br"
  then obtain a E h Q z where other: "artifact_pair_quoted_at K a E Q"
    "predecessor_continuation_certificate C q E h Q z S T U B bu br"
    unfolding continuation_envelope_def by blast
  have same: "D=E \<and> R=Q" using artifact_pair_whole_unique[OF pair other(1)] by blast
  show "\<exists>r s. predecessor_continuation_certificate C q D r R s S T U B bu br"
    using other(2) same by blast
next
  assume "\<exists>r s. predecessor_continuation_certificate C q D r R s S T U B bu br"
  then show "continuation_envelope C q K S T U B bu br"
    using pair unfolding continuation_envelope_def by blast
qed

theorem continuation_envelope_subject_unique:
  assumes first: "continuation_envelope C q K S T U B bu br"
    and second: "continuation_envelope D r K V W X M mu mr"
  shows "S=V \<and> T=W \<and> U=X \<and> B=M \<and> bu=mu \<and> br=mr"
proof -
  obtain k E h R s where left: "artifact_pair_quoted_at K k E R"
    "predecessor_continuation_certificate C q E h R s S T U B bu br"
    using first unfolding continuation_envelope_def by blast
  obtain a F i Q z where right: "artifact_pair_quoted_at K a F Q"
    "predecessor_continuation_certificate D r F i Q z V W X M mu mr"
    using second unfolding continuation_envelope_def by blast
  have same: "R=Q" using artifact_pair_whole_unique[OF left(1) right(1)] by blast
  have other: "predecessor_continuation_certificate D r F i R z V W X M mu mr"
    using right(2) same by simp
  show ?thesis using predecessor_continuation_subject_unique[OF left(2) other] by blast
qed

lemma continuation_envelope_formed:
  assumes "continuation_envelope C q K S T U B bu br"
  shows "exact_formed K"
  using assms artifact_pair_quoted_formed unfolding continuation_envelope_def by blast

theorem continuation_envelope_total:
  assumes certificate: "predecessor_continuation_certificate C q D r R s S T U B bu br"
  shows "\<exists>K. artifact_pair_quoted_at K [] D R \<and> continuation_envelope C q K S T U B bu br"
proof -
  obtain A l G p E pu pr P d F au ar root where fields:
    "current_entry_scope_quoted_at D r A l G p E pu pr P d"
    "replay_scope_quoted_at R s F pu pr au ar root {}"
    using certificate unfolding predecessor_continuation_certificate_def current_continuation_certificate_def by blast
  have df: "exact_formed D" using current_entry_scope_formed[OF fields(1)] by blast
  have rf: "exact_formed R" using replay_scope_formed[OF fields(2)] by blast
  obtain K where pair: "artifact_pair_quoted_at K [] D R" using artifact_pair_quoted_total[OF df rf] by blast
  show ?thesis using pair certificate unfolding continuation_envelope_def by blast
qed

theorem continuation_envelope_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
  shows "\<exists>k D r R s z e F au ar root t I J V.
    artifact_pair_quoted_at K k D R \<and> current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar e t I J \<and>
    native_schema_graph_at F root V \<and> schema_graph_derives (positioned_program P) V root e t {} \<and>
    continuation_permission_invariant P e \<and> continuation_value_presents S T U B bu br t"
proof -
  obtain k D r R s where pair: "artifact_pair_quoted_at K k D R"
    and certificate: "predecessor_continuation_certificate C q D r R s S T U B bu br"
    using envelope unfolding continuation_envelope_def by blast
  show ?thesis using pair predecessor_continuation_derivation[OF current certificate] by blast
qed

theorem continuation_envelope_before:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and envelope: "continuation_envelope C q K S T U B bu br"
  shows "current_snapshot_at C q S \<and> snapshot_formed S \<and> snapshot_lookup S l=Some G"
proof -
  obtain D r R s where certificate: "predecessor_continuation_certificate C q D r R s S T U B bu br"
    using envelope unfolding continuation_envelope_def by blast
  show ?thesis using certificate predecessor_continuation_before[OF current certificate]
    unfolding predecessor_continuation_certificate_def by blast
qed

theorem accepted_envelope_subject_unique:
  assumes first: "current_accepts_at C q F au ar G (Whole_Artifact K)"
    and second: "current_accepts_at D r F au ar H (Whole_Artifact L)"
    and left: "continuation_envelope C q K S T U B bu br"
    and right: "continuation_envelope D r L V W X M mu mr"
  shows "G=H \<and> K=L \<and> S=V \<and> T=W \<and> U=X \<and> B=M \<and> bu=mu \<and> br=mr"
proof -
  have subjects: "G=H \<and> K=L" using current_acceptance_subject_unique[OF first second] by simp
  have other: "continuation_envelope D r K V W X M mu mr" using right subjects by simp
  show ?thesis using subjects continuation_envelope_subject_unique[OF left other] by blast
qed

theorem continuation_envelope_material_unique:
  assumes first: "continuation_envelope C q K S T U B bu br"
    "successor_material_at B bu br X M mu mr"
    and second: "continuation_envelope D r K V W Y N nu nr"
    "successor_material_at N nu nr Z L lu lr"
  shows "X=Z \<and> M=L \<and> mu=lu \<and> mr=lr"
proof -
  have same: "B=N \<and> bu=nu \<and> br=nr" using continuation_envelope_subject_unique[OF first(1) second(1)] by blast
  have other: "successor_material_at B bu br Z L lu lr" using second(2) same by simp
  show ?thesis by (rule successor_material_at_unique[OF first(2) other])
qed

text \<open>
  The whole submitted artifact contains the exact companion frame and exact
  replay record. Their own complete structures determine their roots. The
  replayed call contains the before snapshot, transaction, claimed after, and
  complete material scope. That subject is recovered without storing it again.

  Equal envelopes cannot select a different continuation subject or substitute
  another proposed frame or supporting scope. Once an actual amendment call
  accepts this exact envelope target, the call fixes the envelope and candidate
  together. Envelope formation or a valid continuation proof alone supplies
  no amendment permission, transaction success, or successor selection.
\<close>

end
