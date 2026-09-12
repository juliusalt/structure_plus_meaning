theory Factor_Predecessor_Continuation
  imports Factor_Current_Companions Factor_Current_Certificates
begin

section \<open>Predecessor continuation retains the original selection boundary\<close>

definition predecessor_continuation_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    exact_artifact \<Rightarrow> local_address \<Rightarrow> selection_snapshot \<Rightarrow>
    structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "predecessor_continuation_certificate C q D r R s S T U B bu br \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d. current_entry_scope_quoted_at C q A l G p E pu pr P d) \<and>
    current_companion C q D r \<and> current_snapshot_at C q S \<and>
    current_continuation_certificate D r R s S T U B bu br"

theorem predecessor_continuation_at_current:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "predecessor_continuation_certificate C q D r R s S T U B bu br\<longleftrightarrow>
    current_companion C q D r \<and> current_snapshot_at C q S \<and>
    current_continuation_certificate D r R s S T U B bu br"
  using current unfolding predecessor_continuation_certificate_def by blast

theorem predecessor_continuation_selected_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "predecessor_continuation_certificate C q D r R s S T U B bu br"
  shows "\<exists>z e. current_entry_scope_quoted_at D r A l G z E pu pr P e"
proof -
  have companion: "current_companion C q D r" and certification:
    "current_continuation_certificate D r R s S T U B bu br"
    using certified by (auto simp: predecessor_continuation_certificate_def)
  obtain B' m H z F qu qr Q e where selected:
    "current_entry_scope_quoted_at D r B' m H z F qu qr Q e"
    using certification unfolding current_continuation_certificate_def by blast
  have same: "A=B' \<and> l=m \<and> G=H \<and> E=F \<and> pu=qu \<and> pr=qr \<and> P=Q"
    by (rule current_companion_program[OF companion current selected])
  show ?thesis using selected same by blast
qed

theorem predecessor_continuation_before:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "predecessor_continuation_certificate C q D r R s S T U B bu br"
  shows "snapshot_formed S \<and> snapshot_lookup S l=Some G"
  using certified current_entry_selected_snapshot[OF current]
  unfolding predecessor_continuation_certificate_def by blast

theorem predecessor_continuation_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "predecessor_continuation_certificate C q D r R s S T U B bu br"
  shows "\<exists>z e F au ar root t I K H.
    current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar e t I K \<and>
    native_schema_graph_at F root H \<and> schema_graph_derives (positioned_program P) H root e t {} \<and>
    continuation_permission_invariant P e \<and> continuation_value_presents S T U B bu br t"
proof -
  obtain z e where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    using predecessor_continuation_selected_entry[OF current certified] by blast
  have certification: "current_continuation_certificate D r R s S T U B bu br"
    using certified by (simp add: predecessor_continuation_certificate_def)
  obtain F au ar root t I K H where fields:
    "replay_scope_quoted_at R s F pu pr au ar root {}"
    "native_package_environment F pu pr=E" "native_package_at F pu pr P"
    "native_application_at F au ar e t I K" "native_schema_graph_at F root H"
    "schema_graph_derives (positioned_program P) H root e t {}"
    "continuation_permission_invariant P e" "continuation_value_presents S T U B bu br t"
    using current_continuation_certificate_derivation[OF selected certification] by blast
  show ?thesis using selected fields by blast
qed

theorem predecessor_continuation_active_boundary:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certified: "predecessor_continuation_certificate C q D r R s S T U B bu br"
  shows "\<exists>z e. current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    system_definition_closure P {e}\<subseteq>system_definitions P \<and>
    finite (system_definition_closure P {e}) \<and>
    system_definition_closure P {e}=native_definition_sites E {e}"
proof -
  obtain z e where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    using predecessor_continuation_selected_entry[OF current certified] by blast
  show ?thesis using selected current_entry_dependency_boundary[OF selected] by blast
qed

theorem predecessor_continuation_original_adoption:
  assumes certified: "predecessor_continuation_certificate C q D r R s S T U B bu br"
    and policy: "current_frame_policy C q E pu pr P d"
    and selected: "current_scope_quoted_at D r F qu qr au ar A N v root l G p"
  shows "factor_adopts P d A G p"
proof -
  have companion: "current_companion C q D r"
    using certified by (simp add: predecessor_continuation_certificate_def)
  show ?thesis by (rule companion_requires_original_adoption[OF companion policy selected])
qed

theorem predecessor_continuation_subject_unique:
  assumes first: "predecessor_continuation_certificate C q D r R s S T U B bu br"
    and second: "predecessor_continuation_certificate C' q' D' r' R a V W X M mu mr"
  shows "s=a \<and> S=V \<and> T=W \<and> U=X \<and> B=M \<and> bu=mu \<and> br=mr"
  using first second current_continuation_certificate_subject_unique
  unfolding predecessor_continuation_certificate_def by blast

section \<open>Every permitted selected call has a predecessor-relative record\<close>

theorem predecessor_continuation_presentation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and companion: "current_companion C q D r"
    and selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    and before: "current_snapshot_at C q S"
    and permitted: "factor_continues P e S T U B bu br"
    and present: "continuation_value_presents S T U B bu br t"
  shows "\<exists>R F au root I K.
    predecessor_continuation_certificate C q D r R [] S T U B bu br \<and>
    replay_scope_quoted_at R [] F pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au [] e t I K"
proof -
  obtain R F au root I K where recorded:
    "current_continuation_certificate D r R [] S T U B bu br"
    "replay_scope_quoted_at R [] F pu pr au [] root {}"
    "native_package_environment F pu pr=E" "native_application_at F au [] e t I K"
    using current_continuation_certificate_presentation_total[OF selected permitted present] by blast
  have predecessor: "predecessor_continuation_certificate C q D r R [] S T U B bu br"
    using current companion before recorded(1) unfolding predecessor_continuation_certificate_def by blast
  show ?thesis using predecessor recorded(2-4) by blast
qed

theorem predecessor_continuation_same_entry_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and before: "current_snapshot_at C q S"
    and permitted: "current_continues_at C q F au ar S T U B bu br"
  shows "\<exists>R. predecessor_continuation_certificate C q C q R [] S T U B bu br"
proof -
  obtain R where certification: "current_continuation_certificate C q R [] S T U B bu br"
    using current_continuation_certification_total[OF current permitted] by blast
  have companion: "current_companion C q C q" by (rule current_companion_reflexive[OF current])
  show ?thesis using current before certification companion unfolding predecessor_continuation_certificate_def by blast
qed

text \<open>
  The before snapshot is recovered from the predecessor's actual publication.
  The continuation purpose is selected by a companion current frame under
  the predecessor's original adoption policy. Both frames select the same
  generation and its exact program environment; their selected entries may differ.

  A retained finite graph derives the complete continuation call without
  assumptions under that exact predecessor program. Its prospective semantic
  dependencies remain inside the predecessor package. The program carried by
  the submitted material is never installed as a rule of this derivation.

  This is one component of an amendment certificate. It supplies no independent
  acceptance decision, no assembly or dependency-validity evidence, and no
  successor selection. The final join must bind these exact records in the
  predecessor's accepted argument and relate the claimed after snapshot to
  the successor's actual publication.
\<close>

end
