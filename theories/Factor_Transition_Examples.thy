theory Factor_Transition_Examples
  imports Factor_Transition_Selection Factor_Continuation_Selection_Examples
begin

section \<open>The construction order has no circular proof quotation\<close>

theorem universal_current_selection_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and material: "environment_formed M" and site: "(mu,mr)\<in>environment_positions M"
  shows "\<exists>S B K F au R N root.
    current_snapshot_at C q S \<and> transact S empty_transaction (Applied S) \<and>
    successor_material_at B None [] C M mu mr \<and>
    continuation_envelope C q K S empty_transaction S B None [] \<and>
    current_transition_selection_at C q F au [] G K C \<and>
    certified_transition_selection C q R [] G K C \<and>
    replay_scope_quoted_at R [] N pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_environment N pu pr=E \<and>
    native_judgment_environment N pu pr au []=native_judgment_environment F pu pr au []"
proof -
  have cf: "exact_formed C" and gf: "generation_formed G"
    using current_entry_scope_formed[OF current] by auto
  obtain S where before: "current_snapshot_at C q S" "snapshot_formed S"
    using current_entry_snapshot_total[OF current] by blast
  have trans: "transact S empty_transaction (Applied S)"
    by (rule empty_transaction_preserves_snapshot[OF before(2)])
  obtain B where body: "successor_material_at B None [] C M mu mr"
    using successor_material_total[OF cf material site] by blast
  have bf: "environment_formed B" and bs: "(None,[])\<in>environment_positions B"
    using successor_material_at_formed[OF body] by auto
  obtain t where present: "continuation_value_presents S empty_transaction S B None [] t"
    using continuation_value_presents_total[OF before(2) empty_transaction_formed before(2) bf bs] by blast
  have tf: "term_formed t" using continuation_value_presents_formed[OF present] by blast
  have continuation_invariant: "continuation_permission_invariant P d"
    by (rule constant_entry_continuation_invariant[where b=True]) (use every in auto)
  have permitted: "factor_continues P d S empty_transaction S B None []"
    using continuation_invariant present every[OF tf] unfolding factor_continues_def by blast
  have companion: "current_companion C q C q" by (rule current_companion_reflexive[OF current])
  obtain Q where certificate: "predecessor_continuation_certificate C q C q Q [] S empty_transaction S B None []"
    using predecessor_continuation_presentation_total[OF current companion current before(1) permitted present] by blast
  obtain K where envelope: "continuation_envelope C q K S empty_transaction S B None []"
    using continuation_envelope_total[OF certificate] by blast
  have selection: "transition_selection_certificate C q K G C"
    using trans by (simp only: transition_selection_certificate_with_material[OF envelope body current before(1)])
  have kf: "exact_formed K" by (rule continuation_envelope_formed[OF envelope])
  obtain D qu qr bu br L v tail where scope:
    "current_scope_quoted_at C q D qu qr bu br A L v tail l G p"
    using current_entry_scope_frame[OF current] by blast
  have frame: "current_frame_quoted_at C q D qu qr bu br L v tail"
    using scope by (simp add: current_scope_quoted_at_def)
  have fields: "environment_formed D" "(qu,qr)\<in>environment_positions D"
    "(bu,br)\<in>environment_positions D" "environment_formed L" "(v,tail)\<in>environment_positions L"
    using current_frame_quoted_formed[OF frame] by auto
  have target: "target_formed (Whole_Artifact K)" using kf by simp
  obtain w where argument: "amendment_value_presents D qu qr bu br L v tail G (Whole_Artifact K) w"
    using amendment_value_presents_total[OF fields gf target] by blast
  have wf: "term_formed w" using amendment_value_presents_formed[OF argument] by blast
  have acceptance: "factor_accepts P d D qu qr bu br L v tail G (Whole_Artifact K)"
    using every[OF wf] by (simp only: factor_acceptance_at_presentation[OF invariant argument])
  obtain F au where allowed: "current_accepts_at C q F au [] G (Whole_Artifact K)"
    and fixed: "native_package_environment F pu pr=E"
    using current_acceptance_application_total[OF current frame invariant argument] acceptance by blast
  have transition: "current_transition_selection_at C q F au [] G K C"
    using allowed selection by (simp add: current_transition_selection_at_def)
  obtain R N root where accepted:
    "certified_transition_selection C q R [] G K C"
    "replay_scope_quoted_at R [] N pu pr au [] root {}" "native_package_environment N pu pr=E"
    "native_judgment_environment N pu pr au []=native_judgment_environment F pu pr au []"
    using current_transition_selection_certification_total[OF current transition] by blast
  show ?thesis
    by (rule exI[of _ S], rule exI[of _ B], rule exI[of _ K], rule exI[of _ F], rule exI[of _ au],
        rule exI[of _ R], rule exI[of _ N], rule exI[of _ root])
       (use before(1) trans body envelope transition accepted fixed in blast)
qed

section \<open>One actual current program serves every future supporting scope\<close>

theorem fixed_current_selection_accepts_every_formed_material:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    amendment_permission_invariant P d \<and>
    (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P) \<and>
    (\<forall>M mu mr. environment_formed M \<longrightarrow> (mu,mr)\<in>environment_positions M \<longrightarrow>
      (\<exists>S B K F au R N root.
        current_snapshot_at C [] S \<and> transact S empty_transaction (Applied S) \<and>
        successor_material_at B None [] C M mu mr \<and>
        continuation_envelope C [] K S empty_transaction S B None [] \<and>
        current_transition_selection_at C [] F au [] G K C \<and>
        certified_transition_selection C [] R [] G K C \<and>
        replay_scope_quoted_at R [] N pu [] au [] root {} \<and>
        native_package_environment F pu []=E \<and> native_package_environment N pu []=E \<and>
        native_judgment_environment N pu [] au []=native_judgment_environment F pu [] au []))"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site" and E pu P where program:
    "closed_native_package_at E pu [] P"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have member: "g True\<in>system_definitions P" and invariant: "amendment_permission_invariant P (g True)"
    using program(2) by blast+
  have every: "\<And>t. term_formed t \<Longrightarrow>
    schema_call_formed P (g True) t \<and> (g True,t)\<in>positive_meaning P"
    using program(2)[rule_format, of True] by blast
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P (g True)"
    using current_entry_scope_construction[OF program(1) member authority locus] by blast
  have future: "\<forall>M mu mr. environment_formed M \<longrightarrow> (mu,mr)\<in>environment_positions M \<longrightarrow>
      (\<exists>S B K F au R N root.
        current_snapshot_at C [] S \<and> transact S empty_transaction (Applied S) \<and>
        successor_material_at B None [] C M mu mr \<and>
        continuation_envelope C [] K S empty_transaction S B None [] \<and>
        current_transition_selection_at C [] F au [] G K C \<and>
        certified_transition_selection C [] R [] G K C \<and>
        replay_scope_quoted_at R [] N pu [] au [] root {} \<and>
        native_package_environment F pu []=E \<and> native_package_environment N pu []=E \<and>
        native_judgment_environment N pu [] au []=native_judgment_environment F pu [] au [])"
    using universal_current_selection_total[OF current invariant every] by blast
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ E], rule exI[of _ pu],
        rule exI[of _ P], rule exI[of _ "g True"])
       (use current invariant every future in blast)
qed

text \<open>
  The native program and actual currentness frame are fixed before arbitrary
  future supporting material is supplied. Each supplied formed scope has an
  actual continuation proof, an exact envelope, an actual amendment call,
  and its separate retained acceptance proof. The original program and
  minimal acceptance scope survive certification.

  The material is constructed first, then the continuation record, then the
  submitted envelope, and finally the acceptance record. No record is required
  to contain itself. This witness preserves the selected generation and its
  publication through the empty transaction; it asserts no historical
  succession or genesis adequacy.

  The accepting entry checks every formed argument. Consequently arbitrary
  formed supporting material passes this selection component. This exhibits
  why selection, exact binding, and valid ordinary proofs cannot stand in for
  assembly, dependency, comparison, and interpretation admission. Those
  requirements still need a concrete policy and its adequacy theorem.
\<close>

end
