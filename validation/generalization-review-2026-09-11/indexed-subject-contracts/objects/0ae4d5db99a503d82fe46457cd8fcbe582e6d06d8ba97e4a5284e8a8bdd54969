theory Factor_Continuation_Omissions
  imports Factor_Continuation_Programs Factor_Package_Omissions RRA_Generation_Construction
begin

section \<open>Complete retained ancestry cannot replace a required semantic binding\<close>

theorem retained_history_with_missing_program_binding:
  assumes locus: "target_formed l"
  shows "\<exists>E F C :: local_address option artifact_environment. \<exists>pu au cu P d e t I K G H R k.
    environment_formed E \<and> environment_formed F \<and> F=omit_binding E pu k \<and>
    environment_artifacts F=environment_artifacts E \<and>
    environment_bindings F=environment_bindings E-{((pu,k),fst e)} \<and>
    environment_included C E \<and> environment_included C F \<and> generation_at C cu [] G \<and>
    generation_at E cu [] G \<and> generation_at F cu [] G \<and>
    H\<in>fset (generation_predecessors G) \<and> generation_payload H=Whole_Artifact R \<and>
    artifact_at E (fst e) R \<and> e\<in>system_definitions P \<and>
    binds_slot (native_package_environment E pu []) pu k (fst e) \<and>
    native_package_at E pu [] P \<and> native_application_at E au [] d t I K \<and>
    native_application_at F au [] d t I K \<and> continuation_permission_invariant P d \<and>
    continuation_value_presents {|G|} empty_transaction {|G|} C cu [] t \<and>
    native_advance_at E pu [] au [] {|G|} empty_transaction {|G|} C cu [] \<and>
    \<not>(\<exists>Q. native_package_at F pu [] Q) \<and>
    \<not>native_continuation_at F pu [] au [] {|G|} empty_transaction {|G|} C cu []"
proof -
  obtain E0 :: "local_address option artifact_environment" and u0 P d where policy:
    "closed_native_package_at E0 u0 [] P" "d\<in>system_definitions P" "continuation_permission_invariant P d"
    "\<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      schema_call_formed P d t \<and> ((d,t)\<in>positive_meaning P\<longleftrightarrow>True)"
    using constant_continuation_program[of True] by blast
  have original: "native_package_at E0 u0 [] P" using policy(1) by (simp add: closed_native_package_at_def)
  have nonempty: "system_definitions P\<noteq>{}" using policy(2) by blast
  obtain B pu k e R where selected: "closed_native_package_at B pu [] P"
    "native_package_environment B pu []=B" "binds_slot B pu k (fst e)" "pu\<noteq>fst e"
    "e\<in>system_definitions P" "artifact_at B (fst e) R" "anchor_formed (R,snd e)"
    using native_package_external_selection[OF original nonempty] by blast
  have package: "native_package_at B pu [] P" using selected(1) by (simp add: closed_native_package_at_def)
  have bf: "environment_formed B" using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have rf: "exact_formed R" using selected(7) by (simp add: anchor_formed_def)
  let ?H="Generation l {||} (Whole_Artifact R) l"
  let ?G="Generation l {|?H|} (Whole_Artifact R) l"
  have hf: "generation_formed ?H" by (rule generation_formed.formed) (use locus rf in auto)
  have gf: "generation_formed ?G" by (rule generation_formed.formed) (use locus rf hf in auto)
  have sf: "snapshot_formed {|?G|}" using gf by (simp add: snapshot_formed_def selection_formed_def)
  obtain C0 :: "local_address option artifact_environment" and cu0 where generation: "generation_at C0 cu0 [] ?G"
    using generation_presentation_total[OF gf] by blast
  have c0f: "environment_formed C0" by (rule generation_at_environment_formed[OF generation])
  obtain A h where extension: "environment_formed A" "inj h" "environment_included B A"
    "environment_included (rename_environment h C0) A" "range h\<inter>environment_uses B={}"
    using disjoint_environment_extension[OF bf c0f] by blast
  let ?C="rename_environment h C0"
  let ?cu="h cu0"
  have cf: "environment_formed ?C" by (rule environment_renaming_formed[OF c0f extension(2)])
  have history: "generation_at ?C ?cu [] ?G" by (rule generation_at_use_renaming[OF generation extension(2)])
  have root_use: "pu\<in>environment_uses B"
    by (rule environment_binding_uses(1)[OF bf selected(3)])
  have disjoint: "pu\<notin>environment_uses ?C" using extension(5) root_use by (auto simp: environment_renaming_uses)
  have site: "(?cu,[])\<in>environment_positions ?C"
    using generation_at_has_anchor[OF history] by (auto simp: anchor_formed_def)
  have copied: "native_package_at A pu [] P" by (rule native_package_included[OF package extension(3,1)])
  have canonical: "native_package_environment A pu []=B"
    using native_package_environment_extension[OF package extension(3,1)] selected(2) by simp
  obtain t where present: "continuation_value_presents {|?G|} empty_transaction {|?G|} ?C ?cu [] t"
    using continuation_value_presents_total[OF sf empty_transaction_formed sf cf site] by blast
  have truth: "(d,t)\<in>positive_meaning P" using policy(4)[rule_format, OF present] by simp
  have permission: "factor_continues P d {|?G|} empty_transaction {|?G|} ?C ?cu []"
    using factor_continuation_at_presentation[OF policy(3) present] truth by blast
  obtain E au I K where call: "environment_formed E" "environment_included A E" "au\<notin>environment_uses A"
    "native_package_at E pu [] P" "native_application_at E au [] d t I K"
    "native_package_environment E pu []=native_package_environment A pu []"
    "native_continuation_at E pu [] au [] {|?G|} empty_transaction {|?G|} ?C ?cu []"
    using native_continuation_application_total[OF copied policy(2,3) present] permission by blast
  have into_e: "environment_included B E" by (rule environment_included_trans[OF extension(3) call(2)])
  have history_in_e: "environment_included ?C E" by (rule environment_included_trans[OF extension(4) call(2)])
  have old_history: "generation_at E ?cu [] ?G" by (rule generation_at_included[OF history history_in_e call(1)])
  have trans: "transact {|?G|} empty_transaction (Applied {|?G|})"
    by (rule empty_transaction_preserves_snapshot[OF sf])
  have advance: "native_advance_at E pu [] au [] {|?G|} empty_transaction {|?G|} ?C ?cu []"
    using trans call(7) by (simp add: native_advance_at_def)
  have required: "binds_slot (native_package_environment E pu []) pu k (fst e)"
    using selected(3) canonical call(6) by simp
  have binding: "binds_slot E pu k (fst e)" by (rule included_binding[OF into_e selected(3)])
  have artifact: "artifact_at E (fst e) R" by (rule included_artifact[OF into_e selected(6)])
  let ?F="omit_binding E pu k"
  have ff: "environment_formed ?F" by (rule omit_binding_formed[OF call(1)])
  have exact: "environment_bindings ?F=environment_bindings E-{((pu,k),fst e)}"
    by (rule omit_binding_exact_difference[OF call(1) binding])
  have history_in_f: "environment_included ?C ?F"
    by (rule omit_binding_preserves_other_subenvironment[OF cf history_in_e disjoint])
  have kept_history: "generation_at ?F ?cu [] ?G" by (rule generation_at_included[OF history history_in_f ff])
  have old_use: "pu\<in>environment_uses A" by (rule subsetD[OF included_uses[OF extension(3)] root_use])
  have different: "au\<noteq>pu" using call(3) old_use by blast
  have kept_call: "native_application_at ?F au [] d t I K" by (rule native_application_omit_other_binding[OF call(5) different])
  have no_program: "\<not>(\<exists>Q. native_package_at ?F pu [] Q)"
    by (rule native_package_required_binding_omitted[OF call(4) required])
  have no_permission: "\<not>native_continuation_at ?F pu [] au [] {|?G|} empty_transaction {|?G|} ?C ?cu []"
    using no_program unfolding native_continuation_at_def by blast
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ ?F], rule exI[of _ ?C], rule exI[of _ pu], rule exI[of _ au],
        rule exI[of _ ?cu], rule exI[of _ P], rule exI[of _ d], rule exI[of _ e], rule exI[of _ t],
        rule exI[of _ I], rule exI[of _ K], rule exI[of _ ?G], rule exI[of _ ?H], rule exI[of _ R], rule exI[of _ k])
       (use call(1,4,5) ff exact history_in_e history_in_f history old_history kept_history artifact selected(5)
          required kept_call policy(3) present advance no_program no_permission in auto)
qed

text \<open>
  This witness has an actual admitted positive policy and a successful native
  advancement. Its selected generation has a nonempty predecessor family.
  An ancestor's exact payload is an actual definition artifact of that policy.
  The complete independently placed history scope is included in both compared
  environments, with every artifact and every historical binding unchanged.

  The second environment omits exactly one required program binding. It retains
  all artifact placements, the identical native call and argument, and the
  complete generation reading. Nonetheless no program can be recovered at the
  specified package site. Historical availability of the definition artifact
  therefore cannot replace that missing semantic reference. This concerns a
  supplied program boundary; authority and amendment retain their own joins.
\<close>

end
