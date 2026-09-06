theory Factor_Interpretation_Retention
  imports Factor_Transition_Interpretations Factor_Dependency_Evidence_Examples
begin

section \<open>Retaining independently established reports and interpretation together\<close>

theorem universal_current_interpretation_retention_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and successor: "current_entry_scope_quoted_at X r A' m H z E' qu qr Q e"
    and before: "current_snapshot_at C q S" and after: "current_snapshot_at X r U"
    and trans: "transact S T (Applied U)" and history: "G\<in>fset (generation_predecessors H)"
    and assembly: "predecessor_assembly_certificate C q D h R k H xs B0 W0 Z"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and reports: "amendment_reports_at C q H W F0 fu fr c"
    and bridge: "program_interpretation P Q a b"
    and remainder: "environment_formed V" "(vu,vr)\<in>environment_positions V"
  shows "\<exists>J L Rs N M B K F au Rc N' root.
    interpretation_support_at J None [] a b V vu vr \<and>
    amendment_interpretation_at C q H J None [] \<and>
    comparison_support_at L None [] W F0 fu fr c J None [] \<and>
    amendment_dependency_evidence C q H C q Rs \<and>
    (\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})) \<and>
    dependency_support_at N None [] C Rs L None [] \<and>
    assembly_support_at M None [] D R N None [] \<and> successor_material_at B None [] X M None [] \<and>
    continuation_envelope C q K S T U B None [] \<and>
    current_transition_interpretation_at C q F au [] H K X \<and>
    certified_transition_interpretation C q Rc [] H K X \<and>
    replay_scope_quoted_at Rc [] N' pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_environment N' pu pr=E \<and>
    native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
proof -
  have candidate: "generation_program_scope H E' qu qr Q"
    using successor by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  obtain J where bridge_value: "interpretation_support_at J None [] a b V vu vr"
    and interpreted: "amendment_interpretation_at C q H J None []"
    using amendment_interpretation_total[OF current candidate bridge remainder] by blast
  have jf: "environment_formed J" and jsite: "(None,[])\<in>environment_positions J"
    using interpretation_support_at_formed[OF bridge_value] by auto
  obtain L where comparison: "comparison_support_at L None [] W F0 fu fr c J None []"
    and compared: "amendment_comparison_at C q H L None []"
    using amendment_comparison_total[OF reports jf jsite] by blast
  have lf: "environment_formed L" and lsite: "(None,[])\<in>environment_positions L"
    using comparison_support_at_formed[OF comparison] by auto
  obtain Rs N M B K F au Rc N' root where actual:
    "amendment_dependency_evidence C q H C q Rs"
    "\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})"
    "dependency_support_at N None [] C Rs L None []"
    "assembly_support_at M None [] D R N None []" "successor_material_at B None [] X M None []"
    "continuation_envelope C q K S T U B None []"
    "current_transition_dependencies_at C q F au [] H K X" "certified_transition_dependencies C q Rc [] H K X"
    "replay_scope_quoted_at Rc [] N' pu pr au [] root {}"
    "native_package_environment F pu pr=E" "native_package_environment N' pu pr=E"
    "native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
    using universal_current_transition_dependencies_total[
      OF current successor before after trans history assembly invariant every lf lsite] by blast
  have dependency: "transition_dependency_certificate C q K H X"
    and accepted: "current_accepts_at C q F au [] H (Whole_Artifact K)"
    using actual(7) by (auto simp: current_transition_dependencies_at_def)
  have complete_reports: "transition_comparison_certificate C q K H X"
    using dependency compared by (simp only: transition_comparison_with_material[OF actual(6,5,4,3)])
  have complete: "transition_interpretation_certificate C q K H X"
    using complete_reports interpreted
    by (simp only: transition_interpretation_with_material[OF actual(6,5,4,3) comparison])
  have transition: "current_transition_interpretation_at C q F au [] H K X"
    using accepted complete by (simp add: current_transition_interpretation_at_def)
  have retained: "current_acceptance_certificate C q Rc [] H (Whole_Artifact K)"
    using actual(8) by (simp add: certified_transition_dependencies_def)
  have certified: "certified_transition_interpretation C q Rc [] H K X"
    using retained complete by (simp add: certified_transition_interpretation_def)
  show ?thesis by (rule exI[of _ J], rule exI[of _ L], rule exI[of _ Rs], rule exI[of _ N],
      rule exI[of _ M], rule exI[of _ B], rule exI[of _ K], rule exI[of _ F], rule exI[of _ au],
      rule exI[of _ Rc], rule exI[of _ N'], rule exI[of _ root])
    (use bridge_value interpreted comparison actual(1-6,9-12) transition certified in blast)
qed

text \<open>
  Given the independently established candidate, successful selection, assembly
  account, complete reporter, and exact interpreter, one construction retains
  them together in the accepted material. The interpreter and reporter values
  are formed before dependency support, continuation, and final acceptance.
  The whole original acceptance record retains both scopes and the same
  minimal call environment.

  The displayed predecessor entry permits every formed argument. This theorem
  supplies the missing retention construction; it does not infer comparison
  soundness or interpreter correctness from that permission. Its reports and
  interpretation are explicit premises. Constructing a changed candidate with
  both components from program syntax, native correctness admission, migration,
  and complete genesis remain separate work.
\<close>

end
