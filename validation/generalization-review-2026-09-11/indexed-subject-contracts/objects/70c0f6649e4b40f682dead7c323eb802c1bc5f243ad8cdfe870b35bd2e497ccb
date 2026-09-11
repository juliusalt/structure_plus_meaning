theory Factor_Transition_Comparison_Examples
  imports Factor_Transition_Construction_Examples Factor_Transition_Comparisons Factor_Report_Examples
begin

section \<open>A strict successor retains complete preserving reports in its accepted material\<close>

theorem preserving_comparison_successor_total:
  assumes authority: "target_formed A" and locus: "target_formed l"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>C G p E pu P d H X z F fu T b L Rs D M R B S U K J au Rc N' root.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    current_entry_scope_quoted_at X [] A l H z E pu [] P d \<and>
    system_definitions P={d} \<and>
    (\<forall>t. schema_call_formed P d t\<longleftrightarrow>term_formed t) \<and>
    generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
    closed_native_package_at F fu [] T \<and> b\<in>system_definitions T \<and> program_reports_only T b \<and>
    program_judgment_reports T b=identity_judgment_reports P {d} True False \<and>
    comparison_support_at L None [] {(Some d,Some d)} F fu [] b N nu nr \<and>
    dependency_support_at D None [] C Rs L None [] \<and>
    assembly_support_at M None [] C R D None [] \<and> successor_material_at B None [] X M None [] \<and>
    continuation_envelope C [] K S (replacement_transaction G H) U B None [] \<and>
    transact S (replacement_transaction G H) (Applied U) \<and> U\<noteq>S \<and>
    current_transition_comparison_at C [] J au [] H K X \<and> certified_transition_comparison C [] Rc [] H K X \<and>
    replay_scope_quoted_at Rc [] N' pu [] au [] root {} \<and>
    native_package_environment J pu []=E \<and> native_package_environment N' pu []=E \<and>
    native_judgment_environment N' pu [] au []=native_judgment_environment J pu [] au []"
proof -
  let ?S="recognizer_system () (Pattern_Variable ())"
  have sf: "schema_system_formed ?S" by (rule recognizer_system_formed) simp
  have defs: "system_definitions ?S={()}" by (auto simp: recognizer_system_def system_definitions_def rel_dom_def)
  have member: "()\<in>system_definitions ?S" using defs by simp
  obtain g :: "unit\<Rightarrow>local_address option definition_site" and E pu P where compiled:
    "inj_on g (system_definitions ?S)" "closed_native_package_at E pu [] P"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g ?S) P"
    "positive_meaning P=image (map_prod g id) (positive_meaning ?S)"
    using program_compilation_total[OF sf] by metis
  let ?d="g ()"
  have definitions: "system_definitions P={?d}"
    using compiled(4) defs by (simp add: system_alpha_variant_def renamed_system_definitions)
  have calls: "\<And>t. schema_call_formed P ?d t\<longleftrightarrow>term_formed t"
    using compiled_system_call_boundary[OF sf compiled(1,4) member]
      recognizer_call_formed[where p="Pattern_Variable ()" and a="()"] by simp
  have meaning: "\<And>t. (?d,t)\<in>positive_meaning P\<longleftrightarrow>term_formed t"
    using compiled_system_meaning_at[OF compiled(1) member compiled(5)]
      recognizer_positive_meaning[where p="Pattern_Variable ()" and a="()"] by simp
  have every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P ?d t \<and> (?d,t)\<in>positive_meaning P"
    using calls meaning by blast
  have invariant: "amendment_permission_invariant P ?d"
    using amendment_value_presents_formed
    by (auto simp: amendment_permission_invariant_def calls meaning)
  obtain C G p F fu T b where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P ?d"
    and reporter: "closed_native_package_at F fu [] T" "native_package_environment F fu []=F"
      "b\<in>system_definitions T"
    and reports: "amendment_reports_at C [] G {(Some ?d,Some ?d)} F fu [] b"
    and exact_reports: "program_judgment_reports T b=identity_judgment_reports P {?d} True False"
    using singleton_current_reports[OF compiled(2,3) definitions calls authority locus] by blast
  have old_program: "generation_program_scope G E pu [] P"
    using current by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  have profile: "b\<in>system_definitions T \<and> program_reports_only T b \<and>
    system_report_coverage P P
      (system_comparison_definitions P P (native_package_roots E pu []))
      (system_comparison_definitions P P (native_package_roots E pu []))
      {(Some ?d,Some ?d)} (program_judgment_reports T b) \<and>
    system_report_sound P P (program_judgment_reports T b)"
    using reports by (simp only: amendment_reports_with_scopes[OF current old_program reporter(1,2)])
  obtain L where comparison: "comparison_support_at L None [] {(Some ?d,Some ?d)} F fu [] b N nu nr"
    using amendment_comparison_total[OF reports remainder] by blast
  have lf: "environment_formed L" and site: "(None,[])\<in>environment_positions L"
    using comparison_support_at_formed[OF comparison] by auto
  have entry: "?d\<in>system_definitions P" using definitions by simp
  obtain H X z Rs D M R B S U K J au Rc N' root where actual:
    "generation_predecessors H={|G|}" "G\<noteq>H"
    "current_entry_scope_quoted_at X [] A l H z E pu [] P ?d"
    "dependency_support_at D None [] C Rs L None []"
    "assembly_support_at M None [] C R D None []" "successor_material_at B None [] X M None []"
    "continuation_envelope C [] K S (replacement_transaction G H) U B None []"
    "transact S (replacement_transaction G H) (Applied U)" "U\<noteq>S"
    "current_transition_dependencies_at C [] J au [] H K X"
    "certified_transition_dependencies C [] Rc [] H K X"
    "replay_scope_quoted_at Rc [] N' pu [] au [] root {}"
    "native_package_environment J pu []=E" "native_package_environment N' pu []=E"
    "native_judgment_environment N' pu [] au []=native_judgment_environment J pu [] au []"
    using universal_current_program_successor_total[OF current invariant every compiled(2) entry authority lf site] by blast
  have candidate: "generation_program_scope H E pu [] P"
    using actual(3) by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  have new_reports: "amendment_reports_at C [] H {(Some ?d,Some ?d)} F fu [] b"
    using profile by (simp only: amendment_reports_with_scopes[OF current candidate reporter(1,2)])
  have dependency: "transition_dependency_certificate C [] K H X"
    and accepted: "current_accepts_at C [] J au [] H (Whole_Artifact K)"
    using actual(10) by (auto simp: current_transition_dependencies_at_def)
  have complete: "transition_comparison_certificate C [] K H X"
    using dependency new_reports
    by (simp only: transition_comparison_with_reporter[OF actual(7,6,5,4) comparison])
  have transition: "current_transition_comparison_at C [] J au [] H K X"
    using accepted complete by (simp add: current_transition_comparison_at_def)
  have retained: "current_acceptance_certificate C [] Rc [] H (Whole_Artifact K)"
    using actual(11) by (simp add: certified_transition_dependencies_def)
  have certified: "certified_transition_comparison C [] Rc [] H K X"
    using retained complete by (simp add: certified_transition_comparison_def)
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ E], rule exI[of _ pu],
        rule exI[of _ P], rule exI[of _ ?d], rule exI[of _ H], rule exI[of _ X], rule exI[of _ z],
        rule exI[of _ F], rule exI[of _ fu], rule exI[of _ T], rule exI[of _ b], rule exI[of _ L],
        rule exI[of _ Rs], rule exI[of _ D], rule exI[of _ M], rule exI[of _ R], rule exI[of _ B],
        rule exI[of _ S], rule exI[of _ U], rule exI[of _ K], rule exI[of _ J], rule exI[of _ au],
        rule exI[of _ Rc], rule exI[of _ N'], rule exI[of _ root])
       (use current actual(1-9,12-15) definitions calls reporter profile exact_reports comparison transition certified in blast)
qed

text \<open>
  The complete native reporter is built before the successor's supporting
  material. It preserves every formed argument at the actual singleton program,
  with no finite sample or assumed report relation. The new generation has
  the actual current generation as its direct predecessor and an exact
  construction cause. Its program scope is unchanged, while its generation
  and successful publication snapshot are strictly different.

  The reporter and arbitrary remaining formed material occur inside the
  dependency and assembly support quoted by the continuation proof and accepted
  envelope. The same final acceptance record retains all of those values, the
  exact predecessor program, and the minimal call scope. The joint construction
  supplies the actual successor frame and publication before those later proofs.

  This witness establishes consistency of the combined comparison component.
  Its permissive predecessor does not check comparison adequacy by itself.
  A native protocol proving the full semantic obligations, migration evidence,
  exact historical interpretation, and complete genesis remain necessary.
\<close>

end
