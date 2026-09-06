theory Factor_Report_Examples
  imports Factor_Report_Patterns Factor_Amendment_Reports Factor_Current_Entry_Construction
begin

section \<open>Identical argument correspondences may preserve or change truth\<close>

definition report_example_system ::
  "local_address option definition_site \<Rightarrow> bool \<Rightarrow>
    (unit,unit,local_address option definition_site,unit) schema_system" where
  "report_example_system d b =
    \<lparr>system_interfaces={(d,Pattern_Variable ())},
     system_clauses=(if b then {((d,()),recognizer_schema (Pattern_Variable ()))} else {})\<rparr>"

lemma report_example_formed: "schema_system_formed (report_example_system d b)"
  by (cases b) (auto simp: report_example_system_def schema_system_formed_def recognizer_schema_def
    schema_formed_def schema_dependencies_def system_definitions_def rel_dom_def rel_ran_def single_valued_def)

lemma report_example_definitions [simp]: "system_definitions (report_example_system d b)={d}"
  by (auto simp: report_example_system_def system_definitions_def rel_dom_def)

lemma report_example_call:
  "schema_call_formed (report_example_system d b) e t \<longleftrightarrow> e=d \<and> term_formed t"
  using report_example_formed[of d b] by (auto simp: schema_call_formed_def report_example_system_def)

theorem report_example_meaning:
  "(e,t)\<in>positive_meaning (report_example_system d b) \<longleftrightarrow> e=d \<and> b \<and> term_formed t"
proof
  assume truth: "(e,t)\<in>positive_meaning (report_example_system d b)"
  obtain c V Q where inst: "admitted_schema_instance (report_example_system d b) e c V t Q"
    using truth by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have entry: "e=d \<and> b" using inst by (auto simp: admitted_schema_instance_def report_example_system_def split: if_splits)
  have tf: "term_formed t" using positive_meaning_formed[OF truth] by (simp add: report_example_call)
  show "e=d \<and> b \<and> term_formed t" using entry tf by blast
next
  assume parts: "e=d \<and> b \<and> term_formed t"
  have call: "schema_call_formed (report_example_system d b) e t"
    using parts by (simp add: report_example_call)
  have inst: "admitted_schema_instance (report_example_system d b) e () {((),t)} t {}"
    using parts call by (auto simp: admitted_schema_instance_def report_example_call report_example_system_def
      schema_instance_def recognizer_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def schema_material_satisfied_def term_bindings_formed_def single_valued_def rel_dom_def)
  show "(e,t)\<in>positive_meaning (report_example_system d b)" by (rule positive_meaning_step[OF inst]) simp
qed

theorem paired_report_example_coverage:
  assumes addresses: "octets_formed (snd d)" "octets_formed (snd e)"
  shows "system_report_coverage (report_example_system d a) (report_example_system e b) {d} {e}
    {(Some d,Some e)} (program_judgment_reports (report_pattern_system (Some d) (Some e) (p,i)) ())"
proof -
  let ?P="report_example_system d a"
  let ?Q="report_example_system e b"
  let ?R="program_judgment_reports (report_pattern_system (Some d) (Some e) (p,i)) ()"
  let ?J="(\<lambda>t. ((d,t),(e,t))) ` {t. term_formed t}"
  have sites: "report_definition_formed (Some d)" "report_definition_formed (Some e)"
    using addresses by simp_all
  have nonempty: "Some d\<noteq>None \<or> Some e\<noteq>None" by simp
  have reports: "?R=(\<lambda>t. (report_endpoints (Some d) (Some e) t,(p,i))) ` {t. term_formed t}"
    by (rule report_pattern_system_reports[OF sites nonempty])
  have inside: "?J\<subseteq>system_boundary_calls ?P {d}\<times>system_boundary_calls ?Q {e}"
    by (auto simp: system_boundary_calls_def report_example_call)
  have rows: "rel_dom ?R=correspondence_completion (system_boundary_calls ?P {d}) (system_boundary_calls ?Q {e}) ?J"
    by (auto simp: reports report_endpoints_def correspondence_completion_def
      system_boundary_calls_def report_example_call rel_dom_def rel_ran_def image_iff prod_eq_iff)
  have complete: "correspondence_complete (system_boundary_calls ?P {d}) (system_boundary_calls ?Q {e}) (rel_dom ?R)"
    using correspondence_completion_complete[OF inside] rows by simp
  have functional: "single_valued ?R" by (auto simp: reports single_valued_def)
  have structural: "correspondence_complete {d} {e} {(Some d,Some e)}"
    using correspondence_completion_complete[of "{(d,e)}" "{d}" "{e}"]
    by (auto simp: correspondence_completion_def rel_dom_def rel_ran_def)
  show ?thesis using report_example_formed[of d a] report_example_formed[of e b]
    complete functional structural by (simp add: system_report_coverage_def report_coverage_def)
qed

theorem paired_report_example_sound:
  assumes addresses: "octets_formed (snd d)" "octets_formed (snd e)"
  shows "system_report_sound (report_example_system d a) (report_example_system e b)
    (program_judgment_reports (report_pattern_system (Some d) (Some e) (p,i)) ()) \<longleftrightarrow> (p\<longrightarrow>a=b)"
proof -
  let ?R="program_judgment_reports (report_pattern_system (Some d) (Some e) (p,i)) ()"
  have sites: "report_definition_formed (Some d)" "report_definition_formed (Some e)" using addresses by simp_all
  have nonempty: "Some d\<noteq>None \<or> Some e\<noteq>None" by simp
  have reports: "?R=(\<lambda>t. (report_endpoints (Some d) (Some e) t,(p,i))) ` {t. term_formed t}"
    by (rule report_pattern_system_reports[OF sites nonempty])
  show ?thesis
  proof
    assume sound: "system_report_sound (report_example_system d a) (report_example_system e b) ?R"
    show "p\<longrightarrow>a=b"
    proof
      assume promised: "p"
      have tf: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
      have entry: "((Some (d,Payload_Term []),Some (e,Payload_Term [])),(p,i))\<in>?R"
        using tf by (auto simp: report_pattern_system_meaning[OF sites nonempty] report_endpoints_def)
      have row: "(Some (d,Payload_Term []),Some (e,Payload_Term []))\<in>reported_preservation ?R"
        unfolding reported_preservation_def
        by (rule CollectI, rule exI[of _ i]) (use entry promised in simp)
      have truth: "(d,Payload_Term [])\<in>positive_meaning (report_example_system d a) \<longleftrightarrow>
        (e,Payload_Term [])\<in>positive_meaning (report_example_system e b)"
        using sound row by (auto simp: system_report_sound_def)
      show "a=b" using truth tf by (simp add: report_example_meaning)
    qed
  next
    assume "p\<longrightarrow>a=b"
    then show "system_report_sound (report_example_system d a) (report_example_system e b) ?R"
      by (auto simp: system_report_sound_def reports report_endpoints_def reported_preservation_def
        report_example_meaning prod_eq_iff)
  qed
qed

corollary interpretation_does_not_establish_preservation:
  assumes "octets_formed (snd d)" "octets_formed (snd e)"
  shows "system_report_coverage (report_example_system d False) (report_example_system e True) {d} {e}
      {(Some d,Some e)} (program_judgment_reports (report_pattern_system (Some d) (Some e) (False,True)) ())"
    and "system_report_sound (report_example_system d False) (report_example_system e True)
      (program_judgment_reports (report_pattern_system (Some d) (Some e) (False,True)) ())"
    and "\<not>system_report_sound (report_example_system d False) (report_example_system e True)
      (program_judgment_reports (report_pattern_system (Some d) (Some e) (True,False)) ())"
  using paired_report_example_coverage[OF assms, where a=False and b=True and p=False and i=True]
    paired_report_example_sound[OF assms, of False True False True]
    paired_report_example_sound[OF assms, where a=False and b=True and p=True and i=False] by simp_all

theorem unilateral_report_example:
  assumes address: "octets_formed (snd d)" and target: "schema_system_formed Q"
  shows "system_report_coverage (report_example_system d a) Q {d} {}
      {(Some d,None)} (program_judgment_reports (report_pattern_system (Some d) None (False,True)) ())"
    and "system_report_sound (report_example_system d a) Q
      (program_judgment_reports (report_pattern_system (Some d) None (False,True)) ())"
proof -
  have sites: "report_definition_formed (Some d)" "report_definition_formed None"
    using address by simp_all
  have nonempty: "Some d\<noteq>None \<or> None\<noteq>None" by simp
  have same: "program_judgment_reports (report_pattern_system (Some d) None (False,True)) () =
      absent_judgment_reports (report_example_system d a) Q {d} {}"
    by (simp only: report_pattern_system_reports[OF sites nonempty])
      (cases d; auto simp:
      absent_judgment_reports_def constant_correspondence_reports_def correspondence_completion_def
      system_boundary_calls_def report_example_call rel_dom_def rel_ran_def report_endpoints_def image_iff)
  have structural: "correspondence_completion {d} {} {}=
      {(Some d,None :: local_address option definition_site option)}"
    by (auto simp: correspondence_completion_def rel_dom_def rel_ran_def prod_eq_iff)
  have coverage: "system_report_coverage (report_example_system d a) Q {d} {}
      (correspondence_completion {d} {} {}) (absent_judgment_reports (report_example_system d a) Q {d} {})"
    by (rule absent_judgment_reports_complete[OF report_example_formed target]) simp_all
  show "system_report_coverage (report_example_system d a) Q {d} {}
      {(Some d,None)} (program_judgment_reports (report_pattern_system (Some d) None (False,True)) ())"
    using coverage same structural by simp
  show "system_report_sound (report_example_system d a) Q
      (program_judgment_reports (report_pattern_system (Some d) None (False,True)) ())"
    using absent_judgment_reports_sound[of "report_example_system d a" Q "{d}" "{}"] same by simp
qed

section \<open>A complete preserving report at an actual current native scope\<close>

theorem singleton_current_reports:
  assumes source: "closed_native_package_at E pu pr P" "native_package_environment E pu pr=E"
    and definitions: "system_definitions P={d}"
    and calls: "\<And>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p F fu T b.
    current_entry_scope_quoted_at C [] A l G p E pu pr P d \<and>
    closed_native_package_at F fu [] T \<and> native_package_environment F fu []=F \<and>
    b\<in>system_definitions T \<and>
    amendment_reports_at C [] G {(Some d,Some d)} F fu [] b \<and>
    program_judgment_reports T b=identity_judgment_reports P {d} True False"
proof -
  have package: "native_package_at E pu pr P" using source(1) by (simp add: closed_native_package_at_def)
  have formed: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have member: "d\<in>system_definitions P" using definitions by simp
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu pr P d"
    using current_entry_scope_construction[OF source(1) member authority locus] by blast
  have candidate: "generation_program_scope G E pu pr P"
    using current by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  have purpose: "purpose_entry p d" using current by (simp add: current_entry_scope_quoted_at_def)
  have address: "octets_formed (snd d)" using purpose_entry_formed[OF purpose] by blast
  have root_bound: "native_package_roots E pu pr\<subseteq>{d}"
    using native_package_roots_inside[OF package] definitions by simp
  have root_nonempty: "native_package_roots E pu pr\<noteq>{}"
    using native_package_roots_empty[OF package] definitions by simp
  obtain x where root: "x\<in>native_package_roots E pu pr" using root_nonempty by blast
  have coordinate: "x=d" using subsetD[OF root_bound root] by simp
  have selected: "d\<in>native_package_roots E pu pr" using root coordinate by simp
  have roots: "native_package_roots E pu pr={d}" using root_bound selected by auto
  have domain: "system_comparison_definitions P P (native_package_roots E pu pr)={d}"
    using system_affected_empty[OF formed, where U="{}"] roots
    by (simp add: system_comparison_definitions_def)
  have sites: "report_definition_formed (Some d)" by (simp add: address)
  have nonempty: "Some d\<noteq>None \<or> Some d\<noteq>None" by simp
  obtain F :: "local_address option artifact_environment" and fu T b where reporter:
    "closed_native_package_at F fu [] T" "native_package_environment F fu []=F"
    "b\<in>system_definitions T" "program_reports_only T b"
    "program_judgment_reports T b=(\<lambda>t. (report_endpoints (Some d) (Some d) t,(True,False))) ` {t. term_formed t}"
    using report_pattern_native[OF sites sites nonempty, where b="(True,False)"]
    by metis
  have same: "program_judgment_reports T b=identity_judgment_reports P {d} True False"
    by (auto simp: reporter(5) identity_judgment_reports_def constant_correspondence_reports_def
      system_boundary_calls_def calls report_endpoints_def image_iff dest: schema_call_formed_target)
  have inside: "{d}\<subseteq>system_definitions P" using definitions by simp
  have coverage: "system_report_coverage P P {d} {d} {(Some d,Some d)} (program_judgment_reports T b)"
    using identity_judgment_reports_complete[OF formed inside, of True False] same by simp
  have sound: "system_report_sound P P (program_judgment_reports T b)"
    using identity_judgment_reports_sound[of P "{d}" True False] same by simp
  have complete: "amendment_reports_at C [] G {(Some d,Some d)} F fu [] b"
    using reporter(3,4) coverage sound domain
    by (simp add: amendment_reports_with_scopes[OF current candidate reporter(1,2)])
  show ?thesis by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ F],
    rule exI[of _ fu], rule exI[of _ T], rule exI[of _ b])
    (use current reporter(1-3) complete same in blast)
qed

theorem current_complete_report_witness:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d F fu T b.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    closed_native_package_at F fu [] T \<and> native_package_environment F fu []=F \<and>
    b\<in>system_definitions T \<and>
    amendment_reports_at C [] G {(Some d,Some d)} F fu [] b \<and>
    program_judgment_reports T b=identity_judgment_reports P {d} True False"
proof -
  let ?S="recognizer_system () (Pattern_Variable ())"
  have sf: "schema_system_formed ?S" by (rule recognizer_system_formed) simp
  have defs: "system_definitions ?S={()}" by (auto simp: recognizer_system_def system_definitions_def rel_dom_def)
  obtain g :: "unit \<Rightarrow> local_address option definition_site" and E pu P where compiled:
    "inj_on g (system_definitions ?S)" "closed_native_package_at E pu [] P"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g ?S) P"
    using program_compilation_total[OF sf] by metis
  have definitions: "system_definitions P={g ()}"
    using compiled(4) defs by (simp add: system_alpha_variant_def renamed_system_definitions)
  have member: "()\<in>system_definitions ?S" using defs by simp
  have calls: "\<And>t. schema_call_formed P (g ()) t \<longleftrightarrow> term_formed t"
    using compiled_system_call_boundary[OF sf compiled(1,4) member]
      recognizer_call_formed[where p="Pattern_Variable ()" and a="()"] by simp
  show ?thesis using singleton_current_reports[OF compiled(2,3) definitions calls authority locus] by blast
qed

text \<open>
  The displayed ordinary systems give opposite truth at corresponding calls
  while their structural and interpretation reports remain complete. Declaring
  incompatibility is sound; changing that declaration into preservation fails.
  Equality of truth is checked against the independently defined meanings.

  A closed native singleton program also has an actual currentness frame and
  a separate closed native reporting program whose complete relation preserves
  every formed call. The comparison uses the same generation on both sides;
  it is a nonvacuous coverage witness, not a claim that a new successor has
  been adopted. Current-frame construction does not validate its cause.

  Structural migration and semantic interpretation may coexist with preservation.
  The report program never becomes an acceptance rule merely by being supplied
  as comparison material.
\<close>

end
