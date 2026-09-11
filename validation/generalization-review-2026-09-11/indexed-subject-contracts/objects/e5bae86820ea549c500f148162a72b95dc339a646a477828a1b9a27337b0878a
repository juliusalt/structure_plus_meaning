theory Factor_Interpretation_Construction
  imports Factor_Transition_Construction_Examples Factor_Transition_Interpretations Factor_Copy_Reports
begin

section \<open>Constructing comparison and interpretation before the actual successor\<close>

theorem universal_current_interpreted_successor_total:
  fixes Q :: "local_address option native_system"
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and other: "schema_system_formed Q" and member: "e\<in>system_definitions Q"
    and authority: "target_formed A'"
    and remainder: "environment_formed V" "(vu,vr)\<in>environment_positions V"
  shows "\<exists>F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root.
    closed_native_package_at F v [] T \<and>
    native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and>
    a\<noteq>b \<and>
    interpretation_support_at J None [] a b V vu vr \<and>
    inj_on f (system_definitions P) \<and>
    inj_on g (system_definitions Q) \<and>
    f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
    {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
    system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)) \<and>
    native_package_roots F v []=system_definitions T \<and>
    P\<noteq>T \<and>
    current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
    generation_predecessors H={|G|} \<and>
    G\<noteq>H \<and>
    U0=system_comparison_definitions P T (native_package_roots E pu pr) \<and>
    W=correspondence_completion U0 (system_definitions T) ((\<lambda>d. (d,f d)) ` U0) \<and>
    closed_native_package_at I iu [] R \<and>
    native_package_environment I iu []=I \<and>
    c\<in>system_definitions R \<and>
    program_reports_only R c \<and>
    program_judgment_reports R c=copied_judgment_reports P T U0 (system_definitions T) f \<and>
    amendment_reports_at C q H W I iu [] c \<and>
    amendment_interpretation_at C q H J None [] \<and>
    comparison_support_at L None [] W I iu [] c J None [] \<and>
    dependency_support_at D None [] C Rs L None [] \<and>
    assembly_support_at M None [] C Rb D None [] \<and>
    successor_material_at B None [] X M None [] \<and>
    continuation_envelope C q K S (replacement_transaction G H) U B None [] \<and>
    transact S (replacement_transaction G H) (Applied U) \<and>
    U\<noteq>S \<and>
    (\<forall>m. m\<noteq>l \<longrightarrow> snapshot_lookup U m=snapshot_lookup S m) \<and>
    current_transition_interpretation_at C q N au [] H K X \<and>
    certified_transition_interpretation C q Rc [] H K X \<and>
    replay_scope_quoted_at Rc [] N' pu pr au [] root {} \<and>
    native_package_environment N pu pr=E \<and>
    native_package_environment N' pu pr=E \<and>
    native_judgment_environment N' pu pr au []=native_judgment_environment N pu pr au []"
proof -
  obtain F v T a b J f g where compiled:
    "closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and> a\<noteq>b \<and> interpretation_support_at J None [] a b V vu vr \<and>
    inj_on f (system_definitions P) \<and> inj_on g (system_definitions Q) \<and>
    f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
    {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
    system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)) \<and>
    (\<forall>H. generation_program_scope H F v [] T \<longrightarrow> amendment_interpretation_at C q H J None []) \<and>
    native_package_roots F v []=system_definitions T"
    using current_interpretation_material_total[OF current other remainder] by (atomize_elim) assumption
  have core: "closed_native_package_at F v [] T"
    "native_package_environment F v []=F"
    "program_interpretation P T a b"
    "a\<noteq>b"
    "interpretation_support_at J None [] a b V vu vr"
    "inj_on f (system_definitions P)"
    "inj_on g (system_definitions Q)"
    "f ` system_definitions P \<inter> g ` system_definitions Q={}"
    "{a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={}"
    "system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q))"
    "(\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P))"
    "(\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q))"
    "(\<forall>H. generation_program_scope H F v [] T \<longrightarrow> amendment_interpretation_at C q H J None [])"
    "native_package_roots F v []=system_definitions T"
    using compiled by blast+
  have old: "native_package_at E pu pr P"
    using current_entry_scope_closed[OF current] by (simp add: closed_native_package_at_def)
  have native: "native_package_at F v [] T" using core(1) by (simp add: closed_native_package_at_def)
  have formed: "schema_system_formed P" "schema_system_formed T"
    using native_package_system_formed[OF old] native_package_system_formed[OF native] by auto
  have finite_old: "finite (system_definitions P)" by (rule system_definitions_finite[OF formed(1)])
  have finite_copy: "finite (f ` system_definitions P)" using finite_old by simp
  have fresh: "a\<notin>f ` system_definitions P" using core(9) by auto
  have larger: "insert a (f ` system_definitions P)\<subseteq>system_definitions T" using core(10) by auto
  have sizes: "card (insert a (f ` system_definitions P))\<le>card (system_definitions T)"
    by (rule card_mono[OF system_definitions_finite[OF formed(2)] larger])
  have copy_size: "card (f ` system_definitions P)=card (system_definitions P)" by (rule card_image[OF core(6)])
  have changed: "P\<noteq>T" using sizes finite_copy fresh copy_size by auto
  let ?U0="system_comparison_definitions P T (native_package_roots E pu pr)"
  let ?W="correspondence_completion ?U0 (system_definitions T) ((\<lambda>d. (d,f d)) ` ?U0)"
  have old_roots: "native_package_roots E pu pr\<subseteq>system_definitions P"
    by (rule native_package_roots_inside[OF old])
  have inside: "?U0\<subseteq>system_definitions P"
    using system_comparison_definitions_boundary[where Q=T, OF formed(1) old_roots] by blast
  have mapped: "f ` ?U0\<subseteq>system_definitions T" using inside core(10) by auto
  have calls: "schema_call_formed T (f j) t \<longleftrightarrow> schema_call_formed P j t" if "j\<in>?U0" for j t
    using core(11) inside that by blast
  have truth: "(f j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning P" if "j\<in>?U0" for j t
    using core(11) inside that by blast
  obtain I :: "local_address option artifact_environment" and iu R c where reporter:
    "closed_native_package_at I iu [] R" "native_package_environment I iu []=I"
    "c\<in>system_definitions R" "program_reports_only R c"
    "program_judgment_reports R c=copied_judgment_reports P T ?U0 (system_definitions T) f"
    "system_report_coverage P T ?U0 (system_definitions T) ?W (program_judgment_reports R c)"
    "system_report_sound P T (program_judgment_reports R c)"
    using copied_judgment_reports_native[OF old native inside subset_refl mapped calls truth]
    by (atomize_elim) assumption
  have environments: "environment_formed E" "environment_formed F"
    using native_package_projection(1)[OF old] native_package_projection(1)[OF native]
    by (auto simp: native_package_formed_def)
  have old_address: "octets_formed (snd j)" if "j\<in>?U0" for j
    by (rule environment_position_address[OF environments(1)], rule native_package_entry_position[OF old])
      (use inside that in blast)
  have new_address: "octets_formed (snd j)" if "j\<in>system_definitions T" for j
    by (rule environment_position_address[OF environments(2)], rule native_package_entry_position[OF native that])
  have complete: "correspondence_complete ?U0 (system_definitions T) ?W"
    using reporter(6) by (simp add: system_report_coverage_def)
  have boundary: "?W\<subseteq>insert None (Some ` ?U0)\<times>insert None (Some ` system_definitions T)"
    by (rule correspondence_complete_boundary[OF complete])
  have rows: "term_formed (correspondence_row_data x)" if "x\<in>?W" for x
  proof -
    have left: "fst x=None \<or> (\<exists>j\<in>?U0. fst x=Some j)"
      and right: "snd x=None \<or> (\<exists>j\<in>system_definitions T. snd x=Some j)"
      using boundary that by auto
    show ?thesis using left right old_address new_address by (auto simp: correspondence_row_data_def)
  qed
  have finite_rows: "finite ?W" by (rule system_report_migration_finite[OF reporter(6)])
  have report_package: "native_package_at I iu [] R" using reporter(1) by (simp add: closed_native_package_at_def)
  have report_environment: "environment_formed I"
    using native_package_projection(1)[OF report_package] by (simp add: native_package_formed_def)
  have report_root: "(iu,[])\<in>environment_positions I" by (rule native_package_root_position[OF report_package])
  have report_entry: "c\<in>environment_positions I" by (rule native_package_entry_position[OF report_package reporter(3)])
  have bridge_environment: "environment_formed J" and bridge_site: "(None,[])\<in>environment_positions J"
    using interpretation_support_at_formed[OF core(5)] by auto
  obtain L where comparison: "comparison_support_at L None [] ?W I iu [] c J None []"
    using comparison_support_total[OF finite_rows rows report_environment report_root report_entry bridge_environment bridge_site]
    by blast
  have lf: "environment_formed L" and lsite: "(None,[])\<in>environment_positions L"
    using comparison_support_at_formed[OF comparison] by auto
  have selected: "g e\<in>system_definitions T" using member core(10) by auto
  obtain Z Rb H Rs S U X z Npub vpub Vpub Jpub jpu bpu D M B K N au Rc N' root where actual:
    "program_scope_quoted_at Z [] F v [] T"
    "predecessor_assembly_certificate C q C q Rb [] H [Z] {} (whole_source_construction Z) Z"
    "generation_predecessors H={|G|}"
    "generation_locus H=l"
    "G\<noteq>H"
    "amendment_dependency_evidence C q H C q Rs"
    "(\<forall>R0\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{R0}))"
    "current_entry_scope_quoted_at X [] A' l H z F v [] T (g e)"
    "current_scope_quoted_at X [] Jpub jpu [] bpu [] A' Npub vpub [] l H z"
    "publication_environment_closed Npub vpub [] Vpub"
    "publication_snapshot Vpub=U"
    "publication_evidence Vpub=Abs_fset (image Whole_Artifact (insert Rb Rs))"
    "publication_dependencies Vpub={||}"
    "current_snapshot_at C q S"
    "current_snapshot_at X [] U"
    "transact S (replacement_transaction G H) (Applied U)"
    "U\<noteq>S"
    "(\<forall>m. m\<noteq>l \<longrightarrow> snapshot_lookup U m=snapshot_lookup S m)"
    "dependency_support_at D None [] C Rs L None []"
    "assembly_support_at M None [] C Rb D None []"
    "successor_material_at B None [] X M None []"
    "continuation_envelope C q K S (replacement_transaction G H) U B None []"
    "current_transition_dependencies_at C q N au [] H K X"
    "certified_transition_dependencies C q Rc [] H K X"
    "replay_scope_quoted_at Rc [] N' pu pr au [] root {}"
    "native_package_environment N pu pr=E"
    "native_package_environment N' pu pr=E"
    "native_judgment_environment N' pu pr au []=native_judgment_environment N pu pr au []"
    using universal_current_program_successor_total[OF current invariant every core(1) selected authority lf lsite]
    by (atomize_elim) metis
  have candidate: "generation_program_scope H F v [] T"
    using actual(8) by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  have new_domain: "system_comparison_definitions T P (native_package_roots F v [])=system_definitions T"
    using system_affected_definitions_inside[where P=T and U="system_changed_definitions T P"]
    by (auto simp: core(14) system_comparison_definitions_def)
  have reports: "amendment_reports_at C q H ?W I iu [] c"
    using reporter(3,4,6,7)
    by (simp add: amendment_reports_with_scopes[OF current candidate reporter(1,2)] new_domain)
  have interpreted: "amendment_interpretation_at C q H J None []"
    using core(13) candidate by blast
  have dependency: "transition_dependency_certificate C q K H X"
    and accepted: "current_accepts_at C q N au [] H (Whole_Artifact K)"
    using actual(23) by (auto simp: current_transition_dependencies_at_def)
  have compared: "transition_comparison_certificate C q K H X"
    using dependency reports
    by (simp only: transition_comparison_with_reporter[OF actual(22,21,20,19) comparison])
  have complete_transition: "transition_interpretation_certificate C q K H X"
    using compared interpreted
    by (simp only: transition_interpretation_with_material[OF actual(22,21,20,19) comparison])
  have transition: "current_transition_interpretation_at C q N au [] H K X"
    using accepted complete_transition by (simp add: current_transition_interpretation_at_def)
  have retained: "current_acceptance_certificate C q Rc [] H (Whole_Artifact K)"
    using actual(24) by (simp add: certified_transition_dependencies_def)
  have certified: "certified_transition_interpretation C q Rc [] H K X"
    using retained complete_transition by (simp add: certified_transition_interpretation_def)
  show ?thesis by (rule exI[of _ "F"], rule exI[of _ "v"], rule exI[of _ "T"], rule exI[of _ "a"],
      rule exI[of _ "b"], rule exI[of _ "f"], rule exI[of _ "g"], rule exI[of _ "H"],
      rule exI[of _ "X"], rule exI[of _ "z"], rule exI[of _ "?U0"], rule exI[of _ "?W"],
      rule exI[of _ "I"], rule exI[of _ "iu"], rule exI[of _ "R"], rule exI[of _ "c"],
      rule exI[of _ "J"], rule exI[of _ "L"], rule exI[of _ "Rs"], rule exI[of _ "D"],
      rule exI[of _ "M"], rule exI[of _ "Rb"], rule exI[of _ "B"], rule exI[of _ "S"],
      rule exI[of _ "U"], rule exI[of _ "K"], rule exI[of _ "N"], rule exI[of _ "au"],
      rule exI[of _ "Rc"], rule exI[of _ "N'"], rule exI[of _ "root"])
    (use core(1-12,14) changed actual(3,5,8,16-22,25-28) reporter(1-5)
      reports interpreted comparison transition certified in simp)
qed

section \<open>A fixed actual predecessor serves every future program and selected entry\<close>

theorem fixed_current_interprets_every_future_program:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    amendment_permission_invariant P d \<and>
    (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P) \<and>
    (\<forall>Q :: local_address option native_system. \<forall>e A'.
      schema_system_formed Q \<longrightarrow> e\<in>system_definitions Q \<longrightarrow> target_formed A' \<longrightarrow>
      (\<exists>F v T H X z a b g K N au R.
        closed_native_package_at F v [] T \<and> P\<noteq>T \<and>
        current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
        program_interpretation P T a b \<and> generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        (\<forall>j\<in>system_definitions Q. \<forall>t.
          (schema_call_formed T (g j) t \<longleftrightarrow> schema_call_formed Q j t) \<and>
          ((g j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning Q)) \<and>
        current_transition_interpretation_at C [] N au [] H K X \<and>
        certified_transition_interpretation C [] R [] H K X \<and> native_package_environment N pu []=E))"
proof -
  obtain C G p E pu P d where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    using fixed_current_selection_accepts_every_formed_material[OF authority locus] by blast
  have package: "native_package_at E pu [] P"
    using current_entry_scope_closed[OF current] by (simp add: closed_native_package_at_def)
  have environment: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have site: "(pu,[])\<in>environment_positions E" by (rule native_package_root_position[OF package])
  have future: "\<forall>Q :: local_address option native_system. \<forall>e A'.
      schema_system_formed Q \<longrightarrow> e\<in>system_definitions Q \<longrightarrow> target_formed A' \<longrightarrow>
      (\<exists>F v T H X z a b g K N au R.
        closed_native_package_at F v [] T \<and> P\<noteq>T \<and>
        current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
        program_interpretation P T a b \<and> generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        (\<forall>j\<in>system_definitions Q. \<forall>t.
          (schema_call_formed T (g j) t \<longleftrightarrow> schema_call_formed Q j t) \<and>
          ((g j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning Q)) \<and>
        current_transition_interpretation_at C [] N au [] H K X \<and>
        certified_transition_interpretation C [] R [] H K X \<and> native_package_environment N pu []=E)"
  proof (intro allI impI)
    fix Q :: "local_address option native_system"
    fix e A'
    assume formed: "schema_system_formed Q" and member: "e\<in>system_definitions Q" and owner: "target_formed A'"
    let ?result = "\<lambda>F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root.
      closed_native_package_at F v [] T \<and>
      native_package_environment F v []=F \<and>
      program_interpretation P T a b \<and>
      a\<noteq>b \<and>
      interpretation_support_at J None [] a b E pu [] \<and>
      inj_on f (system_definitions P) \<and>
      inj_on g (system_definitions Q) \<and>
      f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
      {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
      system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
      (\<forall>d\<in>system_definitions P. \<forall>t.
        (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
        ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
      (\<forall>d\<in>system_definitions Q. \<forall>t.
        (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
        ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)) \<and>
      native_package_roots F v []=system_definitions T \<and>
      P\<noteq>T \<and>
      current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
      generation_predecessors H={|G|} \<and>
      G\<noteq>H \<and>
      U0=system_comparison_definitions P T (native_package_roots E pu []) \<and>
      W=correspondence_completion U0 (system_definitions T) ((\<lambda>d. (d,f d)) ` U0) \<and>
      closed_native_package_at I iu [] R \<and>
      native_package_environment I iu []=I \<and>
      c\<in>system_definitions R \<and>
      program_reports_only R c \<and>
      program_judgment_reports R c=copied_judgment_reports P T U0 (system_definitions T) f \<and>
      amendment_reports_at C [] H W I iu [] c \<and>
      amendment_interpretation_at C [] H J None [] \<and>
      comparison_support_at L None [] W I iu [] c J None [] \<and>
      dependency_support_at D None [] C Rs L None [] \<and>
      assembly_support_at M None [] C Rb D None [] \<and>
      successor_material_at B None [] X M None [] \<and>
      continuation_envelope C [] K S (replacement_transaction G H) U B None [] \<and>
      transact S (replacement_transaction G H) (Applied U) \<and>
      U\<noteq>S \<and>
      (\<forall>m. m\<noteq>l \<longrightarrow> snapshot_lookup U m=snapshot_lookup S m) \<and>
      current_transition_interpretation_at C [] N au [] H K X \<and>
      certified_transition_interpretation C [] Rc [] H K X \<and>
      replay_scope_quoted_at Rc [] N' pu [] au [] root {} \<and>
      native_package_environment N pu []=E \<and>
      native_package_environment N' pu []=E \<and>
      native_judgment_environment N' pu [] au []=native_judgment_environment N pu [] au []"
    have result: "\<exists>F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root.
      ?result F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root"
      by (rule universal_current_interpreted_successor_total[
        OF current invariant every[rule_format] formed member owner environment site]; assumption)
    then obtain F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root where full:
      "?result F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root"
    proof (elim exE)
      fix F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root
      assume found: "?result F v T a b f g H X z U0 W I iu R c J L Rs D M Rb B S U K N au Rc N' root"
      show thesis by (rule that[OF found])
    qed
    show "\<exists>F v T H X z a b g K N au R.
        closed_native_package_at F v [] T \<and> P\<noteq>T \<and>
        current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
        program_interpretation P T a b \<and> generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        (\<forall>j\<in>system_definitions Q. \<forall>t.
          (schema_call_formed T (g j) t \<longleftrightarrow> schema_call_formed Q j t) \<and>
          ((g j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning Q)) \<and>
        current_transition_interpretation_at C [] N au [] H K X \<and>
        certified_transition_interpretation C [] R [] H K X \<and> native_package_environment N pu []=E"
      by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ T], rule exI[of _ H],
          rule exI[of _ X], rule exI[of _ z], rule exI[of _ a], rule exI[of _ b],
          rule exI[of _ g], rule exI[of _ K], rule exI[of _ N], rule exI[of _ au], rule exI[of _ Rc])
        (use full in blast)
  qed
  show ?thesis by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ E],
      rule exI[of _ pu], rule exI[of _ P], rule exI[of _ d]) (use current invariant every future in blast)
qed

section \<open>The selected policy may refuse while historical truth remains exact\<close>

theorem interpreted_successor_may_select_refusal:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d F v T H X z a b e' K N au R.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    current_entry_scope_quoted_at X [] A l H z F v [] T e' \<and>
    generation_predecessors H={|G|} \<and> G\<noteq>H \<and> P\<noteq>T \<and> program_interpretation P T a b \<and>
    (\<forall>t. term_formed t \<longrightarrow>
      schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P \<and>
      schema_call_formed T e' t \<and> (e',t)\<notin>positive_meaning T \<and>
      (b,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning T) \<and>
    current_transition_interpretation_at C [] N au [] H K X \<and>
    certified_transition_interpretation C [] R [] H K X \<and> native_package_environment N pu []=E"
proof -
  obtain C G p E pu P d where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and future: "\<forall>Q :: local_address option native_system. \<forall>e A'.
      schema_system_formed Q \<longrightarrow> e\<in>system_definitions Q \<longrightarrow> target_formed A' \<longrightarrow>
      (\<exists>F v T H X z a b g K N au R.
        closed_native_package_at F v [] T \<and> P\<noteq>T \<and>
        current_entry_scope_quoted_at X [] A' l H z F v [] T (g e) \<and>
        program_interpretation P T a b \<and> generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
        (\<forall>j\<in>system_definitions Q. \<forall>t.
          (schema_call_formed T (g j) t \<longleftrightarrow> schema_call_formed Q j t) \<and>
          ((g j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning Q)) \<and>
        current_transition_interpretation_at C [] N au [] H K X \<and>
        certified_transition_interpretation C [] R [] H K X \<and> native_package_environment N pu []=E)"
    using fixed_current_interprets_every_future_program[OF authority locus] by (atomize_elim) assumption
  obtain N0 :: "local_address option artifact_environment" and u0 Q e where source:
    "closed_native_package_at N0 u0 [] Q" "system_definitions Q={e}" "positive_meaning Q={}"
    "\<forall>t. schema_call_formed Q e t\<longleftrightarrow>term_formed t"
    using single_refusing_native_program by (atomize_elim) assumption
  have package: "native_package_at N0 u0 [] Q" using source(1) by (simp add: closed_native_package_at_def)
  have formed: "schema_system_formed Q" by (rule native_package_system_formed[OF package])
  have member: "e\<in>system_definitions Q" using source(2) by simp
  obtain F v T H X z a b g K N au R where actual:
    "closed_native_package_at F v [] T"
    "P\<noteq>T"
    "current_entry_scope_quoted_at X [] A l H z F v [] T (g e)"
    "program_interpretation P T a b"
    "generation_predecessors H={|G|}"
    "G\<noteq>H"
    "\<forall>j\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g j) t \<longleftrightarrow> schema_call_formed Q j t) \<and>
      ((g j,t)\<in>positive_meaning T \<longleftrightarrow> (j,t)\<in>positive_meaning Q)"
    "current_transition_interpretation_at C [] N au [] H K X"
    "certified_transition_interpretation C [] R [] H K X"
    "native_package_environment N pu []=E"
    using future[rule_format, OF formed member authority] by (atomize_elim) metis
  have selected: "\<forall>t. term_formed t \<longrightarrow>
      schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P \<and>
      schema_call_formed T (g e) t \<and> (g e,t)\<notin>positive_meaning T \<and>
      (b,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning T"
  proof (intro allI impI)
    fix t assume tf: "term_formed t"
    have prior: "schema_call_formed P d t" "(d,t)\<in>positive_meaning P" using every tf by auto
    have calls: "schema_call_formed T (g e) t \<longleftrightarrow> schema_call_formed Q e t"
      and truth: "(g e,t)\<in>positive_meaning T \<longleftrightarrow> (e,t)\<in>positive_meaning Q"
      using actual(7) member by blast+
    have historical: "(b,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning T"
      using program_interpretation_at_call(2)[OF actual(4), of d t] prior(2) by blast
    show "schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P \<and>
      schema_call_formed T (g e) t \<and> (g e,t)\<notin>positive_meaning T \<and>
      (b,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning T"
      using prior calls truth historical source(3,4) tf by simp
  qed
  show ?thesis by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ E],
      rule exI[of _ pu], rule exI[of _ P], rule exI[of _ d], rule exI[of _ F], rule exI[of _ v],
      rule exI[of _ T], rule exI[of _ H], rule exI[of _ X], rule exI[of _ z], rule exI[of _ a],
      rule exI[of _ b], rule exI[of _ "g e"], rule exI[of _ K], rule exI[of _ N],
      rule exI[of _ au], rule exI[of _ R])
    (use current actual(2-6,8-10) selected in blast)
qed

text \<open>
  The candidate and complete historical bridge are compiled from the supplied
  finite programs. The actual root selector includes every candidate
  definition. The required old domain is computed from the unchanged current
  scope and the compiled candidate, and its copied image lies inside that
  complete new domain. Each required old call receives a preserving report;
  every additional candidate call receives an explicit unpaired row.

  The reporter and interpreter values precede the candidate's cause and
  publication. The successor construction then builds the exact payload
  account, direct predecessor edge, complete dependency permission records,
  successful replacement publication, continuation, and original acceptance.
  The report and interpreter occupy that same accepted material. The old
  program and minimal acceptance environment survive the final closed proof.

  One fixed actual predecessor works for every future formed program with a
  selected entry. Neither a report relation nor a semantic bridge is assumed
  in that theorem. All source interfaces, truth, and historical output
  contracts follow from finite compilation. The constructed candidate is
  strictly larger than the old program and therefore actually different.

  The refusal example distinguishes the newly selected policy from retained
  historical truth. The old entry permits every formed argument; the new
  selected entry refuses every argument while the interpreter still gives
  the exact old answers. The displayed predecessor remains permissive.
  These constructions establish joint inhabitation of the mathematical
  components, not native admission of their complete correctness evidence.
  Migration, the internal full protocol, reflection, and genesis remain open.
\<close>

end
