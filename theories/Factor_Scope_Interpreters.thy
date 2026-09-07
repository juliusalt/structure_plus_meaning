theory Factor_Scope_Interpreters
  imports Factor_Scope_Forwarding Factor_Program_Reflection Factor_Historical_Programs
begin

section \<open>Adding a forwarding entry preserves the complete existing program\<close>

lemma native_package_definition_edge_closed:
  assumes package: "native_package_at E u r P" and member: "d\<in>system_definitions P"
    and edge: "(d,e)\<in>native_definition_edges E"
  shows "e\<in>system_definitions P"
proof -
  have definitions: "system_definitions P=native_definition_sites E (native_package_roots E u r)"
    using native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  have reached: "d\<in>native_definition_sites E (native_package_roots E u r)"
    using member definitions by simp
  show ?thesis using native_definition_step[OF reached edge] definitions by simp
qed

lemma native_scope_forwarding_edge:
  assumes forwarding: "native_scope_forwarding_at E (fst d) (snd d) k x y z"
    and edge: "(d,e)\<in>native_definition_edges E"
  shows "e=k"
proof -
  obtain i c b s where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i)
    {(c,scope_call_schema b s k x y z)}"
    using forwarding by (auto simp: native_scope_forwarding_at_def)
  obtain p C n S where other: "native_definition_at E (fst d) (snd d) p C"
    "(n,S)\<in>C" "e\<in>schema_dependencies S"
    using edge by (auto simp: native_definition_edges_def)
  have family: "C={(c,scope_call_schema b s k x y z)}"
    using native_definition_unique[OF other(1) raw] by blast
  have schema: "S=scope_call_schema b s k x y z" using other(2) family by simp
  show ?thesis using other(3) by (simp add: schema)
qed

theorem native_scope_forwarding_package_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and callee: "k\<in>system_definitions P"
    and fields: "term_formed x" "term_formed y" "term_formed z"
  shows "\<exists>F u v Q. environment_formed F \<and> environment_included E F \<and>
    u\<notin>environment_uses E \<and> (u,[])\<notin>system_definitions P \<and>
    native_package_at F v [] Q \<and> system_definitions Q=insert (u,[]) (system_definitions P) \<and>
    native_scope_forwarding_at F u [] k x y z \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a)"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain p C where callee_read: "native_definition_at E (fst k) (snd k) p C"
    using native_package_definition_exists[OF package callee] by blast
  have target: "\<exists>R. artifact_at E (fst k) R \<and> anchor_formed (R,snd k)"
    by (rule native_definition_has_anchor[OF callee_read])
  obtain H u where installed: "environment_formed H" "environment_included E H"
    "u\<notin>environment_uses E" "native_scope_forwarding_at H u [] k x y z"
    "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at H w R \<longleftrightarrow> artifact_at E w R"
    "\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot H w s a \<longleftrightarrow> binds_slot E w s a"
    using native_scope_forwarding_total[OF ef target fields] by (elim exE conjE) (rule that; assumption)
  have copied: "native_package_at H pu pr P"
    by (rule native_package_included[OF package installed(2,1)])
  let ?a="(u,[])" let ?U="insert ?a (system_definitions P)"
  have fresh: "?a\<notin>system_definitions P"
  proof
    assume member: "?a\<in>system_definitions P"
    have position: "?a\<in>environment_positions E" by (rule native_package_entry_position[OF package member])
    have "u\<in>environment_uses E"
      using position by (auto simp: environment_positions_def environment_uses_def artifact_at_def rel_dom_def)
    then show False using installed(3) by blast
  qed
  have reads: "\<exists>p C. native_definition_at H (fst d) (snd d) p C" if "d\<in>?U" for d
  proof (cases "d=?a")
    case True
    show ?thesis using installed(4) by (simp add: True native_scope_forwarding_at_def) blast
  next
    case False
    have member: "d\<in>system_definitions P" using that False by simp
    show ?thesis by (rule native_package_definition_exists[OF copied member])
  qed
  have closed: "e\<in>?U" if member: "d\<in>?U" and edge: "(d,e)\<in>native_definition_edges H" for d e
  proof (cases "d=?a")
    case True
    have read: "native_scope_forwarding_at H (fst d) (snd d) k x y z" using installed(4) True by simp
    have "e=k" by (rule native_scope_forwarding_edge[OF read edge])
    then show ?thesis using callee by simp
  next
    case False
    have member: "d\<in>system_definitions P" using member False by simp
    show ?thesis using native_package_definition_edge_closed[OF copied member edge] by simp
  qed
  have sites: "native_definition_sites H ?U=?U"
  proof (rule subset_antisym)
    show "native_definition_sites H ?U\<subseteq>?U"
      by (rule native_definition_sites_least[OF subset_refl closed])
    show "?U\<subseteq>native_definition_sites H ?U" by (rule native_definition_roots)
  qed
  have dependency: "native_package_formed H ?U"
    unfolding native_package_formed_def sites
    by (rule conjI[OF installed(1)], intro ballI, rule reads, assumption)
  have fin: "finite ?U" using system_definitions_finite[OF native_package_system_formed[OF package]] by simp
  have targets: "\<forall>d\<in>?U. \<exists>R. artifact_at H (fst d) R \<and> anchor_formed (R,snd d)"
  proof (intro ballI)
    fix d assume member: "d\<in>?U"
    obtain p C where read: "native_definition_at H (fst d) (snd d) p C"
      using reads[OF member] by blast
    show "\<exists>R. artifact_at H (fst d) R \<and> anchor_formed (R,snd d)"
      by (rule native_definition_has_anchor[OF read])
  qed
  obtain F v L where selected: "environment_formed F" "environment_included H F"
    "native_root_family_at F v [] L" "rel_ran L=?U"
    "\<forall>w\<in>environment_uses H. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at H w R"
    "\<forall>w\<in>environment_uses H. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot H w s a"
    using root_family_environment_total[OF installed(1) fin targets] by (elim exE conjE) (rule that; assumption)
  have kept: "native_package_formed F ?U \<and> native_program F ?U=native_program H ?U"
    by (rule native_dependency_package_included[OF dependency selected(2,1)])
  have result: "native_package_at F v [] (native_program H ?U)"
    unfolding native_package_at_def
    by (rule exI[of _ L]) (use selected(3,4) kept in auto)
  have definitions: "system_definitions (native_program H ?U)=?U"
    by (simp only: native_program_definitions[OF dependency] sites)
  have forwarding: "native_scope_forwarding_at F u [] k x y z"
    by (rule native_scope_forwarding_included[OF installed(4) selected(2,1)])
  have included: "environment_included E F" by (rule environment_included_trans[OF installed(2) selected(2)])
  have uses: "environment_uses E\<subseteq>environment_uses H" by (rule included_uses[OF installed(2)])
  have artifacts: "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R"
  proof (intro ballI allI)
    fix w R assume old_use: "w\<in>environment_uses E"
    have in_H: "w\<in>environment_uses H" by (rule subsetD[OF uses old_use])
    show "artifact_at F w R \<longleftrightarrow> artifact_at E w R"
      by (simp only: selected(5)[rule_format, OF in_H] installed(5)[rule_format, OF old_use])
  qed
  have bindings: "\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a"
  proof (intro ballI allI)
    fix w s a assume old_use: "w\<in>environment_uses E"
    have in_H: "w\<in>environment_uses H" by (rule subsetD[OF uses old_use])
    show "binds_slot F w s a \<longleftrightarrow> binds_slot E w s a"
      by (simp only: selected(6)[rule_format, OF in_H] installed(6)[rule_format, OF old_use])
  qed
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ v],
      rule exI[of _ "native_program H ?U"], rule conjI[OF selected(1)],
      rule conjI[OF included], rule conjI[OF installed(3)], rule conjI[OF fresh],
      rule conjI[OF result], rule conjI[OF definitions], rule conjI[OF forwarding],
      rule conjI[OF artifacts], rule bindings)
qed

section \<open>A finite complete profile binds both entries to the actual candidate\<close>

definition native_scope_interpreter_at ::
  "local_address option artifact_environment \<Rightarrow>
    local_address option definition_site \<Rightarrow> local_address option definition_site \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site \<Rightarrow> local_address option definition_site \<Rightarrow> bool" where
  "native_scope_interpreter_at C ka kb E pu pr F qu qr a b \<longleftrightarrow>
    environment_formed C \<and> (\<exists>P Q H x y.
      native_package_at E pu pr P \<and> native_package_at F qu qr Q \<and>
      a\<in>system_definitions Q \<and> b\<in>system_definitions Q \<and>
      environment_formed H \<and> environment_included C H \<and> environment_included F H \<and>
      environment_value_presents E x \<and> environment_value_presents E y \<and>
      native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr) \<and>
      native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr))"

lemma native_scope_interpreter_witnesses:
  assumes profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
    and target: "native_package_at F qu qr Q"
  obtains H x y where "a\<in>system_definitions Q" "b\<in>system_definitions Q"
    "environment_formed H" "environment_included C H" "environment_included F H"
    "environment_value_presents E x" "environment_value_presents E y"
    "native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr)"
    "native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr)"
proof -
  obtain P' Q' H x y where data:
    "native_package_at E pu pr P'" "native_package_at F qu qr Q'"
    "a\<in>system_definitions Q'" "b\<in>system_definitions Q'"
    "environment_formed H" "environment_included C H" "environment_included F H"
    "environment_value_presents E x" "environment_value_presents E y"
    "native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr)"
    "native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr)"
    using profile unfolding native_scope_interpreter_at_def by blast
  have same: "Q'=Q" by (rule native_package_unique[OF data(2) target])
  show thesis using that data(3-11) same by blast
qed

theorem native_scope_interpreter_distinct:
  assumes profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b" and distinct: "ka\<noteq>kb"
  shows "a\<noteq>b"
proof
  assume same: "a=b"
  obtain H x y where readings:
    "native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr)"
    "native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr)"
    using profile unfolding native_scope_interpreter_at_def by blast
  have other: "native_scope_forwarding_at H (fst a) (snd a) kb y (use_data_term pu) (Payload_Term pr)"
    using readings(2) same by simp
  have "ka=kb" by (rule native_scope_forwarding_callee_unique[OF readings(1) other])
  then show False using distinct by blast
qed

theorem native_scope_interpreter_correct:
  assumes reference: "native_package_at C cu cr R"
    and entries: "ka\<in>system_definitions R" "kb\<in>system_definitions R"
    and admission: "\<forall>z. (ka,z)\<in>positive_meaning R \<longleftrightarrow> program_call_admission_result z"
    and meaning: "\<forall>z. (kb,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
    and profile: "native_scope_interpreter_at C ka kb E pu pr F qu qr a b"
    and source: "native_package_at E pu pr P" and target: "native_package_at F qu qr Q"
  shows "program_interpretation P Q a b"
proof -
  obtain H x y where data: "a\<in>system_definitions Q" "b\<in>system_definitions Q"
    "environment_formed H" "environment_included C H" "environment_included F H"
    "environment_value_presents E x" "environment_value_presents E y"
    "native_scope_forwarding_at H (fst a) (snd a) ka x (use_data_term pu) (Payload_Term pr)"
    "native_scope_forwarding_at H (fst b) (snd b) kb y (use_data_term pu) (Payload_Term pr)"
    using native_scope_interpreter_witnesses[OF profile target] by blast
  have copied: "native_package_at H qu qr Q" by (rule native_package_included[OF target data(5,3)])
  have fixed: "native_package_at H cu cr R" by (rule native_package_included[OF reference data(4,3)])
  have ac: "schema_call_formed Q a z \<longleftrightarrow> term_formed z" for z
    by (rule native_scope_forwarding_call[OF copied data(1,8)])
  have bc: "schema_call_formed Q b z \<longleftrightarrow> term_formed z" for z
    by (rule native_scope_forwarding_call[OF copied data(2,9)])
  have af: "(a,z)\<in>positive_meaning Q \<longleftrightarrow>
    (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (definition_site_value d) t)" for z
    using program_formation_reflection[OF data(6) source, of z]
    by (simp only: native_scope_forwarding_shared_meaning[OF copied fixed data(1) entries(1) data(8)]
        admission program_reflection_components program_call_admission_exact)
  have bf: "(b,z)\<in>positive_meaning Q \<longleftrightarrow>
    (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (definition_site_value d) t)" for z
    using program_meaning_reflection[OF data(7) source, of z]
    by (simp only: native_scope_forwarding_shared_meaning[OF copied fixed data(2) entries(2) data(9)]
        meaning program_reflection_components positive_query_exact)
  show ?thesis using native_package_system_formed[OF source] native_package_system_formed[OF target]
    data(1,2) ac bc af bf by (simp add: program_interpretation_def)
qed

section \<open>Every source package has a closed candidate in this class\<close>

theorem native_scope_interpreter_total:
  assumes reference: "native_package_at C cu cr R"
    and entries: "ka\<in>system_definitions R" "kb\<in>system_definitions R"
    and source: "native_package_at E pu pr P"
    and presentations: "environment_value_presents E x" "environment_value_presents E y"
  shows "\<exists>F qu Q a b. closed_native_package_at F qu [] Q \<and>
    native_package_environment F qu []=F \<and> native_scope_interpreter_at C ka kb E pu pr F qu [] a b \<and>
    a\<noteq>b \<and> {a,b}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert b (insert a (system_definitions R))"
proof -
  have cf: "environment_formed C"
    using native_package_projection(1)[OF reference] by (simp add: native_package_formed_def)
  have fields: "term_formed x" "term_formed y" "term_formed (use_data_term pu)" "term_formed (Payload_Term pr)"
    using environment_value_presents_formed[OF presentations(1)] environment_value_presents_formed[OF presentations(2)]
      schema_call_formed_target[OF positive_meaning_formed[OF package_admission_complete[OF presentations(1) source]]]
    by auto
  obtain H au hu T where first: "environment_formed H" "environment_included C H"
    "(au,[])\<notin>system_definitions R" "native_package_at H hu [] T"
    "system_definitions T=insert (au,[]) (system_definitions R)"
    "native_scope_forwarding_at H au [] ka x (use_data_term pu) (Payload_Term pr)"
    using native_scope_forwarding_package_total[OF reference entries(1) fields(1,3,4)] by (elim exE conjE) (rule that; assumption)
  have second_entry: "kb\<in>system_definitions T" using entries(2) first(5) by simp
  obtain J bu qu Q where second: "environment_formed J" "environment_included H J"
    "(bu,[])\<notin>system_definitions T" "native_package_at J qu [] Q"
    "system_definitions Q=insert (bu,[]) (system_definitions T)"
    "native_scope_forwarding_at J bu [] kb y (use_data_term pu) (Payload_Term pr)"
    using native_scope_forwarding_package_total[OF first(4) second_entry fields(2-4)] by (elim exE conjE) (rule that; assumption)
  let ?F="native_package_environment J qu []"
  have closed: "closed_native_package_at ?F qu [] Q" by (rule native_package_closed_restriction[OF second(4)])
  have package: "native_package_at ?F qu [] Q" using closed by (simp add: closed_native_package_at_def)
  have included: "environment_included C J" by (rule environment_included_trans[OF first(2) second(2)])
  have forwarding: "native_scope_forwarding_at J au [] ka x (use_data_term pu) (Payload_Term pr)"
    by (rule native_scope_forwarding_included[OF first(6) second(2,1)])
  have profile: "native_scope_interpreter_at C ka kb E pu pr ?F qu [] (au,[]) (bu,[])"
    unfolding native_scope_interpreter_at_def
    by (rule conjI[OF cf], rule exI[of _ P], rule exI[of _ Q], rule exI[of _ J],
        rule exI[of _ x], rule exI[of _ y])
      (use source package second(1,5,6) first(5) included presentations forwarding
        native_package_environment_included[of J qu "[]"] in auto)
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ qu], rule exI[of _ Q],
      rule exI[of _ "(au,[])"], rule exI[of _ "(bu,[])"])
    (use closed native_package_closed_environment_fixed[OF closed] profile first(3,5) second(3,5) in auto)
qed

text \<open>
  The public finite profile requires two actual members of the candidate package.
  A common formed extension retains both that candidate environment and the
  complete reference environment. It can retain the reference root selector even
  when the candidate's minimal scope omits it. Extension cannot change an
  existing artifact or binding, and native package meanings remain exact.

  The two entries may store different complete presentations of the same old
  environment. Both forward the arbitrary argument to their fixed reference
  entry at the same actual old package site. Whole-definition readings determine
  these clauses, including their complete absence of further alternatives or
  material conditions. Their meanings therefore agree with the independently
  proved reference on every term. No candidate truth relation supplies this
  correctness argument.

  Starting with any actual reference package containing the two callees,
  construction adds two fresh forwarding definitions and selects the complete
  resulting program. Its canonical restriction is a closed candidate with
  exactly those two definitions and the original reference definitions. The
  old source is retained as data and need not share an active use space with
  the reference. The separate admission theory recognizes this finite profile
  through ordinary calls.
\<close>

end
