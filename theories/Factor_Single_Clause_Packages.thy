theory Factor_Single_Clause_Packages
  imports Factor_Single_Clause_Reading Factor_Package_Extensions Factor_Program_Scopes
begin

lemma native_single_clause_included:
  assumes "native_single_clause_at E u r S" "environment_included E F" "environment_formed F"
  shows "native_single_clause_at F u r S"
proof -
  obtain i c where read: "native_definition_at E u r (Pattern_Variable i) {(c,S)}"
    using assms(1) by (auto simp: native_single_clause_at_def)
  have copied: "native_definition_at F u r (Pattern_Variable i) {(c,S)}"
    by (rule native_definition_included[OF read assms(2,3)])
  show ?thesis unfolding native_single_clause_at_def
    by (rule exI[of _ i], rule exI[of _ c], rule copied)
qed

section \<open>Every formed clause over existing callees has a complete package extension\<close>

theorem native_single_clause_package_total:
  fixes E :: "local_address option artifact_environment"
    and S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes package: "native_package_at E pu pr P" and schema: "schema_formed S"
    and dependencies: "schema_dependencies S\<subseteq>system_definitions P"
  shows "\<exists>F u v Q T. environment_formed F \<and> environment_included E F \<and>
    u\<notin>environment_uses E \<and> (u,[])\<notin>system_definitions P \<and>
    native_package_at F pu pr P \<and> native_package_at F v [] Q \<and>
    system_definitions Q=insert (u,[]) (system_definitions P) \<and>
    native_single_clause_at F u [] T \<and> schema_alpha_variant S T \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q d z \<longleftrightarrow> schema_call_formed P d z) \<and>
      ((d,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have targets: "\<forall>d\<in>schema_dependencies S. \<exists>A. artifact_at E (fst d) A \<and> anchor_formed (A,snd d)"
  proof (intro ballI)
    fix d assume dependency: "d\<in>schema_dependencies S"
    have member: "d\<in>system_definitions P" using dependencies dependency by blast
    obtain p C where read: "native_definition_at E (fst d) (snd d) p C"
      using native_package_definition_exists[OF package member] by blast
    show "\<exists>A. artifact_at E (fst d) A \<and> anchor_formed (A,snd d)"
      by (rule native_definition_has_anchor[OF read])
  qed
  obtain H u T where installed: "environment_formed H" "environment_included E H"
    "u\<notin>environment_uses E" "native_single_clause_at H u [] T" "schema_alpha_variant S T"
    "\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance S X t"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at H w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot H w s x \<longleftrightarrow> binds_slot E w s x"
    using native_single_clause_compilation[OF schema ef targets] by blast
  have copied: "native_package_at H pu pr P" by (rule native_package_included[OF package installed(2,1)])
  have dep: "schema_dependencies T\<subseteq>system_definitions P"
    using dependencies by (simp only: schema_alpha_dependencies[OF installed(5)])
  let ?d="(u,[])" let ?D="insert ?d (system_definitions P)"
  have fresh: "?d\<notin>system_definitions P"
  proof
    assume member: "?d\<in>system_definitions P"
    have site: "?d\<in>environment_positions E" by (rule native_package_entry_position[OF package member])
    have "u\<in>environment_uses E"
      using site by (auto simp: environment_positions_def environment_uses_def artifact_at_def rel_dom_def)
    then show False using installed(3) by blast
  qed
  obtain i c where single: "native_definition_at H u [] (Pattern_Variable i) {(c,T)}"
    using installed(4) by (auto simp: native_single_clause_at_def)
  have reads: "\<exists>p C. native_definition_at H (fst d) (snd d) p C" if "d\<in>?D" for d
  proof (cases "d=?d")
    case True
    show ?thesis by (rule exI[of _ "Pattern_Variable i"], rule exI[of _ "{(c,T)}"])
      (use single True in simp)
  next
    case False
    have member: "d\<in>system_definitions P" using that False by simp
    show ?thesis by (rule native_package_definition_exists[OF copied member])
  qed
  have closed: "e\<in>?D" if member: "d\<in>?D" and edge: "(d,e)\<in>native_definition_edges H" for d e
  proof (cases "d=?d")
    case True
    have read: "native_definition_at H (fst d) (snd d) (Pattern_Variable i) {(c,T)}"
      using single True by simp
    have "e\<in>schema_dependencies T" using edge by (simp only: native_definition_edges_at[OF read]; auto)
    then show ?thesis using dep by blast
  next
    case False
    have old: "d\<in>system_definitions P" using member False by simp
    show ?thesis using native_package_edge_closed[OF copied old edge] by simp
  qed
  have selectable: "\<exists>F v Q. environment_formed F \<and> environment_included H F \<and>
    native_package_at F v [] Q \<and> system_definitions Q=?D \<and>
    (\<forall>w\<in>environment_uses H. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at H w A) \<and>
    (\<forall>w\<in>environment_uses H. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot H w s x)"
  proof (rule native_definition_family_selection[OF installed(1)])
    fix d assume member: "d\<in>?D"
    show "\<exists>p C. native_definition_at H (fst d) (snd d) p C" by (rule reads[OF member])
  next
    fix d e assume member: "d\<in>?D" and edge: "(d,e)\<in>native_definition_edges H"
    show "e\<in>?D" by (rule closed[OF member edge])
  qed
  obtain F v Q where selected: "environment_formed F" "environment_included H F"
    "native_package_at F v [] Q" "system_definitions Q=?D"
    "\<forall>w\<in>environment_uses H. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at H w A"
    "\<forall>w\<in>environment_uses H. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot H w s x"
    using selectable by blast
  have included: "environment_included E F" by (rule environment_included_trans[OF installed(2) selected(2)])
  have old: "native_package_at F pu pr P" by (rule native_package_included[OF package included selected(1)])
  have read: "native_single_clause_at F u [] T" by (rule native_single_clause_included[OF installed(4) selected(2,1)])
  have meanings: "(schema_call_formed Q d z \<longleftrightarrow> schema_call_formed P d z) \<and>
      ((d,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)"
    if member: "d\<in>system_definitions P" for d z
  proof -
    have in_Q: "d\<in>system_definitions Q" using member selected(4) by simp
    show ?thesis using native_packages_shared_call[OF selected(3) old in_Q member, of z]
      native_packages_shared_meaning[OF selected(3) old in_Q member, of z] by blast
  qed
  have uses: "environment_uses E\<subseteq>environment_uses H" by (rule included_uses[OF installed(2)])
  have artifacts: "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    using uses selected(5) installed(7) by blast
  have bindings: "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x"
    using uses selected(6) installed(8) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ v], rule exI[of _ Q], rule exI[of _ T])
    (use selected(1,3,4) included installed(3,5,6) fresh old read meanings artifacts bindings in blast)
qed

text \<open>
  The supplied clause may have arbitrary ordinary and material premises.
  Its actual callees must already belong to the complete original package.
  Compilation changes only private binder and socket coordinates. The common
  selection theorem installs a root family for the original definitions and
  the new definition. Both packages coexist unchanged in the final environment,
  so every original interface and positive meaning is preserved.
\<close>

end
