theory Factor_Root_Environments
  imports Factor_Root_Syntax Factor_Package_Locality
begin

section \<open>Installing an actual complete root selector over an existing environment\<close>

theorem root_family_environment_total:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and fin: "finite D"
    and targets: "\<forall>d\<in>D. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  shows "\<exists>F u Q. environment_formed F \<and> environment_included E F \<and> u \<notin> environment_uses E \<and>
    native_root_family_at F u [] Q \<and> rel_ran Q = D \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  obtain ds :: "local_address option definition_site list" where enumeration: "set ds=D" "distinct ds"
    using finite_distinct_list[OF fin] by metis
  have addresses: "\<forall>d\<in>set ds. octets_formed (snd d)"
  proof (intro ballI)
    fix d assume member: "d \<in> set ds"
    have actual: "d \<in> D" using member enumeration(1) by simp
    obtain R where target: "anchor_formed (R,snd d)" using targets actual by blast
    show "octets_formed (snd d)" using target by (auto simp: anchor_formed_def exact_formed_def)
  qed
  obtain R :: exact_artifact and C :: "(local_address \<times> local_address option definition_site) set" where code:
    "exact_formed R" "reference_table_formed {} C"
    "rel_dom C \<subseteq> rra_carrier (object_structure R)" "rel_ran C = set ds"
    "\<forall>F u. environment_formed F \<longrightarrow> artifact_at F u R \<longrightarrow> syntax_references F u {} C \<longrightarrow>
      native_root_family_at F u [] (set (zip (family_ports (length ds)) ds))"
    using root_family_syntax_total[OF addresses] by metis
  have callees: "\<forall>d\<in>rel_ran C. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    using targets code(4) enumeration(1) by simp
  have bounds: "rel_dom {} \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)" using code(3) by simp
  obtain F u where installed: "environment_formed F" "environment_included E F" "u \<notin> environment_uses E"
    "artifact_at F u R" "syntax_references F u {} C"
    "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using reference_environment_total[OF ef code(1,2) bounds callees] by metis
  let ?Q = "set (zip (family_ports (length ds)) ds)"
  have read: "native_root_family_at F u [] ?Q" using code(5) installed(1,4,5) by blast
  have range: "rel_ran ?Q=D" using zip_range[of "family_ports (length ds)" ds] enumeration(1) by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ ?Q])
    (use installed read range in blast)
qed

lemma native_definition_has_anchor:
  assumes read: "native_definition_at E u r p C"
  shows "\<exists>R. artifact_at E u R \<and> anchor_formed (R,r)"
proof -
  have ef: "environment_formed E" using read by (simp add: native_definition_at_def)
  obtain R ps xs where source: "artifact_at E u R" "record_at R r ps xs"
    using read by (auto simp: native_definition_at_def)
  have rf: "exact_formed R" using ef source(1) unfolding environment_formed_def by blast
  have inside: "r \<in> rra_carrier (object_structure R)" using source(2) by (simp add: record_at_def)
  show ?thesis using source(1) rf inside by (auto simp: anchor_formed_def)
qed

theorem native_dependency_package_selectable:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_formed E D"
  shows "\<exists>F u. environment_formed F \<and> environment_included E F \<and>
    native_package_at F u [] (native_program E D)"
proof -
  have ef: "environment_formed E" using package by (simp add: native_package_formed_def)
  have finite_sites: "finite (native_definition_sites E D)" by (rule native_package_sites(2)[OF package])
  have roots: "D \<subseteq> native_definition_sites E D" by (rule native_definition_roots)
  have fin: "finite D" by (rule finite_subset[OF roots finite_sites])
  have targets: "\<forall>d\<in>D. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  proof (intro ballI)
    fix d assume member: "d \<in> D"
    have site: "d \<in> native_definition_sites E D" by (rule subsetD[OF roots member])
    obtain p C where read: "native_definition_at E (fst d) (snd d) p C"
      using package site by (auto simp: native_package_formed_def)
    show "\<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)" by (rule native_definition_has_anchor[OF read])
  qed
  obtain F u Q where installed: "environment_formed F" "environment_included E F"
    "native_root_family_at F u [] Q" "rel_ran Q=D"
    using root_family_environment_total[OF ef fin targets] by metis
  have copied: "native_package_formed F D \<and> native_program F D = native_program E D"
    by (rule native_dependency_package_included[OF package installed(2,1)])
  have native: "native_package_at F u [] (native_program E D)"
    unfolding native_package_at_def
    by (rule exI[of _ Q]) (use installed(3,4) copied in auto)
  show ?thesis using installed(1,2) native by blast
qed

text \<open>
  Every finite recovered dependency package can receive a concrete structural
  root selector. Its citation family selects exactly the supplied roots, and
  the resulting native package reader recovers the same complete program.
  Existing artifact values and bindings survive the selector installation.
\<close>

end
