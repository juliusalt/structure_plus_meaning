theory Factor_Package_Omissions
  imports Factor_Compiled_Applications Factor_Application_Retention RRA_Binding_Omissions
begin

section \<open>Actual external root selections require their explicit bindings\<close>

lemma native_root_external_binding:
  assumes family: "native_root_family_at E u r Q" and member: "d\<in>rel_ran Q"
    and external: "fst d\<noteq>u"
  shows "\<exists>k. binds_slot E u k (fst d)"
proof -
  obtain s where entry: "(s,d)\<in>Q" using member by (auto simp: rel_ran_def)
  obtain a where loc: "located_at E u a (fst d) (snd d)"
    using native_root_family_origin[OF family entry] by blast
  obtain c where read: "citation_location E u c (fst d) (snd d)"
    using loc unfolding located_at_def by blast
  show ?thesis using read external by (cases c) auto
qed

theorem native_package_external_selection:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and nonempty: "system_definitions P\<noteq>{}"
  shows "\<exists>F u k d R. closed_native_package_at F u [] P \<and> native_package_environment F u []=F \<and>
    binds_slot F u k (fst d) \<and> u\<noteq>fst d \<and> d\<in>system_definitions P \<and>
    artifact_at F (fst d) R \<and> anchor_formed (R,snd d)"
proof -
  let ?D="native_package_roots E pu pr"
  have dependency_package: "native_package_formed E ?D" and program: "P=native_program E ?D"
    by (rule native_package_projection[OF package])+
  have ef: "environment_formed E" using dependency_package by (simp add: native_package_formed_def)
  have roots: "?D\<subseteq>native_definition_sites E ?D" by (rule native_definition_roots)
  have finite: "finite ?D" by (rule finite_subset[OF roots native_package_sites(2)[OF dependency_package]])
  have nonempty_roots: "?D\<noteq>{}"
  proof
    assume empty: "?D={}"
    have "system_definitions P={}"
      using native_package_projection(3)[OF package] empty
      by (simp add: native_package_sites_def native_definition_sites_def)
    then show False using nonempty by blast
  qed
  obtain d where member: "d\<in>?D" using nonempty_roots by blast
  have target: "d\<in>system_definitions P"
    using roots member native_package_projection(3)[OF package] by (auto simp: native_package_sites_def)
  have anchors: "\<forall>e\<in>?D. \<exists>R. artifact_at E (fst e) R \<and> anchor_formed (R,snd e)"
  proof (intro ballI)
    fix e assume root: "e\<in>?D"
    have inside: "e\<in>system_definitions P"
      using roots root native_package_projection(3)[OF package] by (auto simp: native_package_sites_def)
    show "\<exists>R. artifact_at E (fst e) R \<and> anchor_formed (R,snd e)"
      by (rule native_package_definition_anchor[OF package inside])
  qed
  obtain H u Q where installed: "environment_formed H" "environment_included E H" "u\<notin>environment_uses E"
    "native_root_family_at H u [] Q" "rel_ran Q=?D"
    using root_family_environment_total[OF ef finite anchors] by blast
  have copied: "native_package_formed H ?D \<and> native_program H ?D=native_program E ?D"
    by (rule native_dependency_package_included[OF dependency_package installed(2,1)])
  have native: "native_package_at H u [] P"
    unfolding native_package_at_def by (rule exI[of _ Q]) (use installed(4,5) copied program in auto)
  let ?F="native_package_environment H u []"
  have closed: "closed_native_package_at ?F u [] P" by (rule native_package_closed_restriction[OF native])
  have kept: "native_package_at ?F u [] P" using closed by (simp add: closed_native_package_at_def)
  have canonical: "native_package_environment ?F u []=?F" by (rule native_package_environment_idempotent[OF native])
  have family: "native_root_family_at ?F u [] Q" by (rule native_package_environment_roots[OF native installed(4)])
  have entry: "d\<in>rel_ran Q" using member installed(5) by simp
  have old_use: "fst d\<in>environment_uses E"
    using anchors member by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have different: "u\<noteq>fst d" using installed(3) old_use by blast
  obtain k where binding: "binds_slot ?F u k (fst d)"
    using native_root_external_binding[OF family entry] different by blast
  obtain R where source: "artifact_at ?F (fst d) R" "anchor_formed (R,snd d)"
    using native_package_definition_anchor[OF kept target] by blast
  show ?thesis
    by (rule exI[of _ ?F], rule exI[of _ u], rule exI[of _ k], rule exI[of _ d], rule exI[of _ R])
       (use closed canonical binding different target source in blast)
qed

section \<open>Omitting a required program binding cannot select another program\<close>

theorem native_package_required_binding_omitted:
  assumes package: "native_package_at E pu pr P"
    and required: "binds_slot (native_package_environment E pu pr) u k v"
  shows "\<not>(\<exists>Q. native_package_at (omit_binding E u k) pu pr Q)"
proof
  assume "\<exists>Q. native_package_at (omit_binding E u k) pu pr Q"
  then obtain Q where other: "native_package_at (omit_binding E u k) pu pr Q" by blast
  have retained: "environment_included (native_package_environment E pu pr) (omit_binding E u k)"
    by (rule native_package_dependency_material_required[OF package other omit_binding_included])
  show False using omitted_binding_excludes_environment[OF required] retained by blast
qed

lemma native_application_omit_other_binding:
  assumes app: "native_application_at E au ar d t I K" and other: "au\<noteq>u"
  shows "native_application_at (omit_binding E u k) au ar d t I K"
proof -
  let ?D="native_application_demands E au ar"
  let ?A="read_environment E {au} ?D"
  have boundary: "read_boundary_formed E {au} ?D" by (rule native_application_read_boundary[OF app])
  have slots: "\<forall>a\<in>K. (au,a)\<in>?D" using native_application_demands_at[OF app] by blast
  have retained: "native_application_at ?A au ar d t I K"
    by (rule native_application_read_environment[OF app boundary _ slots]) simp
  have outside: "(u,k)\<notin>?D" using other native_application_demands_at[OF app] by auto
  have included: "environment_included ?A (omit_binding E u k)"
    by (rule omit_binding_preserves_unrequested_scope[OF outside])
  have ef: "environment_formed E" using app by (simp add: native_application_at_def)
  show ?thesis by (rule native_application_included[OF retained included omit_binding_formed[OF ef]])
qed

text \<open>
  Every nonempty actual program can be selected through a new external root
  family, then restricted to its complete minimal scope. At least one genuine
  binding is required there. Its target is an actual definition of the same
  recovered program. This construction changes neither the definition sites
  nor the program's positive meaning.

  Omitting any binding required by a recovered package prevents every program
  reading at that package site. All artifacts remain present. A call located
  at a different source use retains its complete syntax and argument reading;
  its required bindings are local to that call's own source. Reading the call
  alone does not recover the omitted semantic dependency.
\<close>

end
