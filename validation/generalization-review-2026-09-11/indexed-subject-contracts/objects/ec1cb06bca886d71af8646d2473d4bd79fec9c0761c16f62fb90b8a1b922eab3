theory Factor_Native_Proofs
  imports Factor_Graph_Construction Factor_Future_Applications
begin

section \<open>Every valid graph has a complete native realization\<close>

theorem derived_graph_native_realization:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P"
    and derived: "schema_graph_derives (positioned_program P) G root d t H"
  shows "\<exists>F h. environment_formed F \<and> environment_included E F \<and> inj_on h (schema_graph_nodes G) \<and>
    native_package_at F pu pr P \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    native_schema_graph_at F (h root) (rename_schema_graph h G) \<and>
    schema_graph_derives (positioned_program P) (rename_schema_graph h G) (h root) d t (image (map_prod h id) H) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v)"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have formed: "schema_graph_formed G root"
    using derived by (auto simp: schema_graph_derives_def schema_graph_reading_def)
  have metadata: "graph_metadata_at E G" by (rule derived_graph_metadata[OF package derived])
  obtain F h where placed: "environment_formed F" "environment_included E F" "inj_on h (schema_graph_nodes G)"
    "native_schema_graph_at F (h root) (rename_schema_graph h G)"
    "\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T"
    "\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
    using native_graph_construction_total[OF ef formed metadata] by blast
  have copied: "schema_graph_derives (positioned_program P) (rename_schema_graph h G)
    (h root) d t (image (map_prod h id) H)"
    by (rule schema_graph_derives_rename[OF derived placed(3)])
  have retained: "native_package_at F pu pr P" by (rule native_package_included[OF package placed(2,1)])
  have canonical: "native_package_environment F pu pr=native_package_environment E pu pr"
    by (rule native_package_environment_extension[OF package placed(2,1)])
  show ?thesis by (rule exI[of _ F], rule exI[of _ h]) (use placed copied retained canonical in blast)
qed

section \<open>Actual positive applications have native closed proofs\<close>

theorem native_positive_proof_total:
  fixes E :: "local_address option artifact_environment"
  assumes positive: "native_positive_holds E pu pr au ar"
  shows "\<exists>F P d t I K G root. environment_formed F \<and> environment_included E F \<and>
    native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    native_schema_graph_at F root G \<and> schema_graph_derives (positioned_program P) G root d t {} \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    (\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v)"
proof -
  obtain P d t I K where source: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "(d,t)\<in>positive_meaning P" using positive by (auto simp: native_positive_holds_def)
  have pf: "schema_system_formed P" by (rule positive_meaning_has_formed_system[OF source(3)])
  have located: "(d,t)\<in>positive_meaning (positioned_program P)"
    using source(3) positioned_program_meaning[OF pf] by simp
  obtain G :: "(local_address option definition_site,local_address option definition_site,
      local_address option definition_site,local_address) schema_derivation_graph"
    and root where derived: "schema_graph_derives (positioned_program P) G root d t {}"
    using addressed_schema_graph_complete[OF located] by blast
  obtain F h where built: "environment_formed F" "environment_included E F"
    "native_package_at F pu pr P" "native_package_environment F pu pr=native_package_environment E pu pr"
    "native_schema_graph_at F (h root) (rename_schema_graph h G)"
    "schema_graph_derives (positioned_program P) (rename_schema_graph h G) (h root) d t {}"
    "\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T"
    "\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
    using derived_graph_native_realization[OF source(1) derived] by auto
  have call: "native_application_at F au ar d t I K"
    by (rule native_application_included[OF source(2) built(2,1)])
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K],
        rule exI[of _ "rename_schema_graph h G"], rule exI[of _ "h root"])
       (use built call source in blast)
qed

text \<open>
  Native realization is now total for every valid finite graph against an
  actual native program. The construction retains all source node identities
  through an injective map, including distinct assertions and explicit sharing.
  The selected program, complete call, and exact assertion values stay fixed.
  Every positive native application has a realized closed proof in a finite
  environment extending its original one. Retention and replay remain separate.
\<close>

end
