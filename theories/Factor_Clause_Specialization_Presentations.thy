theory Factor_Clause_Specialization_Presentations
  imports Factor_Prescribed_Environments Factor_Clause_Specialization_Instances
begin

section \<open>Replacement records use the prescribed target-variable coordinates\<close>

theorem pattern_record_environment_at_coordinates:
  assumes formed: "\<forall>p\<in>set ps. pattern_formed p"
    and addressing: "binder_addressing (pattern_forest_variables ps) f"
    and scope: "f ` pattern_forest_variables ps\<subseteq>B" and boundary: "B\<subseteq>binder_addresses"
  shows "environment_formed (literal_environment (pattern_record_syntax f ps) (pattern_forest_bindings ps))"
    "pattern_record_at (literal_environment (pattern_record_syntax f ps) (pattern_forest_bindings ps))
      None B [] (map (rename_pattern f) ps) (pattern_record_interior ps) (rel_dom (pattern_forest_bindings ps))"
proof -
  let ?R="pattern_record_syntax f ps"
  let ?L="pattern_forest_bindings ps"
  let ?F="literal_environment ?R ?L"
  have rf: "exact_formed ?R" by (rule pattern_record_syntax_formed[OF formed addressing])
  have bounds: "rel_dom ?L\<subseteq>rra_carrier (object_structure ?R)"
    by (auto simp: pattern_record_syntax_carrier[OF addressing])
  show ff: "environment_formed ?F"
    by (rule literal_environment_formed[OF rf pattern_forest_bindings_finite
      pattern_forest_bindings_functional pattern_forest_bindings_formed[OF formed] bounds])
  show "pattern_record_at ?F None B [] (map (rename_pattern f) ps)
      (pattern_record_interior ps) (rel_dom (pattern_forest_bindings ps))"
    by (rule pattern_record_syntax_recovers[OF formed addressing scope boundary ff]) simp_all
qed

section \<open>Complete clause specializations have coordinated native presentations\<close>

theorem clause_specialization_at_coordinates:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E u r P" and source: "((d,c),S)\<in>system_clauses P"
    and specialization: "schema_clause_specialization P d c V T"
    and addressing: "binder_addressing (schema_variables T) f"
    and separate: "f ` schema_variables T \<inter> schema_sockets T={}"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>G w t As I K.
    environment_formed F \<and> environment_formed G \<and>
    environment_included E G \<and> w\<notin>environment_uses E \<and>
    distinct As \<and> set As=schema_variables S \<and>
    pattern_record_at F None (f ` schema_variables T) []
      (substitution_row_patterns As (rename_pattern f \<circ> rel_value V)) I K \<and>
    native_schema_at G w t (rename_schema f id id T) \<and>
    schema_clause_specialization_at E u r d c F None [] G w t \<and>
    (\<forall>v\<in>environment_uses E. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at E v A) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k x. binds_slot G v k x \<longleftrightarrow> binds_slot E v k x)"
proof -
  obtain a where raw: "native_schema_at E (fst d) a S"
    using native_package_schema_origin[OF package source] by blast
  have formed: "schema_formed S" by (rule native_schema_formed[OF raw])
  have ef: "environment_formed E" using raw by (simp add: native_schema_at_def)
  have source_addresses: "\<forall>a\<in>schema_variables S. octets_formed a"
    by (rule native_schema_variables_formed[OF raw])
  have source_sockets: "\<forall>a\<in>schema_sockets S. octets_formed a"
    using native_schema_data_formed[OF raw] by (simp add: schema_data_formed_def)
  have bindings: "pattern_bindings_formed (schema_variables S) V"
    and substitution: "T=schema_substitute (rel_value V) S"
    using schema_clause_specialization_source[OF specialization source] by blast+
  have boundary: "schema_pattern_boundary P d T"
    using specialization by (simp add: schema_clause_specialization_def)
  have tf: "schema_formed T" using boundary by (simp add: schema_pattern_boundary_def)
  have dependencies: "schema_dependencies T\<subseteq>system_definitions P"
    using boundary schema_pattern_call_formed(2)[of P]
    by (auto simp: schema_pattern_boundary_def schema_dependencies_def rel_ran_def; blast)
  have positions: "system_definitions P\<subseteq>environment_positions E"
    using native_package_sites(1)[OF native_package_projection(1)[OF package]]
      native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  have anchors: "\<forall>b\<in>schema_dependencies T. \<exists>A. artifact_at E (fst b) A \<and> anchor_formed (A,snd b)"
    using dependencies positions environment_position_anchor[OF ef] by blast
  have sockets: "finite_addressing (schema_sockets T) id"
    using source_sockets by (simp add: substitution finite_addressing_def)
  have apart: "f ` schema_variables T \<inter> id ` schema_sockets T={}" using separate by simp
  obtain G w R t where target: "environment_formed G" "environment_included E G" "w\<notin>environment_uses E"
    "native_schema_at G w t (rename_schema f id id T)"
    "\<forall>v\<in>environment_uses E. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at E v A"
    "\<forall>v\<in>environment_uses E. \<forall>k x. binds_slot G v k x \<longleftrightarrow> binds_slot E v k x"
    using schema_environment_at_coordinates[OF tf ef anchors addressing sockets apart] by blast
  obtain As where order: "distinct As" "set As=schema_variables S"
    using finite_distinct_list[OF schema_variables_finite[OF formed]] by blast
  let ?ps="substitution_row_patterns As (rel_value V)"
  let ?s="rename_pattern f \<circ> rel_value V"
  let ?F="literal_environment (pattern_record_syntax f ?ps) (pattern_forest_bindings ?ps)"
  let ?I="pattern_record_interior ?ps"
  let ?K="rel_dom (pattern_forest_bindings ?ps)"
  have psformed: "\<forall>p\<in>set ?ps. pattern_formed p"
    using source_addresses pattern_binding_at(2)[OF bindings] by (simp only: substitution_row_formed order(2); blast)
  have psvariables: "pattern_forest_variables ?ps=schema_variables T"
    by (simp only: substitution_row_variables order(2) substitution schema_substitute_variables)
  have psaddressing: "binder_addressing (pattern_forest_variables ?ps) f" using addressing by (simp only: psvariables)
  have psscope: "f ` pattern_forest_variables ?ps\<subseteq>f ` schema_variables T" by (simp only: psvariables)
  have binder_boundary: "f ` schema_variables T\<subseteq>binder_addresses"
    using addressing by (simp add: binder_addressing_def)
  have ff: "environment_formed ?F"
    by (rule pattern_record_environment_at_coordinates(1)[OF psformed psaddressing psscope binder_boundary])
  have psrenamed: "map (rename_pattern f) ?ps=substitution_row_patterns As ?s"
    by (simp add: substitution_row_patterns_def map_map comp_def rename_pattern_def)
  have record_read: "pattern_record_at ?F None (f ` schema_variables T) [] (substitution_row_patterns As ?s) ?I ?K"
    using pattern_record_environment_at_coordinates(2)[OF psformed psaddressing psscope binder_boundary]
    by (simp only: psrenamed)
  have renamed: "schema_substitute ?s S=rename_schema f id id T"
    by (simp only: substitution schema_substitute_renaming[symmetric] schema_substitute_composes
      rename_pattern_def comp_def)
  have finj: "inj_on f (schema_variables T)"
    using addressing by (simp add: binder_addressing_def finite_addressing_def)
  have renamed_boundary: "schema_pattern_boundary P d (rename_schema f id id T)"
    using boundary by (simp only: schema_pattern_boundary_target_alpha[OF tf finj inj_on_id])
  have native: "schema_clause_specialization_at E u r d c ?F None [] G w t"
    unfolding schema_clause_specialization_at_def
    by (rule exI[of _ P], rule exI[of _ S], rule exI[of _ ?s], rule exI[of _ As],
      rule exI[of _ ?I], rule exI[of _ ?K])
      (use package source order record_read target(4) renamed_boundary
        in \<open>simp only: renamed renamed_schema_variables; blast\<close>)
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ G], rule exI[of _ w], rule exI[of _ t],
      rule exI[of _ As], rule exI[of _ ?I], rule exI[of _ ?K])
    (use ff target order record_read native in blast)
qed

theorem native_clause_specialization_representations:
  assumes package: "native_package_at E u r P" and encoded: "environment_value_presents E e"
  shows "\<forall>d c S. \<forall>V::(local_address \<times> 'a term_pattern) set. \<forall>T.
    ((d,c),S)\<in>system_clauses P \<and> schema_clause_specialization P d c V T \<longrightarrow>
    (\<exists>f F G w t As I K z y. binder_addressing (schema_variables T) f \<and>
      f ` schema_variables T \<inter> schema_sockets T={} \<and>
      environment_formed F \<and> environment_formed G \<and> environment_included E G \<and> w\<notin>environment_uses E \<and>
      distinct As \<and> set As=schema_variables S \<and>
      pattern_record_at F None (f ` schema_variables T) []
        (substitution_row_patterns As (rename_pattern f \<circ> rel_value V)) I K \<and>
      native_schema_at G w t (rename_schema f id id T) \<and>
      environment_value_presents F z \<and> environment_value_presents G y \<and>
      (294,clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) z (use_data_term None) (Payload_Term [])
        y (use_data_term w) (Payload_Term t))\<in>positive_meaning clause_specialization_reading_system \<and>
      (\<forall>v\<in>environment_uses E. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at E v A) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k x. binds_slot G v k x \<longleftrightarrow> binds_slot E v k x))"
proof (intro allI impI)
  fix d c S and V :: "(local_address \<times> 'a term_pattern) set" and T
  assume actual: "((d,c),S)\<in>system_clauses P \<and> schema_clause_specialization P d c V T"
  have source: "((d,c),S)\<in>system_clauses P" and specialization: "schema_clause_specialization P d c V T"
    using actual by blast+
  have tf: "schema_formed T" using specialization by (simp add: schema_clause_specialization_def schema_pattern_boundary_def)
  have finite: "finite (schema_sockets T)" using tf by (simp add: schema_sockets_def schema_formed_def finite_rel_dom)
  obtain f where addressing: "binder_addressing (schema_variables T) f"
    and separate: "f ` schema_variables T \<inter> schema_sockets T={}"
    using binder_addressing_avoiding[OF schema_variables_finite[OF tf] finite] by blast
  obtain F :: "local_address option artifact_environment" and G w t As I K
    where built: "environment_formed F" "environment_formed G"
    "environment_included E G" "w\<notin>environment_uses E" "distinct As" "set As=schema_variables S"
    "pattern_record_at F None (f ` schema_variables T) []
      (substitution_row_patterns As (rename_pattern f \<circ> rel_value V)) I K"
    "native_schema_at G w t (rename_schema f id id T)"
    "schema_clause_specialization_at E u r d c F None [] G w t"
    "\<forall>v\<in>environment_uses E. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at E v A"
    "\<forall>v\<in>environment_uses E. \<forall>k x. binds_slot G v k x \<longleftrightarrow> binds_slot E v k x"
    using clause_specialization_at_coordinates[OF package source specialization addressing separate] by blast
  obtain z y where encodings: "environment_value_presents F z" "environment_value_presents G y"
    using environment_value_presents_total[OF built(1)] environment_value_presents_total[OF built(2)] by blast
  have admitted: "(294,clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
      (definition_site_value d) (Payload_Term c) z (use_data_term None) (Payload_Term [])
      y (use_data_term w) (Payload_Term t))\<in>positive_meaning clause_specialization_reading_system"
    using built(9) by (simp only: clause_specialization_reading_on_sources[OF encoded encodings])
  show "\<exists>f F G w t As I K z y. binder_addressing (schema_variables T) f \<and>
      f ` schema_variables T \<inter> schema_sockets T={} \<and>
      environment_formed F \<and> environment_formed G \<and> environment_included E G \<and> w\<notin>environment_uses E \<and>
      distinct As \<and> set As=schema_variables S \<and>
      pattern_record_at F None (f ` schema_variables T) []
        (substitution_row_patterns As (rename_pattern f \<circ> rel_value V)) I K \<and>
      native_schema_at G w t (rename_schema f id id T) \<and>
      environment_value_presents F z \<and> environment_value_presents G y \<and>
      (294,clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) z (use_data_term None) (Payload_Term [])
        y (use_data_term w) (Payload_Term t))\<in>positive_meaning clause_specialization_reading_system \<and>
      (\<forall>v\<in>environment_uses E. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at E v A) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k x. binds_slot G v k x \<longleftrightarrow> binds_slot E v k x)"
    by (rule exI[of _ f], rule exI[of _ F], rule exI[of _ G], rule exI[of _ w], rule exI[of _ t],
      rule exI[of _ As], rule exI[of _ I], rule exI[of _ K], rule exI[of _ z], rule exI[of _ y])
      (use addressing separate built encodings admitted in blast)
qed

text \<open>
  The actual package and its encoding precede every future finite clause
  specialization. Construction preserves the source clause and all its
  ordinary and material socket coordinates. One explicit map renames target
  variables in both the replacement record and the entire target schema.
  The existing native entry accepts their resulting joint input.

  The replacement record and target schema are read from separately supplied
  environments and uses. Their variable correspondence is the displayed map;
  equal bare addresses in unrelated uses do not establish physical identity.
  Constructing a complete graph under one actual shared binder remains a
  separate obligation. Material truth remains conditional as in the existing
  specialization theorem.
\<close>

end
