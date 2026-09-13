theory Factor_Finite_Code_Installation
  imports Factor_Finite_Program_Compilation Factor_Finite_Reference_Environments
begin

section \<open>The complete compiled row family installs its actual code and references\<close>

definition finite_install_code_rows :: "local_address option finite_artifact_environment\<Rightarrow>
    (local_address option definition_site\<times>finite_definition_code) list\<Rightarrow>
    local_address option finite_artifact_environment" where
  "finite_install_code_rows E rows=(let K=\<lambda>d. the (map_of rows d) in
    finite_fresh_reference_sequence E (map (\<lambda>r. fst (fst r)) rows)
      (\<lambda>u. finite_definition_artifact (K (u,[])))
      (\<lambda>u. finite_definition_literals (K (u,[])))
      (\<lambda>u. finite_definition_callees (K (u,[]))))"

theorem finite_install_code_rows_correct:
  assumes environment: "finite_environment_formed E"
    and formed: "finite_system_formed P"
    and members: "set ds\<subseteq>fset (finite_system_definitions P)"
    and distinct: "distinct ds"
    and roots: "\<forall>d\<in>set ds. snd d=[]"
    and fresh: "image fst (set ds)\<inter>fset (finite_environment_uses E)={}"
    and old: "system_definitions (decode_finite_system P)-set ds\<subseteq>
      environment_positions (decode_finite_environment E)"
    and compiled: "finite_compile_definitions P ds=Some rows"
  shows "let F=finite_install_code_rows E rows; K=\<lambda>d. the (map_of rows d) in
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    (\<forall>d\<in>set ds. definition_code_for (system_interface (decode_finite_system P) d)
      (system_clause_family (decode_finite_system P) d) (decode_finite_definition_code (K d)) \<and>
      native_definition_at (decode_finite_environment F) (fst d) (snd d)
        (decode_finite_pattern (finite_definition_interface (K d)))
        (map_relation_values decode_finite_schema (fset (finite_definition_clauses (K d))))) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
proof -
  let ?P="decode_finite_system P"
  let ?E="decode_finite_environment E"
  let ?F="finite_install_code_rows E rows"
  let ?K="\<lambda>d. the (map_of rows d)"
  let ?K'="\<lambda>d. decode_finite_definition_code (?K d)"
  let ?us="map (\<lambda>r. fst (fst r)) rows"
  let ?R="\<lambda>u. finite_definition_artifact (?K (u,[]))"
  let ?L="\<lambda>u. finite_definition_literals (?K (u,[]))"
  let ?C="\<lambda>u. finite_definition_callees (?K (u,[]))"
  have pf: "schema_system_formed ?P" using formed by (simp only: finite_system_formed_correct)
  have inside: "set ds\<subseteq>system_definitions ?P" using members by (simp only: finite_system_definitions_correct)
  have keys: "map fst rows=ds"
    and codes: "\<forall>d\<in>set ds. definition_code_for (system_interface ?P d) (system_clause_family ?P d) (?K' d)"
    by (rule finite_compile_definitions_correct[OF formed members compiled])+
  interpret family: rooted_code_family ?P "set ds" ?K'
    by (rule rooted_code_family.intro[OF pf inside roots codes])
  have sequence: "?us=map fst ds" using keys by (simp only: keys[symmetric] map_map comp_def)
  have uses: "set ?us=family.uses" by (simp only: sequence set_map)
  have injective: "inj_on fst (set ds)"
  proof (rule inj_onI)
    fix d e assume left: "d\<in>set ds" and right: "e\<in>set ds" and same: "fst d=fst e"
    have "(fst d,[]::local_address)=(fst e,[])" using same by simp
    then show "d=e" by (simp only: family.site_shape[OF left] family.site_shape[OF right])
  qed
  have unique: "distinct ?us" using distinct injective by (simp add: sequence distinct_map)
  have separate: "set ?us\<inter>fset (finite_environment_uses E)={}" using fresh by (simp only: uses)
  have artifacts: "\<forall>u\<in>set ?us. finite_exact_formed (?R u)"
    using family.artifact_formation by (simp only: uses finite_exact_formed_correct decode_finite_definition_code_def definition_code.select_convs)
  have profiles: "\<forall>u\<in>set ?us. reference_table_formed
    (map_relation_values decode_finite_object (fset (?L u))) (fset (?C u))"
    using family.profiles by (simp only: uses decode_finite_definition_code_def definition_code.select_convs)
  have bounds: "\<forall>u\<in>set ?us. rel_dom (fset (?L u))\<union>rel_dom (fset (?C u))\<subseteq>
    fset (finite_carrier (finite_structure (?R u)))"
    using family.bounds by (simp only: uses decode_finite_definition_code_def definition_code.select_convs
      map_relation_values_domain decode_finite_object_selectors decode_finite_structure_fields)
  have targets: "\<forall>u\<in>set ?us. \<forall>d\<in>rel_ran (fset (?C u)).
    d\<in>environment_positions ?E \<or> (fst d\<in>set ?us \<and> snd d\<in>fset (finite_carrier (finite_structure (?R (fst d)))))"
  proof (intro ballI)
    fix u d assume use: "u\<in>set ?us" and callee: "d\<in>rel_ran (fset (?C u))"
    have use': "u\<in>family.uses" using use by (simp only: uses)
    have callee': "d\<in>rel_ran (family.callees u)"
      using callee by (simp only: decode_finite_definition_code_def definition_code.select_convs)
    have source: "d\<in>system_definitions ?P" by (rule family.callee_source[OF use' callee'])
    show "d\<in>environment_positions ?E \<or>
      (fst d\<in>set ?us \<and> snd d\<in>fset (finite_carrier (finite_structure (?R (fst d)))))"
    proof (cases "d\<in>set ds")
      case True
      show ?thesis using family.internal_anchor[OF True]
        by (simp only: uses decode_finite_definition_code_def definition_code.select_convs
          decode_finite_object_selectors decode_finite_structure_fields; blast)
    next
      case False
      show ?thesis using old source False by blast
    qed
  qed
  have installation: "?F=finite_fresh_reference_sequence E ?us ?R ?L ?C"
    by (simp add: finite_install_code_rows_def Let_def)
  have actual: "finite_environment_formed ?F" "environment_included ?E (decode_finite_environment ?F)"
    "\<forall>u\<in>set ?us. artifact_at (decode_finite_environment ?F) u (decode_finite_object (?R u)) \<and>
      syntax_references (decode_finite_environment ?F) u
        (map_relation_values decode_finite_object (fset (?L u))) (fset (?C u))"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment ?F) w A \<longleftrightarrow> artifact_at ?E w A"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment ?F) w k v \<longleftrightarrow> binds_slot ?E w k v"
    using finite_fresh_reference_sequence_properties[OF environment unique separate artifacts profiles bounds targets]
    by (simp only: Let_def installation[symmetric]; blast)+
  have ff: "environment_formed (decode_finite_environment ?F)" using actual(1) by (simp only: finite_environment_formed_correct)
  have components: "\<forall>u\<in>family.uses. artifact_at (decode_finite_environment ?F) u (family.artifacts u) \<and>
      syntax_references (decode_finite_environment ?F) u (family.literals u) (family.callees u)"
    using actual(3) by (simp only: uses decode_finite_definition_code_def definition_code.select_convs)
  have readings: "\<forall>d\<in>set ds. definition_code_for (system_interface ?P d) (system_clause_family ?P d) (?K' d) \<and>
      native_definition_at (decode_finite_environment ?F) (fst d) (snd d)
        (decode_finite_pattern (finite_definition_interface (?K d)))
        (map_relation_values decode_finite_schema (fset (finite_definition_clauses (?K d))))"
    using family.installed[OF ff components]
    by (simp only: decode_finite_definition_code_def definition_code.select_convs; blast)
  show ?thesis using actual(1,2,4,5) readings by (simp only: Let_def; blast)
qed

export_code finite_install_code_rows checking SML

end
