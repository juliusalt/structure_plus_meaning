theory Factor_Source_Clauses
  imports Factor_Term_Sequence_Contracts Factor_Table_Literal_Lookup
    Factor_Table_Admission_Profiles Factor_Composed_Readings
begin

section \<open>Existing table and sequence programs retain their complete meanings\<close>

lemma key_fibre_keyed_agreement:
  "systems_agree_on keyed_list_system key_fibre_system (system_definitions keyed_list_system)"
  by (simp add: key_fibre_system_def environment_identity_system_def environment_admission_system_def
    binding_entries_system_def binding_entry_system_def artifact_entries_system_def
    artifact_entry_admission_system_def systems_agree_on_added)

lemma keyed_projection_agreement:
  "systems_agree_on artifact_projection_system keyed_list_system (system_definitions artifact_projection_system)"
  by (simp add: keyed_list_system_def key_absence_system_def coordinate_admission_system_def
    natural_list_system_def natural_admission_system_def environment_comparison_system_def
    environment_bag_system_def environment_selection_system_def environment_entry_system_def
    artifact_identity_system_def artifact_admission_system_def systems_agree_on_added)

lemma key_fibre_projection_agreement:
  "systems_agree_on artifact_projection_system key_fibre_system (system_definitions artifact_projection_system)"
proof (rule systems_agree_on_transitive[OF keyed_projection_agreement])
  show "systems_agree_on keyed_list_system key_fibre_system (system_definitions artifact_projection_system)"
    by (rule systems_agree_on_subdomain[OF key_fibre_keyed_agreement]) auto
qed

lemma source_component_agreement:
  "systems_agree_on key_fibre_system term_sequence_system
    (system_definitions key_fibre_system\<inter>system_definitions term_sequence_system)"
  by (simp add: systems_agree_on_def)

definition source_components_system :: "(nat,nat,nat,nat) schema_system" where
  "source_components_system=system_union key_fibre_system term_sequence_system"

lemma source_components_formed [simp]: "schema_system_formed source_components_system"
  unfolding source_components_system_def
  by (rule system_union_agree_formed[OF key_fibre_system_formed term_sequence_system_formed source_component_agreement])

lemma source_components_definitions [simp]:
  "system_definitions source_components_system=system_definitions key_fibre_system\<union>system_definitions term_sequence_system"
  by (simp add: source_components_system_def)

lemma source_components_call:
  "schema_call_formed source_components_system d t \<longleftrightarrow>
    d\<in>system_definitions source_components_system \<and> term_formed t"
  using system_union_agree_call[OF key_fibre_system_formed term_sequence_system_formed source_component_agreement, of d t]
  by (simp only: source_components_system_def system_union_definitions key_fibre_call term_sequence_call Un_iff; blast)

lemma source_components_key_meaning:
  assumes "d\<in>system_definitions key_fibre_system"
  shows "(d,t)\<in>positive_meaning source_components_system \<longleftrightarrow> (d,t)\<in>positive_meaning key_fibre_system"
  unfolding source_components_system_def
  by (rule system_union_agree_left_locality(2)[OF key_fibre_system_formed term_sequence_system_formed source_component_agreement assms])

lemma source_components_sequence_meaning:
  assumes "d\<in>system_definitions term_sequence_system"
  shows "(d,t)\<in>positive_meaning source_components_system \<longleftrightarrow> (d,t)\<in>positive_meaning term_sequence_system"
  unfolding source_components_system_def
  by (rule system_union_agree_right_locality(2)[OF key_fibre_system_formed term_sequence_system_formed source_component_agreement assms])

section \<open>Complete source admission precedes either lookup branch\<close>

definition source_base_row_schema :: "(nat,nat,nat) factor_schema" where
  "source_base_row_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,1,Pattern_Pair data_x (Pattern_Payload [])),(1,237,data_y)}"

definition source_context_schema :: "(nat,nat,nat) factor_schema" where
  "source_context_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) data_z data_x),
     (1,238,data_z),
     (2,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) data_w data_y),
     (3,241,data_w)}"

definition source_input_schema :: "(nat,nat,nat) factor_schema" where
  "source_input_schema=data_rule (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) data_w)
    {(0,242,Pattern_Pair data_x data_y),
     (1,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 4) data_x),
     (2,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 5) data_z),
     (3,236,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) data_w)}"

definition source_base_schema :: "(nat,nat,nat) factor_schema" where
  "source_base_schema=data_rule (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) data_w)
    {(0,242,Pattern_Pair data_x data_y),
     (1,1,Pattern_Pair data_z (Pattern_Payload [])),
     (2,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 4) data_y),
     (3,28,Pattern_Pair data_z (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair data_w (Pattern_Payload []))))}"

definition source_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "source_clause_family d=(if d=237 then {(0,reader_projection_clause 0 1 0 10)}
    else if d=238 then list_profile_clauses 237 238
    else if d=239 then {(0,source_base_row_schema)}
    else if d=240 then list_profile_clauses 239 240
    else if d=241 then {(0,table_admission_schema 21 240)}
    else if d=242 then {(0,source_context_schema)}
    else if d=243 then {(0,source_input_schema),(1,source_base_schema)}
    else if d=244 then {(0,composed_reading_schema 243 10)} else {})"

lemmas source_schema_defs = source_base_row_schema_def source_context_schema_def source_input_schema_def
  source_base_schema_def composed_reading_schema_def reader_projection_clause_def table_admission_schema_def
  list_profile_clauses_def data_list_nil_schema_def list_step_schema_def

definition source_group_system :: "(nat,nat,nat,nat) schema_system" where
  "source_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{237,238,239,240,241,242,243,244}},
    system_clauses={((d,c),S). d\<in>{237,238,239,240,241,242,243,244} \<and> (c,S)\<in>source_clause_family d}\<rparr>"

lemma source_group_definitions [simp]:
  "system_definitions source_group_system={237,238,239,240,241,242,243,244}"
  by (auto simp: source_group_system_def system_definitions_def rel_dom_def)

lemma source_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces source_group_system \<longleftrightarrow>
    d\<in>system_definitions source_group_system \<and> p=Pattern_Variable 0"
  by (simp only: source_group_definitions; auto simp: source_group_system_def)

lemma source_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses source_group_system \<longleftrightarrow>
    d\<in>system_definitions source_group_system \<and> (c,S)\<in>source_clause_family d"
  by (simp only: source_group_definitions; auto simp: source_group_system_def)

lemma source_group_formed_over:
  "schema_system_formed_over {1,10,21,28,233,236} source_group_system"
proof -
  have finite: "finite (source_clause_family d)" for d
    by (simp add: source_clause_family_def list_profile_clauses_def)
  have functional: "single_valued (source_clause_family d)" for d
    by (auto simp: source_clause_family_def list_profile_clauses_def single_valued_def split: if_splits)
  have schemas: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{1,10,21,28,233,236}\<union>system_definitions source_group_system"
    if "(c,S)\<in>source_clause_family d" for c S d
    using that by (auto simp: source_clause_family_def source_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def split: if_splits)
  show ?thesis
    by (rule schema_system_formed_over_families[where D="system_definitions source_group_system"
        and p="\<lambda>_. Pattern_Variable 0" and C=source_clause_family])
      (use finite functional schemas in \<open>simp_all only: source_group_definitions; auto simp: source_group_system_def\<close>)+
qed

lemma source_external_dependencies:
  "system_external_dependencies source_group_system={1,10,21,28,233,236}"
proof -
  have bounded: "system_external_dependencies source_group_system\<subseteq>{1,10,21,28,233,236}"
    by (rule system_external_dependencies_boundary[OF source_group_formed_over])
  have reached: "e\<in>system_external_dependencies source_group_system"
    if "((d,c),S)\<in>system_clauses source_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions source_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses source_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3) by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have input: "e\<in>system_external_dependencies source_group_system" if "e\<in>{233,236}" for e
    by (rule reached[where d=243 and c=0 and S=source_input_schema])
      (use that in \<open>auto simp: source_clause_family_def source_input_schema_def schema_dependencies_def rel_ran_image\<close>)
  have base: "e\<in>system_external_dependencies source_group_system" if "e\<in>{1,28}" for e
    by (rule reached[where d=243 and c=1 and S=source_base_schema])
      (use that in \<open>auto simp: source_clause_family_def source_base_schema_def schema_dependencies_def rel_ran_image\<close>)
  have projection: "10\<in>system_external_dependencies source_group_system"
    by (rule reached[where d=237 and c=0 and S="reader_projection_clause 0 1 0 10"])
      (auto simp: source_clause_family_def)
  have keys: "21\<in>system_external_dependencies source_group_system"
    by (rule reached[where d=241 and c=0 and S="table_admission_schema 21 240"])
      (auto simp: source_clause_family_def table_admission_schema_def schema_dependencies_def rel_ran_image)
  show ?thesis using bounded input base projection keys by auto
qed

definition source_base_system :: "(nat,nat,nat,nat) schema_system" where
  "source_base_system=rooted_system source_components_system (system_external_dependencies source_group_system)"

lemma source_base_formed [simp]: "schema_system_formed source_base_system"
  unfolding source_base_system_def by (rule rooted_system_formed[OF source_components_formed])

lemma source_base_subdomain:
  "system_definitions source_base_system\<subseteq>system_definitions source_components_system"
  unfolding source_base_system_def by (rule rooted_system_subdomain)

lemma source_base_roots:
  "{1,10,21,28,233,236}\<subseteq>system_definitions source_base_system"
  unfolding source_base_system_def source_external_dependencies
  by (rule rooted_system_roots[OF source_components_formed]) auto

lemma source_base_least:
  assumes "{1,10,21,28,233,236}\<subseteq>U" "system_dependency_closed source_components_system U"
  shows "system_definitions source_base_system\<subseteq>U"
  unfolding source_base_system_def source_external_dependencies
  by (rule rooted_system_least[OF source_components_formed _ assms]) auto

lemma source_base_call:
  "schema_call_formed source_base_system d t \<longleftrightarrow>
    d\<in>system_definitions source_base_system \<and> term_formed t"
  unfolding source_base_system_def
  by (rule rooted_system_variable_calls[OF source_components_formed source_components_call])

interpretation source_group: positive_definition_group source_base_system source_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF source_group_formed_over source_base_roots] source_base_subdomain in auto)

definition source_system :: "(nat,nat,nat,nat) schema_system" where
  "source_system=system_union source_base_system source_group_system"

lemma source_system_formed [simp]: "schema_system_formed source_system"
  using source_group.formed by (simp only: source_system_def)

lemma source_system_definitions [simp]:
  "system_definitions source_system=system_definitions source_base_system\<union>system_definitions source_group_system"
  by (simp add: source_system_def)

lemma source_system_call:
  "schema_call_formed source_system d t \<longleftrightarrow>
    d\<in>system_definitions source_system \<and> term_formed t"
  unfolding source_system_def
  by (rule source_group.variable_calls[OF source_base_call source_group_interfaces])

lemma source_system_clause:
  assumes "d\<in>system_definitions source_group_system"
  shows "((d,c),S)\<in>system_clauses source_system \<longleftrightarrow> (c,S)\<in>source_clause_family d"
  using source_group.group_clauses[OF assms] assms by (simp add: source_system_def)

lemma source_previous_meaning:
  assumes "d\<in>{1,10,21,28,233,236}"
  shows "(d,t)\<in>positive_meaning source_system \<longleftrightarrow> (d,t)\<in>positive_meaning source_components_system"
proof -
  have member: "d\<in>system_definitions source_base_system" using source_base_roots assms by blast
  show ?thesis using source_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF source_components_formed member[unfolded source_base_system_def], of t]
    by (simp only: source_system_def source_base_system_def; blast)
qed

lemma source_component_meanings:
  "(1,t)\<in>positive_meaning source_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
  "(10,t)\<in>positive_meaning source_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(21,t)\<in>positive_meaning source_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(28,t)\<in>positive_meaning source_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  "(233,t)\<in>positive_meaning source_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
  "(236,t)\<in>positive_meaning source_system \<longleftrightarrow> (236,t)\<in>positive_meaning term_sequence_system"
proof -
  show "(1,t)\<in>positive_meaning source_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
    using source_previous_meaning[of 1 t] source_components_key_meaning[of 1 t] key_fibre_bag_meaning[of 1 t]
      bag_comparison_old_meaning[of 1 t] data_comparison_payloads[of t] by auto
  show "(10,t)\<in>positive_meaning source_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
    using source_previous_meaning[of 10 t] source_components_key_meaning[of 10 t]
      whole_system_agreement_meaning[OF artifact_projection_system_formed key_fibre_system_formed
        key_fibre_projection_agreement, of 10 t] by auto
  show "(21,t)\<in>positive_meaning source_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
    using source_previous_meaning[of 21 t] source_components_key_meaning[of 21 t]
      whole_system_agreement_meaning[OF keyed_list_system_formed key_fibre_system_formed
        key_fibre_keyed_agreement, of 21 t] by auto
  show "(28,t)\<in>positive_meaning source_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
    using source_previous_meaning[of 28 t] source_components_key_meaning[of 28 t] by auto
  show "(233,t)\<in>positive_meaning source_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
    using source_previous_meaning[of 233 t] source_components_sequence_meaning[of 233 t] by auto
  show "(236,t)\<in>positive_meaning source_system \<longleftrightarrow> (236,t)\<in>positive_meaning term_sequence_system"
    using source_previous_meaning[of 236 t] source_components_sequence_meaning[of 236 t] by auto
qed

interpretation source_literal: reader_projection_profile source_system 237 10 0 1 0 0
  by (unfold_locales) (auto simp: source_system_clause source_clause_family_def source_system_call)

interpretation source_input_list: list_profile source_system 237 238
  by (unfold_locales) (auto simp: source_system_clause source_clause_family_def source_system_call)

interpretation source_base_rows: list_profile source_system 239 240
  by (unfold_locales) (auto simp: source_system_clause source_clause_family_def source_system_call)

interpretation source_base_table: table_admission_profile source_system 241 21 240
  by (unfold_locales) (auto simp: source_system_clause source_clause_family_def source_system_call)

interpretation source_value_composition: composed_reading_profile source_system 244 243 10
  by (unfold_locales) (auto simp: source_system_clause source_clause_family_def source_system_call)

text \<open>
  Eight definitions contain eleven ordinary clauses. Two complete list
  profiles and the whole-table profile supply source admission. Both lookup
  branches call that same complete context predicate before selecting a value.
  Input lookup uses the existing bounded position operation; base lookup uses
  the existing key collector with a singleton result and admitted whole table.

  Retermination keeps the two existing source formats. The resulting artifact
  data comes from the same returned whole-artifact literal through the existing
  material projection. The base is the least closure of six actual external
  callees, whose original interfaces, clauses, and meanings are preserved.
\<close>

end
