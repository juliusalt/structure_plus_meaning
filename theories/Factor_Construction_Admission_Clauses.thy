theory Factor_Construction_Admission_Clauses
  imports Factor_Construction_Components Factor_Selection_Presentations
begin

section \<open>Actual source selection returns every fragment presentation\<close>

definition selected_fragment_schema :: "(nat,nat,nat) factor_schema" where
  "selected_fragment_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
      (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,244,Pattern_Pair (Pattern_Pair data_x data_y) data_w),
     (1,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 5) data_z),
     (2,6,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 4)),
     (3,205,Pattern_Pair data_w (Pattern_Variable 4))}"

definition selected_piece_row_schema :: "(nat,nat,nat) factor_schema" where
  "selected_piece_row_schema=data_rule
    (context_relation_pattern data_x (Pattern_Pair data_y data_z) (Pattern_Pair data_y data_w))
    {(0,1,data_list_pattern [data_y]),
     (1,246,Pattern_Pair (Pattern_Pair data_x data_z) data_w)}"

definition selected_piece_table_schema :: "(nat,nat,nat) factor_schema" where
  "selected_piece_table_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_w)
    {(0,242,data_x),
     (1,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) data_z data_y),
     (2,21,data_z),
     (3,248,context_relation_pattern data_x data_z data_w)}"

section \<open>The complete original claim is the assembly of those selected pieces\<close>

definition construction_admission_schema :: "(nat,nat,nat) factor_schema" where
  "construction_admission_schema=data_rule
    (foldr Pattern_Pair [Pattern_Variable 0,Pattern_Variable 1,Pattern_Variable 2,
      Pattern_Variable 3,Pattern_Variable 4] (Pattern_Target (Whole_Artifact empty_artifact)))
    {(0,249,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) (Pattern_Variable 5)),
     (1,233,collection_join_pattern (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 6) data_w),
     (2,10,Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 7)),
     (3,230,Pattern_Pair (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7))}"

definition construction_admission_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "construction_admission_clause_family d=(if d=245 then {(0,selected_fragment_schema)}
    else if d=246 then {(0,composed_reading_schema 245 206)}
    else if d=247 then {(0,selected_piece_row_schema)}
    else if d=248 then related_list_clauses 247 248
    else if d=249 then {(0,selected_piece_table_schema)}
    else if d=250 then {(0,construction_admission_schema)} else {})"

lemmas construction_admission_schema_defs = selected_fragment_schema_def selected_piece_row_schema_def
  selected_piece_table_schema_def construction_admission_schema_def composed_reading_schema_def
  related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def

definition construction_admission_group_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_admission_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{245,246,247,248,249,250}},
    system_clauses={((d,c),S). d\<in>{245,246,247,248,249,250} \<and>
      (c,S)\<in>construction_admission_clause_family d}\<rparr>"

lemma construction_admission_group_definitions [simp]:
  "system_definitions construction_admission_group_system={245,246,247,248,249,250}"
  by (auto simp: construction_admission_group_system_def system_definitions_def rel_dom_def)

lemma construction_admission_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces construction_admission_group_system \<longleftrightarrow>
    d\<in>system_definitions construction_admission_group_system \<and> p=Pattern_Variable 0"
  by (simp only: construction_admission_group_definitions; auto simp: construction_admission_group_system_def)

lemma construction_admission_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses construction_admission_group_system \<longleftrightarrow>
    d\<in>system_definitions construction_admission_group_system \<and>
    (c,S)\<in>construction_admission_clause_family d"
  by (simp only: construction_admission_group_definitions; auto simp: construction_admission_group_system_def)

lemma construction_admission_group_formed_over:
  "schema_system_formed_over {1,6,10,21,205,206,230,233,242,244} construction_admission_group_system"
proof -
  have finite: "finite (construction_admission_clause_family d)" for d
    by (simp add: construction_admission_clause_family_def related_list_clauses_def)
  have functional: "single_valued (construction_admission_clause_family d)" for d
    by (auto simp: construction_admission_clause_family_def related_list_clauses_def single_valued_def split: if_splits)
  have schemas: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{1,6,10,21,205,206,230,233,242,244}\<union>
        system_definitions construction_admission_group_system"
    if "(c,S)\<in>construction_admission_clause_family d" for c S d
    using that by (auto simp: construction_admission_clause_family_def construction_admission_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def split: if_splits)
  show ?thesis
    by (rule schema_system_formed_over_families[where D="system_definitions construction_admission_group_system"
        and p="\<lambda>_. Pattern_Variable 0" and C=construction_admission_clause_family])
      (use finite functional schemas in
        \<open>simp_all only: construction_admission_group_definitions; auto simp: construction_admission_group_system_def\<close>)+
qed

lemma construction_admission_external_dependencies:
  "system_external_dependencies construction_admission_group_system={1,6,10,21,205,206,230,233,242,244}"
proof -
  have bounded: "system_external_dependencies construction_admission_group_system\<subseteq>
      {1,6,10,21,205,206,230,233,242,244}"
    by (rule system_external_dependencies_boundary[OF construction_admission_group_formed_over])
  have reached: "e\<in>system_external_dependencies construction_admission_group_system"
    if "((d,c),S)\<in>system_clauses construction_admission_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions construction_admission_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses construction_admission_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3) by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have selected: "e\<in>system_external_dependencies construction_admission_group_system"
    if "e\<in>{6,205,233,244}" for e
    by (rule reached[where d=245 and c=0 and S=selected_fragment_schema])
      (use that in \<open>auto simp: construction_admission_clause_family_def selected_fragment_schema_def schema_dependencies_def rel_ran_image\<close>)
  have material: "206\<in>system_external_dependencies construction_admission_group_system"
    by (rule reached[where d=246 and c=0 and S="composed_reading_schema 245 206"])
      (auto simp: construction_admission_clause_family_def)
  have slot: "1\<in>system_external_dependencies construction_admission_group_system"
    by (rule reached[where d=247 and c=0 and S=selected_piece_row_schema])
      (auto simp: construction_admission_clause_family_def selected_piece_row_schema_def schema_dependencies_def rel_ran_image)
  have table: "e\<in>system_external_dependencies construction_admission_group_system"
    if "e\<in>{21,242}" for e
    by (rule reached[where d=249 and c=0 and S=selected_piece_table_schema])
      (use that in \<open>auto simp: construction_admission_clause_family_def selected_piece_table_schema_def schema_dependencies_def rel_ran_image\<close>)
  have assembly: "e\<in>system_external_dependencies construction_admission_group_system"
    if "e\<in>{10,230}" for e
    by (rule reached[where d=250 and c=0 and S=construction_admission_schema])
      (use that in \<open>auto simp: construction_admission_clause_family_def construction_admission_schema_def schema_dependencies_def rel_ran_image\<close>)
  show ?thesis using bounded selected material slot table assembly by auto
qed

definition construction_admission_base_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_admission_base_system=rooted_system construction_components_system
    (system_external_dependencies construction_admission_group_system)"

lemma construction_admission_base_formed [simp]: "schema_system_formed construction_admission_base_system"
  unfolding construction_admission_base_system_def by (rule rooted_system_formed[OF construction_components_formed])

lemma construction_admission_base_subdomain:
  "system_definitions construction_admission_base_system\<subseteq>system_definitions construction_components_system"
  unfolding construction_admission_base_system_def by (rule rooted_system_subdomain)

lemma construction_admission_base_roots:
  "{1,6,10,21,205,206,230,233,242,244}\<subseteq>system_definitions construction_admission_base_system"
  unfolding construction_admission_base_system_def construction_admission_external_dependencies
  by (rule rooted_system_roots[OF construction_components_formed]) auto

lemma construction_admission_base_least:
  assumes "{1,6,10,21,205,206,230,233,242,244}\<subseteq>U"
    "system_dependency_closed construction_components_system U"
  shows "system_definitions construction_admission_base_system\<subseteq>U"
  unfolding construction_admission_base_system_def construction_admission_external_dependencies
  by (rule rooted_system_least[OF construction_components_formed _ assms]) auto

lemma construction_admission_base_call:
  "schema_call_formed construction_admission_base_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_admission_base_system \<and> term_formed t"
  unfolding construction_admission_base_system_def
  by (rule rooted_system_variable_calls[OF construction_components_formed construction_components_call])

interpretation construction_admission_group:
  positive_definition_group construction_admission_base_system construction_admission_group_system
  by (unfold_locales)
    (use schema_system_formed_over_mono[OF construction_admission_group_formed_over construction_admission_base_roots]
      construction_admission_base_subdomain in auto)

definition construction_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_admission_system=system_union construction_admission_base_system construction_admission_group_system"

lemma construction_admission_system_formed [simp]: "schema_system_formed construction_admission_system"
  using construction_admission_group.formed by (simp only: construction_admission_system_def)

lemma construction_admission_system_definitions [simp]:
  "system_definitions construction_admission_system=
    system_definitions construction_admission_base_system\<union>system_definitions construction_admission_group_system"
  by (simp add: construction_admission_system_def)

lemma construction_admission_call:
  "schema_call_formed construction_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions construction_admission_system \<and> term_formed t"
  unfolding construction_admission_system_def
  by (rule construction_admission_group.variable_calls[OF construction_admission_base_call construction_admission_group_interfaces])

lemma construction_admission_clause:
  assumes "d\<in>system_definitions construction_admission_group_system"
  shows "((d,c),S)\<in>system_clauses construction_admission_system \<longleftrightarrow>
    (c,S)\<in>construction_admission_clause_family d"
  using construction_admission_group.group_clauses[OF assms] assms by (simp add: construction_admission_system_def)

lemma construction_admission_previous_meaning:
  assumes "d\<in>{1,6,10,21,205,206,230,233,242,244}"
  shows "(d,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning construction_components_system"
proof -
  have member: "d\<in>system_definitions construction_admission_base_system"
    using construction_admission_base_roots assms by blast
  show ?thesis using construction_admission_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF construction_components_formed member[unfolded construction_admission_base_system_def], of t]
    by (simp only: construction_admission_system_def construction_admission_base_system_def; blast)
qed

lemma construction_admission_components:
  "(1,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (1,t)\<in>positive_meaning distinct_payloads_system"
  "(6,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(10,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(21,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(205,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (205,t)\<in>positive_meaning fragment_system"
  "(206,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (206,t)\<in>positive_meaning fragment_system"
  "(230,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (230,t)\<in>positive_meaning assembly_checking_system"
  "(233,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (233,t)\<in>positive_meaning term_sequence_system"
  "(242,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (242,t)\<in>positive_meaning source_system"
  "(244,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> (244,t)\<in>positive_meaning source_system"
  using construction_admission_previous_meaning[of 1 t] construction_admission_previous_meaning[of 6 t]
    construction_admission_previous_meaning[of 10 t] construction_admission_previous_meaning[of 21 t]
    construction_admission_previous_meaning[of 205 t] construction_admission_previous_meaning[of 206 t]
    construction_admission_previous_meaning[of 230 t] construction_admission_previous_meaning[of 233 t]
    construction_admission_previous_meaning[of 242 t] construction_admission_previous_meaning[of 244 t]
    construction_component_meanings[of t] by auto

interpretation selected_material_composition: composed_reading_profile construction_admission_system 246 245 206
  by (unfold_locales)
    (auto simp: construction_admission_clause construction_admission_clause_family_def construction_admission_call)

interpretation selected_piece_rows: related_list_profile construction_admission_system 247 248
  by (unfold_locales)
    (auto simp: construction_admission_clause construction_admission_clause_family_def construction_admission_call)

text \<open>
  Six definitions contain seven ordinary clauses. Fragment selection calls
  actual source lookup, complete set comparison, and fragment admission.
  Material is the existing fragment projection. The row traversal preserves
  its slot and the whole table checks key uniqueness independently.

  Table mapping admits the complete source context even for an empty table.
  The final clause retains the original five-field claim and submits its
  derived pieces, actual origins, and claimed output to complete assembly
  admission. Its base is the least closure of ten actual external callees.
  No permission oracle or additional material observation is introduced.
\<close>

end
