theory Factor_Structural_Table_Clauses
  imports Factor_Table_Admission_Profiles Factor_Assembly_Presentations
begin

section \<open>Piece rows and origin rows have separate component boundaries\<close>

definition structural_piece_row_schema :: "(nat,nat,nat) factor_schema" where
  "structural_piece_row_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,1,data_list_pattern [data_x]),(1,11,data_y)}"

definition structural_origin_row_schema :: "(nat,nat,nat) factor_schema" where
  "structural_origin_row_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,1,data_list_pattern [data_x]),(1,1,data_list_pattern [data_y]),(2,1,data_list_pattern [data_z])}"

lemmas structural_table_schema_defs = structural_piece_row_schema_def structural_origin_row_schema_def
  table_admission_schema_def list_profile_clauses_def data_list_nil_schema_def list_step_schema_def

definition structural_table_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "structural_table_clause_family d=
    (if d=211 then {(0,structural_piece_row_schema)}
    else if d=212 then list_profile_clauses 211 212
    else if d=213 then {(0,table_admission_schema 21 212)}
    else if d=214 then {(0,structural_origin_row_schema)}
    else if d=215 then list_profile_clauses 214 215
    else if d=216 then {(0,table_admission_schema 21 215)}
    else {})"

section \<open>The actual callees determine the least base program\<close>

definition structural_table_group_system :: "(nat,nat,nat,nat) schema_system" where
  "structural_table_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{211,212,213,214,215,216}},
    system_clauses={((d,c),S). d\<in>{211,212,213,214,215,216} \<and> (c,S)\<in>structural_table_clause_family d}\<rparr>"

lemma structural_table_group_definitions [simp]:
  "system_definitions structural_table_group_system={211,212,213,214,215,216}"
  by (auto simp: structural_table_group_system_def system_definitions_def rel_dom_def)

lemma structural_table_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces structural_table_group_system \<longleftrightarrow>
    d\<in>system_definitions structural_table_group_system \<and> p=Pattern_Variable 0"
  by (simp only: structural_table_group_definitions; auto simp: structural_table_group_system_def)

lemma structural_table_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses structural_table_group_system \<longleftrightarrow>
    d\<in>system_definitions structural_table_group_system \<and> (c,S)\<in>structural_table_clause_family d"
  by (simp only: structural_table_group_definitions; auto simp: structural_table_group_system_def)

lemma structural_table_group_formed_over:
  "schema_system_formed_over {1,11,21} structural_table_group_system"
proof -
  have family_finite: "finite (structural_table_clause_family d)" for d
    by (simp add: structural_table_clause_family_def list_profile_clauses_def)
  have family_functional: "single_valued (structural_table_clause_family d)" for d
    by (auto simp: structural_table_clause_family_def list_profile_clauses_def single_valued_def
      split: if_splits)
  have family_formed: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{1,11,21}\<union>system_definitions structural_table_group_system"
    if "(c,S)\<in>structural_table_clause_family d" for c S d
    using that by (auto simp: structural_table_clause_family_def structural_table_schema_defs
      schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def split: if_splits)
  have interface_image: "system_interfaces structural_table_group_system=
      (\<lambda>d. (d,Pattern_Variable 0)) ` system_definitions structural_table_group_system"
    by (simp only: structural_table_group_definitions; auto simp: structural_table_group_system_def)
  have clause_union: "system_clauses structural_table_group_system=
      (\<Union>d\<in>system_definitions structural_table_group_system.
        (\<lambda>(c,S). ((d,c),S)) ` structural_table_clause_family d)"
    by (simp only: structural_table_group_definitions; auto simp: structural_table_group_system_def)
  have finite: "finite (system_interfaces structural_table_group_system)"
    "finite (system_clauses structural_table_group_system)"
    by (simp_all add: interface_image clause_union family_finite)
  have interfaces: "single_valued (system_interfaces structural_table_group_system)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses structural_table_group_system)"
    using family_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses structural_table_group_system \<longrightarrow>
      d\<in>system_definitions structural_table_group_system \<and> schema_formed S \<and>
      schema_dependencies S\<subseteq>{1,11,21}\<union>system_definitions structural_table_group_system"
  proof (intro allI impI)
    fix d c S assume clause: "((d,c),S)\<in>system_clauses structural_table_group_system"
    have members: "d\<in>system_definitions structural_table_group_system \<and> (c,S)\<in>structural_table_clause_family d"
      using clause by (simp only: structural_table_group_clauses)
    show "d\<in>system_definitions structural_table_group_system \<and> schema_formed S \<and>
        schema_dependencies S\<subseteq>{1,11,21}\<union>system_definitions structural_table_group_system"
      using members family_formed[OF conjunct2[OF members]] by blast
  qed
  show ?thesis using finite interfaces clauses schemas
    by (simp add: schema_system_formed_over_def)
qed

lemma structural_table_external_dependencies:
  "system_external_dependencies structural_table_group_system={1,11,21}"
proof -
  have bounded: "system_external_dependencies structural_table_group_system\<subseteq>{1,11,21}"
    by (rule system_external_dependencies_boundary[OF structural_table_group_formed_over])
  have reached: "e\<in>system_external_dependencies structural_table_group_system"
    if "((d,c),S)\<in>system_clauses structural_table_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions structural_table_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses structural_table_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3) by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have payload: "1\<in>system_external_dependencies structural_table_group_system"
    by (rule reached[where d=211 and c=0 and S=structural_piece_row_schema])
      (auto simp: structural_table_clause_family_def structural_piece_row_schema_def schema_dependencies_def rel_ran_image)
  have artifact: "11\<in>system_external_dependencies structural_table_group_system"
    by (rule reached[where d=211 and c=0 and S=structural_piece_row_schema])
      (auto simp: structural_table_clause_family_def structural_piece_row_schema_def schema_dependencies_def rel_ran_image)
  have keys: "21\<in>system_external_dependencies structural_table_group_system"
    by (rule reached[where d=213 and c=0 and S="table_admission_schema 21 212"])
      (auto simp: structural_table_clause_family_def table_admission_schema_def schema_dependencies_def rel_ran_image)
  show ?thesis using bounded payload artifact keys by blast
qed

definition structural_table_base_system :: "(nat,nat,nat,nat) schema_system" where
  "structural_table_base_system=rooted_system keyed_list_system
    (system_external_dependencies structural_table_group_system)"

lemma structural_table_base_formed [simp]: "schema_system_formed structural_table_base_system"
  by (simp only: structural_table_base_system_def; rule rooted_system_formed[OF keyed_list_system_formed])

lemma structural_table_base_subdomain:
  "system_definitions structural_table_base_system\<subseteq>system_definitions keyed_list_system"
  by (simp only: structural_table_base_system_def; rule rooted_system_subdomain)

lemma structural_table_base_roots:
  "{1,11,21}\<subseteq>system_definitions structural_table_base_system"
  unfolding structural_table_base_system_def structural_table_external_dependencies
  by (rule rooted_system_roots[OF keyed_list_system_formed]) auto

lemma structural_table_base_call:
  "schema_call_formed structural_table_base_system d t \<longleftrightarrow>
    d\<in>system_definitions structural_table_base_system \<and> term_formed t"
proof -
  have roots: "system_external_dependencies structural_table_group_system\<subseteq>
      system_definitions keyed_list_system"
    by (simp only: structural_table_external_dependencies; auto)
  have definitions: "system_definitions structural_table_base_system=
      system_definition_closure keyed_list_system
        (system_external_dependencies structural_table_group_system)"
    unfolding structural_table_base_system_def
    by (rule rooted_system_definitions[OF keyed_list_system_formed roots])
  have inside: "d\<in>system_definition_closure keyed_list_system
      (system_external_dependencies structural_table_group_system) \<Longrightarrow>
      d\<in>system_definitions keyed_list_system"
    using structural_table_base_subdomain by (simp only: definitions; blast)
  have calls: "schema_call_formed structural_table_base_system d t \<longleftrightarrow>
      d\<in>system_definition_closure keyed_list_system
        (system_external_dependencies structural_table_group_system) \<and>
      schema_call_formed keyed_list_system d t"
    by (simp only: structural_table_base_system_def rooted_system_calls[OF keyed_list_system_formed])
  show ?thesis by (simp only: calls definitions keyed_list_call; use inside in blast)
qed

lemma structural_table_base_least:
  assumes "{1,11,21}\<subseteq>U" "system_dependency_closed keyed_list_system U"
  shows "system_definitions structural_table_base_system\<subseteq>U"
  unfolding structural_table_base_system_def structural_table_external_dependencies
  by (rule rooted_system_least[OF keyed_list_system_formed _ assms]) auto

interpretation structural_table_group: positive_definition_group structural_table_base_system structural_table_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed structural_table_base_system" by simp
  show "schema_system_formed_over (system_definitions structural_table_base_system) structural_table_group_system"
    by (rule schema_system_formed_over_mono[OF structural_table_group_formed_over structural_table_base_roots])
  show "system_definitions structural_table_base_system\<inter>system_definitions structural_table_group_system={}"
    using structural_table_base_subdomain by auto
qed

definition structural_table_system :: "(nat,nat,nat,nat) schema_system" where
  "structural_table_system=system_union structural_table_base_system structural_table_group_system"

lemma structural_table_system_formed [simp]: "schema_system_formed structural_table_system"
  using structural_table_group.formed by (simp only: structural_table_system_def)

lemma structural_table_definitions [simp]:
  "system_definitions structural_table_system=system_definitions structural_table_base_system\<union>system_definitions structural_table_group_system"
  by (simp add: structural_table_system_def)

lemma structural_table_call:
  "schema_call_formed structural_table_system d t \<longleftrightarrow>
    d\<in>system_definitions structural_table_system \<and> term_formed t"
  unfolding structural_table_system_def
  by (rule structural_table_group.variable_calls[OF structural_table_base_call structural_table_group_interfaces])

lemma structural_table_clause:
  assumes "d\<in>system_definitions structural_table_group_system"
  shows "((d,c),S)\<in>system_clauses structural_table_system \<longleftrightarrow> (c,S)\<in>structural_table_clause_family d"
  using structural_table_group.no_old_clause[OF assms, of c S] assms by (simp add: structural_table_system_def)

lemma structural_table_previous_meaning:
  assumes "d\<in>{1,11,21}"
  shows "(d,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning keyed_list_system"
proof -
  have member: "d\<in>system_definitions structural_table_base_system" using structural_table_base_roots assms by blast
  have inside: "d\<in>system_definition_closure keyed_list_system
      (system_external_dependencies structural_table_group_system)"
    using member by (auto simp: structural_table_base_system_def rooted_system_def)
  show ?thesis using structural_table_group.old_meaning[OF member, of t]
    rooted_system_meaning[OF keyed_list_system_formed,
      where roots="system_external_dependencies structural_table_group_system" and d=d and t=t] inside
    by (simp only: structural_table_system_def structural_table_base_system_def; blast)
qed

lemma structural_table_components:
  "(1,data_list_term [t])\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>a. payload_value_presents a t)"
  "(11,t)\<in>positive_meaning structural_table_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
  "(21,t)\<in>positive_meaning structural_table_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
proof -
  have old: "(d,u)\<in>positive_meaning structural_table_system \<longleftrightarrow>
      (d,u)\<in>positive_meaning coordinate_admission_system" if "d\<in>{1,11}" for d u
    using structural_table_previous_meaning[of d u] keyed_list_old_meaning[of d u] that by auto
  have artifacts: "(d,u)\<in>positive_meaning structural_table_system \<longleftrightarrow>
      (d,u)\<in>positive_meaning artifact_identity_system" if "d\<in>{1,11}" for d u
    using old[OF that, of u] coordinate_admission_old_meaning[of d u]
      environment_comparison_artifact_meaning[of d u] that by auto
  show "(1,data_list_term [t])\<in>positive_meaning structural_table_system \<longleftrightarrow>
      (\<exists>a. payload_value_presents a t)"
    using artifacts[of 1 "data_list_term [t]"] artifact_identity_old_meaning[of 1 "data_list_term [t]"]
      artifact_comparison_old_meaning[of 1 "data_list_term [t]"]
      bag_comparison_old_meaning[of 1 "data_list_term [t]"] data_comparison_payloads[of "data_list_term [t]"] payload_value_recognition[of t] by auto
  show "(11,t)\<in>positive_meaning structural_table_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
    using artifacts[of 11 t] artifact_identity_admission[of t] by auto
  show "(21,t)\<in>positive_meaning structural_table_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
    using structural_table_previous_meaning[of 21 t] by auto
qed

text \<open>
  Six definitions and eight ordinary clauses implement two complete table
  admissions. Each row checks its actual components, each recursive list visits
  every row, and each table checks key uniqueness. The least closed base is
  determined by the three actual external entries: payload formation, artifact
  admission, and keyed-list admission. Its complete interfaces and clauses
  agree with the original program, and its meanings are preserved.
\<close>

end
