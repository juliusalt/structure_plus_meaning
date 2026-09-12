theory Factor_Keyed_Table_Clauses
  imports Factor_Key_Fibres Factor_Related_Sets Factor_Recursive_Groups
begin

section \<open>Complete singleton lookups compare values without restricting them to data\<close>

definition keyed_table_row_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "keyed_table_row_schema fibre=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_z))
    {(0,fibre,Pattern_Pair data_y (Pattern_Pair data_x (data_list_pattern [data_z])))}"

definition keyed_table_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "keyed_table_clause_family d=(if d=351 then {(0,keyed_table_row_schema 28)}
    else if d=352 then context_list_clauses 351 352
    else if d=353 then {(0,related_set_schema 352 352)} else {})"

definition keyed_table_group_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_table_group_system=\<lparr>
    system_interfaces={(351,data_x),(352,data_x),(353,data_x)},
    system_clauses={((351,0),keyed_table_row_schema 28),
      ((352,0),context_list_nil_schema),((352,1),context_list_step_schema 351 352),
      ((353,0),related_set_schema 352 352)}\<rparr>"

lemma keyed_table_group_definitions [simp]:
  "system_definitions keyed_table_group_system={351,352,353}"
  by (auto simp: keyed_table_group_system_def system_definitions_def rel_dom_def)

lemma keyed_table_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces keyed_table_group_system \<longleftrightarrow>
    d\<in>{351,352,353} \<and> p=data_x"
  by (auto simp: keyed_table_group_system_def)

lemma keyed_table_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses keyed_table_group_system \<longleftrightarrow>
    d\<in>{351,352,353} \<and> (c,S)\<in>keyed_table_clause_family d"
  by (auto simp: keyed_table_group_system_def keyed_table_clause_family_def context_list_clauses_def)

lemmas keyed_table_schema_defs=keyed_table_row_schema_def context_list_nil_schema_def
  context_list_step_schema_def related_set_schema_def

lemma keyed_table_group_formed_over:
  "schema_system_formed_over {28} keyed_table_group_system"
  by (simp only: schema_system_formed_over_def keyed_table_group_definitions)
    (auto simp: keyed_table_group_system_def keyed_table_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma keyed_table_external_dependencies:
  "system_external_dependencies keyed_table_group_system={28}"
  by (simp only: system_external_dependencies_clauses keyed_table_group_definitions)
    (auto simp: keyed_table_group_system_def keyed_table_schema_defs schema_dependencies_def rel_ran_image)

definition keyed_table_base_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_table_base_system=rooted_system key_fibre_system
    (system_external_dependencies keyed_table_group_system)"

lemma keyed_table_base_formed [simp]: "schema_system_formed keyed_table_base_system"
  unfolding keyed_table_base_system_def by (rule rooted_system_formed[OF key_fibre_system_formed])

lemma keyed_table_base_subdomain:
  "system_definitions keyed_table_base_system\<subseteq>system_definitions key_fibre_system"
  unfolding keyed_table_base_system_def by (rule rooted_system_subdomain)

lemma keyed_table_base_roots: "{28}\<subseteq>system_definitions keyed_table_base_system"
  unfolding keyed_table_base_system_def keyed_table_external_dependencies
  by (rule rooted_system_roots[OF key_fibre_system_formed]) auto

lemma keyed_table_base_least:
  assumes "{28}\<subseteq>U" "system_dependency_closed key_fibre_system U"
  shows "system_definitions keyed_table_base_system\<subseteq>U"
  unfolding keyed_table_base_system_def keyed_table_external_dependencies
  by (rule rooted_system_least[OF key_fibre_system_formed _ assms]) auto

lemma keyed_table_base_call:
  "schema_call_formed keyed_table_base_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_table_base_system \<and> term_formed t"
  unfolding keyed_table_base_system_def
  by (rule rooted_system_variable_calls[OF key_fibre_system_formed key_fibre_call])

interpretation keyed_table_group:
  positive_definition_group keyed_table_base_system keyed_table_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed keyed_table_base_system" by simp
  show "schema_system_formed_over (system_definitions keyed_table_base_system) keyed_table_group_system"
    by (rule schema_system_formed_over_mono[OF keyed_table_group_formed_over keyed_table_base_roots])
  show "system_definitions keyed_table_base_system\<inter>system_definitions keyed_table_group_system={}"
    using keyed_table_base_subdomain by auto
qed

definition keyed_table_comparison_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_table_comparison_system=system_union keyed_table_base_system keyed_table_group_system"

lemma keyed_table_comparison_formed [simp]: "schema_system_formed keyed_table_comparison_system"
  using keyed_table_group.formed by (simp only: keyed_table_comparison_system_def)

lemma keyed_table_comparison_definitions [simp]:
  "system_definitions keyed_table_comparison_system=system_definitions keyed_table_base_system\<union>{351,352,353}"
  by (simp add: keyed_table_comparison_system_def)

lemma keyed_table_comparison_call:
  "schema_call_formed keyed_table_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_table_comparison_system \<and> term_formed t"
  unfolding keyed_table_comparison_system_def
  by (rule keyed_table_group.variable_calls[OF keyed_table_base_call keyed_table_group_interfaces])

lemma keyed_table_comparison_clause:
  assumes "d\<in>{351,352,353}"
  shows "((d,c),S)\<in>system_clauses keyed_table_comparison_system \<longleftrightarrow>
    (c,S)\<in>keyed_table_clause_family d"
  using keyed_table_group.no_old_clause[of d c S] assms
  by (auto simp: keyed_table_comparison_system_def)

lemma keyed_table_source_meaning:
  assumes member: "d\<in>system_definitions keyed_table_base_system"
  shows "(d,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning key_fibre_system"
proof -
  have closure: "d\<in>system_definition_closure key_fibre_system
      (system_external_dependencies keyed_table_group_system)"
    using member by (auto simp: keyed_table_base_system_def rooted_system_def)
  show ?thesis using keyed_table_group.old_meaning[OF member, of t]
    rooted_system_meaning[OF key_fibre_system_formed,
      where roots="system_external_dependencies keyed_table_group_system" and d=d and t=t] closure
    by (simp only: keyed_table_comparison_system_def keyed_table_base_system_def; blast)
qed

lemma keyed_table_fibre_meaning:
  "(28,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    (28,t)\<in>positive_meaning key_fibre_system"
  by (rule keyed_table_source_meaning) (use keyed_table_base_roots in blast)

interpretation keyed_table_rows: context_list_profile keyed_table_comparison_system 351 352
  by (rule context_list_profile.intro)
    (auto simp: keyed_table_comparison_clause keyed_table_clause_family_def keyed_table_comparison_call)

text \<open>
  The row clause invokes the existing complete key-fibre reader. Both complete
  traversals use that same row relation. Their opposite orientations retain
  every key and every value, including literal targets in values. The only
  external native dependency is derived from the actual clauses, and its least
  closed source program is retained. Repeated keys remain occurrences for the
  fibre reader; no table is silently normalized before checking.
\<close>

end
