theory Factor_Keyed_Set_Clauses
  imports Factor_Observation_Components Factor_Related_Sets Factor_Keyed_Comparison
begin

section \<open>Complete finite sets compare keyed finite data sets\<close>

definition keyed_set_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "keyed_set_clause_family d=(if d=312 then {(0,keyed_comparison_schema 2 219)}
    else if d=313 then {(0,compared_member_schema 303 312)}
    else if d=314 then context_list_clauses 313 314
    else if d=315 then {(0,reverse_compared_member_schema 303 312)}
    else if d=316 then context_list_clauses 315 316
    else if d=317 then {(0,related_set_schema 314 316)} else {})"

definition keyed_set_group_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_set_group_system=\<lparr>system_interfaces={(312,data_x),(313,data_x),(314,data_x),
      (315,data_x),(316,data_x),(317,data_x)},
    system_clauses={((312,0),keyed_comparison_schema 2 219),
      ((313,0),compared_member_schema 303 312),
      ((314,0),context_list_nil_schema),((314,1),context_list_step_schema 313 314),
      ((315,0),reverse_compared_member_schema 303 312),
      ((316,0),context_list_nil_schema),((316,1),context_list_step_schema 315 316),
      ((317,0),related_set_schema 314 316)}\<rparr>"

lemma keyed_set_group_definitions [simp]:
  "system_definitions keyed_set_group_system={312,313,314,315,316,317}"
  by (auto simp: keyed_set_group_system_def system_definitions_def rel_dom_def)

lemma keyed_set_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces keyed_set_group_system \<longleftrightarrow> d\<in>{312,313,314,315,316,317} \<and> p=data_x"
  by (auto simp: keyed_set_group_system_def)

lemma keyed_set_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses keyed_set_group_system \<longleftrightarrow>
    d\<in>{312,313,314,315,316,317} \<and> (c,S)\<in>keyed_set_clause_family d"
  by (auto simp: keyed_set_group_system_def keyed_set_clause_family_def context_list_clauses_def)

lemma keyed_set_group_formed_over:
  "schema_system_formed_over {2,219,303} keyed_set_group_system"
  by (simp only: schema_system_formed_over_def keyed_set_group_definitions)
    (auto simp: keyed_set_group_system_def keyed_comparison_schema_def compared_member_schema_def reverse_compared_member_schema_def related_set_schema_def
      context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma keyed_set_external_dependencies:
  "system_external_dependencies keyed_set_group_system={2,219,303}"
  by (simp only: system_external_dependencies_clauses keyed_set_group_definitions)
    (auto simp: keyed_set_group_system_def keyed_comparison_schema_def compared_member_schema_def reverse_compared_member_schema_def related_set_schema_def
      context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_dependencies_def rel_ran_image)

definition keyed_set_base_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_set_base_system=rooted_system observation_collection_system
    (system_external_dependencies keyed_set_group_system)"

lemma keyed_set_base_formed [simp]: "schema_system_formed keyed_set_base_system"
  unfolding keyed_set_base_system_def by (rule rooted_system_formed[OF observation_collection_formed])

lemma keyed_set_base_subdomain:
  "system_definitions keyed_set_base_system\<subseteq>system_definitions observation_collection_system"
  unfolding keyed_set_base_system_def by (rule rooted_system_subdomain)

lemma keyed_set_base_roots:
  "{2,219,303}\<subseteq>system_definitions keyed_set_base_system"
  unfolding keyed_set_base_system_def keyed_set_external_dependencies
  by (rule rooted_system_roots[OF observation_collection_formed])
    (use observation_base_roots in auto)

lemma keyed_set_base_least:
  assumes "{2,219,303}\<subseteq>U" "system_dependency_closed observation_collection_system U"
  shows "system_definitions keyed_set_base_system\<subseteq>U"
  unfolding keyed_set_base_system_def keyed_set_external_dependencies
  by (rule rooted_system_least[OF observation_collection_formed _ assms])
    (use observation_base_roots in auto)

lemma keyed_set_base_call:
  "schema_call_formed keyed_set_base_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_set_base_system \<and> term_formed t"
  unfolding keyed_set_base_system_def
  by (rule rooted_system_variable_calls[OF observation_collection_formed observation_collection_call])

interpretation keyed_set_group:
  positive_definition_group keyed_set_base_system keyed_set_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed keyed_set_base_system" by simp
  show "schema_system_formed_over (system_definitions keyed_set_base_system) keyed_set_group_system"
    by (rule schema_system_formed_over_mono[OF keyed_set_group_formed_over keyed_set_base_roots])
  have boundary: "system_definitions observation_collection_system\<inter>{312,313,314,315,316,317}={}"
    using observation_base_subdomain data_set_comparison_base_subdomain by auto
  show "system_definitions keyed_set_base_system\<inter>system_definitions keyed_set_group_system={}"
    using boundary keyed_set_base_subdomain by auto
qed

definition keyed_set_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_set_system=system_union keyed_set_base_system keyed_set_group_system"

lemma keyed_set_system_formed [simp]: "schema_system_formed keyed_set_system"
  using keyed_set_group.formed by (simp only: keyed_set_system_def)

lemma keyed_set_definitions [simp]:
  "system_definitions keyed_set_system=system_definitions keyed_set_base_system\<union>{312,313,314,315,316,317}"
  by (simp add: keyed_set_system_def)

lemma keyed_set_call:
  "schema_call_formed keyed_set_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_set_system \<and> term_formed t"
  unfolding keyed_set_system_def
  by (rule keyed_set_group.variable_calls[where D="{312,313,314,315,316,317}" and a=0,
    OF keyed_set_base_call]) auto

lemma keyed_set_clause:
  assumes "d\<in>{312,313,314,315,316,317}"
  shows "((d,c),S)\<in>system_clauses keyed_set_system \<longleftrightarrow>
    (c,S)\<in>keyed_set_clause_family d"
  using keyed_set_group.group_clauses[of d c S] assms
  by (simp only: keyed_set_system_def keyed_set_group_clauses
    keyed_set_group_definitions; blast)

lemma keyed_set_base_meaning:
  assumes "d\<in>{2,219,303}"
  shows "(d,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning observation_collection_system"
proof -
  have member: "d\<in>system_definitions keyed_set_base_system"
    using keyed_set_base_roots assms by blast
  show ?thesis using keyed_set_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF observation_collection_formed member[unfolded keyed_set_base_system_def], of t]
    by (simp only: keyed_set_system_def keyed_set_base_system_def)
qed

end
