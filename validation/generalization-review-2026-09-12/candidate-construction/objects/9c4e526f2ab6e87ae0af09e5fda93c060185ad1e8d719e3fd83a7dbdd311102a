theory Factor_Observation_Table_Clauses
  imports Factor_Observation_Table_Components Factor_Binary_Result_Comparison Factor_Keyed_Calculation
begin

section \<open>The declared candidates determine every profile and loss row\<close>

definition observation_profile_table_schema :: "(nat,nat,nat) factor_schema" where
  "observation_profile_table_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) data_w) (Pattern_Variable 4))
    {(0,327,context_relation_pattern (Pattern_Pair data_z data_w) data_x (Pattern_Variable 4))}"

definition observation_loss_table_schema :: "(nat,nat,nat) factor_schema" where
  "observation_loss_table_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) data_w) (Pattern_Variable 4))
    {(0,324,context_relation_pattern data_x data_x (Pattern_Variable 5)),
     (1,332,context_relation_pattern (Pattern_Pair data_z data_w) (Pattern_Variable 5) (Pattern_Variable 4))}"

definition observation_table_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "observation_table_clause_family d=(if d=326 then {(0,keyed_calculation_schema 301)}
    else if d=327 then related_list_clauses 326 327
    else if d=328 then {(0,observation_profile_table_schema)}
    else if d=329 then {(0,admitted_context_schema 311 328)}
    else if d=330 then {(0,result_comparison_schema 329 317)}
    else if d=331 then {(0,keyed_calculation_schema 306)}
    else if d=332 then related_list_clauses 331 332
    else if d=333 then {(0,observation_loss_table_schema)}
    else if d=334 then {(0,admitted_context_schema 311 333)}
    else if d=335 then {(0,result_comparison_schema 334 317)} else {})"

definition observation_table_group_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_group_system=\<lparr>system_interfaces={(326,data_x),(327,data_x),(328,data_x),(329,data_x),(330,data_x),
      (331,data_x),(332,data_x),(333,data_x),(334,data_x),(335,data_x)},
    system_clauses={((326,0),keyed_calculation_schema 301),
      ((327,0),related_list_nil_schema),((327,1),related_list_step_schema 326 327),
      ((328,0),observation_profile_table_schema),((329,0),admitted_context_schema 311 328),
      ((330,0),result_comparison_schema 329 317),((331,0),keyed_calculation_schema 306),
      ((332,0),related_list_nil_schema),((332,1),related_list_step_schema 331 332),
      ((333,0),observation_loss_table_schema),((334,0),admitted_context_schema 311 333),
      ((335,0),result_comparison_schema 334 317)}\<rparr>"

lemma observation_table_group_definitions [simp]:
  "system_definitions observation_table_group_system={326,327,328,329,330,331,332,333,334,335}"
  by (auto simp: observation_table_group_system_def system_definitions_def rel_dom_def)

lemma observation_table_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces observation_table_group_system \<longleftrightarrow>
    d\<in>{326,327,328,329,330,331,332,333,334,335} \<and> p=data_x"
  by (auto simp: observation_table_group_system_def)

lemma observation_table_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses observation_table_group_system \<longleftrightarrow>
    d\<in>{326,327,328,329,330,331,332,333,334,335} \<and> (c,S)\<in>observation_table_clause_family d"
  by (auto simp: observation_table_group_system_def observation_table_clause_family_def related_list_clauses_def)

lemmas observation_table_schema_defs = observation_profile_table_schema_def observation_loss_table_schema_def
  keyed_calculation_schema_def admitted_context_schema_def result_comparison_schema_def
  related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def

lemma observation_table_group_formed_over:
  "schema_system_formed_over {301,306,311,317,324} observation_table_group_system"
  by (simp only: schema_system_formed_over_def observation_table_group_definitions)
    (auto simp: observation_table_group_system_def observation_table_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma observation_table_external_dependencies:
  "system_external_dependencies observation_table_group_system={301,306,311,317,324}"
  by (simp only: system_external_dependencies_clauses observation_table_group_definitions)
    (auto simp: observation_table_group_system_def observation_table_schema_defs schema_dependencies_def rel_ran_image)

definition observation_table_base_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_base_system=rooted_system observation_table_components_system
    (system_external_dependencies observation_table_group_system)"

lemma observation_table_base_formed [simp]: "schema_system_formed observation_table_base_system"
  unfolding observation_table_base_system_def by (rule rooted_system_formed[OF observation_table_components_formed])

lemma observation_table_base_subdomain:
  "system_definitions observation_table_base_system\<subseteq>system_definitions observation_table_components_system"
  unfolding observation_table_base_system_def by (rule rooted_system_subdomain)

lemma observation_table_base_roots:
  "{301,306,311,317,324}\<subseteq>system_definitions observation_table_base_system"
  unfolding observation_table_base_system_def observation_table_external_dependencies
  by (rule rooted_system_roots[OF observation_table_components_formed]) auto

lemma observation_table_base_least:
  assumes "{301,306,311,317,324}\<subseteq>U" "system_dependency_closed observation_table_components_system U"
  shows "system_definitions observation_table_base_system\<subseteq>U"
  unfolding observation_table_base_system_def observation_table_external_dependencies
  by (rule rooted_system_least[OF observation_table_components_formed _ assms]) auto

lemma observation_table_base_call:
  "schema_call_formed observation_table_base_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_base_system \<and> term_formed t"
  unfolding observation_table_base_system_def
  by (rule rooted_system_variable_calls[OF observation_table_components_formed observation_table_components_call])

interpretation observation_table_group:
  positive_definition_group observation_table_base_system observation_table_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed observation_table_base_system" by simp
  show "schema_system_formed_over (system_definitions observation_table_base_system) observation_table_group_system"
    by (rule schema_system_formed_over_mono[OF observation_table_group_formed_over observation_table_base_roots])
  have fresh: "system_definitions observation_table_components_system\<inter>{326,327,328,329,330,331,332,333,334,335}={}"
    using observation_base_subdomain data_set_comparison_base_subdomain data_flatten_base_subdomain by auto
  show "system_definitions observation_table_base_system\<inter>system_definitions observation_table_group_system={}"
    using fresh observation_table_base_subdomain by auto
qed

definition observation_table_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_table_system=system_union observation_table_base_system observation_table_group_system"

lemma observation_table_system_formed [simp]: "schema_system_formed observation_table_system"
  using observation_table_group.formed by (simp only: observation_table_system_def)

lemma observation_table_definitions [simp]:
  "system_definitions observation_table_system=system_definitions observation_table_base_system\<union>{326,327,328,329,330,331,332,333,334,335}"
  by (simp add: observation_table_system_def)

lemma observation_table_call:
  "schema_call_formed observation_table_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_table_system \<and> term_formed t"
  unfolding observation_table_system_def
  by (rule observation_table_group.variable_calls[where D="{326,327,328,329,330,331,332,333,334,335}" and a=0,
    OF observation_table_base_call]) auto

lemma observation_table_clause:
  assumes "d\<in>{326,327,328,329,330,331,332,333,334,335}"
  shows "((d,c),S)\<in>system_clauses observation_table_system \<longleftrightarrow>
    (c,S)\<in>observation_table_clause_family d"
  using observation_table_group.group_clauses[of d c S] assms
  by (simp only: observation_table_system_def observation_table_group_clauses
    observation_table_group_definitions; blast)

lemma observation_table_base_meaning:
  assumes "d\<in>{301,306,311,317,324}"
  shows "(d,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning observation_table_components_system"
proof -
  have member: "d\<in>system_definitions observation_table_base_system" using observation_table_base_roots assms by blast
  show ?thesis using observation_table_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF observation_table_components_formed member[unfolded observation_table_base_system_def], of t]
    by (simp only: observation_table_system_def observation_table_base_system_def)
qed

end
