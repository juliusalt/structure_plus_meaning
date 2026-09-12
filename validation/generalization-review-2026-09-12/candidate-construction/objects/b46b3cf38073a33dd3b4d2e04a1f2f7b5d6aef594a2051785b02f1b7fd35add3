theory Factor_Data_Product_Clauses
  imports Factor_Data_Product_Components Factor_Context_Pairing Factor_Admitted_Context Factor_Result_Comparison
begin

section \<open>Two maps and flattening construct every ordered pair\<close>

definition data_product_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "data_product_clause_family d=(if d=318 then {(0,paired_terms_schema 2 2)}
    else if d=319 then related_list_clauses 318 319
    else if d=320 then {(0,admitted_context_schema 2 319)}
    else if d=321 then {(0,transposed_context_schema 320)}
    else if d=322 then related_list_clauses 321 322
    else if d=323 then {(0,context_result_comparison_schema 322 218)}
    else if d=324 then {(0,admitted_context_schema 4 323)}
    else if d=325 then {(0,context_result_comparison_schema 324 219)} else {})"

definition data_product_group_system :: "(nat,nat,nat,nat) schema_system" where
  "data_product_group_system=\<lparr>system_interfaces={(318,data_x),(319,data_x),(320,data_x),
      (321,data_x),(322,data_x),(323,data_x),(324,data_x),(325,data_x)},
    system_clauses={((318,0),paired_terms_schema 2 2),
      ((319,0),related_list_nil_schema),((319,1),related_list_step_schema 318 319),
      ((320,0),admitted_context_schema 2 319),((321,0),transposed_context_schema 320),
      ((322,0),related_list_nil_schema),((322,1),related_list_step_schema 321 322),
      ((323,0),context_result_comparison_schema 322 218),
      ((324,0),admitted_context_schema 4 323),((325,0),context_result_comparison_schema 324 219)}\<rparr>"

lemma data_product_group_definitions [simp]:
  "system_definitions data_product_group_system={318,319,320,321,322,323,324,325}"
  by (auto simp: data_product_group_system_def system_definitions_def rel_dom_def)

lemma data_product_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces data_product_group_system \<longleftrightarrow> d\<in>{318,319,320,321,322,323,324,325} \<and> p=data_x"
  by (auto simp: data_product_group_system_def)

lemma data_product_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses data_product_group_system \<longleftrightarrow>
    d\<in>{318,319,320,321,322,323,324,325} \<and> (c,S)\<in>data_product_clause_family d"
  by (auto simp: data_product_group_system_def data_product_clause_family_def related_list_clauses_def)

lemma data_product_group_formed_over:
  "schema_system_formed_over {2,4,218,219} data_product_group_system"
  by (simp only: schema_system_formed_over_def data_product_group_definitions)
    (auto simp: data_product_group_system_def paired_terms_schema_def transposed_context_schema_def admitted_context_schema_def context_result_comparison_schema_def
      related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_product_external_dependencies:
  "system_external_dependencies data_product_group_system={2,4,218,219}"
  by (simp only: system_external_dependencies_clauses data_product_group_definitions)
    (auto simp: data_product_group_system_def paired_terms_schema_def transposed_context_schema_def admitted_context_schema_def context_result_comparison_schema_def
      related_list_clauses_def related_list_nil_schema_def related_list_step_schema_def
      schema_dependencies_def rel_ran_image)

definition data_product_base_system :: "(nat,nat,nat,nat) schema_system" where
  "data_product_base_system=rooted_system data_product_components_system
    (system_external_dependencies data_product_group_system)"

lemma data_product_base_formed [simp]: "schema_system_formed data_product_base_system"
  unfolding data_product_base_system_def by (rule rooted_system_formed[OF data_product_components_formed])

lemma data_product_base_subdomain:
  "system_definitions data_product_base_system\<subseteq>system_definitions data_product_components_system"
  unfolding data_product_base_system_def by (rule rooted_system_subdomain)

lemma data_product_base_roots:
  "{2,4,218,219}\<subseteq>system_definitions data_product_base_system"
  unfolding data_product_base_system_def data_product_external_dependencies
  by (rule rooted_system_roots[OF data_product_components_formed])
    (use data_flatten_base_data_roots in auto)

lemma data_product_base_least:
  assumes "{2,4,218,219}\<subseteq>U" "system_dependency_closed data_product_components_system U"
  shows "system_definitions data_product_base_system\<subseteq>U"
  unfolding data_product_base_system_def data_product_external_dependencies
  by (rule rooted_system_least[OF data_product_components_formed _ assms])
    (use data_flatten_base_data_roots in auto)

lemma data_product_base_call:
  "schema_call_formed data_product_base_system d t \<longleftrightarrow>
    d\<in>system_definitions data_product_base_system \<and> term_formed t"
  unfolding data_product_base_system_def
  by (rule rooted_system_variable_calls[OF data_product_components_formed data_product_components_call])

interpretation data_product_group:
  positive_definition_group data_product_base_system data_product_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed data_product_base_system" by simp
  show "schema_system_formed_over (system_definitions data_product_base_system) data_product_group_system"
    by (rule schema_system_formed_over_mono[OF data_product_group_formed_over data_product_base_roots])
  have boundary: "system_definitions data_product_components_system\<inter>{318,319,320,321,322,323,324,325}={}"
    using data_flatten_base_subdomain data_set_comparison_base_subdomain by auto
  show "system_definitions data_product_base_system\<inter>system_definitions data_product_group_system={}"
    using boundary data_product_base_subdomain by auto
qed

definition data_product_system :: "(nat,nat,nat,nat) schema_system" where
  "data_product_system=system_union data_product_base_system data_product_group_system"

lemma data_product_system_formed [simp]: "schema_system_formed data_product_system"
  using data_product_group.formed by (simp only: data_product_system_def)

lemma data_product_definitions [simp]:
  "system_definitions data_product_system=system_definitions data_product_base_system\<union>{318,319,320,321,322,323,324,325}"
  by (simp add: data_product_system_def)

lemma data_product_call:
  "schema_call_formed data_product_system d t \<longleftrightarrow>
    d\<in>system_definitions data_product_system \<and> term_formed t"
  unfolding data_product_system_def
  by (rule data_product_group.variable_calls[where D="{318,319,320,321,322,323,324,325}" and a=0,
    OF data_product_base_call]) auto

lemma data_product_clause:
  assumes "d\<in>{318,319,320,321,322,323,324,325}"
  shows "((d,c),S)\<in>system_clauses data_product_system \<longleftrightarrow>
    (c,S)\<in>data_product_clause_family d"
  using data_product_group.group_clauses[of d c S] assms
  by (simp only: data_product_system_def data_product_group_clauses
    data_product_group_definitions; blast)

lemma data_product_base_meaning:
  assumes "d\<in>{2,4,218,219}"
  shows "(d,t)\<in>positive_meaning data_product_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_product_components_system"
proof -
  have member: "d\<in>system_definitions data_product_base_system"
    using data_product_base_roots assms by blast
  show ?thesis using data_product_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF data_product_components_formed member[unfolded data_product_base_system_def], of t]
    by (simp only: data_product_system_def data_product_base_system_def)
qed

end
