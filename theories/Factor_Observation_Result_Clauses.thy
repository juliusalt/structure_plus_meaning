theory Factor_Observation_Result_Clauses
  imports Factor_Observation_Components Factor_Result_Comparison
begin

section \<open>Profiles and losses instantiate the same result comparison\<close>

definition observation_result_group_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_result_group_system=\<lparr>system_interfaces={(302,data_x),(307,data_x)},
    system_clauses={((302,0),context_result_comparison_schema 301 219),
      ((307,0),context_result_comparison_schema 306 219)}\<rparr>"

lemma observation_result_group_definitions [simp]:
  "system_definitions observation_result_group_system={302,307}"
  by (auto simp: observation_result_group_system_def system_definitions_def rel_dom_def)

lemma observation_result_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces observation_result_group_system \<longleftrightarrow> d\<in>{302,307} \<and> p=data_x"
  by (auto simp: observation_result_group_system_def)

lemma observation_result_group_formed_over:
  "schema_system_formed_over {219,301,306} observation_result_group_system"
  by (simp only: schema_system_formed_over_def observation_result_group_definitions)
    (auto simp: observation_result_group_system_def single_valued_def)

lemma observation_result_external_dependencies:
  "system_external_dependencies observation_result_group_system={219,301,306}"
  by (simp only: system_external_dependencies_clauses observation_result_group_definitions)
    (auto simp: observation_result_group_system_def)

definition observation_result_base_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_result_base_system=rooted_system observation_collection_system
    (system_external_dependencies observation_result_group_system)"

lemma observation_result_base_formed [simp]: "schema_system_formed observation_result_base_system"
  unfolding observation_result_base_system_def by (rule rooted_system_formed[OF observation_collection_formed])

lemma observation_result_base_subdomain:
  "system_definitions observation_result_base_system\<subseteq>system_definitions observation_collection_system"
  unfolding observation_result_base_system_def by (rule rooted_system_subdomain)

lemma observation_result_base_roots:
  "{219,301,306}\<subseteq>system_definitions observation_result_base_system"
  unfolding observation_result_base_system_def observation_result_external_dependencies
  by (rule rooted_system_roots[OF observation_collection_formed]) auto

lemma observation_result_base_least:
  assumes "{219,301,306}\<subseteq>U" "system_dependency_closed observation_collection_system U"
  shows "system_definitions observation_result_base_system\<subseteq>U"
  unfolding observation_result_base_system_def observation_result_external_dependencies
  by (rule rooted_system_least[OF observation_collection_formed _ assms]) auto

lemma observation_result_base_call:
  "schema_call_formed observation_result_base_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_result_base_system \<and> term_formed t"
  unfolding observation_result_base_system_def
  by (rule rooted_system_variable_calls[OF observation_collection_formed observation_collection_call])

interpretation observation_result_group:
  positive_definition_group observation_result_base_system observation_result_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed observation_result_base_system" by simp
  show "schema_system_formed_over (system_definitions observation_result_base_system) observation_result_group_system"
    by (rule schema_system_formed_over_mono[OF observation_result_group_formed_over observation_result_base_roots])
  have boundary: "system_definitions observation_collection_system\<inter>{302,307}={}"
    using observation_base_subdomain data_set_comparison_base_subdomain by auto
  show "system_definitions observation_result_base_system\<inter>system_definitions observation_result_group_system={}"
    using boundary observation_result_base_subdomain by (simp only: observation_result_group_definitions) blast
qed

definition observation_result_system :: "(nat,nat,nat,nat) schema_system" where
  "observation_result_system=system_union observation_result_base_system observation_result_group_system"

lemma observation_result_system_formed [simp]: "schema_system_formed observation_result_system"
  using observation_result_group.formed by (simp only: observation_result_system_def)

lemma observation_result_definitions [simp]:
  "system_definitions observation_result_system=system_definitions observation_result_base_system\<union>{302,307}"
  by (simp add: observation_result_system_def)

lemma observation_result_call:
  "schema_call_formed observation_result_system d t \<longleftrightarrow>
    d\<in>system_definitions observation_result_system \<and> term_formed t"
  unfolding observation_result_system_def
  by (rule observation_result_group.variable_calls[where D="{302,307}" and a=0,
    OF observation_result_base_call]) auto

lemma observation_result_clause:
  assumes "d\<in>{302,307}"
  shows "((d,c),S)\<in>system_clauses observation_result_system \<longleftrightarrow>
    c=0 \<and> S=context_result_comparison_schema (if d=302 then 301 else 306) 219"
proof -
  have member: "d\<in>system_definitions observation_result_group_system" using assms by simp
  have same: "((d,c),S)\<in>system_clauses observation_result_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses observation_result_group_system"
    using observation_result_group.group_clauses[OF member, of c S]
    by (simp only: observation_result_system_def)
  show ?thesis by (simp only: same) (use assms in \<open>auto simp: observation_result_group_system_def\<close>)
qed

lemma observation_result_base_meaning:
  assumes "d\<in>{219,301,306}"
  shows "(d,t)\<in>positive_meaning observation_result_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning observation_collection_system"
proof -
  have member: "d\<in>system_definitions observation_result_base_system"
    using observation_result_base_roots assms by blast
  show ?thesis using observation_result_group.old_meaning[OF member, of t]
    rooted_system_meaning_at[OF observation_collection_formed member[unfolded observation_result_base_system_def], of t]
    by (simp only: observation_result_system_def observation_result_base_system_def)
qed

interpretation observation_profile_comparison:
  context_result_comparison_profile observation_result_system 302 301 219
  by (rule context_result_comparison_profile.intro[OF observation_result_system_formed])
    (auto simp: observation_result_clause observation_result_call)

interpretation observation_losses_comparison:
  context_result_comparison_profile observation_result_system 307 306 219
  by (rule context_result_comparison_profile.intro[OF observation_result_system_formed])
    (auto simp: observation_result_clause observation_result_call)

lemma observation_result_components:
  "(301,t)\<in>positive_meaning observation_result_system \<longleftrightarrow>
    (301,t)\<in>positive_meaning observation_system"
  "(306,t)\<in>positive_meaning observation_result_system \<longleftrightarrow>
    (306,t)\<in>positive_meaning observation_system"
  "(219,t)\<in>positive_meaning observation_result_system \<longleftrightarrow>
    (219,t)\<in>positive_meaning data_set_comparison_system"
  using observation_result_base_meaning[of 301 t] observation_result_base_meaning[of 306 t]
    observation_result_base_meaning[of 219 t] observation_collection_meaning[of 301 t]
    observation_collection_meaning[of 306 t] observation_collection_set_meaning[of t]
  by auto

text \<open>
  Both public entries retain the earlier input computations in a private
  result call. Each then invokes the existing set comparator on that result
  and the supplied output. The least dependency boundary is derived from
  these two actual clauses and retains complete original definitions.
\<close>

end
