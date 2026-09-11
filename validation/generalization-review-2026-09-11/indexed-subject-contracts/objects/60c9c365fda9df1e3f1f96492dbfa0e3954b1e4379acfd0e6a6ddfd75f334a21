theory Factor_Generation_Dependency_Clauses
  imports Factor_Generation_Retention_Base
begin

section \<open>Actual predecessor reports determine recursively read sites\<close>

definition generation_read_site_root_schema :: "(nat,nat,nat) factor_schema" where
  "generation_read_site_root_schema=data_rule
    (Pattern_Pair (generation_source_pattern data_x data_y data_z) (Pattern_Pair data_y data_z))
    {(0,152,generation_source_pattern data_x data_y data_z)}"

definition generation_read_site_step_schema :: "(nat,nat,nat) factor_schema" where
  "generation_read_site_step_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 4)))
    {(0,169,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))),
     (1,155,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 5) (Pattern_Variable 6))
      (Pattern_Variable 7)),
     (2,5,Pattern_Pair
      (generation_predecessor_row_pattern (Pattern_Variable 8) (Pattern_Variable 9)
        (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 4)) (Pattern_Variable 10))
      (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 11)))}"

definition generation_citation_root_schema :: "bool \<Rightarrow> (nat,nat,nat) factor_schema" where
  "generation_citation_root_schema predecessor=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1)) (Pattern_Variable 2))
    {(0,147,Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (generation_fields_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))),
     (1,5,Pattern_Pair
      (if predecessor then Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 2) else Pattern_Variable 2)
      (Pattern_Pair
        (if predecessor then Pattern_Variable 4
         else data_list_pattern [Pattern_Variable 3,Pattern_Variable 5,Pattern_Variable 6])
        (Pattern_Variable 8)))}"

definition generation_request_schema :: "(nat,nat,nat) factor_schema" where
  "generation_request_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 4)))
    {(0,169,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 5))),
     (1,37,artifact_lookup_pattern (Pattern_Variable 0) (Pattern_Variable 3) (Pattern_Variable 6)),
     (2,170,Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 5)) (Pattern_Variable 4))}"

definition generation_demanded_slot_schema :: "(nat,nat,nat) factor_schema" where
  "generation_demanded_slot_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 4)))
    {(0,171,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 5))),
     (1,42,citation_reading_pattern (Pattern_Variable 0) (Pattern_Variable 3) (Pattern_Variable 5)
       (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 8)),
     (2,5,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 9)))}"

definition generation_required_source_schema :: "(nat,nat,nat) factor_schema" where
  "generation_required_source_schema=data_rule
    (Pattern_Pair (generation_source_pattern data_x data_y data_z) data_w)
    {(0,169,Pattern_Pair (generation_source_pattern data_x data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4)))}"

definition generation_required_target_schema :: "(nat,nat,nat) factor_schema" where
  "generation_required_target_schema=data_rule
    (Pattern_Pair (generation_source_pattern data_x data_y data_z) data_w)
    {(0,172,Pattern_Pair (generation_source_pattern data_x data_y data_z)
       (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))),
     (1,38,binding_lookup_pattern data_x (Pattern_Variable 4) (Pattern_Variable 5) data_w)}"

definition generation_closed_source_schema :: "(nat,nat,nat) factor_schema" where
  "generation_closed_source_schema=data_rule
    (generation_source_pattern (Pattern_Pair data_x data_y) data_z data_w)
    {(0,152,generation_source_pattern (Pattern_Pair data_x data_y) data_z data_w),
     (1,51,Pattern_Pair data_x (Pattern_Variable 4)),
     (2,51,Pattern_Pair data_y (Pattern_Variable 5)),
     (3,174,Pattern_Pair (generation_source_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 4)),
     (4,175,Pattern_Pair (generation_source_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 5))}"

definition generation_retention_report_schema :: "(nat,nat,nat) factor_schema" where
  "generation_retention_report_schema=data_rule
    (Pattern_Pair (generation_source_pattern data_x data_y data_z) data_w)
    {(0,176,generation_source_pattern data_w data_y data_z),(1,113,Pattern_Pair data_w data_x)}"

definition generation_retention_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "generation_retention_group_clauses d=
    (if d=169 then {(0,generation_read_site_root_schema),(1,generation_read_site_step_schema)}
     else if d=170 then {(0,generation_citation_root_schema False),(1,generation_citation_root_schema True)}
     else if d=171 then {(0,generation_request_schema)}
     else if d=172 then {(0,generation_demanded_slot_schema)}
     else if d=173 then {(0,generation_required_source_schema),(1,generation_required_target_schema)}
     else if d=174 then context_list_clauses 173 174
     else if d=175 then context_list_clauses 172 175
     else if d=176 then {(0,generation_closed_source_schema)}
     else if d=177 then {(0,generation_retention_report_schema)}
     else {})"

definition generation_retention_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "generation_retention_definition_group=\<lparr>
    system_interfaces=image (\<lambda>d. (d,data_x)) {169,170,171,172,173,174,175,176,177},
    system_clauses=(\<Union>d\<in>{169,170,171,172,173,174,175,176,177}.
      image (\<lambda>(c,S). ((d,c),S)) (generation_retention_group_clauses d))\<rparr>"

lemma generation_retention_group_definitions [simp]:
  "system_definitions generation_retention_definition_group={169,170,171,172,173,174,175,176,177}"
  by (auto simp: generation_retention_definition_group_def system_definitions_def rel_dom_def)

lemma generation_retention_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces generation_retention_definition_group \<longleftrightarrow>
    d\<in>{169,170,171,172,173,174,175,176,177} \<and> p=data_x"
  by (auto simp: generation_retention_definition_group_def)

lemma generation_retention_group_family [simp]:
  "((d,c),S)\<in>system_clauses generation_retention_definition_group \<longleftrightarrow>
    d\<in>{169,170,171,172,173,174,175,176,177} \<and> (c,S)\<in>generation_retention_group_clauses d"
  by (auto simp: generation_retention_definition_group_def)

lemma generation_retention_group_finite: "finite (generation_retention_group_clauses d)"
  by (simp add: generation_retention_group_clauses_def context_list_clauses_def)

lemma generation_retention_group_functional: "single_valued (generation_retention_group_clauses d)"
  by (auto simp: generation_retention_group_clauses_def context_list_clauses_def single_valued_def)

lemmas generation_retention_schema_defs = generation_read_site_root_schema_def generation_read_site_step_schema_def
  generation_citation_root_schema_def generation_request_schema_def generation_demanded_slot_schema_def
  generation_required_source_schema_def generation_required_target_schema_def generation_closed_source_schema_def
  generation_retention_report_schema_def context_list_nil_schema_def context_list_step_schema_def

lemma generation_retention_group_ordinary:
  assumes "(c,S)\<in>generation_retention_group_clauses d"
  shows "schema_material_premises S={}"
  using assms by (auto simp: generation_retention_group_clauses_def context_list_clauses_def
    generation_retention_schema_defs split: if_splits)

lemma generation_retention_group_schema_formation:
  assumes "(c,S)\<in>generation_retention_group_clauses d"
  shows "schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions generation_retention_components_system\<union>
      system_definitions generation_retention_definition_group"
  using assms
  by (auto simp: generation_retention_group_clauses_def context_list_clauses_def generation_retention_schema_defs
    schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
    split: if_splits)

lemma generation_retention_group_source_formation:
  "schema_system_formed_over (system_definitions generation_retention_components_system) generation_retention_definition_group"
proof -
  have finite: "finite (system_interfaces generation_retention_definition_group)"
    "finite (system_clauses generation_retention_definition_group)"
    by (simp_all add: generation_retention_definition_group_def generation_retention_group_finite)
  have interfaces: "single_valued (system_interfaces generation_retention_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses generation_retention_definition_group)"
    using generation_retention_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses generation_retention_definition_group \<longrightarrow>
    d\<in>system_definitions generation_retention_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions generation_retention_components_system\<union>
      system_definitions generation_retention_definition_group"
    using generation_retention_group_schema_formation by auto
  show ?thesis using finite interfaces clauses schemas by (simp add: schema_system_formed_over_def)
qed

lemma generation_retention_group_external_dependencies:
  "system_external_dependencies generation_retention_definition_group={5,37,38,42,51,113,147,152,155}"
  by (simp add: system_external_dependencies_clauses generation_retention_definition_group_def
    generation_retention_group_clauses_def context_list_clauses_def generation_retention_schema_defs
    schema_dependencies_def rel_ran_image system_definitions_def rel_dom_image; auto)

definition generation_retention_base_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_retention_base_system=rooted_system generation_retention_components_system
    (system_external_dependencies generation_retention_definition_group)"

lemma generation_retention_base_formed [simp]: "schema_system_formed generation_retention_base_system"
  unfolding generation_retention_base_system_def
  by (rule rooted_system_formed[OF generation_retention_components_formed])

lemma generation_retention_base_definitions:
  "system_definitions generation_retention_base_system=
    system_definition_closure generation_retention_components_system {5,37,38,42,51,113,147,152,155}"
  unfolding generation_retention_base_system_def generation_retention_group_external_dependencies
  by (rule rooted_system_definitions[OF generation_retention_components_formed]) auto

lemma generation_retention_base_subdomain:
  "system_definitions generation_retention_base_system\<subseteq>system_definitions generation_retention_components_system"
  unfolding generation_retention_base_system_def by (rule rooted_system_subdomain)

lemma generation_retention_base_roots:
  "{5,37,38,42,51,113,147,152,155}\<subseteq>system_definitions generation_retention_base_system"
  unfolding generation_retention_base_system_def generation_retention_group_external_dependencies
  by (rule rooted_system_roots[OF generation_retention_components_formed]) auto

lemma generation_retention_base_least:
  assumes "{5,37,38,42,51,113,147,152,155}\<subseteq>U" "system_dependency_closed generation_retention_components_system U"
  shows "system_definitions generation_retention_base_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: generation_retention_base_definitions)

lemma generation_retention_base_call:
  "schema_call_formed generation_retention_base_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_retention_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies generation_retention_definition_group" and d=d and t=t,
    OF generation_retention_components_formed]
  by (simp only: generation_retention_base_system_def rooted_system_def system_restriction_definitions
    generation_retention_components_call; blast)

lemma generation_retention_base_meaning:
  assumes "d\<in>system_definitions generation_retention_base_system"
  shows "(d,t)\<in>positive_meaning generation_retention_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_retention_components_system"
  using rooted_system_meaning[where roots="system_external_dependencies generation_retention_definition_group" and d=d and t=t,
    OF generation_retention_components_formed] assms
  by (simp only: generation_retention_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma generation_retention_base_agreement:
  "systems_agree_on generation_retention_components_system generation_retention_base_system
    (system_definitions generation_retention_base_system)"
  unfolding generation_retention_base_system_def by (rule rooted_system_agreement)

lemma generation_retention_group_relative_formation:
  "schema_system_formed_over (system_definitions generation_retention_base_system) generation_retention_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies generation_retention_definition_group)
      generation_retention_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF generation_retention_group_source_formation])
  have retained: "system_external_dependencies generation_retention_definition_group\<subseteq>
      system_definitions generation_retention_base_system"
    using generation_retention_base_roots by (simp only: generation_retention_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation generation_retention_group:
  positive_definition_group generation_retention_base_system generation_retention_definition_group
proof (rule positive_definition_group.intro[OF generation_retention_base_formed generation_retention_group_relative_formation])
  let ?new="{169::nat,170,171,172,173,174,175,176,177}"
  have target: "system_definitions target_difference_system\<inter>?new={}" by auto
  have located: "system_definitions located_admission_system\<inter>?new={}" by auto
  have inclusion: "system_definitions environment_inclusion_system\<inter>?new={}" by auto
  have value_fresh: "{139,140,141,142,143,144,145,146}\<inter>?new={}" by auto
  have value_boundary: "system_definitions generation_value_system\<inter>?new={}"
    using generation_target_subdomain target value_fresh unfolding generation_value_definitions by blast
  have components: "system_definitions generation_source_components_system\<inter>?new={}"
    using located value_boundary unfolding generation_source_components_definitions by blast
  have source_fresh: "{147,148,149,150,151,152,153,154,155}\<inter>?new={}" by auto
  have source: "system_definitions generation_source_system\<inter>?new={}"
    using generation_source_base_subdomain components source_fresh unfolding generation_source_definitions by blast
  have fresh: "system_definitions generation_retention_components_system\<inter>
      system_definitions generation_retention_definition_group={}"
    using source inclusion
    unfolding generation_retention_components_definitions generation_retention_group_definitions by blast
  show "system_definitions generation_retention_base_system\<inter>system_definitions generation_retention_definition_group={}"
    using generation_retention_base_subdomain fresh by blast
qed

definition generation_retention_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_retention_system=system_union generation_retention_base_system generation_retention_definition_group"

lemma generation_retention_system_formed [simp]: "schema_system_formed generation_retention_system"
  using generation_retention_group.formed by (simp only: generation_retention_system_def)

lemma generation_retention_definitions [simp]:
  "system_definitions generation_retention_system=
    system_definitions generation_retention_base_system\<union>{169,170,171,172,173,174,175,176,177}"
  by (simp add: generation_retention_system_def)

lemma generation_retention_call:
  "schema_call_formed generation_retention_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_retention_system \<and> term_formed t"
  using generation_retention_group.variable_calls[OF generation_retention_base_call generation_retention_group_interfaces, of d t]
  by (simp only: generation_retention_system_def)

lemma generation_retention_old_meaning:
  assumes "d\<in>system_definitions generation_retention_base_system"
  shows "(d,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_retention_components_system"
  using generation_retention_group.old_meaning[OF assms, of t] generation_retention_base_meaning[OF assms, of t]
  by (simp only: generation_retention_system_def; blast)

lemma generation_retention_clause:
  assumes "d\<in>{169,170,171,172,173,174,175,176,177}"
  shows "((d,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>generation_retention_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses generation_retention_definition_group"
    using generation_retention_group.group_agreement assms
    by (simp only: generation_retention_system_def systems_agree_on_def generation_retention_group_definitions; blast)
  show ?thesis using same assms by (simp only: generation_retention_group_family; blast)
qed

lemma generation_retention_clauses [simp]:
  "((169,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_read_site_root_schema),(1,generation_read_site_step_schema)}"
  "((170,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_citation_root_schema False),(1,generation_citation_root_schema True)}"
  "((171,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_request_schema)}"
  "((172,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_demanded_slot_schema)}"
  "((173,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_required_source_schema),(1,generation_required_target_schema)}"
  "((174,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>context_list_clauses 173 174"
  "((175,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>context_list_clauses 172 175"
  "((176,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_closed_source_schema)}"
  "((177,c),S)\<in>system_clauses generation_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_retention_report_schema)}"
  using generation_retention_clause by (auto simp: generation_retention_group_clauses_def)

lemma generation_retention_components:
  "(5,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(37,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(38,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (38,t)\<in>positive_meaning binding_lookup_system"
  "(42,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (42,t)\<in>positive_meaning citation_reading_system"
  "(51,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(113,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  "(147,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (147,t)\<in>positive_meaning generation_source_system"
  "(152,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (152,t)\<in>positive_meaning generation_source_system"
  "(155,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (155,t)\<in>positive_meaning generation_source_system"
  using generation_retention_old_meaning[of 5 t]
    generation_retention_old_meaning[of 37 t]
    generation_retention_old_meaning[of 38 t]
    generation_retention_old_meaning[of 42 t]
    generation_retention_old_meaning[of 51 t]
    generation_retention_old_meaning[of 113 t]
    generation_retention_old_meaning[of 147 t]
    generation_retention_old_meaning[of 152 t]
    generation_retention_old_meaning[of 155 t] generation_retention_base_roots
    generation_retention_component_meanings[of t] by auto

lemma generation_retention_rule:
  assumes entry: "d\<in>{169,170,171,172,173,174,175,176,177}"
    and clause: "(c,S)\<in>generation_retention_group_clauses d"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning generation_retention_system"
  shows "(d,evaluate_pattern h (schema_conclusion S))\<in>positive_meaning generation_retention_system"
proof -
  have member: "((d,c),S)\<in>system_clauses generation_retention_system"
    using clause by (simp only: generation_retention_clause[OF entry])
  have ordinary: "schema_material_premises S={}" by (rule generation_retention_group_ordinary[OF clause])
  have schema: "schema_formed S" using generation_retention_group_schema_formation[OF clause] by blast
  have formed: "term_formed (evaluate_pattern h (schema_conclusion S))"
    by (rule evaluate_pattern_formed) (use schema assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed generation_retention_system d (evaluate_pattern h (schema_conclusion S))"
    using entry formed by (auto simp: generation_retention_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment call support])
qed

lemma generation_retention_base_boundary:
  "system_definitions generation_retention_base_system\<subseteq>
    system_definitions generation_source_system\<union>system_definitions row_keys_system\<union>{112,113}"
  by (rule generation_retention_base_least[OF _ generation_retention_component_boundary]) auto

theorem generation_retention_has_no_replay_or_scope_checker:
  "system_definitions generation_retention_system\<inter>{80,85,109,110,111,115,122,160,162,165,167}={}"
proof -
  let ?bad="{80::nat,85,109,110,111,115,122,160,162,165,167}"
  have target: "system_definitions target_difference_system\<inter>?bad={}" by auto
  have located: "system_definitions located_admission_system\<inter>?bad={}" by auto
  have local_fresh: "{139,140,141,142,143,144,145,146}\<inter>?bad={}" by auto
  have value_boundary: "system_definitions generation_value_system\<inter>?bad={}"
    using generation_target_subdomain target local_fresh unfolding generation_value_definitions by blast
  have components: "system_definitions generation_source_components_system\<inter>?bad={}"
    using located value_boundary unfolding generation_source_components_definitions by blast
  have source_fresh: "{147,148,149,150,151,152,153,154,155}\<inter>?bad={}" by auto
  have source: "system_definitions generation_source_system\<inter>{80,85,109,110,111,115,122,160,162,165,167}={}"
    using generation_source_base_subdomain components source_fresh unfolding generation_source_definitions by blast
  have lower: "(system_definitions row_keys_system\<union>{112,113})\<inter>{80,85,109,110,111,115,122,160,162,165,167}={}"
    by auto
  have fresh: "{169,170,171,172,173,174,175,176,177}\<inter>?bad={}" by auto
  have upper: "(system_definitions generation_source_system\<union>
      system_definitions row_keys_system\<union>{112,113})\<inter>?bad={}"
    by (simp only: Un_assoc Int_Un_distrib2 source lower; simp)
  have included: "system_definitions generation_retention_base_system\<inter>?bad \<subseteq>
      (system_definitions generation_source_system\<union>system_definitions row_keys_system\<union>{112,113})\<inter>?bad"
    by (rule Int_mono[OF generation_retention_base_boundary subset_refl])
  have base: "system_definitions generation_retention_base_system\<inter>?bad={}"
    using included by (simp only: upper subset_empty)
  show ?thesis by (simp only: generation_retention_definitions Int_Un_distrib2 base fresh; simp)
qed

text \<open>
  Nine definitions have fourteen ordinary clauses. The recursive site entry
  starts from admitted source reading and follows actual complete predecessor
  reports. The local syntax entry exposes all three field citations and every
  predecessor citation. The request and slot entries retain their actual use.

  Required artifact uses are read sources or targets of demanded bindings.
  The two generic list profiles check the actual stored table keys. Closed
  source admission supplies the complete source role even for empty binding
  lists. The final report checks that closed source in the claimed environment
  and its inclusion in the submitted environment at the unchanged root.

  The program's least base contains its nine actual external callees and all
  their complete dependency definitions. No native clause tests a failed
  call, uses an external truth callback, or carries a stored recursion bound.
\<close>

end
