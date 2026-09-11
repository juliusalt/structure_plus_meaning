theory Factor_Generation_Source_Clauses
  imports Factor_Generation_Source_Base Factor_Related_Lists
begin

section \<open>The source reader keeps the existing field and site presentations\<close>

abbreviation generation_fields_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "generation_fields_term l m p c \<equiv> Pair_Term l (Pair_Term m (Pair_Term p c))"

abbreviation generation_fields_pattern ::
  "nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow>
    nat term_pattern \<Rightarrow> nat term_pattern" where
  "generation_fields_pattern l m p c \<equiv> Pattern_Pair l (Pattern_Pair m (Pattern_Pair p c))"

abbreviation generation_source_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "generation_source_term e u r \<equiv> Pair_Term (Pair_Term e u) r"

abbreviation generation_source_pattern ::
  "nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> nat term_pattern" where
  "generation_source_pattern e u r \<equiv> Pattern_Pair (Pattern_Pair e u) r"

abbreviation generation_syntax_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "generation_syntax_argument a r l m p c \<equiv> rooted_rows_argument a r (generation_fields_term l m p c)"

abbreviation generation_fields_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "generation_fields_argument e u r l m p c \<equiv>
    Pair_Term (generation_source_term e u r) (generation_fields_term l m p c)"

abbreviation generation_predecessor_row_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "generation_predecessor_row_term s d z h \<equiv> Pair_Term s (Pair_Term d (Pair_Term z h))"

abbreviation generation_predecessor_row_pattern ::
  "nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow> nat term_pattern \<Rightarrow>
    nat term_pattern \<Rightarrow> nat term_pattern" where
  "generation_predecessor_row_pattern s d z h \<equiv> Pattern_Pair s (Pattern_Pair d (Pattern_Pair z h))"

definition generation_syntax_schema :: "(nat,nat,nat) factor_schema" where
  "generation_syntax_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (generation_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5)))
    {(0,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (data_list_pattern [Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 2),
        Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 6),
        Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 4),
        Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 5)])),
      (1,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 6)) (Pattern_Variable 3))}"

definition generation_fields_schema :: "(nat,nat,nat) factor_schema" where
  "generation_fields_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (generation_fields_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)))
    {(0,37,artifact_lookup_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 7)),
      (1,147,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 2))
        (generation_fields_pattern (Pattern_Variable 8) (Pattern_Variable 4) (Pattern_Variable 9) (Pattern_Variable 10))),
      (2,43,citation_observation_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 8) (Pattern_Variable 3)),
      (3,43,citation_observation_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 9) (Pattern_Variable 5)),
      (4,43,citation_observation_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 10) (Pattern_Variable 6))}"

definition generation_child_value_schema :: "(nat,nat,nat) factor_schema" where
  "generation_child_value_schema=data_rule
    (context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)) (Pattern_Variable 6))
    {(0,153,context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))
      (generation_predecessor_row_pattern (Pattern_Variable 2) (Pattern_Variable 3)
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6)))}"

definition generation_core_report_schema :: "(nat,nat,nat) factor_schema" where
  "generation_core_report_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (generation_fields_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)))
    {(0,139,generation_fields_pattern (Pattern_Variable 3) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)),
      (1,148,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
        (generation_fields_pattern (Pattern_Variable 3) (Pattern_Variable 7) (Pattern_Variable 5) (Pattern_Variable 6))),
      (2,150,context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
        (Pattern_Variable 7) (Pattern_Variable 8)),
      (3,145,Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 4))}"

definition generation_source_schema :: "(nat,nat,nat) factor_schema" where
  "generation_source_schema=data_rule
    (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
    {(0,151,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Variable 3))}"

definition generation_child_row_schema :: "(nat,nat,nat) factor_schema" where
  "generation_child_row_schema=data_rule
    (context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
      (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))
      (generation_predecessor_row_pattern (Pattern_Variable 2) (Pattern_Variable 3)
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) (Pattern_Variable 6)))
    {(0,1,data_list_pattern [Pattern_Variable 2]),
      (1,44,citation_observation_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 3)
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))),
      (2,151,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 4) (Pattern_Variable 5))
        (Pattern_Variable 6))}"

definition generation_predecessor_report_schema :: "(nat,nat,nat) factor_schema" where
  "generation_predecessor_report_schema=data_rule
    (Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
      (Pattern_Variable 3))
    {(0,152,generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2)),
      (1,148,Pattern_Pair (generation_source_pattern (Pattern_Variable 0) (Pattern_Variable 1) (Pattern_Variable 2))
        (generation_fields_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))),
      (2,154,context_relation_pattern (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
        (Pattern_Variable 5) (Pattern_Variable 3))}"

definition generation_source_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "generation_source_group_clauses d=
    (if d=147 then {(0,generation_syntax_schema)}
     else if d=148 then {(0,generation_fields_schema)}
     else if d=149 then {(0,generation_child_value_schema)}
     else if d=150 then related_list_clauses 149 150
     else if d=151 then {(0,generation_core_report_schema)}
     else if d=152 then {(0,generation_source_schema)}
     else if d=153 then {(0,generation_child_row_schema)}
     else if d=154 then related_list_clauses 153 154
     else if d=155 then {(0,generation_predecessor_report_schema)}
     else {})"

definition generation_source_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "generation_source_definition_group=\<lparr>
    system_interfaces=image (\<lambda>d. (d,data_x)) {147,148,149,150,151,152,153,154,155},
    system_clauses=(\<Union>d\<in>{147,148,149,150,151,152,153,154,155}.
      image (\<lambda>(c,S). ((d,c),S)) (generation_source_group_clauses d))\<rparr>"

lemma generation_source_group_definitions [simp]:
  "system_definitions generation_source_definition_group={147,148,149,150,151,152,153,154,155}"
  by (auto simp: generation_source_definition_group_def system_definitions_def rel_dom_def)

lemma generation_source_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces generation_source_definition_group \<longleftrightarrow>
    d\<in>{147,148,149,150,151,152,153,154,155} \<and> p=data_x"
  by (auto simp: generation_source_definition_group_def)

lemma generation_source_group_family [simp]:
  "((d,c),S)\<in>system_clauses generation_source_definition_group \<longleftrightarrow>
    d\<in>{147,148,149,150,151,152,153,154,155} \<and> (c,S)\<in>generation_source_group_clauses d"
  by (auto simp: generation_source_definition_group_def)

lemma generation_source_group_finite: "finite (generation_source_group_clauses d)"
  by (simp add: generation_source_group_clauses_def related_list_clauses_def)

lemma generation_source_group_functional: "single_valued (generation_source_group_clauses d)"
  by (auto simp: generation_source_group_clauses_def related_list_clauses_def single_valued_def)

lemmas generation_source_schema_defs = generation_syntax_schema_def generation_fields_schema_def
  generation_child_value_schema_def generation_core_report_schema_def generation_source_schema_def
  generation_child_row_schema_def generation_predecessor_report_schema_def
  related_list_nil_schema_def related_list_step_schema_def

lemma generation_source_group_schema_formation:
  assumes "(c,S)\<in>generation_source_group_clauses d"
  shows "schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions generation_source_components_system\<union>
      system_definitions generation_source_definition_group"
  using assms
  by (auto simp: generation_source_group_clauses_def related_list_clauses_def generation_source_schema_defs
    schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
    split: if_splits)

lemma generation_source_group_source_formation:
  "schema_system_formed_over (system_definitions generation_source_components_system) generation_source_definition_group"
proof -
  have finite: "finite (system_interfaces generation_source_definition_group)"
    "finite (system_clauses generation_source_definition_group)"
    by (simp_all add: generation_source_definition_group_def generation_source_group_finite)
  have interfaces: "single_valued (system_interfaces generation_source_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses generation_source_definition_group)"
    using generation_source_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses generation_source_definition_group \<longrightarrow>
    d\<in>system_definitions generation_source_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions generation_source_components_system\<union>
      system_definitions generation_source_definition_group"
    using generation_source_group_schema_formation by auto
  show ?thesis using finite interfaces clauses schemas by (simp add: schema_system_formed_over_def)
qed

lemma generation_source_group_external_dependencies:
  "system_external_dependencies generation_source_definition_group={1,32,34,37,43,44,139,145}"
  by (simp add: system_external_dependencies_clauses generation_source_definition_group_def
    generation_source_group_clauses_def related_list_clauses_def generation_source_schema_defs
    schema_dependencies_def rel_ran_image system_definitions_def rel_dom_image; auto)

definition generation_source_base_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_source_base_system=rooted_system generation_source_components_system
    (system_external_dependencies generation_source_definition_group)"

lemma generation_source_base_formed [simp]: "schema_system_formed generation_source_base_system"
  unfolding generation_source_base_system_def
  by (rule rooted_system_formed[OF generation_source_components_formed])

lemma generation_source_base_definitions:
  "system_definitions generation_source_base_system=
    system_definition_closure generation_source_components_system {1,32,34,37,43,44,139,145}"
  unfolding generation_source_base_system_def generation_source_group_external_dependencies
  by (rule rooted_system_definitions[OF generation_source_components_formed]) auto

lemma generation_source_base_subdomain:
  "system_definitions generation_source_base_system\<subseteq>system_definitions generation_source_components_system"
  unfolding generation_source_base_system_def by (rule rooted_system_subdomain)

lemma generation_source_base_roots:
  "{1,32,34,37,43,44,139,145}\<subseteq>system_definitions generation_source_base_system"
  unfolding generation_source_base_system_def generation_source_group_external_dependencies
  by (rule rooted_system_roots[OF generation_source_components_formed]) auto

lemma generation_source_base_least:
  assumes "{1,32,34,37,43,44,139,145}\<subseteq>U" "system_dependency_closed generation_source_components_system U"
  shows "system_definitions generation_source_base_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: generation_source_base_definitions)

lemma generation_source_base_call:
  "schema_call_formed generation_source_base_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_source_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies generation_source_definition_group" and d=d and t=t,
    OF generation_source_components_formed]
  by (simp only: generation_source_base_system_def rooted_system_def system_restriction_definitions
    generation_source_components_call; blast)

lemma generation_source_base_meaning:
  assumes "d\<in>system_definitions generation_source_base_system"
  shows "(d,t)\<in>positive_meaning generation_source_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_source_components_system"
  using rooted_system_meaning[where roots="system_external_dependencies generation_source_definition_group" and d=d and t=t,
    OF generation_source_components_formed] assms
  by (simp only: generation_source_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma generation_source_base_agreement:
  "systems_agree_on generation_source_components_system generation_source_base_system
    (system_definitions generation_source_base_system)"
  unfolding generation_source_base_system_def by (rule rooted_system_agreement)

lemma generation_source_group_relative_formation:
  "schema_system_formed_over (system_definitions generation_source_base_system) generation_source_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies generation_source_definition_group)
      generation_source_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF generation_source_group_source_formation])
  have retained: "system_external_dependencies generation_source_definition_group\<subseteq>
      system_definitions generation_source_base_system"
    using generation_source_base_roots by (simp only: generation_source_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation generation_source_group:
  positive_definition_group generation_source_base_system generation_source_definition_group
proof (rule positive_definition_group.intro[OF generation_source_base_formed generation_source_group_relative_formation])
  have fresh: "system_definitions generation_source_components_system\<inter>
      system_definitions generation_source_definition_group={}"
    using generation_target_subdomain by (auto dest: subsetD)
  show "system_definitions generation_source_base_system\<inter>system_definitions generation_source_definition_group={}"
    using generation_source_base_subdomain fresh by blast
qed

definition generation_source_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_source_system=system_union generation_source_base_system generation_source_definition_group"

lemma generation_source_system_formed [simp]: "schema_system_formed generation_source_system"
  using generation_source_group.formed by (simp only: generation_source_system_def)

lemma generation_source_definitions [simp]:
  "system_definitions generation_source_system=
    system_definitions generation_source_base_system\<union>{147,148,149,150,151,152,153,154,155}"
  by (simp add: generation_source_system_def)

lemma generation_source_call:
  "schema_call_formed generation_source_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_source_system \<and> term_formed t"
  using generation_source_group.variable_calls[OF generation_source_base_call generation_source_group_interfaces, of d t]
  by (simp only: generation_source_system_def)

lemma generation_source_old_meaning:
  assumes "d\<in>system_definitions generation_source_base_system"
  shows "(d,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_source_components_system"
  using generation_source_group.old_meaning[OF assms, of t] generation_source_base_meaning[OF assms, of t]
  by (simp only: generation_source_system_def; blast)

lemma generation_source_clause:
  assumes "d\<in>{147,148,149,150,151,152,153,154,155}"
  shows "((d,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow>
    (c,S)\<in>generation_source_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses generation_source_definition_group"
    using generation_source_group.group_agreement assms
    by (simp only: generation_source_system_def systems_agree_on_def generation_source_group_definitions; blast)
  show ?thesis using same assms by (simp only: generation_source_group_family; blast)
qed

lemma generation_source_clauses [simp]:
  "((147,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_syntax_schema)}"
  "((148,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_fields_schema)}"
  "((149,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_child_value_schema)}"
  "((150,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>related_list_clauses 149 150"
  "((151,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_core_report_schema)}"
  "((152,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_source_schema)}"
  "((153,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_child_row_schema)}"
  "((154,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>related_list_clauses 153 154"
  "((155,c),S)\<in>system_clauses generation_source_system \<longleftrightarrow> (c,S)\<in>{(0,generation_predecessor_report_schema)}"
  using generation_source_clause by (auto simp: generation_source_group_clauses_def)

lemma generation_source_payload:
  "(1,data_list_term [t])\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>b. octets_formed b \<and> t=Payload_Term b)"
  using generation_source_old_meaning[of 1 "data_list_term [t]"] generation_source_base_roots
    generation_source_component_payload[of t] by auto

lemma generation_source_components:
  "(32,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(34,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(37,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(43,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (43,t)\<in>positive_meaning anchored_admission_system"
  "(44,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (44,t)\<in>positive_meaning located_admission_system"
  "(139,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (139,t)\<in>positive_meaning generation_value_system"
  "(145,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> (145,t)\<in>positive_meaning generation_value_system"
  using generation_source_old_meaning[of 32 t] generation_source_old_meaning[of 34 t]
    generation_source_old_meaning[of 37 t] generation_source_old_meaning[of 43 t]
    generation_source_old_meaning[of 44 t] generation_source_old_meaning[of 139 t]
    generation_source_old_meaning[of 145 t] generation_source_base_roots generation_source_component_meanings[of t]
  by auto

interpretation generation_child_values: related_list_profile generation_source_system 149 150
  by (unfold_locales) (auto simp: generation_source_call)

interpretation generation_child_rows: related_list_profile generation_source_system 153 154
  by (unfold_locales) (auto simp: generation_source_call)

text \<open>
  Nine definitions have eleven ordinary clauses. Record and family checks
  preserve complete socket rows. Three anchored readings recover the locus,
  payload, and recorded cause. The recursive child row retains its socket,
  citation endpoint, actual destination use and address, and child value.
  Its value projection and the two sequence relations share those clauses.

  Core reports admit the expected complete value and compare all produced
  predecessor occurrences through the value program's bag identity. Source
  admission projects that report. A complete row report admits the parent
  source and traverses its entire predecessor family. No failed-call test,
  external truth callback, selected enumeration, or recursion bound appears
  in these schemas.
\<close>

end
