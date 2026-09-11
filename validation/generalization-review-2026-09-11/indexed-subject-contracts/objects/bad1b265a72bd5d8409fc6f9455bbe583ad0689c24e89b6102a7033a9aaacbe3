theory Factor_Generation_Scope_Clauses
  imports Factor_Generation_Scope_Base
begin

section \<open>The complete core reading supplies the actual cause or payload\<close>

definition generation_recorded_scope_report_schema :: "(nat,nat,nat) factor_schema" where
  "generation_recorded_scope_report_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,151,Pattern_Pair data_x
      (generation_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3) (Pattern_Variable 4)
        (Pattern_Pair (Pattern_Variable 5) (Pattern_Payload [])))),
      (1,160,Pattern_Pair (Pattern_Variable 5) data_y)}"

definition generation_payload_scope_report_schema :: "(nat,nat,nat) factor_schema" where
  "generation_payload_scope_report_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,151,Pattern_Pair data_x
      (generation_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3)
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Payload [])) (Pattern_Variable 5))),
      (1,165,Pattern_Pair (Pattern_Variable 4) data_y)}"

definition generation_scope_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "generation_scope_group_clauses d=
    (if d=162 then {(0,generation_recorded_scope_report_schema)}
     else if d=163 then {(0,reader_projection_clause 0 1 0 162)}
     else if d=167 then {(0,generation_payload_scope_report_schema)}
     else if d=168 then {(0,reader_projection_clause 0 1 0 167)}
     else {})"

definition generation_scope_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "generation_scope_definition_group=\<lparr>
    system_interfaces=(\<lambda>d. (d,data_x)) ` {162,163,167,168},
    system_clauses=(\<Union>d\<in>{162,163,167,168}.
      (\<lambda>(c,S). ((d,c),S)) ` generation_scope_group_clauses d)\<rparr>"

lemma generation_scope_group_definitions [simp]:
  "system_definitions generation_scope_definition_group={162,163,167,168}"
  by (auto simp: generation_scope_definition_group_def system_definitions_def rel_dom_def)

lemma generation_scope_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces generation_scope_definition_group \<longleftrightarrow>
    d\<in>{162,163,167,168} \<and> p=data_x"
  by (auto simp: generation_scope_definition_group_def)

lemma generation_scope_group_family [simp]:
  "((d,c),S)\<in>system_clauses generation_scope_definition_group \<longleftrightarrow>
    d\<in>{162,163,167,168} \<and> (c,S)\<in>generation_scope_group_clauses d"
  by (auto simp: generation_scope_definition_group_def)

lemma generation_scope_group_finite: "finite (generation_scope_group_clauses d)"
  by (simp add: generation_scope_group_clauses_def)

lemma generation_scope_group_functional: "single_valued (generation_scope_group_clauses d)"
  by (auto simp: generation_scope_group_clauses_def single_valued_def)

lemmas generation_scope_schema_defs = generation_recorded_scope_report_schema_def
  generation_payload_scope_report_schema_def reader_projection_clause_def

lemma generation_scope_group_schema_formation:
  assumes "(c,S)\<in>generation_scope_group_clauses d"
  shows "schema_formed S \<and> schema_material_premises S={} \<and>
    schema_dependencies S\<subseteq>system_definitions generation_scope_components_system\<union>
      system_definitions generation_scope_definition_group"
  using assms by (auto simp: generation_scope_group_clauses_def generation_scope_schema_defs
    schema_formed_def schema_dependencies_def single_valued_def rel_ran_def octets_formed_def split: if_splits)

lemma generation_scope_group_source_formation:
  "schema_system_formed_over (system_definitions generation_scope_components_system) generation_scope_definition_group"
proof -
  have finite: "finite (system_interfaces generation_scope_definition_group)"
    "finite (system_clauses generation_scope_definition_group)"
    by (auto simp: generation_scope_definition_group_def intro: generation_scope_group_finite)
  have interfaces: "single_valued (system_interfaces generation_scope_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses generation_scope_definition_group)"
    using generation_scope_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses generation_scope_definition_group \<longrightarrow>
    d\<in>system_definitions generation_scope_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions generation_scope_components_system\<union>
      system_definitions generation_scope_definition_group"
  proof (intro allI impI)
    fix d c S assume clause: "((d,c),S)\<in>system_clauses generation_scope_definition_group"
    have members: "d\<in>system_definitions generation_scope_definition_group \<and> (c,S)\<in>generation_scope_group_clauses d"
      using clause by (simp only: generation_scope_group_family generation_scope_group_definitions)
    show "d\<in>system_definitions generation_scope_definition_group \<and> schema_formed S \<and>
        schema_dependencies S\<subseteq>system_definitions generation_scope_components_system\<union>system_definitions generation_scope_definition_group"
      using members generation_scope_group_schema_formation[OF conjunct2[OF members]] by blast
  qed
  show ?thesis using finite interfaces clauses schemas by (simp add: schema_system_formed_over_def)
qed

lemma generation_scope_group_external_dependencies:
  "system_external_dependencies generation_scope_definition_group={151,160,165}"
  by (simp add: system_external_dependencies_clauses generation_scope_definition_group_def
    generation_scope_group_clauses_def generation_scope_schema_defs schema_dependencies_def rel_ran_image
    system_definitions_def rel_dom_image; auto)

definition generation_scope_base_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_scope_base_system=rooted_system generation_scope_components_system
    (system_external_dependencies generation_scope_definition_group)"

lemma generation_scope_base_formed [simp]: "schema_system_formed generation_scope_base_system"
  unfolding generation_scope_base_system_def by (rule rooted_system_formed[OF generation_scope_components_formed])

lemma generation_scope_base_definitions:
  "system_definitions generation_scope_base_system=system_definition_closure generation_scope_components_system {151,160,165}"
  unfolding generation_scope_base_system_def generation_scope_group_external_dependencies
  by (rule rooted_system_definitions[OF generation_scope_components_formed]) auto

lemma generation_scope_base_subdomain:
  "system_definitions generation_scope_base_system\<subseteq>system_definitions generation_scope_components_system"
  unfolding generation_scope_base_system_def by (rule rooted_system_subdomain)

lemma generation_scope_base_roots:
  "{151,160,165}\<subseteq>system_definitions generation_scope_base_system"
  unfolding generation_scope_base_system_def generation_scope_group_external_dependencies
  by (rule rooted_system_roots[OF generation_scope_components_formed]) auto

lemma generation_scope_base_least:
  assumes "{151,160,165}\<subseteq>U" "system_dependency_closed generation_scope_components_system U"
  shows "system_definitions generation_scope_base_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: generation_scope_base_definitions)

lemma generation_scope_base_call:
  "schema_call_formed generation_scope_base_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_scope_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies generation_scope_definition_group" and d=d and t=t,
    OF generation_scope_components_formed]
  by (simp only: generation_scope_base_system_def rooted_system_def system_restriction_definitions
    generation_scope_components_call; blast)

lemma generation_scope_base_meaning:
  assumes "d\<in>system_definitions generation_scope_base_system"
  shows "(d,t)\<in>positive_meaning generation_scope_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_scope_components_system"
  using rooted_system_meaning[where roots="system_external_dependencies generation_scope_definition_group" and d=d and t=t,
    OF generation_scope_components_formed] assms
  by (simp only: generation_scope_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma generation_scope_base_agreement:
  "systems_agree_on generation_scope_components_system generation_scope_base_system
    (system_definitions generation_scope_base_system)"
  unfolding generation_scope_base_system_def by (rule rooted_system_agreement)

lemma generation_scope_group_relative_formation:
  "schema_system_formed_over (system_definitions generation_scope_base_system) generation_scope_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies generation_scope_definition_group) generation_scope_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF generation_scope_group_source_formation])
  have retained: "system_external_dependencies generation_scope_definition_group\<subseteq>system_definitions generation_scope_base_system"
    using generation_scope_base_roots by (simp only: generation_scope_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation generation_scope_group: positive_definition_group generation_scope_base_system generation_scope_definition_group
proof (rule positive_definition_group.intro[OF generation_scope_base_formed generation_scope_group_relative_formation])
  let ?N="{162,163,167,168}"
  let ?G="{147,148,149,150,151,152,153,154,155}"
  have source_bound: "system_definitions generation_source_system\<subseteq>
      system_definitions generation_source_components_system\<union>?G"
    using generation_source_base_subdomain unfolding generation_source_definitions by blast
  have source_separate: "?N\<inter>(system_definitions generation_source_components_system\<union>?G)={}"
    using generation_target_subdomain by (auto dest: subsetD)
  have scope_separate: "?N\<inter>(system_definitions scope_reading_components_system\<union>{160,161,164,165,166})={}"
    using context_base_subdomain by (auto dest: subsetD)
  have fresh: "system_definitions generation_scope_components_system\<inter>system_definitions generation_scope_definition_group={}"
    using source_bound scope_programs_boundary source_separate scope_separate
    unfolding generation_scope_components_definitions generation_scope_group_definitions by blast
  show "system_definitions generation_scope_base_system\<inter>system_definitions generation_scope_definition_group={}"
    using generation_scope_base_subdomain fresh by blast
qed

definition generation_scope_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_scope_system=system_union generation_scope_base_system generation_scope_definition_group"

lemma generation_scope_system_formed [simp]: "schema_system_formed generation_scope_system"
  using generation_scope_group.formed by (simp only: generation_scope_system_def)

lemma generation_scope_definitions [simp]:
  "system_definitions generation_scope_system=system_definitions generation_scope_base_system\<union>{162,163,167,168}"
  by (simp add: generation_scope_system_def)

lemma generation_scope_call:
  "schema_call_formed generation_scope_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_scope_system \<and> term_formed t"
  using generation_scope_group.variable_calls[OF generation_scope_base_call generation_scope_group_interfaces, of d t]
  by (simp only: generation_scope_system_def)

lemma generation_scope_old_meaning:
  assumes "d\<in>system_definitions generation_scope_base_system"
  shows "(d,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning generation_scope_components_system"
  using generation_scope_group.old_meaning[OF assms, of t] generation_scope_base_meaning[OF assms, of t]
  by (simp only: generation_scope_system_def; blast)

lemma generation_scope_clause:
  assumes "d\<in>{162,163,167,168}"
  shows "((d,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow>
    (c,S)\<in>generation_scope_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses generation_scope_definition_group"
    using generation_scope_group.group_agreement assms
    by (simp only: generation_scope_system_def systems_agree_on_def generation_scope_group_definitions; blast)
  show ?thesis using same assms by (simp only: generation_scope_group_family; blast)
qed

lemma generation_scope_clauses [simp]:
  "((162,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow> (c,S)\<in>{(0,generation_recorded_scope_report_schema)}"
  "((163,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow> (c,S)\<in>{(0,reader_projection_clause 0 1 0 162)}"
  "((167,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow> (c,S)\<in>{(0,generation_payload_scope_report_schema)}"
  "((168,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow> (c,S)\<in>{(0,reader_projection_clause 0 1 0 167)}"
  using generation_scope_clause by (auto simp: generation_scope_group_clauses_def)

lemma generation_scope_components:
  "(151,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (151,t)\<in>positive_meaning generation_source_system"
  "(160,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (160,t)\<in>positive_meaning judgment_scope_reading_system"
  "(165,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (165,t)\<in>positive_meaning program_scope_reports_system"
  using generation_scope_old_meaning[of 151 t] generation_scope_old_meaning[of 160 t]
    generation_scope_old_meaning[of 165 t] generation_scope_base_roots generation_scope_component_meanings[of t] by auto

text \<open>
  The two report clauses first read the complete core from its actual source.
  Their second premise reads the complete whole artifact selected by the
  cause or payload field. The corresponding source admissions use the same
  generic projection clause. All four clauses are ordinary positive schemas.

  Their actual external dependencies are the complete source report and the
  two independently owned scope reports. The base is exactly the least closed
  boundary generated by those callees. The public and private terms occur in
  actual premise calls; no external truth test or stored duplicate scope is
  introduced.
\<close>

end
