theory Factor_Base_Cause_Clauses
  imports Factor_Base_Cause_Base
begin

section \<open>Ordinary clauses link the actual declaration and its payload\<close>

definition base_admission_report_schema :: "(nat,nat,nat) factor_schema" where
  "base_admission_report_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,115,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)),
     (1,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 6)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
     (2,10,Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 5))}"

definition recorded_base_report_schema :: "(nat,nat,nat) factor_schema" where
  "recorded_base_report_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,151,Pattern_Pair data_x
       (generation_fields_pattern (Pattern_Variable 2) (Pattern_Variable 3)
         (Pattern_Pair data_y (Pattern_Payload [])) (Pattern_Variable 4))),
     (1,162,Pattern_Pair data_x (Pattern_Variable 5)),
     (2,183,Pattern_Variable 5),
     (3,185,Pattern_Pair (Pattern_Variable 5) data_y)}"

definition base_cause_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "base_cause_group_clauses d=
    (if d=185 then {(0,base_admission_report_schema)}
     else if d=186 then {(0,reader_projection_clause 0 1 0 185)}
     else if d=187 then {(0,recorded_base_report_schema)}
     else if d=188 then {(0,reader_projection_clause 0 1 0 187)}
     else {})"

definition base_cause_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "base_cause_definition_group=\<lparr>
    system_interfaces=(\<lambda>d. (d,data_x)) ` {185,186,187,188},
    system_clauses=(\<Union>d\<in>{185,186,187,188}.
      (\<lambda>(c,S). ((d,c),S)) ` base_cause_group_clauses d)\<rparr>"

lemma base_cause_group_definitions [simp]:
  "system_definitions base_cause_definition_group={185,186,187,188}"
  by (auto simp: base_cause_definition_group_def system_definitions_def rel_dom_def)

lemma base_cause_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces base_cause_definition_group \<longleftrightarrow>
    d\<in>{185,186,187,188} \<and> p=data_x"
  by (auto simp: base_cause_definition_group_def)

lemma base_cause_group_family [simp]:
  "((d,c),S)\<in>system_clauses base_cause_definition_group \<longleftrightarrow>
    d\<in>{185,186,187,188} \<and> (c,S)\<in>base_cause_group_clauses d"
  by (auto simp: base_cause_definition_group_def)

lemma base_cause_group_finite: "finite (base_cause_group_clauses d)"
  by (simp add: base_cause_group_clauses_def)

lemma base_cause_group_functional: "single_valued (base_cause_group_clauses d)"
  by (auto simp: base_cause_group_clauses_def single_valued_def)

lemmas base_cause_schema_defs = base_admission_report_schema_def
  recorded_base_report_schema_def reader_projection_clause_def

lemma base_cause_group_schema_formation:
  assumes "(c,S)\<in>base_cause_group_clauses d"
  shows "schema_formed S \<and> schema_material_premises S={} \<and>
    schema_dependencies S\<subseteq>system_definitions base_cause_components_system\<union>
      system_definitions base_cause_definition_group"
  using assms generation_scope_base_roots by (auto simp: base_cause_group_clauses_def base_cause_schema_defs
    schema_formed_def schema_dependencies_def single_valued_def rel_ran_def octets_formed_def split: if_splits)

lemma base_cause_group_source_formation:
  "schema_system_formed_over (system_definitions base_cause_components_system) base_cause_definition_group"
proof -
  have finite: "finite (system_interfaces base_cause_definition_group)"
    "finite (system_clauses base_cause_definition_group)"
    by (auto simp: base_cause_definition_group_def intro: base_cause_group_finite)
  have interfaces: "single_valued (system_interfaces base_cause_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses base_cause_definition_group)"
    using base_cause_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses base_cause_definition_group \<longrightarrow>
    d\<in>system_definitions base_cause_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions base_cause_components_system\<union>
      system_definitions base_cause_definition_group"
  proof (intro allI impI)
    fix d c S assume clause: "((d,c),S)\<in>system_clauses base_cause_definition_group"
    have members: "d\<in>system_definitions base_cause_definition_group \<and> (c,S)\<in>base_cause_group_clauses d"
      using clause by (simp only: base_cause_group_family base_cause_group_definitions)
    show "d\<in>system_definitions base_cause_definition_group \<and> schema_formed S \<and>
        schema_dependencies S\<subseteq>system_definitions base_cause_components_system\<union>system_definitions base_cause_definition_group"
      using members base_cause_group_schema_formation[OF conjunct2[OF members]] by blast
  qed
  show ?thesis using finite interfaces clauses schemas by (simp add: schema_system_formed_over_def)
qed

lemma base_cause_group_external_dependencies:
  "system_external_dependencies base_cause_definition_group={10,58,115,151,162,183}"
  by (simp add: system_external_dependencies_clauses base_cause_definition_group_def
    base_cause_group_clauses_def base_cause_schema_defs schema_dependencies_def rel_ran_image
    system_definitions_def rel_dom_image; auto)

definition base_cause_base_system :: "(nat,nat,nat,nat) schema_system" where
  "base_cause_base_system=rooted_system base_cause_components_system
    (system_external_dependencies base_cause_definition_group)"

lemma base_cause_base_formed [simp]: "schema_system_formed base_cause_base_system"
  unfolding base_cause_base_system_def by (rule rooted_system_formed[OF base_cause_components_formed])

lemma base_cause_base_definitions:
  "system_definitions base_cause_base_system=system_definition_closure base_cause_components_system {10,58,115,151,162,183}"
  unfolding base_cause_base_system_def base_cause_group_external_dependencies
  by (rule rooted_system_definitions[OF base_cause_components_formed]) (use generation_scope_base_roots in auto)

lemma base_cause_base_subdomain:
  "system_definitions base_cause_base_system\<subseteq>system_definitions base_cause_components_system"
  unfolding base_cause_base_system_def by (rule rooted_system_subdomain)

lemma base_cause_base_roots:
  "{10,58,115,151,162,183}\<subseteq>system_definitions base_cause_base_system"
  unfolding base_cause_base_system_def base_cause_group_external_dependencies
  by (rule rooted_system_roots[OF base_cause_components_formed]) (use generation_scope_base_roots in auto)

lemma base_cause_base_least:
  assumes "{10,58,115,151,162,183}\<subseteq>U" "system_dependency_closed base_cause_components_system U"
  shows "system_definitions base_cause_base_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: base_cause_base_definitions)

lemma base_cause_base_call:
  "schema_call_formed base_cause_base_system d t \<longleftrightarrow>
    d\<in>system_definitions base_cause_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies base_cause_definition_group" and d=d and t=t,
    OF base_cause_components_formed]
  by (simp only: base_cause_base_system_def rooted_system_def system_restriction_definitions
    base_cause_components_call; blast)

lemma base_cause_base_meaning:
  assumes "d\<in>system_definitions base_cause_base_system"
  shows "(d,t)\<in>positive_meaning base_cause_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning base_cause_components_system"
  using rooted_system_meaning[where roots="system_external_dependencies base_cause_definition_group" and d=d and t=t,
    OF base_cause_components_formed] assms
  by (simp only: base_cause_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma base_cause_base_agreement:
  "systems_agree_on base_cause_components_system base_cause_base_system
    (system_definitions base_cause_base_system)"
  unfolding base_cause_base_system_def by (rule rooted_system_agreement)

lemma base_cause_group_relative_formation:
  "schema_system_formed_over (system_definitions base_cause_base_system) base_cause_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies base_cause_definition_group) base_cause_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF base_cause_group_source_formation])
  have retained: "system_external_dependencies base_cause_definition_group\<subseteq>system_definitions base_cause_base_system"
    using base_cause_base_roots by (simp only: base_cause_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation base_cause_group: positive_definition_group base_cause_base_system base_cause_definition_group
proof (rule positive_definition_group.intro[OF base_cause_base_formed base_cause_group_relative_formation])
  have fresh: "system_definitions base_cause_components_system\<inter>system_definitions base_cause_definition_group={}"
    using base_cause_old_fresh by auto
  show "system_definitions base_cause_base_system\<inter>system_definitions base_cause_definition_group={}"
    using base_cause_base_subdomain fresh by blast
qed

definition base_cause_system :: "(nat,nat,nat,nat) schema_system" where
  "base_cause_system=system_union base_cause_base_system base_cause_definition_group"

lemma base_cause_system_formed [simp]: "schema_system_formed base_cause_system"
  using base_cause_group.formed by (simp only: base_cause_system_def)

lemma base_cause_definitions [simp]:
  "system_definitions base_cause_system=system_definitions base_cause_base_system\<union>{185,186,187,188}"
  by (simp add: base_cause_system_def)

lemma base_cause_call:
  "schema_call_formed base_cause_system d t \<longleftrightarrow>
    d\<in>system_definitions base_cause_system \<and> term_formed t"
  using base_cause_group.variable_calls[OF base_cause_base_call base_cause_group_interfaces, of d t]
  by (simp only: base_cause_system_def)

lemma base_cause_old_meaning:
  assumes "d\<in>system_definitions base_cause_base_system"
  shows "(d,t)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning base_cause_components_system"
  using base_cause_group.old_meaning[OF assms, of t] base_cause_base_meaning[OF assms, of t]
  by (simp only: base_cause_system_def; blast)

lemma base_cause_clause:
  assumes "d\<in>{185,186,187,188}"
  shows "((d,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow>
    (c,S)\<in>base_cause_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses base_cause_definition_group"
    using base_cause_group.group_agreement assms
    by (simp only: base_cause_system_def systems_agree_on_def base_cause_group_definitions; blast)
  show ?thesis using same assms by (simp only: base_cause_group_family; blast)
qed

lemma base_cause_clauses [simp]:
  "((185,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow> (c,S)\<in>{(0,base_admission_report_schema)}"
  "((186,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow> (c,S)\<in>{(0,reader_projection_clause 0 1 0 185)}"
  "((187,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow> (c,S)\<in>{(0,recorded_base_report_schema)}"
  "((188,c),S)\<in>system_clauses base_cause_system \<longleftrightarrow> (c,S)\<in>{(0,reader_projection_clause 0 1 0 187)}"
  using base_cause_clause by (auto simp: base_cause_group_clauses_def)

lemma base_cause_components:
  "(10,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(58,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(115,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (115,t)\<in>positive_meaning native_positive_admission_system"
  "(151,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (151,t)\<in>positive_meaning generation_source_system"
  "(162,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (162,t)\<in>positive_meaning generation_scope_system"
  "(183,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (183,t)\<in>positive_meaning judgment_retention_system"
  using base_cause_old_meaning[of 10 t] base_cause_old_meaning[of 58 t]
    base_cause_old_meaning[of 115 t] base_cause_old_meaning[of 151 t]
    base_cause_old_meaning[of 162 t] base_cause_old_meaning[of 183 t]
    base_cause_base_roots base_cause_component_meanings[of t] by auto

text \<open>
  Four definitions have four ordinary clauses. A base report requires the
  actual positive judgment and projects the literal in its actual application.
  A recorded report links that declaration to the generation's actual quoted
  scope, requires its least environment, and compares the declared payload
  with the actual payload field. The two source admissions use the generic
  projection clause. These source admissions introduce no additional payload,
  scope, or proof field.

  The base is the least complete-definition closure of six actual external
  callees. Existing meanings are preserved before these clauses are interpreted;
  every new premise is an ordinary call in the resulting finite program.
\<close>

end
