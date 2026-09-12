theory Factor_Construction_Cause_Clauses
  imports Factor_Construction_Cause_Components
begin

section \<open>Ordinary clauses link the actual declaration and its payload\<close>

definition construction_profile_report_schema :: "(nat,nat,nat) factor_schema" where
  "construction_profile_report_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,115,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)),
     (1,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 6)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
     (2,264,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Variable 6)),
     (3,261,Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 5))}"

definition recorded_construction_report_schema :: "(nat,nat,nat) factor_schema" where
  "recorded_construction_report_schema=data_rule
    (Pattern_Pair data_x (foldr Pattern_Pair [data_y,data_z,data_w,Pattern_Variable 4,Pattern_Variable 5]
      (Pattern_Target (Whole_Artifact empty_artifact))))
    {(0,151,Pattern_Pair data_x
       (generation_fields_pattern (Pattern_Variable 6) (Pattern_Variable 7)
         (Pattern_Pair (Pattern_Variable 8) (Pattern_Payload [])) (Pattern_Variable 9))),
     (1,162,Pattern_Pair data_x (Pattern_Variable 10)),
     (2,183,Pattern_Variable 10),
     (3,265,Pattern_Pair (Pattern_Variable 10)
       (foldr Pattern_Pair [data_y,data_z,data_w,Pattern_Variable 4,Pattern_Variable 5]
         (Pattern_Target (Whole_Artifact empty_artifact)))),
     (4,10,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8))}"

definition construction_cause_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "construction_cause_group_clauses d=
    (if d=265 then {(0,construction_profile_report_schema)}
     else if d=266 then {(0,reader_projection_clause 0 1 0 265)}
     else if d=267 then {(0,recorded_construction_report_schema)}
     else if d=268 then {(0,reader_projection_clause 0 1 0 267)}
     else {})"

definition construction_cause_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "construction_cause_definition_group=\<lparr>
    system_interfaces=(\<lambda>d. (d,data_x)) ` {265,266,267,268},
    system_clauses=(\<Union>d\<in>{265,266,267,268}.
      (\<lambda>(cl,S). ((d,cl),S)) ` construction_cause_group_clauses d)\<rparr>"

lemma construction_cause_group_definitions [simp]:
  "system_definitions construction_cause_definition_group={265,266,267,268}"
  by (auto simp: construction_cause_definition_group_def system_definitions_def rel_dom_def)

lemma construction_cause_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces construction_cause_definition_group \<longleftrightarrow>
    d\<in>{265,266,267,268} \<and> p=data_x"
  by (auto simp: construction_cause_definition_group_def)

lemma construction_cause_group_family [simp]:
  "((d,cl),S)\<in>system_clauses construction_cause_definition_group \<longleftrightarrow>
    d\<in>{265,266,267,268} \<and> (cl,S)\<in>construction_cause_group_clauses d"
  by (auto simp: construction_cause_definition_group_def)

lemma construction_cause_group_finite: "finite (construction_cause_group_clauses d)"
  by (simp add: construction_cause_group_clauses_def)

lemma construction_cause_group_functional: "single_valued (construction_cause_group_clauses d)"
  by (auto simp: construction_cause_group_clauses_def single_valued_def)

lemmas construction_cause_schema_defs = construction_profile_report_schema_def
  recorded_construction_report_schema_def reader_projection_clause_def

definition construction_cause_base_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "construction_cause_base_system c k=rooted_system (construction_cause_components_system c k)
    (system_external_dependencies construction_cause_definition_group)"

definition construction_cause_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "construction_cause_system c k=system_union (construction_cause_base_system c k) construction_cause_definition_group"

context related_test_admission
begin

lemma construction_cause_group_schema_formation:
  assumes "(cl,S)\<in>construction_cause_group_clauses d"
  shows "schema_formed S \<and> schema_material_premises S={} \<and>
    schema_dependencies S\<subseteq>system_definitions (construction_cause_components_system c k)\<union>
      system_definitions construction_cause_definition_group"
  using assms generation_scope_base_roots by (auto simp: construction_cause_group_clauses_def construction_cause_schema_defs
    construction_cause_components_definitions schema_formed_def schema_dependencies_def single_valued_def rel_ran_def octets_formed_def split: if_splits)

lemma construction_cause_group_source_formation:
  "schema_system_formed_over (system_definitions (construction_cause_components_system c k)) construction_cause_definition_group"
proof -
  have schemas: "schema_formed S \<and>
      schema_dependencies S\<subseteq>system_definitions (construction_cause_components_system c k)\<union>{265,266,267,268}"
    if "d\<in>{265,266,267,268}" "(cl,S)\<in>construction_cause_group_clauses d" for d cl S
    using construction_cause_group_schema_formation[OF that(2)] by simp
  show ?thesis
    by (rule schema_system_formed_over_families[where D="{265,266,267,268}" and
        p="\<lambda>_. data_x" and C=construction_cause_group_clauses, OF _ _ _ _ _ _ schemas])
      (auto simp: construction_cause_definition_group_def
        intro: construction_cause_group_finite construction_cause_group_functional)
qed

lemma construction_cause_group_external_dependencies:
  "system_external_dependencies construction_cause_definition_group={10,58,115,151,162,183,261,264}"
  by (simp add: system_external_dependencies_clauses construction_cause_definition_group_def
    construction_cause_group_clauses_def construction_cause_schema_defs schema_dependencies_def rel_ran_image
    system_definitions_def rel_dom_image; auto)

lemma construction_cause_base_formed [simp]: "schema_system_formed (construction_cause_base_system c k)"
  unfolding construction_cause_base_system_def by (rule rooted_system_formed[OF construction_cause_components_formed])

lemma construction_cause_base_definitions:
  "system_definitions (construction_cause_base_system c k)=system_definition_closure (construction_cause_components_system c k) {10,58,115,151,162,183,261,264}"
  unfolding construction_cause_base_system_def construction_cause_group_external_dependencies
  by (rule rooted_system_definitions[OF construction_cause_components_formed]) (use generation_scope_base_roots in \<open>auto simp: construction_cause_components_definitions\<close>)

lemma construction_cause_base_subdomain:
  "system_definitions (construction_cause_base_system c k)\<subseteq>system_definitions (construction_cause_components_system c k)"
  unfolding construction_cause_base_system_def by (rule rooted_system_subdomain)

lemma construction_cause_base_roots:
  "{10,58,115,151,162,183,261,264}\<subseteq>system_definitions (construction_cause_base_system c k)"
  unfolding construction_cause_base_system_def construction_cause_group_external_dependencies
  by (rule rooted_system_roots[OF construction_cause_components_formed]) (use generation_scope_base_roots in \<open>auto simp: construction_cause_components_definitions\<close>)

lemma construction_cause_base_least:
  assumes "{10,58,115,151,162,183,261,264}\<subseteq>U" "system_dependency_closed (construction_cause_components_system c k) U"
  shows "system_definitions (construction_cause_base_system c k)\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: construction_cause_base_definitions)

lemma construction_cause_base_call:
  "schema_call_formed (construction_cause_base_system c k) d t \<longleftrightarrow>
    d\<in>system_definitions (construction_cause_base_system c k) \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies construction_cause_definition_group" and d=d and t=t,
    OF construction_cause_components_formed]
  by (simp only: construction_cause_base_system_def rooted_system_def system_restriction_definitions
    construction_cause_components_call; blast)

lemma construction_cause_base_meaning:
  assumes "d\<in>system_definitions (construction_cause_base_system c k)"
  shows "(d,t)\<in>positive_meaning (construction_cause_base_system c k) \<longleftrightarrow>
    (d,t)\<in>positive_meaning (construction_cause_components_system c k)"
  using rooted_system_meaning[where roots="system_external_dependencies construction_cause_definition_group" and d=d and t=t,
    OF construction_cause_components_formed] assms
  by (simp only: construction_cause_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma construction_cause_base_agreement:
  "systems_agree_on (construction_cause_components_system c k) (construction_cause_base_system c k)
    (system_definitions (construction_cause_base_system c k))"
  unfolding construction_cause_base_system_def by (rule rooted_system_agreement)

lemma construction_cause_group_relative_formation:
  "schema_system_formed_over (system_definitions (construction_cause_base_system c k)) construction_cause_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies construction_cause_definition_group) construction_cause_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF construction_cause_group_source_formation])
  have retained: "system_external_dependencies construction_cause_definition_group\<subseteq>system_definitions (construction_cause_base_system c k)"
    using construction_cause_base_roots by (simp only: construction_cause_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation construction_cause_group: positive_definition_group "construction_cause_base_system c k" construction_cause_definition_group
proof (rule positive_definition_group.intro[OF construction_cause_base_formed construction_cause_group_relative_formation])
  have fresh: "system_definitions (construction_cause_components_system c k)\<inter>system_definitions construction_cause_definition_group={}"
    using construction_cause_components_bound by auto
  show "system_definitions (construction_cause_base_system c k)\<inter>system_definitions construction_cause_definition_group={}"
    using construction_cause_base_subdomain fresh by blast
qed

lemma construction_cause_system_formed [simp]: "schema_system_formed (construction_cause_system c k)"
  using construction_cause_group.formed by (simp only: construction_cause_system_def)

lemma construction_cause_definitions [simp]:
  "system_definitions (construction_cause_system c k)=system_definitions (construction_cause_base_system c k)\<union>{265,266,267,268}"
  by (simp add: construction_cause_system_def)

lemma construction_cause_call:
  "schema_call_formed (construction_cause_system c k) d t \<longleftrightarrow>
    d\<in>system_definitions (construction_cause_system c k) \<and> term_formed t"
  using construction_cause_group.variable_calls[OF construction_cause_base_call construction_cause_group_interfaces, of d t]
  by (simp only: construction_cause_system_def)

lemma construction_cause_old_meaning:
  assumes "d\<in>system_definitions (construction_cause_base_system c k)"
  shows "(d,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (d,t)\<in>positive_meaning (construction_cause_components_system c k)"
  using construction_cause_group.old_meaning[OF assms, of t] construction_cause_base_meaning[OF assms, of t]
  by (simp only: construction_cause_system_def; blast)

lemma construction_cause_clause:
  assumes "d\<in>{265,266,267,268}"
  shows "((d,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow>
    (cl,S)\<in>construction_cause_group_clauses d"
proof -
  have same: "((d,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow>
      ((d,cl),S)\<in>system_clauses construction_cause_definition_group"
    using construction_cause_group.group_agreement assms
    by (simp only: construction_cause_system_def systems_agree_on_def construction_cause_group_definitions; blast)
  show ?thesis using same assms by (simp only: construction_cause_group_family; blast)
qed

lemma construction_cause_clauses [simp]:
  "((265,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow> (cl,S)\<in>{(0,construction_profile_report_schema)}"
  "((266,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow> (cl,S)\<in>{(0,reader_projection_clause 0 1 0 265)}"
  "((267,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow> (cl,S)\<in>{(0,recorded_construction_report_schema)}"
  "((268,cl),S)\<in>system_clauses (construction_cause_system c k) \<longleftrightarrow> (cl,S)\<in>{(0,reader_projection_clause 0 1 0 267)}"
  using construction_cause_clause by (auto simp: construction_cause_group_clauses_def)

lemma construction_cause_components:
  "(10,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (10,t)\<in>positive_meaning artifact_projection_system"
  "(58,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(115,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (115,t)\<in>positive_meaning native_positive_admission_system"
  "(151,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (151,t)\<in>positive_meaning generation_source_system"
  "(162,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (162,t)\<in>positive_meaning generation_scope_system"
  "(183,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (183,t)\<in>positive_meaning judgment_retention_system"
  "(261,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (261,t)\<in>positive_meaning construction_comparison_system"
  "(264,t)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow> (264,t)\<in>positive_meaning (related_test_admission_system c k)"
  using construction_cause_old_meaning[of 10 t] construction_cause_old_meaning[of 58 t]
    construction_cause_old_meaning[of 115 t] construction_cause_old_meaning[of 151 t]
    construction_cause_old_meaning[of 162 t] construction_cause_old_meaning[of 183 t]
    construction_cause_old_meaning[of 261 t] construction_cause_old_meaning[of 264 t]
    construction_cause_base_roots construction_cause_component_meanings[of t] by auto

end

text \<open>
  Four variable-interface entries have four complete ordinary clauses. The
  profile report joins actual positive truth, the actual application, the
  configured whole-definition permission check, and complete account comparison.
  The recorded report additionally reads the actual payload and quoted scope,
  requires the least judgment environment, and checks that payload against
  the same account's output. The two source entries use ordinary projection.

  The base is the least complete-definition closure of eight actual external
  callees. All their meanings survive before the new clauses are interpreted.
  Configuration consists only of the reference environment and entry already
  read by the existing permission checker; no external truth parameter is added.
\<close>

end
