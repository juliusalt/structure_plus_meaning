theory Factor_Judgment_Retention_Clauses
  imports Factor_Judgment_Retention_Base
begin

section \<open>The complete shared context supplies both actual readings\<close>

definition judgment_source_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_source_schema=data_rule
    (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))
    {(0,80,source_root_pattern data_x data_y data_z),
     (1,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 5)
       (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8))}"

definition judgment_program_slot_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_program_slot_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,178,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)),
     (1,119,Pattern_Pair (package_context_pattern data_x data_y data_z) (Pattern_Variable 5))}"

definition judgment_application_slot_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_application_slot_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))
      (Pattern_Pair data_w (Pattern_Variable 5)))
    {(0,178,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)),
     (1,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 6)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
     (2,5,Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)))}"

definition judgment_required_root_schema :: "bool \<Rightarrow> (nat,nat,nat) factor_schema" where
  "judgment_required_root_schema application=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))
      (if application then data_w else data_y))
    {(0,178,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))}"

definition judgment_required_definition_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_required_definition_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,178,judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)),
     (1,83,package_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)))}"

definition judgment_required_target_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_required_target_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,179,Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))
       (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))),
     (1,38,binding_lookup_pattern data_x (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 5))}"

definition judgment_closed_source_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_closed_source_schema=data_rule
    (judgment_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5))
    {(0,178,judgment_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5)),
     (1,51,Pattern_Pair data_x (Pattern_Variable 6)),
     (2,51,Pattern_Pair data_y (Pattern_Variable 7)),
     (3,181,Pattern_Pair
       (judgment_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5))
       (Pattern_Variable 6)),
     (4,182,Pattern_Pair
       (judgment_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5))
       (Pattern_Variable 7))}"

definition judgment_retention_report_schema :: "(nat,nat,nat) factor_schema" where
  "judgment_retention_report_schema=data_rule
    (Pattern_Pair (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,183,judgment_context_pattern (Pattern_Variable 5) data_y data_z data_w (Pattern_Variable 4)),
     (1,113,Pattern_Pair (Pattern_Variable 5) data_x)}"

definition judgment_retention_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "judgment_retention_group_clauses d=
    (if d=178 then {(0,judgment_source_schema)}
     else if d=179 then {(0,judgment_program_slot_schema),(1,judgment_application_slot_schema)}
     else if d=180 then {(0,judgment_required_root_schema False),(1,judgment_required_root_schema True),
       (2,judgment_required_definition_schema),(3,judgment_required_target_schema)}
     else if d=181 then context_list_clauses 180 181
     else if d=182 then context_list_clauses 179 182
     else if d=183 then {(0,judgment_closed_source_schema)}
     else if d=184 then {(0,judgment_retention_report_schema)}
     else {})"

definition judgment_retention_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "judgment_retention_definition_group=\<lparr>
    system_interfaces=image (\<lambda>d. (d,data_x)) {178,179,180,181,182,183,184},
    system_clauses=(\<Union>d\<in>{178,179,180,181,182,183,184}.
      image (\<lambda>(c,S). ((d,c),S)) (judgment_retention_group_clauses d))\<rparr>"

lemma judgment_retention_group_definitions [simp]:
  "system_definitions judgment_retention_definition_group={178,179,180,181,182,183,184}"
  by (auto simp: judgment_retention_definition_group_def system_definitions_def rel_dom_def)

lemma judgment_retention_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces judgment_retention_definition_group \<longleftrightarrow>
    d\<in>{178,179,180,181,182,183,184} \<and> p=data_x"
  by (auto simp: judgment_retention_definition_group_def)

lemma judgment_retention_group_family [simp]:
  "((d,c),S)\<in>system_clauses judgment_retention_definition_group \<longleftrightarrow>
    d\<in>{178,179,180,181,182,183,184} \<and> (c,S)\<in>judgment_retention_group_clauses d"
  by (auto simp: judgment_retention_definition_group_def)

lemma judgment_retention_group_finite: "finite (judgment_retention_group_clauses d)"
  by (simp add: judgment_retention_group_clauses_def context_list_clauses_def)

lemma judgment_retention_group_functional: "single_valued (judgment_retention_group_clauses d)"
  by (auto simp: judgment_retention_group_clauses_def context_list_clauses_def single_valued_def)

lemmas judgment_retention_schema_defs = judgment_source_schema_def judgment_program_slot_schema_def
  judgment_application_slot_schema_def judgment_required_root_schema_def judgment_required_definition_schema_def
  judgment_required_target_schema_def judgment_closed_source_schema_def judgment_retention_report_schema_def
  context_list_nil_schema_def context_list_step_schema_def

lemma judgment_retention_group_ordinary:
  assumes "(c,S)\<in>judgment_retention_group_clauses d"
  shows "schema_material_premises S={}"
  using assms by (auto simp: judgment_retention_group_clauses_def context_list_clauses_def
    judgment_retention_schema_defs split: if_splits)

lemma judgment_retention_group_schema_formation:
  assumes "(c,S)\<in>judgment_retention_group_clauses d"
  shows "schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions package_slot_reading_system\<union>
      system_definitions judgment_retention_definition_group"
  using assms by (auto simp: judgment_retention_group_clauses_def context_list_clauses_def judgment_retention_schema_defs
    schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_image octets_formed_def split: if_splits)

lemma judgment_retention_group_source_formation:
  "schema_system_formed_over (system_definitions package_slot_reading_system) judgment_retention_definition_group"
proof -
  have finite: "finite (system_interfaces judgment_retention_definition_group)"
    "finite (system_clauses judgment_retention_definition_group)"
    by (simp_all add: judgment_retention_definition_group_def judgment_retention_group_finite)
  have interfaces: "single_valued (system_interfaces judgment_retention_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses judgment_retention_definition_group)"
    using judgment_retention_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses judgment_retention_definition_group \<longrightarrow>
    d\<in>system_definitions judgment_retention_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions package_slot_reading_system\<union>
      system_definitions judgment_retention_definition_group"
  proof (intro allI impI)
    fix d c S assume clause: "((d,c),S)\<in>system_clauses judgment_retention_definition_group"
    have members: "d\<in>system_definitions judgment_retention_definition_group \<and> (c,S)\<in>judgment_retention_group_clauses d"
      using clause by (simp only: judgment_retention_group_family judgment_retention_group_definitions)
    show "d\<in>system_definitions judgment_retention_definition_group \<and> schema_formed S \<and>
        schema_dependencies S\<subseteq>system_definitions package_slot_reading_system\<union>system_definitions judgment_retention_definition_group"
      using members judgment_retention_group_schema_formation[OF conjunct2[OF members]] by blast
  qed
  show ?thesis using finite interfaces clauses schemas by (simp add: schema_system_formed_over_def)
qed

lemma judgment_retention_group_external_dependencies:
  "system_external_dependencies judgment_retention_definition_group={5,38,51,58,80,83,113,119}"
  by (simp add: system_external_dependencies_clauses judgment_retention_definition_group_def
    judgment_retention_group_clauses_def context_list_clauses_def judgment_retention_schema_defs
    schema_dependencies_def rel_ran_image system_definitions_def rel_dom_image; auto)

definition judgment_retention_base_system :: "(nat,nat,nat,nat) schema_system" where
  "judgment_retention_base_system=rooted_system package_slot_reading_system
    (system_external_dependencies judgment_retention_definition_group)"

lemma judgment_retention_base_formed [simp]: "schema_system_formed judgment_retention_base_system"
  unfolding judgment_retention_base_system_def by (rule rooted_system_formed[OF package_slot_reading_system_formed])

lemma judgment_retention_base_definitions:
  "system_definitions judgment_retention_base_system=
    system_definition_closure package_slot_reading_system {5,38,51,58,80,83,113,119}"
  unfolding judgment_retention_base_system_def judgment_retention_group_external_dependencies
  by (rule rooted_system_definitions[OF package_slot_reading_system_formed]) auto

lemma judgment_retention_base_subdomain:
  "system_definitions judgment_retention_base_system\<subseteq>system_definitions package_slot_reading_system"
  unfolding judgment_retention_base_system_def by (rule rooted_system_subdomain)

lemma judgment_retention_base_roots:
  "{5,38,51,58,80,83,113,119}\<subseteq>system_definitions judgment_retention_base_system"
  unfolding judgment_retention_base_system_def judgment_retention_group_external_dependencies
  by (rule rooted_system_roots[OF package_slot_reading_system_formed]) auto

lemma judgment_retention_base_least:
  assumes "{5,38,51,58,80,83,113,119}\<subseteq>U" "system_dependency_closed package_slot_reading_system U"
  shows "system_definitions judgment_retention_base_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: judgment_retention_base_definitions)

lemma judgment_retention_base_call:
  "schema_call_formed judgment_retention_base_system d t \<longleftrightarrow>
    d\<in>system_definitions judgment_retention_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies judgment_retention_definition_group" and d=d and t=t,
    OF package_slot_reading_system_formed]
  by (simp only: judgment_retention_base_system_def rooted_system_def system_restriction_definitions
    package_slot_reading_call; blast)

lemma judgment_retention_base_meaning:
  assumes "d\<in>system_definitions judgment_retention_base_system"
  shows "(d,t)\<in>positive_meaning judgment_retention_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_slot_reading_system"
  using rooted_system_meaning[where roots="system_external_dependencies judgment_retention_definition_group" and d=d and t=t,
    OF package_slot_reading_system_formed] assms
  by (simp only: judgment_retention_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma judgment_retention_base_agreement:
  "systems_agree_on package_slot_reading_system judgment_retention_base_system
    (system_definitions judgment_retention_base_system)"
  unfolding judgment_retention_base_system_def by (rule rooted_system_agreement)

lemma judgment_retention_group_relative_formation:
  "schema_system_formed_over (system_definitions judgment_retention_base_system) judgment_retention_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies judgment_retention_definition_group)
      judgment_retention_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF judgment_retention_group_source_formation])
  have retained: "system_external_dependencies judgment_retention_definition_group\<subseteq>
      system_definitions judgment_retention_base_system"
    using judgment_retention_base_roots by (simp only: judgment_retention_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation judgment_retention_group:
  positive_definition_group judgment_retention_base_system judgment_retention_definition_group
proof (rule positive_definition_group.intro[OF judgment_retention_base_formed judgment_retention_group_relative_formation])
  have fresh: "system_definitions package_slot_reading_system\<inter>system_definitions judgment_retention_definition_group={}"
    by auto
  show "system_definitions judgment_retention_base_system\<inter>system_definitions judgment_retention_definition_group={}"
    using judgment_retention_base_subdomain fresh by blast
qed

definition judgment_retention_system :: "(nat,nat,nat,nat) schema_system" where
  "judgment_retention_system=system_union judgment_retention_base_system judgment_retention_definition_group"

lemma judgment_retention_system_formed [simp]: "schema_system_formed judgment_retention_system"
  using judgment_retention_group.formed by (simp only: judgment_retention_system_def)

lemma judgment_retention_definitions [simp]:
  "system_definitions judgment_retention_system=system_definitions judgment_retention_base_system\<union>{178,179,180,181,182,183,184}"
  by (simp add: judgment_retention_system_def)

lemma judgment_retention_call:
  "schema_call_formed judgment_retention_system d t \<longleftrightarrow>
    d\<in>system_definitions judgment_retention_system \<and> term_formed t"
  using judgment_retention_group.variable_calls[OF judgment_retention_base_call judgment_retention_group_interfaces, of d t]
  by (simp only: judgment_retention_system_def)

lemma judgment_retention_old_meaning:
  assumes "d\<in>system_definitions judgment_retention_base_system"
  shows "(d,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_slot_reading_system"
  using judgment_retention_group.old_meaning[OF assms, of t] judgment_retention_base_meaning[OF assms, of t]
  by (simp only: judgment_retention_system_def; blast)

lemma judgment_retention_clause:
  assumes "d\<in>{178,179,180,181,182,183,184}"
  shows "((d,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>judgment_retention_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses judgment_retention_definition_group"
    using judgment_retention_group.group_agreement assms
    by (simp only: judgment_retention_system_def systems_agree_on_def judgment_retention_group_definitions; blast)
  show ?thesis using same assms by (simp only: judgment_retention_group_family; blast)
qed

lemma judgment_retention_clauses [simp]:
  "((178,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>{(0,judgment_source_schema)}"
  "((179,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,judgment_program_slot_schema),(1,judgment_application_slot_schema)}"
  "((180,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow>
    (c,S)\<in>{(0,judgment_required_root_schema False),(1,judgment_required_root_schema True),
      (2,judgment_required_definition_schema),(3,judgment_required_target_schema)}"
  "((181,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 180 181"
  "((182,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 179 182"
  "((183,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>{(0,judgment_closed_source_schema)}"
  "((184,c),S)\<in>system_clauses judgment_retention_system \<longleftrightarrow> (c,S)\<in>{(0,judgment_retention_report_schema)}"
  using judgment_retention_clause by (auto simp: judgment_retention_group_clauses_def)

lemma judgment_retention_components:
  "(5,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(38,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (38,t)\<in>positive_meaning binding_lookup_system"
  "(51,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(58,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(80,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(83,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(113,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  "(119,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (119,t)\<in>positive_meaning package_slot_reading_system"
  using judgment_retention_old_meaning[of 5 t] judgment_retention_old_meaning[of 38 t]
    judgment_retention_old_meaning[of 51 t] judgment_retention_old_meaning[of 58 t]
    judgment_retention_old_meaning[of 80 t] judgment_retention_old_meaning[of 83 t]
    judgment_retention_old_meaning[of 113 t] judgment_retention_old_meaning[of 119 t]
    judgment_retention_base_roots judgment_retention_component_meanings[of t] by auto

lemma judgment_retention_base_boundary:
  "system_definitions judgment_retention_base_system\<subseteq>
    system_definitions package_membership_system\<union>{103,104,105,112,113,119}"
  by (rule judgment_retention_base_least[OF _ judgment_retention_component_boundary]) auto

theorem judgment_retention_has_no_truth_or_proof_checker:
  "system_definitions judgment_retention_system\<inter>{84,85,94,97,102,107,110,111,115,118,122,151,160,162,165,167}={}"
  using judgment_retention_base_boundary
  by (auto simp only: judgment_retention_definitions; auto)

text \<open>
  Seven definitions have thirteen ordinary clauses. Readability checks the
  package and application in one complete environment. Slot queries select
  actual package or application reads. Required uses are the two roots,
  reached definition uses, and targets of those demanded slots.

  Generic list profiles check both complete stored key lists. A retained
  environment report checks a closed readable context in the claimed
  environment and its inclusion in the supplied source. The base retains the
  least complete-definition closure of eight actual external callees.
\<close>

end
