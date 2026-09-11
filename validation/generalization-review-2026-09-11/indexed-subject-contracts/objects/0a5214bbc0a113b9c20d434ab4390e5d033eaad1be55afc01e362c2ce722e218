theory Factor_Generation_Clauses
  imports Factor_Generation_Values Factor_Target_Comparison Factor_Recursive_Groups Factor_Related_Difference
begin

section \<open>The existing four fields and their mutually recursive comparisons\<close>

abbreviation generation_left_pattern :: "nat term_pattern" where
  "generation_left_pattern \<equiv> Pattern_Pair (Pattern_Variable 0)
    (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))"

abbreviation generation_right_pattern :: "nat term_pattern" where
  "generation_right_pattern \<equiv> Pattern_Pair (Pattern_Variable 4)
    (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))"

definition generation_admission_schema :: "(nat,nat,nat) factor_schema" where
  "generation_admission_schema=data_rule generation_left_pattern
    {(0,35,Pattern_Variable 0),(1,143,Pattern_Variable 1),
      (2,35,Pattern_Variable 2),(3,35,Pattern_Variable 3)}"

definition generation_identity_schema :: "(nat,nat,nat) factor_schema" where
  "generation_identity_schema=data_rule (Pattern_Pair generation_left_pattern generation_right_pattern)
    {(0,139,generation_left_pattern),(1,139,generation_right_pattern),
      (2,135,Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 4)),
      (3,145,Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 5)),
      (4,135,Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 6)),
      (5,135,Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 7))}"

definition generation_difference_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "generation_difference_schema i=data_rule (Pattern_Pair generation_left_pattern generation_right_pattern)
    {(0,139,generation_left_pattern),(1,139,generation_right_pattern),
      (2,(if i=1 then 146 else 136),Pattern_Pair (Pattern_Variable i) (Pattern_Variable (i+4)))}"

definition generation_group_clauses :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "generation_group_clauses d=
    (if d=139 then {(0,generation_admission_schema)}
     else if d=140 then {(0,generation_identity_schema)}
     else if d=141 then {(0,generation_difference_schema 0),(1,generation_difference_schema 1),
       (2,generation_difference_schema 2),(3,generation_difference_schema 3)}
     else if d=142 then context_list_clauses 141 142
     else if d=143 then separated_list_clauses 139 142 143
     else if d=144 then related_selection_clauses 2 4 140 144
     else if d=145 then related_bag_clauses 144 145
     else if d=146 then related_difference_clauses 2 4 142 144 146
     else {})"

definition generation_definition_group :: "(nat,nat,nat,nat) schema_system" where
  "generation_definition_group=\<lparr>
    system_interfaces=(\<lambda>d. (d,data_x)) ` {139,140,141,142,143,144,145,146},
    system_clauses=(\<Union>d\<in>{139,140,141,142,143,144,145,146}.
      (\<lambda>(c,S). ((d,c),S)) ` generation_group_clauses d)\<rparr>"

lemma generation_group_definitions [simp]:
  "system_definitions generation_definition_group={139,140,141,142,143,144,145,146}"
  by (auto simp: generation_definition_group_def system_definitions_def rel_dom_def)

lemma generation_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces generation_definition_group \<longleftrightarrow>
    d\<in>{139,140,141,142,143,144,145,146} \<and> p=data_x"
  by (auto simp: generation_definition_group_def)

lemma generation_group_family [simp]:
  "((d,c),S)\<in>system_clauses generation_definition_group \<longleftrightarrow>
    d\<in>{139,140,141,142,143,144,145,146} \<and> (c,S)\<in>generation_group_clauses d"
  by (auto simp: generation_definition_group_def)

lemma generation_group_finite: "finite (generation_group_clauses d)"
  by (simp add: generation_group_clauses_def context_list_clauses_def separated_list_clauses_def
    related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def)

lemma generation_group_functional: "single_valued (generation_group_clauses d)"
  by (auto simp: generation_group_clauses_def context_list_clauses_def separated_list_clauses_def
    related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def single_valued_def)

lemmas generation_group_schema_defs = generation_admission_schema_def generation_identity_schema_def
  generation_difference_schema_def context_list_nil_schema_def context_list_step_schema_def
  data_list_nil_schema_def separated_list_step_schema_def related_selection_here_schema_def
  selection_later_schema_def bag_nil_schema_def bag_step_schema_def related_extra_schema_def related_missing_schema_def

lemma generation_group_schema_formation:
  assumes "(c,S)\<in>generation_group_clauses d"
  shows "schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions target_difference_system\<union>system_definitions generation_definition_group"
  using assms
  by (auto simp: generation_group_clauses_def context_list_clauses_def separated_list_clauses_def
    related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def
    generation_group_schema_defs schema_formed_def schema_dependencies_def single_valued_def
    rel_dom_def rel_ran_def octets_formed_def split: if_splits)

lemma generation_group_source_formation:
  "schema_system_formed_over (system_definitions target_difference_system) generation_definition_group"
proof -
  have finite: "finite (system_interfaces generation_definition_group)"
    "finite (system_clauses generation_definition_group)"
    by (simp_all add: generation_definition_group_def generation_group_finite)
  have interfaces: "single_valued (system_interfaces generation_definition_group)"
    by (auto simp: single_valued_def)
  have clauses: "single_valued (system_clauses generation_definition_group)"
    using generation_group_functional by (auto simp: single_valued_def; blast)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses generation_definition_group \<longrightarrow>
    d\<in>system_definitions generation_definition_group \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions target_difference_system\<union>system_definitions generation_definition_group"
    using generation_group_schema_formation by auto
  show ?thesis using finite interfaces clauses schemas
    by (simp add: schema_system_formed_over_def)
qed

lemma generation_group_external_dependencies:
  "system_external_dependencies generation_definition_group={2,4,35,135,136}"
  by (simp add: system_external_dependencies_clauses generation_definition_group_def
    generation_group_clauses_def context_list_clauses_def separated_list_clauses_def
    related_selection_clauses_def related_bag_clauses_def related_difference_clauses_def
    generation_group_schema_defs schema_dependencies_def rel_ran_image system_definitions_def rel_dom_image; auto)

definition generation_target_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_target_system=rooted_system target_difference_system
    (system_external_dependencies generation_definition_group)"

lemma generation_target_system_formed [simp]: "schema_system_formed generation_target_system"
  unfolding generation_target_system_def by (rule rooted_system_formed[OF target_difference_system_formed])

lemma generation_target_definitions:
  "system_definitions generation_target_system=system_definition_closure target_difference_system {2,4,35,135,136}"
  unfolding generation_target_system_def generation_group_external_dependencies
  by (rule rooted_system_definitions[OF target_difference_system_formed]) auto

lemma generation_target_subdomain:
  "system_definitions generation_target_system\<subseteq>system_definitions target_difference_system"
  unfolding generation_target_system_def by (rule rooted_system_subdomain)

lemma generation_target_roots:
  "{2,4,35,135,136}\<subseteq>system_definitions generation_target_system"
  unfolding generation_target_system_def generation_group_external_dependencies
  by (rule rooted_system_roots[OF target_difference_system_formed]) auto

lemma generation_target_least:
  assumes "{2,4,35,135,136}\<subseteq>U" "system_dependency_closed target_difference_system U"
  shows "system_definitions generation_target_system\<subseteq>U"
  using system_definition_closure_least[OF assms] by (simp only: generation_target_definitions)

lemma generation_target_call:
  "schema_call_formed generation_target_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_target_system \<and> term_formed t"
  using rooted_system_calls[where roots="system_external_dependencies generation_definition_group" and d=d and t=t,
    OF target_difference_system_formed]
  by (simp only: generation_target_system_def rooted_system_def system_restriction_definitions target_difference_call; blast)

lemma generation_target_meaning:
  assumes "d\<in>system_definitions generation_target_system"
  shows "(d,t)\<in>positive_meaning generation_target_system \<longleftrightarrow> (d,t)\<in>positive_meaning target_difference_system"
  using rooted_system_meaning[where roots="system_external_dependencies generation_definition_group" and d=d and t=t,
    OF target_difference_system_formed] assms
  by (simp only: generation_target_system_def rooted_system_def system_restriction_definitions; blast)

lemma generation_target_agreement:
  "systems_agree_on target_difference_system generation_target_system (system_definitions generation_target_system)"
  unfolding generation_target_system_def by (rule rooted_system_agreement)

lemma generation_group_relative_formation:
  "schema_system_formed_over (system_definitions generation_target_system) generation_definition_group"
proof -
  have actual: "schema_system_formed_over (system_external_dependencies generation_definition_group) generation_definition_group"
    by (rule schema_system_formed_over_actual_dependencies[OF generation_group_source_formation])
  have retained: "system_external_dependencies generation_definition_group\<subseteq>system_definitions generation_target_system"
    using generation_target_roots by (simp only: generation_group_external_dependencies)
  show ?thesis by (rule schema_system_formed_over_mono[OF actual retained])
qed

interpretation generation_group: positive_definition_group generation_target_system generation_definition_group
  by (rule positive_definition_group.intro[OF generation_target_system_formed generation_group_relative_formation])
    (use generation_target_subdomain in auto)

definition generation_value_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_value_system=system_union generation_target_system generation_definition_group"

lemma generation_value_system_formed [simp]: "schema_system_formed generation_value_system"
  using generation_group.formed by (simp only: generation_value_system_def)

lemma generation_value_definitions [simp]:
  "system_definitions generation_value_system=
    system_definitions generation_target_system\<union>{139,140,141,142,143,144,145,146}"
  by (simp add: generation_value_system_def)

lemma generation_value_call:
  "schema_call_formed generation_value_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_value_system \<and> term_formed t"
  using generation_group.variable_calls[OF generation_target_call generation_group_interfaces, of d t]
  by (simp only: generation_value_system_def)

lemma generation_value_old_meaning:
  assumes "d\<in>system_definitions generation_target_system"
  shows "(d,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_difference_system"
  using generation_group.old_meaning[OF assms, of t] generation_target_meaning[OF assms, of t]
  by (simp only: generation_value_system_def; blast)

lemma generation_value_base_agreement:
  "systems_agree_on generation_target_system generation_value_system (system_definitions generation_target_system)"
  using generation_group.old_agreement by (simp only: generation_value_system_def)

lemma generation_value_clause:
  assumes "d\<in>{139,140,141,142,143,144,145,146}"
  shows "((d,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>generation_group_clauses d"
proof -
  have same: "((d,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow>
      ((d,c),S)\<in>system_clauses generation_definition_group"
    using generation_group.group_agreement assms
    by (simp only: generation_value_system_def systems_agree_on_def generation_group_definitions; blast)
  show ?thesis using same assms by (simp only: generation_group_family; blast)
qed

lemma generation_value_clauses [simp]:
  "((139,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>{(0,generation_admission_schema)}"
  "((140,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>{(0,generation_identity_schema)}"
  "((141,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow>
    (c,S)\<in>{(0,generation_difference_schema 0),(1,generation_difference_schema 1),
      (2,generation_difference_schema 2),(3,generation_difference_schema 3)}"
  "((142,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 141 142"
  "((143,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>separated_list_clauses 139 142 143"
  "((144,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>related_selection_clauses 2 4 140 144"
  "((145,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>related_bag_clauses 144 145"
  "((146,c),S)\<in>system_clauses generation_value_system \<longleftrightarrow> (c,S)\<in>related_difference_clauses 2 4 142 144 146"
  using generation_value_clause by (auto simp: generation_group_clauses_def)

lemma generation_value_bag_meaning:
  assumes "d\<in>{2,4}"
  shows "(d,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (d,t)\<in>positive_meaning bag_comparison_system"
  using assms generation_target_roots generation_value_old_meaning[of d t] target_difference_old_meaning[of d t]
    target_identity_old_meaning[of d t] artifact_difference_old_meaning[of d t]
    bag_difference_bag_meaning[of d t] by auto

lemma generation_value_components:
  "(2,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  "(4,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
  "(35,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (\<exists>x. target_value_presents x t)"
  "(135,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (135,t)\<in>positive_meaning target_identity_system"
  "(136,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (136,t)\<in>positive_meaning target_difference_system"
  using generation_target_roots generation_value_bag_meaning[of 2 t] bag_comparison_recognizes[of t]
    generation_value_bag_meaning[of 4 t] data_list_exact[of t]
    generation_value_old_meaning[of 35 t] target_difference_components(1)[of t]
    generation_value_old_meaning[of 135 t] target_difference_old_meaning[of 135 t]
    generation_value_old_meaning[of 136 t] by auto

interpretation generation_collections: separated_list_profile generation_value_system 141 142 139 143
  by (unfold_locales) (auto simp: generation_value_call)

section \<open>The actual positive clauses determine the recursive equations\<close>

lemma generation_admission_valuation:
  "(139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      (35,h 0)\<in>positive_meaning generation_value_system \<and>
      (143,h 1)\<in>positive_meaning generation_value_system \<and>
      (35,h 2)\<in>positive_meaning generation_value_system \<and>
      (35,h 3)\<in>positive_meaning generation_value_system)"
proof -
  have ordinary: "\<And>c S. ((139,c),S)\<in>system_clauses generation_value_system \<Longrightarrow> schema_material_premises S={}"
    by (auto simp: generation_admission_schema_def)
  show ?thesis using ordinary_positive_entry_valuation[where P=generation_value_system and d=139 and t=t, OF ordinary]
    by (auto simp: generation_value_call generation_admission_schema_def schema_variables_def)
qed

lemma generation_admission_fields:
  "(139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>a b c d. t=Pair_Term a (Pair_Term b (Pair_Term c d)) \<and>
      (\<exists>l. target_value_presents l a) \<and> (143,b)\<in>positive_meaning generation_value_system \<and>
      (\<exists>p. target_value_presents p c) \<and> (\<exists>q. target_value_presents q d))"
proof
  assume "(139,t)\<in>positive_meaning generation_value_system"
  then show "\<exists>a b c d. t=Pair_Term a (Pair_Term b (Pair_Term c d)) \<and>
    (\<exists>l. target_value_presents l a) \<and> (143,b)\<in>positive_meaning generation_value_system \<and>
    (\<exists>p. target_value_presents p c) \<and> (\<exists>q. target_value_presents q d)"
    by (simp only: generation_admission_valuation generation_value_components) blast
next
  assume "\<exists>a b c d. t=Pair_Term a (Pair_Term b (Pair_Term c d)) \<and>
    (\<exists>l. target_value_presents l a) \<and> (143,b)\<in>positive_meaning generation_value_system \<and>
    (\<exists>p. target_value_presents p c) \<and> (\<exists>q. target_value_presents q d)"
  then obtain a b c d l p q where fields: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    "target_value_presents l a" "(143,b)\<in>positive_meaning generation_value_system"
    "target_value_presents p c" "target_value_presents q d" by blast
  have formed: "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    using target_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(4)]
      target_value_presents_formed[OF fields(5)] schema_call_formed_target[OF positive_meaning_formed[OF fields(3)]] by auto
  show "(139,t)\<in>positive_meaning generation_value_system"
    by (simp only: generation_admission_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then c else d"])
      (use fields formed in \<open>auto simp: generation_value_components\<close>)
qed

text \<open>
  This group has eight ordinary definitions. Admission reads the independently
  defined generation's locus, complete predecessor set, payload, and recorded
  cause. Equality compares all four fields; inequality has one alternative
  for each field, under complete admission of both operands. The two list
  traversals and three comparison helpers supply the positive recursion.

  The base is the least closed restriction of the existing target program
  containing the group's five actual external callees. Its complete retained
  definitions preserve their original calls and meaning. The group is compiled
  after its actual positive meaning has been related to the existing generation
  class. Cause validity, publication, authority, and replay are separate from
  these value operations.
\<close>

end
