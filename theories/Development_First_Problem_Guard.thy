theory Development_First_Problem_Guard
  imports Factor_Package_Additions Factor_Payload_Audit Factor_Requirement_Installation
    Factor_Clause_Family_Rules
begin

text \<open>
  The first problem's asked relation (DECISIONS.md, "The first problem's requirements use the test of a
  native distinction; the octet audit is one of its parts"): the requirement guard with four sockets on
  the pair of two site values, the given's first and the candidate's second, every socket receiving the
  whole pair. G1, retention: the candidate's environment includes the given's. G2, formation and closure:
  the candidate's site holds a native package. G3, the callee boundary: every definition of that package
  is a definition of the given's package or stands at a use of no artifact of the given's environment. G4,
  the octet audit: every definition of that package that is not a definition of the given's states no
  payload but the empty one. Each goal consumes its readers' contracts as proved; a refusal names the
  socket that failed. The test is the owner's (Q23 (a)); its encoding as these four goals is generated and
  stands until the owner authorizes it.
\<close>

section \<open>The readers the goals call, joined where they agree\<close>

lemma inclusion_complete_data_agreement:
  "systems_agree_on environment_inclusion_system complete_data_admission_system
    (system_definitions environment_inclusion_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def)

lemma admission_complete_data_agreement:
  "systems_agree_on package_admission_system complete_data_admission_system
    (system_definitions package_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def)

lemma call_admission_complete_data_agreement:
  "systems_agree_on definition_call_admission_system complete_data_admission_system
    (system_definitions definition_call_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def
    package_slot_list_system_def package_source_list_system_def package_slot_reading_system_def
    package_source_reading_system_def scope_forwarding_system_def native_positive_admission_system_def
    positive_query_system_def environment_inclusion_system_def artifact_inclusion_system_def
    replay_admission_system_def retention_admission_system_def replay_slot_list_system_def
    replay_source_list_system_def replay_slot_reading_system_def replay_source_reading_system_def
    definition_slot_reading_system_def schema_slot_reading_system_def premise_slot_reading_system_def
    derivation_admission_system_def proof_claim_checking_system_def keyed_row_join_system_def
    row_qualification_system_def proof_graph_membership_system_def proof_graph_admission_system_def
    proof_bound_checking_system_def proof_link_checking_system_def proof_node_reading_system_def
    discharge_table_reading_system_def binding_table_reading_system_def site_link_vector_system_def
    application_vector_system_def site_link_reading_system_def site_citation_reading_system_def
    admitted_instantiation_system_def program_call_list_system_def application_admission_system_def
    program_call_admission_system_def package_membership_system_def definition_edge_reading_system_def
    definition_clause_reading_system_def package_admission_system_def root_family_reading_system_def
    located_list_system_def package_closure_admission_system_def definition_callee_list_system_def
    definition_callee_inclusion_system_def schema_callee_list_system_def schema_callee_inclusion_system_def)

lemma call_admission_audit_agreement:
  "systems_agree_on definition_call_admission_system payload_audit_system
    (system_definitions definition_call_admission_system)"
  by (simp add: systems_agree_on_added payload_audit_system_def clause_family_payloads_system_def
    clause_payloads_system_def empty_payload_calls_system_def empty_payload_rows_system_def
    empty_payloads_system_def)

lemma complete_below: "system_definitions complete_data_admission_system\<subseteq>{..<390}"
  by auto

lemma audit_below: "system_definitions payload_audit_system\<subseteq>{..<506}"
  by auto

lemma scope_below:
  "system_definitions scope_reading_components_system\<subseteq>{..<390}"
proof -
  have complete: "system_definitions complete_data_admission_system\<subseteq>{..<390}" by (rule complete_below)
  have lookup: "system_definitions artifact_lookup_system\<subseteq>{..<390}" by auto
  have base: "system_definitions context_base_system\<subseteq>{..<390}"
    by (rule subset_trans[OF context_base_subdomain lookup])
  show ?thesis
    by (simp only: scope_reading_components_definitions context_admission_definitions Un_subset_iff)
      (use complete base in auto)
qed

lemma scope_numbers_fresh:
  assumes "d\<in>{390,391,392,393,500,501,502,503,504,505,520,521,522,523,524,525,526}"
  shows "d\<notin>system_definitions scope_reading_components_system"
proof
  assume "d\<in>system_definitions scope_reading_components_system"
  then have "d<390" using scope_below by blast
  then show False using assms by simp
qed

lemma additions_below:
  "system_definitions use_additions_system\<subseteq>{..<394}"
proof -
  have scope: "system_definitions scope_reading_components_system\<subseteq>{..<394}"
    by (rule subset_trans[OF scope_below]) auto
  have "system_definitions use_additions_system=
      {390,391,392,393}\<union>system_definitions scope_reading_components_system"
    by (simp only: use_additions_definitions addition_list_definitions addition_element_definitions
      use_absence_definitions) blast
  then show ?thesis using scope by simp
qed

lemma guard_numbers_fresh:
  "d\<in>{500,501,502,503,504,505,520,521,522,523,524,525,526} \<Longrightarrow> d\<notin>system_definitions use_additions_system"
  "d\<in>{520,521,522,523,524,525,526} \<Longrightarrow> d\<notin>system_definitions payload_audit_system"
proof -
  show "d\<notin>system_definitions use_additions_system" if "d\<in>{500,501,502,503,504,505,520,521,522,523,524,525,526}"
  proof
    assume "d\<in>system_definitions use_additions_system"
    then have "d<394" using additions_below by blast
    then show False using that by simp
  qed
  show "d\<notin>system_definitions payload_audit_system" if "d\<in>{520,521,522,523,524,525,526}"
  proof
    assume "d\<in>system_definitions payload_audit_system"
    then have "d<506" using audit_below by blast
    then show False using that by simp
  qed
qed

lemma complete_data_additions_agreement:
  "systems_agree_on complete_data_admission_system use_additions_system
    (system_definitions complete_data_admission_system)"
proof -
  have scope: "systems_agree_on complete_data_admission_system scope_reading_components_system
      (system_definitions complete_data_admission_system)"
    unfolding scope_reading_components_system_def
    by (rule system_union_agree_left[OF context_admission_system_formed scope_context_agreement])
  have fresh: "d\<notin>system_definitions complete_data_admission_system" if "d\<in>{390,391,392,393}" for d
  proof
    assume "d\<in>system_definitions complete_data_admission_system"
    then have "d<390" using complete_below by blast
    then show False using that by simp
  qed
  have added: "systems_agree_on scope_reading_components_system use_additions_system
      (system_definitions complete_data_admission_system)"
    using fresh by (simp add: systems_agree_on_added use_additions_system_def addition_list_system_def
      addition_element_system_def use_absence_system_def)
  show ?thesis by (rule systems_agree_on_transitive[OF scope added])
qed

lemma inclusion_additions_agreement:
  "systems_agree_on environment_inclusion_system use_additions_system (system_definitions environment_inclusion_system)"
  by (rule whole_agreement_transitive[OF inclusion_complete_data_agreement complete_data_additions_agreement])

lemma admission_additions_agreement:
  "systems_agree_on package_admission_system use_additions_system (system_definitions package_admission_system)"
  by (rule whole_agreement_transitive[OF admission_complete_data_agreement complete_data_additions_agreement])

lemma readers_agreement:
  "systems_agree_on use_additions_system payload_audit_system
    (system_definitions use_additions_system\<inter>system_definitions payload_audit_system)"
proof (rule common_component_overlap_agreement[where B=definition_call_admission_system])
  show "systems_agree_on definition_call_admission_system use_additions_system
      (system_definitions definition_call_admission_system\<inter>system_definitions use_additions_system)"
    by (rule systems_agree_on_subdomain[OF whole_agreement_transitive[OF
      call_admission_complete_data_agreement complete_data_additions_agreement]]) blast
  show "systems_agree_on definition_call_admission_system payload_audit_system
      (system_definitions definition_call_admission_system\<inter>system_definitions payload_audit_system)"
    by (rule systems_agree_on_subdomain[OF call_admission_audit_agreement]) blast
  show "system_definitions use_additions_system\<inter>system_definitions payload_audit_system\<subseteq>
      system_definitions definition_call_admission_system"
  proof
    fix x assume x: "x\<in>system_definitions use_additions_system\<inter>system_definitions payload_audit_system"
    have "x\<in>{500,501,502,503,504,505} \<or> x\<in>system_definitions definition_call_admission_system"
      using x by (simp only: Int_iff payload_audit_definitions clause_family_payloads_definitions
        clause_payloads_definitions empty_payload_calls_definitions empty_payload_rows_definitions
        empty_payloads_definitions insert_iff) blast
    then show "x\<in>system_definitions definition_call_admission_system"
      using x guard_numbers_fresh(1)[of x] by blast
  qed
qed

definition guard_readers_system :: "(nat,nat,nat,nat) schema_system" where
  "guard_readers_system=system_union use_additions_system payload_audit_system"

lemma guard_readers_formed [simp]: "schema_system_formed guard_readers_system"
  unfolding guard_readers_system_def
  by (rule system_union_agree_formed[OF use_additions_system_formed payload_audit_system_formed readers_agreement])

lemma guard_readers_definitions:
  "system_definitions guard_readers_system=system_definitions use_additions_system\<union>system_definitions payload_audit_system"
  by (simp add: guard_readers_system_def)

lemma guard_readers_call:
  "schema_call_formed guard_readers_system d t \<longleftrightarrow> d\<in>system_definitions guard_readers_system \<and> term_formed t"
  unfolding guard_readers_system_def
  by (simp only: system_union_agree_call[OF use_additions_system_formed payload_audit_system_formed readers_agreement]
    use_additions_call payload_audit_call system_union_definitions Un_iff) blast

lemma guard_readers_left:
  assumes "d\<in>system_definitions use_additions_system"
  shows "(d,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning use_additions_system"
  using system_union_agree_left_locality[OF use_additions_system_formed payload_audit_system_formed
    readers_agreement assms] by (simp add: guard_readers_system_def)

lemma guard_readers_right:
  assumes "d\<in>system_definitions payload_audit_system"
  shows "(d,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning payload_audit_system"
  using system_union_agree_right_locality[OF use_additions_system_formed payload_audit_system_formed
    readers_agreement assms] by (simp add: guard_readers_system_def)

lemma guard_fresh:
  assumes "d\<in>{520,521,522,523,524,525,526}"
  shows "d\<notin>system_definitions guard_readers_system"
proof -
  have "d\<notin>system_definitions use_additions_system" by (rule guard_numbers_fresh(1)) (use assms in auto)
  moreover have "d\<notin>system_definitions payload_audit_system" by (rule guard_numbers_fresh(2)[OF assms])
  ultimately show ?thesis by (simp only: guard_readers_definitions Un_iff) blast
qed

lemma additions_sites:
  "{80,113,392,83,156,79,47,76}\<subseteq>system_definitions use_additions_system"
proof -
  have "113\<in>system_definitions use_additions_system"
    using whole_agreement_definitions[OF inclusion_additions_agreement] by auto
  moreover have "80\<in>system_definitions use_additions_system"
    using whole_agreement_definitions[OF admission_additions_agreement] by auto
  moreover have "{83,79,47,76}\<subseteq>system_definitions use_additions_system"
    using complete_data_addition_components(6) whole_agreement_definitions[OF complete_data_additions_agreement]
    by auto
  moreover have "156\<in>system_definitions use_additions_system" "392\<in>system_definitions use_additions_system"
    by simp_all
  ultimately show ?thesis by auto
qed

lemma guard_reader_sites:
  "{80,113,392,505,83,156,79,47,76}\<subseteq>system_definitions guard_readers_system"
proof -
  have "505\<in>system_definitions payload_audit_system" by simp
  then show ?thesis using additions_sites by (simp only: guard_readers_definitions) blast
qed

section \<open>The goals: argument views over the pair, and the audit as the callee of the additions notion\<close>

text \<open>
  G1 and G2 are views: each takes the whole pair and passes its reader the part the reader's argument is,
  the two environment values for inclusion and the candidate's site value read as a source and root for
  package admission. G3 is the callee boundary as it stands. G4 is the additions notion again, its callee
  the audit of the member's definition in the candidate's environment. The numbers 520–526 are above
  every numbered site of the library.
\<close>

definition retention_goal_schema :: "(nat,nat,nat) factor_schema" where
  "retention_goal_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,113,Pattern_Pair data_x data_z)}"

definition formation_goal_schema :: "(nat,nat,nat) factor_schema" where
  "formation_goal_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w)))
    {(0,80,Pattern_Pair (Pattern_Pair data_y data_z) data_w)}"

definition audit_callee_schema :: "(nat,nat,nat) factor_schema" where
  "audit_callee_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,505,Pattern_Pair (Pattern_Pair data_y data_w) (Pattern_Variable 4))}"

definition retention_goal_system :: "(nat,nat,nat,nat) schema_system" where
  "retention_goal_system=add_view_definition guard_readers_system 520 data_x {(0,retention_goal_schema)}"

definition formation_goal_system :: "(nat,nat,nat,nat) schema_system" where
  "formation_goal_system=add_view_definition retention_goal_system 521 data_x {(0,formation_goal_schema)}"

definition audit_callee_system :: "(nat,nat,nat,nat) schema_system" where
  "audit_callee_system=add_view_definition formation_goal_system 522 data_x {(0,audit_callee_schema)}"

definition audit_element_system :: "(nat,nat,nat,nat) schema_system" where
  "audit_element_system=add_view_definition audit_callee_system 523 data_x (addition_element_clauses 522)"

definition audit_list_system :: "(nat,nat,nat,nat) schema_system" where
  "audit_list_system=add_view_definition audit_element_system 524 data_x (context_list_clauses 523 524)"

definition first_problem_goals_system :: "(nat,nat,nat,nat) schema_system" where
  "first_problem_goals_system=add_view_definition audit_list_system 525 data_x {(0,package_additions_schema 524)}"

lemma retention_goal_system_formed [simp]: "schema_system_formed retention_goal_system"
  unfolding retention_goal_system_def
  using guard_reader_sites
  by (intro add_recursive_definition_formed[OF guard_readers_formed])
    (auto simp: retention_goal_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def guard_fresh)

lemma retention_goal_definitions [simp]:
  "system_definitions retention_goal_system=insert 520 (system_definitions guard_readers_system)"
  by (simp add: retention_goal_system_def)

lemma formation_goal_system_formed [simp]: "schema_system_formed formation_goal_system"
  unfolding formation_goal_system_def
  using guard_reader_sites
  by (intro add_recursive_definition_formed[OF retention_goal_system_formed])
    (auto simp: formation_goal_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def guard_fresh)

lemma formation_goal_definitions [simp]:
  "system_definitions formation_goal_system=insert 521 (system_definitions retention_goal_system)"
  by (simp add: formation_goal_system_def)

lemma audit_callee_system_formed [simp]: "schema_system_formed audit_callee_system"
  unfolding audit_callee_system_def
  using guard_reader_sites
  by (intro add_recursive_definition_formed[OF formation_goal_system_formed])
    (auto simp: audit_callee_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def guard_fresh)

lemma audit_callee_definitions [simp]:
  "system_definitions audit_callee_system=insert 522 (system_definitions formation_goal_system)"
  by (simp add: audit_callee_system_def)

lemma audit_element_system_formed [simp]: "schema_system_formed audit_element_system"
  unfolding audit_element_system_def
  using guard_reader_sites
  by (intro add_recursive_definition_formed[OF audit_callee_system_formed])
    (auto simp: addition_element_clauses_def addition_member_schema_def addition_callee_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def guard_fresh)

lemma audit_element_definitions [simp]:
  "system_definitions audit_element_system=insert 523 (system_definitions audit_callee_system)"
  by (simp add: audit_element_system_def)

lemma audit_list_system_formed [simp]: "schema_system_formed audit_list_system"
  unfolding audit_list_system_def
  by (rule add_recursive_definition_formed[OF audit_element_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      guard_fresh)

lemma audit_list_definitions [simp]:
  "system_definitions audit_list_system=insert 524 (system_definitions audit_element_system)"
  by (simp add: audit_list_system_def)

lemma first_problem_goals_formed [simp]: "schema_system_formed first_problem_goals_system"
  unfolding first_problem_goals_system_def
  using guard_reader_sites
  by (intro add_recursive_definition_formed[OF audit_list_system_formed])
    (auto simp: package_additions_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def guard_fresh)

lemma first_problem_goals_definitions [simp]:
  "system_definitions first_problem_goals_system=insert 525 (system_definitions audit_list_system)"
  by (simp add: first_problem_goals_system_def)

lemma first_problem_goals_call:
  "schema_call_formed first_problem_goals_system d t \<longleftrightarrow>
    d\<in>system_definitions first_problem_goals_system \<and> term_formed t"
proof -
  have retention: "schema_call_formed retention_goal_system d t \<longleftrightarrow>
      d\<in>system_definitions retention_goal_system \<and> term_formed t" for d t
    using added_variable_calls[OF guard_readers_formed
      retention_goal_system_formed[unfolded retention_goal_system_def] guard_readers_call]
    by (simp only: retention_goal_system_def[symmetric])
  have formation: "schema_call_formed formation_goal_system d t \<longleftrightarrow>
      d\<in>system_definitions formation_goal_system \<and> term_formed t" for d t
    using added_variable_calls[OF retention_goal_system_formed
      formation_goal_system_formed[unfolded formation_goal_system_def] retention]
    by (simp only: formation_goal_system_def[symmetric])
  have callee: "schema_call_formed audit_callee_system d t \<longleftrightarrow>
      d\<in>system_definitions audit_callee_system \<and> term_formed t" for d t
    using added_variable_calls[OF formation_goal_system_formed
      audit_callee_system_formed[unfolded audit_callee_system_def] formation]
    by (simp only: audit_callee_system_def[symmetric])
  have element: "schema_call_formed audit_element_system d t \<longleftrightarrow>
      d\<in>system_definitions audit_element_system \<and> term_formed t" for d t
    using added_variable_calls[OF audit_callee_system_formed
      audit_element_system_formed[unfolded audit_element_system_def] callee]
    by (simp only: audit_element_system_def[symmetric])
  have listing: "schema_call_formed audit_list_system d t \<longleftrightarrow>
      d\<in>system_definitions audit_list_system \<and> term_formed t" for d t
    using added_variable_calls[OF audit_element_system_formed
      audit_list_system_formed[unfolded audit_list_system_def] element]
    by (simp only: audit_list_system_def[symmetric])
  show ?thesis
    using added_variable_calls[OF audit_list_system_formed
      first_problem_goals_formed[unfolded first_problem_goals_system_def] listing]
    by (simp only: first_problem_goals_system_def[symmetric])
qed

lemma first_problem_goals_families:
  "((520,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=retention_goal_schema"
  "((521,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=formation_goal_schema"
  "((522,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=audit_callee_schema"
  "((523,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 522"
  "((524,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 523 524"
  "((525,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=package_additions_schema 524"
proof -
  have owned: "((d,c),S)\<in>system_clauses guard_readers_system \<Longrightarrow> d\<in>system_definitions guard_readers_system"
    for d c S
    using guard_readers_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses guard_readers_system" if "d\<in>{520,521,522,523,524,525}" for d c S
    using that guard_fresh[of d] owned by auto
  show "((520,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=retention_goal_schema"
    "((521,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=formation_goal_schema"
    "((522,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=audit_callee_schema"
    "((523,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 522"
    "((524,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 523 524"
    "((525,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=package_additions_schema 524"
    using absent by (auto simp: first_problem_goals_system_def audit_list_system_def audit_element_system_def
      audit_callee_system_def formation_goal_system_def retention_goal_system_def)
qed

lemma goals_extension_agreement:
  "systems_agree_on guard_readers_system first_problem_goals_system (system_definitions guard_readers_system)"
  using guard_fresh by (simp add: systems_agree_on_added first_problem_goals_system_def audit_list_system_def
    audit_element_system_def audit_callee_system_def formation_goal_system_def retention_goal_system_def)

lemma first_problem_goals_components:
  "(113,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  "(80,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(505,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (505,t)\<in>positive_meaning payload_audit_system"
  "(392,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (392,t)\<in>positive_meaning use_additions_system"
  "(156,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>E u r. site_value_presents E u r t)"
  "(83,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> package_membership_result t"
  "(79,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(47,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
proof -
  have lifted: "(d,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
    if "d\<in>system_definitions guard_readers_system" for d
    using whole_system_agreement_meaning[OF guard_readers_formed first_problem_goals_formed
      goals_extension_agreement that] by simp
  have left: "(d,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning use_additions_system"
    if "d\<in>system_definitions use_additions_system" for d
  proof -
    have "d\<in>system_definitions guard_readers_system" using that by (simp only: guard_readers_definitions Un_iff) blast
    then show ?thesis using lifted guard_readers_left[OF that] by blast
  qed
  have inclusion: "(113,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
      (113,t)\<in>positive_meaning use_additions_system"
    using whole_system_agreement_meaning[OF environment_inclusion_system_formed use_additions_system_formed
      inclusion_additions_agreement, of 113] by simp
  have sites: "113\<in>system_definitions use_additions_system" "80\<in>system_definitions use_additions_system"
    "392\<in>system_definitions use_additions_system" "156\<in>system_definitions use_additions_system"
    "83\<in>system_definitions use_additions_system" "79\<in>system_definitions use_additions_system"
    "47\<in>system_definitions use_additions_system" "76\<in>system_definitions use_additions_system"
    using additions_sites by blast+
  have audit_site: "505\<in>system_definitions guard_readers_system" "505\<in>system_definitions payload_audit_system"
    using guard_reader_sites by (blast, simp)
  have admission: "(80,t)\<in>positive_meaning package_admission_system \<longleftrightarrow>
      (80,t)\<in>positive_meaning use_additions_system"
    using whole_system_agreement_meaning[OF package_admission_system_formed use_additions_system_formed
      admission_additions_agreement, of 80] by simp
  show "(113,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
    using left[OF sites(1)] inclusion by simp
  show "(80,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
    using left[OF sites(2)] admission by simp
  show "(505,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (505,t)\<in>positive_meaning payload_audit_system"
    using lifted[OF audit_site(1)] guard_readers_right[OF audit_site(2)] by simp
  show "(392,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (392,t)\<in>positive_meaning use_additions_system"
    using left[OF sites(3)] by simp
  show "(156,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>E u r. site_value_presents E u r t)"
    using left[OF sites(4)] use_additions_components(1)[of t] by simp
  show "(83,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> package_membership_result t"
    using left[OF sites(5)] use_additions_components(2)[of t] by simp
  show "(79,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
    using left[OF sites(6)] use_additions_components(3)[of t] by simp
  show "(47,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    using left[OF sites(7)] use_additions_components(4)[of t] by simp
  show "(76,t)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
    using left[OF sites(8)] use_additions_components(5)[of t] by simp
qed

interpretation audit_additions: package_additions_profile first_problem_goals_system 523 524 525 522
  by unfold_locales (simp_all add: first_problem_goals_families first_problem_goals_call first_problem_goals_components)

section \<open>Each goal's contract at the pair\<close>

text \<open>
  Each goal site of the program holds one ordinary clause under a variable interface, so its meaning is a
  valuation of that clause (@{thm [source] positive_variable_rule_family},
  @{thm [source] ordinary_schema_rule_valuation}); each view rule below only rearranges that valuation.
\<close>

lemma goal_view_rule:
  assumes family: "\<And>c S. ((n,c),S)\<in>system_clauses first_problem_goals_system \<longleftrightarrow> c=0 \<and> S=R"
    and member: "n\<in>system_definitions first_problem_goals_system"
    and ordinary: "schema_material_premises R={}"
  shows "(n,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables R. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion R) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises R \<longrightarrow> (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system))"
proof -
  have call: "\<And>t. schema_call_formed first_problem_goals_system n t \<longleftrightarrow> term_formed t"
    using member by (simp add: first_problem_goals_call)
  have formed: "schema_formed R"
    using first_problem_goals_formed family[of 0 R] unfolding schema_system_formed_def by blast
  have "(n,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
      schema_rule_instance R (positive_meaning first_problem_goals_system) z"
    by (simp only: positive_variable_rule_family[OF call] system_clause_member family) blast
  then show ?thesis by (simp only: ordinary_schema_rule_valuation[OF formed ordinary])
qed

lemma retention_goal_rule:
  "(520,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>x y a b.
    z=Pair_Term (Pair_Term x y) (Pair_Term a b) \<and> term_formed y \<and> term_formed b \<and>
    (113,Pair_Term x a)\<in>positive_meaning environment_inclusion_system)"
proof -
  have view: "(520,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables retention_goal_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion retention_goal_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises retention_goal_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system))"
    by (rule goal_view_rule[OF first_problem_goals_families(1)]) (simp_all add: retention_goal_schema_def)
  show ?thesis
  proof
    assume "(520,z)\<in>positive_meaning first_problem_goals_system"
    then obtain f where f: "\<forall>a\<in>schema_variables retention_goal_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion retention_goal_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises retention_goal_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system"
      using view by blast
    then show "\<exists>x y a b. z=Pair_Term (Pair_Term x y) (Pair_Term a b) \<and> term_formed y \<and> term_formed b \<and>
      (113,Pair_Term x a)\<in>positive_meaning environment_inclusion_system"
      by (auto simp: retention_goal_schema_def schema_variables_def first_problem_goals_components)
  next
  assume "\<exists>x y a b. z=Pair_Term (Pair_Term x y) (Pair_Term a b) \<and> term_formed y \<and> term_formed b \<and>
    (113,Pair_Term x a)\<in>positive_meaning environment_inclusion_system"
  then obtain x y a b where parts: "z=Pair_Term (Pair_Term x y) (Pair_Term a b)" "term_formed y" "term_formed b"
    "(113,Pair_Term x a)\<in>positive_meaning environment_inclusion_system" by blast
  have operands: "term_formed x" "term_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by simp_all
  show "(520,z)\<in>positive_meaning first_problem_goals_system" unfolding view
    by (rule exI[of _ "\<lambda>n::nat. if n=0 then x else if n=1 then y else if n=2 then a else b"])
      (use parts operands in \<open>auto simp: retention_goal_schema_def schema_variables_def
        first_problem_goals_components\<close>)
  qed
qed

lemma formation_goal_rule:
  "(521,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>x y a b.
    z=Pair_Term x (Pair_Term y (Pair_Term a b)) \<and> term_formed x \<and>
    (80,Pair_Term (Pair_Term y a) b)\<in>positive_meaning package_admission_system)"
proof -
  have view: "(521,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables formation_goal_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion formation_goal_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises formation_goal_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system))"
    by (rule goal_view_rule[OF first_problem_goals_families(2)]) (simp_all add: formation_goal_schema_def)
  show ?thesis
  proof
    assume "(521,z)\<in>positive_meaning first_problem_goals_system"
    then obtain f where f: "\<forall>a\<in>schema_variables formation_goal_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion formation_goal_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises formation_goal_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system"
      using view by blast
    then show "\<exists>x y a b. z=Pair_Term x (Pair_Term y (Pair_Term a b)) \<and> term_formed x \<and>
      (80,Pair_Term (Pair_Term y a) b)\<in>positive_meaning package_admission_system"
      by (auto simp: formation_goal_schema_def schema_variables_def first_problem_goals_components)
  next
  assume "\<exists>x y a b. z=Pair_Term x (Pair_Term y (Pair_Term a b)) \<and> term_formed x \<and>
    (80,Pair_Term (Pair_Term y a) b)\<in>positive_meaning package_admission_system"
  then obtain x y a b where parts: "z=Pair_Term x (Pair_Term y (Pair_Term a b))" "term_formed x"
    "(80,Pair_Term (Pair_Term y a) b)\<in>positive_meaning package_admission_system" by blast
  have operands: "term_formed y" "term_formed a" "term_formed b"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by simp_all
  show "(521,z)\<in>positive_meaning first_problem_goals_system" unfolding view
    by (rule exI[of _ "\<lambda>n::nat. if n=0 then x else if n=1 then y else if n=2 then a else b"])
      (use parts operands in \<open>auto simp: formation_goal_schema_def schema_variables_def
        first_problem_goals_components\<close>)
  qed
qed

lemma audit_callee_rule:
  "(522,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>x y c a b.
    z=Pair_Term (Pair_Term x (Pair_Term y c)) (Pair_Term a b) \<and> term_formed x \<and> term_formed c \<and>
    (505,Pair_Term (Pair_Term y a) b)\<in>positive_meaning payload_audit_system)"
proof -
  have view: "(522,z)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables audit_callee_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion audit_callee_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises audit_callee_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system))"
    by (rule goal_view_rule[OF first_problem_goals_families(3)]) (simp_all add: audit_callee_schema_def)
  show ?thesis
  proof
    assume "(522,z)\<in>positive_meaning first_problem_goals_system"
    then obtain f where f: "\<forall>a\<in>schema_variables audit_callee_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion audit_callee_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises audit_callee_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning first_problem_goals_system"
      using view by blast
    then show "\<exists>x y c a b. z=Pair_Term (Pair_Term x (Pair_Term y c)) (Pair_Term a b) \<and> term_formed x \<and>
      term_formed c \<and> (505,Pair_Term (Pair_Term y a) b)\<in>positive_meaning payload_audit_system"
      by (auto simp: audit_callee_schema_def schema_variables_def first_problem_goals_components)
  next
  assume "\<exists>x y c a b. z=Pair_Term (Pair_Term x (Pair_Term y c)) (Pair_Term a b) \<and> term_formed x \<and>
    term_formed c \<and> (505,Pair_Term (Pair_Term y a) b)\<in>positive_meaning payload_audit_system"
  then obtain x y c a b where parts: "z=Pair_Term (Pair_Term x (Pair_Term y c)) (Pair_Term a b)"
    "term_formed x" "term_formed c" "(505,Pair_Term (Pair_Term y a) b)\<in>positive_meaning payload_audit_system"
    by blast
  have operands: "term_formed y" "term_formed a" "term_formed b"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(4)]] by simp_all
  show "(522,z)\<in>positive_meaning first_problem_goals_system" unfolding view
    by (rule exI[of _ "\<lambda>n::nat. if n=0 then x else if n=1 then y else if n=2 then c else if n=3 then a else b"])
      (use parts operands in \<open>auto simp: audit_callee_schema_def schema_variables_def
        first_problem_goals_components\<close>)
  qed
qed

theorem retention_goal_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(520,Pair_Term t w)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> environment_included E F"
proof -
  obtain e where e: "environment_value_presents E e" "t=Pair_Term e (site_data_term u r)"
    using first by (auto simp: site_value_presents_def)
  obtain f where f: "environment_value_presents F f" "w=Pair_Term f (site_data_term v s)"
    using second by (auto simp: site_value_presents_def)
  have data: "term_formed (site_data_term u r)" "term_formed (site_data_term v s)"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] e(2) f(2) by simp_all
  have inclusion: "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow> environment_included E F"
    by (rule environment_inclusion_on_values[OF e(1) f(1)])
  show ?thesis using data by (auto simp: retention_goal_rule e(2) f(2) inclusion)
qed

theorem formation_goal_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(521,Pair_Term t w)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow> (\<exists>R. native_package_at F v s R)"
proof -
  obtain f where f: "environment_value_presents F f" "w=Pair_Term f (site_data_term v s)"
    using second by (auto simp: site_value_presents_def)
  have formed: "term_formed t" using site_value_presents_formed[OF first] by blast
  have admission: "(80,Pair_Term (Pair_Term f (use_data_term v)) (Payload_Term s))
      \<in>positive_meaning package_admission_system \<longleftrightarrow> (\<exists>R. native_package_at F v s R)"
    by (rule package_admission_on_values[OF f(1)])
  show ?thesis by (auto simp: formation_goal_rule f(2) site_data_term_def admission formed)
qed

theorem boundary_goal_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(392,Pair_Term t w)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E))"
  by (simp only: first_problem_goals_components(4) use_additions_on_values[OF first second])

lemma audit_callee_at_site:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(522,Pair_Term (Pair_Term t w) (definition_site_value d))\<in>positive_meaning first_problem_goals_system
    \<longleftrightarrow> (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})"
proof -
  obtain f where f: "environment_value_presents F f" "w=Pair_Term f (site_data_term v s)"
    using second by (auto simp: site_value_presents_def)
  have formed: "term_formed t" "term_formed (site_data_term v s)"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] f(2) by simp_all
  have audit: "(505,Pair_Term (Pair_Term f (use_data_term (fst d))) (Payload_Term (snd d)))
      \<in>positive_meaning payload_audit_system \<longleftrightarrow>
    (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})"
    by (rule payload_audit_on_values[OF f(1)])
  show ?thesis
    using formed audit by (auto simp: audit_callee_rule f(2) site_data_term_def)
qed

theorem audit_goal_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(525,Pair_Term t w)\<in>positive_meaning first_problem_goals_system \<longleftrightarrow>
    (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
  by (simp only: audit_additions.on_values[OF first second] audit_callee_at_site[OF first second])

text \<open>
  G4 is the callee boundary's instance at the audit's relation: the audit of the member's definition in
  the candidate's environment is kept by the audit's clause (@{thm [source] payload_audit_renamed}), so the
  goal is invariant along every renaming correspondence of the pair (@{thm [source]
  package_additions_profile.renaming}).
\<close>

lemma audit_callee_equivariant:
  "renaming_equivariant bij package_additions_callee_renaming
    (\<lambda>x. (site_context_formed (fst (fst x)) \<and> site_context_formed (snd (fst x))) \<and> True)
    (package_additions_callee_relation
      (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))"
  by (auto simp: renaming_equivariant_def product_action_def payload_audit_renamed)

corollary audit_goal_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence
      (factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
        (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)) package_additions_renaming h) (=)
    (\<lambda>p. (525,p)\<in>positive_meaning first_problem_goals_system) (\<lambda>p. (525,p)\<in>positive_meaning first_problem_goals_system)"
  by (rule audit_additions.renaming[OF audit_callee_equivariant]) (rule audit_callee_at_site; assumption)

section \<open>The guard: four sockets, each a separate requirement on the whole pair\<close>

definition first_problem_requirements :: "(nat\<times>nat) set" where
  "first_problem_requirements={(0,520),(1,521),(2,392),(3,525)}"

interpretation first_problem_guard:
  requirement_guard_extension first_problem_goals_system 526 first_problem_requirements
proof
  show "schema_system_formed first_problem_goals_system" by simp
  show "526\<notin>system_definitions first_problem_goals_system" using guard_fresh[of 526] by simp
  show "finite first_problem_requirements" by (simp add: first_problem_requirements_def)
  show "single_valued first_problem_requirements"
    by (auto simp: first_problem_requirements_def single_valued_def)
  show "rel_ran first_problem_requirements\<subseteq>system_definitions first_problem_goals_system"
    using guard_reader_sites by (auto simp: first_problem_requirements_def rel_ran_def)
qed

abbreviation first_problem_guard_system :: "(nat,nat,nat,nat) schema_system" where
  "first_problem_guard_system\<equiv>install_requirement_guard first_problem_goals_system 526 first_problem_requirements"

lemma goal_sites:
  "520\<in>system_definitions first_problem_goals_system" "521\<in>system_definitions first_problem_goals_system"
  "392\<in>system_definitions first_problem_goals_system" "525\<in>system_definitions first_problem_goals_system"
  using guard_reader_sites by auto

theorem guard_socket_meanings:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(520,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow> environment_included E F"
    and "(521,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow> (\<exists>R. native_package_at F v s R)"
    and "(392,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
      (\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          fst d\<notin>environment_uses E))"
    and "(525,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
      (\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
  by (simp_all only: first_problem_guard.unchanged_original_meaning[OF goal_sites(1)]
    first_problem_guard.unchanged_original_meaning[OF goal_sites(2)]
    first_problem_guard.unchanged_original_meaning[OF goal_sites(3)]
    first_problem_guard.unchanged_original_meaning[OF goal_sites(4)]
    retention_goal_on_values[OF first second] formation_goal_on_values[OF first second]
    boundary_goal_on_values[OF first second] audit_goal_on_values[OF first second])

theorem first_problem_guard_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
    environment_included E F \<and> (\<exists>R. native_package_at F v s R) \<and>
    (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E)) \<and>
    (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
proof -
  have formed: "term_formed (Pair_Term t w)"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] by simp
  have exact: "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow> term_formed (Pair_Term t w) \<and>
      (\<forall>(s,d)\<in>first_problem_requirements. (d,Pair_Term t w)\<in>positive_meaning first_problem_guard_system)"
    by (rule first_problem_guard.guard.exact)
  have sockets: "(\<forall>(s,d)\<in>first_problem_requirements. (d,Pair_Term t w)\<in>positive_meaning first_problem_guard_system)
      \<longleftrightarrow> (520,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
        (521,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
        (392,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
        (525,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    by (auto simp: first_problem_requirements_def)
  show ?thesis
    by (simp only: exact sockets guard_socket_meanings[OF first second] formed simp_thms)
qed

text \<open>A failing goal refuses the guard, and the socket that failed is named.\<close>

theorem first_problem_guard_refusal:
  assumes "(s,g)\<in>first_problem_requirements" "(g,t)\<notin>positive_meaning first_problem_guard_system"
  shows "(526,t)\<notin>positive_meaning first_problem_guard_system"
  by (rule first_problem_guard.guard.failed_requirement[OF assms])

corollary first_problem_guard_refusals:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "\<not>environment_included E F \<Longrightarrow> (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    and "\<not>(\<exists>R. native_package_at F v s R) \<Longrightarrow> (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    and "\<not>(\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          fst d\<notin>environment_uses E)) \<Longrightarrow>
      (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    and "\<not>(\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))) \<Longrightarrow>
      (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
proof -
  have sockets: "(0,520)\<in>first_problem_requirements" "(1,521)\<in>first_problem_requirements"
    "(2,392)\<in>first_problem_requirements" "(3,525)\<in>first_problem_requirements"
    by (simp_all add: first_problem_requirements_def)
  show "\<not>environment_included E F \<Longrightarrow> (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    using first_problem_guard_refusal[OF sockets(1)] guard_socket_meanings(1)[OF first second] by blast
  show "\<not>(\<exists>R. native_package_at F v s R) \<Longrightarrow> (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    using first_problem_guard_refusal[OF sockets(2)] guard_socket_meanings(2)[OF first second] by blast
  show "\<not>(\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          fst d\<notin>environment_uses E)) \<Longrightarrow>
      (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    using first_problem_guard_refusal[OF sockets(3)] guard_socket_meanings(3)[OF first second] by blast
  show "\<not>(\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))) \<Longrightarrow>
      (526,Pair_Term t w)\<notin>positive_meaning first_problem_guard_system"
    using first_problem_guard_refusal[OF sockets(4)] guard_socket_meanings(4)[OF first second] by blast
qed

section \<open>The contract in the words of the requirement\<close>

lemma given_member_use:
  assumes package: "native_package_at E u r Q" and member: "d\<in>system_definitions Q"
  shows "fst d\<in>environment_uses E"
proof -
  obtain Z where raw: "native_root_family_at E u r Z" "native_package_formed E (rel_ran Z)"
    using package by (auto simp: native_package_at_def)
  have "d\<in>native_definition_sites E (rel_ran Z)" using member native_package_complete_roots[OF package raw(1)] by simp
  then obtain p C where "native_definition_at E (fst d) (snd d) p C"
    using raw(2) by (auto simp: native_package_formed_def)
  then have "(fst d,snd d)\<in>environment_positions E" by (rule native_definition_position)
  then show ?thesis by (auto simp: environment_positions_def environment_uses_def rel_dom_def artifact_at_def)
qed

theorem first_problem_guard_contract:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
    environment_included E F \<and> (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
proof -
  let ?given="\<lambda>d. \<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q"
  let ?audited="\<lambda>d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}"
  have unique: "R=R'" if "native_package_at F v s R" "native_package_at F v s R'" for R R'
    using native_package_unique[OF that] by simp
  have used: "fst d\<in>environment_uses E" if "?given d" for d
  proof -
    from that obtain Q where "native_package_at E u r Q" "d\<in>system_definitions Q" by blast
    then show ?thesis by (rule given_member_use)
  qed
  show ?thesis
  proof
    assume "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    then have included: "environment_included E F"
      and bounded: "\<exists>R. native_package_at F v s R \<and>
        (\<forall>d\<in>system_definitions R. ?given d \<or> fst d\<notin>environment_uses E)"
      and audited: "\<exists>R. native_package_at F v s R \<and> (\<forall>d\<in>system_definitions R. ?given d \<or> ?audited d)"
      using first_problem_guard_on_values[OF first second] by blast+
    obtain R where R: "native_package_at F v s R"
      "\<forall>d\<in>system_definitions R. ?given d \<or> fst d\<notin>environment_uses E"
      using bounded by blast
    obtain R' where R': "native_package_at F v s R'" "\<forall>d\<in>system_definitions R'. ?given d \<or> ?audited d"
      using audited by blast
    have same: "R'=R" by (rule unique[OF R'(1) R(1)])
    have "\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow> ?audited d"
      using R'(2) used unfolding same by blast
    then show "environment_included E F \<and> (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. ?given d \<or> fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow> ?audited d))"
      using included R by blast
  next
    assume "environment_included E F \<and> (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. ?given d \<or> fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow> ?audited d))"
    then obtain R where included: "environment_included E F" and R: "native_package_at F v s R"
      "\<forall>d\<in>system_definitions R. ?given d \<or> fst d\<notin>environment_uses E"
      "\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow> ?audited d" by blast
    have "\<forall>d\<in>system_definitions R. ?given d \<or> ?audited d" using R(2,3) by blast
    then show "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
      using first_problem_guard_on_values[OF first second] included R(1,2) by blast
  qed
qed

corollary first_problem_guard_invariance:
  assumes "site_value_presents E u r t" "site_value_presents E u r t'"
    "site_value_presents F v s w" "site_value_presents F v s w'"
  shows "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
    (526,Pair_Term t' w')\<in>positive_meaning first_problem_guard_system"
  by (simp only: first_problem_guard_on_values[OF assms(1,3)] first_problem_guard_on_values[OF assms(2,4)])

section \<open>The payloads the guard states\<close>

lemma first_problem_guard_leaves:
  "schema_leaves retention_goal_schema={}" "schema_leaves formation_goal_schema={}"
  "schema_leaves audit_callee_schema={}" "schema_leaves (requirement_guard_schema first_problem_requirements)={}"
  by (simp_all add: schema_leaves_def material_leaves_def retention_goal_schema_def formation_goal_schema_def
    audit_callee_schema_def requirement_guard_schema_def first_problem_requirements_def)

text \<open>
  The guard's own schemas state no leaf; the second instance of the additions notion states what its
  schemas do (@{thm [source] package_additions_leaves}): nothing, but the empty payload terminating the
  context list. The payloads the guard reads beyond these are its readers', stated and judged where each
  reader was proved: the audit's are the empty payload alone (@{thm [source] payload_audit_own_payloads}).
  Sites are compared for equality; an address stays an inert payload, a use is structure.

  The pair's members are site values, an environment and a package site, and nothing more; the given's is
  first. G3 and G4 read one closure bound of the candidate's package each, in their own rules. The contract
  holds for any pair: exactly when the candidate's environment includes the given's, the candidate's site
  holds a native package, every definition of that package is the given's or stands at a use of no artifact
  of the given's environment, and every definition at such a use states no payload but the empty one; a
  refusal names its socket, and the verdict is the same at every presentation of both site values.
\<close>

end
