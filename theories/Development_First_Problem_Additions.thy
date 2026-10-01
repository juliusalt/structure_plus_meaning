theory Development_First_Problem_Additions
  imports Development_First_Problem_Guard Factor_Extension_Packages
begin

text \<open>
  The first problem's asked relation over additions (DECISIONS.md, task 928's entry, course (c)): the
  requirement guard with four sockets on the pair of the given's site value and the candidate's additions,
  every socket receiving the whole pair. Each socket reads the requirement of the guard over two site values
  (@{text Development_First_Problem_Guard}) at the given and its extension by the additions, and is exact to
  it there: G1, the extension's formation (AX1's reader), exact to retention; G2, the package at the
  candidate's site of the extension (AX2a's reader), exact to formation and closure; G3, the callee boundary,
  its added members read through the least environment and a bound of the package, each bound member a member
  of the given's package or an added definition standing at a use of no given artifact; G4, the octet audit,
  each bound member a member of the given's package or a definition, read in the least environment or at the
  given's value, stating no payload but the empty one. A judgment reads the candidate's additions and the
  given's value; nothing of the given is read again beyond the calls the table holds. A refusal names its socket.
\<close>

section \<open>The readers the goals call, joined where they agree\<close>

lemma call_admission_complete_definitions:
  "system_definitions definition_call_admission_system\<subseteq>system_definitions complete_data_admission_system"
  by (rule whole_agreement_definitions[OF call_admission_complete_data_agreement])

lemma extension_formation_sites:
  "system_definitions extension_formation_system={950,951,952,953,954}\<union>system_definitions artifact_lookup_system"
  by auto

lemma extension_package_sites:
  "system_definitions extension_package_system=
    {955,956,957,958,959,960,961,962,963,964,965,966}\<union>system_definitions package_membership_system\<union>
      system_definitions extension_formation_system"
  by auto

lemma payload_audit_sites:
  "system_definitions payload_audit_system={500,501,502,503,504,505}\<union>system_definitions definition_call_admission_system"
  by (auto simp: payload_audit_definitions clause_family_payloads_definitions clause_payloads_definitions
    empty_payload_calls_definitions empty_payload_rows_definitions empty_payloads_definitions)

lemma additions_number_facts:
  "{950,951,952,953,954}\<inter>{..<390::nat}={}" "{955,956,957,958,959,960,961,962,963,964,965,966}\<inter>{..<390::nat}={}"
  "{500,501,502,503,504,505}\<inter>{..<390::nat}={}" "{950,951,952,953,954}\<inter>{955,956,957,958,959,960,961,962,963,964,965,966::nat}={}"
  "{950,951,952,953,954}\<inter>{500,501,502,503,504,505::nat}={}"
  "{955,956,957,958,959,960,961,962,963,964,965,966}\<inter>{500,501,502,503,504,505::nat}={}"
  "{950,951,952,953,954}\<subseteq>{..<970::nat}" "{955,956,957,958,959,960,961,962,963,964,965,966}\<subseteq>{..<970::nat}"
  "{..<390::nat}\<subseteq>{..<970}" "{..<506::nat}\<subseteq>{..<970}"
  "{980,981,982,983,984,985,986,987,988,989,990,991,992}\<inter>{..<970::nat}={}"
  by auto

lemma membership_package_agreement:
  "systems_agree_on package_membership_system extension_package_system (system_definitions package_membership_system)"
  by (rule systems_agree_on_transitive[OF system_union_agree_left[OF extension_formation_system_formed
    membership_formation_agreement, folded extension_readers_base_system_def]
    systems_agree_on_subdomain[OF extension_package_base_agreement]]) simp

lemma complete_package_agreement:
  "systems_agree_on complete_data_admission_system extension_package_system
    (system_definitions complete_data_admission_system\<inter>system_definitions extension_package_system)"
proof -
  have union: "systems_agree_on extension_readers_base_system complete_data_admission_system
      (system_definitions extension_readers_base_system\<inter>system_definitions complete_data_admission_system)"
    unfolding extension_readers_base_system_def
    by (rule overlap_agreement_union[OF package_membership_system_formed extension_formation_system_formed])
      (rule systems_agree_on_subdomain[OF membership_complete_data_agreement], blast,
       rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF complete_formation_agreement]], blast)
  show ?thesis
    by (rule systems_agree_on_transitive[OF systems_agree_on_subdomain[OF systems_agree_on_sym[OF union]]
      systems_agree_on_subdomain[OF extension_package_base_agreement]])
      (use complete_below in auto)
qed

lemma complete_audit_agreement:
  "systems_agree_on complete_data_admission_system payload_audit_system
    (system_definitions complete_data_admission_system\<inter>system_definitions payload_audit_system)"
proof (rule systems_agree_on_subdomain[OF systems_agree_on_transitive[OF
    systems_agree_on_sym[OF call_admission_complete_data_agreement] call_admission_audit_agreement]])
  show "system_definitions complete_data_admission_system\<inter>system_definitions payload_audit_system\<subseteq>
      system_definitions definition_call_admission_system"
    using complete_below additions_number_facts(3) by (simp only: payload_audit_sites) blast
qed

lemma additions_overlap_cover:
  assumes "A\<subseteq>C" "B\<subseteq>C" "N\<inter>M={}"
  shows "(N\<union>A)\<inter>(M\<union>B)\<subseteq>C"
  using assms by blast

lemma formation_package_agreement:
  "systems_agree_on extension_formation_system extension_package_system
    (system_definitions extension_formation_system\<inter>system_definitions extension_package_system)"
  by (rule systems_agree_on_subdomain[OF systems_agree_on_transitive[OF system_union_agree_right[OF
    package_membership_system_formed membership_formation_agreement, folded extension_readers_base_system_def]
    systems_agree_on_subdomain[OF extension_package_base_agreement]]]) auto

lemma formation_audit_agreement:
  "systems_agree_on extension_formation_system payload_audit_system
    (system_definitions extension_formation_system\<inter>system_definitions payload_audit_system)"
proof (rule common_component_overlap_agreement[OF complete_formation_agreement complete_audit_agreement])
  show "system_definitions extension_formation_system\<inter>system_definitions payload_audit_system\<subseteq>
      system_definitions complete_data_admission_system"
    unfolding extension_formation_sites payload_audit_sites
    by (rule additions_overlap_cover[OF lookup_complete_definitions call_admission_complete_definitions
      additions_number_facts(5)])
qed

lemma package_audit_agreement:
  "systems_agree_on extension_package_system payload_audit_system
    (system_definitions extension_package_system\<inter>system_definitions payload_audit_system)"
proof (rule common_component_overlap_agreement[OF complete_package_agreement complete_audit_agreement])
  show "system_definitions extension_package_system\<inter>system_definitions payload_audit_system\<subseteq>
      system_definitions complete_data_admission_system"
    unfolding extension_package_sites payload_audit_sites
    using membership_complete_definitions lookup_complete_definitions call_admission_complete_definitions complete_below
    by auto
qed

definition additions_pair_readers_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_pair_readers_system=system_union extension_formation_system extension_package_system"

definition additions_readers_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_readers_system=system_union additions_pair_readers_system payload_audit_system"

lemma additions_pair_readers_formed [simp]: "schema_system_formed additions_pair_readers_system"
  unfolding additions_pair_readers_system_def
  by (rule system_union_agree_formed[OF extension_formation_system_formed extension_package_system_formed
    formation_package_agreement])

lemma pair_audit_agreement:
  "systems_agree_on additions_pair_readers_system payload_audit_system
    (system_definitions additions_pair_readers_system\<inter>system_definitions payload_audit_system)"
  unfolding additions_pair_readers_system_def
  by (rule overlap_agreement_union[OF extension_formation_system_formed extension_package_system_formed
    formation_audit_agreement package_audit_agreement])

lemma additions_readers_formed [simp]: "schema_system_formed additions_readers_system"
  unfolding additions_readers_system_def
  by (rule system_union_agree_formed[OF additions_pair_readers_formed payload_audit_system_formed pair_audit_agreement])

lemma additions_readers_definitions:
  "system_definitions additions_readers_system=system_definitions extension_formation_system\<union>
    system_definitions extension_package_system\<union>system_definitions payload_audit_system"
  by (simp add: additions_readers_system_def additions_pair_readers_system_def)

lemma additions_pair_readers_call:
  "schema_call_formed additions_pair_readers_system d t \<longleftrightarrow>
    d\<in>system_definitions additions_pair_readers_system \<and> term_formed t"
  unfolding additions_pair_readers_system_def
  by (simp only: system_union_agree_call[OF extension_formation_system_formed extension_package_system_formed
    formation_package_agreement] extension_formation_call extension_package_call system_union_definitions Un_iff) blast

lemma additions_readers_call:
  "schema_call_formed additions_readers_system d t \<longleftrightarrow> d\<in>system_definitions additions_readers_system \<and> term_formed t"
  unfolding additions_readers_system_def
  by (simp only: system_union_agree_call[OF additions_pair_readers_formed payload_audit_system_formed
    pair_audit_agreement] additions_pair_readers_call payload_audit_call system_union_definitions Un_iff) blast

lemma additions_readers_formation:
  assumes member: "d\<in>system_definitions extension_formation_system"
  shows "(d,t)\<in>positive_meaning additions_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_formation_system"
proof -
  have pair: "d\<in>system_definitions additions_pair_readers_system"
    using member by (simp only: additions_pair_readers_system_def system_union_definitions Un_iff) blast
  show ?thesis
    using system_union_agree_left_locality(2)[OF additions_pair_readers_formed payload_audit_system_formed
      pair_audit_agreement pair, of t]
      system_union_agree_left_locality(2)[OF extension_formation_system_formed extension_package_system_formed
      formation_package_agreement member, of t]
    by (simp add: additions_readers_system_def additions_pair_readers_system_def)
qed

lemma additions_readers_package:
  assumes member: "d\<in>system_definitions extension_package_system"
  shows "(d,t)\<in>positive_meaning additions_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_package_system"
proof -
  have pair: "d\<in>system_definitions additions_pair_readers_system"
    using member by (simp only: additions_pair_readers_system_def system_union_definitions Un_iff) blast
  show ?thesis
    using system_union_agree_left_locality(2)[OF additions_pair_readers_formed payload_audit_system_formed
      pair_audit_agreement pair, of t]
      system_union_agree_right_locality(2)[OF extension_formation_system_formed extension_package_system_formed
      formation_package_agreement member, of t]
    by (simp add: additions_readers_system_def additions_pair_readers_system_def)
qed

lemma additions_readers_audit:
  assumes member: "d\<in>system_definitions payload_audit_system"
  shows "(d,t)\<in>positive_meaning additions_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning payload_audit_system"
  using system_union_agree_right_locality(2)[OF additions_pair_readers_formed payload_audit_system_formed
    pair_audit_agreement member, of t]
  by (simp add: additions_readers_system_def)

lemma additions_package_reader_sites: "{957,961,79,47,76,83}\<subseteq>system_definitions extension_package_system"
  by simp

lemma additions_reader_sites:
  "{950,954,957,961,79,47,76,83,505}\<subseteq>system_definitions additions_readers_system"
proof -
  have "505\<in>system_definitions payload_audit_system" by simp
  then show ?thesis using additions_package_reader_sites by (auto simp: additions_readers_definitions)
qed

lemma additions_readers_below: "system_definitions additions_readers_system\<subseteq>{..<970}"
proof -
  have lookup: "system_definitions artifact_lookup_system\<subseteq>{..<970}"
    by (rule subset_trans[OF subset_trans[OF lookup_complete_definitions complete_below] additions_number_facts(9)])
  have membership: "system_definitions package_membership_system\<subseteq>{..<970}"
    by (rule subset_trans[OF subset_trans[OF membership_complete_definitions complete_below] additions_number_facts(9)])
  have audit: "system_definitions payload_audit_system\<subseteq>{..<970}"
    by (rule subset_trans[OF audit_below additions_number_facts(10)])
  show ?thesis
    using lookup membership audit additions_number_facts(7,8)
    by (simp only: additions_readers_definitions extension_formation_sites extension_package_sites Un_subset_iff)
qed

lemma additions_fresh:
  assumes "d\<in>{980,981,982,983,984,985,986,987,988,989,990,991,992}"
  shows "d\<notin>system_definitions additions_readers_system"
  using assms additions_readers_below additions_number_facts(11) by blast

section \<open>The goals over the pair of the given's site value and the additions\<close>

text \<open>
  G1 and G2 are views: G1 passes AX1's reader the given's environment value and the additions, G2 passes AX2a's
  reader the given's site value read as a source and root, and the additions. G3 and G4 read the candidate's
  package through the witnesses its reader hands in: at a site of an added use, the least environment (957) and
  the root family read there (79); at a site of a given use, the root family read at the given's value; in both,
  a bound of the package holding the roots (47). Every bound member is checked by the notion of additions'
  element (@{const addition_element_clauses}): a member of the given's package (83) or the callee. G3's callee is
  a definition read in the environment the family was read in, its callees in the bound, at a use absent among
  the given's use keys (950, key absence against the given's artifact table). G4's callee is a definition, read
  there or at the given's value, its callees in the bound, stating no payload but the empty one (505). At a site
  of an added use the members clause reads the least environment and a view of it (991 for G3, 992 for G4) whose
  clause reads the root family and the bound, so that each premise holding a witness has no other free variable
  (task 961, the planner's q180). The numbers 980 to 992 are above every numbered site of the readers.
\<close>

definition additions_retention_schema :: "(nat,nat,nat) factor_schema" where
  "additions_retention_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,954,Pattern_Pair data_x data_z)}"

definition additions_package_schema :: "(nat,nat,nat) factor_schema" where
  "additions_package_schema=data_rule (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) data_w)
    {(0,961,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) data_w)}"

abbreviation additions_context_pattern :: "nat term_pattern" where
  "additions_context_pattern \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))"

definition additions_boundary_callee_schema :: "(nat,nat,nat) factor_schema" where
  "additions_boundary_callee_schema=data_rule (Pattern_Pair additions_context_pattern (Pattern_Variable 6))
    {(0,76,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))
        (Pattern_Pair (Pattern_Variable 6) (Pattern_Payload []))),
     (1,950,Pattern_Pair data_x (Pattern_Variable 6))}"

definition additions_audit_read_schema :: "(nat,nat,nat) factor_schema" where
  "additions_audit_read_schema=data_rule
    (Pattern_Pair additions_context_pattern (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))
    {(0,76,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Payload []))),
     (1,505,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 6)) (Pattern_Variable 7))}"

definition additions_audit_given_schema :: "(nat,nat,nat) factor_schema" where
  "additions_audit_given_schema=data_rule
    (Pattern_Pair additions_context_pattern (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))
    {(0,76,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 5))
        (Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Payload []))),
     (1,505,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 6)) (Pattern_Variable 7))}"

definition additions_audit_callee_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "additions_audit_callee_clauses={(0,additions_audit_read_schema),(1,additions_audit_given_schema)}"

abbreviation additions_pair_pattern :: "nat term_pattern" where
  "additions_pair_pattern \<equiv> Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    (Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))
      (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))"

definition additions_members_view_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "additions_members_view_schema list_site=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
      (Pattern_Variable 8)) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))
    {(0,79,citation_observation_pattern (Pattern_Variable 8) (Pattern_Variable 6) (Pattern_Variable 7)
        (Pattern_Variable 9)),
     (1,47,Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)),
     (2,list_site,Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
        (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10))) (Pattern_Variable 10))}"

definition additions_members_added_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "additions_members_added_schema view_site=data_rule additions_pair_pattern
    {(0,957,Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y)
        (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))) (Pattern_Variable 8)),
     (1,view_site,Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
        (Pattern_Variable 8)) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))}"

definition additions_members_given_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "additions_members_given_schema list_site=data_rule additions_pair_pattern
    {(0,79,citation_observation_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 6) (Pattern_Variable 7)
        (Pattern_Variable 9)),
     (1,47,Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)),
     (2,list_site,Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
        (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Variable 10))) (Pattern_Variable 10))}"

definition additions_members_clauses :: "nat \<Rightarrow> nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "additions_members_clauses view_site list_site=
    {(0,additions_members_added_schema view_site),(1,additions_members_given_schema list_site)}"

definition additions_retention_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_retention_system=add_view_definition additions_readers_system 980 data_x {(0,additions_retention_schema)}"

definition additions_package_goal_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_package_goal_system=add_view_definition additions_retention_system 981 data_x {(0,additions_package_schema)}"

definition additions_boundary_callee_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_boundary_callee_system=
    add_view_definition additions_package_goal_system 982 data_x {(0,additions_boundary_callee_schema)}"

definition additions_boundary_element_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_boundary_element_system=
    add_view_definition additions_boundary_callee_system 983 data_x (addition_element_clauses 982)"

definition additions_boundary_list_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_boundary_list_system=
    add_view_definition additions_boundary_element_system 984 data_x (context_list_clauses 983 984)"

definition additions_boundary_view_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_boundary_view_system=
    add_view_definition additions_boundary_list_system 991 data_x {(0,additions_members_view_schema 984)}"

definition additions_boundary_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_boundary_system=
    add_view_definition additions_boundary_view_system 985 data_x (additions_members_clauses 991 984)"

definition additions_audit_callee_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_audit_callee_system=add_view_definition additions_boundary_system 986 data_x additions_audit_callee_clauses"

definition additions_audit_element_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_audit_element_system=
    add_view_definition additions_audit_callee_system 987 data_x (addition_element_clauses 986)"

definition additions_audit_list_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_audit_list_system=
    add_view_definition additions_audit_element_system 988 data_x (context_list_clauses 987 988)"

definition additions_audit_view_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_audit_view_system=
    add_view_definition additions_audit_list_system 992 data_x {(0,additions_members_view_schema 988)}"

definition additions_goals_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_goals_system=add_view_definition additions_audit_view_system 989 data_x (additions_members_clauses 992 988)"

lemma additions_retention_system_formed [simp]: "schema_system_formed additions_retention_system"
  unfolding additions_retention_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_readers_formed])
    (auto simp: additions_retention_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def additions_fresh)

lemma additions_retention_definitions [simp]:
  "system_definitions additions_retention_system=insert 980 (system_definitions additions_readers_system)"
  by (simp add: additions_retention_system_def)

lemma additions_package_goal_system_formed [simp]: "schema_system_formed additions_package_goal_system"
  unfolding additions_package_goal_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_retention_system_formed])
    (auto simp: additions_package_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def additions_fresh)

lemma additions_package_goal_definitions [simp]:
  "system_definitions additions_package_goal_system=insert 981 (system_definitions additions_retention_system)"
  by (simp add: additions_package_goal_system_def)

lemma additions_boundary_callee_system_formed [simp]: "schema_system_formed additions_boundary_callee_system"
  unfolding additions_boundary_callee_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_package_goal_system_formed])
    (auto simp: additions_boundary_callee_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def additions_fresh)

lemma additions_boundary_callee_definitions [simp]:
  "system_definitions additions_boundary_callee_system=insert 982 (system_definitions additions_package_goal_system)"
  by (simp add: additions_boundary_callee_system_def)

lemma additions_boundary_element_system_formed [simp]: "schema_system_formed additions_boundary_element_system"
  unfolding additions_boundary_element_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_boundary_callee_system_formed])
    (auto simp: addition_element_clauses_def addition_member_schema_def addition_callee_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_boundary_element_definitions [simp]:
  "system_definitions additions_boundary_element_system=insert 983 (system_definitions additions_boundary_callee_system)"
  by (simp add: additions_boundary_element_system_def)

lemma additions_boundary_list_system_formed [simp]: "schema_system_formed additions_boundary_list_system"
  unfolding additions_boundary_list_system_def
  by (rule add_recursive_definition_formed[OF additions_boundary_element_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      additions_fresh)

lemma additions_boundary_list_definitions [simp]:
  "system_definitions additions_boundary_list_system=insert 984 (system_definitions additions_boundary_element_system)"
  by (simp add: additions_boundary_list_system_def)

lemma additions_boundary_view_system_formed [simp]: "schema_system_formed additions_boundary_view_system"
  unfolding additions_boundary_view_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_boundary_list_system_formed])
    (auto simp: additions_members_view_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_boundary_view_definitions [simp]:
  "system_definitions additions_boundary_view_system=insert 991 (system_definitions additions_boundary_list_system)"
  by (simp add: additions_boundary_view_system_def)

lemma additions_boundary_system_formed [simp]: "schema_system_formed additions_boundary_system"
  unfolding additions_boundary_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_boundary_view_system_formed])
    (auto simp: additions_members_clauses_def additions_members_added_schema_def additions_members_given_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_boundary_definitions [simp]:
  "system_definitions additions_boundary_system=insert 985 (system_definitions additions_boundary_view_system)"
  by (simp add: additions_boundary_system_def)

lemma additions_audit_callee_system_formed [simp]: "schema_system_formed additions_audit_callee_system"
  unfolding additions_audit_callee_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_boundary_system_formed])
    (auto simp: additions_audit_callee_clauses_def additions_audit_read_schema_def additions_audit_given_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      additions_fresh)

lemma additions_audit_callee_definitions [simp]:
  "system_definitions additions_audit_callee_system=insert 986 (system_definitions additions_boundary_system)"
  by (simp add: additions_audit_callee_system_def)

lemma additions_audit_element_system_formed [simp]: "schema_system_formed additions_audit_element_system"
  unfolding additions_audit_element_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_audit_callee_system_formed])
    (auto simp: addition_element_clauses_def addition_member_schema_def addition_callee_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_audit_element_definitions [simp]:
  "system_definitions additions_audit_element_system=insert 987 (system_definitions additions_audit_callee_system)"
  by (simp add: additions_audit_element_system_def)

lemma additions_audit_list_system_formed [simp]: "schema_system_formed additions_audit_list_system"
  unfolding additions_audit_list_system_def
  by (rule add_recursive_definition_formed[OF additions_audit_element_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def
      additions_fresh)

lemma additions_audit_list_definitions [simp]:
  "system_definitions additions_audit_list_system=insert 988 (system_definitions additions_audit_element_system)"
  by (simp add: additions_audit_list_system_def)

lemma additions_audit_view_system_formed [simp]: "schema_system_formed additions_audit_view_system"
  unfolding additions_audit_view_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_audit_list_system_formed])
    (auto simp: additions_members_view_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_audit_view_definitions [simp]:
  "system_definitions additions_audit_view_system=insert 992 (system_definitions additions_audit_list_system)"
  by (simp add: additions_audit_view_system_def)

lemma additions_goals_formed [simp]: "schema_system_formed additions_goals_system"
  unfolding additions_goals_system_def
  using additions_reader_sites
  by (intro add_recursive_definition_formed[OF additions_audit_view_system_formed])
    (auto simp: additions_members_clauses_def additions_members_added_schema_def additions_members_given_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def additions_fresh)

lemma additions_goals_definitions [simp]:
  "system_definitions additions_goals_system=insert 989 (system_definitions additions_audit_view_system)"
  by (simp add: additions_goals_system_def)

lemma additions_goals_call:
  "schema_call_formed additions_goals_system d t \<longleftrightarrow> d\<in>system_definitions additions_goals_system \<and> term_formed t"
proof -
  have retention: "schema_call_formed additions_retention_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_retention_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_readers_formed
      additions_retention_system_formed[unfolded additions_retention_system_def] additions_readers_call]
    by (simp only: additions_retention_system_def[symmetric])
  have package: "schema_call_formed additions_package_goal_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_package_goal_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_retention_system_formed
      additions_package_goal_system_formed[unfolded additions_package_goal_system_def] retention]
    by (simp only: additions_package_goal_system_def[symmetric])
  have bcallee: "schema_call_formed additions_boundary_callee_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_boundary_callee_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_package_goal_system_formed
      additions_boundary_callee_system_formed[unfolded additions_boundary_callee_system_def] package]
    by (simp only: additions_boundary_callee_system_def[symmetric])
  have belement: "schema_call_formed additions_boundary_element_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_boundary_element_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_boundary_callee_system_formed
      additions_boundary_element_system_formed[unfolded additions_boundary_element_system_def] bcallee]
    by (simp only: additions_boundary_element_system_def[symmetric])
  have blist: "schema_call_formed additions_boundary_list_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_boundary_list_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_boundary_element_system_formed
      additions_boundary_list_system_formed[unfolded additions_boundary_list_system_def] belement]
    by (simp only: additions_boundary_list_system_def[symmetric])
  have bview: "schema_call_formed additions_boundary_view_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_boundary_view_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_boundary_list_system_formed
      additions_boundary_view_system_formed[unfolded additions_boundary_view_system_def] blist]
    by (simp only: additions_boundary_view_system_def[symmetric])
  have boundary: "schema_call_formed additions_boundary_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_boundary_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_boundary_view_system_formed
      additions_boundary_system_formed[unfolded additions_boundary_system_def] bview]
    by (simp only: additions_boundary_system_def[symmetric])
  have acallee: "schema_call_formed additions_audit_callee_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_audit_callee_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_boundary_system_formed
      additions_audit_callee_system_formed[unfolded additions_audit_callee_system_def] boundary]
    by (simp only: additions_audit_callee_system_def[symmetric])
  have aelement: "schema_call_formed additions_audit_element_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_audit_element_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_audit_callee_system_formed
      additions_audit_element_system_formed[unfolded additions_audit_element_system_def] acallee]
    by (simp only: additions_audit_element_system_def[symmetric])
  have alist: "schema_call_formed additions_audit_list_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_audit_list_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_audit_element_system_formed
      additions_audit_list_system_formed[unfolded additions_audit_list_system_def] aelement]
    by (simp only: additions_audit_list_system_def[symmetric])
  have aview: "schema_call_formed additions_audit_view_system d t \<longleftrightarrow>
      d\<in>system_definitions additions_audit_view_system \<and> term_formed t" for d t
    using added_variable_calls[OF additions_audit_list_system_formed
      additions_audit_view_system_formed[unfolded additions_audit_view_system_def] alist]
    by (simp only: additions_audit_view_system_def[symmetric])
  show ?thesis
    using added_variable_calls[OF additions_audit_view_system_formed
      additions_goals_formed[unfolded additions_goals_system_def] aview]
    by (simp only: additions_goals_system_def[symmetric])
qed

lemma additions_goals_families:
  "((980,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_retention_schema"
  "((981,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_package_schema"
  "((982,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_boundary_callee_schema"
  "((983,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 982"
  "((984,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 983 984"
  "((985,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_members_clauses 991 984"
  "((986,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_audit_callee_clauses"
  "((987,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 986"
  "((988,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 987 988"
  "((989,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_members_clauses 992 988"
  "((991,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema 984"
  "((992,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema 988"
proof -
  have owned: "((d,c),S)\<in>system_clauses additions_readers_system \<Longrightarrow> d\<in>system_definitions additions_readers_system"
    for d c S
    using additions_readers_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses additions_readers_system"
    if "d\<in>{980,981,982,983,984,985,986,987,988,989,991,992}" for d c S
    using that additions_fresh[of d] owned by auto
  show "((980,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_retention_schema"
    "((981,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_package_schema"
    "((982,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_boundary_callee_schema"
    "((983,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 982"
    "((984,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 983 984"
    "((985,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_members_clauses 991 984"
    "((986,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_audit_callee_clauses"
    "((987,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses 986"
    "((988,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 987 988"
    "((989,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_members_clauses 992 988"
    "((991,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema 984"
    "((992,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema 988"
    using absent by (auto simp: additions_goals_system_def additions_audit_view_system_def additions_audit_list_system_def
      additions_audit_element_system_def additions_audit_callee_system_def additions_boundary_system_def
      additions_boundary_view_system_def
      additions_boundary_list_system_def additions_boundary_element_system_def additions_boundary_callee_system_def
      additions_package_goal_system_def additions_retention_system_def)
qed

lemma additions_goals_agreement:
  "systems_agree_on additions_readers_system additions_goals_system (system_definitions additions_readers_system)"
  using additions_fresh by (simp add: systems_agree_on_added additions_goals_system_def additions_audit_view_system_def
    additions_audit_list_system_def
    additions_audit_element_system_def additions_audit_callee_system_def additions_boundary_system_def
    additions_boundary_view_system_def
    additions_boundary_list_system_def additions_boundary_element_system_def additions_boundary_callee_system_def
    additions_package_goal_system_def additions_retention_system_def)

lemma additions_goals_lifted:
  assumes "d\<in>system_definitions additions_readers_system"
  shows "(d,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning additions_readers_system"
  using whole_system_agreement_meaning[OF additions_readers_formed additions_goals_formed additions_goals_agreement assms]
  by simp

lemma additions_goals_components:
  "(954,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (954,t)\<in>positive_meaning extension_formation_system"
  "(950,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (950,t)\<in>positive_meaning extension_formation_system"
  "(961,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (961,t)\<in>positive_meaning extension_package_system"
  "(957,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (957,t)\<in>positive_meaning extension_package_system"
  "(79,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(47,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(83,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
  "(505,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (505,t)\<in>positive_meaning payload_audit_system"
proof -
  have formation: "(d,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_formation_system"
    if "d\<in>system_definitions extension_formation_system" for d
  proof -
    have "d\<in>system_definitions additions_readers_system"
      using that by (simp only: additions_readers_definitions Un_iff) blast
    then show ?thesis using additions_goals_lifted[of d t] additions_readers_formation[OF that, of t] by blast
  qed
  have package: "(d,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_package_system"
    if "d\<in>system_definitions extension_package_system" for d
  proof -
    have "d\<in>system_definitions additions_readers_system"
      using that by (simp only: additions_readers_definitions Un_iff) blast
    then show ?thesis using additions_goals_lifted[of d t] additions_readers_package[OF that, of t] by blast
  qed
  have audit: "(d,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (d,t)\<in>positive_meaning payload_audit_system"
    if "d\<in>system_definitions payload_audit_system" for d
  proof -
    have "d\<in>system_definitions additions_readers_system"
      using that by (simp only: additions_readers_definitions Un_iff) blast
    then show ?thesis using additions_goals_lifted[of d t] additions_readers_audit[OF that, of t] by blast
  qed
  have sites: "957\<in>system_definitions extension_package_system" "961\<in>system_definitions extension_package_system"
    "79\<in>system_definitions extension_package_system" "47\<in>system_definitions extension_package_system"
    "76\<in>system_definitions extension_package_system" "83\<in>system_definitions extension_package_system"
    using additions_package_reader_sites by blast+
  show "(954,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (954,t)\<in>positive_meaning extension_formation_system"
    by (rule formation) simp
  show "(950,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (950,t)\<in>positive_meaning extension_formation_system"
    by (rule formation) simp
  show "(961,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (961,t)\<in>positive_meaning extension_package_system"
    by (rule package[OF sites(2)])
  show "(957,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (957,t)\<in>positive_meaning extension_package_system"
    by (rule package[OF sites(1)])
  show "(79,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
    using package[OF sites(3)] extension_package_components(6)[of t] by simp
  show "(47,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    using package[OF sites(4)] extension_package_components(3)[of t] by simp
  show "(76,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    using package[OF sites(5)] extension_package_components(4)[of t] by simp
  show "(83,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (83,t)\<in>positive_meaning package_membership_system"
    using package[OF sites(6)] extension_package_components(8)[of t] by simp
  show "(505,t)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (505,t)\<in>positive_meaning payload_audit_system"
    by (rule audit) simp
qed

lemma additions_goals_valuation:
  assumes "(d,t)\<in>positive_meaning additions_goals_system"
  shows "\<exists>c S f. ((d,c),S)\<in>system_clauses additions_goals_system \<and> (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning additions_goals_system)"
  using schema_consequences_valuationD[of d t additions_goals_system "positive_meaning additions_goals_system"]
    assms positive_meaning_unfold[of additions_goals_system] by blast

interpretation additions_boundary_lists: context_list_profile additions_goals_system 983 984
  by (rule context_list_profile.intro) (auto simp: additions_goals_call additions_goals_families)

interpretation additions_audit_lists: context_list_profile additions_goals_system 987 988
  by (rule context_list_profile.intro) (auto simp: additions_goals_call additions_goals_families)

subsection \<open>The raw readings of the new clauses\<close>

lemma additions_view_rule:
  assumes family: "\<And>c S. ((n,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=R"
    and ordinary: "schema_material_premises R={}"
  shows "(n,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables R. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion R) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises R \<longrightarrow> (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system))"
  by (rule variable_single_clause_valuation[OF additions_goals_formed family ordinary]) (simp add: additions_goals_call)

lemma additions_retention_rule:
  "(980,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>x y a. z=Pair_Term (Pair_Term x y) a \<and> term_formed y \<and>
    (954,Pair_Term x a)\<in>positive_meaning extension_formation_system)"
proof -
  have view: "(980,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables additions_retention_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion additions_retention_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises additions_retention_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system))"
    by (rule additions_view_rule[OF additions_goals_families(1)]) (simp add: additions_retention_schema_def)
  show ?thesis
  proof
    assume "(980,z)\<in>positive_meaning additions_goals_system"
    then obtain f where "\<forall>a\<in>schema_variables additions_retention_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion additions_retention_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises additions_retention_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
      using view by blast
    then show "\<exists>x y a. z=Pair_Term (Pair_Term x y) a \<and> term_formed y \<and>
      (954,Pair_Term x a)\<in>positive_meaning extension_formation_system"
      by (auto simp: additions_retention_schema_def schema_variables_def additions_goals_components)
  next
    assume "\<exists>x y a. z=Pair_Term (Pair_Term x y) a \<and> term_formed y \<and>
      (954,Pair_Term x a)\<in>positive_meaning extension_formation_system"
    then obtain x y a where parts: "z=Pair_Term (Pair_Term x y) a" "term_formed y"
      "(954,Pair_Term x a)\<in>positive_meaning extension_formation_system" by blast
    have operands: "term_formed x" "term_formed a"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by simp_all
    show "(980,z)\<in>positive_meaning additions_goals_system" unfolding view
      by (rule exI[of _ "\<lambda>n::nat. if n=0 then x else if n=1 then y else a"])
        (use parts operands in \<open>auto simp: additions_retention_schema_def schema_variables_def
          additions_goals_components\<close>)
  qed
qed

lemma additions_package_rule:
  "(981,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>x y w a. z=Pair_Term (Pair_Term x (Pair_Term y w)) a \<and>
    (961,Pair_Term (Pair_Term (Pair_Term x y) w) a)\<in>positive_meaning extension_package_system)"
proof -
  have view: "(981,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables additions_package_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion additions_package_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises additions_package_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system))"
    by (rule additions_view_rule[OF additions_goals_families(2)]) (simp add: additions_package_schema_def)
  show ?thesis
  proof
    assume "(981,z)\<in>positive_meaning additions_goals_system"
    then obtain f where "\<forall>a\<in>schema_variables additions_package_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion additions_package_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises additions_package_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
      using view by blast
    then show "\<exists>x y w a. z=Pair_Term (Pair_Term x (Pair_Term y w)) a \<and>
      (961,Pair_Term (Pair_Term (Pair_Term x y) w) a)\<in>positive_meaning extension_package_system"
      by (auto simp: additions_package_schema_def schema_variables_def additions_goals_components)
  next
    assume "\<exists>x y w a. z=Pair_Term (Pair_Term x (Pair_Term y w)) a \<and>
      (961,Pair_Term (Pair_Term (Pair_Term x y) w) a)\<in>positive_meaning extension_package_system"
    then obtain x y w a where parts: "z=Pair_Term (Pair_Term x (Pair_Term y w)) a"
      "(961,Pair_Term (Pair_Term (Pair_Term x y) w) a)\<in>positive_meaning extension_package_system" by blast
    have operands: "term_formed x" "term_formed y" "term_formed w" "term_formed a"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by simp_all
    show "(981,z)\<in>positive_meaning additions_goals_system" unfolding view
      by (rule exI[of _ "\<lambda>n::nat. if n=0 then x else if n=1 then y else if n=2 then w else a"])
        (use parts operands in \<open>auto simp: additions_package_schema_def schema_variables_def
          additions_goals_components\<close>)
  qed
qed

lemma additions_boundary_callee_rule:
  "(982,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>a0 a1 gu gr v k m.
    z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) m \<and>
    term_formed a1 \<and> term_formed gu \<and> term_formed gr \<and>
    (76,Pair_Term (Pair_Term v k) (Pair_Term m (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<and>
    (950,Pair_Term a0 m)\<in>positive_meaning extension_formation_system)"
proof -
  have view: "(982,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables additions_boundary_callee_schema. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion additions_boundary_callee_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises additions_boundary_callee_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system))"
    by (rule additions_view_rule[OF additions_goals_families(3)]) (simp add: additions_boundary_callee_schema_def)
  show ?thesis
  proof
    assume "(982,z)\<in>positive_meaning additions_goals_system"
    then obtain f where "\<forall>a\<in>schema_variables additions_boundary_callee_schema. term_formed (f a)"
      "z=evaluate_pattern f (schema_conclusion additions_boundary_callee_schema)"
      "\<forall>s d p. (s,d,p)\<in>schema_premises additions_boundary_callee_schema \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
      using view by blast
    then show "\<exists>a0 a1 gu gr v k m.
      z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) m \<and>
      term_formed a1 \<and> term_formed gu \<and> term_formed gr \<and>
      (76,Pair_Term (Pair_Term v k) (Pair_Term m (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<and>
      (950,Pair_Term a0 m)\<in>positive_meaning extension_formation_system"
      by (auto simp: additions_boundary_callee_schema_def schema_variables_def additions_goals_components)
  next
    assume "\<exists>a0 a1 gu gr v k m.
      z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) m \<and>
      term_formed a1 \<and> term_formed gu \<and> term_formed gr \<and>
      (76,Pair_Term (Pair_Term v k) (Pair_Term m (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<and>
      (950,Pair_Term a0 m)\<in>positive_meaning extension_formation_system"
    then obtain a0 a1 gu gr v k m where parts:
      "z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) m"
      "term_formed a1" "term_formed gu" "term_formed gr"
      "(76,Pair_Term (Pair_Term v k) (Pair_Term m (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
      "(950,Pair_Term a0 m)\<in>positive_meaning extension_formation_system" by blast
    have listed: "term_formed v" "term_formed k" "term_formed m"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(5)]] by simp_all
    have fresh: "term_formed a0" using schema_call_formed_target[OF positive_meaning_formed[OF parts(6)]] by simp
    show "(982,z)\<in>positive_meaning additions_goals_system" unfolding view
      by (rule exI[of _ "\<lambda>n::nat. if n=0 then a0 else if n=1 then a1 else if n=2 then gu else if n=3 then gr
          else if n=4 then v else if n=5 then k else m"])
        (use parts listed fresh in \<open>auto simp: additions_boundary_callee_schema_def schema_variables_def
          additions_goals_components\<close>)
  qed
qed

lemma additions_audit_callee_rule:
  "(986,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>a0 a1 gu gr v k mu mr.
    z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) (Pair_Term mu mr) \<and>
    term_formed a0 \<and> term_formed a1 \<and> term_formed gu \<and> term_formed gr \<and> term_formed v \<and> term_formed k \<and>
    ((76,Pair_Term (Pair_Term v k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term v mu) mr)\<in>positive_meaning payload_audit_system \<or>
     (76,Pair_Term (Pair_Term (Pair_Term a0 a1) k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term (Pair_Term a0 a1) mu) mr)\<in>positive_meaning payload_audit_system))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((986,c),S)\<in>system_clauses additions_goals_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "z=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
    by (blast dest: additions_goals_valuation)
  have "(c,S)\<in>additions_audit_callee_clauses" using clause by (simp add: additions_goals_families)
  then consider "S=additions_audit_read_schema" | "S=additions_audit_given_schema"
    by (auto simp: additions_audit_callee_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have "z=Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 4) (f 5)))
        (Pair_Term (f 6) (f 7)) \<and>
      term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
      term_formed (f 5) \<and>
      (76,Pair_Term (Pair_Term (f 4) (f 5)) (Pair_Term (Pair_Term (f 6) (f 7)) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term (f 4) (f 6)) (f 7))\<in>positive_meaning payload_audit_system"
      using vars conclusion support
      by (auto simp: 1 additions_audit_read_schema_def schema_variables_def additions_goals_components)
    then show ?rhs by blast
  next
    case 2
    have "z=Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 4) (f 5)))
        (Pair_Term (f 6) (f 7)) \<and>
      term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 4) \<and>
      term_formed (f 5) \<and>
      (76,Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (f 5)) (Pair_Term (Pair_Term (f 6) (f 7)) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (f 6)) (f 7))\<in>positive_meaning payload_audit_system"
      using vars conclusion support
      by (auto simp: 2 additions_audit_given_schema_def schema_variables_def additions_goals_components)
    then show ?rhs by blast
  qed
next
  assume ?rhs
  then obtain a0 a1 gu gr v k mu mr where z:
    "z=Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term v k)) (Pair_Term mu mr)"
    and formed: "term_formed a0" "term_formed a1" "term_formed gu" "term_formed gr" "term_formed v" "term_formed k"
    and calls: "(76,Pair_Term (Pair_Term v k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term v mu) mr)\<in>positive_meaning payload_audit_system \<or>
     (76,Pair_Term (Pair_Term (Pair_Term a0 a1) k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term (Pair_Term a0 a1) mu) mr)\<in>positive_meaning payload_audit_system"
    by blast
  let ?f="\<lambda>n::nat. if n=0 then a0 else if n=1 then a1 else if n=2 then gu else if n=3 then gr else if n=4 then v
    else if n=5 then k else if n=6 then mu else mr"
  from calls show ?lhs
  proof
    assume read: "(76,Pair_Term (Pair_Term v k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term v mu) mr)\<in>positive_meaning payload_audit_system"
    have member: "term_formed mu" "term_formed mr"
      using schema_call_formed_target[OF positive_meaning_formed[OF conjunct2[OF read]]] by simp_all
    have "(986,evaluate_pattern ?f (schema_conclusion additions_audit_read_schema))\<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed member read in \<open>auto simp: additions_goals_families additions_audit_callee_clauses_def
          additions_audit_read_schema_def schema_variables_def additions_goals_call additions_goals_components\<close>)
    then show ?thesis by (simp add: z additions_audit_read_schema_def)
  next
    assume given: "(76,Pair_Term (Pair_Term (Pair_Term a0 a1) k) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term (Pair_Term a0 a1) mu) mr)\<in>positive_meaning payload_audit_system"
    have member: "term_formed mu" "term_formed mr"
      using schema_call_formed_target[OF positive_meaning_formed[OF conjunct2[OF given]]] by simp_all
    have "(986,evaluate_pattern ?f (schema_conclusion additions_audit_given_schema))\<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed member given in \<open>auto simp: additions_goals_families additions_audit_callee_clauses_def
          additions_audit_given_schema_def schema_variables_def additions_goals_call additions_goals_components\<close>)
    then show ?thesis by (simp add: z additions_audit_given_schema_def)
  qed
qed

lemma additions_element_rule:
  assumes family: "\<And>c S. ((n,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses m"
    and member: "n\<in>system_definitions additions_goals_system"
  shows "(n,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>x y w c v. z=Pair_Term (Pair_Term (Pair_Term x (Pair_Term y w)) c) v \<and> term_formed c \<and>
      (83,package_subject_argument x y w v)\<in>positive_meaning package_membership_system) \<or>
    (\<exists>a v. z=Pair_Term a v \<and> (m,Pair_Term a v)\<in>positive_meaning additions_goals_system)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((n,c),S)\<in>system_clauses additions_goals_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "z=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
    by (blast dest: additions_goals_valuation)
  have "(c,S)\<in>addition_element_clauses m" using clause family by blast
  then consider "S=addition_member_schema" | "S=addition_callee_schema m"
    by (auto simp: addition_element_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have "z=Pair_Term (Pair_Term (Pair_Term (f 0) (Pair_Term (f 1) (f 2))) (f 4)) (f 3) \<and> term_formed (f 4) \<and>
      (83,package_subject_argument (f 0) (f 1) (f 2) (f 3))\<in>positive_meaning package_membership_system"
      using vars conclusion support
      by (auto simp: 1 addition_member_schema_def schema_variables_def additions_goals_components)
    then show ?rhs by blast
  next
    case 2
    have "z=Pair_Term (f 0) (f 1) \<and> (m,Pair_Term (f 0) (f 1))\<in>positive_meaning additions_goals_system"
      using conclusion support by (auto simp: 2 addition_callee_schema_def)
    then show ?rhs by blast
  qed
next
  assume ?rhs
  then show ?lhs
  proof
    assume "\<exists>x y w c v. z=Pair_Term (Pair_Term (Pair_Term x (Pair_Term y w)) c) v \<and> term_formed c \<and>
      (83,package_subject_argument x y w v)\<in>positive_meaning package_membership_system"
    then obtain x y w c v where parts: "z=Pair_Term (Pair_Term (Pair_Term x (Pair_Term y w)) c) v" "term_formed c"
      "(83,package_subject_argument x y w v)\<in>positive_meaning package_membership_system" by blast
    have operands: "term_formed x" "term_formed y" "term_formed w" "term_formed v"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by simp_all
    let ?f="\<lambda>i::nat. if i=0 then x else if i=1 then y else if i=2 then w else if i=3 then v else c"
    have "(n,evaluate_pattern ?f (schema_conclusion addition_member_schema))\<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use member parts operands in \<open>auto simp: family addition_element_clauses_def addition_member_schema_def
          schema_variables_def additions_goals_call additions_goals_components\<close>)
    then show ?thesis by (simp add: parts(1) addition_member_schema_def)
  next
    assume "\<exists>a v. z=Pair_Term a v \<and> (m,Pair_Term a v)\<in>positive_meaning additions_goals_system"
    then obtain a v where parts: "z=Pair_Term a v" "(m,Pair_Term a v)\<in>positive_meaning additions_goals_system" by blast
    have operands: "term_formed a" "term_formed v"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by simp_all
    let ?f="\<lambda>i::nat. if i=0 then a else v"
    have "(n,evaluate_pattern ?f (schema_conclusion (addition_callee_schema m)))\<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use member parts operands in \<open>auto simp: family addition_element_clauses_def addition_callee_schema_def
          schema_variables_def additions_goals_call\<close>)
    then show ?thesis by (simp add: parts(1) addition_callee_schema_def)
  qed
qed

lemma additions_members_view_meaning:
  assumes view: "\<And>c S. ((vs,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema ls"
    and vmember: "vs\<in>system_definitions additions_goals_system"
  shows "(vs,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) l) (Pair_Term u r))
      \<in>positive_meaning additions_goals_system \<longleftrightarrow>
    term_formed a0 \<and> term_formed a1 \<and> term_formed gu \<and> term_formed gr \<and> term_formed l \<and> term_formed u \<and>
    term_formed r \<and> (\<exists>q k. (47,Pair_Term q k)\<in>positive_meaning data_subset_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((vs,c),S)\<in>system_clauses additions_goals_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and conclusion: "Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) l) (Pair_Term u r)=
      evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
    by (blast dest: additions_goals_valuation)
  have S: "S=additions_members_view_schema ls" using clause view by blast
  have fvals: "f 0=a0" "f 1=a1" "f 2=gu" "f 3=gr" "f 8=l" "f 6=u" "f 7=r"
    using conclusion by (simp_all add: S additions_members_view_schema_def)
  have "term_formed (f 0) \<and> term_formed (f 1) \<and> term_formed (f 2) \<and> term_formed (f 3) \<and> term_formed (f 8) \<and>
    term_formed (f 6) \<and> term_formed (f 7) \<and> (47,Pair_Term (f 9) (f 10))\<in>positive_meaning data_subset_system \<and>
    (79,citation_observation_argument (f 8) (f 6) (f 7) (f 9))\<in>positive_meaning root_family_reading_system \<and>
    (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 8) (f 10))) (f 10))
      \<in>positive_meaning additions_goals_system"
    using vars support by (auto simp: S additions_members_view_schema_def schema_variables_def additions_goals_components)
  then show ?rhs unfolding fvals by blast
next
  assume ?rhs
  then obtain q k where formed: "term_formed a0" "term_formed a1" "term_formed gu" "term_formed gr" "term_formed l"
      "term_formed u" "term_formed r"
    and sub: "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
    and read: "(79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system"
    and list: "(ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
      \<in>positive_meaning additions_goals_system" by blast
  have qk: "term_formed q" "term_formed k" using schema_call_formed_target[OF positive_meaning_formed[OF sub]] by simp_all
  let ?f="\<lambda>i::nat. if i=0 then a0 else if i=1 then a1 else if i=2 then gu else if i=3 then gr else if i=6 then u
    else if i=7 then r else if i=8 then l else if i=9 then q else k"
  have "(vs,evaluate_pattern ?f (schema_conclusion (additions_members_view_schema ls)))
      \<in>positive_meaning additions_goals_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use vmember formed qk sub read list in \<open>auto simp: view additions_members_view_schema_def
        schema_variables_def additions_goals_call additions_goals_components\<close>)
  then show ?lhs by (simp add: additions_members_view_schema_def)
qed

lemma additions_members_rule:
  assumes family: "\<And>c S. ((n,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>additions_members_clauses vs ls"
    and view: "\<And>c S. ((vs,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> c=0 \<and> S=additions_members_view_schema ls"
    and member: "n\<in>system_definitions additions_goals_system" and vmember: "vs\<in>system_definitions additions_goals_system"
  shows "(n,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>a0 a1 gu gr ar br u r q k.
    z=Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term ar br) (Pair_Term u r)) \<and>
    term_formed ar \<and> term_formed br \<and> (47,Pair_Term q k)\<in>positive_meaning data_subset_system \<and>
    ((\<exists>l. (957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system) \<or>
     (79,citation_observation_argument (Pair_Term a0 a1) u r q)\<in>positive_meaning root_family_reading_system \<and>
     (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term a0 a1) k)) k)
       \<in>positive_meaning additions_goals_system))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain c S f where clause: "((n,c),S)\<in>system_clauses additions_goals_system"
    and vars: "\<forall>a\<in>schema_variables S. term_formed (f a)" and conclusion: "z=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>positive_meaning additions_goals_system"
    by (blast dest: additions_goals_valuation)
  have "(c,S)\<in>additions_members_clauses vs ls" using clause family by blast
  then consider "S=additions_members_added_schema vs" | "S=additions_members_given_schema ls"
    by (auto simp: additions_members_clauses_def)
  then show ?rhs
  proof cases
    case 1
    have parts: "z=Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3)))
        (Pair_Term (Pair_Term (f 4) (f 5)) (Pair_Term (f 6) (f 7))) \<and>
      term_formed (f 4) \<and> term_formed (f 5) \<and>
      (957,Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 4) (f 5))) (f 8))
        \<in>positive_meaning extension_package_system \<and>
      (vs,Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (f 8)) (Pair_Term (f 6) (f 7)))
        \<in>positive_meaning additions_goals_system"
      using vars conclusion support
      by (auto simp: 1 additions_members_added_schema_def schema_variables_def additions_goals_components)
    then obtain q k where "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
      "(79,citation_observation_argument (f 8) (f 6) (f 7) q)\<in>positive_meaning root_family_reading_system"
      "(ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3))) (Pair_Term (f 8) k)) k)
        \<in>positive_meaning additions_goals_system"
      unfolding additions_members_view_meaning[OF view vmember] by blast
    then show ?rhs using parts by blast
  next
    case 2
    have "z=Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3)))
        (Pair_Term (Pair_Term (f 4) (f 5)) (Pair_Term (f 6) (f 7))) \<and>
      term_formed (f 4) \<and> term_formed (f 5) \<and> (47,Pair_Term (f 9) (f 10))\<in>positive_meaning data_subset_system \<and>
      (79,citation_observation_argument (Pair_Term (f 0) (f 1)) (f 6) (f 7) (f 9))\<in>positive_meaning root_family_reading_system \<and>
      (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (f 2) (f 3)))
        (Pair_Term (Pair_Term (f 0) (f 1)) (f 10))) (f 10))\<in>positive_meaning additions_goals_system"
      using vars conclusion support
      by (auto simp: 2 additions_members_given_schema_def schema_variables_def additions_goals_components)
    then show ?rhs by blast
  qed
next
  assume ?rhs
  then obtain a0 a1 gu gr ar br u r q k where z:
    "z=Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term ar br) (Pair_Term u r))"
    and bounds: "term_formed ar" "term_formed br"
    and sub: "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
    and calls: "(\<exists>l. (957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system) \<or>
     (79,citation_observation_argument (Pair_Term a0 a1) u r q)\<in>positive_meaning root_family_reading_system \<and>
     (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term a0 a1) k)) k)
       \<in>positive_meaning additions_goals_system"
    by blast
  have qk: "term_formed q" "term_formed k" using schema_call_formed_target[OF positive_meaning_formed[OF sub]] by simp_all
  from calls show ?lhs
  proof
    assume "\<exists>l. (957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system"
    then obtain l where least: "(957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)
        \<in>positive_meaning extension_package_system"
      and read: "(79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system"
      and list: "(ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system" by blast
    have lf: "term_formed a0" "term_formed a1" "term_formed l"
      using schema_call_formed_target[OF positive_meaning_formed[OF least]] by simp_all
    have ur: "term_formed u" "term_formed r"
      using schema_call_formed_target[OF positive_meaning_formed[OF read]] by simp_all
    have gf: "term_formed gu" "term_formed gr"
      using schema_call_formed_target[OF positive_meaning_formed[OF list]] by simp_all
    have viewed: "(vs,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) l) (Pair_Term u r))
        \<in>positive_meaning additions_goals_system"
      unfolding additions_members_view_meaning[OF view vmember] using lf ur gf sub read list by blast
    let ?f="\<lambda>i::nat. if i=0 then a0 else if i=1 then a1 else if i=2 then gu else if i=3 then gr else if i=4 then ar
      else if i=5 then br else if i=6 then u else if i=7 then r else l"
    have "(n,evaluate_pattern ?f (schema_conclusion (additions_members_added_schema vs)))
        \<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use member lf ur gf bounds least viewed in \<open>auto simp: family additions_members_clauses_def
          additions_members_added_schema_def schema_variables_def additions_goals_call additions_goals_components\<close>)
    then show ?thesis by (simp add: z additions_members_added_schema_def)
  next
    assume given: "(79,citation_observation_argument (Pair_Term a0 a1) u r q)\<in>positive_meaning root_family_reading_system \<and>
     (ls,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term a0 a1) k)) k)
       \<in>positive_meaning additions_goals_system"
    have lf: "term_formed a0" "term_formed a1" "term_formed u" "term_formed r"
      using schema_call_formed_target[OF positive_meaning_formed[OF conjunct1[OF given]]] by simp_all
    have gf: "term_formed gu" "term_formed gr"
      using schema_call_formed_target[OF positive_meaning_formed[OF conjunct2[OF given]]] by simp_all
    let ?f="\<lambda>i::nat. if i=0 then a0 else if i=1 then a1 else if i=2 then gu else if i=3 then gr else if i=4 then ar
      else if i=5 then br else if i=6 then u else if i=7 then r else if i=9 then q else k"
    have "(n,evaluate_pattern ?f (schema_conclusion (additions_members_given_schema ls)))
        \<in>positive_meaning additions_goals_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use member lf gf bounds qk sub given in \<open>auto simp: family additions_members_clauses_def
          additions_members_given_schema_def schema_variables_def additions_goals_call additions_goals_components\<close>)
    then show ?thesis by (simp add: z additions_members_given_schema_def)
  qed
qed

section \<open>The readings of a bound member\<close>

text \<open>
  The given's package is closed: every member it holds is defined in any formed environment including the given's,
  with its callees among its members. A finite set of sites closed so, holding a site's roots, gives the package
  there, its members among the set.
\<close>

lemma additions_given_closed:
  assumes outer: "environment_included E F" and ff: "environment_formed F"
  shows "finite {d. \<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q} \<and>
    (\<forall>d\<in>{d. \<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q}. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>{d. \<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q}))"
proof (cases "\<exists>Q. native_package_at E u r Q")
  case True
  then obtain Q where Q: "native_package_at E u r Q" by blast
  have G: "{d. \<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q}=system_definitions Q"
    using Q native_package_unique[OF Q] by blast
  have formed: "native_package_formed E (native_package_roots E u r)" by (rule native_package_projection(1)[OF Q])
  have sites: "system_definitions Q=native_definition_sites E (native_package_roots E u r)"
    using native_package_projection(3)[OF Q] by (simp add: native_package_sites_def)
  have closed: "\<forall>d\<in>system_definitions Q. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>system_definitions Q)"
  proof
    fix d assume member: "d\<in>system_definitions Q"
    obtain p C where raw: "native_definition_at E (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>native_definition_sites E (native_package_roots E u r)"
      using native_package_sites_closed_bound[OF formed] member sites by blast
    show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>system_definitions Q)"
      using native_definition_included[OF raw(1) outer ff] raw(2) sites by auto
  qed
  show ?thesis using G closed native_package_sites(2)[OF formed] sites by simp
next
  case False
  then show ?thesis by simp
qed

lemma additions_members_cover:
  assumes ff: "environment_formed F" and family: "native_root_family_at F u r Q"
    and finite: "finite K" and roots: "rel_ran Q\<subseteq>K"
    and closed: "\<forall>d\<in>K. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>K)"
  shows "\<exists>P. native_package_at F u r P \<and> system_definitions P\<subseteq>K"
proof -
  have formed: "native_package_formed F (rel_ran Q)"
    unfolding native_package_finite_closed_bound using ff finite roots closed by blast
  have sites: "system_definitions (native_program F (rel_ran Q))\<subseteq>K"
    using native_program_definitions[OF formed] native_closed_bound_contains_sites[OF roots closed] by simp
  have "native_package_at F u r (native_program F (rel_ran Q))"
    unfolding native_package_at_def using family formed by blast
  then show ?thesis using sites by blast
qed

lemma additions_boundary_callee_at_values:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and data: "data_elements ys" and site: "term_formed (site_data_term gu gr)"
  shows "(982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>d p C. x=definition_site_value d \<and> native_definition_at V (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      fst d\<notin>environment_uses E)"
proof -
  obtain ps b where e: "e=Pair_Term (pair_list_term ps) b" and bf: "term_formed b" and keyed: "formed_key_rows ps"
    and uses: "\<And>w. use_data_term w\<in>set (map fst ps) \<longleftrightarrow> w\<in>environment_uses E"
    by (rule environment_value_uses[OF given]) (rule that; assumption)
  have listing: "(76,Pair_Term (Pair_Term v (data_list_term ys)) (Pair_Term x (Payload_Term [])))
      \<in>positive_meaning definition_callee_list_system \<longleftrightarrow>
    (\<exists>u r p C. x=site_data_term u r \<and> native_definition_at V u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys))"
    using definition_callee_list_on_values[OF read data, of "[x]"] by simp
  have fresh: "(950,Pair_Term (pair_list_term ps) (site_data_term u r))\<in>positive_meaning extension_formation_system
      \<longleftrightarrow> u\<notin>environment_uses E" if sited: "term_formed (site_data_term u r)" for u r
  proof -
    have pf: "term_formed (Payload_Term r)" using sited by (simp add: site_data_term_def)
    have "(950,Pair_Term (pair_list_term ps) (site_data_term u r))\<in>positive_meaning extension_formation_system
        \<longleftrightarrow> use_data_term u\<notin>set (map fst ps)"
    proof
      assume "(950,Pair_Term (pair_list_term ps) (site_data_term u r))\<in>positive_meaning extension_formation_system"
      then obtain xs k w where parts:
        "Pair_Term (pair_list_term ps) (site_data_term u r)=Pair_Term (pair_list_term xs) (Pair_Term k w)"
        "k\<notin>set (map fst xs)" unfolding added_use_fresh_exact by blast
      have "xs=ps" "k=use_data_term u" using parts(1) by (simp_all add: site_data_term_def pair_list_term_injective)
      then show "use_data_term u\<notin>set (map fst ps)" using parts(2) by simp
    next
      assume absent: "use_data_term u\<notin>set (map fst ps)"
      show "(950,Pair_Term (pair_list_term ps) (site_data_term u r))\<in>positive_meaning extension_formation_system"
        unfolding added_use_fresh_exact
        by (rule exI[of _ ps], rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term r"])
          (use absent keyed pf in \<open>simp add: site_data_term_def\<close>)
    qed
    then show ?thesis using uses[of u] by blast
  qed
  have vf: "term_formed v" using environment_value_presents_formed[OF read] by blast
  have kf: "term_formed (data_list_term ys)" using data by (simp add: data_list_term_formed)
  have ef: "term_formed (pair_list_term ps)" "term_formed b" using environment_value_presents_formed[OF given] e by simp_all
  show ?thesis
  proof
    assume "(982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system"
    then obtain a0 a1 g1 g2 v' k' m where eq:
        "Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x=
          Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term g1 g2)) (Pair_Term v' k')) m"
      and c76: "(76,Pair_Term (Pair_Term v' k') (Pair_Term m (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system"
      and c950: "(950,Pair_Term a0 m)\<in>positive_meaning extension_formation_system"
      unfolding additions_boundary_callee_rule by blast
    have same: "a0=pair_list_term ps" "v'=v" "k'=data_list_term ys" "m=x" using eq by (simp_all add: e)
    have calls: "(76,Pair_Term (Pair_Term v (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system"
      "(950,Pair_Term (pair_list_term ps) x)\<in>positive_meaning extension_formation_system"
      using c76 c950 same by simp_all
    obtain u r p C where parts: "x=site_data_term u r" "native_definition_at V u r p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      using calls(1) listing by blast
    have "u\<notin>environment_uses E"
      using calls(2) fresh[OF native_definition_site_data_formed[OF parts(2)]] parts(1) by simp
    then show "\<exists>d p C. x=definition_site_value d \<and> native_definition_at V (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      fst d\<notin>environment_uses E"
      using parts by (intro exI[of _ "(u,r)"]) auto
  next
    assume "\<exists>d p C. x=definition_site_value d \<and> native_definition_at V (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      fst d\<notin>environment_uses E"
    then obtain d p C where parts: "x=definition_site_value d" "native_definition_at V (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      "fst d\<notin>environment_uses E" by blast
    have xf: "term_formed x" using native_definition_site_data_formed[OF parts(2)] parts(1) by simp
    have list: "(76,Pair_Term (Pair_Term v (data_list_term ys)) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system"
      using listing parts(1-3) by (cases d) auto
    have absent: "(950,Pair_Term (pair_list_term ps) x)\<in>positive_meaning extension_formation_system"
      using fresh[of "fst d" "snd d"] xf parts(1,4) by simp
    show "(982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system"
      unfolding additions_boundary_callee_rule
      by (rule exI[of _ "pair_list_term ps"], rule exI[of _ b], rule exI[of _ "use_data_term gu"],
        rule exI[of _ "Payload_Term gr"], rule exI[of _ v], rule exI[of _ "data_list_term ys"], rule exI[of _ x])
        (use list absent ef site in \<open>simp add: e site_data_term_def\<close>)
  qed
qed

lemma additions_audit_callee_at_values:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and data: "data_elements ys" and site: "term_formed (site_data_term gu gr)"
  shows "(986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>d p C. x=definition_site_value d \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]} \<and>
      (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C))"
proof -
  obtain a0 a1 where e: "e=Pair_Term a0 a1" using environment_value_uses[OF given] by blast
  have joint: "((76,Pair_Term (Pair_Term w (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term w mu) mr)\<in>positive_meaning payload_audit_system) \<longleftrightarrow>
    (\<exists>d p C. Pair_Term mu mr=definition_site_value d \<and> native_definition_at W (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]})" if wv: "environment_value_presents W w" for W w mu mr
  proof
    assume both: "(76,Pair_Term (Pair_Term w (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term w mu) mr)\<in>positive_meaning payload_audit_system"
    obtain u r p C where parts: "Pair_Term mu mr=site_data_term u r" "native_definition_at W u r p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      using definition_callee_list_on_values[OF wv data, of "[Pair_Term mu mr]"] both by auto
    have m: "mu=use_data_term u" "mr=Payload_Term r" using parts(1) by (simp_all add: site_data_term_def)
    obtain p' C' where audited: "native_definition_at W u r p' C'" "definition_payloads p' C'\<subseteq>{[]}"
      using payload_audit_on_values[OF wv, of u r] both m by auto
    have "p'=p \<and> C'=C" by (rule native_definition_unique[OF audited(1) parts(2)])
    then show "\<exists>d p C. Pair_Term mu mr=definition_site_value d \<and> native_definition_at W (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]}"
      using parts audited by (intro exI[of _ "(u,r)"]) auto
  next
    assume "\<exists>d p C. Pair_Term mu mr=definition_site_value d \<and> native_definition_at W (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]}"
    then obtain d p C where parts: "Pair_Term mu mr=definition_site_value d" "native_definition_at W (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      "definition_payloads p C\<subseteq>{[]}" by blast
    have m: "mu=use_data_term (fst d)" "mr=Payload_Term (snd d)" using parts(1) by (simp_all add: site_data_term_def)
    have "(76,Pair_Term (Pair_Term w (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system"
      using definition_callee_list_on_values[OF wv data, of "[Pair_Term mu mr]"] parts(1-3) by (cases d) auto
    moreover have "(505,Pair_Term (Pair_Term w mu) mr)\<in>positive_meaning payload_audit_system"
      using payload_audit_on_values[OF wv, of "fst d" "snd d"] parts(2,4) m by auto
    ultimately show "(76,Pair_Term (Pair_Term w (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term w mu) mr)\<in>positive_meaning payload_audit_system" by blast
  qed
  have vf: "term_formed v" using environment_value_presents_formed[OF read] by blast
  have kf: "term_formed (data_list_term ys)" using data by (simp add: data_list_term_formed)
  have ef: "term_formed a0" "term_formed a1" using environment_value_presents_formed[OF given] e by simp_all
  have sf: "term_formed (use_data_term gu)" "term_formed (Payload_Term gr)" using site by (simp_all add: site_data_term_def)
  show ?thesis
  proof
    assume "(986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system"
    then obtain mu mr where x: "x=Pair_Term mu mr" and calls:
      "(76,Pair_Term (Pair_Term v (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term v mu) mr)\<in>positive_meaning payload_audit_system \<or>
      (76,Pair_Term (Pair_Term e (data_list_term ys)) (Pair_Term (Pair_Term mu mr) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term e mu) mr)\<in>positive_meaning payload_audit_system"
      unfolding additions_audit_callee_rule by (auto simp: e site_data_term_def)
    from calls show "\<exists>d p C. x=definition_site_value d \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]} \<and>
      (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C)"
      using joint[OF read, of mu mr] joint[OF given, of mu mr] x by blast
  next
    assume "\<exists>d p C. x=definition_site_value d \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
      definition_payloads p C\<subseteq>{[]} \<and>
      (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C)"
    then obtain d p C where parts: "x=definition_site_value d"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      "definition_payloads p C\<subseteq>{[]}"
      "native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C" by blast
    have x: "x=Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))" using parts(1) by (simp add: site_data_term_def)
    have calls: "(76,Pair_Term (Pair_Term v (data_list_term ys))
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term v (use_data_term (fst d))) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system \<or>
      (76,Pair_Term (Pair_Term e (data_list_term ys))
          (Pair_Term (Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))) (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<and>
      (505,Pair_Term (Pair_Term e (use_data_term (fst d))) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system"
    proof -
      have sited: "Pair_Term (use_data_term (fst d)) (Payload_Term (snd d))=definition_site_value d"
        by (simp add: site_data_term_def)
      from parts(4) show ?thesis
      proof
        assume "native_definition_at V (fst d) (snd d) p C"
        then show ?thesis using joint[OF read, of "use_data_term (fst d)" "Payload_Term (snd d)"] parts(2,3) sited
          by blast
      next
        assume "native_definition_at E (fst d) (snd d) p C"
        then show ?thesis using joint[OF given, of "use_data_term (fst d)" "Payload_Term (snd d)"] parts(2,3) sited
          by blast
      qed
    qed
    show "(986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) x)
      \<in>positive_meaning additions_goals_system"
      unfolding additions_audit_callee_rule
      by (rule exI[of _ a0], rule exI[of _ a1], rule exI[of _ "use_data_term gu"], rule exI[of _ "Payload_Term gr"],
        rule exI[of _ v], rule exI[of _ "data_list_term ys"], rule exI[of _ "use_data_term (fst d)"],
        rule exI[of _ "Payload_Term (snd d)"]) (use calls x ef sf vf kf in \<open>auto simp: e site_data_term_def\<close>)
  qed
qed

lemma additions_element_at_values:
  assumes family: "\<And>c S. ((n,c),S)\<in>system_clauses additions_goals_system \<longleftrightarrow> (c,S)\<in>addition_element_clauses m"
    and member: "n\<in>system_definitions additions_goals_system"
    and given: "environment_value_presents E e" and site: "term_formed (site_data_term gu gr)" and other: "term_formed c"
  shows "(n,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) c) x)\<in>positive_meaning additions_goals_system
    \<longleftrightarrow> (\<exists>d. x=definition_site_value d \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q)) \<or>
      (m,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) c) x)\<in>positive_meaning additions_goals_system"
proof -
  have membership: "(83,package_subject_argument e (use_data_term gu) (Payload_Term gr) x)
      \<in>positive_meaning package_membership_system \<longleftrightarrow>
    (\<exists>d. x=definition_site_value d \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q))"
  proof
    assume "(83,package_subject_argument e (use_data_term gu) (Payload_Term gr) x)
      \<in>positive_meaning package_membership_system"
    then obtain E' e' v a d P where parts:
      "package_subject_argument e (use_data_term gu) (Payload_Term gr) x=
        package_subject_argument e' (use_data_term v) (Payload_Term a) (definition_site_value d)"
      "environment_value_presents E' e'" "native_package_at E' v a P" "d\<in>system_definitions P"
      unfolding package_membership_exact by blast
    have same: "e'=e" "v=gu" "a=gr" "x=definition_site_value d"
      using parts(1) by (simp_all add: inj_eq[OF use_data_term_injective])
    have "E'=E" using environment_value_presents_unique[OF parts(2)[unfolded same(1)] given] .
    then show "\<exists>d. x=definition_site_value d \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q)"
      using parts(3,4) same by blast
  next
    assume "\<exists>d. x=definition_site_value d \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q)"
    then obtain d Q where d: "x=definition_site_value d" "native_package_at E gu gr Q" "d\<in>system_definitions Q"
      by blast
    show "(83,package_subject_argument e (use_data_term gu) (Payload_Term gr) x)
      \<in>positive_meaning package_membership_system"
      using package_membership_on_values[OF given, of gu gr d] d by auto
  qed
  show ?thesis
    unfolding additions_element_rule[OF family member]
    using membership other site by (auto simp: site_data_term_def)
qed

subsection \<open>G3: every bound member is the given's or an added definition at a use no given artifact holds\<close>

lemma additions_boundary_sound:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and site: "term_formed (site_data_term gu gr)"
    and inner: "environment_included V F" and outer: "environment_included E F" and ff: "environment_formed F"
    and family: "native_root_family_at V u r Q" and range: "rel_ran Q=set ds"
    and sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) k)\<in>positive_meaning data_subset_system"
    and list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v k)) k)
      \<in>positive_meaning additions_goals_system"
  shows "\<exists>R. native_package_at F u r R \<and> (\<forall>d\<in>system_definitions R.
    (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or> fst d\<notin>environment_uses E)"
proof -
  let ?c="Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v k)"
  obtain ys where k: "k=data_list_term ys" and cf: "term_formed ?c"
    and each: "\<forall>x\<in>set ys. (983,Pair_Term ?c x)\<in>positive_meaning additions_goals_system"
    using additions_boundary_lists.semantics.sound_at[OF list] by blast
  have ys: "data_elements ys" "set (map (\<lambda>d. definition_site_value d) ds)\<subseteq>set ys"
    using sub unfolding k data_subset_lists by blast+
  have vk: "term_formed (Pair_Term v k)" using cf by simp
  let ?G="{d. \<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q}"
  let ?K="{d. definition_site_value d\<in>set ys \<and> (\<exists>p C. native_definition_at V (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)) \<and>
    fst d\<notin>environment_uses E}"
  have split: "d\<in>?K\<union>?G" if member: "definition_site_value d\<in>set ys" for d
  proof -
    have held: "(983,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using each member by blast
    have "d\<in>?G \<or> (982,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using held additions_element_at_values[OF additions_goals_families(4) _ given site vk,
        of "definition_site_value d"] by simp
    moreover have "d\<in>?K" if "(982,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using that additions_boundary_callee_at_values[OF given read ys(1) site, of "definition_site_value d"] member
      unfolding k by auto
    ultimately show ?thesis by blast
  qed
  have finiteK: "finite ?K"
  proof (rule finite_subset)
    show "?K\<subseteq>(\<lambda>d. definition_site_value d) -` set ys" by auto
    show "finite ((\<lambda>d. definition_site_value d) -` set ys)" by (rule finite_vimageI) (auto simp: inj_on_def)
  qed
  have given_closed: "finite ?G \<and> (\<forall>d\<in>?G. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?G))"
    by (rule additions_given_closed[OF outer ff])
  have closedK: "\<forall>d\<in>?K. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
  proof
    fix d assume "d\<in>?K"
    then obtain p C where raw: "native_definition_at V (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by blast
    have "schema_dependencies S\<subseteq>?K\<union>?G" if "(c,S)\<in>C" for c S
    proof
      fix y assume "y\<in>schema_dependencies S"
      then have "definition_site_value y\<in>set ys" using raw(2) that by blast
      then show "y\<in>?K\<union>?G" by (rule split)
    qed
    then show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
      using native_definition_included[OF raw(1) inner ff] by blast
  qed
  have closed: "\<forall>d\<in>?K\<union>?G. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
  proof
    fix d assume member: "d\<in>?K\<union>?G"
    show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
    proof (cases "d\<in>?K")
      case True
      from closedK[rule_format, OF True] show ?thesis by blast
    next
      case False
      then have "d\<in>?G" using member by blast
      from conjunct2[OF given_closed, rule_format, OF this] obtain p C where
        "native_definition_at F (fst d) (snd d) p C" "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?G" by blast
      then show ?thesis by blast
    qed
  qed
  have finite: "finite (?K\<union>?G)" using finiteK given_closed by simp
  have roots: "rel_ran Q\<subseteq>?K\<union>?G"
  proof
    fix y assume "y\<in>rel_ran Q"
    then have "definition_site_value y\<in>set ys" using range ys(2) by auto
    then show "y\<in>?K\<union>?G" by (rule split)
  qed
  obtain P where P: "native_package_at F u r P" "system_definitions P\<subseteq>?K\<union>?G"
    using additions_members_cover[OF ff native_root_family_included[OF family inner ff] finite roots closed] by blast
  show ?thesis using P by blast
qed

lemma additions_boundary_list_complete:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and site: "term_formed (site_data_term gu gr)" and finite: "finite D"
    and covered: "\<forall>d\<in>D. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      ((\<exists>p C. native_definition_at V (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D)) \<and>
        fst d\<notin>environment_uses E)"
  shows "\<exists>ys. set ys=(\<lambda>d. definition_site_value d) ` D \<and> data_elements ys \<and>
    (984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) (data_list_term ys))
      \<in>positive_meaning additions_goals_system"
proof -
  obtain ds where ds: "set ds=D" using finite_list[OF finite] by blast
  let ?ys="map (\<lambda>d. definition_site_value d) ds"
  have siteformed: "term_formed (definition_site_value d)" if "d\<in>D" for d
  proof -
    from covered that consider (member) Q where "native_package_at E gu gr Q" "d\<in>system_definitions Q"
      | (defined) p C where "native_definition_at V (fst d) (snd d) p C" by blast
    then show ?thesis
    proof cases
      case member
      then show ?thesis using native_package_member_address[OF member] by (simp add: site_data_term_def)
    next
      case defined
      then show ?thesis using native_definition_site_data_formed by blast
    qed
  qed
  have data: "data_elements ?ys" using siteformed ds by (auto simp: site_data_term_self_contained)
  have vf: "term_formed v" using environment_value_presents_formed[OF read] by blast
  have ef: "term_formed e" using environment_value_presents_formed[OF given] by blast
  have kf: "term_formed (data_list_term ?ys)" using data by (simp add: data_list_term_formed)
  let ?c="Pair_Term v (data_list_term ?ys)"
  have cf: "term_formed ?c" using vf kf by simp
  have each: "\<forall>x\<in>set ?ys. (983,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
      \<in>positive_meaning additions_goals_system"
  proof
    fix x assume "x\<in>set ?ys"
    then obtain d where d: "d\<in>D" "x=definition_site_value d" using ds by auto
    have element: "(983,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
        \<in>positive_meaning additions_goals_system \<longleftrightarrow>
      (\<exists>d'. x=definition_site_value d' \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d'\<in>system_definitions Q)) \<or>
      (982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)\<in>positive_meaning additions_goals_system"
      by (rule additions_element_at_values[OF additions_goals_families(4) _ given site cf]) simp
    have callee: "(982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
        \<in>positive_meaning additions_goals_system \<longleftrightarrow>
      (\<exists>d p C. x=definition_site_value d \<and> native_definition_at V (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys) \<and>
        fst d\<notin>environment_uses E)"
      by (rule additions_boundary_callee_at_values[OF given read data site])
    have choice: "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      ((\<exists>p C. native_definition_at V (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D)) \<and>
        fst d\<notin>environment_uses E)" using covered d(1) by blast
    from choice show "(983,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
      \<in>positive_meaning additions_goals_system"
    proof
      assume "\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q"
      then show ?thesis using element d(2) by blast
    next
      assume inner: "(\<exists>p C. native_definition_at V (fst d) (snd d) p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D)) \<and> fst d\<notin>environment_uses E"
      then obtain p C where raw: "native_definition_at V (fst d) (snd d) p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D" by blast
      have "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys"
        using raw(2) ds by auto
      then have "(982,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
          \<in>positive_meaning additions_goals_system"
        using callee raw(1) inner d(2) by blast
      then show ?thesis using element by blast
    qed
  qed
  have list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) (data_list_term ?ys))
      \<in>positive_meaning additions_goals_system"
    by (rule additions_boundary_lists.complete) (use ef site cf data each in \<open>simp_all add: data_list_term_formed\<close>)
  show ?thesis by (intro exI[of _ ?ys] conjI) (use list data ds in simp_all)
qed

subsection \<open>G4: every bound member is the given's or a definition stating no payload but the empty one\<close>

lemma additions_audit_sound:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and site: "term_formed (site_data_term gu gr)"
    and inner: "environment_included V F" and outer: "environment_included E F" and ff: "environment_formed F"
    and family: "native_root_family_at V u r Q" and range: "rel_ran Q=set ds"
    and sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) k)\<in>positive_meaning data_subset_system"
    and list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v k)) k)
      \<in>positive_meaning additions_goals_system"
  shows "\<exists>R. native_package_at F u r R \<and> (\<forall>d\<in>system_definitions R.
    (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
    (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))"
proof -
  let ?c="Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v k)"
  obtain ys where k: "k=data_list_term ys" and cf: "term_formed ?c"
    and each: "\<forall>x\<in>set ys. (987,Pair_Term ?c x)\<in>positive_meaning additions_goals_system"
    using additions_audit_lists.semantics.sound_at[OF list] by blast
  have ys: "data_elements ys" "set (map (\<lambda>d. definition_site_value d) ds)\<subseteq>set ys"
    using sub unfolding k data_subset_lists by blast+
  have vk: "term_formed (Pair_Term v k)" using cf by simp
  let ?G="{d. \<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q}"
  let ?K="{d. definition_site_value d\<in>set ys \<and> (\<exists>p C.
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys) \<and>
    definition_payloads p C\<subseteq>{[]} \<and>
    (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C))}"
  have split: "d\<in>?K\<union>?G" if member: "definition_site_value d\<in>set ys" for d
  proof -
    have held: "(987,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using each member by blast
    have "d\<in>?G \<or> (986,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using held additions_element_at_values[OF additions_goals_families(8) _ given site vk,
        of "definition_site_value d"] by simp
    moreover have "d\<in>?K" if "(986,Pair_Term ?c (definition_site_value d))\<in>positive_meaning additions_goals_system"
      using that additions_audit_callee_at_values[OF given read ys(1) site, of "definition_site_value d"] member
      unfolding k by auto
    ultimately show ?thesis by blast
  qed
  have finiteK: "finite ?K"
  proof (rule finite_subset)
    show "?K\<subseteq>(\<lambda>d. definition_site_value d) -` set ys" by auto
    show "finite ((\<lambda>d. definition_site_value d) -` set ys)" by (rule finite_vimageI) (auto simp: inj_on_def)
  qed
  have given_closed: "finite ?G \<and> (\<forall>d\<in>?G. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?G))"
    by (rule additions_given_closed[OF outer ff])
  have closedK: "\<forall>d\<in>?K. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]} \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
  proof
    fix d assume "d\<in>?K"
    then obtain p C where raw: "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      "definition_payloads p C\<subseteq>{[]}"
      "native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C" by blast
    have defined: "native_definition_at F (fst d) (snd d) p C"
      using raw(3) native_definition_included[OF _ inner ff] native_definition_included[OF _ outer ff] by blast
    have "schema_dependencies S\<subseteq>?K\<union>?G" if "(c,S)\<in>C" for c S
    proof
      fix y assume "y\<in>schema_dependencies S"
      then have "definition_site_value y\<in>set ys" using raw(1) that by blast
      then show "y\<in>?K\<union>?G" by (rule split)
    qed
    then show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]} \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
      using defined raw(2) by blast
  qed
  have closed: "\<forall>d\<in>?K\<union>?G. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
  proof
    fix d assume member: "d\<in>?K\<union>?G"
    show "\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?K\<union>?G)"
    proof (cases "d\<in>?K")
      case True
      from closedK[rule_format, OF True] show ?thesis by blast
    next
      case False
      then have "d\<in>?G" using member by blast
      from conjunct2[OF given_closed, rule_format, OF this] obtain p C where
        "native_definition_at F (fst d) (snd d) p C" "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?G" by blast
      then show ?thesis by blast
    qed
  qed
  have finite: "finite (?K\<union>?G)" using finiteK given_closed by simp
  have roots: "rel_ran Q\<subseteq>?K\<union>?G"
  proof
    fix y assume "y\<in>rel_ran Q"
    then have "definition_site_value y\<in>set ys" using range ys(2) by auto
    then show "y\<in>?K\<union>?G" by (rule split)
  qed
  obtain P where P: "native_package_at F u r P" "system_definitions P\<subseteq>?K\<union>?G"
    using additions_members_cover[OF ff native_root_family_included[OF family inner ff] finite roots closed] by blast
  have "\<forall>d\<in>system_definitions P. d\<in>?G \<or> (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})"
  proof
    fix d assume "d\<in>system_definitions P"
    then have "d\<in>?K\<union>?G" using P(2) by blast
    then show "d\<in>?G \<or> (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})"
    proof
      assume "d\<in>?K"
      from closedK[rule_format, OF this] show ?thesis by blast
    qed blast
  qed
  then show ?thesis using P(1) by blast
qed

lemma additions_audit_list_complete:
  assumes given: "environment_value_presents E e" and read: "environment_value_presents V v"
    and site: "term_formed (site_data_term gu gr)" and finite: "finite D"
    and covered: "\<forall>d\<in>D. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      (\<exists>p C. (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D) \<and> definition_payloads p C\<subseteq>{[]})"
  shows "\<exists>ys. set ys=(\<lambda>d. definition_site_value d) ` D \<and> data_elements ys \<and>
    (988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term v (data_list_term ys))) (data_list_term ys))
      \<in>positive_meaning additions_goals_system"
proof -
  obtain ds where ds: "set ds=D" using finite_list[OF finite] by blast
  let ?ys="map (\<lambda>d. definition_site_value d) ds"
  have siteformed: "term_formed (definition_site_value d)" if "d\<in>D" for d
  proof -
    from covered that consider (member) Q where "native_package_at E gu gr Q" "d\<in>system_definitions Q"
      | (defined) p C where "native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C"
      by blast
    then show ?thesis
    proof cases
      case member
      then show ?thesis using native_package_member_address[OF member] by (simp add: site_data_term_def)
    next
      case defined
      then show ?thesis using native_definition_site_data_formed by blast
    qed
  qed
  have data: "data_elements ?ys" using siteformed ds by (auto simp: site_data_term_self_contained)
  have vf: "term_formed v" using environment_value_presents_formed[OF read] by blast
  have ef: "term_formed e" using environment_value_presents_formed[OF given] by blast
  have kf: "term_formed (data_list_term ?ys)" using data by (simp add: data_list_term_formed)
  let ?c="Pair_Term v (data_list_term ?ys)"
  have cf: "term_formed ?c" using vf kf by simp
  have each: "\<forall>x\<in>set ?ys. (987,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
      \<in>positive_meaning additions_goals_system"
  proof
    fix x assume "x\<in>set ?ys"
    then obtain d where d: "d\<in>D" "x=definition_site_value d" using ds by auto
    have element: "(987,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
        \<in>positive_meaning additions_goals_system \<longleftrightarrow>
      (\<exists>d'. x=definition_site_value d' \<and> (\<exists>Q. native_package_at E gu gr Q \<and> d'\<in>system_definitions Q)) \<or>
      (986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)\<in>positive_meaning additions_goals_system"
      by (rule additions_element_at_values[OF additions_goals_families(8) _ given site cf]) simp
    have callee: "(986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
        \<in>positive_meaning additions_goals_system \<longleftrightarrow>
      (\<exists>d p C. x=definition_site_value d \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys) \<and>
        definition_payloads p C\<subseteq>{[]} \<and>
        (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C))"
      by (rule additions_audit_callee_at_values[OF given read data site])
    have choice: "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      (\<exists>p C. (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D) \<and> definition_payloads p C\<subseteq>{[]})"
      using covered d(1) by blast
    from choice show "(987,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
      \<in>positive_meaning additions_goals_system"
    proof
      assume "\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q"
      then show ?thesis using element d(2) by blast
    next
      assume "\<exists>p C. (native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D) \<and> definition_payloads p C\<subseteq>{[]}"
      then obtain p C where raw: "native_definition_at V (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C"
        "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>D" "definition_payloads p C\<subseteq>{[]}" by blast
      have "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ?ys"
        using raw(2) ds by auto
      then have "(986,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) x)
          \<in>positive_meaning additions_goals_system"
        using callee raw(1,3) d(2) by blast
      then show ?thesis using element by blast
    qed
  qed
  have list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) ?c) (data_list_term ?ys))
      \<in>positive_meaning additions_goals_system"
    by (rule additions_audit_lists.complete) (use ef site cf data each in \<open>simp_all add: data_list_term_formed\<close>)
  show ?thesis by (intro exI[of _ ?ys] conjI) (use list data ds in simp_all)
qed

subsection \<open>G3 and G4 at the given's value and the additions\<close>

lemma additions_extension_site:
  assumes family: "native_root_family_at (environment_extension E A B) u r Q"
  shows "u\<in>environment_uses E \<or> u\<in>rel_dom A"
proof -
  obtain R0 where "artifact_at (environment_extension E A B) u R0" using family by (auto simp: native_root_family_at_def)
  then have "u\<in>environment_uses (environment_extension E A B)"
    using rel_domI[of u R0] by (simp add: environment_uses_def artifact_at_def)
  then show ?thesis by (auto simp: extension_uses)
qed

theorem additions_boundary_on_values:
  assumes given: "environment_value_presents E e" and rows: "environment_rows_presents (A,B) (Pair_Term ar br)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and formed: "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
  shows "(985,Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))
      \<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>R. native_package_at (environment_extension E A B) u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or> fst d\<notin>environment_uses E))"
proof -
  let ?F="environment_extension E A B"
  let ?z="Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r))"
  have site: "term_formed (site_data_term gu gr)" and arf: "term_formed ar" "term_formed br"
    using formed by simp_all
  have outer: "environment_included E ?F" by (rule environment_extension_included)
  obtain a0 a1 where e: "e=Pair_Term a0 a1" using environment_value_uses[OF given] by blast
  have rule: "(985,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>a0 a1 gu gr ar br u r q k.
    z=Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term ar br) (Pair_Term u r)) \<and>
    term_formed ar \<and> term_formed br \<and> (47,Pair_Term q k)\<in>positive_meaning data_subset_system \<and>
    ((\<exists>l. (957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (984,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system) \<or>
     (79,citation_observation_argument (Pair_Term a0 a1) u r q)\<in>positive_meaning root_family_reading_system \<and>
     (984,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term a0 a1) k)) k)
       \<in>positive_meaning additions_goals_system))" for z
    by (rule additions_members_rule[OF additions_goals_families(6) additions_goals_families(11)]) simp_all
  show ?thesis
  proof
    assume holds: "(985,?z)\<in>positive_meaning additions_goals_system"
    obtain q k where sub: "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
      and calls: "(\<exists>l. (957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
          (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
          (984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system) \<or>
        (79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
        (984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system"
      using holds unfolding rule by (auto simp: e site_data_term_def)
    from calls show "\<exists>R. native_package_at ?F u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or> fst d\<notin>environment_uses E)"
    proof
      assume "\<exists>l. (957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
          (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
          (984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system"
      then obtain l where least: "(957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system"
        and read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system"
        and list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system" by blast
      obtain L where L: "environment_value_presents L l" "environment_bindings L=B"
        "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
        using least_environment_sound[OF given rows least] by blast
      have inner: "environment_included L ?F" using L(2,3) by (auto simp: environment_included_def)
      obtain ds where q: "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
        using read by (simp only: root_family_reading_at_source[OF L(1)]) blast
      obtain Q where Q: "native_root_family_at L u r Q" "rel_ran Q=set ds"
        using root_family_reading_recovers[OF L(1) read[unfolded q]] by blast
      show ?thesis by (rule additions_boundary_sound[OF given L(1) site inner outer ff Q sub[unfolded q] list])
    next
      assume "(79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
        (984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system"
      then have read: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)
          \<in>positive_meaning root_family_reading_system"
        and list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system" by blast+
      obtain ds where q: "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
        using read by (simp only: root_family_reading_at_source[OF given]) blast
      obtain Q where Q: "native_root_family_at E u r Q" "rel_ran Q=set ds"
        using root_family_reading_recovers[OF given read[unfolded q]] by blast
      show ?thesis by (rule additions_boundary_sound[OF given given site outer outer ff Q sub[unfolded q] list])
    qed
  next
    assume "\<exists>R. native_package_at ?F u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or> fst d\<notin>environment_uses E)"
    then obtain R where package: "native_package_at ?F u r R"
      and bounded: "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E" by blast
    obtain Q where familyF: "native_root_family_at ?F u r Q" and pformed: "native_package_formed ?F (rel_ran Q)"
      and program: "R=native_program ?F (rel_ran Q)" using package by (auto simp: native_package_at_def)
    from additions_extension_site[OF familyF] show "(985,?z)\<in>positive_meaning additions_goals_system"
    proof
      assume added_site: "u\<in>rel_dom A"
      let ?L="additions_least_environment E A B" and ?T="{z\<in>environment_artifacts E. fst z\<in>snd ` B}"
      have familyL: "native_root_family_at ?L u r Q"
        using extension_added_root_family[OF additions ff added_site] familyF by blast
      have apart: "A\<inter>?T={}"
      proof -
        have "fst z\<in>rel_dom A" if "z\<in>A" for z using that rel_domI[of "fst z" "snd z" A] by simp
        moreover have "fst z\<in>environment_uses E" if "z\<in>environment_artifacts E" for z
          using that rel_domI[of "fst z" "snd z" "environment_artifacts E"] by (simp add: environment_uses_def)
        ultimately show ?thesis using additions_parts(2)[OF additions] by blast
      qed
      have part: "?T\<subseteq>environment_artifacts E" by blast
      obtain l where l: "environment_value_presents ?L l"
        "(957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system"
        using least_environment_complete[OF given rows additions_least_formed[OF additions ff]
          additions_least_bindings[OF additions] additions_least_artifacts[OF additions] part apart additions ff] by blast
      obtain ds where read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r)
          (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
        and range: "rel_ran Q=set ds" using root_family_reading_total[OF l(1) familyL] by blast
      let ?S="system_definitions R"
      have sites: "?S=native_definition_sites ?F (rel_ran Q)" using native_program_definitions[OF pformed] program by simp
      have closed: "\<forall>d\<in>?S. \<exists>p C. native_definition_at ?F (fst d) (snd d) p C \<and>
          (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)"
        using native_package_sites_closed_bound[OF pformed] sites by simp
      have finite: "finite ?S" using native_package_sites(2)[OF pformed] sites by simp
      have covered: "\<forall>d\<in>?S. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          ((\<exists>p C. native_definition_at ?L (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)) \<and>
            fst d\<notin>environment_uses E)"
      proof
        fix d assume member: "d\<in>?S"
        show "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          ((\<exists>p C. native_definition_at ?L (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)) \<and>
            fst d\<notin>environment_uses E)"
        proof (cases "\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q")
          case True
          then show ?thesis by blast
        next
          case False
          then have outside: "fst d\<notin>environment_uses E" using bounded member by blast
          have "fst d\<in>environment_uses ?F" by (rule native_package_member_use[OF package member])
          then have added: "fst d\<in>rel_dom A" using outside by (auto simp: extension_uses)
          obtain p C where raw: "native_definition_at ?F (fst d) (snd d) p C"
            "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S" using closed member by blast
          have "native_definition_at ?L (fst d) (snd d) p C"
            using extension_added_definition[OF additions ff added] raw(1) by blast
          then show ?thesis using raw(2) outside by blast
        qed
      qed
      obtain ys where ys: "set ys=(\<lambda>d. definition_site_value d) ` ?S" "data_elements ys"
        and list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l (data_list_term ys)))
          (data_list_term ys))\<in>positive_meaning additions_goals_system"
        using additions_boundary_list_complete[OF given l(1) site finite covered] by blast
      have roots: "set ds\<subseteq>?S" using native_definition_roots[of "rel_ran Q" ?F] range sites by simp
      have sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) (data_list_term ys))
          \<in>positive_meaning data_subset_system"
        using ys roots by (auto simp: data_subset_lists)
      show ?thesis unfolding rule
        by (rule exI[of _ a0], rule exI[of _ a1], rule exI[of _ "use_data_term gu"], rule exI[of _ "Payload_Term gr"],
          rule exI[of _ ar], rule exI[of _ br], rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term r"],
          rule exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ds)"], rule exI[of _ "data_list_term ys"])
          (use e arf sub l(2) read list in \<open>auto simp: site_data_term_def\<close>)
    next
      assume given_site: "u\<in>environment_uses E"
      have packageE: "native_package_at E u r R" using extension_given_package[OF additions ff given_site] package by blast
      obtain QE where familyE: "native_root_family_at E u r QE" and eformed: "native_package_formed E (rel_ran QE)"
        and eprogram: "R=native_program E (rel_ran QE)" using packageE by (auto simp: native_package_at_def)
      let ?S="system_definitions R"
      have sites: "?S=native_definition_sites E (rel_ran QE)" using native_program_definitions[OF eformed] eprogram by simp
      have finite: "finite ?S" using native_package_sites(2)[OF eformed] sites by simp
      have covered: "\<forall>d\<in>?S. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          ((\<exists>p C. native_definition_at E (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)) \<and>
            fst d\<notin>environment_uses E)"
      proof
        fix d assume member: "d\<in>?S"
        have "fst d\<in>environment_uses E" by (rule native_package_member_use[OF packageE member])
        then show "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          ((\<exists>p C. native_definition_at E (fst d) (snd d) p C \<and> (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)) \<and>
            fst d\<notin>environment_uses E)" using bounded member by blast
      qed
      obtain ds where read: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
          (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
        and range: "rel_ran QE=set ds" using root_family_reading_total[OF given familyE] by blast
      obtain ys where ys: "set ys=(\<lambda>d. definition_site_value d) ` ?S" "data_elements ys"
        and list: "(984,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e (data_list_term ys)))
          (data_list_term ys))\<in>positive_meaning additions_goals_system"
        using additions_boundary_list_complete[OF given given site finite covered] by blast
      have roots: "set ds\<subseteq>?S" using native_definition_roots[of "rel_ran QE" E] range sites by simp
      have sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) (data_list_term ys))
          \<in>positive_meaning data_subset_system"
        using ys roots by (auto simp: data_subset_lists)
      show ?thesis unfolding rule
        by (rule exI[of _ a0], rule exI[of _ a1], rule exI[of _ "use_data_term gu"], rule exI[of _ "Payload_Term gr"],
          rule exI[of _ ar], rule exI[of _ br], rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term r"],
          rule exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ds)"], rule exI[of _ "data_list_term ys"])
          (use e arf sub read list in \<open>auto simp: site_data_term_def\<close>)
    qed
  qed
qed

theorem additions_audit_on_values:
  assumes given: "environment_value_presents E e" and rows: "environment_rows_presents (A,B) (Pair_Term ar br)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and formed: "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
  shows "(989,Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))
      \<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>R. native_package_at (environment_extension E A B) u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      (\<exists>p C. native_definition_at (environment_extension E A B) (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
proof -
  let ?F="environment_extension E A B"
  let ?z="Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r))"
  have site: "term_formed (site_data_term gu gr)" and arf: "term_formed ar" "term_formed br"
    using formed by simp_all
  have outer: "environment_included E ?F" by (rule environment_extension_included)
  obtain a0 a1 where e: "e=Pair_Term a0 a1" using environment_value_uses[OF given] by blast
  have rule: "(989,z)\<in>positive_meaning additions_goals_system \<longleftrightarrow> (\<exists>a0 a1 gu gr ar br u r q k.
    z=Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term ar br) (Pair_Term u r)) \<and>
    term_formed ar \<and> term_formed br \<and> (47,Pair_Term q k)\<in>positive_meaning data_subset_system \<and>
    ((\<exists>l. (957,Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
      (79,citation_observation_argument l u r q)\<in>positive_meaning root_family_reading_system \<and>
      (988,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term l k)) k)
        \<in>positive_meaning additions_goals_system) \<or>
     (79,citation_observation_argument (Pair_Term a0 a1) u r q)\<in>positive_meaning root_family_reading_system \<and>
     (988,Pair_Term (Pair_Term (Pair_Term (Pair_Term a0 a1) (Pair_Term gu gr)) (Pair_Term (Pair_Term a0 a1) k)) k)
       \<in>positive_meaning additions_goals_system))" for z
    by (rule additions_members_rule[OF additions_goals_families(10) additions_goals_families(12)]) simp_all
  show ?thesis
  proof
    assume holds: "(989,?z)\<in>positive_meaning additions_goals_system"
    obtain q k where sub: "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
      and calls: "(\<exists>l. (957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
          (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
          (988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system) \<or>
        (79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
        (988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system"
      using holds unfolding rule by (auto simp: e site_data_term_def)
    from calls show "\<exists>R. native_package_at ?F u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      (\<exists>p C. native_definition_at ?F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))"
    proof
      assume "\<exists>l. (957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system \<and>
          (79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
          (988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system"
      then obtain l where least: "(957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system"
        and read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system"
        and list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l k)) k)
            \<in>positive_meaning additions_goals_system" by blast
      obtain L where L: "environment_value_presents L l" "environment_bindings L=B"
        "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
        using least_environment_sound[OF given rows least] by blast
      have inner: "environment_included L ?F" using L(2,3) by (auto simp: environment_included_def)
      obtain ds where q: "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
        using read by (simp only: root_family_reading_at_source[OF L(1)]) blast
      obtain Q where Q: "native_root_family_at L u r Q" "rel_ran Q=set ds"
        using root_family_reading_recovers[OF L(1) read[unfolded q]] by blast
      show ?thesis by (rule additions_audit_sound[OF given L(1) site inner outer ff Q sub[unfolded q] list])
    next
      assume "(79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)\<in>positive_meaning root_family_reading_system \<and>
        (988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system"
      then have read: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r) q)
          \<in>positive_meaning root_family_reading_system"
        and list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e k)) k)
          \<in>positive_meaning additions_goals_system" by blast+
      obtain ds where q: "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
        using read by (simp only: root_family_reading_at_source[OF given]) blast
      obtain Q where Q: "native_root_family_at E u r Q" "rel_ran Q=set ds"
        using root_family_reading_recovers[OF given read[unfolded q]] by blast
      show ?thesis by (rule additions_audit_sound[OF given given site outer outer ff Q sub[unfolded q] list])
    qed
  next
    assume "\<exists>R. native_package_at ?F u r R \<and> (\<forall>d\<in>system_definitions R.
      (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
      (\<exists>p C. native_definition_at ?F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))"
    then obtain R where package: "native_package_at ?F u r R"
      and bounded: "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
        (\<exists>p C. native_definition_at ?F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})" by blast
    obtain Q where familyF: "native_root_family_at ?F u r Q" and pformed: "native_package_formed ?F (rel_ran Q)"
      and program: "R=native_program ?F (rel_ran Q)" using package by (auto simp: native_package_at_def)
    from additions_extension_site[OF familyF] show "(989,?z)\<in>positive_meaning additions_goals_system"
    proof
      assume added_site: "u\<in>rel_dom A"
      let ?L="additions_least_environment E A B" and ?T="{z\<in>environment_artifacts E. fst z\<in>snd ` B}"
      have familyL: "native_root_family_at ?L u r Q"
        using extension_added_root_family[OF additions ff added_site] familyF by blast
      have apart: "A\<inter>?T={}"
      proof -
        have "fst z\<in>rel_dom A" if "z\<in>A" for z using that rel_domI[of "fst z" "snd z" A] by simp
        moreover have "fst z\<in>environment_uses E" if "z\<in>environment_artifacts E" for z
          using that rel_domI[of "fst z" "snd z" "environment_artifacts E"] by (simp add: environment_uses_def)
        ultimately show ?thesis using additions_parts(2)[OF additions] by blast
      qed
      have part: "?T\<subseteq>environment_artifacts E" by blast
      obtain l where l: "environment_value_presents ?L l"
        "(957,Pair_Term (Pair_Term e (Pair_Term ar br)) l)\<in>positive_meaning extension_package_system"
        using least_environment_complete[OF given rows additions_least_formed[OF additions ff]
          additions_least_bindings[OF additions] additions_least_artifacts[OF additions] part apart additions ff] by blast
      obtain ds where read: "(79,citation_observation_argument l (use_data_term u) (Payload_Term r)
          (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
        and range: "rel_ran Q=set ds" using root_family_reading_total[OF l(1) familyL] by blast
      let ?S="system_definitions R"
      have sites: "?S=native_definition_sites ?F (rel_ran Q)" using native_program_definitions[OF pformed] program by simp
      have closed: "\<forall>d\<in>?S. \<exists>p C. native_definition_at ?F (fst d) (snd d) p C \<and>
          (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)"
        using native_package_sites_closed_bound[OF pformed] sites by simp
      have finite: "finite ?S" using native_package_sites(2)[OF pformed] sites by simp
      have covered: "\<forall>d\<in>?S. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. (native_definition_at ?L (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
            (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S) \<and> definition_payloads p C\<subseteq>{[]})"
      proof
        fix d assume member: "d\<in>?S"
        show "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. (native_definition_at ?L (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
            (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S) \<and> definition_payloads p C\<subseteq>{[]})"
        proof (cases "\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q")
          case True
          then show ?thesis by blast
        next
          case False
          then obtain p C where audited: "native_definition_at ?F (fst d) (snd d) p C" "definition_payloads p C\<subseteq>{[]}"
            using bounded member by blast
          obtain p' C' where raw: "native_definition_at ?F (fst d) (snd d) p' C'"
            "\<forall>c S. (c,S)\<in>C' \<longrightarrow> schema_dependencies S\<subseteq>?S" using closed member by blast
          have same: "p'=p \<and> C'=C" by (rule native_definition_unique[OF raw(1) audited(1)])
          have "fst d\<in>environment_uses ?F" by (rule native_package_member_use[OF package member])
          then consider (added) "fst d\<in>rel_dom A" | (old) "fst d\<in>environment_uses E" by (auto simp: extension_uses)
          then have "native_definition_at ?L (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C"
          proof cases
            case added
            then show ?thesis using extension_added_definition[OF additions ff added] audited(1) by blast
          next
            case old
            then show ?thesis using extension_given_definition[OF additions ff old] audited(1) by blast
          qed
          then show ?thesis using raw(2) same audited(2) by blast
        qed
      qed
      obtain ys where ys: "set ys=(\<lambda>d. definition_site_value d) ` ?S" "data_elements ys"
        and list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term l (data_list_term ys)))
          (data_list_term ys))\<in>positive_meaning additions_goals_system"
        using additions_audit_list_complete[OF given l(1) site finite covered] by blast
      have roots: "set ds\<subseteq>?S" using native_definition_roots[of "rel_ran Q" ?F] range sites by simp
      have sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) (data_list_term ys))
          \<in>positive_meaning data_subset_system"
        using ys roots by (auto simp: data_subset_lists)
      show ?thesis unfolding rule
        by (rule exI[of _ a0], rule exI[of _ a1], rule exI[of _ "use_data_term gu"], rule exI[of _ "Payload_Term gr"],
          rule exI[of _ ar], rule exI[of _ br], rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term r"],
          rule exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ds)"], rule exI[of _ "data_list_term ys"])
          (use e arf sub l(2) read list in \<open>auto simp: site_data_term_def\<close>)
    next
      assume given_site: "u\<in>environment_uses E"
      have packageE: "native_package_at E u r R" using extension_given_package[OF additions ff given_site] package by blast
      obtain QE where familyE: "native_root_family_at E u r QE" and eformed: "native_package_formed E (rel_ran QE)"
        and eprogram: "R=native_program E (rel_ran QE)" using packageE by (auto simp: native_package_at_def)
      let ?S="system_definitions R"
      have sites: "?S=native_definition_sites E (rel_ran QE)" using native_program_definitions[OF eformed] eprogram by simp
      have eclosed: "\<forall>d\<in>?S. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
          (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S)"
        using native_package_sites_closed_bound[OF eformed] sites by simp
      have finite: "finite ?S" using native_package_sites(2)[OF eformed] sites by simp
      have covered: "\<forall>d\<in>?S. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. (native_definition_at E (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
            (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S) \<and> definition_payloads p C\<subseteq>{[]})"
      proof
        fix d assume member: "d\<in>?S"
        show "(\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. (native_definition_at E (fst d) (snd d) p C \<or> native_definition_at E (fst d) (snd d) p C) \<and>
            (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?S) \<and> definition_payloads p C\<subseteq>{[]})"
        proof (cases "\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q")
          case True
          then show ?thesis by blast
        next
          case False
          then obtain p C where audited: "native_definition_at ?F (fst d) (snd d) p C" "definition_payloads p C\<subseteq>{[]}"
            using bounded member by blast
          have old: "fst d\<in>environment_uses E" by (rule native_package_member_use[OF packageE member])
          have edef: "native_definition_at E (fst d) (snd d) p C"
            using extension_given_definition[OF additions ff old] audited(1) by blast
          obtain p' C' where raw: "native_definition_at E (fst d) (snd d) p' C'"
            "\<forall>c S. (c,S)\<in>C' \<longrightarrow> schema_dependencies S\<subseteq>?S" using eclosed member by blast
          have same: "p'=p \<and> C'=C" by (rule native_definition_unique[OF raw(1) edef])
          then show ?thesis using edef raw(2) audited(2) by blast
        qed
      qed
      obtain ds where read: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
          (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
        and range: "rel_ran QE=set ds" using root_family_reading_total[OF given familyE] by blast
      obtain ys where ys: "set ys=(\<lambda>d. definition_site_value d) ` ?S" "data_elements ys"
        and list: "(988,Pair_Term (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term e (data_list_term ys)))
          (data_list_term ys))\<in>positive_meaning additions_goals_system"
        using additions_audit_list_complete[OF given given site finite covered] by blast
      have roots: "set ds\<subseteq>?S" using native_definition_roots[of "rel_ran QE" E] range sites by simp
      have sub: "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) (data_list_term ys))
          \<in>positive_meaning data_subset_system"
        using ys roots by (auto simp: data_subset_lists)
      show ?thesis unfolding rule
        by (rule exI[of _ a0], rule exI[of _ a1], rule exI[of _ "use_data_term gu"], rule exI[of _ "Payload_Term gr"],
          rule exI[of _ ar], rule exI[of _ br], rule exI[of _ "use_data_term u"], rule exI[of _ "Payload_Term r"],
          rule exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ds)"], rule exI[of _ "data_list_term ys"])
          (use e arf sub read list in \<open>auto simp: site_data_term_def\<close>)
    qed
  qed
qed

section \<open>The four sockets at the pair of a site value and an additions value\<close>

lemma additions_pair_parts:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
  obtains e ar br where "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
proof -
  obtain e where e: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    using first by (auto simp: site_value_presents_def)
  obtain p where p: "environment_rows_presents (A,B) p" "a=Pair_Term p (site_data_term u r)"
    using second by (auto simp: additions_value_presents_def)
  obtain ar br where "p=Pair_Term ar br" using p(1) by (auto simp: environment_rows_presents_def)
  then show ?thesis using that e p by blast
qed

lemma additions_pair_formed:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and relation: "additions_formation_relation (E,((A,B),(u,r)))"
  shows "term_formed (Pair_Term t a)"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    by (rule additions_pair_parts[OF first second])
  have pair: "additions_pair_presents (E,((A,B),(u,r))) (Pair_Term e a)"
    using parts(1) second by (simp add: additions_pair_presents_def factor_pair_presents_def)
  have holds: "(954,Pair_Term e a)\<in>positive_meaning extension_formation_system"
    using extension_formation_on_pairs[OF pair] relation by simp
  have "term_formed (Pair_Term e a)" using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by simp
  then show ?thesis using site_value_presents_formed[OF first] by simp
qed

theorem additions_retention_on_pairs:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
  shows "(980,Pair_Term t a)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    additions_formation_relation (E,((A,B),(u,r)))"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    by (rule additions_pair_parts[OF first second])
  have pair: "additions_pair_presents (E,((A,B),(u,r))) (Pair_Term e a)"
    using parts(1) second by (simp add: additions_pair_presents_def factor_pair_presents_def)
  have sf: "term_formed (site_data_term gu gr)" using site_value_presents_formed[OF first] parts(2) by simp
  show ?thesis
    using extension_formation_on_pairs[OF pair] sf by (auto simp: additions_retention_rule parts(2))
qed

lemma additions_sockets_at_values:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and relation: "additions_formation_relation (E,((A,B),(u,r)))"
  obtains e ar br where "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    "environment_additions E A B" "environment_formed (environment_extension E A B)"
    "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    by (rule additions_pair_parts[OF first second])
  have "term_formed (Pair_Term t a)" by (rule additions_pair_formed[OF first second relation])
  then show ?thesis using that parts relation by simp
qed

theorem additions_package_on_pairs:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and relation: "additions_formation_relation (E,((A,B),(u,r)))"
  shows "(981,Pair_Term t a)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    (\<exists>R. native_package_at (environment_extension E A B) u r R)"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    "environment_additions E A B" "environment_formed (environment_extension E A B)"
    "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
    by (rule additions_sockets_at_values[OF first second relation])
  have spf: "term_formed (Pair_Term (source_root_argument e (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term ar br) (site_data_term u r)))" using parts(7) by (simp add: site_data_term_def)
  have package: "(961,Pair_Term (source_root_argument e (use_data_term gu) (Payload_Term gr))
      (Pair_Term (Pair_Term ar br) (site_data_term u r)))\<in>positive_meaning extension_package_system \<longleftrightarrow>
    (\<exists>P. native_package_at (environment_extension E A B) u r P)"
    by (rule extension_package_at_values[OF parts(1) parts(3) parts(5) parts(6) spf])
  show ?thesis using package by (auto simp: additions_package_rule parts(2,4) site_data_term_def)
qed

theorem additions_boundary_on_pairs:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and relation: "additions_formation_relation (E,((A,B),(u,r)))"
  shows "(985,Pair_Term t a)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E) ((E,gu,gr),(environment_extension E A B,u,r))"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    "environment_additions E A B" "environment_formed (environment_extension E A B)"
    "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
    by (rule additions_sockets_at_values[OF first second relation])
  show ?thesis using additions_boundary_on_values[OF parts(1) parts(3) parts(5) parts(6) parts(7)] parts(2,4) by simp
qed

theorem additions_audit_on_pairs:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and relation: "additions_formation_relation (E,((A,B),(u,r)))"
  shows "(989,Pair_Term t a)\<in>positive_meaning additions_goals_system \<longleftrightarrow>
    package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      definition_payloads p C\<subseteq>{[]}) ((E,gu,gr),(environment_extension E A B,u,r))"
proof -
  obtain e ar br where parts: "environment_value_presents E e" "t=Pair_Term e (site_data_term gu gr)"
    "environment_rows_presents (A,B) (Pair_Term ar br)" "a=Pair_Term (Pair_Term ar br) (site_data_term u r)"
    "environment_additions E A B" "environment_formed (environment_extension E A B)"
    "term_formed (Pair_Term (Pair_Term e (site_data_term gu gr)) (Pair_Term (Pair_Term ar br) (site_data_term u r)))"
    by (rule additions_sockets_at_values[OF first second relation])
  show ?thesis using additions_audit_on_values[OF parts(1) parts(3) parts(5) parts(6) parts(7)] parts(2,4) by simp
qed

section \<open>The guard over additions: four sockets, each a separate requirement on the whole pair\<close>

definition additions_requirements :: "(nat\<times>nat) set" where
  "additions_requirements={(0,980),(1,981),(2,985),(3,989)}"

interpretation additions_guard:
  requirement_guard_extension additions_goals_system 990 additions_requirements
proof
  show "schema_system_formed additions_goals_system" by simp
  show "990\<notin>system_definitions additions_goals_system" using additions_fresh[of 990] by simp
  show "finite additions_requirements" by (simp add: additions_requirements_def)
  show "single_valued additions_requirements" by (auto simp: additions_requirements_def single_valued_def)
  show "rel_ran additions_requirements\<subseteq>system_definitions additions_goals_system"
    by (auto simp: additions_requirements_def rel_ran_def)
qed

abbreviation additions_guard_system :: "(nat,nat,nat,nat) schema_system" where
  "additions_guard_system\<equiv>install_requirement_guard additions_goals_system 990 additions_requirements"

text \<open>
  The guard's relation, on the given's site context and the additions' data: the extension is formed (G1); the
  candidate's site holds a package of the extension (G2); every member of that package is the given's or stands at
  a use of no given artifact (G3); every member is the given's or states no payload but the empty one (G4). G3 and
  G4 are the relation of the notion of additions (@{const package_additions_relation}) at the given's site context
  and the candidate's, the extension with the additions' site.
\<close>

abbreviation additions_candidate where
  "additions_candidate x \<equiv> (environment_extension (fst (fst x)) (fst (fst (snd x))) (snd (fst (snd x))),snd (snd x))"

abbreviation additions_guard_relation where
  "additions_guard_relation x \<equiv> additions_formation_relation (fst (fst x),snd x) \<and>
    extension_package_relation (fst (fst x),snd x) \<and>
    package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E) (fst x,additions_candidate x) \<and>
    package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
      definition_payloads p C\<subseteq>{[]}) (fst x,additions_candidate x)"

lemma additions_guard_sockets:
  "(990,z)\<in>positive_meaning additions_guard_system \<longleftrightarrow> term_formed z \<and>
    (980,z)\<in>positive_meaning additions_goals_system \<and> (981,z)\<in>positive_meaning additions_goals_system \<and>
    (985,z)\<in>positive_meaning additions_goals_system \<and> (989,z)\<in>positive_meaning additions_goals_system"
proof -
  have unchanged: "(d,z)\<in>positive_meaning additions_guard_system \<longleftrightarrow> (d,z)\<in>positive_meaning additions_goals_system"
    if "d\<in>system_definitions additions_goals_system" for d
    by (rule additions_guard.unchanged_original_meaning[OF that])
  show ?thesis
    using additions_guard.guard.exact[of z] unchanged[of 980] unchanged[of 981] unchanged[of 985] unchanged[of 989]
    by (simp add: additions_requirements_def)
qed

theorem additions_guard_on_pairs:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
  shows "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
    additions_guard_relation ((E,(gu,gr)),((A,B),(u,r)))"
proof
  assume "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system"
  then have sockets: "(980,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    "(981,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    "(985,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    "(989,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    by (simp_all add: additions_guard_sockets)
  have relation: "additions_formation_relation (E,((A,B),(u,r)))"
    using sockets(1) additions_retention_on_pairs[OF first second] by blast
  show "additions_guard_relation ((E,(gu,gr)),((A,B),(u,r)))"
    using relation sockets(2-4) additions_package_on_pairs[OF first second relation]
      additions_boundary_on_pairs[OF first second relation] additions_audit_on_pairs[OF first second relation]
    by simp
next
  assume holds: "additions_guard_relation ((E,(gu,gr)),((A,B),(u,r)))"
  then have relation: "additions_formation_relation (E,((A,B),(u,r)))" by simp
  have formed: "term_formed (Pair_Term t a)" by (rule additions_pair_formed[OF first second relation])
  show "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system"
    using holds formed additions_retention_on_pairs[OF first second] additions_package_on_pairs[OF first second relation]
      additions_boundary_on_pairs[OF first second relation] additions_audit_on_pairs[OF first second relation]
    by (simp add: additions_guard_sockets)
qed

section \<open>Each socket is exact to its predecessor at the given and its extension\<close>

text \<open>
  A candidate of the first problem is presented by its additions relative to the given (@{const additions_presents}):
  its environment includes the given's, and its bindings not the given's are sourced at uses the given does not
  hold. That domain is a residual choice (task 928's verdict, answer 2): a candidate adds its own artifacts and
  their bindings, sourced at the uses it adds, so that every reading of the given stays exact under an answer,
  which is what retention asks; a binding added at an address of a given artifact is not a candidate. On that
  domain each socket of the guard over additions holds exactly where its predecessor's socket of the guard over
  site values holds at the given's site value and a site value of the candidate, and so does the guard.
\<close>

lemma additions_presents_parts:
  assumes presented: "additions_presents E (F,(u,r)) a"
  shows "additions_value_presents (added_rows E F,(u,r)) a"
    and "environment_additions E (fst (added_rows E F)) (snd (added_rows E F))"
    and "F=environment_extension E (fst (added_rows E F)) (snd (added_rows E F))"
    and "environment_formed F" and "(u,r)\<in>environment_positions F" and "environment_included E F"
  using presented additions_domain_extension[of E F "(u,r)"] by (auto simp: additions_presents_def additions_domain_def)

lemma additions_presents_relation:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
  shows "additions_formation_relation (E,(added_rows E F,(u,r)))"
proof -
  obtain e where e: "environment_value_presents E e" using first by (auto simp: site_value_presents_def)
  obtain f where f: "environment_value_presents F f"
    using environment_value_presents_total additions_presents_parts(4)[OF presented] by blast
  have holds: "(954,Pair_Term e a)\<in>positive_meaning extension_formation_system"
    by (rule extension_formation_on_additions(1)[OF e presented f])
  have pair: "additions_pair_presents (E,(added_rows E F,(u,r))) (Pair_Term e a)"
    using e additions_presents_parts(1)[OF presented] by (simp add: additions_pair_presents_def factor_pair_presents_def)
  show ?thesis using extension_formation_on_pairs[OF pair] holds by blast
qed

theorem additions_sockets_exact:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
    and candidate: "site_value_presents F u r w"
  shows "(980,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (520,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    and "(981,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (521,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    and "(985,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (392,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    and "(989,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (525,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
proof -
  obtain A B where AB: "added_rows E F=(A,B)" by fastforce
  have second: "additions_value_presents ((A,B),(u,r)) a" using additions_presents_parts(1)[OF presented] AB by simp
  have relation: "additions_formation_relation (E,((A,B),(u,r)))" using additions_presents_relation[OF first presented] AB by simp
  have F: "F=environment_extension E A B" using additions_presents_parts(3)[OF presented] AB by simp
  have included: "environment_included E F" by (rule additions_presents_parts(6)[OF presented])
  have unchanged: "(d,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (d,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    if "d\<in>system_definitions additions_goals_system" for d
    by (rule additions_guard.unchanged_original_meaning[OF that])
  show "(980,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (520,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    using unchanged[of 980] additions_retention_on_pairs[OF first second] relation
      guard_socket_meanings(1)[OF first candidate] included by simp
  show "(981,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (521,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    using unchanged[of 981] additions_package_on_pairs[OF first second relation]
      guard_socket_meanings(2)[OF first candidate] F by simp
  show "(985,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (392,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    using unchanged[of 985] additions_boundary_on_pairs[OF first second relation]
      guard_socket_meanings(3)[OF first candidate] F by simp
  show "(989,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (525,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    using unchanged[of 989] additions_audit_on_pairs[OF first second relation]
      guard_socket_meanings(4)[OF first candidate] F by simp
qed

theorem additions_guard_first_problem:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
    and candidate: "site_value_presents F u r w"
  shows "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
    (526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
proof -
  obtain A B where AB: "added_rows E F=(A,B)" by fastforce
  have second: "additions_value_presents ((A,B),(u,r)) a" using additions_presents_parts(1)[OF presented] AB by simp
  have relation: "additions_formation_relation (E,((A,B),(u,r)))" using additions_presents_relation[OF first presented] AB by simp
  have ta: "term_formed (Pair_Term t a)" by (rule additions_pair_formed[OF first second relation])
  have tw: "term_formed (Pair_Term t w)"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF candidate] by simp
  have unchanged: "(d,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
      (d,Pair_Term t a)\<in>positive_meaning additions_goals_system"
    if "d\<in>system_definitions additions_goals_system" for d
    by (rule additions_guard.unchanged_original_meaning[OF that])
  have old: "(526,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow> term_formed (Pair_Term t w) \<and>
      (520,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
      (521,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
      (392,Pair_Term t w)\<in>positive_meaning first_problem_guard_system \<and>
      (525,Pair_Term t w)\<in>positive_meaning first_problem_guard_system"
    using first_problem_guard.guard.exact[of "Pair_Term t w"] by (simp add: first_problem_requirements_def)
  show ?thesis
    using old ta tw additions_guard_sockets[of "Pair_Term t a"] unchanged[of 980] unchanged[of 981] unchanged[of 985]
      unchanged[of 989] additions_sockets_exact[OF first presented candidate] by simp
qed

section \<open>The contract in the words of the requirement\<close>

theorem additions_guard_contract:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
  shows "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
    environment_included E F \<and> (\<exists>R. native_package_at F u r R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
proof -
  have placed: "environment_formed F \<and> (u,r)\<in>environment_positions F"
    using additions_presents_parts(4,5)[OF presented] by simp
  obtain w where candidate: "site_value_presents F u r w" using site_presentations.total[of "(F,(u,r))"] placed by auto
  show ?thesis
    using additions_guard_first_problem[OF first presented candidate] first_problem_guard_contract[OF first candidate]
    by simp
qed

text \<open>A failing socket refuses the guard, and the socket that failed is named.\<close>

theorem additions_guard_refusal:
  assumes "(s,g)\<in>additions_requirements" "(g,z)\<notin>positive_meaning additions_guard_system"
  shows "(990,z)\<notin>positive_meaning additions_guard_system"
  by (rule additions_guard.guard.failed_requirement[OF assms])

corollary additions_guard_refusals:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
  shows "\<not>environment_included E F \<Longrightarrow> (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    and "\<not>(\<exists>R. native_package_at F u r R) \<Longrightarrow> (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    and "\<not>(\<exists>R. native_package_at F u r R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          fst d\<notin>environment_uses E)) \<Longrightarrow>
      (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    and "\<not>(\<exists>R. native_package_at F u r R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))) \<Longrightarrow>
      (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
proof -
  have placed: "environment_formed F \<and> (u,r)\<in>environment_positions F"
    using additions_presents_parts(4,5)[OF presented] by simp
  obtain w where candidate: "site_value_presents F u r w" using site_presentations.total[of "(F,(u,r))"] placed by auto
  have sockets: "(0,980)\<in>additions_requirements" "(1,981)\<in>additions_requirements"
    "(2,985)\<in>additions_requirements" "(3,989)\<in>additions_requirements"
    by (simp_all add: additions_requirements_def)
  show "\<not>environment_included E F \<Longrightarrow> (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    using additions_guard_refusal[OF sockets(1)] additions_sockets_exact(1)[OF first presented candidate]
      guard_socket_meanings(1)[OF first candidate] by blast
  show "\<not>(\<exists>R. native_package_at F u r R) \<Longrightarrow> (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    using additions_guard_refusal[OF sockets(2)] additions_sockets_exact(2)[OF first presented candidate]
      guard_socket_meanings(2)[OF first candidate] by blast
  show "\<not>(\<exists>R. native_package_at F u r R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          fst d\<notin>environment_uses E)) \<Longrightarrow>
      (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    using additions_guard_refusal[OF sockets(3)] additions_sockets_exact(3)[OF first presented candidate]
      guard_socket_meanings(3)[OF first candidate] by blast
  show "\<not>(\<exists>R. native_package_at F u r R \<and>
        (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
          (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}))) \<Longrightarrow>
      (990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
    using additions_guard_refusal[OF sockets(4)] additions_sockets_exact(4)[OF first presented candidate]
      guard_socket_meanings(4)[OF first candidate] by blast
qed

corollary additions_retention_refusal:
  assumes first: "site_value_presents E gu gr t" and second: "additions_value_presents ((A,B),(u,r)) a"
    and failed: "\<not>additions_formation_relation (E,((A,B),(u,r)))"
  shows "(990,Pair_Term t a)\<notin>positive_meaning additions_guard_system"
  using additions_guard_on_pairs[OF first second] failed by auto

corollary additions_guard_invariance:
  assumes "site_value_presents E gu gr t" "site_value_presents E gu gr t'"
    "additions_value_presents ((A,B),(u,r)) a" "additions_value_presents ((A,B),(u,r)) a'"
  shows "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
    (990,Pair_Term t' a')\<in>positive_meaning additions_guard_system"
  by (simp only: additions_guard_on_pairs[OF assms(1,3)] additions_guard_on_pairs[OF assms(2,4)])

corollary additions_guard_presentation_invariance:
  assumes "site_value_presents E gu gr t" "site_value_presents E gu gr t'"
    "additions_presents E (F,(u,r)) a" "additions_presents E (F,(u,r)) a'"
  shows "(990,Pair_Term t a)\<in>positive_meaning additions_guard_system \<longleftrightarrow>
    (990,Pair_Term t' a')\<in>positive_meaning additions_guard_system"
  by (simp only: additions_guard_contract[OF assms(1,3)] additions_guard_contract[OF assms(2,4)])

section \<open>The guard over additions is equivariant under permutations of uses\<close>

text \<open>
  A permutation of uses acts on the given's site context by the site-context action and on the additions by their
  use action (@{thm [source] additions_renaming_action}): the environment action on their rows and bindings and the
  site action on their site. The extension moves with them (@{thm [source] environment_extension_renaming}). Each
  socket's relation is kept by its own clause, consumed as stated: G1's by the extension's formation
  (@{thm [source] extension_formation_equivariant}), G2's by the package's clause
  (@{thm [source] extension_package_equivariant}), G3's and
  G4's by the notion of additions' clause (@{thm [source] package_additions_renamed}) at their callees' clauses
  (@{thm [source] use_absence_callee_equivariant}, @{thm [source] audit_callee_equivariant}, the latter the audit's
  own, @{thm [source] payload_audit_equivariant}). The guard's presented form is then invariant along every renaming
  correspondence of the pair (@{thm [source] presented_observation_renaming}).
\<close>


lemma added_rows_renaming:
  assumes permutation: "bij h"
  shows "added_rows (rename_environment h E) (rename_environment h F)=
    ((\<lambda>(u,R). (h u,R)) ` fst (added_rows E F),(\<lambda>((u,k),v). ((h u,k),h v)) ` snd (added_rows E F))"
proof -
  have inj: "inj h" by (rule bij_is_inj[OF permutation])
  have rows: "inj (\<lambda>(u,R). (h u,R::exact_artifact))"
    using inj by (auto simp: inj_def inj_eq split: prod.splits)
  have binds: "inj (\<lambda>((u,k),v). ((h u,k::local_address),h v))"
    using inj by (auto simp: inj_def inj_eq split: prod.splits)
  show ?thesis
    by (simp add: added_rows_def rename_environment_def image_set_diff[OF rows] image_set_diff[OF binds])
qed

theorem additions_guard_equivariant:
  "renaming_equivariant bij (product_action site_context_renaming additions_renaming)
    (\<lambda>x. site_context_formed (fst x) \<and> additions_data_domain (snd x)) additions_guard_relation"
proof (unfold renaming_equivariant_def, intro allI impI, goal_cases)
  case (1 h x)
  then have permutation: "bij h" and domain: "site_context_formed (fst x) \<and> additions_data_domain (snd x)"
    by simp_all
  obtain E gu gr A B u r where x: "x=((E,(gu,gr)),((A,B),(u,r)))" by (metis prod.collapse)
  let ?F="environment_extension E A B"
  let ?A="(\<lambda>(u,R). (h u,R)) ` A" and ?B="(\<lambda>((u,k),v). ((h u,k),h v)) ` B"
  have extension: "environment_extension (rename_environment h E) ?A ?B=rename_environment h ?F"
    by (simp add: environment_extension_renaming)
  have moved: "additions_guard_relation (product_action site_context_renaming additions_renaming h x) \<longleftrightarrow>
      (environment_additions (rename_environment h E) ?A ?B \<and> environment_formed (rename_environment h ?F) \<and>
        octets_formed r) \<and>
      (\<exists>P. native_package_at (rename_environment h ?F) (h u) r P) \<and>
      package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E)
        (package_additions_renaming h ((E,gu,gr),(?F,u,r))) \<and>
      package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
        definition_payloads p C\<subseteq>{[]}) (package_additions_renaming h ((E,gu,gr),(?F,u,r)))"
    by (simp add: x extension)
  have original: "additions_guard_relation x \<longleftrightarrow>
      (environment_additions E A B \<and> environment_formed ?F \<and> octets_formed r) \<and>
      (\<exists>P. native_package_at ?F u r P) \<and>
      package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E) ((E,gu,gr),(?F,u,r)) \<and>
      package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
        definition_payloads p C\<subseteq>{[]}) ((E,gu,gr),(?F,u,r))"
    by (simp add: x)
  have formation: "(environment_additions (rename_environment h E) ?A ?B \<and>
        environment_formed (rename_environment h ?F) \<and> octets_formed r) \<longleftrightarrow>
      (environment_additions E A B \<and> environment_formed ?F \<and> octets_formed r)"
    using extension_formation_equivariant[unfolded renaming_equivariant_def, rule_format, OF permutation,
      of "(E,((A,B),(u,r)))"] domain by (simp add: x extension)
  have package: "(\<exists>Q. native_package_at (rename_environment h ?F) (h u) r Q) \<longleftrightarrow>
      (\<exists>P. native_package_at ?F u r P)" if ff: "environment_formed ?F"
    using extension_package_equivariant[unfolded renaming_equivariant_def, rule_format, OF permutation,
      of "(E,((A,B),(u,r)))"] domain ff by (simp add: x extension)
  show ?case
  proof (cases "environment_additions E A B \<and> environment_formed ?F \<and> octets_formed r \<and>
      (\<exists>P. native_package_at ?F u r P)")
    case False
    then show ?thesis unfolding moved original using formation package by blast
  next
    case True
    then have ff: "environment_formed ?F" by blast
    obtain P where "native_package_at ?F u r P" using True by blast
    then have position: "(u,r)\<in>environment_positions ?F" by (rule native_package_site_position)
    have contexts: "site_context_formed (E,gu,gr) \<and> site_context_formed (?F,u,r)"
      using domain ff position by (simp add: x)
    show ?thesis
    proof -
      have boundary: "package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E)
          (package_additions_renaming h ((E,gu,gr),(?F,u,r))) \<longleftrightarrow>
        package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E) ((E,gu,gr),(?F,u,r))"
        by (rule package_additions_renamed[OF use_absence_callee_equivariant permutation contexts])
      have audit: "package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
            definition_payloads p C\<subseteq>{[]}) (package_additions_renaming h ((E,gu,gr),(?F,u,r))) \<longleftrightarrow>
        package_additions_relation (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and>
            definition_payloads p C\<subseteq>{[]}) ((E,gu,gr),(?F,u,r))"
        by (rule package_additions_renamed[OF audit_callee_equivariant permutation contexts])
      show ?thesis unfolding moved original using formation package[OF ff] boundary audit by blast
    qed
  qed
qed

theorem additions_value_class:
  "presentation_class additions_value_presents additions_data_domain (\<lambda>t. \<exists>z. additions_value_presents z t)"
proof (rule presentation_class.intro, goal_cases)
  case (1 z t)
  then obtain p where p: "environment_rows_presents (fst z) p" unfolding additions_value_presents_def by blast
  show ?case using environment_rows_domain[of "fst (fst z)" "snd (fst z)" p "snd z"] p by simp
next
  case (2 z t) then show ?case by blast
next
  case (3 z)
  obtain p where p: "environment_rows_presents (fst (fst z),snd (fst z)) p"
    using environment_rows_total[of "fst (fst z)" "snd (fst z)"] 3 by (auto simp: additions_data_domain_def)
  show ?case using p by (auto simp: additions_value_presents_def)
next
  case (4 t) then show ?case .
next
  case (5 z t y) then show ?case by (rule additions_value_unique)
qed

abbreviation additions_guard_presents where
  "additions_guard_presents \<equiv> factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
    additions_value_presents"

lemma additions_guard_presentation_class:
  "presentation_class additions_guard_presents (\<lambda>x. site_context_formed (fst x) \<and> additions_data_domain (snd x))
    (\<lambda>p. \<exists>x. additions_guard_presents x p)"
  using presentation_class.recovered_admission[OF factor_pair_class[OF site_presentations.presentation_class_axioms
    additions_value_class]] by simp

lemma additions_guard_observed:
  assumes presented: "additions_guard_presents x p"
  shows "(990,p)\<in>positive_meaning additions_guard_system \<longleftrightarrow> additions_guard_relation x"
proof -
  obtain E gu gr A B u r where x: "x=((E,(gu,gr)),((A,B),(u,r)))" by (metis prod.collapse)
  obtain t a where t: "site_value_presents E gu gr t" and a: "additions_value_presents ((A,B),(u,r)) a"
    and p: "p=Pair_Term t a"
    using presented unfolding x factor_pair_presents_def by auto
  show ?thesis using additions_guard_on_pairs[OF t a] by (simp add: p x)
qed

corollary additions_guard_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence additions_guard_presents
      (product_action site_context_renaming additions_renaming) h) (=)
    (\<lambda>p. (990,p)\<in>positive_meaning additions_guard_system) (\<lambda>p. (990,p)\<in>positive_meaning additions_guard_system)"
  using presented_observation_renaming[where observe="\<lambda>p. (990,p)\<in>positive_meaning additions_guard_system"
      and P="\<lambda>x. additions_guard_relation x", OF additions_guard_presentation_class
      renaming_action_product[OF site_context_renaming_action additions_renaming_action] additions_guard_observed]
    additions_guard_equivariant by blast

section \<open>What the new clauses leave to a producer, and the payloads they state\<close>

text \<open>
  Read for commitment: the views of G1 and G2 and the two callees bind every variable their premises use in their
  heads; the element and list clauses are the notion of additions' and the context list's, read where they were
  installed. The two members clauses hold premise-only witnesses: at a site of an added use the least environment
  (variable 8), read beside the view (991, 992) whose clause holds the root family read there (9) and the bound
  (10); at a site of a given use the root family and the bound. Every premise holding a witness has no other free
  variable, as W2's registrations need (task 961). They are the witnesses of 961's added-site clause and 960's bound,
  handed in by a producer for an admission
  and collected for a refusal where the asked program is installed; each of G3 and G4 receives them again, since
  every socket receives the whole pair and nothing else. No socket of these clauses is declared here.
\<close>

lemma additions_premise_only_variables:
  "schema_variables additions_retention_schema=pattern_variables (schema_conclusion additions_retention_schema)"
  "schema_variables additions_package_schema=pattern_variables (schema_conclusion additions_package_schema)"
  "schema_variables additions_boundary_callee_schema=pattern_variables (schema_conclusion additions_boundary_callee_schema)"
  "schema_variables additions_audit_read_schema=pattern_variables (schema_conclusion additions_audit_read_schema)"
  "schema_variables additions_audit_given_schema=pattern_variables (schema_conclusion additions_audit_given_schema)"
  "schema_variables (additions_members_added_schema ls)-
    pattern_variables (schema_conclusion (additions_members_added_schema ls))={8}"
  "schema_variables (additions_members_view_schema ls)-
    pattern_variables (schema_conclusion (additions_members_view_schema ls))={9,10}"
  "schema_variables (additions_members_given_schema ls)-
    pattern_variables (schema_conclusion (additions_members_given_schema ls))={9,10}"
  by (auto simp: schema_variables_def additions_retention_schema_def additions_package_schema_def
    additions_boundary_callee_schema_def additions_audit_read_schema_def additions_audit_given_schema_def
    additions_members_added_schema_def additions_members_given_schema_def additions_members_view_schema_def)

lemma additions_pair_readers_payloads [lineage_payloads]: "system_payloads additions_pair_readers_system\<subseteq>{[]}"
  unfolding additions_pair_readers_system_def by (intro lineage_payload_steps lineage_payloads)

lemma additions_readers_payloads [lineage_payloads]: "system_payloads additions_readers_system\<subseteq>{[]}"
  unfolding additions_readers_system_def by (intro lineage_payload_steps lineage_payloads)

lemma additions_retention_system_payloads [lineage_payloads]: "system_payloads additions_retention_system\<subseteq>{[]}"
  unfolding additions_retention_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_retention_schema_def)

lemma additions_package_goal_system_payloads [lineage_payloads]:
  "system_payloads additions_package_goal_system\<subseteq>{[]}"
  unfolding additions_package_goal_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_package_schema_def)

lemma additions_boundary_callee_system_payloads [lineage_payloads]:
  "system_payloads additions_boundary_callee_system\<subseteq>{[]}"
  unfolding additions_boundary_callee_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps
    additions_boundary_callee_schema_def)

lemma additions_boundary_element_system_payloads [lineage_payloads]:
  "system_payloads additions_boundary_element_system\<subseteq>{[]}"
  unfolding additions_boundary_element_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps addition_element_clauses_def
    addition_member_schema_def addition_callee_schema_def)

lemma additions_boundary_list_system_payloads [lineage_payloads]:
  "system_payloads additions_boundary_list_system\<subseteq>{[]}"
  unfolding additions_boundary_list_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma additions_boundary_view_system_payloads [lineage_payloads]:
  "system_payloads additions_boundary_view_system\<subseteq>{[]}"
  unfolding additions_boundary_view_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_members_view_schema_def)

lemma additions_boundary_system_payloads [lineage_payloads]: "system_payloads additions_boundary_system\<subseteq>{[]}"
  unfolding additions_boundary_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_members_clauses_def
    additions_members_added_schema_def additions_members_given_schema_def)

lemma additions_audit_callee_system_payloads [lineage_payloads]:
  "system_payloads additions_audit_callee_system\<subseteq>{[]}"
  unfolding additions_audit_callee_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps
    additions_audit_callee_clauses_def additions_audit_read_schema_def additions_audit_given_schema_def)

lemma additions_audit_element_system_payloads [lineage_payloads]:
  "system_payloads additions_audit_element_system\<subseteq>{[]}"
  unfolding additions_audit_element_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps addition_element_clauses_def
    addition_member_schema_def addition_callee_schema_def)

lemma additions_audit_list_system_payloads [lineage_payloads]:
  "system_payloads additions_audit_list_system\<subseteq>{[]}"
  unfolding additions_audit_list_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma additions_audit_view_system_payloads [lineage_payloads]:
  "system_payloads additions_audit_view_system\<subseteq>{[]}"
  unfolding additions_audit_view_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_members_view_schema_def)

lemma additions_goals_system_payloads [lineage_payloads]: "system_payloads additions_goals_system\<subseteq>{[]}"
  unfolding additions_goals_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps additions_members_clauses_def
    additions_members_added_schema_def additions_members_given_schema_def)

lemma additions_guard_system_payloads [lineage_payloads]: "system_payloads additions_guard_system\<subseteq>{[]}"
  unfolding install_requirement_guard_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps requirement_guard_schema_def
    additions_requirements_def)

lemma additions_guard_leaves:
  "schema_leaves additions_retention_schema={}" "schema_leaves additions_package_schema={}"
  "schema_leaves (additions_members_added_schema ls)={}" "schema_leaves (additions_members_given_schema ls)={}"
  "schema_leaves (requirement_guard_schema additions_requirements)={}"
  "schema_leaves additions_boundary_callee_schema={Payload_Term []}"
  "schema_leaves additions_audit_read_schema={Payload_Term []}"
  "schema_leaves additions_audit_given_schema={Payload_Term []}"
  by (simp_all add: schema_leaves_def material_leaves_def additions_retention_schema_def additions_package_schema_def
    additions_members_added_schema_def additions_members_given_schema_def requirement_guard_schema_def
    additions_requirements_def additions_boundary_callee_schema_def additions_audit_read_schema_def
    additions_audit_given_schema_def)

text \<open>
  The guard's own schemas state no leaf; its two callees state the empty payload closing a singleton list, and
  nothing else; the element and list clauses are the notion of additions' and the context list's, which state what
  their owner states (@{thm [source] package_additions_leaves}): nothing but the empty payload terminating the
  list. Every program of the guard states the empty payload alone, by the lineage rule from its readers' facts
  (@{thm [source] extension_formation_system_payloads}, @{thm [source] extension_package_system_payloads},
  @{thm [source] payload_audit_system_payloads}) and its steps' own patterns (@{thm [source]
  additions_guard_system_payloads}). Sites are compared for equality; an address stays an inert payload, a use is
  structure.

  The pair's members are the given's site value and the additions: the added rows and bindings in the environment
  value's row presentations and the candidate's site. On a candidate of the domain the guard holds exactly where the
  guard over site values holds at the given's site value and a site value of the candidate: the candidate's
  environment includes the given's, its site holds a native package, every definition of that package is the
  given's or stands at a use of no artifact of the given's environment, and every definition at such a use states
  no payload but the empty one. A refusal names its socket, and the verdict is the same at every presentation of
  both arguments.
\<close>

end
