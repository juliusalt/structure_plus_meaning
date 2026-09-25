theory Development_Given_Program
  imports Development_Given_Readers Factor_Program_Reflection Factor_Application_Admission Factor_Derivation_Admission Factor_Replay_Admission Factor_Environment_Comparison Factor_Generation_Contracts Factor_Generation_Source_Contracts Factor_Generation_Scope_Base Factor_Base_Cause_Base Factor_Adoption_Comparison
begin

section \<open>The readers a leaf's request is granted, joined with the given's readers\<close>

text \<open>
  Task 378's Requests grant a leaf's request the Factor readers it may call: package, definition and
  call admission, the positive query and program reflection, derivation and replay admission,
  generation, adoption and environment identity. The given's readers (@{const guard_readers_system})
  hold package and definition admission, environment inclusion and every reader of the complete-data
  lineage below 124, among them call and application admission (84, 85), derivation and replay
  admission (99--111), the positive query (112--115) and environment identity (16); the generation
  values' operations (139--146), the generation source reading (147--155) and the adoption values'
  admission and identity (269, 270) stand in three other programs. The granted entries are the public
  operation sites of each granted reader not already an entry of the given, as its theory's
  native-operations theorem fixes them (environment inclusion 113 is an entry already). The joined
  program is the given's readers' program joined with those three programs where they agree; every
  definition keeps its theory's number.
\<close>

definition given_granted_entries :: "nat fset" where
  "given_granted_entries={|16,84,85,99,100,101,102,106,107,108,109,110,111,112,114,115,
    139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,269,270|}"

subsection \<open>The right component of a union agrees with it, and an overlap agreement reverses\<close>

lemma system_union_agree_right:
  assumes left: "schema_system_formed P"
    and agree: "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
  shows "systems_agree_on Q (system_union P Q) (system_definitions Q)"
proof -
  have swap: "system_union Q P=system_union P Q" by (simp add: system_union_def Un_commute)
  have "systems_agree_on Q P (system_definitions Q\<inter>system_definitions P)"
    using systems_agree_on_sym[OF agree] by (simp only: Int_commute)
  from system_union_agree_left[OF left this] show ?thesis by (simp only: swap)
qed

lemma overlap_agreement_sym:
  assumes "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
  shows "systems_agree_on Q P (system_definitions Q\<inter>system_definitions P)"
  using systems_agree_on_sym[OF assms] by (simp only: Int_commute)

subsection \<open>Where the granted programs stand\<close>

lemma granted_bounds:
  "system_definitions generation_value_system\<subseteq>{..<147}"
  "system_definitions located_admission_system\<subseteq>{..<45}"
  "system_definitions adoption_comparison_base\<subseteq>system_definitions generation_value_system"
  "system_definitions generation_source_system\<subseteq>{..<156}"
  "system_definitions adoption_value_system\<subseteq>{..<147}\<union>{269,270}"
proof -
  have difference: "system_definitions target_difference_system\<subseteq>{..<137}" by auto
  show generation: "system_definitions generation_value_system\<subseteq>{..<147}"
    using generation_target_subdomain difference by auto
  show located: "system_definitions located_admission_system\<subseteq>{..<45}" by auto
  show base: "system_definitions adoption_comparison_base\<subseteq>system_definitions generation_value_system"
    unfolding adoption_comparison_base_def by (rule rooted_system_subdomain)
  have below: "{..<45}\<subseteq>{..<(147::nat)}" "{..<147}\<subseteq>{..<(156::nat)}" by auto
  have components: "system_definitions generation_source_components_system\<subseteq>{..<147}"
    unfolding generation_source_components_definitions
    using generation located below by (auto simp del: generation_value_definitions located_admission_definitions)
  have "system_definitions generation_source_base_system\<subseteq>{..<156}"
    by (rule order.trans[OF generation_source_base_subdomain order.trans[OF components below(2)]])
  then show "system_definitions generation_source_system\<subseteq>{..<156}"
    unfolding generation_source_definitions by auto
  show "system_definitions adoption_value_system\<subseteq>{..<147}\<union>{269,270}"
    using base generation by auto
qed

lemma guard_readers_bound:
  "system_definitions guard_readers_system\<subseteq>system_definitions complete_data_admission_system\<union>
    {156,157,158,159,390,391,392,393,500,501,502,503,504,505}"
proof -
  have context_base: "system_definitions context_base_system\<subseteq>system_definitions complete_data_admission_system"
    by (rule order.trans[OF context_base_subdomain]) simp
  have additions: "system_definitions use_additions_system={390,391,392,393}\<union>
      (system_definitions complete_data_admission_system\<union>(system_definitions context_base_system\<union>{156,157,158,159}))"
    by (simp only: use_additions_definitions addition_list_definitions addition_element_definitions
      use_absence_definitions scope_reading_components_definitions context_admission_definitions) blast
  have audit: "system_definitions payload_audit_system\<subseteq>{500,501,502,503,504,505}\<union>
      system_definitions definition_call_admission_system"
    by (simp only: payload_audit_definitions clause_family_payloads_definitions clause_payloads_definitions
      empty_payload_calls_definitions empty_payload_rows_definitions empty_payloads_definitions) blast
  have call: "system_definitions definition_call_admission_system\<subseteq>system_definitions complete_data_admission_system"
    by (rule whole_agreement_definitions[OF call_admission_complete_data_agreement])
  show ?thesis
    unfolding guard_readers_definitions using context_base additions audit call by blast
qed

lemma granted_fresh_complete_data:
  "{139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,269,270}\<inter>
    system_definitions complete_data_admission_system={}"
  by auto

subsection \<open>The granted programs agree on their overlaps\<close>

lemma generation_value_source_agreement:
  "systems_agree_on generation_value_system generation_source_system
    (system_definitions generation_value_system\<inter>system_definitions generation_source_system)"
proof -
  let ?U="system_definitions generation_value_system\<inter>system_definitions generation_source_system"
  have fresh: "{147,148,149,150,151,152,153,154,155}\<inter>system_definitions generation_value_system={}"
    using granted_bounds(1) by (auto simp del: generation_value_definitions)
  have base: "?U\<subseteq>system_definitions generation_source_base_system"
    using fresh unfolding generation_source_definitions by blast
  have one: "systems_agree_on generation_value_system generation_source_components_system ?U"
    by (rule systems_agree_on_subdomain[OF system_union_agree_right[OF located_admission_system_formed
      generation_located_agreement, folded generation_source_components_system_def]]) blast
  have two: "systems_agree_on generation_source_components_system generation_source_base_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_base_agreement base])
  have three: "systems_agree_on generation_source_base_system generation_source_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_retained_agreement base])
  show ?thesis by (rule systems_agree_on_transitive[OF one systems_agree_on_transitive[OF two three]])
qed

lemma adoption_base_values_agreement:
  "systems_agree_on adoption_comparison_base generation_value_system (system_definitions adoption_comparison_base)"
  unfolding adoption_comparison_base_def by (rule rooted_agreement_transfer) (simp add: systems_agree_on_def)

lemma adoption_base_value_agreement:
  "systems_agree_on adoption_comparison_base adoption_value_system (system_definitions adoption_comparison_base)"
  by (rule whole_agreement_transitive[OF adoption_admission_view.old_agreement[folded adoption_admission_system_def]
    adoption_identity_view.old_agreement[folded adoption_value_system_def]])

lemma generation_value_adoption_agreement:
  "systems_agree_on generation_value_system adoption_value_system
    (system_definitions generation_value_system\<inter>system_definitions adoption_value_system)"
proof (rule common_component_overlap_agreement[where B=adoption_comparison_base])
  show "systems_agree_on adoption_comparison_base generation_value_system
      (system_definitions adoption_comparison_base\<inter>system_definitions generation_value_system)"
    by (rule systems_agree_on_subdomain[OF adoption_base_values_agreement]) blast
  show "systems_agree_on adoption_comparison_base adoption_value_system
      (system_definitions adoption_comparison_base\<inter>system_definitions adoption_value_system)"
    by (rule systems_agree_on_subdomain[OF adoption_base_value_agreement]) blast
  have "269\<notin>system_definitions generation_value_system" "270\<notin>system_definitions generation_value_system"
    using granted_bounds(1) by (auto simp del: generation_value_definitions)
  then show "system_definitions generation_value_system\<inter>system_definitions adoption_value_system\<subseteq>
      system_definitions adoption_comparison_base"
    unfolding adoption_value_definitions by blast
qed

lemma source_adoption_agreement:
  "systems_agree_on generation_source_system adoption_value_system
    (system_definitions generation_source_system\<inter>system_definitions adoption_value_system)"
proof (rule common_component_overlap_agreement[where B=generation_value_system])
  show "systems_agree_on generation_value_system generation_source_system
      (system_definitions generation_value_system\<inter>system_definitions generation_source_system)"
    by (rule generation_value_source_agreement)
  show "systems_agree_on generation_value_system adoption_value_system
      (system_definitions generation_value_system\<inter>system_definitions adoption_value_system)"
    by (rule generation_value_adoption_agreement)
  have "269\<notin>system_definitions generation_source_system" "270\<notin>system_definitions generation_source_system"
    using granted_bounds(4) by (auto simp del: generation_source_definitions)
  then show "system_definitions generation_source_system\<inter>system_definitions adoption_value_system\<subseteq>
      system_definitions generation_value_system"
    unfolding adoption_value_definitions using granted_bounds(3) by blast
qed

subsection \<open>The granted programs agree with complete data admission on their overlaps\<close>

lemma values_complete_data_agreement:
  "systems_agree_on generation_value_system complete_data_admission_system
    (system_definitions generation_value_system\<inter>system_definitions complete_data_admission_system)"
proof (rule common_component_overlap_agreement[where B=located_admission_system])
  show "systems_agree_on located_admission_system generation_value_system
      (system_definitions located_admission_system\<inter>system_definitions generation_value_system)"
    by (rule generation_located_agreement)
  show "systems_agree_on located_admission_system complete_data_admission_system
      (system_definitions located_admission_system\<inter>system_definitions complete_data_admission_system)"
    by (rule systems_agree_on_subdomain[OF complete_data_located_agreement]) blast
  have lower: "system_definitions target_difference_system\<inter>system_definitions complete_data_admission_system
      \<subseteq>system_definitions located_admission_system" by auto
  show "system_definitions generation_value_system\<inter>system_definitions complete_data_admission_system\<subseteq>
      system_definitions located_admission_system"
    using generation_target_subdomain lower granted_fresh_complete_data
    unfolding generation_value_definitions by blast
qed

lemma adoption_complete_data_agreement:
  "systems_agree_on adoption_value_system complete_data_admission_system
    (system_definitions adoption_value_system\<inter>system_definitions complete_data_admission_system)"
proof (rule common_component_overlap_agreement[where B=generation_value_system])
  show "systems_agree_on generation_value_system adoption_value_system
      (system_definitions generation_value_system\<inter>system_definitions adoption_value_system)"
    by (rule generation_value_adoption_agreement)
  show "systems_agree_on generation_value_system complete_data_admission_system
      (system_definitions generation_value_system\<inter>system_definitions complete_data_admission_system)"
    by (rule values_complete_data_agreement)
  show "system_definitions adoption_value_system\<inter>system_definitions complete_data_admission_system\<subseteq>
      system_definitions generation_value_system"
    unfolding adoption_value_definitions using granted_bounds(3) granted_fresh_complete_data by blast
qed

lemmas source_complete_data_agreement = systems_agree_on_sym[OF base_cause_source_agreement]

subsection \<open>The joined program\<close>

lemma source_adoption_formed [simp]:
  "schema_system_formed (system_union generation_source_system adoption_value_system)"
  by (rule system_union_agree_formed[OF generation_source_system_formed adoption_value_system_formed
    source_adoption_agreement])

lemma values_source_adoption_agreement:
  "systems_agree_on generation_value_system (system_union generation_source_system adoption_value_system)
    (system_definitions generation_value_system\<inter>
      system_definitions (system_union generation_source_system adoption_value_system))"
  by (rule overlap_agreement_sym[OF overlap_agreement_union[OF generation_source_system_formed
    adoption_value_system_formed overlap_agreement_sym[OF generation_value_source_agreement]
    overlap_agreement_sym[OF generation_value_adoption_agreement]]])

definition granted_readers_system :: "(nat,nat,nat,nat) schema_system" where
  "granted_readers_system=system_union generation_value_system
    (system_union generation_source_system adoption_value_system)"

lemma granted_readers_formed [simp]: "schema_system_formed granted_readers_system"
  unfolding granted_readers_system_def
  by (rule system_union_agree_formed[OF generation_value_system_formed source_adoption_formed
    values_source_adoption_agreement])

lemma granted_readers_bound:
  "system_definitions granted_readers_system\<subseteq>{..<156}\<union>{269,270}"
proof -
  have "{..<147}\<subseteq>{..<(156::nat)}" by auto
  then show ?thesis unfolding granted_readers_system_def system_union_definitions
    using granted_bounds(1,4,5) by (auto simp del: generation_value_definitions generation_source_definitions
      adoption_value_definitions)
qed

lemma granted_complete_data_agreement:
  "systems_agree_on complete_data_admission_system granted_readers_system
    (system_definitions complete_data_admission_system\<inter>system_definitions granted_readers_system)"
  unfolding granted_readers_system_def
  by (rule overlap_agreement_sym[OF overlap_agreement_union[OF generation_value_system_formed source_adoption_formed
    values_complete_data_agreement overlap_agreement_union[OF generation_source_system_formed
      adoption_value_system_formed source_complete_data_agreement adoption_complete_data_agreement]]])

lemma additions_guard_agreement:
  "systems_agree_on use_additions_system guard_readers_system (system_definitions use_additions_system)"
  unfolding guard_readers_system_def
  by (rule system_union_agree_left[OF payload_audit_system_formed readers_agreement])

lemmas complete_data_guard_agreement =
  whole_agreement_transitive[OF complete_data_additions_agreement additions_guard_agreement]

lemma guard_granted_agreement:
  "systems_agree_on guard_readers_system granted_readers_system
    (system_definitions guard_readers_system\<inter>system_definitions granted_readers_system)"
proof (rule common_component_overlap_agreement[where B=complete_data_admission_system])
  show "systems_agree_on complete_data_admission_system guard_readers_system
      (system_definitions complete_data_admission_system\<inter>system_definitions guard_readers_system)"
    by (rule systems_agree_on_subdomain[OF complete_data_guard_agreement]) blast
  show "systems_agree_on complete_data_admission_system granted_readers_system
      (system_definitions complete_data_admission_system\<inter>system_definitions granted_readers_system)"
    by (rule granted_complete_data_agreement)
  show "system_definitions guard_readers_system\<inter>system_definitions granted_readers_system\<subseteq>
      system_definitions complete_data_admission_system"
  proof
    fix x assume x: "x\<in>system_definitions guard_readers_system\<inter>system_definitions granted_readers_system"
    have "x\<in>{..<156}\<union>{269,270}" using x granted_readers_bound by blast
    then have "x\<notin>{156,157,158,159,390,391,392,393,500,501,502,503,504,505}" by auto
    then show "x\<in>system_definitions complete_data_admission_system" using x guard_readers_bound by blast
  qed
qed

definition given_program_system :: "(nat,nat,nat,nat) schema_system" where
  "given_program_system=system_union guard_readers_system granted_readers_system"

lemma given_program_formed [simp]: "schema_system_formed given_program_system"
  unfolding given_program_system_def
  by (rule system_union_agree_formed[OF guard_readers_formed granted_readers_formed guard_granted_agreement])

lemma given_program_definitions:
  "system_definitions given_program_system=system_definitions guard_readers_system\<union>
    system_definitions granted_readers_system"
  by (simp add: given_program_system_def)

section \<open>What the joined program means\<close>

text \<open>
  The joined program means what the given's readers mean at their definitions and what each granted
  program means at its own. A reader's system that agrees with the joined program on its whole domain
  means there what it means alone (@{thm [source] whole_system_agreement_meaning}): one lemma,
  instantiated once per reader's system; each granted entry's exact contract is then an instance at the
  joined program, read through it, none proved again.
\<close>

lemma given_program_left:
  assumes "d\<in>system_definitions guard_readers_system"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  using system_union_agree_left_locality(2)[OF guard_readers_formed granted_readers_formed
    guard_granted_agreement assms] by (simp only: given_program_system_def)

lemma given_program_meaning:
  assumes formed: "schema_system_formed S"
    and agreement: "systems_agree_on S given_program_system (system_definitions S)"
    and member: "d\<in>system_definitions S"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning S"
  by (rule whole_system_agreement_meaning[OF formed given_program_formed agreement member])

subsection \<open>Each reader's system agrees with the joined program on its whole domain\<close>

lemma guard_program_agreement:
  "systems_agree_on guard_readers_system given_program_system (system_definitions guard_readers_system)"
  unfolding given_program_system_def
  by (rule system_union_agree_left[OF granted_readers_formed guard_granted_agreement])

lemma granted_program_agreement:
  "systems_agree_on granted_readers_system given_program_system (system_definitions granted_readers_system)"
  unfolding given_program_system_def
  by (rule system_union_agree_right[OF guard_readers_formed guard_granted_agreement])

lemma values_granted_agreement:
  "systems_agree_on generation_value_system granted_readers_system (system_definitions generation_value_system)"
  unfolding granted_readers_system_def
  by (rule system_union_agree_left[OF source_adoption_formed values_source_adoption_agreement])

lemma source_adoption_granted_agreement:
  "systems_agree_on (system_union generation_source_system adoption_value_system) granted_readers_system
    (system_definitions (system_union generation_source_system adoption_value_system))"
  unfolding granted_readers_system_def
  by (rule system_union_agree_right[OF generation_value_system_formed values_source_adoption_agreement])

lemma positive_complete_data_agreement:
  "systems_agree_on native_positive_admission_system complete_data_admission_system
    (system_definitions native_positive_admission_system)"
  by (simp add: systems_agree_on_added
    complete_data_admission_system_def package_retention_admission_system_def package_slot_list_system_def
    package_source_list_system_def package_slot_reading_system_def package_source_reading_system_def
    scope_forwarding_system_def)

lemma replay_positive_agreement:
  "systems_agree_on replay_admission_system native_positive_admission_system
    (system_definitions replay_admission_system)"
  by (simp add: systems_agree_on_added native_positive_admission_system_def positive_query_system_def
    environment_inclusion_system_def artifact_inclusion_system_def)

lemma derivation_replay_agreement:
  "systems_agree_on derivation_admission_system replay_admission_system
    (system_definitions derivation_admission_system)"
  by (simp add: systems_agree_on_added replay_admission_system_def retention_admission_system_def
    replay_slot_list_system_def replay_source_list_system_def replay_slot_reading_system_def
    replay_source_reading_system_def definition_slot_reading_system_def schema_slot_reading_system_def
    premise_slot_reading_system_def)

lemma application_derivation_agreement:
  "systems_agree_on application_admission_system derivation_admission_system
    (system_definitions application_admission_system)"
  by (simp add: systems_agree_on_added derivation_admission_system_def proof_claim_checking_system_def
    keyed_row_join_system_def row_qualification_system_def proof_graph_membership_system_def
    proof_graph_admission_system_def proof_bound_checking_system_def proof_link_checking_system_def
    proof_node_reading_system_def discharge_table_reading_system_def binding_table_reading_system_def
    site_link_vector_system_def application_vector_system_def site_link_reading_system_def
    site_citation_reading_system_def admitted_instantiation_system_def program_call_list_system_def)

lemma call_application_agreement:
  "systems_agree_on program_call_admission_system application_admission_system
    (system_definitions program_call_admission_system)"
  by (simp add: systems_agree_on_added application_admission_system_def)

lemma comparison_located_agreement:
  "systems_agree_on environment_comparison_system located_admission_system
    (system_definitions environment_comparison_system)"
  by (simp add: systems_agree_on_added located_admission_system_def anchored_admission_system_def
    citation_reading_system_def citation_location_system_def citation_interpretation_system_def
    citation_resolution_system_def binding_lookup_system_def artifact_lookup_system_def
    citation_admission_system_def target_admission_system_def record_admission_system_def
    socket_chain_system_def family_admission_system_def family_sockets_system_def family_socket_system_def
    headed_material_system_def key_fibre_system_def environment_identity_system_def
    environment_admission_system_def binding_entries_system_def binding_entry_system_def
    artifact_entries_system_def artifact_entry_admission_system_def keyed_list_system_def
    key_absence_system_def coordinate_admission_system_def natural_list_system_def
    natural_admission_system_def)

lemmas complete_data_program_agreement =
  whole_agreement_transitive[OF complete_data_guard_agreement guard_program_agreement]
lemmas positive_program_agreement =
  whole_agreement_transitive[OF positive_complete_data_agreement complete_data_program_agreement]
lemmas replay_program_agreement =
  whole_agreement_transitive[OF replay_positive_agreement positive_program_agreement]
lemmas derivation_program_agreement =
  whole_agreement_transitive[OF derivation_replay_agreement replay_program_agreement]
lemmas application_program_agreement =
  whole_agreement_transitive[OF application_derivation_agreement derivation_program_agreement]
lemmas call_program_agreement =
  whole_agreement_transitive[OF call_application_agreement application_program_agreement]
lemmas comparison_program_agreement =
  whole_agreement_transitive[OF comparison_located_agreement
    whole_agreement_transitive[OF complete_data_located_agreement complete_data_program_agreement]]
lemmas values_program_agreement =
  whole_agreement_transitive[OF values_granted_agreement granted_program_agreement]
lemmas source_adoption_program_agreement =
  whole_agreement_transitive[OF source_adoption_granted_agreement granted_program_agreement]
lemmas source_program_agreement =
  whole_agreement_transitive[OF system_union_agree_left[OF adoption_value_system_formed source_adoption_agreement]
    source_adoption_program_agreement]
lemmas adoption_program_agreement =
  whole_agreement_transitive[OF system_union_agree_right[OF generation_source_system_formed source_adoption_agreement]
    source_adoption_program_agreement]

lemmas given_program_call_meaning =
  given_program_meaning[OF program_call_admission_system_formed call_program_agreement]
lemmas given_program_application_meaning =
  given_program_meaning[OF application_admission_system_formed application_program_agreement]
lemmas given_program_positive_meaning =
  given_program_meaning[OF native_positive_admission_system_formed positive_program_agreement]
lemmas given_program_derivation_meaning =
  given_program_meaning[OF derivation_admission_system_formed derivation_program_agreement]
lemmas given_program_replay_meaning =
  given_program_meaning[OF replay_admission_system_formed replay_program_agreement]
lemmas given_program_comparison_meaning =
  given_program_meaning[OF environment_comparison_system_formed comparison_program_agreement]
lemmas given_program_values_meaning =
  given_program_meaning[OF generation_value_system_formed values_program_agreement]
lemmas given_program_source_meaning =
  given_program_meaning[OF generation_source_system_formed source_program_agreement]
lemmas given_program_adoption_meaning =
  given_program_meaning[OF adoption_value_system_formed adoption_program_agreement]

subsection \<open>Every granted entry's exact contract at the joined program\<close>

lemma granted_entry_members:
  "16\<in>system_definitions environment_comparison_system"
  "84\<in>system_definitions program_call_admission_system"
  "85\<in>system_definitions application_admission_system"
  "84\<in>system_definitions native_positive_admission_system"
  "114\<in>system_definitions native_positive_admission_system"
  "115\<in>system_definitions native_positive_admission_system"
  "102\<in>system_definitions derivation_admission_system"
  "111\<in>system_definitions replay_admission_system"
  "139\<in>system_definitions generation_value_system"
  "140\<in>system_definitions generation_value_system"
  "152\<in>system_definitions generation_source_system"
  "269\<in>system_definitions adoption_value_system"
  "270\<in>system_definitions adoption_value_system"
  by simp_all

lemmas given_program_call_admission_exact =
  program_call_admission_exact[unfolded given_program_call_meaning[OF granted_entry_members(2), symmetric]]
lemmas given_program_application_admission_exact =
  application_admission_exact[unfolded given_program_application_meaning[OF granted_entry_members(3), symmetric]]
lemmas given_program_formation_reflection =
  program_formation_reflection[unfolded given_program_positive_meaning[OF granted_entry_members(4), symmetric]]
lemmas given_program_meaning_reflection =
  program_meaning_reflection[unfolded given_program_positive_meaning[OF granted_entry_members(5), symmetric]]
lemmas given_program_positive_admission_exact =
  native_positive_admission_exact[unfolded given_program_positive_meaning[OF granted_entry_members(6), symmetric]]
lemmas given_program_derivation_admission_exact =
  derivation_admission_exact[unfolded given_program_derivation_meaning[OF granted_entry_members(7), symmetric]]
lemmas given_program_replay_admission_exact =
  replay_admission_exact[unfolded given_program_replay_meaning[OF granted_entry_members(8), symmetric]]
lemmas given_program_environment_comparison_exact =
  environment_comparison_exact[unfolded given_program_comparison_meaning[OF granted_entry_members(1), symmetric]]
lemmas given_program_generation_admission_exact =
  generation_admission_exact[unfolded given_program_values_meaning[OF granted_entry_members(9), symmetric]]
lemmas given_program_generation_identity_exact =
  generation_identity_exact[unfolded given_program_values_meaning[OF granted_entry_members(10), symmetric]]
lemmas given_program_generation_source_exact =
  generation_source_exact[unfolded given_program_source_meaning[OF granted_entry_members(11), symmetric]]
lemmas given_program_adoption_admission_exact =
  adoption_admission_exact[unfolded given_program_adoption_meaning[OF granted_entry_members(12), symmetric]]
lemmas given_program_adoption_identity_exact =
  adoption_identity_exact[unfolded given_program_adoption_meaning[OF granted_entry_members(13), symmetric]]

lemma granted_operation_members:
  "d\<in>{112,113,114,115} \<Longrightarrow> d\<in>system_definitions native_positive_admission_system"
  "d\<in>{99,100,101,102} \<Longrightarrow> d\<in>system_definitions derivation_admission_system"
  "d\<in>{106,107,108,109,110,111} \<Longrightarrow> d\<in>system_definitions replay_admission_system"
  "d\<in>{139,140,141,142,143,144,145,146} \<Longrightarrow> d\<in>system_definitions generation_value_system"
  "d\<in>{147,148,149,150,151,152,153,154,155} \<Longrightarrow> d\<in>system_definitions generation_source_system"
  "d\<in>{269,270} \<Longrightarrow> d\<in>system_definitions adoption_value_system"
  by auto

lemma given_program_positive_operations_exact:
  assumes "d\<in>{112,113,114,115}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> positive_operation_result d t"
proof -
  have "d\<in>system_definitions native_positive_admission_system" by (rule granted_operation_members(1)[OF assms])
  then show ?thesis by (simp only: given_program_positive_meaning positive_operations_exact[OF assms])
qed

lemma given_program_derivation_operations_exact:
  assumes "d\<in>{99,100,101,102}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> derivation_operation_result d t"
proof -
  have "d\<in>system_definitions derivation_admission_system" by (rule granted_operation_members(2)[OF assms])
  then show ?thesis by (simp only: given_program_derivation_meaning derivation_operations_exact[OF assms])
qed

lemma given_program_replay_operations_exact:
  assumes "d\<in>{106,107,108,109,110,111}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> replay_operation_result d t"
proof -
  have "d\<in>system_definitions replay_admission_system" by (rule granted_operation_members(3)[OF assms])
  then show ?thesis by (simp only: given_program_replay_meaning replay_operations_exact[OF assms])
qed

lemma given_program_generation_operations_exact:
  assumes "d\<in>{139,140,141,142,143,144,145,146}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> generation_operation_result d t"
proof -
  have "d\<in>system_definitions generation_value_system" by (rule granted_operation_members(4)[OF assms])
  then show ?thesis by (simp only: given_program_values_meaning generation_operations_exact[OF assms])
qed

lemma given_program_generation_source_operations_exact:
  assumes "d\<in>{147,148,149,150,151,152,153,154,155}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> generation_source_operation_result d t"
proof -
  have "d\<in>system_definitions generation_source_system" by (rule granted_operation_members(5)[OF assms])
  then show ?thesis by (simp only: given_program_source_meaning generation_source_operations_exact[OF assms])
qed

lemma given_program_adoption_operations_exact:
  assumes "d\<in>{269,270}"
  shows "(d,t)\<in>positive_meaning given_program_system \<longleftrightarrow> adoption_value_operation_result d t"
proof -
  have "d\<in>system_definitions adoption_value_system" by (rule granted_operation_members(6)[OF assms])
  then show ?thesis by (simp only: given_program_adoption_meaning adoption_value_operations_exact[OF assms])
qed

lemma given_granted_members:
  "fset given_granted_entries\<subseteq>system_definitions given_program_system"
proof -
  have entries: "fset given_granted_entries={16}\<union>{84}\<union>{85}\<union>{99,100,101,102}\<union>{106,107,108,109,110,111}\<union>
      {112,114,115}\<union>{139,140,141,142,143,144,145,146}\<union>{147,148,149,150,151,152,153,154,155}\<union>{269,270}"
    by (auto simp: given_granted_entries_def)
  have "{16}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF comparison_program_agreement]]) simp
  moreover have "{84}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF call_program_agreement]]) simp
  moreover have "{85}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF application_program_agreement]]) simp
  moreover have "{99,100,101,102}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF derivation_program_agreement]]) simp
  moreover have "{106,107,108,109,110,111}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF replay_program_agreement]]) simp
  moreover have "{112,114,115}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF positive_program_agreement]]) simp
  moreover have "{139,140,141,142,143,144,145,146}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF values_program_agreement]]) simp
  moreover have "{147,148,149,150,151,152,153,154,155}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF source_program_agreement]]) simp
  moreover have "{269,270}\<subseteq>system_definitions given_program_system"
    by (rule order.trans[OF _ whole_agreement_definitions[OF adoption_program_agreement]]) simp
  ultimately show ?thesis unfolding entries by (simp only: Un_subset_iff)
qed

section \<open>The joined program's finite presentation\<close>

text \<open>
  Derived from its parts' presentations: the given's readers (@{const finite_given_readers}), the
  generation values' program and the two rooted bases of the added lineages, the generation source base
  and the adoption comparison base. A rooted base is presented as the restriction of its source's
  presentation to the closure of its roots (@{thm [source] finite_system_of_rooted}), each root set the
  finite set its external dependencies compute; the generation values' target base likewise, over the
  target difference program's presentation. Nothing presented by a piece is reduced again.
\<close>

definition finite_target_difference_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_target_difference_program=finite_system_of target_difference_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_target_difference_program_code}
  @{thm finite_target_difference_program_def} [] []\<close>

definition finite_generation_target_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_generation_target_program=finite_system_of generation_target_system"

lemma finite_generation_target_program_code [code]:
  "finite_generation_target_program=finite_system_restriction finite_target_difference_program
    (finite_definition_closure finite_target_difference_program {|2,4,35,135,136|})"
  unfolding finite_generation_target_program_def finite_target_difference_program_def
  using finite_system_of_rooted[OF target_difference_system_formed, of "{|2,4,35,135,136|}"]
  by (simp add: generation_target_system_def generation_group_external_dependencies)

definition finite_generation_values_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_generation_values_program=finite_system_of generation_value_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_generation_values_program_code}
  @{thm finite_generation_values_program_def} [@{thm finite_generation_target_program_def}] []\<close>

definition finite_generation_source_components_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_generation_source_components_program=finite_system_of generation_source_components_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_generation_source_components_program_code}
  @{thm finite_generation_source_components_program_def} [@{thm finite_generation_values_program_def}] []\<close>

definition finite_generation_source_base_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_generation_source_base_program=finite_system_of generation_source_base_system"

lemma finite_generation_source_base_program_code [code]:
  "finite_generation_source_base_program=finite_system_restriction finite_generation_source_components_program
    (finite_definition_closure finite_generation_source_components_program {|1,32,34,37,43,44,139,145|})"
  unfolding finite_generation_source_base_program_def finite_generation_source_components_program_def
  using finite_system_of_rooted[OF generation_source_components_formed, of "{|1,32,34,37,43,44,139,145|}"]
  by (simp add: generation_source_base_system_def generation_source_group_external_dependencies)

definition finite_adoption_base_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_adoption_base_program=finite_system_of adoption_comparison_base"

lemma finite_adoption_base_program_code [code]:
  "finite_adoption_base_program=finite_system_restriction finite_generation_values_program
    (finite_definition_closure finite_generation_values_program {|35,135,139,140|})"
  unfolding finite_adoption_base_program_def finite_generation_values_program_def
  using finite_system_of_rooted[OF generation_value_system_formed, of "{|35,135,139,140|}"]
  by (simp add: adoption_comparison_base_def)

definition finite_given_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_given_program=finite_system_of given_program_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_given_program_code}
  @{thm finite_given_program_def}
  [@{thm finite_given_readers_def}, @{thm finite_generation_values_program_def},
    @{thm finite_generation_source_base_program_def}, @{thm finite_adoption_base_program_def}] []\<close>

lemma finite_given_program_exact:
  "decode_finite_system finite_given_program=given_program_system"
  unfolding finite_given_program_def by (rule decode_finite_system_of[OF given_program_formed])

lemma finite_given_program_formed:
  "finite_system_formed finite_given_program"
  by (simp only: finite_system_formed_correct finite_given_program_exact given_program_formed)

export_code finite_given_program finite_system_formed fcard finite_system_definitions finite_system_payloads
  checking SML

end
