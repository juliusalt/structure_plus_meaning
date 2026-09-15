theory Factor_Digit_History_Known_Generation
  imports Factor_Digit_History_Steps Factor_History_Generation_Members
    RRA_Known_Generation_Rows Factor_Digit_Policy_Backends Finite_Reader_Identity_Maps
begin

definition digit_history_known_attempt where
  "digit_history_known_attempt q l rows E pu pr au ar root R=digit_policy_replay_using
    digit_construct_known_generation
    (history_header_policy (digit_history_header q)) (history_header_policy_use (digit_history_header q))
    (history_header_entry (digit_history_header q)) (digit_history_material q) l rows E pu pr au ar root R"

lemma digit_history_known_attempt_exact:
  assumes valid: "digit_required_history_valid q"
    and members: "indexed_history_members (digit_history_index q) rows"
  shows "digit_history_known_attempt q l rows E pu pr au ar root R=
    digit_required_history_attempt q l rows E pu pr au ar root R"
  unfolding digit_history_known_attempt_def digit_required_history_attempt_def
    digit_policy_replay_original_instance[symmetric]
  by (rule digit_policy_replay_constructor_congruence)
    (rule digit_construct_known_generation_exact[OF digit_history_indexed_generations[OF valid members]])

definition digit_required_history_known_step where
  "digit_required_history_known_step q l rows E pu pr au ar root R=(
    if indexed_history_members (digit_history_index q) rows then
      map_option (\<lambda>(A,u,G). digit_history_append_state q A u G)
        (digit_history_known_attempt q l rows E pu pr au ar root R) else None)"

theorem digit_required_history_known_step_exact:
  assumes valid: "digit_required_history_valid q"
  shows "digit_required_history_known_step q l rows E pu pr au ar root R=
    digit_required_history_step q l rows E pu pr au ar root R"
  by (cases "indexed_history_members (digit_history_index q) rows")
    (simp_all only: digit_required_history_known_step_def digit_required_history_step_def
      digit_history_known_attempt_exact[OF valid] if_True if_False)

lift_definition (code_dt) digit_history_known_step ::
  "digit_required_history\<Rightarrow>finite_exact_target\<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>local_address\<Rightarrow>local_address option definition_site\<Rightarrow>
    finite_exact_artifact\<Rightarrow>digit_required_history option"
  is digit_required_history_known_step
  by (auto simp only: digit_required_history_known_step_exact
    intro: optional_result_invariant digit_required_history_step_valid)

lemma digit_history_known_step_raw:
  "map_option raw_digit_required_history (digit_history_known_step q l rows E pu pr au ar root R)=
    digit_required_history_known_step (raw_digit_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

theorem digit_history_known_step_exact:
  "digit_history_known_step q l rows E pu pr au ar root R=digit_history_step q l rows E pu pr au ar root R"
proof -
  have same: "map_option raw_digit_required_history (digit_history_known_step q l rows E pu pr au ar root R)=
    map_option raw_digit_required_history (digit_history_step q l rows E pu pr au ar root R)"
    by (simp only: digit_history_known_step_raw digit_history_step_raw
      digit_required_history_known_step_exact[OF digit_required_history_valid])
  show ?thesis using same
    by (simp only: optional_identity_map_injective[OF raw_digit_required_history_inject])
qed

export_code digit_history_known_step digit_history_view checking SML

text \<open>
  Only the closed valid history and its actual membership guard authorize the
  known predecessor premise. All original target, replay and policy checks
  remain executable. The entire optional closed result equals the established
  operation, including refusals, stored head, original material, fixed header,
  ordered ledger and exact cache. The guard and equality proofs do not establish
  complete historical permission, reachability or a full physical cost bound.
\<close>

end
