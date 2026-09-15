theory Factor_Known_History_Control_Construction
  imports Factor_Shared_History_Construction Factor_Constructed_Original_History_Execution
    RRA_Known_Original_Generation_Rows Factor_Policy_Constructor_Congruence
begin

definition known_original_history_step :: "finite_required_history_state\<Rightarrow>_" where
  "known_original_history_step q l rows E pu pr au ar root R=(
    if list_all (\<lambda>row. row\<in>set (required_history_members q)) rows then
      map_option (\<lambda>(A,u,G). q\<lparr>required_history_material:=A,
        required_history_members:=((u,[]),G)#required_history_members q\<rparr>)
        (policy_record_replay_from_source finite_construct_known_original_generation
          (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
          (required_history_material q) l rows E pu pr au ar root R)
    else None)"

theorem known_original_history_step_exact:
  assumes valid: "finite_required_history_valid q"
  shows "known_original_history_step q l rows E pu pr au ar root R=
    finite_required_history_step q l rows E pu pr au ar root R"
proof -
  have formed: "finite_environment_formed (required_history_material q)"
    using valid by (auto simp: finite_required_history_valid_def)
  have attempt: "policy_record_replay_from_source finite_construct_known_original_generation
      (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
      (required_history_material q) l rows E pu pr au ar root R=
    policy_record_replay_from_source finite_construct_generation_record
      (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
      (required_history_material q) l rows E pu pr au ar root R"
    if members: "list_all (\<lambda>row. row\<in>set (required_history_members q)) rows"
    by (rule policy_record_from_source_constructor_congruence)
      (rule finite_construct_known_original_generation_exact[OF formed
        required_history_member_generations[OF valid members]])
  show ?thesis
    by (cases "list_all (\<lambda>row. row\<in>set (required_history_members q)) rows")
      (simp_all add: known_original_history_step_def finite_required_history_step_constructed_code attempt)
qed

declare digit_history_legacy.simps[code del]

lemma digit_history_legacy_known_rows_code [code]:
  "digit_history_legacy (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    map_option (\<lambda>following. (Suc (Suc (fst (digit_allocated_view (digit_history_material previous)))),
      following,fset_of_list (required_history_members following)))
      (known_original_history_step (digit_history_original_state previous) l rows E pu pr au ar root R))"
proof -
  have valid: "finite_required_history_valid (digit_history_original_state (raw_digit_required_history q))"
    using digit_required_history_valid[of q] by (simp only: digit_required_history_valid_def; blast)
  show ?thesis by (simp only: digit_history_legacy.simps Let_def known_original_history_step_exact[OF valid])
qed

lemma closed_history_known_constructor:
  assumes members: "indexed_history_members (digit_history_index (raw_digit_required_history q)) rows"
  shows "digit_construct_known_generation (digit_history_material (raw_digit_required_history q)) l p c rows=
    digit_construct_generation (digit_history_material (raw_digit_required_history q)) l p c rows"
  by (rule digit_construct_known_generation_exact[OF
      digit_history_indexed_generations[OF digit_required_history_valid members]])

lemma closed_history_known_replay:
  assumes members: "indexed_history_members (digit_history_index (raw_digit_required_history q)) rows"
  shows "record_native_replay_with digit_construct_known_generation
      (digit_history_material (raw_digit_required_history q)) l rows E pu pr au ar root R=
    record_native_replay_with digit_construct_generation
      (digit_history_material (raw_digit_required_history q)) l rows E pu pr au ar root R"
  by (rule record_native_replay_constructor_congruence; rule closed_history_known_constructor[OF members])

declare digit_history_without_policy.simps[code del]
declare digit_history_without_replay.simps[code del]

lemma digit_history_without_policy_known_rows_code [code]:
  "digit_history_without_policy (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    if indexed_history_members (digit_history_index previous) rows then
      map_option (\<lambda>(A,u,G,J,C). digit_history_append_state previous A u G)
        (record_native_replay_with digit_construct_known_generation (digit_history_material previous)
          l rows E pu pr au ar root R) else None)"
  by (cases "indexed_history_members (digit_history_index (raw_digit_required_history q)) rows")
    (simp_all add: digit_history_without_policy.simps Let_def closed_history_known_replay)

lemma digit_history_without_replay_known_rows_code [code]:
  "digit_history_without_replay (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    if indexed_history_members (digit_history_index previous) rows then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> map_option (\<lambda>(A,u,G). digit_history_append_state previous A u G)
          (digit_construct_known_generation (digit_history_material previous) l (Finite_Whole R) (Finite_Whole C) rows))
    else None)"
  by (cases "indexed_history_members (digit_history_index (raw_digit_required_history q)) rows")
    (simp_all add: digit_history_without_replay.simps Let_def closed_history_known_constructor split: option.splits)

text \<open>The legacy allocator and the two controls that retain membership
  instantiate the same complete known-predecessor equation. The closed input
  invariant and the actual membership guard supply every required reading.
  Each control retains its own remaining guards, allocation operation, full
  optional result, original state fields, ordered ledger and cache. An omitted
  membership guard supplies no premise for this refinement.\<close>

end
