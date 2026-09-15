theory Factor_Digit_History_Steps
  imports Factor_Digit_History_Projection Factor_Digit_Policy_Replay
begin

definition digit_history_append_state where
  "digit_history_append_state (q::digit_required_history_state) A u G=
    q\<lparr>digit_history_material:=A,digit_history_ledger:=((u,[]),G)#digit_history_ledger q,
      digit_history_index:=history_member_insert (digit_history_index q) u [] G\<rparr>"

lemma digit_history_append_components:
  "digit_history_header (digit_history_append_state q A u G)=digit_history_header q"
  "digit_history_material (digit_history_append_state q A u G)=A"
  "digit_history_ledger (digit_history_append_state q A u G)=((u,[]),G)#digit_history_ledger q"
  "digit_history_index (digit_history_append_state q A u G)=history_member_insert (digit_history_index q) u [] G"
  by (simp_all add: digit_history_append_state_def)

lemma digit_history_append_original:
  "digit_history_original_state (digit_history_append_state q A u G)=
    finite_required_history_append (digit_history_original_state q) (snd (digit_allocated_view A)) u G"
  by (simp add: digit_history_append_state_def digit_history_original_state_def finite_history_append_components)

lemma digit_history_append_base:
  "digit_history_base_view (digit_history_append_state q A u G)=
    (fst (digit_allocated_view A),finite_required_history_append (digit_history_original_state q)
      (snd (digit_allocated_view A)) u G)"
  by (simp only: digit_history_base_view_def digit_history_append_original digit_history_append_components)

definition digit_required_history_attempt where
  "digit_required_history_attempt q l rows E pu pr au ar root R=digit_policy_record_replay
    (history_header_policy (digit_history_header q)) (history_header_policy_use (digit_history_header q))
    (history_header_entry (digit_history_header q)) (digit_history_material q) l rows E pu pr au ar root R"

definition bounded_history_attempt where
  "bounded_history_attempt (state::nat\<times>finite_required_history_state) l rows E pu pr au ar root R=
    policy_record_replay_with snd finite_construct_bounded_generation
      (required_history_policy (snd state)) (required_history_policy_use (snd state)) (required_history_entry (snd state))
      (fst state,required_history_material (snd state)) l rows E pu pr au ar root R"

lemma digit_required_history_attempt_projection:
  "map_option (\<lambda>(A,u,G). (digit_allocated_view A,u,G))
      (digit_required_history_attempt q l rows E pu pr au ar root R)=
    bounded_history_attempt (digit_history_base_view q) l rows E pu pr au ar root R"
  by (simp only: digit_required_history_attempt_def bounded_history_attempt_def digit_history_base_components
    digit_history_policy_fields digit_history_original_components prod.collapse digit_policy_record_replay_projection)

lemma digit_required_history_attempt_valid:
  assumes previous: "finite_required_history_valid (digit_history_original_state q)"
    and result: "digit_required_history_attempt q l rows E pu pr au ar root R=Some (A,u,G)"
  shows "finite_required_history_valid (finite_required_history_append (digit_history_original_state q)
    (snd (digit_allocated_view A)) u G)"
proof -
  have attempt: "digit_policy_record_replay (required_history_policy (digit_history_original_state q))
    (required_history_policy_use (digit_history_original_state q)) (required_history_entry (digit_history_original_state q))
    (digit_history_material q) l rows E pu pr au ar root R=Some (A,u,G)"
    using result by (simp only: digit_required_history_attempt_def digit_history_policy_fields)
  show ?thesis by (rule digit_policy_record_replay_append_valid[OF previous _ attempt])
    (simp only: digit_history_original_components)
qed

definition digit_required_history_step where
  "digit_required_history_step q l rows E pu pr au ar root R=(if indexed_history_members (digit_history_index q) rows then
    map_option (\<lambda>(A,u,G). digit_history_append_state q A u G)
      (digit_required_history_attempt q l rows E pu pr au ar root R) else None)"

definition bounded_required_history_step where
  "bounded_required_history_step (state::nat\<times>finite_required_history_state) l rows E pu pr au ar root R=(
    if list_all (\<lambda>row. row\<in>set (required_history_members (snd state))) rows then
      map_option (\<lambda>((n,A),u,G). (n,finite_required_history_append (snd state) A u G))
        (bounded_history_attempt state l rows E pu pr au ar root R) else None)"

theorem digit_required_history_step_projection:
  assumes cache: "history_member_index_exact (digit_history_index q) (digit_history_ledger q)"
  shows "map_option digit_history_base_view (digit_required_history_step q l rows E pu pr au ar root R)=
    bounded_required_history_step (digit_history_base_view q) l rows E pu pr au ar root R"
  by (simp add: digit_required_history_step_def bounded_required_history_step_def
    digit_history_base_components digit_history_original_components indexed_history_members_exact[OF cache]
    digit_required_history_attempt_projection[symmetric] option.map_comp comp_def
    case_prod_unfold digit_history_append_base)

theorem digit_required_history_step_valid:
  assumes previous: "digit_required_history_valid q"
    and result: "digit_required_history_step q l rows E pu pr au ar root R=Some following"
  shows "digit_required_history_valid following"
proof -
  have original: "finite_required_history_valid (digit_history_original_state q)"
    and cache: "history_member_index_exact (digit_history_index q) (digit_history_ledger q)"
    using previous by (simp only: digit_required_history_valid_def; blast)+
  obtain A u G where attempt: "digit_required_history_attempt q l rows E pu pr au ar root R=Some (A,u,G)"
    and following: "following=digit_history_append_state q A u G"
    using result by (auto simp: digit_required_history_step_def split: option.splits if_splits)
  have next_original: "finite_required_history_valid (digit_history_original_state following)"
    using digit_required_history_attempt_valid[OF original attempt]
    by (simp only: following digit_history_append_original)
  have next_cache: "history_member_index_exact (digit_history_index following) (digit_history_ledger following)"
    using history_member_insert_exact[OF cache, of u "[]" G]
    by (simp add: following digit_history_append_state_def)
  show ?thesis using next_original next_cache by (simp only: digit_required_history_valid_def)
qed

lift_definition (code_dt) digit_history_step ::
  "digit_required_history\<Rightarrow>finite_exact_target\<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>local_address\<Rightarrow>local_address option definition_site\<Rightarrow>
    finite_exact_artifact\<Rightarrow>digit_required_history option"
  is digit_required_history_step
  by (auto intro: optional_result_invariant digit_required_history_step_valid)

lemma digit_history_step_raw:
  "map_option raw_digit_required_history (digit_history_step q l rows E pu pr au ar root R)=
    digit_required_history_step (raw_digit_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

theorem digit_required_history_step_view:
  assumes valid: "digit_required_history_valid q"
  shows "map_option digit_history_state_view (digit_required_history_step q l rows E pu pr au ar root R)=
    map_option bounded_history_result_view
      (bounded_required_history_step (digit_history_base_view q) l rows E pu pr au ar root R)"
proof (rule optional_result_view_projection)
  have cache: "history_member_index_exact (digit_history_index q) (digit_history_ledger q)"
    using valid by (simp only: digit_required_history_valid_def; blast)
  show "map_option digit_history_base_view (digit_required_history_step q l rows E pu pr au ar root R)=
    bounded_required_history_step (digit_history_base_view q) l rows E pu pr au ar root R"
    by (rule digit_required_history_step_projection[OF cache])
next
  fix following
  assume result: "digit_required_history_step q l rows E pu pr au ar root R=Some following"
  have "digit_required_history_valid following" by (rule digit_required_history_step_valid[OF valid result])
  then show "digit_history_state_view following=bounded_history_result_view (digit_history_base_view following)"
    by (simp only: digit_required_history_valid_def; blast intro: digit_history_state_view_cache)
qed

theorem digit_history_step_view:
  "map_option digit_history_view (digit_history_step q l rows E pu pr au ar root R)=
    map_option bounded_history_result_view (bounded_required_history_step
      (digit_history_base_view (raw_digit_required_history q)) l rows E pu pr au ar root R)"
proof -
  have "map_option digit_history_state_view
      (map_option raw_digit_required_history (digit_history_step q l rows E pu pr au ar root R))=
    map_option bounded_history_result_view (bounded_required_history_step
      (digit_history_base_view (raw_digit_required_history q)) l rows E pu pr au ar root R)"
    by (simp only: digit_history_step_raw digit_required_history_step_view[OF digit_required_history_valid])
  then show ?thesis by (simp only: option.map_comp comp_def digit_history_view_def[abs_def])
qed

export_code digit_history_step digit_history_view checking SML

text \<open>
  The actual member index checks every requested predecessor. The actual digit
  replay and policy operation returns the new material, generation and use, then
  one append preserves the header and advances both the ordered ledger and cache.
  The complete optional result retains the original state, actual allocation
  head and entire cache relation. Validity reuses the original append contract;
  full historical permission and reachability remain separate obligations.
\<close>

end
