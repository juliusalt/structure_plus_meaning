theory Factor_Success_Shared_History
  imports Factor_Shared_History_Construction Optional_Success_Reuse
begin

fun history_request_members_present where
  "history_request_members_present (q,History_Step l rows E pu pr au ar root R)=
    indexed_history_members (digit_history_index (raw_digit_required_history q)) rows"

lemma history_unguarded_from_checked:
  assumes members: "history_request_members_present X"
  shows "digit_history_unguarded X=map_option raw_digit_required_history (digit_history_apply X)"
  using members by (cases X; cases "snd X")
    (simp add: digit_history_step_raw digit_required_history_step_def)

lemma history_checked_success_without_policy:
  assumes result: "map_option raw_digit_required_history (digit_history_apply X)=Some following"
  shows "digit_history_without_policy X=Some following"
proof -
  obtain q l rows E pu pr au ar root R where shape:
    "X=(q,History_Step l rows E pu pr au ar root R)"
    by (cases X; cases "snd X") auto
  have members: "indexed_history_members (digit_history_index (raw_digit_required_history q)) rows"
    and checked: "map_option (\<lambda>(A,u,G). digit_history_append_state (raw_digit_required_history q) A u G)
      (digit_required_history_attempt (raw_digit_required_history q) l rows E pu pr au ar root R)=Some following"
    using result by (auto simp: shape digit_history_step_raw digit_required_history_step_def split: if_splits)
  have unfiltered: "map_option (\<lambda>(A,u,G,J,C). digit_history_append_state (raw_digit_required_history q) A u G)
      (record_native_replay_with digit_construct_generation (digit_history_material (raw_digit_required_history q))
        l rows E pu pr au ar root R)=Some following"
    using mapped_checked_success_unfiltered[OF checked[unfolded
      digit_required_history_attempt_def digit_policy_record_replay_def]]
    by (simp add: comp_def case_prod_unfold)
  show ?thesis by (simp add: shape Let_def members unfiltered)
qed

lemma history_checked_success_without_replay:
  assumes result: "map_option raw_digit_required_history (digit_history_apply X)=Some following"
  shows "digit_history_without_replay X=Some following"
  using history_checked_success_without_policy[OF result]
  by (cases X; cases "snd X")
    (auto simp: Let_def record_native_replay_with_def option.map_comp comp_def
      case_prod_unfold split: if_splits option.splits prod.splits)

definition history_reused_controls where
  "history_reused_controls X typed=(
    if history_request_members_present X then typed else digit_history_unguarded X,
    optional_success_reuse typed (\<lambda>_. digit_history_without_policy X),
    optional_success_reuse typed (\<lambda>_. digit_history_without_replay X))"

lemma history_reused_controls_exact:
  assumes typed: "typed=map_option raw_digit_required_history (digit_history_apply X)"
  shows "history_reused_controls X typed=
    (digit_history_unguarded X,digit_history_without_policy X,digit_history_without_replay X)"
proof -
  have policy: "optional_success_reuse typed (\<lambda>_. digit_history_without_policy X)=digit_history_without_policy X"
    by (rule optional_success_reuse_exact; simp only: typed; erule history_checked_success_without_policy)
  have replay: "optional_success_reuse typed (\<lambda>_. digit_history_without_replay X)=digit_history_without_replay X"
    by (rule optional_success_reuse_exact; simp only: typed; erule history_checked_success_without_replay)
  have membership: "(if history_request_members_present X then typed else digit_history_unguarded X)=
    digit_history_unguarded X"
    by (cases "history_request_members_present X")
      (simp_all add: typed history_unguarded_from_checked)
  show ?thesis by (simp only: history_reused_controls_def membership policy replay)
qed

declare digit_history_prepare_shared_code[code del]

lemma digit_history_prepare_success_shared_code [code]:
  "digit_history_prepare X=(let typed=map_option raw_digit_required_history (constructed_history_apply X);
    controls=history_reused_controls X typed
    in (X,map_option digit_history_state_view typed,typed,digit_history_legacy X,
      fst controls,fst (snd controls),snd (snd controls)))"
proof -
  have controls: "history_reused_controls X (map_option raw_digit_required_history (constructed_history_apply X))=
    (digit_history_unguarded X,digit_history_without_policy X,digit_history_without_replay X)"
    by (rule history_reused_controls_exact; simp only: constructed_history_apply_exact)
  show ?thesis by (simp only: Let_def controls fst_conv snd_conv digit_history_prepare_shared_code)
qed

text \<open>The complete checked result is shared with each original omitted
  guard operation only under its actual sufficient premise. Membership allows
  reuse of the unguarded result even on failure. Policy and replay controls
  reuse only a complete successful result; otherwise their actual operations
  still execute and may expose the original omitted-guard failures.\<close>

end
