theory Factor_Digit_History_References
  imports Factor_Digit_History_Steps Factor_Required_History_Methods
begin

type_synonym digit_history_subject = "digit_required_history\<times>required_history_input"
type_synonym digit_history_result_row = "required_history_certificate option\<times>digit_history_result option option"

fun bounded_history_transition where
  "bounded_history_transition (state::nat\<times>finite_required_history_state)
      (History_Step l rows E pu pr au ar root R) following=(
    set rows\<subseteq>set (required_history_members (snd state)) \<and>
    (\<exists>A u G J C. record_native_replay_with finite_construct_bounded_generation
      (fst state,required_history_material (snd state)) l rows E pu pr au ar root R=Some (A,u,G,J,C) \<and>
      certified_policy_cause_at (decode_finite_environment (required_history_policy (snd state)))
        (required_history_policy_use (snd state)) [] (required_history_entry (snd state))
        (decode_finite_environment (snd A)) u [] (decode_finite_generation G)
        (decode_finite_environment E) root (decode_finite_object R) \<and>
      following=(fst A,finite_required_history_append (snd state) (snd A) u G)))"

lemma bounded_history_transition_exact:
  "bounded_required_history_step state l rows E pu pr au ar root R=Some following \<longleftrightarrow>
    bounded_history_transition state (History_Step l rows E pu pr au ar root R) following"
  by (auto simp: bounded_required_history_step_def bounded_history_attempt_def
    policy_record_replay_with_result finite_certified_policy_cause_exact list_all_iff split: option.splits prod.splits)

fun digit_history_apply where
  "digit_history_apply (q,History_Step l rows E pu pr au ar root R)=digit_history_step q l rows E pu pr au ar root R"

fun digit_history_reference_option where
  "digit_history_reference_option (q,History_Step l rows E pu pr au ar root R)=
    map_option bounded_history_result_view (bounded_required_history_step
      (digit_history_base_view (raw_digit_required_history q)) l rows E pu pr au ar root R)"

definition digit_history_transition where
  "digit_history_transition X following=(case X of (q,input) \<Rightarrow> case following of (n,A,I) \<Rightarrow>
    bounded_history_transition (digit_history_base_view (raw_digit_required_history q)) input (n,A) \<and>
    I=fset_of_list (required_history_members A))"

theorem digit_history_reference_exact:
  "digit_history_reference_option X=Some following \<longleftrightarrow> digit_history_transition X following"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  show ?thesis by (cases input; cases following)
    (auto simp: shape digit_history_transition_def bounded_history_result_view_def
      bounded_history_transition_exact split: option.splits prod.splits)
qed

lemma digit_history_apply_exact:
  "map_option digit_history_view (digit_history_apply X)=digit_history_reference_option X"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  show ?thesis by (cases input) (simp only: shape digit_history_apply.simps digit_history_reference_option.simps
    digit_history_step_view)
qed

definition digit_history_family_reference where
  "digit_history_family_reference subjects=fimage (\<lambda>(key,input).
    (key,map_option digit_history_reference_option input)) subjects"

definition digit_history_family_condition where
  "digit_history_family_condition f method subjects=relation_reader_condition
    (\<lambda>row. row |\<in>| digit_history_family_reference subjects) f (method subjects)"

fun digit_history_unguarded where
  "digit_history_unguarded (q,History_Step l rows E pu pr au ar root R)=
    map_option (\<lambda>(A,u,G). digit_history_append_state (raw_digit_required_history q) A u G)
      (digit_required_history_attempt (raw_digit_required_history q) l rows E pu pr au ar root R)"

fun digit_history_without_policy where
  "digit_history_without_policy (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    if indexed_history_members (digit_history_index previous) rows then
      map_option (\<lambda>(A,u,G,J,C). digit_history_append_state previous A u G)
        (record_native_replay_with digit_construct_generation (digit_history_material previous)
          l rows E pu pr au ar root R) else None)"

fun digit_history_without_replay where
  "digit_history_without_replay (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    if indexed_history_members (digit_history_index previous) rows then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> map_option (\<lambda>(A,u,G). digit_history_append_state previous A u G)
          (digit_construct_generation (digit_history_material previous) l (Finite_Whole R) (Finite_Whole C) rows))
    else None)"

fun digit_history_legacy where
  "digit_history_legacy (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_digit_required_history q in
    map_option (\<lambda>following. (Suc (Suc (fst (digit_allocated_view (digit_history_material previous)))),
      following,fset_of_list (required_history_members following)))
      (finite_required_history_step (digit_history_original_state previous) l rows E pu pr au ar root R))"

definition digit_history_prepare where
  "digit_history_prepare X=(X,digit_history_reference_option X,
    map_option raw_digit_required_history (digit_history_apply X),digit_history_legacy X,
    digit_history_unguarded X,digit_history_without_policy X,digit_history_without_replay X)"

text \<open>
  The independent bounded history operation determines the complete result and
  cache relation. Actual typed, legacy and omitted-guard operations are prepared
  once for each whole subject. The legacy original history remains a separate
  allocation operation. Missing membership, policy and replay checks are actual
  alternate operations, not supplied truth values.
\<close>

end
