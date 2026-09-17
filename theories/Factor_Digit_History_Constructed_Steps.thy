theory Factor_Digit_History_Constructed_Steps
  imports Factor_Digit_History_Constructed_Attempts
begin

definition digit_required_history_constructed_step where
  "digit_required_history_constructed_step=digit_history_step_using digit_history_constructed_attempt"

theorem digit_required_history_constructed_step_exact:
  assumes valid: "digit_required_history_valid q"
  shows "digit_required_history_constructed_step q l rows E pu pr au ar root R=
    digit_required_history_step q l rows E pu pr au ar root R"
  unfolding digit_required_history_constructed_step_def digit_history_step_original_instance[symmetric]
  by (rule digit_history_step_attempt_congruence)
    (rule digit_history_constructed_attempt_exact[OF valid])

lift_definition (code_dt) digit_history_constructed_step ::
  "digit_required_history\<Rightarrow>finite_exact_target\<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>local_address\<Rightarrow>local_address option definition_site\<Rightarrow>
    finite_exact_artifact\<Rightarrow>digit_required_history option"
  is digit_required_history_constructed_step
  by (auto simp only: digit_required_history_constructed_step_exact
    intro: optional_result_invariant digit_required_history_step_valid)

lemma digit_history_constructed_step_raw:
  "map_option raw_digit_required_history (digit_history_constructed_step q l rows E pu pr au ar root R)=
    digit_required_history_constructed_step (raw_digit_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

theorem digit_history_constructed_step_exact:
  "digit_history_constructed_step q l rows E pu pr au ar root R=digit_history_step q l rows E pu pr au ar root R"
proof -
  have same: "map_option raw_digit_required_history (digit_history_constructed_step q l rows E pu pr au ar root R)=
    map_option raw_digit_required_history (digit_history_step q l rows E pu pr au ar root R)"
    by (simp only: digit_history_constructed_step_raw digit_history_step_raw
      digit_required_history_constructed_step_exact[OF digit_required_history_valid])
  show ?thesis using same
    by (simp only: optional_identity_map_injective[OF raw_digit_required_history_inject])
qed

text \<open>
  The original membership guard and ordered append are unchanged. The closed
  operation preserves every refusal and complete state, including its stored
  head, material, fixed header, ordered ledger and exact membership cache.
  The private known constructor obtains its prerequisite from this guard and
  the closed invariant; it does not admit arbitrary unrecorded predecessor rows.
  Full physical cost, historical permission and reachability remain separate.
\<close>

end
