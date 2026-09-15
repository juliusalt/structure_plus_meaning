theory Factor_Digit_History_Attempt_Refinement
  imports Factor_Digit_History_Steps
begin

definition digit_history_step_using where
  "digit_history_step_using attempt q l rows E pu pr au ar root R=(
    if indexed_history_members (digit_history_index q) rows then
      map_option (\<lambda>(A,u,G). digit_history_append_state q A u G)
        (attempt q l rows E pu pr au ar root R) else None)"

lemma digit_history_step_original_instance:
  "digit_history_step_using digit_required_history_attempt=digit_required_history_step"
  by (simp only: digit_history_step_using_def[abs_def] digit_required_history_step_def[abs_def])

lemma digit_history_step_attempt_congruence:
  assumes attempt: "indexed_history_members (digit_history_index q) rows \<Longrightarrow>
    build q l rows E pu pr au ar root R=original q l rows E pu pr au ar root R"
  shows "digit_history_step_using build q l rows E pu pr au ar root R=
    digit_history_step_using original q l rows E pu pr au ar root R"
  by (cases "indexed_history_members (digit_history_index q) rows")
    (simp_all only: digit_history_step_using_def attempt if_True if_False)

text \<open>
  The original exact index guard and complete ordered append are factored once.
  An attempt refinement needs its complete optional equation only under that
  actual guard. Refusal, fixed header, material, head, ledger and cache follow
  through the unchanged outer operation.
\<close>

end
