theory Factor_Digit_Policy_Construction
  imports Factor_Known_Replay_Policy Factor_Digit_Policy_Replay
begin

definition digit_policy_record_from_source where
  "digit_policy_record_from_source=policy_record_replay_from_source digit_construct_generation"

theorem digit_policy_record_from_source_exact:
  "digit_policy_record_from_source K ku entry H l rows E pu pr au ar root R=
    digit_policy_record_replay K ku entry H l rows E pu pr au ar root R"
  unfolding digit_policy_record_from_source_def digit_policy_record_replay_exact
  by (rule generation_record_backend.policy_record_replay_from_source_exact[
    OF digit_generation_backend.generation_record_backend_axioms])

export_code digit_policy_record_from_source checking SML

end
