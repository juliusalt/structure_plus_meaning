theory Factor_Digit_Policy_Replay
  imports Factor_Parametric_Policy_Attempts Factor_Digit_Policy_Causes RRA_Digit_Generation_Backend
begin

definition digit_policy_record_replay where
  "digit_policy_record_replay K ku entry H l rows E pu pr au ar root R=
    optional_checked_result (\<lambda>(A,u,G,J,C). digit_certified_policy_cause K ku [] entry A u [] G E root R)
      (\<lambda>(A,u,G,J,C). (A,u,G))
      (record_native_replay_with digit_construct_generation H l rows E pu pr au ar root R)"

theorem digit_policy_record_replay_exact:
  "digit_policy_record_replay K ku entry H l rows E pu pr au ar root R=
    policy_record_replay_with (\<lambda>q. snd (digit_allocated_view q)) digit_construct_generation
      K ku entry H l rows E pu pr au ar root R"
  by (simp only: digit_policy_record_replay_def policy_record_replay_with_def digit_certified_policy_cause_exact)

theorem digit_policy_record_replay_projection:
  "map_option (\<lambda>(A,u,G). (digit_allocated_view A,u,G))
      (digit_policy_record_replay K ku entry H l rows E pu pr au ar root R)=
    policy_record_replay_with snd finite_construct_bounded_generation
      K ku entry (digit_allocated_view H) l rows E pu pr au ar root R"
  unfolding digit_policy_record_replay_exact
  by (rule policy_record_replay_with_projection[where project=digit_allocated_view
    and original=finite_construct_bounded_generation]) (rule digit_construct_generation_projection, rule refl)

theorem digit_policy_record_replay_append_valid:
  assumes previous: "finite_required_history_valid q"
    and material: "snd (digit_allocated_view H)=required_history_material q"
    and result: "digit_policy_record_replay (required_history_policy q) (required_history_policy_use q)
      (required_history_entry q) H l rows E pu pr au ar root R=Some (A,u,G)"
  shows "finite_required_history_valid (finite_required_history_append q (snd (digit_allocated_view A)) u G)"
  using result[unfolded digit_policy_record_replay_exact]
  by (rule policy_record_replay_append_valid[OF digit_generation_backend.generation_record_backend_axioms previous material])

text \<open>
  The actual digit policy check filters the actual digit replay result. Its
  full optional result projects to the independently established bounded policy
  attempt. Original history validity reuses the existing backend and append
  contracts; no whole generation-material view occurs in this native operation.
\<close>

end
