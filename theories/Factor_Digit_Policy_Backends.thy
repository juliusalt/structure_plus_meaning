theory Factor_Digit_Policy_Backends
  imports Factor_Digit_Policy_Replay Factor_Replay_Constructor_Congruence
begin

definition digit_policy_replay_using where
  "digit_policy_replay_using construct K ku entry H l rows E pu pr au ar root R=
    optional_checked_result (\<lambda>(A,u,G,J,C). digit_certified_policy_cause K ku [] entry A u [] G E root R)
      (\<lambda>(A,u,G,J,C). (A,u,G))
      (record_native_replay_with construct H l rows E pu pr au ar root R)"

lemma digit_policy_replay_original_instance:
  "digit_policy_replay_using digit_construct_generation=digit_policy_record_replay"
  by (simp only: digit_policy_replay_using_def[abs_def] digit_policy_record_replay_def[abs_def])

lemma digit_policy_replay_constructor_congruence:
  assumes each: "\<And>p c. construct H l p c rows=original H l p c rows"
  shows "digit_policy_replay_using construct K ku entry H l rows E pu pr au ar root R=
    digit_policy_replay_using original K ku entry H l rows E pu pr au ar root R"
proof -
  have replay: "record_native_replay_with construct H l rows E pu pr au ar root R=
    record_native_replay_with original H l rows E pu pr au ar root R"
    by (rule record_native_replay_constructor_congruence) (rule each)
  show ?thesis by (simp only: digit_policy_replay_using_def replay)
qed

text \<open>
  The unchanged complete digit policy check filters the complete replay result.
  A constructor refinement instantiates the shared replay congruence and never
  replaces policy checking with a constructor or history-validity claim.
\<close>

end
