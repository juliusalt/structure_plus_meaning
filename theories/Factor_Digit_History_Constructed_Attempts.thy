theory Factor_Digit_History_Constructed_Attempts
  imports Factor_Digit_History_Known_Generation Factor_Digit_History_Policy_Construction
    Factor_Policy_Constructor_Congruence
begin

definition digit_history_source_attempt_using where
  "digit_history_source_attempt_using construct q l rows E pu pr au ar root R=
    policy_record_replay_from_source construct
      (history_header_policy (digit_history_header q)) (history_header_policy_use (digit_history_header q))
      (history_header_entry (digit_history_header q)) (digit_history_material q) l rows E pu pr au ar root R"

lemma digit_history_source_attempt_original:
  "digit_history_source_attempt_using digit_construct_generation=digit_history_policy_attempt"
  by (simp only: digit_history_source_attempt_using_def[abs_def]
    digit_history_policy_attempt_def[abs_def] digit_policy_record_from_source_def)

lemma digit_history_source_attempt_constructor_congruence:
  assumes each: "\<And>p c. construct (digit_history_material q) l p c rows=
    original (digit_history_material q) l p c rows"
  shows "digit_history_source_attempt_using construct q l rows E pu pr au ar root R=
    digit_history_source_attempt_using original q l rows E pu pr au ar root R"
  unfolding digit_history_source_attempt_using_def
  by (rule policy_record_from_source_constructor_congruence) (rule each)

definition digit_history_constructed_attempt where
  "digit_history_constructed_attempt=digit_history_source_attempt_using digit_construct_known_generation"

theorem digit_history_constructed_attempt_exact:
  assumes valid: "digit_required_history_valid q"
    and members: "indexed_history_members (digit_history_index q) rows"
  shows "digit_history_constructed_attempt q l rows E pu pr au ar root R=
    digit_required_history_attempt q l rows E pu pr au ar root R"
proof -
  have same: "digit_history_source_attempt_using digit_construct_known_generation q l rows E pu pr au ar root R=
    digit_history_source_attempt_using digit_construct_generation q l rows E pu pr au ar root R"
    by (rule digit_history_source_attempt_constructor_congruence)
      (rule digit_construct_known_generation_exact[OF digit_history_indexed_generations[OF valid members]])
  show ?thesis by (simp only: digit_history_constructed_attempt_def same
    digit_history_source_attempt_original digit_history_policy_attempt_exact)
qed

text \<open>
  The original history invariant and actual index guard establish every
  predecessor reading. The actual successful replay and quotation contracts
  establish the complete scope used by policy construction. These are the
  separate prerequisites of the two refinements. Their composition retains
  every remaining original check and the entire optional result.
\<close>

end
