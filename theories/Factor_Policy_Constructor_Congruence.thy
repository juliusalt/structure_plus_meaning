theory Factor_Policy_Constructor_Congruence
  imports Factor_Known_Replay_Policy
begin

lemma policy_record_from_source_constructor_congruence:
  assumes each: "\<And>p c. construct H l p c rows=original H l p c rows"
  shows "policy_record_replay_from_source construct K ku entry H l rows E pu pr au ar root R=
    policy_record_replay_from_source original K ku entry H l rows E pu pr au ar root R"
  by (simp only: policy_record_replay_from_source_def each)

text \<open>
  Every constructor call uses the fixed material, locus and predecessor rows.
  Equality for all actual payload and quotation targets therefore preserves
  the entire policy construction, including its original replay guard,
  quotation, package-policy check, refusals and complete successful values.
\<close>

end
