theory Factor_Replay_Constructor_Congruence
  imports Factor_Parametric_Generation_Replay
begin

lemma record_native_replay_constructor_congruence:
  assumes each: "\<And>p c. construct H l p c rows=original H l p c rows"
  shows "record_native_replay_with construct H l rows E pu pr au ar root R=
    record_native_replay_with original H l rows E pu pr au ar root R"
  by (simp only: record_native_replay_with_def each)

text \<open>
  Equality of the actual constructor calls at the fixed material, locus and
  predecessor rows suffices for the whole replay result. Every payload and
  quotation target is quantified. Original replay admission, quotation,
  refusals and all successful result fields are unchanged.
\<close>

end
