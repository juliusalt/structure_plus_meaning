theory RRA_Known_Generation_Rows
  imports RRA_Digit_Generation_Construction
begin

definition generation_record_targets_ready where
  "generation_record_targets_ready l p c rows=(finite_target_formed l \<and>
    finite_target_formed p \<and> finite_target_formed c \<and> distinct (map snd rows))"

lemma finite_generation_ready_known_rows:
  assumes formed: "finite_environment_formed E"
    and rows: "list_all (\<lambda>(d,G). finite_check_generation G E (fst d) (snd d)) rows"
  shows "finite_generation_record_ready E l p c rows=generation_record_targets_ready l p c rows"
  by (simp only: finite_generation_record_ready_def generation_record_targets_ready_def formed rows simp_thms)

definition digit_generation_body where
  "digit_generation_body q l p c rows=Option.bind
    (keyed_option_map (digit_generation_anchor q) (map fst rows)) (\<lambda>anchors.
      map_option (\<lambda>following. (following,digit_allocated_next_use q,finite_generation_record_core l p c rows))
        (digit_generation_installation q l p c anchors))"

lemma digit_construct_generation_factored:
  "digit_construct_generation q l p c rows=(if digit_generation_ready q l p c rows then
    digit_generation_body q l p c rows else None)"
  by (simp only: digit_construct_generation_def digit_generation_body_def)

definition digit_construct_known_generation where
  "digit_construct_known_generation q l p c rows=(if generation_record_targets_ready l p c rows then
    digit_generation_body q l p c rows else None)"

theorem digit_construct_known_generation_exact:
  assumes rows: "list_all (\<lambda>(d,G). finite_check_generation G
    (snd (digit_allocated_view q)) (fst d) (snd d)) rows"
  shows "digit_construct_known_generation q l p c rows=digit_construct_generation q l p c rows"
  by (simp only: digit_construct_known_generation_def digit_construct_generation_factored
    digit_generation_readiness_exact
    finite_generation_ready_known_rows[OF digit_allocated_environment_formed rows])

text \<open>
  The exact predecessor-reading premise removes only its repeated recursive
  check. Target formation, distinctness, actual anchor selection, allocation,
  binding installation and literal grafting remain the original operations.
  This private constructor is not an admission operation on arbitrary rows:
  its complete equality requires every stated original predecessor reading.
\<close>

end
