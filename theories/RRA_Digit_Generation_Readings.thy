theory RRA_Digit_Generation_Readings
  imports RRA_Lookup_Generation_Checking RRA_Digit_Allocated_Projection
begin

lemma digit_allocated_artifact_function:
  "digit_allocated_artifacts q=encoded_environment_artifacts digit_use_path (snd (raw_digit_allocated q))"
  by (rule ext; transfer; simp)

lemma digit_allocated_binding_function:
  "digit_allocated_bindings q=encoded_environment_bindings digit_use_path digit_address_path (snd (raw_digit_allocated q))"
  by (rule ext, rule ext; transfer; simp)

lemma digit_allocated_reading_contract:
  "environment_lookup_reading (digit_allocated_artifacts q) (digit_allocated_bindings q) (snd (digit_allocated_view q))"
  by (unfold_locales)
    (simp only: digit_allocated_artifact_function digit_allocated_binding_function digit_allocated_view_raw
      encoded_bounded_view_def snd_conv;
      rule digit_environment.view_exact[unfolded encoded_environment_represents_def])

lemma digit_allocated_environment_formed:
  "finite_environment_formed (snd (digit_allocated_view q))"
proof -
  obtain E where formed: "finite_environment_formed E"
    and represented: "encoded_environment_represents digit_use_path digit_address_path (snd (raw_digit_allocated q)) E"
    using digit_allocated_valid[of q] by (auto simp: encoded_bounded_valid_def)
  show ?thesis by (simp only: digit_allocated_view_raw encoded_bounded_view_def snd_conv
    digit_environment.view_representation[OF represented]; rule formed)
qed

definition digit_generation_fields where
  "digit_generation_fields q=lookup_generation_field_readings (digit_allocated_artifacts q) (digit_allocated_bindings q)"

definition digit_check_generation where
  "digit_check_generation q G=lookup_check_generation G (digit_allocated_artifacts q) (digit_allocated_bindings q)"

definition digit_generation_ready where
  "digit_generation_ready q=lookup_generation_record_ready (digit_allocated_artifacts q) (digit_allocated_bindings q)"

definition digit_generation_anchor where
  "digit_generation_anchor q=lookup_anchor_artifact (digit_allocated_artifacts q)"

theorem digit_generation_fields_exact:
  "digit_generation_fields q u r=finite_generation_field_readings (snd (digit_allocated_view q)) u r"
  unfolding digit_generation_fields_def
  by (rule environment_lookup_reading.generation_fields_exact[OF digit_allocated_reading_contract digit_allocated_environment_formed])

theorem digit_generation_check_exact:
  "digit_check_generation q G u r=finite_check_generation G (snd (digit_allocated_view q)) u r"
  unfolding digit_check_generation_def
  by (rule environment_lookup_reading.generation_check_exact[OF digit_allocated_reading_contract digit_allocated_environment_formed])

theorem digit_generation_readiness_exact:
  "digit_generation_ready q l p c rows=finite_generation_record_ready (snd (digit_allocated_view q)) l p c rows"
  unfolding digit_generation_ready_def
  by (rule environment_lookup_reading.generation_readiness_exact[OF digit_allocated_reading_contract digit_allocated_environment_formed])

theorem digit_generation_anchor_exact:
  "digit_generation_anchor q d=finite_anchor_artifact (snd (digit_allocated_view q)) d"
  unfolding digit_generation_anchor_def
  by (rule environment_lookup_reading.anchor_artifact_exact[OF digit_allocated_reading_contract])

text \<open>
  The existing closed digit-store type carries original formation and complete
  lookups. Every field reading, recursive generation check, readiness result
  and selected anchor equals its original finite operation on every input.
  The complete view occurs in the contract, not in these native operations.
\<close>

end
