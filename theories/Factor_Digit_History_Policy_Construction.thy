theory Factor_Digit_History_Policy_Construction
  imports Factor_Digit_Policy_Construction Factor_Digit_History_Attempt_Refinement Finite_Reader_Identity_Maps
begin

definition digit_history_policy_attempt where
  "digit_history_policy_attempt q l rows E pu pr au ar root R=digit_policy_record_from_source
    (history_header_policy (digit_history_header q)) (history_header_policy_use (digit_history_header q))
    (history_header_entry (digit_history_header q)) (digit_history_material q) l rows E pu pr au ar root R"

lemma digit_history_policy_attempt_exact:
  "digit_history_policy_attempt q l rows E pu pr au ar root R=digit_required_history_attempt q l rows E pu pr au ar root R"
  by (simp only: digit_history_policy_attempt_def digit_required_history_attempt_def digit_policy_record_from_source_exact)

definition digit_required_history_policy_step where
  "digit_required_history_policy_step=digit_history_step_using digit_history_policy_attempt"

theorem digit_required_history_policy_step_exact:
  "digit_required_history_policy_step q l rows E pu pr au ar root R=digit_required_history_step q l rows E pu pr au ar root R"
  unfolding digit_required_history_policy_step_def digit_history_step_original_instance[symmetric]
  by (rule digit_history_step_attempt_congruence) (rule digit_history_policy_attempt_exact)

lift_definition (code_dt) digit_history_policy_step ::
  "digit_required_history\<Rightarrow>finite_exact_target\<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>local_address\<Rightarrow>local_address option definition_site\<Rightarrow>
    finite_exact_artifact\<Rightarrow>digit_required_history option"
  is digit_required_history_policy_step
  by (auto simp only: digit_required_history_policy_step_exact
    intro: optional_result_invariant digit_required_history_step_valid)

lemma digit_history_policy_step_raw:
  "map_option raw_digit_required_history (digit_history_policy_step q l rows E pu pr au ar root R)=
    digit_required_history_policy_step (raw_digit_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

theorem digit_history_policy_step_exact:
  "digit_history_policy_step q l rows E pu pr au ar root R=digit_history_step q l rows E pu pr au ar root R"
proof -
  have same: "map_option raw_digit_required_history (digit_history_policy_step q l rows E pu pr au ar root R)=
    map_option raw_digit_required_history (digit_history_step q l rows E pu pr au ar root R)"
    by (simp only: digit_history_policy_step_raw digit_history_step_raw digit_required_history_policy_step_exact)
  show ?thesis using same
    by (simp only: optional_identity_map_injective[OF raw_digit_required_history_inject])
qed

text \<open>
  The ordinary digit constructor instantiates the established semantic backend.
  Original history membership still guards the attempt, and the same complete
  append constructs the closed result. The raw and typed operations retain
  exact complete equality, including early refusal under the actual policy.
  This refinement is independent of the known-predecessor constructor and does
  not establish full historical permission, reachability or physical cost.
\<close>

end
