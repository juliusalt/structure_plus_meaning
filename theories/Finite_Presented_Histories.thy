theory Finite_Presented_Histories
  imports Finite_Presented_Structures
    Factor_Required_History_Methods
begin

section \<open>A required history keeps every stored component\<close>

definition finite_history_member_value ::
  "(local_address option definition_site\<times>finite_generation) \<Rightarrow> finite_factor_term" where
  "finite_history_member_value=finite_pair_presentation finite_site_data (finite_generation_value Finite_Target)"

lemma finite_history_members_injective [intro]:
  "inj (finite_sequence_presentation finite_history_member_value)"
  unfolding finite_history_member_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective finite_site_data_injective
      finite_generation_value_injective finite_target_injective)

lemma finite_history_goals_injective [intro]:
  "inj (finite_sequence_presentation (finite_goal_value finite_site_data))"
  by (intro finite_sequence_presentation_injective finite_goal_value_injective finite_site_data_injective)

definition finite_history_state_value :: "finite_required_history_state \<Rightarrow> finite_factor_term" where
  "finite_history_state_value q=
    Finite_Pair (finite_environment_presentation (required_history_source q))
    (Finite_Pair (finite_use_data (required_history_source_use q))
    (Finite_Pair (Finite_Payload (required_history_source_root q))
    (Finite_Pair (finite_sequence_presentation (finite_goal_value finite_site_data) (required_history_goals q))
    (Finite_Pair (finite_site_data (required_history_entry q))
    (Finite_Pair (finite_environment_presentation (required_history_policy q))
    (Finite_Pair (finite_use_data (required_history_policy_use q))
    (Finite_Pair (finite_environment_presentation (required_history_material q))
      (finite_sequence_presentation finite_history_member_value (required_history_members q)))))))))"

lemma finite_history_state_value_injective [intro]: "inj finite_history_state_value"
proof (rule injI)
  fix q r assume same: "finite_history_state_value q=finite_history_state_value r"
  show "q=r"
    by (rule finite_required_history_state.equality;
      use same in \<open>simp add: finite_history_state_value_def inj_eq[OF finite_environment_presentation_injective]
        inj_eq[OF finite_use_data_injective] inj_eq[OF finite_site_data_injective]
        inj_eq[OF finite_history_goals_injective] inj_eq[OF finite_history_members_injective]\<close>)
qed

definition finite_required_history_value :: "required_history \<Rightarrow> finite_factor_term" where
  "finite_required_history_value h=finite_history_state_value (raw_required_history h)"

lemma finite_required_history_value_injective [intro]: "inj finite_required_history_value"
  by (rule injI) (simp add: finite_required_history_value_def inj_eq[OF finite_history_state_value_injective]
    raw_required_history_inject)

fun finite_history_input_value :: "required_history_input \<Rightarrow> finite_factor_term" where
  "finite_history_input_value (History_Step l rows E pu pr au ar root R)=
    Finite_Pair (Finite_Target l)
    (Finite_Pair (finite_sequence_presentation finite_history_member_value rows)
    (Finite_Pair (finite_environment_presentation E)
    (Finite_Pair (finite_use_data pu)
    (Finite_Pair (Finite_Payload pr)
    (Finite_Pair (finite_use_data au)
    (Finite_Pair (Finite_Payload ar)
    (Finite_Pair (finite_site_data root) (finite_artifact_term R))))))))"

lemma finite_history_input_value_injective [intro]: "inj finite_history_input_value"
proof (rule injI)
  fix x y assume same: "finite_history_input_value x=finite_history_input_value y"
  then show "x=y"
    by (cases x; cases y) (simp add: inj_eq[OF finite_target_injective]
      inj_eq[OF finite_history_members_injective] inj_eq[OF finite_environment_presentation_injective]
      inj_eq[OF finite_use_data_injective] inj_eq[OF finite_site_data_injective] inj_eq[OF finite_artifact_term_injective])
qed

section \<open>Certificates, subjects and result rows compose those presentations\<close>

definition finite_native_schema_proof_value ::
  "(local_address,local_address,local_address) finite_schema_proof \<Rightarrow> finite_factor_term" where
  "finite_native_schema_proof_value=finite_proof_value Finite_Payload (finite_pair_presentation Finite_Payload id) Finite_Payload"

lemma finite_native_schema_proof_value_injective [intro]: "inj finite_native_schema_proof_value"
  unfolding finite_native_schema_proof_value_def
  by (intro finite_proof_value_injective finite_pair_presentation_injective finite_payload_injective inj_on_id)

definition finite_history_certificate_value :: "required_history_certificate \<Rightarrow> finite_factor_term" where
  "finite_history_certificate_value=finite_pair_presentation finite_call_value finite_native_schema_proof_value"

lemma finite_history_certificate_value_injective [intro]: "inj finite_history_certificate_value"
  unfolding finite_history_certificate_value_def
  by (intro finite_pair_presentation_injective finite_call_value_injective finite_native_schema_proof_value_injective)

definition finite_history_subject_value ::
  "(required_history_certificate option\<times>required_history_subject option) \<Rightarrow> finite_factor_term" where
  "finite_history_subject_value=finite_pair_presentation (finite_option_presentation finite_history_certificate_value)
    (finite_option_presentation (finite_pair_presentation finite_required_history_value finite_history_input_value))"

definition finite_history_result_value :: "required_history_result_row \<Rightarrow> finite_factor_term" where
  "finite_history_result_value=finite_pair_presentation (finite_option_presentation finite_history_certificate_value)
    (finite_option_presentation (finite_option_presentation finite_history_state_value))"

lemma finite_history_rows_injective [intro]:
  "inj finite_history_subject_value" "inj finite_history_result_value"
  unfolding finite_history_subject_value_def finite_history_result_value_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
      finite_history_certificate_value_injective finite_required_history_value_injective
      finite_history_input_value_injective finite_history_state_value_injective)+

text \<open>
  A required history is presented by its raw state; the state keeps its source,
  policy and material environments, uses, root, goal sequence, entry site and
  ordered member ledger. Every component uses the presentation of its notion, so
  the whole presentation is injective without assuming validity.
\<close>

end
