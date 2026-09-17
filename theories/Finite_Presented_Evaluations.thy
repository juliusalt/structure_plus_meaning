theory Finite_Presented_Evaluations
  imports Finite_Viewed_Values Finite_Presented_Native_Programs
begin

section \<open>Program calls, applications, rules and readings over their coordinates\<close>

definition finite_coordinate_call_value where
  "finite_coordinate_call_value site=finite_pair_presentation site id"

lemma finite_coordinate_call_value_injective [intro]: "inj site \<Longrightarrow> inj (finite_coordinate_call_value site)"
  unfolding finite_coordinate_call_value_def by (intro finite_pair_presentation_injective inj_on_id)

definition finite_coordinate_application_value where
  "finite_coordinate_application_value site address=finite_pair_presentation site (finite_pair_presentation address
    (finite_pair_presentation id (finite_pair_presentation
      (finite_collection_presentation (finite_pair_presentation address id))
      (finite_collection_presentation (finite_pair_presentation address (finite_coordinate_call_value site))))))"

lemma finite_coordinate_application_value_injective [intro]:
  "inj site \<Longrightarrow> inj address \<Longrightarrow> inj (finite_coordinate_application_value site address)"
  unfolding finite_coordinate_application_value_def
  by (intro finite_pair_presentation_injective finite_collection_presentation_injective inj_on_id
      finite_coordinate_call_value_injective)

definition finite_coordinate_rule_value where
  "finite_coordinate_rule_value site address=finite_pair_presentation (finite_coordinate_call_value site)
    (finite_collection_presentation (finite_pair_presentation address (finite_coordinate_call_value site)))"

lemma finite_coordinate_rule_value_injective [intro]:
  "inj site \<Longrightarrow> inj address \<Longrightarrow> inj (finite_coordinate_rule_value site address)"
  unfolding finite_coordinate_rule_value_def
  by (intro finite_pair_presentation_injective finite_collection_presentation_injective
      finite_coordinate_call_value_injective)

definition finite_program_readings_value where
  "finite_program_readings_value site address=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data
      (finite_pair_presentation (finite_collection_presentation (finite_coordinate_application_value site address))
        (finite_collection_presentation (finite_coordinate_rule_value site address)))))"

lemma finite_program_readings_value_injective [intro]:
  "inj site \<Longrightarrow> inj address \<Longrightarrow> inj (finite_program_readings_value site address)"
  unfolding finite_program_readings_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective finite_collection_presentation_injective
      finite_coordinate_application_value_injective finite_coordinate_rule_value_injective)

definition finite_program_answers_value where
  "finite_program_answers_value site=finite_option_presentation (finite_collection_presentation
    (finite_coordinate_call_value site))"

lemma finite_program_answers_value_injective [intro]: "inj site \<Longrightarrow> inj (finite_program_answers_value site)"
  unfolding finite_program_answers_value_def
  by (intro finite_option_presentation_injective finite_collection_presentation_injective
      finite_coordinate_call_value_injective)

definition finite_natural_system_value where
  "finite_natural_system_value=finite_system_presentation finite_natural_data finite_natural_data
    finite_natural_data finite_natural_data"

lemma finite_natural_system_value_injective [intro]: "inj finite_natural_system_value"
  unfolding finite_natural_system_value_def
  by (intro finite_system_presentation_injective finite_natural_data_injective)

section \<open>Environments presented through their artifact rows and bindings\<close>

definition finite_artifact_value_rows_value :: "artifact_value_rows \<Rightarrow> finite_factor_term" where
  "finite_artifact_value_rows_value=finite_pair_presentation (finite_sequence_presentation Finite_Payload)
    (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation Finite_Payload
        (finite_pair_presentation Finite_Payload Finite_Payload)))
      (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation Finite_Payload Finite_Payload))
        (finite_sequence_presentation (finite_pair_presentation Finite_Payload Finite_Payload))))"

lemma finite_artifact_value_rows_value_injective [intro]: "inj finite_artifact_value_rows_value"
  unfolding finite_artifact_value_rows_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective finite_payload_injective)

definition finite_environment_rows_value where
  "finite_environment_rows_value=finite_pair_presentation
    (finite_sequence_presentation (finite_pair_presentation finite_use_data finite_artifact_value_rows_value))
    (finite_sequence_presentation (finite_pair_presentation finite_site_data finite_use_data))"

lemma finite_environment_rows_value_injective [intro]: "inj finite_environment_rows_value"
  unfolding finite_environment_rows_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective finite_use_data_injective
      finite_artifact_value_rows_value_injective finite_site_data_injective)

text \<open>
  A call keeps its site and term; applications and rules keep their site,
  address, instantiated terms and premise calls; program readings keep formation,
  head coverage, demand closure, every application and every rule. All are
  parameterized by the presentations of their site and address coordinates, so
  native and natural coordinate programs specialize them. Answers are optional
  call collections. Environment rows keep every use with its complete artifact
  rows and every binding in order.
\<close>

end
