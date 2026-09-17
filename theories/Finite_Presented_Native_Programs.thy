theory Finite_Presented_Native_Programs
  imports Finite_Presented_Replays
begin

section \<open>Native source problems, sources, answers and evidenced results\<close>

definition finite_native_source_problem_value ::
  "('r \<Rightarrow> finite_factor_term) \<Rightarrow>
    local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>'r \<Rightarrow> finite_factor_term" where
  "finite_native_source_problem_value rest=finite_pair_presentation finite_environment_presentation
    (finite_pair_presentation finite_use_data (finite_pair_presentation Finite_Payload rest))"

lemma finite_native_source_problem_value_injective [intro]:
  "inj rest \<Longrightarrow> inj (finite_native_source_problem_value rest)"
  unfolding finite_native_source_problem_value_def
  by (intro finite_pair_presentation_injective finite_environment_presentation_injective finite_use_data_injective
      finite_payload_injective)

definition finite_native_source_value where
  "finite_native_source_value=finite_option_presentation finite_native_system_value"

lemma finite_native_source_value_injective [intro]: "inj finite_native_source_value"
  unfolding finite_native_source_value_def
  by (intro finite_option_presentation_injective finite_native_system_value_injective)

definition finite_native_answers_value where
  "finite_native_answers_value answer=finite_option_presentation (finite_pair_presentation finite_native_system_value
    (finite_collection_presentation answer))"

lemma finite_native_answers_value_injective [intro]:
  "inj answer \<Longrightarrow> inj (finite_native_answers_value answer)"
  unfolding finite_native_answers_value_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective
      finite_native_system_value_injective finite_collection_presentation_injective)

definition finite_native_program_evaluation_value where
  "finite_native_program_evaluation_value=finite_native_answers_value finite_call_value"

lemma finite_native_program_evaluation_value_injective [intro]: "inj finite_native_program_evaluation_value"
  unfolding finite_native_program_evaluation_value_def
  by (intro finite_native_answers_value_injective finite_call_value_injective)

definition finite_native_evidence_result_value where
  "finite_native_evidence_result_value evidence=finite_option_presentation (finite_pair_presentation finite_native_system_value
    (finite_pair_presentation (finite_collection_presentation finite_call_value) evidence))"

lemma finite_native_evidence_result_value_injective [intro]:
  "inj evidence \<Longrightarrow> inj (finite_native_evidence_result_value evidence)"
  unfolding finite_native_evidence_result_value_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective
      finite_native_system_value_injective finite_collection_presentation_injective finite_call_value_injective)

definition finite_admitted_terms_value :: "finite_factor_term fset option \<Rightarrow> finite_factor_term" where
  "finite_admitted_terms_value=finite_option_presentation (finite_collection_presentation id)"

lemma finite_admitted_terms_value_injective [intro]: "inj finite_admitted_terms_value"
  unfolding finite_admitted_terms_value_def
  by (intro finite_option_presentation_injective finite_collection_presentation_injective inj_on_id)

text \<open>
  A native source problem is an environment, a use, a root and the problem's
  further inputs. A source is the optional native system read there. Answers
  keep the system with every answer, specialized to calls for an ordinary
  program evaluation; an evidenced result also keeps the evidence of those
  calls. Admitted terms are the optional requested terms a reading keeps. Each
  presentation states only the injectivity contracts of its parts.
\<close>

end
