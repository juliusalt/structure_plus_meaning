theory Native_Control_Source_Execution
  imports Native_Control_Sourced_Children Native_Control_Child_Review
begin

type_synonym guard_source_record_result = "local_address option finite_artifact_environment \<times>
  (nat \<times> local_address option definition_site) fset \<times>
  local_address option definition_site \<times> local_address option finite_artifact_environment \<times>
  local_address option \<times> local_address option finite_native_system"

definition guard_source_records_value ::
    "(nat \<times> guard_source_record_result option) list option \<Rightarrow> finite_factor_term" where
  "guard_source_records_value=finite_option_presentation (finite_sequence_presentation
    (finite_pair_presentation finite_natural_data (finite_option_presentation
      (finite_pair_presentation finite_environment_presentation
        (finite_pair_presentation (finite_collection_presentation
          (finite_pair_presentation finite_natural_data finite_site_data))
          (finite_pair_presentation finite_site_data
            (finite_pair_presentation finite_environment_presentation
              (finite_pair_presentation finite_use_data finite_native_system_value))))))))"

lemma guard_source_records_value_injective: "inj guard_source_records_value"
  unfolding guard_source_records_value_def
  by (intro finite_option_presentation_injective finite_sequence_presentation_injective
    finite_pair_presentation_injective finite_collection_presentation_injective
    finite_natural_data_injective finite_site_data_injective finite_environment_presentation_injective
    finite_use_data_injective finite_native_system_value_injective)

definition guard_source_records_summary ::
    "(nat \<times> guard_source_record_result option) list option \<Rightarrow> (nat \<times> (nat \<times> nat \<times> nat) option) list option" where
  "guard_source_records_summary=map_option (map (\<lambda>(i,source). (i,
    map_option (\<lambda>(E,coordinates,d,K,v,P).
      (fcard coordinates,fcard (finite_system_definitions P),fcard (finite_system_clauses P))) source)))"

export_code admitted_guard_source_records guard_source_records_value guard_source_records_summary
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Source_Execution file_prefix "native_control_source_execution"

text \<open>The complete retained value includes the original environment, every
  definition-coordinate pair, installed entry, installed environment, use and
  the actual recovered program. The summary is diagnostic only. Original native
  reports gate this operation and the original reader supplies the source.\<close>

end
