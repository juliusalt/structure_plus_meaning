theory Native_Control_Artifact_Reused_Execution
  imports Native_Control_Quotation_Construction
begin

declare judgment_artifact_execution_question_def[code del]

lemma judgment_artifact_execution_reused_code [code]:
  "judgment_artifact_execution_question ignored=filtered_development_question judgment_artifact_candidates
    (\<lambda>a. list_all (\<lambda>s. syntax_judgment_check s \<longrightarrow> a=Complete_Artifact_Body) syntax_judgment_cases)"
  by (simp only: judgment_artifact_execution_question_def judgment_artifact_question_def
    judgment_artifact_reused_observation)

export_code judgment_artifact_probe judgment_artifact_check judgment_artifact_execution_question
  judgment_artifact_value judgment_steering_questions context_execution_summary native_steered_development
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Artifact file_prefix "native_control_artifact"

end
