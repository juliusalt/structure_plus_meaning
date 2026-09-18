theory Native_Control_Guard_Execution
  imports Native_Control_Installed_Guard Native_Control_Quotation_Code
begin

definition installed_guard_source_available ::
  "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> bool" where
  "installed_guard_source_available K v=(finite_native_source K v []\<noteq>None)"

lemma installed_guard_source_available_exact:
  "installed_guard_source_available K v \<longleftrightarrow>
    (\<exists>T. native_package_at (decode_finite_environment K) v [] T)"
  by (simp only: installed_guard_source_available_def finite_native_source_absent; blast)

export_code installed_guard_source_available admitted_guard_requests admitted_guard_install admitted_guard_install_summary
  judgment_artifact_choice guard_representation_choice finite_guard_constructor checked_judgment_rows
  judgment_bridge_question judgment_artifact_execution_question guard_representation_execution_question
  judgment_steering_questions context_execution_summary native_steered_development
  judgment_artifact_value judgment_bridge_install_value finite_sequence_presentation
  finite_system_formed finite_native_source finite_term_shared_word_fold integer_of_nat
  fcard finite_system_definitions
  in Eval module_name Native_Control_Installed file_prefix "native_control_installed"


end
