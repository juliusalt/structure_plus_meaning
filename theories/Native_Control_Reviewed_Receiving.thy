theory Native_Control_Reviewed_Receiving
  imports Native_Control_Receiving_Controls
begin

section \<open>The original admission chooses the operation that is executed\<close>

definition receiving_program_result where
  "receiving_program_result program reports = (let rows=receiving_construct reports in
    (rows,optional_view_run receiving_read receiving_project [] (fst program) rows))"

lemma receiving_selected_result_exact:
  assumes chosen: "receiving_refinement_choice report = Some program"
  shows "receiving_program_result program (body,adapter,target) =
    admitted_guard_received body adapter target"
  using receiving_refinement_selected_program[OF chosen]
  by (simp add: receiving_program_result_def receiving_construct_def Let_def
    receiving_project_option admitted_guard_received_reuses_original_view)

definition native_reviewed_receiving where
  "native_reviewed_receiving review reports = map_option
    (\<lambda>program. receiving_program_result program reports) (receiving_refinement_choice review)"

theorem native_reviewed_receiving_exact:
  "native_reviewed_receiving review (body,adapter,target) =
    map_option (\<lambda>_. admitted_guard_received body adapter target) (receiving_refinement_choice review)"
  unfolding native_reviewed_receiving_def
  by (cases "receiving_refinement_choice review") (simp_all add: receiving_selected_result_exact)

definition native_reviewed_receiving_family where
  "native_reviewed_receiving_family review subjects = map_option
    (\<lambda>program. Parallel.map (receiving_program_result program) subjects) (receiving_refinement_choice review)"

theorem native_reviewed_receiving_family_exact:
  "native_reviewed_receiving_family review subjects = map_option (\<lambda>_.
    map (\<lambda>(body,adapter,target). admitted_guard_received body adapter target) subjects)
      (receiving_refinement_choice review)"
proof (cases "receiving_refinement_choice review")
  case None then show ?thesis by (simp add: native_reviewed_receiving_family_def)
next
  case (Some program)
  have each: "receiving_program_result program reports =
    (case reports of (body,adapter,target) \<Rightarrow> admitted_guard_received body adapter target)" for reports
    by (cases reports rule: prod_cases3) (simp only: prod.case receiving_selected_result_exact[OF Some])
  have same_function: "receiving_program_result program =
      (\<lambda>(body,adapter,target). admitted_guard_received body adapter target)"
    by (rule ext) (rule each)
  show ?thesis by (simp only: native_reviewed_receiving_family_def Some option.simps Parallel.map_def same_function)
qed

definition native_reviewed_source_query where
  "native_reviewed_source_query review K v = map_option (\<lambda>program.
    source_reader_run (snd program) (\<lambda>(E,u). installed_guard_source_available E u) (K,v))
      (receiving_refinement_choice review)"

theorem native_reviewed_source_query_exact:
  "native_reviewed_source_query review K v = map_option
    (\<lambda>_. installed_guard_source_available K v) (receiving_refinement_choice review)"
proof (cases "receiving_refinement_choice review")
  case None then show ?thesis by (simp add: native_reviewed_source_query_def)
next
  case (Some program)
  have program: "program=(Project_Optional,Keep_Source_Reader)"
    by (rule receiving_refinement_selected_program[OF Some])
  show ?thesis by (simp add: native_reviewed_source_query_def Some program)
qed

definition receiving_result_summary where
  "receiving_result_summary result = (case result of (rows,checks) \<Rightarrow>
    (admitted_guard_install_summary rows,checks))"

definition receiving_input_controls where
  "receiving_input_controls body adapter target = [
    (body,adapter,target),
    (absent_development_report,adapter,target),
    (body,absent_development_report,target),
    (body,adapter,absent_development_report)]"

lemma receiving_original_refusals:
  "admitted_guard_received absent_development_report adapter target = (None,None)"
  "admitted_guard_received body absent_development_report target = (None,None)"
  "admitted_guard_received body adapter absent_development_report = (None,None)"
  by (simp_all add: admitted_guard_received_def installed_guard_source_checks_def)

lemma native_reviewed_receiving_absent:
  "native_reviewed_receiving absent_development_report reports = None"
  "native_reviewed_receiving_family absent_development_report subjects = None"
  "native_reviewed_source_query absent_development_report K v = None"
  by (simp_all add: native_reviewed_receiving_def native_reviewed_receiving_family_def
    native_reviewed_source_query_def receiving_refinement_choice_def)

definition receiving_checks_value where
  "receiving_checks_value = finite_option_presentation (finite_sequence_presentation
    (finite_pair_presentation isabelle_position_data finite_boolean_data))"

definition receiving_complete_value where
  "receiving_complete_value = finite_pair_presentation judgment_bridge_install_value receiving_checks_value"

lemma receiving_complete_value_injective: "inj receiving_complete_value"
  unfolding receiving_complete_value_def receiving_checks_value_def
  by (intro finite_pair_presentation_injective judgment_bridge_install_value_injective
    finite_option_presentation_injective finite_sequence_presentation_injective
    isabelle_position_data_injective finite_boolean_data_injective)

export_code native_reviewed_receiving native_reviewed_receiving_family native_reviewed_source_query
  receiving_input_controls receiving_result_summary receiving_empty_source
  receiving_refinement_question receiving_refinement_choice receiving_facets optional_view_observation
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  judgment_bridge_install_value receiving_complete_value admitted_guard_install_summary
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Reviewed_Receiving file_prefix "native_control_reviewed_receiving"

text \<open>The interpreter consumes the program returned by the original native
  admission. It does not receive a host-selected method. Its complete optional
  result equals the original receiving operation on every three reports; the
  family equation preserves order, multiplicity and failures while exposing
  independent operations. The arbitrary-source query still executes its original
  reader. The complete presentation also retains the returned source view.\<close>

end
