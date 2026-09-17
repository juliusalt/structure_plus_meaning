theory Development_Presentation
  imports Finite_Presented_Workflows Finite_Term_Words Factor_Development_Comparison Factor_Source_Development_Cases
    Native_Development_Execution_Base
begin

section \<open>Development results, assessments and steering\<close>

definition finite_development_result_value where
  "finite_development_result_value=finite_pair_presentation finite_development_report_value finite_development_decision_value"

definition finite_development_assessment_value :: "bool\<times>bool\<times>bool\<times>bool\<times>bool \<Rightarrow> finite_factor_term" where
  "finite_development_assessment_value=finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data finite_boolean_data)))"

definition finite_development_context_value where
  "finite_development_context_value=finite_pair_presentation finite_development_question_value finite_development_result_value"

definition finite_development_cell_value where
  "finite_development_cell_value=finite_pair_presentation finite_development_result_value finite_development_assessment_value"

definition finite_steered_result_value where
  "finite_steered_result_value=finite_pair_presentation finite_natural_data (finite_pair_presentation
    finite_development_question_value (finite_pair_presentation finite_development_report_value
      (finite_pair_presentation finite_development_decision_value finite_development_decision_value)))"

definition finite_development_steering_value where
  "finite_development_steering_value=finite_pair_presentation (finite_sequence_presentation finite_development_question_value)
    (finite_pair_presentation (finite_assessment_table_value finite_development_context_value finite_development_cell_value)
      (finite_option_presentation (finite_pair_presentation finite_development_question_value
        (finite_pair_presentation finite_development_report_value (finite_pair_presentation finite_development_decision_value
          (finite_option_presentation finite_index_sequence_value))))))"

definition finite_steered_development_value where
  "finite_steered_development_value request=finite_pair_presentation (finite_sequence_presentation request)
    (finite_pair_presentation finite_development_steering_value
      (finite_pair_presentation (finite_option_presentation finite_natural_data)
        (finite_option_presentation (finite_sequence_presentation finite_steered_result_value))))"

lemma finite_development_values_injective [intro]:
  "inj finite_development_result_value" "inj finite_development_assessment_value"
  "inj finite_development_context_value" "inj finite_development_cell_value"
  "inj finite_steered_result_value" "inj finite_development_steering_value"
  "inj request \<Longrightarrow> inj (finite_steered_development_value request)"
  unfolding finite_development_result_value_def finite_development_assessment_value_def
    finite_development_context_value_def finite_development_cell_value_def finite_steered_result_value_def
    finite_development_steering_value_def finite_steered_development_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective finite_natural_data_injective
      finite_option_presentation_injective finite_sequence_presentation_injective finite_assessment_table_value_injective
      finite_development_report_value_injective finite_development_decision_value_injective
      finite_development_question_value_injective finite_index_values_injective)+

section \<open>Source development requests, reports and admissions\<close>

definition finite_source_proposal_value :: "source_development_proposal \<Rightarrow> finite_factor_term" where
  "finite_source_proposal_value=finite_pair_presentation finite_native_system_value finite_site_data"

definition finite_source_entry_value :: "source_development_entry \<Rightarrow> finite_factor_term" where
  "finite_source_entry_value=finite_pair_presentation finite_site_data
    (finite_pair_presentation finite_environment_presentation finite_use_data)"

definition source_development_request_view :: "source_development_request \<Rightarrow> _" where
  "source_development_request_view R=(source_development_environment R,source_development_use R,
    source_development_root R,source_development_targets R,source_development_input R,source_development_outputs R)"

lemma source_development_request_view_injective [intro]: "inj source_development_request_view"
proof (rule injI)
  fix x y :: source_development_request
  assume same: "source_development_request_view x=source_development_request_view y"
  show "x=y" by (rule source_development_request.equality; use same in \<open>simp add: source_development_request_view_def\<close>)
qed

definition finite_source_request_value where
  "finite_source_request_value=finite_viewed_value (finite_native_source_problem_value
    (finite_pair_presentation (finite_sequence_presentation finite_source_proposal_value)
      (finite_pair_presentation id (finite_sequence_presentation id)))) source_development_request_view"

definition source_development_report_view :: "source_development_report \<Rightarrow> _" where
  "source_development_report_view report=(source_report_proposals report,source_report_observations report,
    source_report_question report,source_report_execution report,source_report_selected report,
    source_report_installed report,source_report_stage report,source_report_query report)"

lemma source_development_report_view_injective [intro]: "inj source_development_report_view"
proof (rule injI)
  fix x y :: source_development_report
  assume same: "source_development_report_view x=source_development_report_view y"
  show "x=y" by (rule source_development_report.equality; use same in \<open>simp add: source_development_report_view_def\<close>)
qed

definition finite_source_report_value where
  "finite_source_report_value=finite_viewed_value (finite_pair_presentation
    (finite_sequence_presentation finite_source_proposal_value)
    (finite_pair_presentation (finite_indexed_rows_value (finite_sequence_presentation finite_boolean_data))
      (finite_pair_presentation (finite_option_presentation finite_development_question_value)
        (finite_pair_presentation (finite_option_presentation finite_steered_result_value)
          (finite_pair_presentation (finite_option_presentation finite_source_proposal_value)
            (finite_pair_presentation (finite_option_presentation finite_source_entry_value)
              (finite_pair_presentation (finite_option_presentation finite_workflow_stage_value)
                (finite_option_presentation finite_workflow_stage_result_value))))))))
    source_development_report_view"

definition finite_source_admission_value where
  "finite_source_admission_value=finite_option_presentation (finite_pair_presentation finite_source_proposal_value
    (finite_pair_presentation finite_source_entry_value finite_workflow_stage_result_value))"

definition finite_source_development_value where
  "finite_source_development_value=finite_pair_presentation (finite_sequence_presentation finite_source_request_value)
    (finite_pair_presentation (finite_steered_development_value finite_development_question_value)
      (finite_option_presentation (finite_sequence_presentation (finite_pair_presentation finite_source_request_value
        (finite_pair_presentation finite_source_report_value finite_source_admission_value)))))"

lemma finite_source_development_values_injective [intro]:
  "inj finite_source_proposal_value" "inj finite_source_entry_value" "inj finite_source_request_value"
  "inj finite_source_report_value" "inj finite_source_admission_value" "inj finite_source_development_value"
proof -
  show proposal: "inj finite_source_proposal_value"
    unfolding finite_source_proposal_value_def
    by (intro finite_pair_presentation_injective finite_native_system_value_injective finite_site_data_injective)
  show entry: "inj finite_source_entry_value"
    unfolding finite_source_entry_value_def
    by (intro finite_pair_presentation_injective finite_site_data_injective finite_environment_presentation_injective
        finite_use_data_injective)
  show request: "inj finite_source_request_value"
    unfolding finite_source_request_value_def
    by (intro finite_viewed_value_injective finite_native_source_problem_value_injective finite_pair_presentation_injective
        finite_sequence_presentation_injective proposal inj_on_id source_development_request_view_injective)
  show report: "inj finite_source_report_value"
    unfolding finite_source_report_value_def
    by (intro finite_viewed_value_injective finite_pair_presentation_injective finite_sequence_presentation_injective
        proposal finite_indexed_rows_value_injective finite_boolean_data_injective finite_option_presentation_injective
        finite_development_question_value_injective finite_development_values_injective entry
        finite_workflow_stage_value_injective finite_workflow_stage_result_value_injective
        source_development_report_view_injective)
  show admission: "inj finite_source_admission_value"
    unfolding finite_source_admission_value_def
    by (intro finite_option_presentation_injective finite_pair_presentation_injective proposal entry
        finite_workflow_stage_result_value_injective)
  show "inj finite_source_development_value"
    unfolding finite_source_development_value_def
    by (intro finite_pair_presentation_injective finite_sequence_presentation_injective request
        finite_development_values_injective finite_development_question_value_injective
        finite_option_presentation_injective report admission)
qed

section \<open>Complete development, steering and source development reports\<close>

definition native_development_presented_report where
  "native_development_presented_report ws selections=(let packet=development_producer_packet ws selections in
    (native_development_indices,ws,packet,
      assessment_truth_rows (\<lambda>(actual,A). development_producer_inspect A) development_facets (fst packet)))"

definition native_development_report_value where
  "native_development_report_value ws selections=finite_scoped_report_value
    (finite_investigation_packet_value finite_development_context_value finite_development_cell_value)
    (native_development_presented_report ws selections)"

definition native_development_report_selections :: "nat list list" where
  "native_development_report_selections=[[],[0,1],[0,1,2,3,4]]"

definition development_empty_questions :: "native_development_question list" where
  "development_empty_questions=[]"

definition development_first_questions :: "native_development_question list" where
  "development_first_questions=take 1 development_case_inputs"

definition native_steering_presented_report where
  "native_steering_presented_report qs requests=(let result=native_steered_development qs requests in
    (development_methods,development_facets,result,
      assessment_truth_rows (\<lambda>(actual,A). development_producer_inspect A) development_facets
        (fst (snd (fst (snd result))))))"

definition native_steering_report_value where
  "native_steering_report_value qs requests=finite_scoped_report_value
    (finite_steered_development_value finite_development_question_value)
    (native_steering_presented_report qs requests)"

definition source_development_presented_report where
  "source_development_presented_report qs requests=(let result=native_source_development qs requests;
    controls=(case snd (snd result) of Some ((R,report,admission)#rows) \<Rightarrow> source_development_report_controls R report
      | _ \<Rightarrow> [])
    in (development_methods,development_facets,(result,controls),
      assessment_truth_rows (\<lambda>(actual,A). development_producer_inspect A) development_facets
        (fst (snd (fst (snd (fst (snd result))))))))"

definition source_development_report_value where
  "source_development_report_value qs requests=finite_scoped_report_value
    (finite_pair_presentation finite_source_development_value
      (finite_indexed_rows_value (finite_pair_presentation finite_source_report_value finite_source_admission_value)))
    (source_development_presented_report qs requests)"

lemma development_report_values_injective:
  "inj (finite_scoped_report_value
    (finite_investigation_packet_value finite_development_context_value finite_development_cell_value))"
  "inj (finite_scoped_report_value (finite_steered_development_value finite_development_question_value))"
  "inj (finite_scoped_report_value (finite_pair_presentation finite_source_development_value
    (finite_indexed_rows_value (finite_pair_presentation finite_source_report_value finite_source_admission_value))))"
  by (intro finite_scoped_report_value_injective finite_investigation_packet_value_injective
      finite_development_values_injective finite_development_question_value_injective finite_pair_presentation_injective
      finite_source_development_values_injective finite_indexed_rows_value_injective)+

theorem development_report_words_exact:
  "finite_term_shared_word (native_development_report_value ws s)=
    finite_term_shared_word (native_development_report_value vs t) \<longleftrightarrow>
    native_development_presented_report ws s=native_development_presented_report vs t"
  "finite_term_shared_word (native_steering_report_value qs rs)=
    finite_term_shared_word (native_steering_report_value ps ts) \<longleftrightarrow>
    native_steering_presented_report qs rs=native_steering_presented_report ps ts"
  "finite_term_shared_word (source_development_report_value qs Rs)=
    finite_term_shared_word (source_development_report_value ps Ts) \<longleftrightarrow>
    source_development_presented_report qs Rs=source_development_presented_report ps Ts"
  by (simp_all add: finite_term_shared_word_injective native_development_report_value_def
      native_steering_report_value_def source_development_report_value_def
      inj_eq[OF development_report_values_injective(1)] inj_eq[OF development_report_values_injective(2)]
      inj_eq[OF development_report_values_injective(3)])

text \<open>
  Development contexts keep each complete question with its original report and
  reference decision, and cells keep every candidate report, decision and
  assessment. Steering keeps the questions, the complete table and the steering
  question, report, admission and selected methods, the choice and every steered
  result. Source development keeps every request, the steering policy and every
  request report and admission, together with each control report of the first
  request. Each presented report keeps its scopes and every actual inspection.
\<close>

end
