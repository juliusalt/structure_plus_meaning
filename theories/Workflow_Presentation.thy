theory Workflow_Presentation
  imports Finite_Presented_Workflows Finite_Term_Words Factor_Workflow_Comparison Factor_Required_Workflow_Comparison
    Factor_Workflow_Input_Scope Factor_Workflow_Expanded_Comparison Native_Workflow_Execution_Base
begin

section \<open>Workflow comparisons specialize the investigation packet\<close>

definition finite_workflow_assessment_value ::
  "finite_factor_term list list\<times>finite_factor_term list list\<times>bool \<Rightarrow> finite_factor_term" where
  "finite_workflow_assessment_value=finite_pair_presentation (finite_sequence_presentation (finite_sequence_presentation id))
    (finite_pair_presentation (finite_sequence_presentation (finite_sequence_presentation id)) finite_boolean_data)"

definition finite_workflow_packet_value where
  "finite_workflow_packet_value subject execution=finite_investigation_packet_value
    (finite_pair_presentation (finite_pair_presentation subject id) execution)
    (finite_pair_presentation execution finite_workflow_assessment_value)"

lemma finite_workflow_packet_values_injective [intro]:
  "inj finite_workflow_assessment_value"
  "inj subject \<Longrightarrow> inj execution \<Longrightarrow> inj (finite_workflow_packet_value subject execution)"
  unfolding finite_workflow_assessment_value_def finite_workflow_packet_value_def
  by (intro finite_investigation_packet_value_injective finite_pair_presentation_injective inj_on_id
      finite_sequence_presentation_injective finite_boolean_data_injective)+

definition finite_workflow_case_value where
  "finite_workflow_case_value=finite_pair_presentation finite_required_workflow_value id"

lemma finite_workflow_case_value_injective [intro]: "inj finite_workflow_case_value"
  unfolding finite_workflow_case_value_def
  by (intro finite_pair_presentation_injective finite_required_workflow_value_injective inj_on_id)

section \<open>Complete workflow, required, expanded and input scope reports\<close>

definition workflow_presented_report where
  "workflow_presented_report ws selections=(let packet=workflow_packet ws selections in
    (workflow_indices,ws,packet,assessment_truth_rows (\<lambda>(actual,A). workflow_inspect A) [0,1,2,3] (fst packet)))"

definition workflow_report_value where
  "workflow_report_value ws selections=finite_scoped_report_value
    (finite_workflow_packet_value finite_workflow_protocol_value finite_workflow_execution_value)
    (workflow_presented_report ws selections)"

definition required_workflow_presented_report where
  "required_workflow_presented_report ws selections=(let packet=required_workflow_packet ws selections in
    (required_workflow_indices,ws,packet,assessment_truth_rows (\<lambda>(actual,A). workflow_inspect A) [0,1,2,3] (fst packet)))"

definition required_workflow_report_value where
  "required_workflow_report_value ws selections=finite_scoped_report_value
    (finite_workflow_packet_value finite_required_workflow_value (finite_option_presentation finite_workflow_execution_value))
    (required_workflow_presented_report ws selections)"

definition workflow_report_selections :: "nat list list" where
  "workflow_report_selections=[[],[0,1],[0,1,2,3]]"

definition expanded_workflow_report_scope :: "nat list" where
  "expanded_workflow_report_scope=(case expanded_workflow_indices of None \<Rightarrow> [] | Some ws \<Rightarrow> ws)"

definition expanded_workflow_presented_report where
  "expanded_workflow_presented_report ws selections=(let packet=expanded_workflow_packet ws selections in
    (expanded_workflow_indices,ws,packet,
      map_option (\<lambda>p. assessment_truth_rows (\<lambda>(actual,A). workflow_inspect A) [0,1,2,3] (fst p)) packet))"

definition finite_expanded_workflow_report_value where
  "finite_expanded_workflow_report_value=finite_pair_presentation (finite_option_presentation finite_index_sequence_value)
    (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation
      (finite_option_presentation (finite_workflow_packet_value finite_required_workflow_value
        (finite_option_presentation finite_workflow_execution_value)))
      (finite_option_presentation finite_assessment_truth_value)))"

definition expanded_workflow_report_value where
  "expanded_workflow_report_value ws selections=finite_expanded_workflow_report_value
    (expanded_workflow_presented_report ws selections)"

definition workflow_input_scope_presented_report where
  "workflow_input_scope_presented_report (ws::nat list) selections=
    (workflow_input_scope_indices,ws,workflow_input_scope_packet selections,selected_workflow_input_scope)"

definition finite_workflow_input_scope_report_value where
  "finite_workflow_input_scope_report_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation
      (finite_investigation_packet_value (finite_sequence_presentation finite_workflow_case_value)
        (finite_pair_presentation (finite_sequence_presentation finite_workflow_case_value)
          (finite_indexed_rows_value finite_boolean_data)))
      (finite_option_presentation (finite_sequence_presentation finite_workflow_case_value))))"

definition workflow_input_scope_report_value where
  "workflow_input_scope_report_value ws selections=finite_workflow_input_scope_report_value
    (workflow_input_scope_presented_report ws selections)"

definition workflow_input_scope_report_selections :: "nat list list" where
  "workflow_input_scope_report_selections=[[],[0,1],[0,1,2,3,4]]"

lemma workflow_report_values_injective:
  "inj (finite_scoped_report_value
    (finite_workflow_packet_value finite_workflow_protocol_value finite_workflow_execution_value))"
  "inj (finite_scoped_report_value
    (finite_workflow_packet_value finite_required_workflow_value (finite_option_presentation finite_workflow_execution_value)))"
  "inj finite_expanded_workflow_report_value" "inj finite_workflow_input_scope_report_value"
  unfolding finite_expanded_workflow_report_value_def finite_workflow_input_scope_report_value_def
  by (intro finite_scoped_report_value_injective finite_workflow_packet_values_injective
      finite_workflow_protocol_value_injective finite_workflow_execution_value_injective
      finite_required_workflow_value_injective finite_option_presentation_injective finite_pair_presentation_injective
      finite_index_values_injective finite_assessment_truth_value_injective finite_investigation_packet_value_injective
      finite_sequence_presentation_injective finite_workflow_case_value_injective finite_indexed_rows_value_injective
      finite_boolean_data_injective)+

theorem workflow_report_words_exact:
  "finite_term_shared_word (workflow_report_value ws s)=finite_term_shared_word (workflow_report_value vs t) \<longleftrightarrow>
    workflow_presented_report ws s=workflow_presented_report vs t"
  "finite_term_shared_word (required_workflow_report_value ws s)=
    finite_term_shared_word (required_workflow_report_value vs t) \<longleftrightarrow>
    required_workflow_presented_report ws s=required_workflow_presented_report vs t"
  "finite_term_shared_word (expanded_workflow_report_value ws s)=
    finite_term_shared_word (expanded_workflow_report_value vs t) \<longleftrightarrow>
    expanded_workflow_presented_report ws s=expanded_workflow_presented_report vs t"
  "finite_term_shared_word (workflow_input_scope_report_value ws s)=
    finite_term_shared_word (workflow_input_scope_report_value vs t) \<longleftrightarrow>
    workflow_input_scope_presented_report ws s=workflow_input_scope_presented_report vs t"
  by (simp_all add: finite_term_shared_word_injective workflow_report_value_def required_workflow_report_value_def
      expanded_workflow_report_value_def workflow_input_scope_report_value_def
      inj_eq[OF workflow_report_values_injective(1)] inj_eq[OF workflow_report_values_injective(2)]
      inj_eq[OF workflow_report_values_injective(3)] inj_eq[OF workflow_report_values_injective(4)])

text \<open>
  A workflow packet specializes the investigation packet with a subject, its
  problem and execution in each context and every candidate execution with its
  complete path assessment. Protocols with complete executions and required
  workflows with optional executions specialize it. The expanded report keeps the
  optional selected scope and packet, and the input scope report keeps every
  candidate scope with its computed qualities and the selected scope. Each report
  keeps its scopes and every actual inspection.
\<close>

end
