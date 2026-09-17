theory Evaluation_Presentation
  imports Finite_Presented_Evaluations Finite_Presented_Native_Construction Finite_Term_Words
    Factor_Program_Evaluation_Investigation Factor_Native_Evaluation_Cases
begin

section \<open>Program evaluations specialize readings over natural and native coordinates\<close>

definition program_evaluation_report_view where
  "program_evaluation_report_view report=(case report of (P,D,formed,covered,closed,A,R,answer,methods) \<Rightarrow>
    (P,D,(formed,covered,closed,A,R),answer,methods))"

lemma program_evaluation_report_view_injective [intro]: "inj program_evaluation_report_view"
  by (rule injI) (auto simp: program_evaluation_report_view_def split: prod.splits)

definition finite_program_evaluation_report_value where
  "finite_program_evaluation_report_value=finite_viewed_value (finite_pair_presentation finite_natural_system_value
    (finite_pair_presentation (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
      (finite_pair_presentation (finite_program_readings_value finite_natural_data finite_natural_data)
        (finite_pair_presentation (finite_program_answers_value finite_natural_data)
          (finite_indexed_rows_value (finite_pair_presentation (finite_program_answers_value finite_natural_data)
            (finite_indexed_rows_value finite_boolean_data)))))))
    program_evaluation_report_view"

definition finite_native_evaluation_report_value where
  "finite_native_evaluation_report_value=finite_option_presentation (finite_native_source_problem_value
    (finite_pair_presentation (finite_option_presentation finite_site_data)
      (finite_pair_presentation finite_native_source_value
        (finite_pair_presentation (finite_collection_presentation finite_call_value)
          (finite_pair_presentation (finite_option_presentation (finite_program_readings_value finite_site_data Finite_Payload))
            finite_native_program_evaluation_value)))))"

definition finite_investigation_selection_value where
  "finite_investigation_selection_value=finite_pair_presentation (finite_sequence_presentation finite_index_triple_value)
    (finite_pair_presentation (finite_sequence_presentation finite_index_pair_value) finite_index_sequence_value)"

lemma finite_evaluation_report_values_injective [intro]:
  "inj finite_program_evaluation_report_value" "inj finite_native_evaluation_report_value"
  "inj finite_investigation_selection_value"
  unfolding finite_program_evaluation_report_value_def finite_native_evaluation_report_value_def
    finite_investigation_selection_value_def
  by (intro finite_viewed_value_injective finite_pair_presentation_injective finite_natural_system_value_injective
      finite_collection_presentation_injective finite_coordinate_call_value_injective finite_natural_data_injective
      finite_program_readings_value_injective finite_program_answers_value_injective finite_indexed_rows_value_injective
      finite_boolean_data_injective program_evaluation_report_view_injective finite_option_presentation_injective
      finite_native_source_problem_value_injective finite_site_data_injective finite_native_source_value_injective
      finite_call_value_injective finite_payload_injective finite_native_program_evaluation_value_injective
      finite_sequence_presentation_injective finite_index_values_injective)+

section \<open>The complete program and native evaluation report\<close>

definition native_evaluation_indices :: "nat list" where
  "native_evaluation_indices=[0..<21]"

definition program_evaluation_presented_report where
  "program_evaluation_presented_report ws selections=(let
      observations=program_evaluation_investigation_observations;
      relation=program_evaluation_investigation_relation
    in (program_evaluation_workload_indices,ws,(map (\<lambda>w. (w,program_evaluation_report w)) ws,
      (observations,relation,program_evaluation_selected),
      map (investigation_cycle_report [0,1,2,3,4] [0,1,2] observations relation) selections,
      map (\<lambda>i. (i,native_evaluation_report i)) native_evaluation_indices)))"

definition finite_program_evaluation_packet_value where
  "finite_program_evaluation_packet_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation
      (finite_indexed_rows_value finite_program_evaluation_report_value)
      (finite_pair_presentation finite_investigation_selection_value
        (finite_pair_presentation (finite_sequence_presentation finite_investigation_cycle_value)
          (finite_indexed_rows_value finite_native_evaluation_report_value)))))"

definition program_evaluation_report_value where
  "program_evaluation_report_value ws selections=finite_program_evaluation_packet_value
    (program_evaluation_presented_report ws selections)"

definition program_evaluation_report_selections :: "nat list list" where
  "program_evaluation_report_selections=[[],[0],[0,1,2]]"

lemma finite_program_evaluation_packet_value_injective: "inj finite_program_evaluation_packet_value"
  unfolding finite_program_evaluation_packet_value_def
  by (intro finite_pair_presentation_injective finite_index_values_injective finite_indexed_rows_value_injective
      finite_evaluation_report_values_injective finite_sequence_presentation_injective finite_investigation_values_injective)

theorem program_evaluation_report_word_exact:
  "finite_term_shared_word (program_evaluation_report_value ws s)=
    finite_term_shared_word (program_evaluation_report_value vs t) \<longleftrightarrow>
    program_evaluation_presented_report ws s=program_evaluation_presented_report vs t"
  by (simp add: finite_term_shared_word_injective program_evaluation_report_value_def
      inj_eq[OF finite_program_evaluation_packet_value_injective])

text \<open>
  A natural coordinate program evaluation report is presented through the view
  that groups its program readings; every method keeps its answer and actual
  qualities. Native evaluation reports specialize native source problems with
  their focus, source, demand, readings and evaluation. The presented report
  keeps both scopes, the complete comparison selection, every revision cycle and
  every native evaluation.
\<close>

end
