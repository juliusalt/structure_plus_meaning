theory Digit_Replay_Presentation
  imports Finite_Presented_Replays Finite_Presented_Assessments Finite_Term_Words
    Factor_Digit_Replay_Investigation
begin

section \<open>Replay contexts and assessments retain every optional level\<close>

definition finite_digit_replay_subject_value :: "digit_replay_subject \<Rightarrow> finite_factor_term" where
  "finite_digit_replay_subject_value=finite_bounded_replay_subject_value \<circ> digit_replay_subject_view"

definition finite_digit_replay_row_value :: "digit_replay_result_row \<Rightarrow> finite_factor_term" where
  "finite_digit_replay_row_value=(finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation (finite_collection_presentation finite_bounded_replay_value)))"

definition finite_digit_replay_prepared_value where
  "finite_digit_replay_prepared_value=(finite_pair_presentation finite_digit_replay_subject_value (finite_pair_presentation (finite_collection_presentation finite_bounded_replay_value) (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_collection_presentation finite_bounded_replay_value)))))"

definition finite_digit_replay_cause_value where
  "finite_digit_replay_cause_value=(finite_option_presentation (finite_pair_presentation finite_cause_subject_value (finite_pair_presentation finite_cause_report_value finite_boolean_data)))"

definition finite_digit_replay_assessed_row_value where
  "finite_digit_replay_assessed_row_value=(finite_pair_presentation (finite_collection_presentation finite_bounded_replay_value) (finite_pair_presentation (finite_collection_presentation finite_bounded_replay_value) (finite_collection_presentation (finite_pair_presentation finite_bounded_replay_value finite_digit_replay_cause_value))))"

definition finite_digit_replay_context_value where
  "finite_digit_replay_context_value=(finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_replay_subject_value))) (finite_pair_presentation finite_boolean_data (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_replay_prepared_value))) (finite_collection_presentation finite_digit_replay_row_value))))"

definition finite_digit_replay_assessment_value where
  "finite_digit_replay_assessment_value=(finite_pair_presentation (finite_collection_presentation finite_digit_replay_row_value) (finite_pair_presentation (finite_collection_presentation finite_digit_replay_row_value) (finite_pair_presentation finite_boolean_data (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_replay_assessed_row_value))))))"

definition finite_digit_replay_source_value where
  "finite_digit_replay_source_value=(finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_original_replay_input_value))) (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_bounded_replay_subject_value))) (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_replay_subject_value))) (finite_pair_presentation finite_natural_data finite_boolean_data)))))"

definition finite_digit_replay_seeds_value where
  "finite_digit_replay_seeds_value=(finite_pair_presentation finite_literal_seed_value (finite_pair_presentation (finite_option_presentation finite_decision_replay_value) finite_generation_problem_value))"

definition finite_digit_replay_previous_value where
  "finite_digit_replay_previous_value=(finite_pair_presentation (finite_sequence_presentation finite_literal_source_value) (finite_sequence_presentation finite_history_source_value))"

lemma finite_digit_replay_subject_value_exact:
  "finite_digit_replay_subject_value X=finite_digit_replay_subject_value Y \<longleftrightarrow>
    digit_replay_subject_view X=digit_replay_subject_view Y"
  by (simp add: finite_digit_replay_subject_value_def inj_eq[OF finite_bounded_replay_subject_value_injective])

section \<open>Original sources and actual inspections accompany the complete packet\<close>

definition digit_replay_presented_sources where
  "digit_replay_presented_sources table=map (\<lambda>(w,C,cells).
    let subjects=fst C; original=bounded_replay_case w
    in (w,digit_replay_original_inputs w,original,subjects,digit_replay_chain_length w,
      digit_replay_source_equal subjects original)) table"

definition digit_replay_presented_qualities where
  "digit_replay_presented_qualities=assessment_truth_rows digit_replay_family_inspect [0,1]"

definition digit_replay_report where
  "digit_replay_report ws selections=(let packet=digit_replay_packet ws selections in
    (digit_replay_indices,ws,
      (literal_replay_seed,required_history_seed_replays,digit_replay_initial_material_source),
      (digit_replay_literal_sources,digit_replay_history_sources),
      packet,digit_replay_presented_qualities (fst packet),digit_replay_source_scope ws,
      digit_replay_presented_sources (fst packet)))"

definition digit_replay_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "digit_replay_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_digit_replay_seeds_value (finite_pair_presentation finite_digit_replay_previous_value (finite_pair_presentation (finite_investigation_packet_value finite_digit_replay_context_value finite_digit_replay_assessment_value) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation finite_index_sequence_value (finite_sequence_presentation finite_digit_replay_source_value)))))))) (digit_replay_report ws selections)"


definition digit_replay_report_selections :: "nat list list" where
  "digit_replay_report_selections=[[],[0],[0,1]]"

export_code digit_replay_report_value checking SML

text \<open>
  The report keeps the full available scope and the requested scope, all literal
  and history seeds, all previous source families, the complete packet, actual
  candidate inspections and every original and projected source row. Source
  equality is computed from the actual packet context; the independent bounded
  inputs are retained separately. Digit stores are presented exactly through
  digit_allocated_view by the established subject-view operation.
\<close>

end
