theory Digit_History_Presentation
  imports Finite_Presented_Histories Finite_Presented_Investigations Finite_Term_Words
    Factor_Digit_History_Investigation
begin

section \<open>A digit history is presented through its original view\<close>

lemma finite_history_member_injective [intro]: "inj finite_history_member_value"
  unfolding finite_history_member_value_def
  by (intro finite_pair_presentation_injective finite_site_data_injective finite_generation_value_injective
      finite_target_injective)

definition finite_history_view_value :: "digit_history_result \<Rightarrow> finite_factor_term" where
  "finite_history_view_value=finite_pair_presentation finite_natural_data
    (finite_pair_presentation finite_history_state_value (finite_collection_presentation finite_history_member_value))"

lemma finite_history_view_value_injective [intro]: "inj finite_history_view_value"
  unfolding finite_history_view_value_def
  by (intro finite_pair_presentation_injective finite_natural_data_injective finite_history_state_value_injective
      finite_collection_presentation_injective finite_history_member_injective)

definition finite_digit_history_value :: "digit_required_history \<Rightarrow> finite_factor_term" where
  "finite_digit_history_value q=finite_history_view_value (digit_history_view q)"

definition finite_digit_state_value :: "digit_required_history_state \<Rightarrow> finite_factor_term" where
  "finite_digit_state_value q=finite_history_view_value (digit_history_state_view q)"

definition finite_digit_subject_value :: "digit_history_subject \<Rightarrow> finite_factor_term" where
  "finite_digit_subject_value X=finite_pair_presentation finite_history_view_value finite_history_input_value
    (digit_history_subject_view X)"

definition finite_bounded_subject_value where
  "finite_bounded_subject_value X=finite_pair_presentation finite_history_view_value finite_history_input_value
    (bounded_history_subject_view X)"

lemma finite_history_view_identities:
  "finite_digit_history_value q=finite_digit_history_value r \<longleftrightarrow> digit_history_view q=digit_history_view r"
  "finite_digit_state_value s=finite_digit_state_value t \<longleftrightarrow> digit_history_state_view s=digit_history_state_view t"
  "finite_digit_subject_value X=finite_digit_subject_value Y \<longleftrightarrow>
    digit_history_subject_view X=digit_history_subject_view Y"
  "finite_bounded_subject_value Z=finite_bounded_subject_value W \<longleftrightarrow>
    bounded_history_subject_view Z=bounded_history_subject_view W"
  using finite_pair_presentation_injective[OF finite_history_view_value_injective finite_history_input_value_injective]
  by (simp_all add: finite_digit_history_value_def finite_digit_state_value_def finite_digit_subject_value_def
    finite_bounded_subject_value_def inj_eq[OF finite_history_view_value_injective] inj_eq)

section \<open>Rows, prepared operations, contexts and sources compose those views\<close>

definition finite_digit_result_row_value :: "digit_history_result_row \<Rightarrow> finite_factor_term" where
  "finite_digit_result_row_value=finite_pair_presentation (finite_option_presentation finite_history_certificate_value)
    (finite_option_presentation (finite_option_presentation finite_history_view_value))"

definition finite_digit_prepared_value where
  "finite_digit_prepared_value=finite_pair_presentation finite_digit_subject_value
    (finite_pair_presentation (finite_option_presentation finite_history_view_value)
    (finite_pair_presentation (finite_option_presentation finite_digit_state_value)
    (finite_pair_presentation (finite_option_presentation finite_history_view_value)
    (finite_pair_presentation (finite_option_presentation finite_digit_state_value)
    (finite_pair_presentation (finite_option_presentation finite_digit_state_value)
      (finite_option_presentation finite_digit_state_value))))))"

definition finite_digit_context_value where
  "finite_digit_context_value=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation
      (finite_collection_presentation (finite_pair_presentation
        (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_subject_value)))
      (finite_pair_presentation
        (finite_collection_presentation (finite_pair_presentation
          (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_digit_prepared_value)))
        (finite_collection_presentation finite_digit_result_row_value)))"

definition finite_digit_assessment_value where
  "finite_digit_assessment_value=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation (finite_collection_presentation finite_digit_result_row_value)
      (finite_collection_presentation finite_digit_result_row_value))"

definition digit_history_source_rows where
  "digit_history_source_rows ws=map (\<lambda>(w,old,original). (w,old,original,digit_history_chain_length w,
    digit_history_source_equal (digit_history_case w) original)) (digit_history_source_cases ws)"

definition finite_digit_source_value where
  "finite_digit_source_value=finite_pair_presentation finite_natural_data
    (finite_pair_presentation (finite_collection_presentation finite_history_subject_value)
      (finite_pair_presentation
        (finite_collection_presentation (finite_pair_presentation
          (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_bounded_subject_value)))
        (finite_pair_presentation finite_natural_data finite_boolean_data)))"

section \<open>A digit history report presents its scope, packet and source rows\<close>

definition digit_history_report where
  "digit_history_report packet ws selections=(ws,packet ws selections,digit_history_source_rows ws)"

definition digit_history_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "digit_history_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_investigation_packet_value finite_digit_context_value finite_digit_assessment_value)
      (finite_sequence_presentation finite_digit_source_value)) (digit_history_report digit_history_packet ws selections)"

definition digit_history_report_selections :: "nat list list" where
  "digit_history_report_selections=[[],[0],[0,1]]"

export_code digit_history_report_value checking SML

text \<open>
  A digit history, its stored state and its subjects are presented through the
  existing original views, so two stores are identified exactly when their
  original views agree; the store layout carries no identity of its own. The
  report keeps the requested scope, the complete packet, and for every source
  its original and bounded inputs, chain length and native source equality.
\<close>

end
