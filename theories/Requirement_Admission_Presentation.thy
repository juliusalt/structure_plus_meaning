theory Requirement_Admission_Presentation
  imports Finite_Presented_Native_Certificates Finite_Term_Words
    Factor_Native_Requirement_Sharing Factor_Native_Admission_Investigation Native_Admission_Execution_Base
begin

section \<open>Goal investigations specialize source readings, entry targets and partial results\<close>

definition finite_goal_source_report_value where
  "finite_goal_source_report_value=finite_pair_presentation finite_native_source_value
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation (finite_collection_presentation finite_call_value)
      (finite_pair_presentation finite_native_program_evaluation_value finite_admitted_terms_value)))"

lemma finite_goal_source_report_value_injective [intro]: "inj finite_goal_source_report_value"
  unfolding finite_goal_source_report_value_def
  by (intro finite_pair_presentation_injective finite_native_source_value_injective finite_boolean_data_injective
      finite_collection_presentation_injective finite_call_value_injective
      finite_native_program_evaluation_value_injective finite_admitted_terms_value_injective)

definition finite_native_entry_target_report_value where
  "finite_native_entry_target_report_value=finite_option_presentation (finite_pair_presentation finite_site_data
    (finite_pair_presentation finite_environment_presentation (finite_pair_presentation finite_use_data
      (finite_pair_presentation finite_native_source_value
        (finite_pair_presentation (finite_collection_presentation finite_call_value)
          (finite_pair_presentation finite_native_program_evaluation_value
            (finite_pair_presentation finite_admitted_terms_value finite_native_source_value)))))))"

lemma finite_native_entry_target_report_value_injective [intro]: "inj finite_native_entry_target_report_value"
  unfolding finite_native_entry_target_report_value_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective finite_site_data_injective
      finite_environment_presentation_injective finite_use_data_injective finite_native_source_value_injective
      finite_collection_presentation_injective finite_call_value_injective
      finite_native_program_evaluation_value_injective finite_admitted_terms_value_injective)

definition finite_goal_investigation_packet_value where
  "finite_goal_investigation_packet_value goals=finite_investigation_packet_value
    (finite_subject_report_value (finite_goal_problem_value goals) finite_goal_source_report_value
      finite_native_entry_target_report_value)
    (finite_option_presentation (finite_partial_result_assessment_value id))"

lemma finite_goal_investigation_packet_value_injective [intro]:
  "inj goals \<Longrightarrow> inj (finite_goal_investigation_packet_value goals)"
  unfolding finite_goal_investigation_packet_value_def
  by (intro finite_investigation_packet_value_injective finite_subject_report_value_injective
      finite_goal_problem_value_injective finite_goal_source_report_value_injective
      finite_native_entry_target_report_value_injective finite_option_presentation_injective
      finite_partial_result_assessment_value_injective inj_on_id)

section \<open>Complete requirement and admission investigations\<close>

definition native_requirement_presented_report where
  "native_requirement_presented_report ws selections=(let packet=native_requirement_shared_packet ws selections
    in (native_requirement_indices,ws,packet,
      assessment_truth_rows native_requirement_optional_inspect [0,1,2,3] (fst packet)))"

definition native_requirement_report_value where
  "native_requirement_report_value ws selections=finite_scoped_report_value
    (finite_goal_investigation_packet_value (finite_sequence_presentation (finite_goal_value finite_site_data)))
    (native_requirement_presented_report ws selections)"

definition native_requirement_report_selections :: "nat list list" where
  "native_requirement_report_selections=[[],[0],[0,3,2],[0,1,2,3]]"

definition native_admission_presented_report where
  "native_admission_presented_report ws selections=(let
      table=map (\<lambda>w. (w,native_admission_report w,map (\<lambda>m. (m,native_admission_assess m w)) [0,1,2,3,4,5])) ws;
      report=native_admission_investigation_report ws selections
    in (native_admission_indices,ws,(table,fst report,snd report),
      assessment_truth_rows native_admission_optional_inspect [0,1,2,3] table))"

definition native_admission_report_value where
  "native_admission_report_value ws selections=finite_scoped_report_value
    (finite_goal_investigation_packet_value (finite_goal_value finite_site_data))
    (native_admission_presented_report ws selections)"

definition native_admission_report_selections :: "nat list list" where
  "native_admission_report_selections=[[],[0],[0,1,2,3]]"

lemma requirement_admission_report_values_injective:
  "inj (finite_scoped_report_value
    (finite_goal_investigation_packet_value (finite_sequence_presentation (finite_goal_value finite_site_data))))"
  "inj (finite_scoped_report_value (finite_goal_investigation_packet_value (finite_goal_value finite_site_data)))"
  by (intro finite_scoped_report_value_injective finite_goal_investigation_packet_value_injective
      finite_sequence_presentation_injective finite_goal_value_injective finite_site_data_injective)+

theorem requirement_admission_report_words_exact:
  "finite_term_shared_word (native_requirement_report_value ws s)=
    finite_term_shared_word (native_requirement_report_value vs t) \<longleftrightarrow>
    native_requirement_presented_report ws s=native_requirement_presented_report vs t"
  "finite_term_shared_word (native_admission_report_value ws s)=
    finite_term_shared_word (native_admission_report_value vs t) \<longleftrightarrow>
    native_admission_presented_report ws s=native_admission_presented_report vs t"
  by (simp_all add: finite_term_shared_word_injective native_requirement_report_value_def
      native_admission_report_value_def inj_eq[OF requirement_admission_report_values_injective(1)]
      inj_eq[OF requirement_admission_report_values_injective(2)])

text \<open>
  A goal source reading keeps the source, requirement support, demand, evaluation
  and admitted requested terms. An entry target reading keeps the constructed
  site, environment and use with their source, demand, evaluation, admitted
  terms and the original source. The goal investigation packet specializes the
  investigation packet with subject reports of goal problems and optional
  partial result assessments of terms; requirement lists and single admission
  goals specialize its goal presentation. The presented reports keep the
  complete and executed scopes, every subject, source, target and assessment,
  the comparison, all revision cycles and every actual inspection.
\<close>

end
