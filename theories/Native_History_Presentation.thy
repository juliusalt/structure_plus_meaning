theory Native_History_Presentation
  imports Finite_Presented_Native_Certificates Finite_Term_Words Factor_Native_History_Reports
begin

section \<open>Native histories specialize evidenced results, witnessed histories and their reviews\<close>

definition finite_native_history_result_value :: "native_history_result \<Rightarrow> finite_factor_term" where
  "finite_native_history_result_value=finite_native_evidence_result_value
    (finite_witnessed_history_value (finite_collection_presentation finite_call_value) finite_native_application_value)"

definition finite_native_history_review_value where
  "finite_native_history_review_value=finite_option_presentation (finite_pair_presentation
    (finite_iteration_review_value (finite_collection_presentation finite_call_value))
    (finite_witness_review_value (finite_collection_presentation finite_call_value) finite_native_application_value))"

definition finite_native_history_cell_value where
  "finite_native_history_cell_value=finite_option_presentation (finite_pair_presentation
    (finite_evidence_assessment_value finite_call_value) finite_native_history_review_value)"

definition finite_native_history_packet_value where
  "finite_native_history_packet_value=finite_subject_assessment_packet_value
    (finite_subject_report_value finite_native_history_subject_value finite_native_history_reference_value
      finite_native_history_result_value)
    finite_native_history_cell_value"

lemma finite_native_history_values_injective [intro]:
  "inj finite_native_history_result_value" "inj finite_native_history_review_value"
  "inj finite_native_history_cell_value" "inj finite_native_history_packet_value"
proof -
  have calls: "inj (finite_collection_presentation finite_call_value)"
    by (intro finite_collection_presentation_injective finite_call_value_injective)
  show result: "inj finite_native_history_result_value"
    unfolding finite_native_history_result_value_def
    by (intro finite_native_evidence_result_value_injective finite_witnessed_history_value_injective calls
        finite_native_application_value_injective)
  show review: "inj finite_native_history_review_value"
    unfolding finite_native_history_review_value_def
    by (intro finite_option_presentation_injective finite_pair_presentation_injective
        finite_iteration_review_value_injective finite_witness_review_value_injective calls
        finite_native_application_value_injective)
  show cell: "inj finite_native_history_cell_value"
    unfolding finite_native_history_cell_value_def
    by (intro finite_option_presentation_injective finite_pair_presentation_injective
        finite_evidence_assessment_value_injective finite_call_value_injective review)
  show "inj finite_native_history_packet_value"
    unfolding finite_native_history_packet_value_def
    by (intro finite_subject_assessment_packet_value_injective finite_subject_report_value_injective
        finite_native_history_subject_value_injective finite_native_history_reference_value_injective result cell)
qed

section \<open>The complete native history investigation\<close>

definition native_history_presented_report where
  "native_history_presented_report ws selections=(let packet=native_history_report_packet ws selections in
    (native_history_indices,ws,packet,assessment_truth_rows (\<lambda>cell. native_history_optional_inspect (map_option fst cell))
      [0..<6] (map (\<lambda>(w,cells). (w,(),cells)) (fst (snd packet)))))"

definition native_history_report_value where
  "native_history_report_value ws selections=finite_scoped_report_value
    finite_native_history_packet_value (native_history_presented_report ws selections)"

theorem native_history_report_value_exact:
  "native_history_report_value ws selections=native_history_report_value vs choices \<longleftrightarrow>
    native_history_presented_report ws selections=native_history_presented_report vs choices"
  unfolding native_history_report_value_def
  by (intro inj_eq finite_scoped_report_value_injective finite_native_history_values_injective)

theorem native_history_report_word_exact:
  "finite_term_shared_word (native_history_report_value ws selections)=
    finite_term_shared_word (native_history_report_value vs choices) \<longleftrightarrow>
    native_history_presented_report ws selections=native_history_presented_report vs choices"
  by (simp only: finite_term_shared_word_injective native_history_report_value_exact)

definition native_history_report_selections :: "nat list list" where
  "native_history_report_selections=[[],[0,1,2,3],[0,1,2,3,4,5],[3,0,1,4,5,2]]"

text \<open>
  A native history result specializes an evidenced result whose evidence is the
  witnessed history of call states and native applications. Its review
  specializes the iteration review of call states and the witness review of
  applications, and each cell keeps the evidence assessment of calls with that
  review. The packet specializes the subject and assessment packet with the
  history problem, source reading and every candidate result. The presented report
  keeps the complete scope, the executed scope, the packet and the actual
  inspection of every cell.
\<close>

end
