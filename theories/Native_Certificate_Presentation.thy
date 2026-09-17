theory Native_Certificate_Presentation
 imports Finite_Presented_Native_Certificates Finite_Term_Words
begin

definition native_certificate_presented_report where
  "native_certificate_presented_report ws selections=(let packet=native_certificate_report_packet ws selections in
    (native_certificate_indices,ws,packet,assessment_truth_rows (\<lambda>(result,A). native_certificate_inspect A) [0..<7] (map (\<lambda>(w,X,reference,cells). (w,(X,reference),cells)) (fst packet))))"

definition native_certificate_report_value where
  "native_certificate_report_value ws selections=finite_scoped_report_value
    finite_native_certificate_packet_value (native_certificate_presented_report ws selections)"

theorem native_certificate_report_value_exact:
  "native_certificate_report_value ws selections=native_certificate_report_value vs choices \<longleftrightarrow>
    native_certificate_presented_report ws selections=native_certificate_presented_report vs choices"
  unfolding native_certificate_report_value_def
  by (intro inj_eq finite_scoped_report_value_injective finite_native_certificate_packet_value_injective)

theorem native_certificate_report_word_exact:
  "finite_term_shared_word (native_certificate_report_value ws selections)=
    finite_term_shared_word (native_certificate_report_value vs choices) \<longleftrightarrow>
    native_certificate_presented_report ws selections=native_certificate_presented_report vs choices"
  by (simp only: finite_term_shared_word_injective native_certificate_report_value_exact)

definition native_certificate_report_selections :: "nat list list" where
  "native_certificate_report_selections=[[],[0,1,2,6],[0,1,2,3,4,5,6]]"

export_code native_certificate_report_value checking SML
end
