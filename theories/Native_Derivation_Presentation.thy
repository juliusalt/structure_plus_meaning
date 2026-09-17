theory Native_Derivation_Presentation
 imports Finite_Presented_Native_Certificates Finite_Term_Words
begin

definition native_derivation_presented_report where
  "native_derivation_presented_report ws selections=(let packet=native_derivation_report_packet ws selections in
    (native_derivation_indices,ws,packet,assessment_truth_rows (\<lambda>cell. native_derivation_optional_inspect (map_option fst cell)) [0..<6] (map (\<lambda>(w,cells). (w,(),cells)) (fst (snd packet)))))"

definition native_derivation_report_value where
  "native_derivation_report_value ws selections=finite_scoped_report_value
    finite_native_derivation_packet_value (native_derivation_presented_report ws selections)"

theorem native_derivation_report_value_exact:
  "native_derivation_report_value ws selections=native_derivation_report_value vs choices \<longleftrightarrow>
    native_derivation_presented_report ws selections=native_derivation_presented_report vs choices"
  unfolding native_derivation_report_value_def
  by (intro inj_eq finite_scoped_report_value_injective finite_native_derivation_packet_value_injective)

theorem native_derivation_report_word_exact:
  "finite_term_shared_word (native_derivation_report_value ws selections)=
    finite_term_shared_word (native_derivation_report_value vs choices) \<longleftrightarrow>
    native_derivation_presented_report ws selections=native_derivation_presented_report vs choices"
  by (simp only: finite_term_shared_word_injective native_derivation_report_value_exact)

definition native_derivation_report_selections :: "nat list list" where
  "native_derivation_report_selections=[[],[0,2,5],[0,1,2,3,4,5],[5,3,4,2,1,0]]"

export_code native_derivation_report_value checking SML
end
