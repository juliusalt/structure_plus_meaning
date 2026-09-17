theory Native_Graph_Presentation
 imports Finite_Presented_Native_Construction Finite_Term_Words
begin

definition native_graph_presented_report where
  "native_graph_presented_report ws selections=(let packet=native_graph_report_packet ws selections in
    (native_graph_indices,ws,packet,
      assessment_truth_rows (\<lambda>(result,A). native_graph_inspect A) [0..<6] (fst packet)))"

definition native_graph_report_value where
  "native_graph_report_value ws selections=finite_scoped_inspected_packet_value
    finite_native_graph_checked_subject_value finite_native_graph_cell_value (native_graph_presented_report ws selections)"

theorem native_graph_report_value_exact:
  "native_graph_report_value ws selections=native_graph_report_value vs choices \<longleftrightarrow>
    native_graph_presented_report ws selections=native_graph_presented_report vs choices"
  unfolding native_graph_report_value_def
  by (intro inj_eq finite_scoped_inspected_packet_value_injective
      finite_native_graph_checked_subject_value_injective finite_native_graph_cell_value_injective)

theorem native_graph_report_word_exact:
  "finite_term_shared_word (native_graph_report_value ws selections)=
    finite_term_shared_word (native_graph_report_value vs choices) \<longleftrightarrow>
    native_graph_presented_report ws selections=native_graph_presented_report vs choices"
  by (simp only: finite_term_shared_word_injective native_graph_report_value_exact)

definition native_graph_report_selections :: "nat list list" where
  "native_graph_report_selections=[[],[0,2,3,5],[0,1,2,3,4,5],[0,2,3,5,1],[0,1,2,4,5]]"

export_code native_graph_report_value checking SML
end
