theory Use_Codec_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition use_codec_presented_report where
 "use_codec_presented_report ws selections=(let packet=use_codec_packet ws selections in
   (use_codec_indices,ws,packet,assessment_truth_rows use_codec_inspect [0..<4] (fst packet)))"

definition use_codec_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "use_codec_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_dual_comparison_packet_value finite_use_codec_subject_value finite_use_codec_report_value) finite_assessment_truth_value))) (use_codec_presented_report ws selections)"

definition use_codec_report_selections :: "nat list list" where
 "use_codec_report_selections=[[],[0],[0,1,2],[0,1,2,3]]"
export_code use_codec_report_value checking SML
end
