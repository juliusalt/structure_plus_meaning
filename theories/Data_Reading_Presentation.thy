theory Data_Reading_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition data_reading_presented_report where
 "data_reading_presented_report ws selections=(let fixture=data_reading_fixture_packet in
   (fixture,data_reading_indices,ws,map_option (\<lambda>source.
     let packet=data_reading_packet source ws selections in
       (source,finite_complete_data_readings_prepared source [],packet,
         assessment_truth_rows data_reading_inspect [0,1] (fst packet))) (snd fixture)))"

definition data_reading_report_value where
 "data_reading_report_value ws selections=(finite_pair_presentation (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation finite_history_certificate_value (finite_option_presentation finite_artifact_term))) (finite_option_presentation finite_artifact_term)) (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_option_presentation (finite_pair_presentation finite_artifact_term (finite_pair_presentation (finite_collection_presentation id) (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation (finite_pair_presentation finite_artifact_term Finite_Payload) id) (finite_reader_assessment_presentation id)) finite_assessment_truth_value))))))) (data_reading_presented_report ws selections)"

definition data_reading_report_selections :: "nat list list" where
 "data_reading_report_selections=[[],[0],[0,1]]"
export_code data_reading_report_value checking SML
end
