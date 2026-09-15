theory Factor_Packet_Source_Projections
  imports Context_Source_Projections Factor_Digit_Replay_Investigation
    Factor_Constructed_History_Investigation
begin

definition replay_table_sources where
  "replay_table_sources table=context_source_rows (\<lambda>w context.
    (digit_replay_original_inputs w,replay_family_input_map digit_allocated_view (fst context))) table"

theorem replay_table_sources_exact:
  "replay_table_sources (fst (digit_replay_packet ws selections))=digit_replay_source_cases ws"
  unfolding replay_table_sources_def digit_replay_packet_def digit_replay_source_cases_def
  by (simp only: Let_def fst_conv; rule context_source_rows_exact)
    (simp add: digit_replay_family_context_def digit_replay_case_projection)

definition history_table_sources where
  "history_table_sources table=context_source_rows (\<lambda>w context.
    (required_history_case (digit_history_source_index w),
      fimage (\<lambda>(key,input). (key,map_option (history_subject_map digit_history_base) input))
        (fst (snd (fst context))))) table"

theorem history_table_sources_exact:
  "history_table_sources (fst (constructed_history_packet ws selections))=digit_history_source_cases ws"
  unfolding history_table_sources_def constructed_history_packet_def constructed_history.packet_def
    digit_history_source_cases_def
  by (simp only: Let_def fst_conv; rule context_source_rows_exact)
    (simp add: constructed_history.make_context_def digit_history_question_context_def
      digit_history_context_def digit_history_case_base_projection Let_def)

text \<open>Both source families retain every original initial source and the
  complete bounded input. Existing whole input projection contracts supply the
  latter from the actual subjects already stored in each packet. Neither theorem
  gives arbitrary supplied table cells an input correspondence claim.\<close>

end
