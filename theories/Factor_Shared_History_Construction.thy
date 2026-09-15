theory Factor_Shared_History_Construction
  imports Factor_Nested_History_Identity History_Stage_Operations
begin

declare digit_policy_record_replay_def[code del]

lemma digit_policy_record_replay_constructed_code [code]:
  "digit_policy_record_replay K ku entry H l rows E pu pr au ar root R=
    digit_policy_record_from_source K ku entry H l rows E pu pr au ar root R"
  by (rule digit_policy_record_from_source_exact[symmetric])

lemma constructed_history_apply_exact:
  "constructed_history_apply X=digit_history_apply X"
  by (cases X; cases "snd X") (simp add: digit_history_constructed_step_exact)

declare digit_history_apply.simps[code del]
declare digit_history_reference_option.simps[code del]

lemma digit_history_apply_constructed_code [code]:
  "digit_history_apply X=constructed_history_apply X"
  by (rule constructed_history_apply_exact[symmetric])

lemma digit_history_reference_constructed_code [code]:
  "digit_history_reference_option X=constructed_history_result X"
  by (rule constructed_history_result_exact[symmetric])

declare digit_history_prepare_def[code del]

lemma digit_history_prepare_shared_code [code]:
  "digit_history_prepare X=(let typed=map_option raw_digit_required_history (constructed_history_apply X)
    in (X,map_option digit_history_state_view typed,typed,digit_history_legacy X,
      digit_history_unguarded X,digit_history_without_policy X,digit_history_without_replay X))"
  by (simp add: digit_history_prepare_def Let_def constructed_history_apply_exact
      option.map_comp comp_def digit_history_view_def[abs_def] digit_history_apply_exact[symmetric])

lemma known_predecessor_history_result_exact:
  "known_predecessor_history_result X=digit_history_reference_option X"
  by (simp only: known_predecessor_history_result_def known_history_apply_exact digit_history_apply_exact)

definition constructed_history_shared_context where
  "constructed_history_shared_context subjects=(let original=digit_history_question_context subjects;
    reference=snd (snd (snd original))
    in (original,[reference,reference,reference,
      digit_history_produced_family constructed_history_without_membership subjects]))"

lemma constructed_history_shared_context_exact:
  "constructed_history_shared_context subjects=constructed_history.make_context subjects"
proof -
  have constructed: "constructed_history_result=digit_history_reference_option"
    by (rule ext; rule constructed_history_result_exact)
  have known: "known_predecessor_history_result=digit_history_reference_option"
    by (rule ext; rule known_predecessor_history_result_exact)
  have quoted: "quoted_history_result=digit_history_reference_option"
    by (rule ext; rule quoted_history_result_exact)
  show ?thesis by (simp add: constructed_history_shared_context_def constructed_history.make_context_def
      constructed_history.additional_results_def digit_history_question_context_def
      digit_history_result_candidates.make_context_def digit_history_result_candidates.additional_results_def
      digit_history_context_def digit_history_prepared_reference_exact Let_def
      digit_history_produced_family_def digit_history_family_reference_def
      constructed known quoted)
qed

declare constructed_history_packet_def[code del]

lemma constructed_history_packet_shared_code [code]:
  "constructed_history_packet ws selections=(let table=context_assessment_table constructed_history.methods ws
      (\<lambda>w. constructed_history_shared_context (digit_history_case w)) constructed_history.assessment;
    compared=context_assessment_investigation constructed_history.methods [0,1] ws table digit_history_question_inspect
    in (table,compared,map (investigation_cycle_report constructed_history.methods [0,1]
      (fst compared) (fst (snd compared))) selections))"
  by (simp only: constructed_history_packet_def constructed_history.packet_def
      constructed_history_shared_context_exact)

declare history_stage_context_def[code del]

lemma history_stage_context_shared_code [code]:
  "history_stage_context subjects=constructed_history_shared_context subjects"
  by (simp only: history_stage_context_def constructed_history_shared_context_exact)

text \<open>The existing closed-history refinement supplies the complete
  original result under its actual invariant and membership guard. Its typed
  and original views are computed together. Three separately established
  equal producers reuse that complete reference family. The actual omitted
  membership producer, all nineteen original methods, all original fields,
  ordered ledgers, cache relations and observation conditions remain.\<close>

end
