theory Factor_Prepared_Replay_Assessments
  imports Factor_Prepared_Cause_Scope_Reports Factor_Shared_Replay_Construction Prepared_Assessment_Functions
    Factor_Digit_Replay_Investigation
begin

definition replay_assessment_with_reader where
  "replay_assessment_with_reader read_cause context m=(case context of (X,reference,variants) \<Rightarrow>
    let result=digit_replay_prepared m X variants
    in (result,reference,fimage (\<lambda>value. (value,read_cause value)) result))"

definition prepared_replay_assessor where
  "prepared_replay_assessor context=(case context of (X,reference,variants) \<Rightarrow>
    replay_assessment_with_reader (prepared_replay_cause_reader X) context)"

lemma prepared_replay_assessor_exact:
  "prepared_replay_assessor context m=digit_replay_assessment m context"
  by (cases "context")
    (simp add: prepared_replay_assessor_def prepared_replay_cause_reader_exact
      replay_assessment_with_reader_def digit_replay_assessment_def split: prod.splits)

definition family_assessment_with_prepared where
  "family_assessment_with_prepared covered reference prepared m=(let
    causes=fimage (\<lambda>(key,input). (key,map_option (\<lambda>assess. assess m) input)) prepared
    in (digit_replay_family_change m (digit_replay_assessed_results causes),reference,covered,causes))"

definition prepared_replay_family_assessor where
  "prepared_replay_family_assessor context=(case context of (subjects,covered,prepared,reference) \<Rightarrow>
    family_assessment_with_prepared covered reference
      (fimage (\<lambda>(key,input). (key,map_option prepared_replay_assessor input)) prepared))"

lemma prepared_replay_family_assessor_exact:
  "prepared_replay_family_assessor context m=digit_replay_family_assessment m context"
  by (cases "context")
    (simp add: prepared_replay_family_assessor_def family_assessment_with_prepared_def
      digit_replay_family_assessment_shared_code fimage_fimage option.map_comp comp_def
      case_prod_unfold prepared_replay_assessor_exact split: prod.splits)

definition prepared_replay_table where
  "prepared_replay_table ws=prepared_context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
    ws (\<lambda>w. digit_replay_family_context (digit_replay_case w)) prepared_replay_family_assessor"

lemma prepared_replay_table_exact:
  "prepared_replay_table ws=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
    ws (\<lambda>w. digit_replay_family_context (digit_replay_case w)) digit_replay_family_assessment"
  unfolding prepared_replay_table_def
  by (rule prepared_context_assessment_table_exact; rule prepared_replay_family_assessor_exact)

declare digit_replay_packet_def[code del]

lemma digit_replay_packet_prepared_causes_code [code]:
  "digit_replay_packet ws selections=(let table=prepared_replay_table ws;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
      [0,1] ws table digit_replay_family_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
      [0,1] (fst compared) (fst (snd compared))) selections))"
  by (simp only: digit_replay_packet_def prepared_replay_table_exact)

text \<open>The complete original context remains in every output row.
  Per-input preparation supplies the same actual assessment function to every
  candidate. Every original variant, mutation, optional position, cause row,
  family change, observation, comparison and revision remains in the packet.\<close>

end
