theory Factor_Primary_Computed_Cause_Execution
  imports Factor_Computed_Replay_Causes
begin

declare prepared_replay_assessor_def[code del]

lemma primary_computed_replay_assessor_code [code]:
  "prepared_replay_assessor context=computed_replay_assessor 1 context"
  by (rule computed_replay_assessor_exact[symmetric])

end
