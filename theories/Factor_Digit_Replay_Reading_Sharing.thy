theory Factor_Digit_Replay_Reading_Sharing
  imports Factor_Digit_Replay_Reports
begin

declare digit_replay_cause_report_def[code del]

lemma digit_replay_cause_report_shared_code [code]:
  "digit_replay_cause_report X result=map_option (\<lambda>Y.
    let readings=certified_cause_report Y in (Y,readings,certified_cause_decide 0 readings))
      (digit_replay_cause_subject X result)"
  by (simp only: digit_replay_cause_report_def certified_cause_method_def Let_def)

text \<open>
  The original cause decision consumes the complete readings already retained
  in the report. The whole optional subject, readings and truth value are equal
  to the original operation; its semantic definition and all existing contracts
  remain applicable. This code equation makes no independent physical cost claim.
\<close>

end
