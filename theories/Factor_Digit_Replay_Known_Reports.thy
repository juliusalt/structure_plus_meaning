theory Factor_Digit_Replay_Known_Reports
  imports Factor_Digit_Replay_Reading_Sharing Factor_Known_Cause_Reports
begin

declare digit_replay_cause_report_shared_code[code del]

theorem digit_replay_cause_report_known_code [code]:
  "digit_replay_cause_report X result=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    map_option (\<lambda>Y. let readings=certified_cause_report_at_source pu pr au ar Y
      in (Y,readings,certified_cause_decide 0 readings)) (digit_replay_cause_subject X result))"
  by (cases X) (simp add: digit_replay_cause_report_shared_code certified_cause_report_at_source_exact)

end
