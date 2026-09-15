theory Factor_Digit_Replay_Reports
  imports Factor_Digit_Replay_References Factor_Certified_Cause_Assessment
begin

definition digit_replay_cause_subject ::
  "digit_replay_subject\<Rightarrow>bounded_replay_value\<Rightarrow>certified_cause_subject option" where
  "digit_replay_cause_subject X result=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    map_option (\<lambda>((n,A),u,G,J,C). (A,u,[],G,E,root,R)) result)"

definition digit_replay_cause_report where
  "digit_replay_cause_report X result=map_option (\<lambda>Y.
    (Y,certified_cause_report Y,certified_cause_method 0 Y)) (digit_replay_cause_subject X result)"

theorem digit_replay_cause_report_exact:
  "map_option (\<lambda>(Y,readings,certified). certified) (digit_replay_cause_report X result)=
    map_option certified_cause_holds (digit_replay_cause_subject X result)"
  by (simp add: digit_replay_cause_report_def option.map_comp comp_def certified_cause_original_exact)

text \<open>
  Each successful candidate value supplies its whole original cause subject.
  The existing reader computes generation presence, exact payload, every cause
  scope, minimal environment, package, application and replay reading. Its
  verdict retains the original certified-cause meaning independently of the
  particular complete replay operation being compared.
\<close>

end
