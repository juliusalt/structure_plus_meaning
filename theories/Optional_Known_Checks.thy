theory Optional_Known_Checks
  imports Optional_Checked_Results
begin

theorem optional_checked_result_known_check:
  assumes every: "\<And>value. input=Some value \<Longrightarrow> check value=known"
  shows "optional_checked_result check extract input=(if known then map_option extract input else None)"
  by (cases input) (simp_all add: optional_checked_result_case every)

text \<open>
  A check can be moved before an optional operation only when its actual result
  contract establishes the same condition for every possible successful value.
  Refusal and the complete extracted result remain unchanged. The condition is
  not supplied by an unproved flag or an expected observation table.
\<close>

end
