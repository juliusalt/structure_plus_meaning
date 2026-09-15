theory Optional_Checked_Results
  imports Optional_Transition_Sequences
begin

definition optional_checked_result where
  "optional_checked_result check extract input=Option.bind input
    (\<lambda>value. if check value then Some (extract value) else None)"

lemma optional_checked_result_case:
  "optional_checked_result check extract input=(case input of None \<Rightarrow> None
    | Some value \<Rightarrow> if check value then Some (extract value) else None)"
  by (cases input) (simp_all add: optional_checked_result_def)

theorem optional_checked_result_projection:
  assumes initial: "map_option project input=original_input"
    and checks: "\<And>value. original_check (project value)=check value"
    and results: "\<And>value. original_extract (project value)=result_project (extract value)"
  shows "map_option result_project (optional_checked_result check extract input)=
    optional_checked_result original_check original_extract original_input"
  unfolding optional_checked_result_def
  by (rule optional_bind_projection[where project=project])
    (rule initial, simp add: checks results split: if_splits)

text \<open>
  An actual check filters each available result before its selected fields are
  returned. Exact input projection, the actual check equation and the complete
  result-field equation compose through the existing optional bind contract.
  Neither an unavailable value nor a failed check supplies a result.
\<close>

end
