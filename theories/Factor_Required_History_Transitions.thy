theory Factor_Required_History_Transitions
  imports Factor_Required_History_Steps
begin

definition finite_required_history_attempt where
  "finite_required_history_attempt (q::finite_required_history_state) l rows E pu pr au ar root R=(
    case finite_record_native_replay (required_history_material q) l rows E pu pr au ar root R of
      None \<Rightarrow> None | Some (A,u,G,J,C) \<Rightarrow>
      if finite_certified_policy_cause (required_history_policy q) (required_history_policy_use q) []
        (required_history_entry q) A u [] G E root R then Some (A,u,G) else None)"

definition finite_required_history_append where
  "finite_required_history_append (q::finite_required_history_state) A u G=
    q\<lparr>required_history_material:=A,
      required_history_members:=((u,[]),G)#required_history_members q\<rparr>"

theorem finite_required_history_step_factored:
  "finite_required_history_step q l rows E pu pr au ar root R=(
    if list_all (\<lambda>row. row\<in>set (required_history_members q)) rows then
      map_option (\<lambda>(A,u,G). finite_required_history_append q A u G)
        (finite_required_history_attempt q l rows E pu pr au ar root R) else None)"
  by (auto simp: finite_required_history_step_def finite_required_history_attempt_def
    finite_required_history_append_def split: option.splits)

text \<open>
  This factors the already established transition at its first alternate
  membership implementation. The original replay and policy operation is
  unchanged. The complete state update retains the ordered ledger, including
  repetitions, independently of an auxiliary membership representation.
\<close>

end
