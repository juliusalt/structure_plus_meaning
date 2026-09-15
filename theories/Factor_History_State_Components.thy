theory Factor_History_State_Components
  imports Factor_Required_History_Transitions
begin

record finite_required_history_header =
  history_header_source :: "local_address option finite_artifact_environment"
  history_header_source_use :: "local_address option"
  history_header_source_root :: local_address
  history_header_goals :: "local_address option definition_site admission_goal list"
  history_header_entry :: "local_address option definition_site"
  history_header_policy :: "local_address option finite_artifact_environment"
  history_header_policy_use :: "local_address option"

definition finite_history_header :: "finite_required_history_state\<Rightarrow>finite_required_history_header" where
  "finite_history_header q=\<lparr>history_header_source=required_history_source q,
    history_header_source_use=required_history_source_use q,history_header_source_root=required_history_source_root q,
    history_header_goals=required_history_goals q,history_header_entry=required_history_entry q,
    history_header_policy=required_history_policy q,history_header_policy_use=required_history_policy_use q\<rparr>"

definition finite_history_with :: "finite_required_history_header\<Rightarrow>
  local_address option finite_artifact_environment\<Rightarrow>
  (local_address option definition_site\<times>finite_generation) list\<Rightarrow>finite_required_history_state" where
  "finite_history_with h material members=\<lparr>required_history_source=history_header_source h,
    required_history_source_use=history_header_source_use h,required_history_source_root=history_header_source_root h,
    required_history_goals=history_header_goals h,required_history_entry=history_header_entry h,
    required_history_policy=history_header_policy h,required_history_policy_use=history_header_policy_use h,
    required_history_material=material,required_history_members=members\<rparr>"

theorem finite_history_components_recover:
  "finite_history_with (finite_history_header q) (required_history_material q) (required_history_members q)=q"
  by (cases q) (simp add: finite_history_with_def finite_history_header_def)

lemma finite_history_with_components:
  "finite_history_header (finite_history_with h material members)=h"
  "required_history_material (finite_history_with h material members)=material"
  "required_history_members (finite_history_with h material members)=members"
  by (cases h; simp add: finite_history_with_def finite_history_header_def)+

theorem finite_history_append_components:
  "finite_required_history_append (finite_history_with h material members) A u G=
    finite_history_with h A (((u,[]),G)#members)"
  by (simp add: finite_required_history_append_def finite_history_with_def)

text \<open>
  Fixed source, requirement and policy fields form one header. Material and the
  ordered member ledger remain independent components. Both reconstruction
  directions preserve the entire original state, and append changes exactly
  the material and ordered ledger. The decomposition alone supplies no validity
  or permission judgment and stores no second primitive material environment.
\<close>

end
