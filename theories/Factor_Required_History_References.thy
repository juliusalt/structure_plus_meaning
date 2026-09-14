theory Factor_Required_History_References
  imports Factor_Required_History_Projection Finite_Relation_Reader_Assessments
begin

datatype required_history_input = History_Step finite_exact_target
  "(local_address option definition_site\<times>finite_generation) list"
  "local_address option finite_artifact_environment" "local_address option" local_address
  "local_address option" local_address "local_address option definition_site" finite_exact_artifact

type_synonym required_history_subject = "required_history\<times>required_history_input"

fun required_history_transition where
  "required_history_transition (q,History_Step l rows E pu pr au ar root R) following=(
    let previous=raw_required_history q in
    set rows\<subseteq>set (required_history_members previous) \<and>
    (\<exists>A u G J C. finite_record_native_replay (required_history_material previous)
      l rows E pu pr au ar root R=Some (A,u,G,J,C) \<and>
      certified_policy_cause_at (decode_finite_environment (required_history_policy previous))
        (required_history_policy_use previous) [] (required_history_entry previous)
        (decode_finite_environment A) u [] (decode_finite_generation G)
        (decode_finite_environment E) root (decode_finite_object R) \<and>
      following=previous\<lparr>required_history_material:=A,
        required_history_members:=((u,[]),G)#required_history_members previous\<rparr>))"

fun required_history_reference_option where
  "required_history_reference_option (q,History_Step l rows E pu pr au ar root R)=
    finite_required_history_step (raw_required_history q) l rows E pu pr au ar root R"

theorem required_history_reference_exact:
  "required_history_reference_option X=Some following \<longleftrightarrow> required_history_transition X following"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  show ?thesis by (cases input)
    (auto simp: shape finite_required_history_step_result finite_certified_policy_cause_exact
      list_all_iff Let_def)
qed

text \<open>
  The transition requires actual predecessor membership, the existing joined
  replay constructor, the original semantic policy-cause relation, and exact
  equality of every resulting state field. The constructor's established
  contract supplies record formation, actual readings and preservation. This
  does not identify the invariant with complete historical permission.
\<close>

end
