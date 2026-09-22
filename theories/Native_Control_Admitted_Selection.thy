theory Native_Control_Admitted_Selection
  imports Native_Control_Finite_Guard
begin

section \<open>The two previous native decisions gate the actual source request\<close>

definition judgment_artifact_choice where
  "judgment_artifact_choice report=keyed_admitted_choice (first_occurrence_key judgment_artifact_candidates)
    judgment_artifact_candidates (judgment_artifact_execution_question ()) report"

definition guard_representation_choice where
  "guard_representation_choice report=keyed_admitted_choice (first_occurrence_key guard_representation_candidates)
    guard_representation_candidates (guard_representation_execution_question ()) report"

lemma judgment_artifact_choice_condition:
  assumes chosen: "judgment_artifact_choice report=Some a"
  shows "judgment_artifact_agreement a judgment_artifact_cases"
proof -
  have "judgment_artifact_observation a judgment_artifact_cases"
    by (rule keyed_admitted_choice_condition[OF first_occurrence_key_inj_on
      chosen[unfolded judgment_artifact_choice_def judgment_artifact_execution_question_def
        judgment_artifact_question_def keyed_development_question_def]]) simp
  then show ?thesis by (simp only: judgment_artifact_observation_exact)
qed

lemma guard_representation_choice_condition:
  assumes chosen: "guard_representation_choice report=Some m"
  shows "guard_representation_condition m checked_judgment_rows"
proof -
  have "guard_representation_observation m checked_judgment_rows"
    by (rule keyed_admitted_choice_condition[OF first_occurrence_key_inj_on
      chosen[unfolded guard_representation_choice_def guard_representation_execution_question_def
        guard_representation_question_def keyed_development_question_def]]) simp
  then show ?thesis by (simp only: guard_representation_observation_exact)
qed

definition admitted_guard_requests where
  "admitted_guard_requests body adapter target=(if
    judgment_artifact_choice adapter=Some Complete_Artifact_Body \<and>
    guard_representation_choice target=Some Complete_Guard_Target
    then judgment_bridge_install body else None)"

theorem admitted_guard_requests_fields:
  assumes requested: "admitted_guard_requests body adapter target=Some rows"
    and member: "(i,Some (d,E,u))\<in>set rows"
  shows "judgment_bridge_install body=Some rows"
    and "judgment_artifact_choice adapter=Some Complete_Artifact_Body"
    and "guard_representation_choice target=Some Complete_Guard_Target"
    and "judgment_artifact_agreement Complete_Artifact_Body judgment_artifact_cases"
    and "guard_representation_condition Complete_Guard_Target checked_judgment_rows"
  using requested unfolding admitted_guard_requests_def
  by (auto split: if_splits intro: judgment_artifact_choice_condition guard_representation_choice_condition)

lemma admitted_guard_requests_original_source:
  assumes requested: "admitted_guard_requests body adapter target=Some rows"
    and member: "(i,Some (d,E,u))\<in>set rows"
  obtains Q accepted where "judgment_bridge_question ()=Some Q"
    "native_development_admission Q body=Some accepted"
    "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates (judgment_bridge_candidates!i))\<in>set accepted"
    "judgment_bridge_source (judgment_bridge_candidates!i)=Some (d,E,u)"
  by (rule judgment_bridge_install_fields[OF admitted_guard_requests_fields(1)[OF requested member] member])
    (rule that; assumption)

text \<open>No producer identifier or retained host-selected index is an input to
  this consumer. Each returned subject passes its original native question and
  admission. Empty or distinct-value ambiguity is refused. The body request is
  still the actual original judgment installation, not a substitute package.
  This gate does not by itself build the complete artifact guard or confer
  governing policy authority.\<close>

end
