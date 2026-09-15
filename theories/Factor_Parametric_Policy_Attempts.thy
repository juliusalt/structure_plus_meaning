theory Factor_Parametric_Policy_Attempts
  imports Factor_Parametric_Generation_Replay Factor_Generation_History_Append Factor_History_State_Components
    Optional_Checked_Results
begin

definition policy_record_replay_with where
  "policy_record_replay_with read_material construct K ku entry H l rows E pu pr au ar root R=
    optional_checked_result (\<lambda>(A,u,G,J,C). finite_certified_policy_cause K ku [] entry
      (read_material A) u [] G E root R) (\<lambda>(A,u,G,J,C). (A,u,G))
      (record_native_replay_with construct H l rows E pu pr au ar root R)"

lemma policy_record_replay_with_result:
  "policy_record_replay_with read_material construct K ku entry H l rows E pu pr au ar root R=
      Some (A,u,G) \<longleftrightarrow>
    (\<exists>J C. record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C) \<and>
      finite_certified_policy_cause K ku [] entry (read_material A) u [] G E root R)"
  by (auto simp: policy_record_replay_with_def optional_checked_result_case split: option.splits prod.splits if_splits)

theorem original_history_attempt_instance:
  "policy_record_replay_with id finite_construct_generation_record
      (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
      (required_history_material q) l rows E pu pr au ar root R=
    finite_required_history_attempt q l rows E pu pr au ar root R"
  by (simp only: policy_record_replay_with_def optional_checked_result_case finite_required_history_attempt_def
    original_record_replay_instance id_apply case_prod_unfold)

theorem policy_record_replay_with_projection:
  assumes each: "\<And>q l p c rows. map_option (\<lambda>(following,u,G). (project following,u,G))
    (construct q l p c rows)=original (project q) l p c rows"
    and reads: "\<And>q. original_read (project q)=read_material q"
  shows "map_option (\<lambda>(A,u,G). (project A,u,G))
      (policy_record_replay_with read_material construct K ku entry H l rows E pu pr au ar root R)=
    policy_record_replay_with original_read original K ku entry (project H) l rows E pu pr au ar root R"
proof -
  have replay: "map_option (\<lambda>(A,u,G,J,C). (project A,u,G,J,C))
      (record_native_replay_with construct H l rows E pu pr au ar root R)=
    record_native_replay_with original (project H) l rows E pu pr au ar root R"
    by (rule record_native_replay_with_projection[where project=project
      and construct=construct and original=original]; rule each)
  show ?thesis unfolding policy_record_replay_with_def
    by (rule optional_checked_result_projection[where project="\<lambda>(A,u,G,J,C). (project A,u,G,J,C)"])
      (rule replay, auto simp: reads split: prod.splits)
qed

theorem policy_record_replay_append_valid:
  assumes backend: "generation_record_backend read_material construct"
    and previous: "finite_required_history_valid q"
    and material: "read_material H=required_history_material q"
    and result: "policy_record_replay_with read_material construct
      (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
      H l rows E pu pr au ar root R=Some (A,u,G)"
  shows "finite_required_history_valid (finite_required_history_append q (read_material A) u G)"
proof -
  obtain J C where replay: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
    and admitted: "finite_certified_policy_cause (required_history_policy q) (required_history_policy_use q) []
      (required_history_entry q) (read_material A) u [] G E root R"
    using result by (simp only: policy_record_replay_with_result; blast)
  have generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    using replay by (simp only: record_native_replay_with_result; blast)
  have formed: "finite_environment_formed (read_material A)"
    by (rule generation_record_backend.result_formed[OF backend generated])
  have included: "finite_environment_included (required_history_material q) (read_material A)"
    using generation_record_backend.result_included[OF backend generated] by (simp only: material)
  have generation: "finite_check_generation G (read_material A) u []"
    by (rule generation_record_backend.generation[OF backend generated])
  have payload: "generation_payload G=Finite_Whole R"
    by (simp add: generation_record_backend.core[OF backend generated] finite_generation_record_core_def)
  show ?thesis by (rule finite_required_history_append_valid[OF previous formed included generation payload admitted])
qed

text \<open>
  The actual replay and actual original policy checker determine the optional
  attempt. Projection retains both failures and the complete returned state,
  use and generation. History validity instantiates the established backend
  and original append contracts. Membership is a separate admission guard;
  this attempt alone does not establish historical reachability or a cost bound.
\<close>

end
