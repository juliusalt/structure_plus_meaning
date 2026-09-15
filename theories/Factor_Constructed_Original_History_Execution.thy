theory Factor_Constructed_Original_History_Execution
  imports Factor_Known_Replay_Policy Factor_Digit_History_Cases
begin

declare finite_required_history_attempt_def[code del]

lemma finite_required_history_attempt_constructed_code [code]:
  "finite_required_history_attempt q l rows E pu pr au ar root R=
    policy_record_replay_from_source finite_construct_generation_record
      (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
      (required_history_material q) l rows E pu pr au ar root R"
  unfolding original_history_attempt_instance[symmetric]
  by (rule generation_record_backend.policy_record_replay_from_source_exact[
      OF original_generation_backend.generation_record_backend_axioms, symmetric])

declare finite_required_history_step_def[code del]

lemma original_history_step_over_extensions:
  "finite_required_history_step q l rows E pu pr au ar root R=(
    if list_all (\<lambda>row. row\<in>set (required_history_members q)) rows then
      map_option (\<lambda>(A,u,G). q\<lparr>required_history_material:=A,
        required_history_members:=((u,[]),G)#required_history_members q\<rparr>)
        (policy_record_replay_with id finite_construct_generation_record
          (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
          (required_history_material q) l rows E pu pr au ar root R)
    else None)"
  by (auto simp: finite_required_history_step_def policy_record_replay_with_def
      optional_checked_result_case original_record_replay_instance
      split: option.splits prod.splits if_splits)

lemma finite_required_history_step_constructed_code [code]:
  "finite_required_history_step q l rows E pu pr au ar root R=(
    if list_all (\<lambda>row. row\<in>set (required_history_members q)) rows then
      map_option (\<lambda>(A,u,G). q\<lparr>required_history_material:=A,
        required_history_members:=((u,[]),G)#required_history_members q\<rparr>)
        (policy_record_replay_from_source finite_construct_generation_record
          (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
          (required_history_material q) l rows E pu pr au ar root R)
    else None)"
  by (simp only: original_history_step_over_extensions
      generation_record_backend.policy_record_replay_from_source_exact[
        OF original_generation_backend.generation_record_backend_axioms])

declare bounded_history_case_def[code del]

lemma bounded_history_case_projection_code [code]:
  "bounded_history_case w=fimage (\<lambda>(key,input).
    (key,map_option (history_subject_map digit_history_base) input)) (digit_history_case w)"
  by (rule digit_history_case_base_projection[symmetric])

text \<open>The original allocator instantiates the established policy
  construction equation with its own proved backend. Original membership and
  ordered append remain the factored transition. The existing complete chain
  projection computes the original bounded case for every index. These code
  equations preserve the independently stated original operations and every
  refusal; they do not supply source-equality verdicts from a host table.\<close>

end
