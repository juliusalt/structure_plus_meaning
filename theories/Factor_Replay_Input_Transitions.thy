theory Factor_Replay_Input_Transitions
  imports Factor_Digit_Replay_Families RRA_Digit_Environment_Loading Optional_State_Requests
begin

type_synonym 'a replay_record_input = "'a option\<times>finite_exact_target\<times>
  (local_address option definition_site\<times>finite_generation) list\<times>literal_replay_subject"
type_synonym bounded_replay_subject =
  "(nat\<times>local_address option finite_artifact_environment) replay_record_input"
type_synonym original_replay_input = "local_address option finite_artifact_environment\<times>
  finite_exact_target\<times>(local_address option definition_site\<times>finite_generation) list\<times>literal_replay_subject"

definition digit_replay_load :: "original_replay_input\<Rightarrow>digit_replay_subject" where
  "digit_replay_load X=(load_digit_environment (fst X),snd X)"

definition bounded_replay_load :: "original_replay_input\<Rightarrow>bounded_replay_subject" where
  "bounded_replay_load X=(if finite_environment_formed (fst X) then
    Some (finite_compact_use_head (finite_environment_uses (fst X)) None,fst X) else None,snd X)"

lemma replay_initial_input_projection:
  "optional_request_map digit_allocated_view (digit_replay_load X)=bounded_replay_load X"
  by (simp add: optional_request_map_def digit_replay_load_def bounded_replay_load_def load_digit_environment_exact)

lemma replay_initial_requests:
  "snd (digit_replay_load X)=snd X"
  "snd (bounded_replay_load X)=snd X"
  by (simp_all only: digit_replay_load_def bounded_replay_load_def snd_conv)

definition replay_following_input ::
  "('a\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>
      (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
      ('a\<times>local_address option\<times>finite_generation) option)\<Rightarrow>
    'a replay_record_input\<Rightarrow>'a replay_record_input" where
  "replay_following_input construct=optional_request_follow
    (\<lambda>q (l,rows,replay). record_replay_subject_with construct q l rows replay)
    (\<lambda>(l,rows,replay) (u,G,J,C). (l,[((u,[]),G)],replay))"

lemma replay_result_first_projection:
  "map_option (\<lambda>(following,result). (digit_allocated_view following,result))
      (record_replay_subject_with digit_construct_generation q l rows X)=
    record_replay_subject_with finite_construct_bounded_generation (digit_allocated_view q) l rows X"
  using digit_replay_subject_projection[of q l rows X]
  by (simp only: case_prod_unfold prod.collapse)

lemma replay_following_input_projection:
  "optional_request_map digit_allocated_view (replay_following_input digit_construct_generation X)=
    replay_following_input finite_construct_bounded_generation (optional_request_map digit_allocated_view X)"
  unfolding replay_following_input_def
  by (rule optional_request_follow_projection)
    (simp only: case_prod_unfold fst_conv snd_conv replay_result_first_projection[unfolded case_prod_unfold])

definition replay_input_chain where
  "replay_input_chain construct n X=(replay_following_input construct ^^ n) X"

theorem replay_input_chain_projection:
  "optional_request_map digit_allocated_view (replay_input_chain digit_construct_generation n X)=
    replay_input_chain finite_construct_bounded_generation n (optional_request_map digit_allocated_view X)"
  unfolding replay_input_chain_def
  by (rule function_iteration_projection; rule replay_following_input_projection)

text \<open>
  The first input retains the complete original environment and loading bound.
  Each next request cites the preceding actual returned generation and site.
  Complete projection instantiates generic optional state/request transitions
  and arbitrary iteration, preserving failure and every original replay field.
\<close>

end
