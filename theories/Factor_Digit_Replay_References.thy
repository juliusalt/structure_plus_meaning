theory Factor_Digit_Replay_References
  imports Factor_Digit_Generation_Replay Factor_Literal_Replay_Cases Finite_Prepared_Results
begin

type_synonym digit_replay_subject = "digit_allocated_environment option\<times>finite_exact_target\<times>
  (local_address option definition_site\<times>finite_generation) list\<times>literal_replay_subject"
type_synonym bounded_replay_value = "((nat\<times>local_address option finite_artifact_environment)\<times>
  local_address option\<times>finite_generation\<times>local_address option finite_artifact_environment\<times>
  finite_exact_artifact) option"

definition record_replay_subject_with where
  "record_replay_subject_with construct q l rows X=(case X of (E,pu,pr,au,ar,root,R) \<Rightarrow>
    record_native_replay_with construct q l rows E pu pr au ar root R)"

lemma digit_replay_subject_projection:
  "map_option (\<lambda>(following,u,G,J,C). (digit_allocated_view following,u,G,J,C))
      (record_replay_subject_with digit_construct_generation q l rows X)=
    record_replay_subject_with finite_construct_bounded_generation (digit_allocated_view q) l rows X"
  by (cases X) (simp only: record_replay_subject_with_def case_prod_conv
    digit_record_native_replay_def[symmetric] digit_record_native_replay_projection)

definition digit_replay_relation :: "digit_replay_subject\<Rightarrow>bounded_replay_value\<Rightarrow>bool" where
  "digit_replay_relation X result=(case X of (input,l,rows,replay) \<Rightarrow>
    \<exists>q. input=Some q \<and> result=record_replay_subject_with finite_construct_bounded_generation
      (digit_allocated_view q) l rows replay)"

definition digit_replay_reference :: "digit_replay_subject\<Rightarrow>bounded_replay_value fset" where
  "digit_replay_reference X=(case X of (input,l,rows,replay) \<Rightarrow>
    finite_prepared_results (\<lambda>q. record_replay_subject_with finite_construct_bounded_generation
      (digit_allocated_view q) l rows replay) input)"

definition digit_replay_typed :: "digit_replay_subject\<Rightarrow>bounded_replay_value fset" where
  "digit_replay_typed X=(case X of (input,l,rows,replay) \<Rightarrow>
    finite_prepared_results (\<lambda>q. map_option
      (\<lambda>(following,u,G,J,C). (digit_allocated_view following,u,G,J,C))
        (record_replay_subject_with digit_construct_generation q l rows replay)) input)"

theorem digit_replay_reference_exact:
  "result |\<in>| digit_replay_reference X \<longleftrightarrow> digit_replay_relation X result"
  by (cases X) (simp only: digit_replay_reference_def digit_replay_relation_def
    case_prod_conv finite_prepared_results_exact)

theorem digit_replay_typed_exact:
  "digit_replay_typed X=digit_replay_reference X"
  by (cases X) (simp only: digit_replay_typed_def digit_replay_reference_def
    case_prod_conv digit_replay_subject_projection)

text \<open>
  Complete operation comparison retains the actual replay request, generation
  request, optional prepared state and complete optional result. An unavailable
  input has no result family; an available refused operation has the singleton
  absent result. The original bounded constructor and actual replay guard and
  quotation define the reference independently of the digit implementation.
\<close>

end
