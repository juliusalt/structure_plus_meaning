theory Factor_Digit_Replay_Cases
  imports Factor_Replay_Input_Transitions Factor_Required_History_Cases RRA_Finite_Generation_Record_Cases
begin

fun replay_history_original_input :: "required_history_subject\<Rightarrow>original_replay_input" where
  "replay_history_original_input (q,History_Step l rows E pu pr au ar root R)=
    (required_history_material (raw_required_history q),l,rows,E,pu,pr,au,ar,root,R)"

definition replay_literal_original_inputs where
  "replay_literal_original_inputs w=fimage (\<lambda>(key,input). (Some key,
    map_option (\<lambda>replay. (fst (generation_record_case 1),Finite_Whole (finite_payload_syntax [60]),[],replay)) input))
      (literal_replay_family literal_replay_seed w)"

definition replay_history_original_inputs where
  "replay_history_original_inputs w=fimage (\<lambda>(key,input).
    (key,map_option replay_history_original_input input)) (required_history_case w)"

definition digit_replay_original_inputs where
  "digit_replay_original_inputs (w::nat)=(if w<7 then replay_literal_original_inputs w
    else if w<19 then replay_history_original_inputs (w-7)
    else if w<23 then replay_history_original_inputs 0 else replay_literal_original_inputs 0)"

definition digit_replay_chain_length :: "nat\<Rightarrow>nat" where
  "digit_replay_chain_length w=(if w=19 then 1 else if w=20 then 2 else if w=21 then 4 else if w=22 then 8 else 0)"

definition replay_family_input_map where
  "replay_family_input_map project inputs=fimage (\<lambda>(key,input).
    (key,map_option (optional_request_map project) input)) inputs"

definition replay_case_finish where
  "replay_case_finish construct (w::nat) inputs=(if w<19 then inputs
    else if w<23 then fimage (\<lambda>(key,input).
      (key,map_option (replay_input_chain construct (digit_replay_chain_length w)) input)) inputs
    else fimage (\<lambda>(key,input). (key,map_option (\<lambda>X. (None,snd X)) input)) inputs)"

definition digit_replay_case ::
  "nat\<Rightarrow>(required_history_certificate option\<times>digit_replay_subject option) fset" where
  "digit_replay_case w=replay_case_finish digit_construct_generation w
    (fimage (\<lambda>(key,input). (key,map_option digit_replay_load input)) (digit_replay_original_inputs w))"

definition bounded_replay_case ::
  "nat\<Rightarrow>(required_history_certificate option\<times>bounded_replay_subject option) fset" where
  "bounded_replay_case w=replay_case_finish finite_construct_bounded_generation w
    (fimage (\<lambda>(key,input). (key,map_option bounded_replay_load input)) (digit_replay_original_inputs w))"

theorem digit_replay_case_projection:
  "replay_family_input_map digit_allocated_view (digit_replay_case w)=bounded_replay_case w"
  by (cases "w<19"; cases "w<23")
    (simp_all add: replay_family_input_map_def digit_replay_case_def bounded_replay_case_def replay_case_finish_def
      fimage_fimage option.map_comp comp_def case_prod_unfold replay_initial_input_projection
      replay_input_chain_projection optional_request_map_unavailable replay_initial_requests)

definition digit_replay_subject_view :: "digit_replay_subject\<Rightarrow>bounded_replay_subject" where
  "digit_replay_subject_view=optional_request_map digit_allocated_view"

definition digit_replay_source_equal ::
  "(required_history_certificate option\<times>digit_replay_subject option) fset\<Rightarrow>
    (required_history_certificate option\<times>bounded_replay_subject option) fset\<Rightarrow>bool" where
  "digit_replay_source_equal subjects original=(replay_family_input_map digit_allocated_view subjects=original)"

definition digit_replay_source_scope :: "nat list\<Rightarrow>nat list" where
  "digit_replay_source_scope ws=ws"

definition digit_replay_source_cases where
  "digit_replay_source_cases ws=map (\<lambda>w. (w,digit_replay_original_inputs w,bounded_replay_case w)) ws"

definition digit_replay_initial_material_source where
  "digit_replay_initial_material_source=generation_record_case 1"

definition digit_replay_literal_sources where
  "digit_replay_literal_sources=map (\<lambda>w. (w,literal_replay_family literal_replay_seed w)) [0..<7]"

definition digit_replay_history_sources where
  "digit_replay_history_sources=map (\<lambda>w. (w,required_history_case w)) [0..<12]"

definition digit_replay_indices :: "nat list" where
  "digit_replay_indices=[0..<24]"

text \<open>
  All seven original literal replay variants and all twelve original required
  history requests supply complete sources. The literal cases retain unrelated
  original generation material. History inputs retain the actual old generations
  and predecessor rows, including readable material absent from the ledger;
  replay recording does not itself impose that separate membership condition.
  Further inputs use one, two, four and eight actual returned replays, and one
  case makes the digit state unavailable. Every complete typed input projects
  to the independently executed bounded input for every index.
\<close>

end
