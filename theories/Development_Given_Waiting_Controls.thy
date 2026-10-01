theory Development_Given_Waiting_Controls
  imports Development_Given_Productions Development_Given_Modes Factor_Resolution_Checks
    Development_Given_Execution_Fixtures Native_Execution_Refinements
begin

text \<open>
  WC2's control (DECISIONS.md, task 495's entry, correction (16) of "Committed choice, for refusals"; task 914): #896's
  fixture of 55's pair clause (@{const c896_term}) at K2's check form (R5's committed search started at the root's
  focus) over the given's rooted readers, under the narrowed commitment of the given's input record at its frames,
  production bound the search's, at the moded selection with @{const given_modes} and at the waiting moded selection
  (@{const finite_waiting_moded_select_in} at the empty table, the record's own declarations and frames): the verdict
  and the states the search visits (O1's count, @{const committed_counted_search}, whose outcome is the committed
  search's). A thin theory no library theory imports, importing no evaluating theory.
\<close>

text \<open>As in the other execution theories, @{const finite_object_of} and @{const union_class} abort in code.\<close>

declare [[code abort: finite_object_of union_class]]

definition given_waiting_select ::
    "bool \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection" where
  "given_waiting_select w n = (let K = finite_narrowed_commitment finite_rooted_given_readers n given_input_declarations
      given_input_frames; Dm = resolution_declarations.truncate given_input_declarations in
    if w then finite_waiting_moded_select_in resolution_empty_table no_witness_construction K Dm given_input_frames
      given_modes finite_rooted_given_readers
    else finite_moded_select no_witness_construction K Dm given_modes finite_rooted_given_readers)"

definition given_waiting_row :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool option \<times> nat" where
  "given_waiting_row w k v n = (let t = c896_term k v; P = finite_rooted_given_readers;
      K = finite_narrowed_commitment P n given_input_declarations given_input_frames;
      S = committed_counted_search (given_waiting_select w n) no_witness_construction K P n (Some []) {||}
        (finite_initial_state 55 t) in
    (finite_resolution_verdict (finite_outcome_result P 55 t (fst S)), snd S))"

text \<open>A row's verdict is K2's check form at the selection (@{thm [source] committed_counted_search_outcome}).\<close>

lemma given_waiting_row_check:
  "fst (given_waiting_row w k v n) = finite_check_verdict_by (given_waiting_select w n) no_witness_construction
    (finite_narrowed_commitment finite_rooted_given_readers n given_input_declarations given_input_frames)
    finite_rooted_given_readers 55 (c896_term k v) n"
  by (simp add: given_waiting_row_def finite_check_verdict_by_def finite_check_resolution_by_def
    committed_counted_search_outcome Let_def)

text \<open>
  The rows, in one evaluation: at depth 1 the true call (variant 0) resolved and the calls with the first leaf (2) and
  the last leaf (1) changed refuted at bound 500, at the moded selection (@{term False}) and at the waiting moded
  selection (@{term True}), with the states each search visits; at depth 2 the call with its last leaf changed, which
  the moded selection leaves unresolved at 800 (4,166 states) and does not return at larger bounds, refuted at the
  waiting moded selection at 1500 in 3,211 states (4,785 before M2, task 998, which leaves 10 calling 0 alone beside
  its material premise: every row visits fewer states, 1,645, 1,709, 1,598, 1,737, 1,739 and 1,746 at depth 1 before),
  the same at 800: its search is exhausted below either bound. The
  other depth-2 rows (the moded selection's, the true call and the first leaf changed at both) cost more than a check
  carries at every rebuild: they stand in the task's measurement (`.build/tasks/914/measurement.md`, before M2): at depth 2 the
  true call resolved at 1500 in 4,437 states at the moded selection and 4,590 at the waiting moded selection, the call
  with its first leaf changed refuted in 3,987 (at 800) and 4,159 (at 1500). R4 (@{const finite_program_resolution})
  returns no verdict at depth 1 within 10 s at 500 (review 828's follow-up 6 found the same), so no R4 value stands
  beside these rows.
\<close>

lemma given_waiting_control:
  "map (\<lambda>(w,k,v,n). given_waiting_row w k v n)
     [(False,1,0,500),(True,1,0,500),(False,1,2,500),(True,1,2,500),(False,1,1,500),(True,1,1,500),(True,2,1,1500)] =
   [(Some True,981),(Some True,1045),(Some False,934),(Some False,1073),(Some False,1075),(Some False,1082),
    (Some False,3211)]"
  by eval

end
