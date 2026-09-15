theory RRA_Digit_Generation_Cases
  imports RRA_Digit_Generation_Methods RRA_Generation_Input_Transitions
begin

definition digit_generation_source_problem :: "nat\<Rightarrow>generation_record_problem" where
  "digit_generation_source_problem w=generation_record_case (if w<16 then w else 1)"

definition digit_generation_chain_length :: "nat\<Rightarrow>nat" where
  "digit_generation_chain_length w=(if w=17 then 1 else if w=18 then 2 else if w=19 then 4 else if w=20 then 16 else 0)"

definition digit_generation_case :: "nat\<Rightarrow>digit_generation_subject" where
  "digit_generation_case w=(let initial=digit_initial_generation_input (digit_generation_source_problem w) in
    if w<16 then initial else if w<21 then digit_generation_chain (digit_generation_chain_length w) initial
    else digit_generation_reservations (w-20) initial)"

definition bounded_generation_case :: "nat\<Rightarrow>bounded_generation_subject" where
  "bounded_generation_case w=(let initial=bounded_initial_generation_input (digit_generation_source_problem w) in
    if w<16 then initial else if w<21 then bounded_generation_chain (digit_generation_chain_length w) initial
    else bounded_generation_reservations (w-20) initial)"

theorem digit_generation_case_projection:
  "generation_input_map digit_allocated_view (digit_generation_case w)=bounded_generation_case w"
  by (cases "w<16"; cases "w<21")
    (simp_all add: digit_generation_case_def bounded_generation_case_def
      digit_generation_chain_projection digit_generation_reservations_projection initial_generation_input_projection)

definition digit_generation_source_scope :: "nat list\<Rightarrow>nat list" where
  "digit_generation_source_scope ws=ws"

definition digit_generation_source_cases :: "nat list\<Rightarrow>(nat\<times>generation_record_problem\<times>bounded_generation_subject) list" where
  "digit_generation_source_cases ws=map (\<lambda>w. (w,digit_generation_source_problem w,bounded_generation_case w)) ws"

definition digit_generation_subject_view :: "digit_generation_subject\<Rightarrow>bounded_generation_subject" where
  "digit_generation_subject_view X=generation_input_map digit_allocated_view X"

definition digit_generation_source_equal :: "digit_generation_subject\<Rightarrow>bounded_generation_subject\<Rightarrow>bool" where
  "digit_generation_source_equal X original=(digit_generation_subject_view X=original)"

definition digit_generation_indices :: "nat list" where
  "digit_generation_indices=[0..<24]"

text \<open>
  The sixteen original construction problems remain the source of their
  complete initial inputs. Actual further constructions use the preceding
  returned store, use and generation through chains of zero, one, two, four
  and sixteen steps. Three additional subjects reserve one, two or three
  prefixes without growing their material. Every complete typed input equals
  the independently executed bounded reference input, for every case index.
\<close>

end
