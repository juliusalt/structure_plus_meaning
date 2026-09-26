theory Development_First_Problem_Execution
  imports Development_First_Problem Development_Native_State_Execution Development_Recording_Refinements
    Native_Execution_Refinements
begin

section \<open>The posing's construction, compiled where it is called\<close>

text \<open>
  Task 397: the posing of the native loop's first problem (@{const development_first_problem_posing}) executed with
  the recording's refinement collection and the export boundary's refinements in effect. The posing is reported with
  its seconds, its payload's addresses, the carrier addresses of its cause and whether its cause is the owner record
  of 18:53's; a posing that returns no generation, or whose cause is another, is refused. That behaviour is
  @{text Native_State_Execution.recording} (@{text Development_Native_State_Execution}) at the recording that cites the
  owner record: @{text First_Problem_Execution.posing} states it over the compiled code its caller supplies. The posing
  is compiled and evaluated where it is called, in the held measurement: the caller compiles, in one @{text ML} block,
  @{const development_owner_record_1853}, @{const development_citing_generation}, @{const native_state_report} and
  @{const development_first_problem_payload}, and passes them to @{text posing}. Making the payload (1,882,537
  addresses, the asked installation's environment and the given's) was 16.8 s of the 23.5 s this theory's code took
  at every load (task 562), for a posing no load calls.

  At every load the five owner records are recorded and read back (moved from @{text Development_Owner_Records}), each
  timed, and a record that does not read back refuses the theory: the one control of the owner records' recording
  (task 562 moved @{text Development_Native_State_Execution}'s owner record here). No library theory imports this one.
\<close>

definition first_problem_owner_directions :: "finite_factor_term list" where
  "first_problem_owner_directions=[development_owner_direction_1750,development_owner_direction_1812,
    development_owner_direction_1836,development_owner_direction_1853,development_owner_direction_1957]"

definition first_problem_owner_record_read_back :: "finite_factor_term \<Rightarrow> bool option" where
  "first_problem_owner_record_read_back t=development_owner_record_read_back t (development_owner_record t)"


lemma first_problem_posing_recording:
  "development_first_problem_posing=
    Option.bind development_owner_record_1853 (development_citing_generation development_first_problem_payload)"
  by (fact development_first_problem_posing_def)

ML \<open>
structure First_Problem_Execution =
struct
  val directions = @{code first_problem_owner_directions}
  val read_back = @{code first_problem_owner_record_read_back}
  fun timed label f x =
    let val (t, r) = Timing.timing f x
    in (writeln ("FIRST PROBLEM " ^ label ^ ": " ^ Timing.message t); r) end
  fun owner_records () =
    ListPair.appEq (fn (stamp, t) =>
      if timed ("owner record " ^ stamp ^ " read back") read_back t = SOME true then ()
      else error ("FIRST PROBLEM owner record " ^ stamp ^ ": not read back"))
      (["1750", "1812", "1836", "1853", "1957"], directions)
  fun posing record cite report payload =
    (case record of
      NONE => error "FIRST PROBLEM: no owner record of 18:53"
    | SOME r => Native_State_Execution.recording (fn t => cite t r) report "first problem posing" payload)
end
\<close>

ML \<open>val _ = First_Problem_Execution.owner_records ()\<close>

end
