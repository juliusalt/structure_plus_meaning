theory Development_First_Problem_Execution
  imports Development_First_Problem Development_Native_State_Execution Development_Recording_Refinements
    Native_Execution_Refinements
begin

section \<open>The posing's construction, compiled once\<close>

text \<open>
  Task 397: the posing of the native loop's first problem (@{const development_first_problem_posing}) executed with
  the recording's refinement collection and the export boundary's refinements in effect. One compilation holds the
  payload, the owner record of 18:53 and the citing recording. The posing is reported with its seconds, its payload's
  addresses, the carrier addresses of its cause and whether its cause is the owner record of 18:53's (the report of
  @{text Development_Native_State_Execution}); a posing that returns no generation, or whose cause is another, is
  refused. The posing runs where @{text First_Problem_Execution.posing} is called, in the held measurement. At every
  load the five owner records are recorded and read back (moved from @{text Development_Owner_Records}), each timed,
  and a record that does not read back refuses the theory. No library theory imports this one.
\<close>

definition first_problem_owner_directions :: "finite_factor_term list" where
  "first_problem_owner_directions=[development_owner_direction_1750,development_owner_direction_1812,
    development_owner_direction_1836,development_owner_direction_1853,development_owner_direction_1957]"

definition first_problem_owner_record_read_back :: "finite_factor_term \<Rightarrow> bool option" where
  "first_problem_owner_record_read_back t=development_owner_record_read_back t (development_owner_record t)"

text \<open>
  The asked installation's constants are defined through the interpretation of @{text given_readers_extension}; their
  code equations are the locale's definitions at the asked program.
\<close>

lemma asked_installation_code [code]:
  "asked_environment=fst (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_program given_readers_placement))"
  "asked_use=snd (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_program given_readers_placement))"
  "asked_placement=finite_program_coordinates given_environment (finite_system_definitions finite_rooted_given_readers)
    (finite_system_definitions finite_asked_program) given_readers_placement"
  by (simp_all only: asked_environment_def asked_use_def asked_placement_def asked_extension.installed_environment_def
    asked_extension.installed_use_def asked_extension.installed_def asked_extension.installed_placement_def)

lemma first_problem_posing_recording:
  "development_first_problem_posing=
    Option.bind development_owner_record_1853 (development_citing_generation development_first_problem_payload)"
  by (fact development_first_problem_posing_def)

ML \<open>
structure First_Problem_Execution =
struct
  val directions = @{code first_problem_owner_directions}
  val read_back = @{code first_problem_owner_record_read_back}
  val payload = @{code development_first_problem_payload}
  val record = @{code development_owner_record_1853}
  val cite = @{code development_citing_generation}
  val report = @{code native_state_report}
  fun timed label f x =
    let val (t, r) = Timing.timing f x
    in (writeln ("FIRST PROBLEM " ^ label ^ ": " ^ Timing.message t); r) end
  fun count NONE = "none" | count (SOME n) = IntInf.toString n
  fun owner_records () =
    ListPair.appEq (fn (stamp, t) =>
      if timed ("owner record " ^ stamp ^ " read back") read_back t = SOME true then ()
      else error ("FIRST PROBLEM owner record " ^ stamp ^ ": not read back"))
      (["1750", "1812", "1836", "1853", "1957"], directions)
  fun posing () =
    (case record of
      NONE => error "FIRST PROBLEM: no owner record of 18:53"
    | SOME r =>
        let
          val g = timed "posing recording" (cite payload) r
          val (a, (c, same)) = report payload g
          val _ = writeln ("FIRST PROBLEM posing: payload " ^ IntInf.toString a ^ " addresses, cause " ^ count c ^
            " carrier addresses, the owner record of 18:53's cause " ^ Bool.toString same)
        in if same then g else error "FIRST PROBLEM posing: no generation, or a cause other than the owner record's" end)
end
\<close>

ML \<open>val _ = First_Problem_Execution.owner_records ()\<close>

end
