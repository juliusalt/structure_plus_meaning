theory Development_Native_State_Execution
  imports Development_Bounded_Recording_Execution Development_Recording_Refinements Development_Native_State
    Native_Execution_Refinements
begin

section \<open>The native state's first generation, compiled where it is recorded\<close>

text \<open>
  Task 482's entry, its (4) X (#395's remainder): the recording of the native state's first generation, the base
  generation at the given's value (@{const development_native_state_first_generation}), with the recording's
  refinement collection and the export boundary's refinements in effect. Each recording is reported with its seconds,
  its payload's addresses, the carrier addresses of its cause, and whether its cause is the owner record of 18:53's; a
  recording that returns no generation, or whose cause is another, is refused.

  The ML structure @{text Native_State_Execution} states that behaviour once, over the compiled recording and report
  its caller supplies, and this theory compiles and evaluates nothing at build. It recorded the owner record of 18:53
  at every build (task 561), about 7 s of compilation for a control the owner records' read-back makes at every load of
  @{text Development_First_Problem_Execution}, which keeps it alone (task 562). The given's value, and
  the controls of task 492 cut from it (8,013 and 32,009 addresses, @{text Development_Bounded_Recording_Execution}),
  are compiled and evaluated where they are called: the caller compiles, in one @{text ML} block,
  @{text native_state_given}, @{const bounded_recording_subjects}, @{const development_base_generation} and
  @{text native_state_report}, and passes them to @{text controls} or @{text first_generation}. The given's code (the
  development package's and the readers' programs, their installation and the given's presentation) was about half of
  this theory's load, compiled and evaluated at every build for two controls that are made where they are asked for.
  No library theory imports this one.
\<close>

definition native_state_given :: "unit \<Rightarrow> finite_factor_term" where
  "native_state_given u=development_given_value"

lemma native_state_first_generation_recording:
  "development_native_state_first_generation=development_base_generation (native_state_given ())"
  by (simp add: development_native_state_first_generation_def native_state_given_def)

definition native_state_owner_cause :: "finite_exact_artifact option" where
  "native_state_owner_cause=bounded_recording_cause development_owner_direction_1853"

definition native_state_report ::
    "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option \<Rightarrow>
      integer\<times>integer option\<times>bool" where
  "native_state_report t r=(integer_of_nat (bounded_recording_addresses t),
     map_option (\<lambda>C. integer_of_nat (fcard (finite_carrier (finite_structure C)))) (bounded_recording_generation_cause r),
     bounded_recording_generation_cause r\<noteq>None \<and> bounded_recording_generation_cause r=native_state_owner_cause)"

ML \<open>
structure Native_State_Execution =
struct
  fun timed label f x =
    let val (t, r) = Timing.timing f x
    in (writeln ("NATIVE STATE " ^ label ^ ": " ^ Timing.message t); r) end
  fun count NONE = "none" | count (SOME n) = IntInf.toString n
  fun recording record report label t =
    let
      val r = timed (label ^ " recording") record t
      val (a, (c, same)) = report t r
      val _ = writeln ("NATIVE STATE " ^ label ^ ": payload " ^ IntInf.toString a ^ " addresses, cause " ^ count c ^
        " carrier addresses, the owner record of 18:53's cause " ^ Bool.toString same)
    in if same then r else error ("NATIVE STATE " ^ label ^ ": no generation, or a cause other than the owner record's") end
  fun controls record report subjects = ListPair.appEq (fn (label, t) => ignore (recording record report label t))
    (["owner record 18:53", "cut 4000", "cut 16000"], subjects)
  fun first_generation record report given = recording record report "first generation" (given ())
end
\<close>

end
