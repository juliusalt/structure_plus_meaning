theory Development_Given_Query_Parameters
  imports Factor_Committing_Query_Parameters Development_Given_Productions Development_Given_Modes
    Development_Rooted_Registrations Development_First_Request_Registrations
begin

section \<open>The given's committing instance\<close>

text \<open>
  The given's input record (@{const given_input_declarations}) and frames (@{const given_input_frames}) at the rooted
  readers, the check forms' program, with the given's modes (@{const given_modes}): the ground part as the check forms
  use it (@{text Development_Given_Declarations_Execution}), the lifted part the record varied along the query program's
  left injection, its commitment the root-kept restriction.
\<close>

abbreviation given_query_program :: "(nat+'v,nat,nat,nat) finite_schema_system" where
  "given_query_program \<equiv> finite_query_program finite_rooted_given_readers"

abbreviation given_query_parameters ::
    "nat \<Rightarrow> (nat,nat,nat,nat) resolution_table \<Rightarrow> (nat+'v,nat,nat,nat) resolution_table \<Rightarrow>
      (nat,nat,nat,nat,'v) query_parameters" where
  "given_query_parameters m \<Theta> \<Theta>' \<equiv> committing_query_parameters finite_rooted_given_readers m given_input_declarations
    given_input_frames given_modes \<Theta> \<Theta>'"

text \<open>
  The given's record at the rooted readers is discharged there (#798's record, @{thm [source]
  given_input_declarations_discharged}, @{thm [source] given_input_frames_discharged}, @{thm [source]
  given_input_declarations_productions}), and the query program means what the rooted readers mean
  (@{thm [source] finite_query_program_meaning}). The record carried along the left injection is therefore V2b's carried
  record there (@{text varied_narrowed_record}) exactly where three conditions of the carrying hold at the query program:
  its sources' narrowings agree, its productions stay discharged, and every narrowed socket keeps a production.
\<close>

theorem given_query_record_from:
  assumes agree: "varied_narrowings_agree finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) given_input_declarations"
    and varied: "productions_discharged (positive_meaning (decode_finite_system (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)))
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) m
      (produced_declarations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
        given_input_declarations)"
    and declared': "narrowed_productions_declared (produced_declarations_varied finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) given_input_declarations)"
  shows "varied_narrowed_record finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
    given_input_declarations given_declarations_correspondence given_input_frames m m"
proof (rule varied_narrowed_record.intro, goal_cases)
  case 1 show ?case by (rule finite_rooted_given_readers_formed)
next
  case 2 show ?case by (rule finite_query_program_formed[OF finite_rooted_given_readers_formed])
next
  case (3 d x) show ?case by (simp only: finite_query_program_meaning[OF finite_rooted_given_readers_formed])
next
  case 4 show ?case by (rule agree)
next
  case 5 show ?case using given_input_declarations_discharged(1) by (simp add: finite_rooted_given_readers_exact)
next
  case 6 show ?case using given_input_frames_discharged by (simp add: finite_rooted_given_readers_exact)
next
  case 7 show ?case by (rule given_input_declarations_productions)
next
  case 8 show ?case by (rule varied)
next
  case 9 show ?case by (rule declared')
qed

theorem given_query_exact:
  assumes varied_record: "varied_narrowed_record finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
      given_input_declarations given_declarations_correspondence given_input_frames m m"
    and true: "finite_table_true finite_rooted_given_readers \<Theta>"
    and true': "finite_table_true (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) \<Theta>'"
  shows "finite_query_exact (given_query_parameters m \<Theta> \<Theta>' :: (nat,nat,nat,nat,'v) query_parameters)
    finite_rooted_given_readers n"
  by (rule committing_query_exact[OF varied_record given_input_declarations_discharged(3) true true'])

section \<open>The registrations' completeness at a committing instance\<close>

text \<open>
  W4a's completeness at a query's parameters (W5's forms) holds wherever @{const finite_query_exact} does, so at a
  committing instance each is its form composed with @{thm [source] committing_query_exact}: at the given's committing
  instance for the rooted readers, and at a committing instance of a record carried to the given's readers or to the
  first request's program, its carried record the named premise.
\<close>

lemmas given_rooted_registrations_committing = given_rooted_registrations_complete_in[OF given_query_exact]
lemmas given_rooted_construction_committing = given_rooted_construction_complete_in[OF given_query_exact]
lemmas given_witness_registrations_committing = given_witness_registrations_complete_in[OF given_query_exact]
lemmas given_readers_registrations_committing = given_readers_registrations_complete_in[OF committing_query_exact]
lemmas given_readers_construction_committing = given_readers_construction_complete_in[OF committing_query_exact]
lemmas readers_agreement_registrations_committing = readers_agreement_registrations_complete_in[OF committing_query_exact]
lemmas first_request_registrations_committing = first_request_registrations_complete_in[OF committing_query_exact]
lemmas first_request_construction_committing = first_request_construction_complete_in[OF committing_query_exact]

end
