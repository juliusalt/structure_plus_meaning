theory Development_Bounded_Recording_Execution
  imports Development_Recording_Refinements Development_Native_State Native_Execution_Refinements
begin

section \<open>The bounded recording at the owner record of 18:53 and two cuts of the given's value\<close>

text \<open>
  The controls of task 492 (task 482's entry, its (4) B2): the owner record of 18:53 and the given's value cut as
  task 481 cuts it (a preorder cut of the first n pairs and leaves, the rest the empty payload: 8,013 and 32,009
  addresses at 4,000 and 16,000), each recorded as a base generation by the bounded recording, whose cause targets
  are one, as the entry expects: F0 does not depend on the payload. They are evaluated with the refinement
  collection in effect in the one compilation of @{text Development_Native_State_Execution} (task 538), which
  reports each payload's addresses and each cause's carrier addresses and refuses a cause other than the owner
  record's; this theory states them and runs nothing.
\<close>

primrec bounded_recording_cut :: "finite_factor_term \<Rightarrow> nat \<Rightarrow> nat \<times> finite_factor_term" where
  "bounded_recording_cut (Finite_Pair a b) n=(if n=0 then (0,Finite_Payload []) else
     (case bounded_recording_cut a (n-1) of (m,a') \<Rightarrow>
       (case bounded_recording_cut b m of (k,b') \<Rightarrow> (k,Finite_Pair a' b'))))"
| "bounded_recording_cut (Finite_Payload v) n=(if n=0 then (0,Finite_Payload []) else (n-1,Finite_Payload v))"
| "bounded_recording_cut (Finite_Target x) n=(if n=0 then (0,Finite_Payload []) else (n-1,Finite_Target x))"

primrec bounded_recording_addresses :: "finite_factor_term \<Rightarrow> nat" where
  "bounded_recording_addresses (Finite_Pair a b)=3+bounded_recording_addresses a+bounded_recording_addresses b"
| "bounded_recording_addresses (Finite_Payload v)=1"
| "bounded_recording_addresses (Finite_Target a)=1"

definition bounded_recording_subjects :: "finite_factor_term list" where
  "bounded_recording_subjects=[development_owner_direction_1853,
     snd (bounded_recording_cut development_given_value 4000), snd (bounded_recording_cut development_given_value 16000)]"

definition bounded_recording_generation_cause ::
    "(local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option \<Rightarrow>
      finite_exact_artifact option" where
  "bounded_recording_generation_cause r=(case r of
     None \<Rightarrow> None
   | Some (B,u,G) \<Rightarrow> (case generation_cause G of Finite_Whole C \<Rightarrow> Some C | Finite_Anchor C a \<Rightarrow> None))"

definition bounded_recording_cause :: "finite_factor_term \<Rightarrow> finite_exact_artifact option" where
  "bounded_recording_cause t=bounded_recording_generation_cause (development_base_generation t)"

end
