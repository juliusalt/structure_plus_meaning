theory Development_Bounded_Recording_Execution
  imports Development_Recording_Refinements Development_Native_State Native_Execution_Refinements
begin

section \<open>The bounded recording at the owner record of 18:53 and two cuts of the given's value\<close>

text \<open>
  The controls of task 492 (task 482's entry, its (4) B2), evaluated once with the refinement collection in
  effect: the owner record of 18:53 and the given's value cut as task 481 cuts it (a preorder cut of the
  first n pairs and leaves, the rest the empty payload: 8,013 and 32,009 addresses at 4,000 and 16,000), each
  recorded as a base generation by the bounded recording. The evaluation shows each payload's addresses, the
  size of each recorded cause in carrier addresses, and whether the three cause targets are equal, as the
  entry expects: F0 does not depend on the payload.
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

definition bounded_recording_cause :: "finite_factor_term \<Rightarrow> finite_exact_artifact option" where
  "bounded_recording_cause t=(case development_base_generation t of
     None \<Rightarrow> None
   | Some (B,u,G) \<Rightarrow> (case generation_cause G of Finite_Whole C \<Rightarrow> Some C | Finite_Anchor C a \<Rightarrow> None))"

definition development_bounded_recording_controls :: "nat list \<times> nat option list \<times> bool" where
  "development_bounded_recording_controls=(let causes=map bounded_recording_cause bounded_recording_subjects in
     (map bounded_recording_addresses bounded_recording_subjects,
      map (map_option (\<lambda>C. fcard (finite_carrier (finite_structure C)))) causes,
      list_all (\<lambda>c. c\<noteq>None \<and> c=hd causes) causes))"

value development_bounded_recording_controls

end
