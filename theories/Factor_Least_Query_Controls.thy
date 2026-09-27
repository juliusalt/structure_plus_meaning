theory Factor_Least_Query_Controls
  imports Factor_Resolution_Controls
begin

section \<open>W2's queries at a table\<close>

text \<open>
  W5's control (task 847), imported by no theory and evaluated once: the given's registration of 561 collected by W2's
  queries at a query's parameters holding a table (@{text query_control_parameters}), beside the collection at the
  plain parameters (@{const merge_control_collected}, R4's). The table at each variable type holds the call 26 at a
  formed environment, resolved by R4 with one certificate, so it is a true call and the table valid; the queries
  of 561's families are selections, whose goals stay open where the table closes ground calls only, so the collection
  at the table is the collection at the plain parameters: at the compatible pair the merge, at the conflicting pair
  the conflict read back as no formed environment. 77 at the control package is not evaluated here: at the plain
  parameters and at a table with no commitment its queries enumerate 37's output (tasks 718 and 857), and the
  committing instance, the given's declarations varied along the lifting, waits on the design placed for q161 (A).
\<close>

definition query_control_table ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) resolution_table" where
  "query_control_table P d t n=(case finite_program_resolution no_witness_construction P d t n of
      Finite_Resolved C \<Rightarrow> if fcard C=1 then Resolution_Table (\<lambda>z. if z=(d,t) then Some (fthe_elem C) else None)
        else resolution_empty_table
    | _ \<Rightarrow> resolution_empty_table)"

definition query_control_parameters where
  "query_control_parameters n=
    (plain_parameters\<lparr>parameter_table:=query_control_table finite_given_readers 26
        (finite_environment_value registration_control_other) n\<rparr>,
     plain_parameters\<lparr>parameter_table:=query_control_table (finite_query_program finite_given_readers) 26
        (finite_environment_value registration_control_other) n\<rparr>)"

definition query_control_entries :: "nat \<Rightarrow> bool" where
  "query_control_entries n=((case resolution_table_lookup
      (parameter_table (fst (query_control_parameters n :: (_,_,_,_,nat) query_parameters)))
      (26,finite_environment_value registration_control_other) of None \<Rightarrow> False | Some c \<Rightarrow> True) \<and>
    (case resolution_table_lookup (parameter_table (snd (query_control_parameters n :: (_,_,_,_,nat) query_parameters)))
      (26,finite_environment_value registration_control_other) of None \<Rightarrow> False | Some c \<Rightarrow> True))"

definition query_control_collected :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> local_address option finite_artifact_environment option option" where
  "query_control_collected E F=map_option finite_environment_value_read
    (finite_registration_value_in (query_control_parameters 400) finite_given_readers 80 merge_witness_registration
      (merge_control_bindings E F))"

lemma least_query_controls:
  "query_control_entries 400 \<and>
    query_control_collected environment_reader_control_rooted registration_control_other=
      merge_control_collected environment_reader_control_rooted registration_control_other \<and>
    query_control_collected environment_reader_control_rooted registration_control_other=
      Some (Some (finite_merge_environment environment_reader_control_rooted registration_control_other)) \<and>
    query_control_collected environment_reader_control_rooted registration_control_conflict=
      merge_control_collected environment_reader_control_rooted registration_control_conflict \<and>
    query_control_collected environment_reader_control_rooted registration_control_conflict=Some None"
  by eval

end
