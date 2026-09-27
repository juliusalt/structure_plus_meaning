theory Factor_Least_Query_Controls
  imports Factor_Resolution_Controls
begin

section \<open>W2's queries at a table, at a producer's commitment and at its root-kept restriction\<close>

text \<open>
  W5's control (task 847), imported by no theory and evaluated once: the given's registration of 561 collected by W2's
  queries at a query's parameters holding a table (@{text query_control_parameters}, built once in the evaluation),
  beside the collection at the plain parameters (@{const merge_control_collected}, R4's). The table at each variable
  type holds the call 26 at a formed environment, resolved by R4 with one certificate, so it is a true call and the
  table valid; the queries of 561's families are selections, whose goals stay open where the table closes ground calls
  only, so the collection at the table is the collection at the plain parameters: at the compatible pair the merge, at
  the conflicting pair the conflict read back as no formed environment.

  VK1's controls (task 920). A query rooted at the permutation site of R5's commitment control, a declared producer,
  at a two-element list with its output open: its two answers are two presentations of one output. The committed
  search at the producer's commitment commits the root goal at the top focus and keeps the least answer only; at the
  commitment's root-kept restriction (@{const finite_root_kept}) the root goal holds a root variable, so it is not
  committed there and both answers are found, as R4 finds them. A ground query at the selection site, sel([1,2],(2,[1])),
  whose clause's premise sel([2],(2,[])) is ground and a table entry: the entry closes that goal inside the query (a
  root call is found holding one node where the plain search's holds two), and the query's values are those of the
  plain instance (review 848's follow-up 2).
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

definition query_control_entries where
  "query_control_entries \<Xi>=((case resolution_table_lookup (parameter_table (fst \<Xi>))
      (26,finite_environment_value registration_control_other) of None \<Rightarrow> False | Some c \<Rightarrow> True) \<and>
    (case resolution_table_lookup (parameter_table (snd \<Xi>))
      (26,finite_environment_value registration_control_other) of None \<Rightarrow> False | Some c \<Rightarrow> True))"

definition query_control_collected where
  "query_control_collected \<Xi> E F=map_option finite_environment_value_read
    (finite_registration_value_in \<Xi> finite_given_readers 80 merge_witness_registration (merge_control_bindings E F))"

definition producer_query_pattern :: "(nat,nat+nat) resolution_variable finite_term_pattern" where
  "producer_query_pattern=map_finite_term_pattern finite_query_variable
    (Finite_Pattern_Pair (finite_exact_term_pattern (control_payload_list [[1],[2]])) (Finite_Variable (0::nat)))"

definition producer_query_declarations :: "(nat+nat,nat,nat) resolution_declarations" where
  "producer_query_declarations=\<lparr>declared_producers={|(1,view_identity,[view_output])|},
    declared_consumers={||}, declared_sockets={||}\<rparr>"

definition producer_query_values :: "(nat+nat,nat,nat,nat) resolution_parameters \<Rightarrow> finite_factor_term fset" where
  "producer_query_values Z=fimage finite_residual_term (finite_root_calls (finite_parameters_search Z
    (finite_query_program commitment_control_program) 40 (finite_pattern_state 1 producer_query_pattern)))"

definition producer_query_committed :: "(nat+nat,nat,nat,nat) resolution_parameters" where
  "producer_query_committed=plain_parameters\<lparr>parameter_commitment:=finite_declared_commitment producer_query_declarations\<rparr>"

definition producer_query_kept :: "(nat+nat,nat,nat,nat) resolution_parameters" where
  "producer_query_kept=plain_parameters\<lparr>parameter_commitment:=
    finite_root_kept (finite_declared_commitment producer_query_declarations)\<rparr>"

definition table_query_root :: finite_factor_term where
  "table_query_root=Finite_Pair (control_payload_list [[1],[2]]) (Finite_Pair (Finite_Payload [2]) (control_payload_list [[1]]))"

definition table_query_call :: finite_factor_term where
  "table_query_call=Finite_Pair (control_payload_list [[2]]) (Finite_Pair (Finite_Payload [2]) (control_payload_list []))"

definition table_query_entry :: "(nat+nat,nat,nat,nat) resolution_table" where
  "table_query_entry=query_control_table (finite_query_program commitment_control_program) 0 table_query_call 40"

definition table_query_outcome :: "(nat+nat,nat,nat,nat) resolution_table \<Rightarrow> (nat+nat,nat,nat,nat) resolution_outcome" where
  "table_query_outcome \<Theta>=finite_parameters_search (plain_parameters\<lparr>parameter_table:=\<Theta>\<rparr>)
    (finite_query_program commitment_control_program) 40
    (finite_pattern_state 0 (finite_exact_term_pattern table_query_root :: (nat,nat+nat) resolution_variable finite_term_pattern))"

definition table_query_values :: "(nat+nat,nat,nat,nat) resolution_table \<Rightarrow> finite_factor_term fset" where
  "table_query_values \<Theta>=fimage finite_residual_term (finite_root_calls (table_query_outcome \<Theta>))"

definition table_query_sizes :: "(nat+nat,nat,nat,nat) resolution_table \<Rightarrow> nat fset" where
  "table_query_sizes \<Theta>=fimage (\<lambda>st. fcard (fimage resolution_node_position (resolution_nodes st)))
    (resolution_found (table_query_outcome \<Theta>))"

lemma least_query_controls:
  "let \<Xi>=query_control_parameters 400; R4=producer_query_values plain_parameters;
    C=producer_query_values producer_query_committed; Kr=producer_query_values producer_query_kept in
    query_control_entries \<Xi> \<and>
    query_control_collected \<Xi> environment_reader_control_rooted registration_control_other=
      merge_control_collected environment_reader_control_rooted registration_control_other \<and>
    query_control_collected \<Xi> environment_reader_control_rooted registration_control_other=
      Some (Some (finite_merge_environment environment_reader_control_rooted registration_control_other)) \<and>
    query_control_collected \<Xi> environment_reader_control_rooted registration_control_conflict=
      merge_control_collected environment_reader_control_rooted registration_control_conflict \<and>
    query_control_collected \<Xi> environment_reader_control_rooted registration_control_conflict=Some None \<and>
    fcard R4=2 \<and> fcard C=1 \<and> C |\<subseteq>| R4 \<and> Kr=R4 \<and>
    (case resolution_table_lookup table_query_entry (0,table_query_call) of None \<Rightarrow> False | Some c \<Rightarrow> True) \<and>
    table_query_values table_query_entry=table_query_values resolution_empty_table \<and>
    table_query_values table_query_entry={|table_query_root|} \<and>
    table_query_sizes table_query_entry={|1|} \<and> table_query_sizes resolution_empty_table={|2|}"
  by eval

end
