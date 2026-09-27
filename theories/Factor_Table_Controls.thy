theory Factor_Table_Controls
  imports Factor_Resolution_Completeness
begin

text \<open>
  The table's control (build GT1b of the section "The given's calls are decided once" of task 495's entry), one lemma
  by one evaluation; no theory imports this theory. Site 1 holds of X where site 0 does, site 0 where site 2 does, and
  site 2 of the payload [1]. The table holds one entry, site 0 at [1], its certificate the one R4's resolution of that
  call returns, which the checker accepts, so the table is valid (@{text table_control_valid}). At the table the call of
  site 1 at [1] is resolved with its premise closed by the entry: its found state holds one node where at the empty
  table it holds three, and two steps resolve it where at the empty table they leave it cut, unresolved. The call at
  [2], false, is refuted at the table as R4 refutes it at the empty table: a refutation rests on no entry.
\<close>

definition table_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "table_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),(2,Finite_Variable 0)|},
    finite_system_clauses={|
      ((2,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [1], finite_schema_premises={||},
        finite_schema_materials={||}\<rparr>),
      ((0,0),\<lparr>finite_schema_conclusion=Finite_Variable 0, finite_schema_premises={|(0,(2,Finite_Variable 0))|},
        finite_schema_materials={||}\<rparr>),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Variable 0, finite_schema_premises={|(0,(0,Finite_Variable 0))|},
        finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition table_control_entry :: "(nat,nat,nat) finite_schema_proof option" where
  "table_control_entry = (case finite_program_resolution no_witness_construction table_control_program 0
      (Finite_Payload [1]) 10 of Finite_Resolved C \<Rightarrow> Some (fthe_elem C) | _ \<Rightarrow> None)"

definition table_control_table :: "(nat,nat,nat,nat) resolution_table" where
  "table_control_table = Resolution_Table (\<lambda>q. if q = (0,Finite_Payload [1]) then table_control_entry else None)"

definition table_control_row ::
    "(nat,nat,nat,nat) resolution_table \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option \<times> nat fset" where
  "table_control_row \<Theta> t n = (finite_resolution_verdict
      (finite_program_resolution_in \<Theta> no_witness_construction table_control_program 1 t n),
    fimage (\<lambda>st. fcard (resolution_nodes st)) (resolution_found
      (finite_resolution_search_in \<Theta> no_witness_construction table_control_program n (finite_initial_state 1 t))))"

lemma table_controls:
  "(case table_control_entry of Some c \<Rightarrow> finite_checks_schema_proof table_control_program c 0 (Finite_Payload [1])
      | None \<Rightarrow> False) \<and>
    table_control_row table_control_table (Finite_Payload [1]) 2 = (Some True, {|1|}) \<and>
    table_control_row resolution_empty_table (Finite_Payload [1]) 2 = (None, {||}) \<and>
    table_control_row table_control_table (Finite_Payload [1]) 3 = (Some True, {|1|}) \<and>
    table_control_row resolution_empty_table (Finite_Payload [1]) 3 = (Some True, {|3|}) \<and>
    table_control_row table_control_table (Finite_Payload [2]) 3 = (Some False, {||}) \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction table_control_program 1
      (Finite_Payload [2]) 3) = Some False"
  by eval

lemma table_control_valid: "finite_table_valid table_control_program table_control_table"
proof -
  obtain c where c: "table_control_entry = Some c"
    "finite_checks_schema_proof table_control_program c 0 (Finite_Payload [1])"
    using table_controls by (auto split: option.splits)
  show ?thesis unfolding finite_table_valid_def table_control_table_def c(1) using c(2) by (auto split: if_splits)
qed

end
