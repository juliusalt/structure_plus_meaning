theory Factor_Table_Search_Controls
  imports Factor_Table_Controls Factor_Deferred_Search
begin

text \<open>
  The control of the table in F2's shared representation (build GT3 of the section "The given's calls are decided
  once" of task 495's entry, task 876), one lemma by one evaluation; no theory imports this theory. GT1b's program
  and its one entry (@{text Factor_Table_Controls}) as a listed table: the search at it, computed through the deferred
  search at the table (@{thm [source] finite_resolution_search_listed_deferred_code}), equals R3's search at the
  table, computed by R3's own equations, at the call the entry closes and at the false call beside it; its found
  state holds one node where the search at the empty table holds three, and at two steps it resolves the call where
  the search at the empty table is cut.
\<close>

definition table_search_entries :: "((nat \<times> finite_factor_term) \<times> (nat,nat,nat) finite_schema_proof) list" where
  "table_search_entries = (case table_control_entry of Some c \<Rightarrow> [((0,Finite_Payload [1]),c)] | None \<Rightarrow> [])"

definition table_search_nodes :: "(nat,nat,nat,nat) resolution_outcome \<Rightarrow> nat fset" where
  "table_search_nodes R = fimage (\<lambda>st. fcard (resolution_nodes st)) (resolution_found R)"

lemma table_search_controls:
  "table_search_entries \<noteq> [] \<and>
    (let st = finite_initial_state 1 (Finite_Payload [1]); sf = finite_initial_state 1 (Finite_Payload [2]) in
    finite_resolution_search_listed table_search_entries no_witness_construction table_control_program 3 st =
      finite_resolution_search_in table_control_table no_witness_construction table_control_program 3 st \<and>
    finite_resolution_search_listed table_search_entries no_witness_construction table_control_program 3 sf =
      finite_resolution_search_in table_control_table no_witness_construction table_control_program 3 sf \<and>
    table_search_nodes (finite_resolution_search_listed table_search_entries no_witness_construction
      table_control_program 2 st) = {|1|} \<and>
    table_search_nodes (finite_resolution_search_listed [] no_witness_construction table_control_program 2 st) = {||} \<and>
    table_search_nodes (finite_resolution_search_listed [] no_witness_construction table_control_program 3 st) = {|3|})"
  by eval

end
