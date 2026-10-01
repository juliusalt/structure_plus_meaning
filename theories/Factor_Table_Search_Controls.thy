theory Factor_Table_Search_Controls
  imports Factor_Table_Controls Factor_Deferred_Search Factor_Resolution_Checks
begin

text \<open>
  The control of the table in F2's shared representation (build GT3 of the section "The given's calls are decided
  once" of task 495's entry, task 876), one lemma by one evaluation; no theory imports this theory. GT1b's program
  and its one entry (@{text Factor_Table_Controls}) as a listed table: the search at it, computed through the deferred
  search at the table (@{thm [source] finite_resolution_search_listed_deferred_code}), equals R3's search at the
  table, computed by R3's own equations, at the call the entry closes and at the false call beside it; its found
  state holds one node where the search at the empty table holds three, and at two steps it resolves the call where
  the search at the empty table is cut.

  The committed side (GT3b, task 970), in the same evaluation: the route's check constant at the listed table, computed
  through the route's search over the deferred committed representation at the table
  (@{thm [source] moded_check_resolution_listed_code}), equals GT2c's check form at the table computed by its own
  equations, at the call the entry closes and at the false call; the route's search at the table holds one node at two
  steps where at the empty list it is cut and at three steps holds three. At a table of the same true call whose
  certificate the checker does not accept, the tree result resolves nothing through the entry, while the route's search
  still closes the call by the table's calls alone and GT4's graph verdict of its found state holds
  (@{const moded_check_graph_verdicts_listed}).
\<close>

abbreviation table_route_declarations :: "(nat,nat,nat,unit) produced_declarations" where
  "table_route_declarations \<equiv> unproduced (unnarrowed no_declarations)"

definition table_route_search ::
    "((nat \<times> finite_factor_term) \<times> (nat,nat,nat) finite_schema_proof) list \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow>
      (nat,nat,nat,nat) resolution_outcome" where
  "table_route_search es t n = moded_deferred_route_search_in es no_witness_construction table_control_program 0
    table_route_declarations {||} no_declarations {||}
    (access_narrowed_commitment table_control_program 0 table_route_declarations {||})
    (finite_declared_raisers table_control_program (resolution_declarations.truncate table_route_declarations))
    (clause_sockets_distinct table_control_program) (Some []) 1 t n"

definition table_route_check ::
    "((nat \<times> finite_factor_term) \<times> (nat,nat,nat) finite_schema_proof) list \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow>
      (nat,nat,nat,nat) finite_resolution_result" where
  "table_route_check es t n = moded_check_resolution_listed es no_witness_construction table_control_program 0
    table_route_declarations {||} no_declarations {||} 1 t n"

definition table_unaccepted_entries :: "((nat \<times> finite_factor_term) \<times> (nat,nat,nat) finite_schema_proof) list" where
  "table_unaccepted_entries = [((0,Finite_Payload [1]),Schema_Proof 0 {||} {||})]"

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
    table_search_nodes (finite_resolution_search_listed [] no_witness_construction table_control_program 3 st) = {|3|} \<and>
    clause_sockets_distinct table_control_program \<and>
    table_route_check table_search_entries (Finite_Payload [1]) 3 = moded_check_resolution_in table_control_table
      no_witness_construction table_control_program 0 table_route_declarations {||} no_declarations {||} 1 (Finite_Payload [1]) 3 \<and>
    table_route_check table_search_entries (Finite_Payload [2]) 3 = moded_check_resolution_in table_control_table
      no_witness_construction table_control_program 0 table_route_declarations {||} no_declarations {||} 1 (Finite_Payload [2]) 3 \<and>
    finite_resolution_verdict (table_route_check table_search_entries (Finite_Payload [1]) 3) = Some True \<and>
    finite_resolution_verdict (table_route_check table_search_entries (Finite_Payload [2]) 3) = Some False \<and>
    table_search_nodes (table_route_search table_search_entries (Finite_Payload [1]) 2) = {|1|} \<and>
    table_search_nodes (table_route_search [] (Finite_Payload [1]) 2) = {||} \<and>
    table_search_nodes (table_route_search [] (Finite_Payload [1]) 3) = {|3|} \<and>
    finite_resolution_verdict (table_route_check table_unaccepted_entries (Finite_Payload [1]) 3) = None \<and>
    table_search_nodes (table_route_search table_unaccepted_entries (Finite_Payload [1]) 2) = {|1|} \<and>
    fimage snd (moded_check_graph_verdicts_listed table_unaccepted_entries no_witness_construction table_control_program 0
      table_route_declarations {||} no_declarations {||} 1 (Finite_Payload [1]) 3) = {|True|})"
  by eval

end
