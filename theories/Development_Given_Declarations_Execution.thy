theory Development_Given_Declarations_Execution
  imports Development_Given_Carried_Declarations Native_Execution_Refinements
begin

text \<open>
  The controls of the given's record (\<open>Development_Given_Carried_Declarations\<close>), each by one evaluation over the
  given's rooted readers, in a thin theory that no library theory imports.

  The first lemma evaluates three calls under the committed resolution with the record: at 500 on a whole
  artifact of five atoms it is resolved; at 10 on that artifact beside the list of its atoms in reverse order it is
  resolved; at 10 beside a list missing one atom it is refuted. It states these three verdicts and nothing about
  other calls.

  The second evaluates, at 79 over a root family of five sites, the state R3's search reaches when it expands 79's one
  clause: each pending premise with its position, its callee, and whether it is a ground call, an independent goal
  and a leaf call (the classes @{const finite_goal_selection} orders by), and the positions R3's selection takes
  there.
\<close>

text \<open>
  The instantiation family's socket schemas are written through @{const finite_pattern_of}, whose target leaves go
  through @{const finite_object_of}, which has no code; none of those schemas holds a target, so that branch is never
  reached, and it aborts in code, as in @{text Development_Socket_Liveness_Execution}.
\<close>

declare [[code abort: finite_object_of]]

definition given_control_artifact :: finite_exact_artifact where
  "given_control_artifact = \<lparr>finite_structure = \<lparr>finite_carrier = {|[1],[2],[3],[4],[5]|}, finite_incidence = {||}\<rparr>,
    finite_data = \<lparr>finite_bag = {#}, finite_bindings = {||}\<rparr>\<rparr>"

definition given_control_rows :: "local_address list \<Rightarrow> finite_factor_term" where
  "given_control_rows A = Finite_Pair (finite_data_list (map Finite_Payload A))
    (Finite_Pair (finite_data_list []) (Finite_Pair (finite_data_list []) (finite_data_list [])))"

abbreviation given_control_resolution :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "given_control_resolution d t \<equiv> finite_resolution_verdict (finite_committed_resolution no_witness_construction
    (finite_declared_commitment given_declarations) finite_rooted_given_readers d t 40)"

lemma given_declarations_control:
  "given_control_resolution 500 (Finite_Target (Finite_Whole given_control_artifact)) = Some True \<and>
   given_control_resolution 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[5],[4],[3],[2],[1]])) = Some True \<and>
   given_control_resolution 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[1],[2],[3],[4]])) = Some False"
  by eval

section \<open>79's clause at a root family of five sites\<close>

definition given_control_sites :: "local_address option definition_site list" where
  "given_control_sites = [(None,[1]),(None,[2]),(None,[3]),(None,[4]),(None,[5])]"

definition given_control_roots :: "local_address option finite_artifact_environment \<times> local_address option" where
  "given_control_roots = finite_select_roots (finite_enumerated_environment [(None,given_control_artifact)] [])
    given_control_sites"

definition given_control_root_call :: "local_address option definition_site list \<Rightarrow> finite_factor_term" where
  "given_control_root_call ds = Finite_Pair
    (Finite_Pair (finite_environment_value (fst given_control_roots)) (finite_use_data (snd given_control_roots)))
    (Finite_Pair (Finite_Payload []) (finite_data_list (map development_site_value ds)))"

fun given_control_goal :: "(nat,nat,nat,nat) resolution_goal fset \<Rightarrow> (nat,nat,nat,nat) resolution_goal \<Rightarrow>
    nat list \<times> nat \<times> bool \<times> bool \<times> bool" where
  "given_control_goal G (Resolution_Call_Goal q r d p) = (q,d,finite_ground_call_goal (Resolution_Call_Goal q r d p),
    finite_independent_goal G (Resolution_Call_Goal q r d p), finite_leaf_call_goal (Resolution_Call_Goal q r d p))"
| "given_control_goal G (Resolution_Material_Goal q r M) = (q,fst r,False,False,False)"

definition given_control_clause_states where
  "given_control_clause_states t = fimage (\<lambda>st. (fimage (given_control_goal (resolution_pending st)) (resolution_pending st),
      case finite_resolution_select no_witness_construction finite_rooted_given_readers st of
        Select_Goals G \<Rightarrow> fimage resolution_goal_position G | _ \<Rightarrow> {||}))
    (finite_call_successors finite_rooted_given_readers (finite_initial_state 79 t) [] None 79
      (finite_exact_term_pattern t))"

lemma given_root_family_clause_control:
  "given_control_clause_states (given_control_root_call (rev given_control_sites)) =
    {|({|([0],37,False,False,True),([1],32,False,False,True),([2],59,False,False,False),([3],78,False,False,True),
        ([4],51,False,False,False),([5],59,False,False,True)|}, {|[0]|})|}"
  by eval

end
