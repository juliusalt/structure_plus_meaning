theory Development_Given_Declarations_Execution
  imports Development_Given_Productions_Execution Factor_Resolution_Checks Native_Execution_Refinements
begin

text \<open>
  The controls of the given's record (\<open>Development_Given_Carried_Declarations\<close>), each by one evaluation over the
  given's rooted readers, in a thin theory that no library theory imports.

  The first lemma evaluates, in one evaluation, calls under the committed resolution with the record, its frames
  (@{const given_narrowed_frames}) and a positive production bound: at 500 on a whole artifact of five atoms it is
  resolved; at 10 on that artifact beside the list of its atoms in reverse order it is resolved; at 10 beside a list
  missing one atom it is refuted. It states these verdicts and nothing about other calls.

  The same evaluation checks the join's claim (DECISIONS.md, "The given's one record is a keyed join"): no socket of
  the plain record stands at a key of 48's narrowed sockets, so the keyed filter keeps the plain record whole
  (@{text given_plain_declarations_unkeyed}).

  The second evaluates, at 79 over a root family of five sites, the state R3's search reaches when it expands 79's one
  clause: each pending premise with its position, its callee, and whether it is a ground call, an independent goal
  and a leaf call (the classes @{const finite_goal_selection} orders by), and the positions R3's selection takes
  there.

  The third evaluates 55's two-union clause at K2's check form, at the moded selection with the given's modes and
  I3a's input record (@{text given_union_control}): true calls resolved and a false call refuted at 55's pair clause,
  #519's counterexample among the cases, and the goals at 48 the search meets, none committed with its production.
\<close>

text \<open>
  The instantiation family's socket schemas are written through @{const finite_pattern_of}, whose target leaves go
  through @{const finite_object_of}, which has no code; none of those schemas holds a target, so that branch is never
  reached, and it aborts in code, as in @{text Development_Socket_Liveness_Execution}.
\<close>

declare [[code abort: finite_object_of union_class]]

definition given_control_artifact :: finite_exact_artifact where
  "given_control_artifact = \<lparr>finite_structure = \<lparr>finite_carrier = {|[1],[2],[3],[4],[5]|}, finite_incidence = {||}\<rparr>,
    finite_data = \<lparr>finite_bag = {#}, finite_bindings = {||}\<rparr>\<rparr>"

definition given_control_rows :: "local_address list \<Rightarrow> finite_factor_term" where
  "given_control_rows A = Finite_Pair (finite_data_list (map Finite_Payload A))
    (Finite_Pair (finite_data_list []) (Finite_Pair (finite_data_list []) (finite_data_list [])))"

abbreviation given_control_resolution :: "nat \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "given_control_resolution n d t \<equiv> finite_resolution_verdict (finite_committed_resolution no_witness_construction
    (finite_narrowed_commitment finite_rooted_given_readers 20 given_declarations given_narrowed_frames)
    finite_rooted_given_readers d t n)"

lemma given_declarations_control:
  "given_control_resolution 40 500 (Finite_Target (Finite_Whole given_control_artifact)) = Some True \<and>
   given_control_resolution 40 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[5],[4],[3],[2],[1]])) = Some True \<and>
   given_control_resolution 40 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[1],[2],[3],[4]])) = Some False \<and>
   fBall (declared_sockets given_plain_declarations) (\<lambda>(e,S,s,rest).
    \<not> socket_keyed (resolution_declarations.truncate (union_produced given_union_sockets)) e S s)"
  by eval

lemma given_plain_declarations_unkeyed:
  "unkeyed_declarations (resolution_declarations.truncate (union_produced given_union_sockets)) given_plain_declarations =
    given_plain_declarations"
proof -
  have keep: "ffilter (\<lambda>(e,S,s,rest). \<not> socket_keyed (resolution_declarations.truncate (union_produced given_union_sockets))
      e S s) (declared_sockets given_plain_declarations) = declared_sockets given_plain_declarations"
    using conjunct2[OF conjunct2[OF conjunct2[OF given_declarations_control]]]
    by (auto intro!: fset_eqI)
  show ?thesis unfolding unkeyed_declarations_def keep by simp
qed

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

section \<open>55's two-union clause at the check form\<close>

text \<open>
  A pattern quoted in an environment (@{const finite_pattern_syntax} at the binder coordinates of \<open>{x0,x1}\<close>, at use
  @{term None}) and a call of 55 at its root: the scope x0,x1, x0 bound to [7] and x1 to [8], the instance, the used
  variables, the interior (every position of the quoted pair, in an order no join computes) and no external slot. At
  depth 1 the pattern is (x0,x1); at depth 2 ((x0,x1),x0), whose pair clause calls 55 again on the inner pair, the
  inner call's used variables and interior premise-only outputs of 48 at the clause's narrowed sockets. The used
  variables stand as x1,x0, the order the production does not choose (#519's counterexample, a commitment refuting a
  true call), and at depth 1 also as x0,x1.
\<close>

definition given_union_pattern :: "nat \<Rightarrow> nat finite_term_pattern" where
  "given_union_pattern k = (if k = 1 then Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)
    else Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 0))"

definition given_union_binder :: "nat \<Rightarrow> local_address" where
  "given_union_binder = finite_binder_coordinates {|0,1|}"

definition given_union_environment :: "nat \<Rightarrow> local_address option finite_artifact_environment" where
  "given_union_environment k =
    finite_enumerated_environment [(None,finite_pattern_syntax given_union_binder (given_union_pattern k))] []"

definition given_union_payloads :: "local_address list \<Rightarrow> finite_factor_term" where
  "given_union_payloads A = finite_data_list (map Finite_Payload A)"

definition given_union_interior :: "nat \<Rightarrow> local_address list" where
  "given_union_interior k = (if k = 1 then [[3],[1],[2],[],[0]] else [[3],[2,3],[1],[2],[2,0],[],[2,2],[0],[2,1]])"

definition given_union_call :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat list \<Rightarrow> finite_factor_term" where
  "given_union_call k t ws = Finite_Pair
    (Finite_Pair (finite_environment_value (given_union_environment k)) (finite_use_data None))
    (Finite_Pair (Finite_Payload [])
      (Finite_Pair (Finite_Pair (given_union_payloads [given_union_binder 0,given_union_binder 1])
          (finite_data_list [Finite_Pair (Finite_Payload (given_union_binder 0)) (Finite_Payload [7]),
            Finite_Pair (Finite_Payload (given_union_binder 1)) (Finite_Payload [8])]))
        (Finite_Pair t (Finite_Pair (given_union_payloads (map given_union_binder ws))
          (Finite_Pair (given_union_payloads (given_union_interior k)) (given_union_payloads []))))))"

text \<open>The true instances, and a false one at each depth (the instance's last leaf [8] for [7] at depth 2).\<close>

definition given_union_true :: "nat \<Rightarrow> nat list \<Rightarrow> finite_factor_term" where
  "given_union_true k ws = given_union_call k (if k = 1 then Finite_Pair (Finite_Payload [7]) (Finite_Payload [8])
    else Finite_Pair (Finite_Pair (Finite_Payload [7]) (Finite_Payload [8])) (Finite_Payload [7])) ws"

definition given_union_false :: "nat \<Rightarrow> finite_factor_term" where
  "given_union_false k = given_union_call k (if k = 1 then Finite_Pair (Finite_Payload [8]) (Finite_Payload [8])
    else Finite_Pair (Finite_Pair (Finite_Payload [7]) (Finite_Payload [8])) (Finite_Payload [8])) [1,0]"

text \<open>
  The check form (K2's @{const moded_check_resolution}: the search started at the root's own focus) at the moded
  selection with @{const given_modes}, under the narrowed commitment of the given's input record
  (@{const given_input_declarations}) at its frames (@{const given_input_frames}), production bound m.
\<close>

abbreviation given_union_commitment :: "nat \<Rightarrow> (nat,nat,nat,nat) resolution_commitment" where
  "given_union_commitment m \<equiv> finite_narrowed_commitment finite_rooted_given_readers m given_input_declarations
    given_input_frames"

definition given_union_check :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "given_union_check m t n = finite_resolution_verdict (moded_check_resolution no_witness_construction
    finite_rooted_given_readers m given_input_declarations given_input_frames
    (resolution_declarations.truncate given_input_declarations) given_modes 55 t n)"

text \<open>
  The goals at 48 the check form's search selects, each with its position and whether it is committed with its
  production defined there: the union produced (@{const committed_trace} at this probe).
\<close>

fun given_union_probe :: "(nat,nat,nat,nat) resolution_commitment \<Rightarrow> nat list option \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_goal \<Rightarrow> (nat list \<times> bool) fset" where
  "given_union_probe K F st (Resolution_Call_Goal q r e p) = (if e = 48 then
    {|(q, finite_goal_committing K F st (Resolution_Call_Goal q r e p) \<and>
      commit_production K F st (Resolution_Call_Goal q r e p) \<noteq> None)|} else {||})"
| "given_union_probe K F st (Resolution_Material_Goal q r M) = {||}"

definition given_union_trace :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> (nat list \<times> bool) list" where
  "given_union_trace m t n = (let K = given_union_commitment m in
    sorted_list_of_fset (committed_trace (given_union_probe K)
      (finite_moded_select no_witness_construction K (resolution_declarations.truncate given_input_declarations)
        given_modes finite_rooted_given_readers)
      no_witness_construction K finite_rooted_given_readers n (Some []) {||} (finite_initial_state 55 (t))))"

text \<open>
  The rows, in one evaluation. At depth 1 the true call is resolved at 500 with its used variables in either order, and
  the false call is refuted there (the counted search: 1,645 and 1,598 states; the committed form at @{term None}, 4,621
  states unresolved at 300, returns nothing at 500 within a held run, nor R4). At depth 2 the true call is resolved at
  1500 (4,437 states). A commitment refuting the true call with the unchosen order, #519's counterexample, does not
  arise. The union is not produced: at depth 2 the search selects the goals at 55's sockets 7 and 8, the outer call's
  and the inner call's ([2,7], [2,8]), and a goal at 48 under the inner call's premise 1, and none is committed with
  its production (the trace at 800); the unions are searched. The false call at depth 2 is unresolved at 800 and not
  returned at 1500 within a held run: it is not a row here (investigation #896).
\<close>

lemma given_union_control:
  "given_union_check 20 (given_union_true 1 [1,0]) 500 = Some True \<and>
   given_union_check 20 (given_union_true 1 [0,1]) 500 = Some True \<and>
   given_union_check 20 (given_union_false 1) 500 = Some False \<and>
   given_union_check 20 (given_union_true 2 [1,0]) 1500 = Some True \<and>
   given_union_trace 20 (given_union_true 2 [1,0]) 800 =
    [([2,1,7],False),([2,7],False),([2,8],False),([7],False),([8],False)]"
  by eval

end
