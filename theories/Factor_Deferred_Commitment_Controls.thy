theory Factor_Deferred_Commitment_Controls
  imports Factor_Resolution_Checks Development_Given_Productions Development_Given_Modes Development_Given_Execution_Fixtures
    Native_Execution_Refinements "HOL-Library.Product_Lexorder"
begin

text \<open>
  Task 905's control of the route over the deferred search (D1d, DECISIONS.md, task 495's entry, its addition "The step
  at the given's depth"), in a theory no theory imports, evaluated once: at each row the route's form over the shared
  representation (@{const moded_route_with}, the body of the six kept equations), its form over the deferred
  one (@{const moded_deferred_route_with}) and the constant through its code are computed and compared whole, at the
  check form and at the committed form: 113 over #830's three-row environment (the given's checks' row 7), 77/1 and
  the given's 77 at 30 steps, over the given's rooted readers with @{const given_input_declarations},
  @{const lookup_frames} and @{const given_modes}. The code of the route constants, of R5's committed search and of
  R3's search is read from the theory's code data: each is the deferred one.
\<close>

declare [[code abort: finite_object_of union_class]]

text \<open>The given's 77 call, as #886 ran it: the given's first definition calling no other, and its bound.\<close>

definition dc_given_site :: "local_address option definition_site option" where
  "dc_given_site = (case finite_native_source given_environment given_use [] of None \<Rightarrow> None
    | Some P \<Rightarrow> find (\<lambda>d. ffUnion (fimage (\<lambda>((e,c),S). if e = d then fimage (\<lambda>(s,(e',p)). e') (finite_schema_premises S)
        else {||}) (finite_system_clauses P)) = {||}) (sorted_list_of_fset (finite_system_definitions P)))"

definition dc_call :: "nat \<Rightarrow> nat \<times> local_address option definition_site list option \<times> finite_factor_term" where
  "dc_call k = (if k = 0 then (77, map_option (\<lambda>d. [d]) dc_given_site, case dc_given_site of None \<Rightarrow> Finite_Payload []
      | Some d \<Rightarrow> Finite_Pair (finite_environment_value given_environment) (finite_data_list [finite_site_data d]))
    else if k = 7 then (113, None, modes_113_call 3)
    else (case productions_call k of (bound,t) \<Rightarrow> (77, bound, t)))"

definition dc_row :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list \<times> integer" where
  "dc_row check k n = (case dc_call k of (d,bound,t) \<Rightarrow> let \<kappa> = modes_construction bound n; P = finite_rooted_given_readers;
      D = given_input_declarations; \<Phi> = lookup_frames; Dm = resolution_declarations.truncate D; M = given_modes;
      Kc = access_narrowed_commitment P n D \<Phi>; X = finite_declared_raisers P (resolution_declarations.truncate D);
      cs = clause_sockets_distinct P; F0 = (if check then Some [] else None);
      a = moded_route_with \<kappa> P n D \<Phi> Dm M Kc X cs F0 d t n;
      b = moded_deferred_route_with \<kappa> P n D \<Phi> Dm M Kc X cs F0 d t n;
      c = (if check then moded_check_resolution \<kappa> P n D \<Phi> Dm M d t n else moded_committed_resolution \<kappa> P n D \<Phi> Dm M d t n) in
    ([cs, b = a, c = b], case finite_resolution_verdict b of None \<Rightarrow> 0 | Some True \<Rightarrow> 1 | Some False \<Rightarrow> 2))"

section \<open>The evaluation\<close>

ML \<open>
local
  val thy = @{theory}
  val ctxt = @{context}
  fun uses c d =
    let
      val eqns = the_default [] (snd (Code.equations_of_cert thy (Code.get_cert ctxt [] c)))
    in exists (fn ((_, (_, rhs)), _) => Term.exists_Const (fn (n, _) => n = d) rhs) eqns end
  val _ = (uses @{const_name finite_resolution_search} @{const_name deferred_representation} andalso
    uses @{const_name finite_committed_search} @{const_name deferred_committed_representation} andalso
    uses @{const_name moded_check_resolution} @{const_name moded_deferred_route_with} andalso
    uses @{const_name moded_committed_resolution} @{const_name moded_deferred_route_with} andalso
    uses @{const_name moded_check_demand} @{const_name moded_deferred_route_with} andalso
    uses @{const_name moded_committed_demand} @{const_name moded_deferred_route_with} andalso
    uses @{const_name native_moded_check_resolution} @{const_name moded_deferred_route_with} andalso
    uses @{const_name native_moded_committed_resolution} @{const_name moded_deferred_route_with})
    orelse error "DEFERRED COMMITMENT CONTROL: a code equation is not the deferred one"
  val _ = writeln "DEFERRED COMMITMENT CONTROL code: the deferred equations are in effect"
  val nat = @{code nat_of_integer}
  val row = @{code dc_row}
  fun check name (check, k, n) =
    let val (bs, v) = row check (nat k) (nat n) in
      if forall I bs then writeln ("DEFERRED COMMITMENT CONTROL " ^ name ^ ": equal, verdict " ^ IntInf.toString v)
      else error ("DEFERRED COMMITMENT CONTROL " ^ name ^ ": " ^ commas (map Bool.toString bs))
    end
in
  val _ = check "113 at 3 rows, check, 2000" (true, 7, 2000)
  val _ = check "113 at 3 rows, committed, 2000" (false, 7, 2000)
  val _ = check "77/1, check, 400" (true, 1, 400)
  val _ = check "77/1, committed, 400" (false, 1, 400)
  val _ = check "the given's 77, check, 30" (true, 0, 30)
end
\<close>

end
