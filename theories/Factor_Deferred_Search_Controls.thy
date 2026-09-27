theory Factor_Deferred_Search_Controls
  imports Factor_Deferred_Search Development_Given_Execution_Fixtures Native_Execution_Refinements
begin

text \<open>
  Task 926's control of the deferred search (D1b, DECISIONS.md, task 495's entry, its addition "The step at the given's
  depth"), in a theory no theory imports, evaluated once: the deferred search (@{thm [source] deferred_kept_search}'s left
  side), the shared search and R3's search computed by F2b1's indexed state (the right side of
  @{text finite_resolution_search_code}) compared at #830's three rows, 113/1, 77/1 and the given's 77 at 30 steps, and
  at a two-clause list builder at 50, 100 and 200 elements. Every compared search keeps its nodes as it defines them;
  the deferred one never substitutes a node, reading each through the store. Beside the equalities, the list builder
  counts the node records each bind reaches (the holder buckets of the variables it binds) against the depth, through
  a copy of the deferred successors whose bind notes its reach (@{text c_note}, an identity in HOL, a counter in ML).
\<close>

ML \<open>
structure DeferredControl =
struct
  val reach_max = Unsynchronized.ref 0
  val reach_sum = Unsynchronized.ref 0
  val binds = Unsynchronized.ref 0
  fun reset () = (reach_max := 0; reach_sum := 0; binds := 0)
  fun note (k : IntInf.int) =
    let val i = IntInf.toInt k
    in (reach_max := Int.max (!reach_max, i); reach_sum := !reach_sum + i; binds := !binds + 1; true) end
end
\<close>

definition c_note :: "integer \<Rightarrow> bool" where "c_note k = True"

code_printing constant c_note \<rightharpoonup> (SML) "DeferredControl.note"

section \<open>The deferred search with its binds' reach noted\<close>

definition c_reach :: "(('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> nat" where
  "c_reach s d = fcard (ffUnion (fimage (\<lambda>a. tree_bucket (deferred_holders d) (deferred_key d a)) (fset_of_list (map fst s))))"

definition c_bind :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "c_bind P s d = (if c_note (integer_of_nat (c_reach s d)) then deferred_bind P s d else deferred_bind P s d)"

definition c_successors :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) deferred_search fset" where
  "c_successors \<kappa> P d h = search_successors_with (deferred_access \<kappa> P d) (\<lambda>r. d\<lparr>deferred_inner := r\<rparr>)
    (\<lambda>q s r. c_bind P s (deferred_at q d r)) P (deferred_inner d) h"

definition c_search :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "c_search \<kappa> P n st = selected_search ((deferred_representation \<kappa> P)\<lparr>rep_successors := c_successors \<kappa> P\<rparr>)
    (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st)"

section \<open>The compared searches\<close>

fun c_dkind :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> nat" where
  "c_dkind (Resolution_Cut G) = 0"
| "c_dkind (Resolution_Stuck G) = 1"
| "c_dkind (Resolution_Witnessed B g) = 2"
| "c_dkind (Resolution_Refused C) = 3"
| "c_dkind (Resolution_Unconstructed d S a G) = 4"

definition c_light :: "('a,'s,'d,'c) resolution_outcome \<Rightarrow> integer list" where
  "c_light R = map integer_of_nat [fcard (resolution_found R), fcard (resolution_diagnoses R),
      sum (\<lambda>st. fcard (resolution_nodes st)) (fset (resolution_found R))] @
    map (\<lambda>k. if fBex (resolution_diagnoses R) (\<lambda>D. c_dkind D = k) then 1 else 0) [0,1,2,3,4]"

definition c_compare :: "(nat,nat,nat,nat) finite_witness_construction \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow>
    nat \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow> bool list \<times> integer list" where
  "c_compare \<kappa> P n st = (let
      A = indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st);
      B = selected_search (shared_representation \<kappa> P) (search_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of P st);
      C = selected_search (deferred_representation \<kappa> P) (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st);
      D = c_search \<kappa> P n st in
    ([clause_sockets_distinct P, search_placeable st, search_variables_placed st, C = A, C = B, D = C], c_light C))"

section \<open>Fixtures\<close>

text \<open>The given's 77 call, as #886's draft reads it: the given's first definition without callees, and its bound.\<close>

definition c_callees :: "local_address option finite_native_system \<Rightarrow> local_address option definition_site \<Rightarrow>
    local_address option definition_site fset" where
  "c_callees P d = ffUnion (fimage (\<lambda>((e,c),S). if e = d then fimage (\<lambda>(s,(e',p)). e') (finite_schema_premises S)
    else {||}) (finite_system_clauses P))"

definition c_given_site :: "local_address option definition_site option" where
  "c_given_site = (case finite_native_source given_environment given_use [] of None \<Rightarrow> None
    | Some P \<Rightarrow> find (\<lambda>d. c_callees P d = {||}) (sorted_list_of_fset (finite_system_definitions P)))"

definition c_given_call :: "local_address option definition_site list option \<times> finite_factor_term" where
  "c_given_call = (map_option (\<lambda>d. [d]) c_given_site, case c_given_site of None \<Rightarrow> Finite_Payload []
    | Some d \<Rightarrow> Finite_Pair (finite_environment_value given_environment) (finite_data_list [finite_site_data d]))"

definition c_77 :: "local_address option definition_site list option \<times> finite_factor_term \<Rightarrow> nat \<Rightarrow>
    bool list \<times> integer list" where
  "c_77 c n = c_compare (modes_construction (fst c) n) finite_rooted_given_readers n (finite_initial_state 77 (snd c))"

definition c_113 :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<times> integer list" where
  "c_113 m n = c_compare no_witness_construction finite_given_readers n (finite_initial_state 113 (modes_113_call m))"

text \<open>
  A two-clause list builder: @{text "mk (s N) (cons a L) \<Leftarrow> mk N L"} and @{text "mk 0 nil"}, called through
  @{text "top N \<Leftarrow> mk N L"} at a ground numeral, so every node on the branch holds the list's open tail.
\<close>

definition c_list_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "c_list_program = \<lparr>finite_system_interfaces = {|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses = {|
      ((0,0),\<lparr>finite_schema_conclusion = Finite_Variable 0,
        finite_schema_premises = {|(0,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))|},
        finite_schema_materials = {||}\<rparr>),
      ((1,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []),
        finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
      ((1,1),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Variable 0))
          (Finite_Pattern_Pair (Finite_Pattern_Payload [2]) (Finite_Variable 1)),
        finite_schema_premises = {|(0,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))|},
        finite_schema_materials = {||}\<rparr>)|}\<rparr>"

fun c_numeral :: "nat \<Rightarrow> finite_factor_term" where
  "c_numeral 0 = Finite_Payload []"
| "c_numeral (Suc k) = Finite_Pair (Finite_Payload [1]) (c_numeral k)"

definition c_list :: "nat \<Rightarrow> bool list \<times> integer list" where
  "c_list k = c_compare no_witness_construction c_list_program (k + 10) (finite_initial_state 0 (c_numeral k))"

definition c_list_reach :: "nat \<Rightarrow> integer list" where
  "c_list_reach k = c_light (c_search no_witness_construction c_list_program (k + 10) (finite_initial_state 0 (c_numeral k)))"

section \<open>The evaluation\<close>

ML \<open>
local
  val nat = @{code nat_of_integer}
  val c77 = @{code c_77}
  val c113 = @{code c_113}
  val clist = @{code c_list}
  val creach = @{code c_list_reach}
  val given = @{code c_given_call}
  val production = @{code productions_call}
  fun ints xs = "[" ^ commas (map IntInf.toString xs) ^ "]"
  fun check name (bs, light) =
    if forall I bs then writeln ("DEFERRED CONTROL " ^ name ^ ": equal " ^ ints light)
    else error ("DEFERRED CONTROL " ^ name ^ ": " ^ commas (map Bool.toString bs) ^ " " ^ ints light)
  fun reach k =
    let
      val _ = DeferredControl.reset ()
      val light = creach (nat k)
    in
      if !DeferredControl.reach_max <= IntInf.toInt k + 2 then
        writeln ("DEFERRED CONTROL list " ^ IntInf.toString k ^ ": binds " ^ string_of_int (!DeferredControl.binds) ^
          ", records reached at most " ^ string_of_int (!DeferredControl.reach_max) ^ " a bind, " ^
          string_of_int (!DeferredControl.reach_sum) ^ " in all " ^ ints light)
      else error ("DEFERRED CONTROL list " ^ IntInf.toString k ^ ": a bind reached " ^
        string_of_int (!DeferredControl.reach_max) ^ " records")
    end
in
  val _ = check "113 at 3 rows, 1500" (c113 (nat 3) (nat 1500))
  val _ = check "113/1, 400" (c113 (nat 1) (nat 400))
  val _ = check "77/1, 400" (c77 (production (nat 1)) (nat 400))
  val _ = check "the given's 77, 30" (c77 given (nat 30))
  val _ = map (fn k => check ("list " ^ IntInf.toString k) (clist (nat k))) [50, 100, 200]
  val _ = map reach [50, 100, 200]
end
\<close>

end
