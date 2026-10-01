theory Development_First_Problem_Additions_Controls
  imports Development_First_Problem_Additions_Fixtures Development_Given_Productions Factor_Resolution_Checks
    Factor_Shared_Resolution Factor_Shared_Commitments Factor_Shared_Search Factor_Indexed_Resolution
    Factor_Resolution_Graph_Checks Native_Execution_Refinements
begin

text \<open>
  The controls of the asked relation over additions (task 938, AX3b), over the small given and its candidates of
  @{text Development_First_Problem_Additions_Fixtures}: at the numbered asked program over additions
  (@{const finite_asked_additions_program}), the guard over additions (990) and each of its four sockets (980 the
  extension's formation, 981 the package at the candidate's site, 985 the callee boundary, 989 the octet audit) at
  the pair of the given's site value and the additions value; beside them the guard over site values (526) at the
  pair of the given's and the candidate's site values at the numbered asked program (@{const finite_asked_program}).
  Each call at the check form (@{const moded_check_resolution}, the search started at the root's own focus) with the
  given's input record (@{const given_input_declarations}, @{const given_input_frames}) and modes
  (@{const given_modes}), read at both programs by their agreement with the given's readers, the construction the
  given's registrations (@{const given_witness_registrations}); no witness is handed in. Each call is reported with
  its verdict, its diagnoses' kinds, the states of the committed search at the check form's focus
  (@{const committed_search_states}) and R4's verdict (@{const finite_program_resolution}) beside. One evaluation,
  compiled once over the refinement collection in effect; no theory imports this one.

  What it reports at bound 100 (task 938's run): every call unresolved, its only diagnoses cuts at the bound, at both
  programs and in every case, R4's verdict unresolved beside each; under 1.5 s a call. The committed search at the
  check form visits 101 to 375 states a call: at no additions 113 at 980, 254 at 981, 256 at 985 and at 989, 105 at
  990 and 104 at 526; at the extended candidates 101 at 980, 990 and 526, 222 to 229 at 981, 234 to 243 at 985 and
  989; at the added use the given holds 350 at 981 and 375 at 985 and 989. At bound 200 the same calls were cut at
  200 to 1,411 states, and the added use the given holds took 4,862 states and 52 s at 981; at no additions 980 at
  bound 600 did not return within the 180 s a probe allows. The construction hands in no
  witness: the premise-only witnesses of 957, 960, 961 and of 985's and 989's members clauses are produced by AX2b's
  registrations and the least environment's production, not by the given's four registrations; and the refusals
  through a registration are AX5's, at VK2's committing instance. Each case reports its socket by its own call.
\<close>

declare [[code abort: finite_object_of union_class]]

definition additions_control_kinds :: "(nat,nat,nat,nat) finite_resolution_result \<Rightarrow> integer list" where
  "additions_control_kinds R=(case R of Finite_Unresolved D \<Rightarrow>
      map integer_of_nat (sorted_list_of_fset (fimage modes_diagnosis_kind D)) | _ \<Rightarrow> [])"

definition additions_control_report :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow>
    bool option\<times>integer list\<times>integer\<times>bool option" where
  "additions_control_report P d t n=(let \<kappa>=finite_collection_construction given_witness_registrations n;
    D=given_input_declarations; \<Phi>=given_input_frames; Dm=resolution_declarations.truncate D;
    K=finite_narrowed_commitment P n D \<Phi>; sel=finite_moded_select \<kappa> K Dm given_modes P;
    R=moded_check_resolution \<kappa> P n D \<Phi> Dm given_modes d t n in
    (finite_resolution_verdict R,additions_control_kinds R,
      integer_of_nat (committed_search_states sel \<kappa> K P n (Some []) {||} (finite_initial_state d t)),
      finite_resolution_verdict (finite_program_resolution \<kappa> P d t n)))"

ML \<open>
local
  val cases = @{code additions_fixture_cases}
  val report = @{code additions_control_report}
  val new_program = @{code finite_asked_additions_program}
  val old_program = @{code finite_asked_program}
  val pair = @{code Finite_Pair}
  val nat = @{code nat_of_integer}
  val bound = nat 100
  fun verdict NONE = "unresolved" | verdict (SOME true) = "holds" | verdict (SOME false) = "refuted"
  fun show (v, (ks, (s, r4))) = verdict v ^ ", kinds [" ^ String.concatWith "," (map IntInf.toString ks) ^
    "], states " ^ IntInf.toString s ^ ", R4 " ^ verdict r4
  fun run label prog d t =
    let val (time, r) = Timing.timing (fn () => report prog (nat d) t bound) ()
    in writeln ("ADDITIONS CONTROL " ^ label ^ ": " ^ show r ^ " (" ^ Timing.message time ^ ")") end
  fun control (name, (t, (a, w))) =
    (List.app (fn d => run (name ^ " at " ^ IntInf.toString d) new_program d (pair (t, a))) [980, 981, 985, 989, 990];
     run (name ^ " at the guard over site values, 526") old_program 526 (pair (t, w)))
in
  val _ = List.app control cases
end
\<close>

end
