theory Factor_Material_Reading_Controls
  imports Development_Given_Program Factor_Resolution_Commitments Factor_Finite_Closed_Installation
    Factor_Finite_Mapped_Extensions Factor_Finite_Artifact_Value_Readers Native_Execution_Refinements
begin

text \<open>
  The control of R1's corrected skeleton reading (task 808, RD1 of task 790's section in task 496's entry), imported by
  no library theory. 11, artifact admission, is resolved alone over the given's rooted readers by R5's committed
  resolution at no declaration and no construction and at R5's own selection: its target, premise-only in 11's clause,
  is produced by 10's material premise, whose skeleton the data lays out and whose source it binds, with no
  registration. A wrong leaf dies where it is laid: an entry of the skeleton with no reading makes the skeleton
  unreadable, and the material goal has no solution, whatever the skeleton or the source still leaves open.
\<close>

declare [[code abort: finite_object_of]]

section \<open>A wrong leaf is refused where it is laid\<close>

text \<open>
  The atoms field's first entry is a payload where an atom's entry (an address paired with an anchor) must stand: it
  has no reading under any substitution. The rest of the skeleton and the source are open, so the reading before
  RD1 left the goal waiting; it has no solution.
\<close>

definition reading_control_wrong_leaf :: "nat finite_material_pattern" where
  "reading_control_wrong_leaf = \<lparr>finite_material_source=Finite_Variable 0,
    finite_material_atoms=Finite_Pattern_Pair (Finite_Pattern_Payload [2]) (Finite_Variable 1),
    finite_material_edges=Finite_Variable 2, finite_material_counts=Finite_Variable 3,
    finite_material_functions=Finite_Variable 4\<rparr>"

lemma reading_control_wrong_leaf_refused:
  "finite_enumeration_pattern_read (finite_incidence_entry (finite_atom_entries
      (finite_material_atoms reading_control_wrong_leaf))) (finite_material_edges reading_control_wrong_leaf) = Open_Reading"
  "finite_pattern_variables (finite_material_source reading_control_wrong_leaf) \<noteq> {||}"
  "finite_material_resolution reading_control_wrong_leaf = Material_Solutions {||}"
  by (simp_all add: reading_control_wrong_leaf_def finite_material_resolution_unreadable_field finite_atom_entry_def
    ground_reading_def)

section \<open>11 alone at chain artifacts and at the 18-address artifact of 77/1's environment\<close>

text \<open>
  A chain artifact of k addresses [1], \<dots>, [k] and the k - 1 incidence rows ([i],[i],[i+1]), as task 790's draft
  builds it; the 18-address artifact is the one of that size in the environment the one-fact program of 77/1 is
  installed in, its data read from the environment's presented value.
\<close>

definition reading_control_chain :: "nat \<Rightarrow> finite_exact_artifact" where
  "reading_control_chain k = \<lparr>finite_structure = \<lparr>finite_carrier = fset_of_list (map (\<lambda>i. [i]) [1..<Suc k]),
    finite_incidence = fset_of_list (map (\<lambda>i. ([i],[i],[Suc i])) [1..<k])\<rparr>,
    finite_data = \<lparr>finite_bag = {#}, finite_bindings = {||}\<rparr>\<rparr>"

definition reading_control_fact_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "reading_control_fact_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [],
      finite_schema_premises={||}, finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition reading_control_environment :: "local_address option finite_artifact_environment" where
  "reading_control_environment = (case finite_extend_mapped_native (fst empty_package_selection)
      empty_installation_program reading_control_fact_program (\<lambda>_. (None,[])) of
    Some (K,v) \<Rightarrow> K | None \<Rightarrow> finite_empty_environment)"

definition reading_control_large :: finite_factor_term where
  "reading_control_large = (case finite_environment_value reading_control_environment of
      Finite_Pair A B \<Rightarrow> (case finite_data_list_read A of
          Some rows \<Rightarrow> (case filter (\<lambda>t. case finite_artifact_value_read t of
              Some C \<Rightarrow> fcard (finite_carrier (finite_structure C)) = 18 | None \<Rightarrow> False)
            (map (\<lambda>r. case r of Finite_Pair u d \<Rightarrow> d | t \<Rightarrow> t) rows) of t # ts \<Rightarrow> t | [] \<Rightarrow> Finite_Payload [])
        | None \<Rightarrow> Finite_Payload [])
    | t \<Rightarrow> t)"

text \<open>
  The resolution is R5's at a selection that counts the states it is asked at: @{text tk} is called once for each
  state the search selects at and never changes the selection, so the counted resolution is R5's committed resolution
  itself (@{text reading_control_counted_exact}).
\<close>

definition reading_control_counted ::
    "(unit \<Rightarrow> bool) \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) finite_resolution_result" where
  "reading_control_counted tk t n = finite_committed_resolution_by (\<lambda>st. if tk () then
      finite_committed_select no_witness_construction (finite_declared_commitment no_declarations)
        finite_rooted_given_readers st
      else finite_committed_select no_witness_construction (finite_declared_commitment no_declarations)
        finite_rooted_given_readers st)
    no_witness_construction (finite_declared_commitment no_declarations) finite_rooted_given_readers 11 t n"

lemma reading_control_counted_exact:
  "reading_control_counted tk t n = finite_committed_resolution no_witness_construction
    (finite_declared_commitment no_declarations) finite_rooted_given_readers 11 t n"
  by (simp add: reading_control_counted_def finite_committed_resolution_select)

text \<open>
  The report of a call: its verdict (1 resolved, 0 refuted, 2 unresolved), its certificates and whether every one is
  accepted by the checker at the call.
\<close>

definition reading_control_report :: "(unit \<Rightarrow> bool) \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> nat list" where
  "reading_control_report tk t n = (case reading_control_counted tk t n of
      Finite_Resolved C \<Rightarrow> [1, fcard C,
        if fBall C (\<lambda>p. finite_checks_schema_proof finite_rooted_given_readers p 11 t) then 1 else 0]
    | Finite_Refuted \<Rightarrow> [0,0,0] | Finite_Unresolved D \<Rightarrow> [2,0,0])"

definition reading_control_chain_value :: "nat \<Rightarrow> finite_factor_term" where
  "reading_control_chain_value k = finite_artifact_value (reading_control_chain k)"

ML \<open>
local
  val report = @{code reading_control_report}
  val chain = @{code reading_control_chain_value}
  val large = @{code reading_control_large}
  val nat = @{code nat_of_integer} o IntInf.fromInt
  val int_of = IntInf.toInt o @{code integer_of_nat}
  fun run (name, t) =
    let
      val states = Unsynchronized.ref 0
      fun tk () = (states := !states + 1; true)
      val t0 = Timing.start ()
      val r = map int_of (report tk t (nat 3000))
      val tm = Timing.result t0
    in (name, r, !states, tm) end
  val calls = map (fn k => ("chain k=" ^ Int.toString k, chain (nat k))) [1, 2, 3, 8] @ [("77/1's 18-address", large)]
  val results = map run calls
  fun line (name, r, s, tm) =
    "READING CONTROL " ^ name ^ ": verdict/certificates/checked " ^ commas (map Int.toString r) ^
      ", states " ^ Int.toString s ^ ", " ^ Timing.message tm
in
  val _ = List.app (writeln o line) results
  val _ = if forall (fn (_, r, _, _) => (case r of [1, c, 1] => c > 0 | _ => false)) results then ()
    else error ("Reading control failed: " ^ space_implode "; " (map line results))
end
\<close>

end
