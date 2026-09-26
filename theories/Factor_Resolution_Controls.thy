theory Factor_Resolution_Controls
  imports Factor_Material_Resolution Factor_Distinct_Payloads Factor_Substitution Factor_Resolution_Completeness
    Factor_Executed_Controls Factor_Resolution_Commitments
begin

text \<open>
  The resolver's controls, one lemma proved by one evaluation; no library theory imports this theory.

  Site 1 concludes its payload list from the premise of site 0 at the pair of its variables 1 and 0 and
  the material premise @{const distinct_payloads_material}. At a ground list of payloads, resolving site
  0 by its two clauses binds variable 1 to the enumeration of the pairs of each payload and a fresh
  variable; those fresh variables are 3, 4, \<dots> here. The material premise's fields are then the
  pattern below, whose decoding is @{const distinct_payloads_material} with its variable 1 replaced by
  that enumeration pattern, and its skeleton is ground.
\<close>

definition site_one_atoms :: "octets list \<Rightarrow> nat finite_term_pattern" where
  "site_one_atoms as = foldr (\<lambda>(i,a) p. Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable (3+i))) p)
    (zip [0..<length as] as) (Finite_Pattern_Target (Finite_Whole finite_empty_artifact))"

definition site_one_material :: "octets list \<Rightarrow> nat finite_material_pattern" where
  "site_one_material as = \<lparr>finite_material_source=Finite_Variable 2, finite_material_atoms=site_one_atoms as,
    finite_material_edges=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_counts=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_functions=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)\<rparr>"

lemma site_one_material_decoded:
  "decode_finite_material (site_one_material as) =
    material_pattern_substitute (\<lambda>v. if v=1 then decode_finite_pattern (site_one_atoms as) else Pattern_Variable v)
      distinct_payloads_material"
  by (simp add: site_one_material_def decode_finite_material_def distinct_payloads_material_def
    material_pattern_substitute_def)

text \<open>
  A finite presentation of the three clauses of @{const distinct_payloads_system}, proved to decode to it, so that
  site 1 is resolved end to end over the program's own clauses.
\<close>

definition finite_distinct_payloads_material :: "nat finite_material_pattern" where
  "finite_distinct_payloads_material = \<lparr>finite_material_source=Finite_Variable 2,
    finite_material_atoms=Finite_Variable 1,
    finite_material_edges=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_counts=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
    finite_material_functions=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)\<rparr>"

definition finite_distinct_payloads_system :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_distinct_payloads_system = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|
      ((0,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Pattern_Target (Finite_Whole finite_empty_artifact))
          (Finite_Pattern_Payload []), finite_schema_premises={||}, finite_schema_materials={||}\<rparr>),
      ((0,1),\<lparr>finite_schema_conclusion=Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2))
          (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3)),
        finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
        finite_schema_materials={||}\<rparr>),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Variable 0,
        finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 0)))|},
        finite_schema_materials={|(1,finite_distinct_payloads_material)|}\<rparr>)|}\<rparr>"

lemma finite_distinct_payloads_decoded: "decode_finite_system finite_distinct_payloads_system = distinct_payloads_system"
  by (simp add: finite_distinct_payloads_system_def distinct_payloads_system_def carrier_projection_empty_schema_def
    carrier_projection_cons_schema_def distinct_payloads_schema_def distinct_payloads_material_def
    finite_distinct_payloads_material_def decode_finite_schema_def decode_finite_material_def map_relation_values_def
    decode_finite_call_pattern_def)

abbreviation control_payload_list :: "octets list \<Rightarrow> finite_factor_term" where
  "control_payload_list as \<equiv> foldr (\<lambda>a t. Finite_Pair (Finite_Payload a) t) as (Finite_Payload [])"

text \<open>
  E1's control program (@{const implemented_base_control}): its root (None,[3]) holds of a term where the witness
  (None,[2]) does, and the witness's clause has the premise-only variable [1], which the plain evaluator leaves
  unanswered (@{thm [source] implemented_base_control_plain}). The resolver resolves the root call and constructs
  the witness: the certificate's node at the witness binds [1] to the empty payload.
\<close>

definition control_witness_bound :: "native_resolution_result \<Rightarrow> bool" where
  "control_witness_bound r = (case r of Finite_Resolved C \<Rightarrow> fBex C (\<lambda>p. case p of Schema_Proof c V B \<Rightarrow>
      fBex B (\<lambda>(s,q). case q of Schema_Proof c' V' B' \<Rightarrow> ([1],Finite_Payload []) |\<in>| V'))
    | _ \<Rightarrow> False)"

text \<open>
  At [[1],[2]] the premise has one solution: the source is the whole artifact with carrier {[1],[2]}, no
  incidence and no data, and each fresh variable its occurrence. At [[1],[1]] it has none, the addresses
  not being distinct. At the empty list its solution is the empty artifact. At [[1]] with its edges
  field a payload, the skeleton holds no variable and has no reading: no solution, whatever the source.
  Resolved end to end over the finite presentation of the program, site 1 resolves [[1],[2]] and the empty list
  and refutes [[1],[1]]; E1's root call is resolved with its witness constructed. One evaluation compiles the
  resolver once for all of them.
\<close>

text \<open>
  The commitment's control (R5, @{text Factor_Resolution_Commitments}): a selection (site 0) of an element from a
  data list, its call pairing the list with the element and the remainder; a permutation (site 1), presentation-free
  at its output, whose clause selects the head and permutes the remainder; and a check (site 2) that a list is a
  permutation of another, through an intermediate permutation that the permutation site consumes at its left side.
  The permutation is declared a producer, its left side a consumer of it, and the selection's socket in the
  permutation's clause an inner commitment inside a focus. At a list of n distinct elements R4 keeps each of the n!
  intermediate permutations, each a certificate; the committed resolution keeps one at every commitment: one
  certificate at n = 4 and at n = 6, and at n = 6 it refutes a list that is not a permutation. R4 refutes that list
  too, and its exactness makes the refutation the program's meaning (@{text commitment_control_refuted}); the
  committed exactness's premise is discharged by the tasks continuing 586 (DECISIONS.md, task 495's entry, its
  correction (4)).
\<close>

definition commitment_selection_here :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_selection_here = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)),
    finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition commitment_selection_later :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_selection_later = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))),
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 2)
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3))))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_permutation_nil :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_permutation_nil = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Pattern_Payload [])
      (Finite_Pattern_Payload []), finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition commitment_permutation_cons :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_permutation_cons = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)),
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_control_check :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_control_check = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 1)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "commitment_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),commitment_permutation_cons),((2,0),commitment_control_check)|}\<rparr>"

definition commitment_control_declarations :: "(nat,nat,nat) resolution_declarations" where
  "commitment_control_declarations = \<lparr>declared_producers={|1|}, declared_consumers={|(1,1,False)|},
    declared_sockets={|(1,commitment_permutation_cons,0,False)|}\<rparr>"

abbreviation commitment_control_call :: "octets list \<Rightarrow> octets list \<Rightarrow> finite_factor_term" where
  "commitment_control_call as bs \<equiv> Finite_Pair (control_payload_list as) (control_payload_list bs)"

definition commitment_certificates :: "(nat,nat,nat,nat) finite_resolution_result \<Rightarrow> nat" where
  "commitment_certificates r = (case r of Finite_Resolved C \<Rightarrow> fcard C | _ \<Rightarrow> 0)"

text \<open>
  The exchange control (review 519, finding 1): a socket declared without the kept head below the focus root. Sites 0
  and 1 are the selection and the permutation above; site 3, p(X,rs) :- sel(X,(r,S')), perm(S',rs), its selection
  socket declared without the kept head; site 4, G(X,[]) :- p(X,[a]), a producer with one answer at every input;
  site 5, c(Pair x y), a fact of every formed pair, G's consumer at its right side; site 6,
  root(X) :- G(X,W), c(Pair X W). Every declaration is discharged, and root([[1],[2]]) holds (r=[2], S'=[[1]]). A
  commitment of the selection inside G's focus keeps its least answer ([1],[[2]]) and perm([[2]],[[1]]) fails: the
  socket's parent is not the focus root, so the test does not commit it and the committed resolution resolves the
  call, as R4 does.
\<close>

definition commitment_exchange_select :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_exchange_select = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3),
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_exchange_functional :: "octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "commitment_exchange_functional a = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Payload []),
    finite_schema_premises={|(0,(3,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Pattern_Payload []))))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_exchange_consumer :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_exchange_consumer = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition commitment_exchange_root :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_exchange_root = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(4,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))),
      (1,(5,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_exchange_program :: "octets \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "commitment_exchange_program a = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (3,Finite_Variable 0),(4,Finite_Variable 0),(5,Finite_Variable 0),(6,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),commitment_permutation_cons),((3,0),commitment_exchange_select),
      ((4,0),commitment_exchange_functional a),((5,0),commitment_exchange_consumer),((6,0),commitment_exchange_root)|}\<rparr>"

definition commitment_exchange_declarations :: "(nat,nat,nat) resolution_declarations" where
  "commitment_exchange_declarations = \<lparr>declared_producers={|4|}, declared_consumers={|(4,5,True)|},
    declared_sockets={|(3,commitment_exchange_select,0,False)|}\<rparr>"

text \<open>
  The variant control (review 519's second shape): q(X) :- perm(X,[V|[a|W]]), c(Pair X [V|[a|W]]), the permutation a
  producer whose selection socket is declared without the kept head, c its consumer at the right side. The output
  q's clause gives the permutation is constrained, not a variant of the permutation clause's head output, so the
  socket is not committed under it: at a=[1] over [[1],[2]] the committed resolution resolves the call as R4 does,
  and at a=[3] both refute it.
\<close>

definition commitment_variant_root :: "octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "commitment_variant_root a = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable 2))))),
      (1,(5,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable 2)))))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_variant_program :: "octets \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "commitment_variant_program a = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (5,Finite_Variable 0),(7,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),commitment_permutation_cons),((5,0),commitment_exchange_consumer),
      ((7,0),commitment_variant_root a)|}\<rparr>"

definition commitment_variant_declarations :: "(nat,nat,nat) resolution_declarations" where
  "commitment_variant_declarations = \<lparr>declared_producers={|1|}, declared_consumers={|(1,5,True)|},
    declared_sockets={|(1,commitment_permutation_cons,0,False)|}\<rparr>"

text \<open>
  The sibling control, the counterexample to #565's exchange premise at a socket (task 586; DECISIONS.md, task 495's
  entry, correction (4)): site 3, c(X) :- r(Z), prod(Pair X Y), cons(Pair Z Y), over the facts r(z1), r(z2),
  prod(x,a), prod(x,b), cons(z1,a), cons(z2,b) (x the empty payload, z1 = [1], z2 = [2]), prod's socket declared with
  the kept head. The declaration is discharged: each answer of prod at x extends a true instance of the clause with
  the head kept. At the supported state where r was resolved first with z2, the kept answer a = [3] leaves cons(z2,a)
  false: no kept state is supported, so the premise, quantified over every supported state, fails. The verdict
  survives here because R3's selection, one goal per state, takes prod first at c's clause (its pattern the one call
  holding a leaf), where the premise holds, r's goal still pending: the committed resolution resolves c(x); where
  r(z1) holds only through c(x), its branch reaches the root's call, barred at the commitment, and the call is left
  unresolved, never refuted.
\<close>

definition commitment_fact :: "nat finite_term_pattern \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "commitment_fact p = \<lparr>finite_schema_conclusion=p, finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition commitment_sibling_clause :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_sibling_clause = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(0,Finite_Variable 1)),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))),
      (2,(2,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_sibling_loop :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_sibling_loop = \<lparr>finite_schema_conclusion=Finite_Pattern_Payload [1],
    finite_schema_premises={|(0,(3,Finite_Pattern_Payload []))|}, finite_schema_materials={||}\<rparr>"

definition commitment_sibling_program :: "octets \<Rightarrow> octets \<Rightarrow> bool \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "commitment_sibling_program a b l = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_fact (Finite_Pattern_Payload [2])),
      ((0,1),if l then commitment_sibling_loop else commitment_fact (Finite_Pattern_Payload [1])),
      ((1,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload a))),
      ((1,1),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload b))),
      ((2,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Pattern_Payload a))),
      ((2,1),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [2]) (Finite_Pattern_Payload b))),
      ((3,0),commitment_sibling_clause)|}\<rparr>"

definition commitment_sibling_declarations :: "(nat,nat,nat) resolution_declarations" where
  "commitment_sibling_declarations = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(3,commitment_sibling_clause,1,True)|}\<rparr>"

text \<open>
  The order control (task 589): the sibling control's clause with r's call holding a leaf, c(X) :- r(Pair [] Z),
  prod(Pair X Y), cons(Pair Z Y), over r([],z2), r([],z1) :- c(x) and prod's and cons' facts, prod's socket declared
  with the kept head and discharged. R3's selection takes r first, a leaf-bearing call at the lower position; its
  branch z1 reaches the root's call, pruned under the unbarred root. Had prod been committed in branch z2, its kept
  answer a would leave cons(z2,a) false and the true call c(x) refuted; the socket is committed only while its
  siblings are pending (@{const finite_siblings_pending}), so it is searched plainly and resolved as by R4.
\<close>

definition commitment_order_clause :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_order_clause = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 1))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))),
      (2,(2,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))|},
    finite_schema_materials={||}\<rparr>"

definition commitment_order_loop :: "(nat,nat,nat) finite_factor_schema" where
  "commitment_order_loop = \<lparr>finite_schema_conclusion=
      Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [1]),
    finite_schema_premises={|(0,(3,Finite_Pattern_Payload []))|}, finite_schema_materials={||}\<rparr>"

definition commitment_order_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "commitment_order_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0)|},
    finite_system_clauses={|
      ((0,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [2]))),
      ((0,1),commitment_order_loop),
      ((1,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [3]))),
      ((1,1),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [4]))),
      ((2,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Pattern_Payload [3]))),
      ((2,1),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [2]) (Finite_Pattern_Payload [4]))),
      ((3,0),commitment_order_clause)|}\<rparr>"

definition commitment_order_declarations :: "(nat,nat,nat) resolution_declarations" where
  "commitment_order_declarations = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(3,commitment_order_clause,1,True)|}\<rparr>"

text \<open>
  The material control (task 621, #593's first counterexample): p(x) :- mat(C;A,E,B,F), q(Pair A E), over an artifact
  C of two atoms and no incidence, q(Pair A_o E) a fact at the enumeration A_o of C's atoms that is not the canonical
  one and q(Pair A_c E) :- p(x) at the canonical A_c, the material socket declared with the kept head. Under the
  former rule a committed material premise kept the barred set: after the commitment q(A_c)'s one derivation reached
  p(x), a ground goal equal to the unbarred root's call, pruned, and the true call was refuted. Under the one barring
  rule the root is barred at the commitment and the branch ends in a cut: the call is unresolved, never refuted, and
  R4 resolves it.
\<close>

abbreviation material_control_artifact :: finite_exact_artifact where
  "material_control_artifact \<equiv> finite_enumerated_artifact [[1],[2]] [] [] []"

definition material_control_answer :: "local_address list \<Rightarrow> nat finite_term_pattern" where
  "material_control_answer as = finite_exact_term_pattern (Finite_Pair
    (finite_enumeration_term (map (finite_atom_term material_control_artifact) as)) (finite_enumeration_term []))"

definition material_control_clause :: "(nat,nat,nat) finite_factor_schema" where
  "material_control_clause = \<lparr>finite_schema_conclusion=Finite_Pattern_Payload [],
    finite_schema_premises={|(1,(0,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))|},
    finite_schema_materials={|(0,\<lparr>finite_material_source=Finite_Pattern_Target (Finite_Whole material_control_artifact),
      finite_material_atoms=Finite_Variable 1, finite_material_edges=Finite_Variable 2,
      finite_material_counts=Finite_Variable 3, finite_material_functions=Finite_Variable 4\<rparr>)|}\<rparr>"

definition material_control_loop :: "(nat,nat,nat) finite_factor_schema" where
  "material_control_loop = \<lparr>finite_schema_conclusion=
      material_control_answer (fst (finite_artifact_rows material_control_artifact)),
    finite_schema_premises={|(0,(1,Finite_Pattern_Payload []))|}, finite_schema_materials={||}\<rparr>"

definition material_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "material_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|
      ((0,0),commitment_fact (material_control_answer (rev (fst (finite_artifact_rows material_control_artifact))))),
      ((0,1),material_control_loop),((1,0),material_control_clause)|}\<rparr>"

definition material_control_declarations :: "(nat,nat,nat) resolution_declarations" where
  "material_control_declarations = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(1,material_control_clause,0,True)|}\<rparr>"

lemma material_control:
  "finite_resolution_verdict (finite_program_resolution no_witness_construction material_control_program 1
      (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment material_control_declarations) material_control_program 1
      (Finite_Payload []) 20) = None"
  by eval

text \<open>
  The premise-only control (task 630, review 622's follow-up 1): c(X) :- prod(Pair X Y), mat(Z;A,E,B,F), over prod's
  facts prod([1],[2]) and prod([1],[3]), the material premise's fields the canonical rows of an artifact of two atoms,
  prod's socket declared with the kept head. With a literal source the socket commits at c([1]) and keeps one of prod's
  two answers: one certificate against R4's two. With the source a variable Z registered with that artifact's value, Z
  is constructed first; Z is then premise-only and bound, so the socket's test fails
  (@{const finite_premise_only_free}) and the search does not commit: both answers stay, two certificates.
\<close>

definition premise_only_material :: "nat finite_term_pattern \<Rightarrow> nat finite_material_pattern" where
  "premise_only_material src = (case finite_artifact_rows material_control_artifact of (A,E,B,F) \<Rightarrow>
    \<lparr>finite_material_source=src,
      finite_material_atoms=finite_exact_term_pattern
        (finite_enumeration_term (map (finite_atom_term material_control_artifact) A)),
      finite_material_edges=finite_exact_term_pattern
        (finite_enumeration_term (map (finite_incidence_term material_control_artifact) E)),
      finite_material_counts=finite_exact_term_pattern
        (finite_enumeration_term (map (finite_attachment_term material_control_artifact) B)),
      finite_material_functions=finite_exact_term_pattern
        (finite_enumeration_term (map (finite_attachment_term material_control_artifact) F))\<rparr>)"

definition premise_only_clause :: "nat finite_term_pattern \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "premise_only_clause src = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)))|},
    finite_schema_materials={|(1,premise_only_material src)|}\<rparr>"

definition premise_only_program :: "nat finite_term_pattern \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "premise_only_program src = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|
      ((0,0),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Pattern_Payload [2]))),
      ((0,1),commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload [1]) (Finite_Pattern_Payload [3]))),
      ((1,0),premise_only_clause src)|}\<rparr>"

definition premise_only_declarations :: "nat finite_term_pattern \<Rightarrow> (nat,nat,nat) resolution_declarations" where
  "premise_only_declarations src = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(1,premise_only_clause src,0,True)|}\<rparr>"

abbreviation premise_only_literal :: "nat finite_term_pattern" where
  "premise_only_literal \<equiv> Finite_Pattern_Target (Finite_Whole material_control_artifact)"

definition premise_only_construction :: "(nat,nat,nat,nat) finite_witness_construction" where
  "premise_only_construction = \<lparr>witness_registered=(\<lambda>d S.
      if d = 1 \<and> S = premise_only_clause (Finite_Variable 2) then {|2|} else {||}),
    witness_value=(\<lambda>P d S B a. if d = 1 \<and> a = 2
      then Some (Finite_Target (Finite_Whole material_control_artifact)) else None)\<rparr>"

lemma premise_only_control:
  "commitment_certificates (finite_program_resolution no_witness_construction
      (premise_only_program premise_only_literal) 1 (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment (premise_only_declarations premise_only_literal))
      (premise_only_program premise_only_literal) 1 (Finite_Payload [1]) 20) = 1 \<and>
    commitment_certificates (finite_program_resolution premise_only_construction
      (premise_only_program (Finite_Variable 2)) 1 (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution premise_only_construction
      (finite_declared_commitment (premise_only_declarations (Finite_Variable 2)))
      (premise_only_program (Finite_Variable 2)) 1 (Finite_Payload [1]) 20) = 2"
  by eval

lemma site_one_material_controls:
  "finite_material_resolution (site_one_material [[1],[2]]) = Material_Solutions
      {|{|(2,Finite_Target (Finite_Whole (finite_enumerated_artifact [[1],[2]] [] [] []))),
          (3,Finite_Target (Finite_Anchor (finite_enumerated_artifact [[1],[2]] [] [] []) [1])),
          (4,Finite_Target (Finite_Anchor (finite_enumerated_artifact [[1],[2]] [] [] []) [2]))|}|} \<and>
    finite_material_resolution (site_one_material [[1],[1]]) = Material_Solutions {||} \<and>
    finite_material_resolution (site_one_material []) =
      Material_Solutions {|{|(2,Finite_Target (Finite_Whole finite_empty_artifact))|}|} \<and>
    finite_material_resolution ((site_one_material [[1]])\<lparr>finite_material_edges:=Finite_Pattern_Payload []\<rparr>) =
      Material_Solutions {||} \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_distinct_payloads_system 1
      (control_payload_list [[1],[2]]) 12) = Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_distinct_payloads_system 1
      (control_payload_list [[1],[1]]) 12) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_distinct_payloads_system 1
      (control_payload_list []) 12) = Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction implemented_base_control (None,[3])
      (Finite_Payload []) 12) = Some True \<and>
    control_witness_bound (finite_program_resolution no_witness_construction implemented_base_control (None,[3])
      (Finite_Payload []) 12) \<and>
    commitment_certificates (finite_program_resolution no_witness_construction commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4]] [[4],[3],[2],[1]]) 60) = 24 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4]] [[4],[3],[2],[1]]) 60) = 1 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[1]]) 60) = 1 \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[1]]) 60) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[7]]) 60) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (commitment_exchange_program [1]) 6
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_exchange_declarations) (commitment_exchange_program [1]) 6
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[7]]) 60) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (commitment_variant_program [1]) 7
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_variant_declarations) (commitment_variant_program [1]) 7
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_variant_declarations) (commitment_variant_program [3]) 7
      (control_payload_list [[1],[2]]) 30) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (commitment_variant_program [3]) 7
      (control_payload_list [[1],[2]]) 30) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction
      (commitment_sibling_program [3] [4] False) 3 (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_sibling_declarations) (commitment_sibling_program [3] [4] False) 3
      (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_sibling_declarations) (commitment_sibling_program [3] [4] True) 3
      (Finite_Payload []) 20) = None \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction
      (commitment_sibling_program [3] [4] True) 3 (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction commitment_order_program 3
      (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_order_declarations) commitment_order_program 3
      (Finite_Payload []) 20) = Some True"
  by eval

text \<open>
  The resolver's answers are the programs' meanings (@{thm [source] finite_resolution_verdict_exact}): the payload
  lists [[1],[2]] and [] are distinct and [[1],[1]] is not (@{thm [source] distinct_payload_list_exact}), and E1's
  root call holds (@{thm [source] implemented_base_control_meaning}), where the plain evaluation has no answer.
\<close>

corollary site_one_resolution_meaning:
  "(1,decode_finite_term (control_payload_list [[1],[2]])) \<in> positive_meaning distinct_payloads_system"
  "(1,decode_finite_term (control_payload_list [[1],[1]])) \<notin> positive_meaning distinct_payloads_system"
  "(1,decode_finite_term (control_payload_list [])) \<in> positive_meaning distinct_payloads_system"
proof -
  have v: "\<And>t b. finite_resolution_verdict (finite_program_resolution no_witness_construction
      finite_distinct_payloads_system 1 t 12) = Some b \<Longrightarrow>
      b \<longleftrightarrow> (1,decode_finite_term t) \<in> positive_meaning distinct_payloads_system"
    by (drule finite_resolution_verdict_exact) (simp only: finite_distinct_payloads_decoded)
  show "(1,decode_finite_term (control_payload_list [[1],[2]])) \<in> positive_meaning distinct_payloads_system"
    "(1,decode_finite_term (control_payload_list [[1],[1]])) \<notin> positive_meaning distinct_payloads_system"
    "(1,decode_finite_term (control_payload_list [])) \<in> positive_meaning distinct_payloads_system"
    using site_one_material_controls v[of "control_payload_list [[1],[2]]" True]
      v[of "control_payload_list [[1],[1]]" False] v[of "control_payload_list []" True] by blast+
qed

text \<open>
  The committed resolution's answer at a true call is sound (@{thm [source] finite_committed_resolution_sound}): the
  list [[6],[5],[4],[3],[2],[1]] is a permutation of [[1],[2],[3],[4],[5],[6]] in the control program's meaning.
\<close>

corollary commitment_control_resolved:
  "(2,decode_finite_term (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[1]])) \<in>
    positive_meaning (decode_finite_system commitment_control_program)"
proof -
  have "finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[1]]) 60) = Some True"
    using site_one_material_controls by (elim conjE) assumption
  then obtain C where "finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_control_declarations) commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[1]]) 60 = Finite_Resolved C"
    by (auto simp: finite_resolution_verdict_true)
  then show ?thesis by (rule finite_committed_resolution_sound(2))
qed

text \<open>
  The false call is refuted by R4, exact (@{thm [source] finite_resolution_verdict_exact}): the list
  [[6],[5],[4],[3],[2],[7]] is not a permutation of [[1],[2],[3],[4],[5],[6]] in the control program's meaning, the
  committed resolution's verdict at the same call.
\<close>

corollary commitment_control_refuted:
  "(2,decode_finite_term (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[7]])) \<notin>
    positive_meaning (decode_finite_system commitment_control_program)"
proof -
  have "finite_resolution_verdict (finite_program_resolution no_witness_construction commitment_control_program 2
      (commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[7]]) 60) = Some False"
    using site_one_material_controls by (elim conjE) assumption
  then show ?thesis
    using finite_resolution_verdict_exact[of commitment_control_program 2
      "commitment_control_call [[1],[2],[3],[4],[5],[6]] [[6],[5],[4],[3],[2],[7]]" 60 False] by simp
qed

corollary implemented_base_control_resolved:
  "native_call_evaluation implemented_base_control {|((None,[3]),Finite_Payload [])|}=(implemented_base_control_demand,None)"
  "((None,[3]),decode_finite_term (Finite_Payload [])) \<in> positive_meaning (decode_finite_system implemented_base_control)"
  using implemented_base_control_plain site_one_material_controls
    finite_resolution_verdict_exact[of implemented_base_control "(None,[3])" "Finite_Payload []" 12 True]
  by simp_all

end
