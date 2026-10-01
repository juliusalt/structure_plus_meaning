theory Factor_Resolution_Controls
  imports Factor_Material_Resolution Factor_Distinct_Payloads Factor_Substitution Factor_Resolution_Completeness
    Factor_Executed_Controls Factor_Resolution_Commitments Development_Given_Registrations
    Development_First_Request_Registrations Factor_Finite_Closed_Installation
    Factor_Shared_Resolution Factor_Shared_Commitments Factor_Resolution_Graph_Checks Factor_Material_Reading_Controls
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
  "commitment_control_declarations = \<lparr>declared_producers={|(1,view_identity,[view_output])|},
    declared_consumers={|(1,1,view_swap,0)|},
    declared_sockets={|(1,commitment_permutation_cons,0,False,view_identity,view_identity)|}\<rparr>"

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
  "commitment_exchange_declarations = \<lparr>declared_producers={|(4,view_identity,[view_output])|},
    declared_consumers={|(4,5,view_identity,0)|},
    declared_sockets={|(3,commitment_exchange_select,0,False,view_identity,view_identity)|}\<rparr>"

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
  "commitment_variant_declarations = \<lparr>declared_producers={|(1,view_identity,[view_output])|},
    declared_consumers={|(1,5,view_identity,0)|},
    declared_sockets={|(1,commitment_permutation_cons,0,False,view_identity,view_identity)|}\<rparr>"

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
    declared_sockets={|(3,commitment_sibling_clause,1,True,view_identity,view_identity)|}\<rparr>"

text \<open>
  The order control (task 589): the sibling control's clause with r's call holding a leaf, c(X) :- r(Pair [] Z),
  prod(Pair X Y), cons(Pair Z Y), over r([],z2), r([],z1) :- c(x) and prod's and cons' facts, prod's socket declared
  with the kept head and discharged. R3's former selection took r first, a leaf-bearing call at the lower position;
  its branch z1 reached the root's call, pruned under the unbarred root, and prod, reached after r, was searched
  plainly and resolved as by R4. Under F1's selection (task 693) prod is committable once c's clause is resolved and
  the commitment's priority takes it before r: it commits, keeps a, and every branch ends at a cut at the barred
  root, so the call is unresolved, never refuted — the value the addition "The resolver at the given's size" to task
  495's entry predicted. Had the kept answer been carried to cons(z2,a) the true call would have been refuted; the
  barred cut keeps it unresolved, and R4 resolves it.
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
    declared_sockets={|(3,commitment_order_clause,1,True,view_identity,view_identity)|}\<rparr>"

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
    declared_sockets={|(1,material_control_clause,0,True,view_identity,view_identity)|}\<rparr>"

text \<open>
  The premise-only control (task 630, review 622's follow-up 1): c(X) :- prod(Pair X Y), mat(Z;A,E,B,F), over prod's
  facts prod([1],[2]) and prod([1],[3]), the material premise's fields the canonical rows of an artifact of two atoms,
  prod's socket declared with the kept head. With a literal source the socket commits at c([1]) and keeps one of prod's
  two answers: one certificate against R4's two. With the source a variable Z registered with that artifact's value, Z
  is constructed first; Z is then premise-only, bound and not among prod's inputs, so the socket's test fails
  (@{const finite_premise_only_inputs}) and the search does not commit: both answers stay, two certificates.
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
    declared_sockets={|(1,premise_only_clause src,0,True,view_identity,view_identity)|}\<rparr>"

abbreviation premise_only_literal :: "nat finite_term_pattern" where
  "premise_only_literal \<equiv> Finite_Pattern_Target (Finite_Whole material_control_artifact)"

definition premise_only_construction :: "(nat,nat,nat,nat) finite_witness_construction" where
  "premise_only_construction = \<lparr>witness_registered=(\<lambda>d S.
      if d = 1 \<and> S = premise_only_clause (Finite_Variable 2) then {|2|} else {||}),
    witness_value=(\<lambda>P d S B a. if d = 1 \<and> a = 2
      then Some (Finite_Target (Finite_Whole material_control_artifact)) else None)\<rparr>"

text \<open>
  The test's conjuncts at a state (review 632's follow-up 5, and correction (7)'s counterexamples, task 718): at the
  goal standing at a position and the node at its parent position, the list
  [@{const commit_call}, @{const commit_material} of @{const finite_declared_commitment},
  @{const finite_socket_commitment}, @{const finite_children_closed}, @{const finite_premise_only_inputs},
  @{const finite_premise_only_unshared}, @{const finite_socket_pair}, @{const finite_input_output_apart},
  @{const finite_call_narrowed}, @{const finite_material_narrowed}], each at the identity views, the socket's key the
  position's last. A state after one step from a root call is the one successor of the root goal
  (@{const finite_goal_successors}); a constructed state is a node with its clause's instances pending under its
  bindings (@{const finite_node_binding}), the form @{const finite_children_closed} reads.
\<close>

abbreviation commitment_goal_at :: "(nat,nat,nat,nat) resolution_state \<Rightarrow> nat list \<Rightarrow>
    (nat,nat,nat,nat) resolution_goal option" where
  "commitment_goal_at st q \<equiv> finite_singleton_option (ffilter (\<lambda>h. resolution_goal_position h = q) (resolution_pending st))"

definition commitment_root_successor :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow>
    (nat,nat,nat,nat) resolution_state option" where
  "commitment_root_successor P d t = finite_singleton_option (finite_goal_successors P (finite_initial_state d t)
    (Resolution_Call_Goal [] None d (finite_exact_term_pattern t)))"

definition commitment_test_conjuncts :: "(nat,nat,nat) resolution_declarations \<Rightarrow> nat list option \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> nat list \<Rightarrow> bool list" where
  "commitment_test_conjuncts D F st q = (case (commitment_goal_at st q,
      finite_singleton_option (ffilter (\<lambda>nd. resolution_node_position nd = butlast q) (resolution_nodes st))) of
    (Some g, Some nd) \<Rightarrow> [commit_call (finite_declared_commitment D) F st g,
      commit_material (finite_declared_commitment D) F st g,
      finite_socket_commitment D view_identity view_identity F st g,
      finite_children_closed view_identity view_identity st nd (last q),
      finite_premise_only_inputs view_identity view_identity st nd (last q),
      finite_premise_only_unshared nd,
      finite_socket_pair view_identity q (resolution_node_schema nd),
      finite_input_output_apart view_identity nd,
      finite_call_narrowed D view_identity view_identity F st g,
      finite_material_narrowed D view_identity view_identity F st g]
  | _ \<Rightarrow> [])"

definition commitment_node_children :: "(nat,nat,nat,nat) resolution_node \<Rightarrow> (nat,nat,nat,nat) resolution_goal fset" where
  "commitment_node_children nd = fimage (\<lambda>(s,e,p). Resolution_Call_Goal (resolution_node_position nd@[s])
        (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute (finite_node_binding nd) p))
      (finite_schema_premises (resolution_node_schema nd)) |\<union>|
    fimage (\<lambda>(s,N). Resolution_Material_Goal (resolution_node_position nd@[s])
        (resolution_node_site nd,resolution_node_clause nd,s) (finite_material_pattern_substitute (finite_node_binding nd) N))
      (finite_schema_materials (resolution_node_schema nd))"

definition commitment_node_state :: "(nat,nat,nat,nat) resolution_node \<Rightarrow> (nat,nat,nat,nat) resolution_state" where
  "commitment_node_state nd = Resolution_State (commitment_node_children nd) {|nd|} {||}"

definition commitment_verdicts :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
    nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option list" where
  "commitment_verdicts P D d t = [finite_resolution_verdict (finite_program_resolution no_witness_construction P d t 20),
    finite_resolution_verdict (finite_committed_resolution no_witness_construction (finite_declared_commitment D) P d t 20)]"

text \<open>
  The premise-only control's states (review 632's follow-up 5): at c([1]) with the literal source the state after the
  root's step commits the socket at [0]; with the registered source Z the state after Z's construction
  (@{const finite_construction_step} at the root's node) refuses it, and the one conjunct false among the socket test's
  and the narrowing's is @{const finite_premise_only_inputs}: Z is premise-only, bound and not among prod's inputs.
\<close>

definition premise_only_constructed_state :: "(nat,nat,nat,nat) resolution_state option" where
  "premise_only_constructed_state = (case commitment_root_successor (premise_only_program (Finite_Variable 2)) 1
      (Finite_Payload [1]) of
      Some st \<Rightarrow> (case finite_singleton_option (resolution_nodes st) of
          Some nd \<Rightarrow> Some (finite_construction_step premise_only_construction (premise_only_program (Finite_Variable 2)) st nd)
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"

text \<open>
  Correction (7)'s counterexamples (DECISIONS.md, task 495's entry, "Committed choice, for refusals"), each a state at
  which a condition the test checks fails and the test refuses the commitment there. (i) The premise-only control's
  program with the literal source, at the state after the root's step with the material premise's goal at [1] replaced
  by another goal at that position: the material premise is neither pending as its instance nor closed, and the stray
  goal is no instance, so @{const finite_children_closed} fails and the socket at [0], which the socket test accepts,
  is not committed; the call c([1]) keeps R4's value. (ii) p(B) :- mat(C0;A,E,K,Fn), r(B), the material socket kept,
  over the fact r(e1), e1 the enumeration of C0's atoms that is not the canonical e0: the constructed parent holds the
  call p(z_A), z_A its own image of the premise-only A, so @{const finite_premise_only_unshared} fails. (iii) The
  focus root p(W,W), p(B,C) :- mat(K;C,A2,A3,A4), s(B), the material socket free, over s(e1): the output is a variant
  and the holders test passes, and the call's input and output share W, so @{const finite_input_output_apart} fails.
  (ii) and (iii) are unreachable from a call (a premise-only image is fresh when its node is made; a focus root's
  input is ground); at the calls p(e1), p(e0) and p(e1,e1), p(e0,e0) the committed resolution keeps R4's value.
\<close>

definition commitment_enumeration :: "local_address list \<Rightarrow> finite_factor_term" where
  "commitment_enumeration as = finite_enumeration_term (map (finite_atom_term material_control_artifact) as)"

abbreviation commitment_canonical :: finite_factor_term where
  "commitment_canonical \<equiv> commitment_enumeration (fst (finite_artifact_rows material_control_artifact))"

abbreviation commitment_other :: finite_factor_term where
  "commitment_other \<equiv> commitment_enumeration (rev (fst (finite_artifact_rows material_control_artifact)))"

definition narrowing_material :: "nat finite_material_pattern" where
  "narrowing_material = \<lparr>finite_material_source=Finite_Pattern_Target (Finite_Whole material_control_artifact),
    finite_material_atoms=Finite_Variable 1, finite_material_edges=Finite_Variable 2,
    finite_material_counts=Finite_Variable 3, finite_material_functions=Finite_Variable 4\<rparr>"

definition narrowing_kept_clause :: "(nat,nat,nat) finite_factor_schema" where
  "narrowing_kept_clause = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(1,(1,Finite_Variable 0))|}, finite_schema_materials={|(0,narrowing_material)|}\<rparr>"

definition narrowing_free_clause :: "(nat,nat,nat) finite_factor_schema" where
  "narrowing_free_clause = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises={|(1,(1,Finite_Variable 0))|}, finite_schema_materials={|(0,narrowing_material)|}\<rparr>"

definition narrowing_program :: "(nat,nat,nat) finite_factor_schema \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "narrowing_program S = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),S),((1,0),commitment_fact (finite_exact_term_pattern commitment_other))|}\<rparr>"

definition narrowing_declarations :: "(nat,nat,nat) finite_factor_schema \<Rightarrow> bool \<Rightarrow> (nat,nat,nat) resolution_declarations" where
  "narrowing_declarations S keep = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(0,S,0,keep,view_identity,view_identity)|}\<rparr>"

abbreviation narrowing_own :: "nat \<Rightarrow> (nat,nat) resolution_variable finite_term_pattern" where
  "narrowing_own a \<equiv> Finite_Variable (([],True),a)"

abbreviation narrowing_root_variable :: "(nat,nat) resolution_variable finite_term_pattern" where
  "narrowing_root_variable \<equiv> Finite_Variable (([],False),0)"

definition narrowing_kept_node :: "(nat,nat,nat,nat) resolution_node" where
  "narrowing_kept_node = Resolution_Node [] 0 0 narrowing_kept_clause (narrowing_own 1)
    {|(0,narrowing_own 1),(1,narrowing_own 1),(2,narrowing_own 2),(3,narrowing_own 3),(4,narrowing_own 4)|}"

definition narrowing_free_node :: "(nat,nat,nat,nat) resolution_node" where
  "narrowing_free_node = Resolution_Node [] 0 0 narrowing_free_clause
    (Finite_Pattern_Pair narrowing_root_variable narrowing_root_variable)
    {|(0,narrowing_root_variable),(1,narrowing_root_variable),(2,narrowing_own 2),(3,narrowing_own 3),(4,narrowing_own 4)|}"

definition narrowing_stray_state :: "(nat,nat,nat,nat) resolution_state option" where
  "narrowing_stray_state = map_option (\<lambda>st. Resolution_State
      (finsert (Resolution_Call_Goal [1] None 0 (Finite_Pattern_Payload [9]))
        (ffilter (\<lambda>h. resolution_goal_position h \<noteq> [1]) (resolution_pending st)))
      (resolution_nodes st) (resolution_witnesses st))
    (commitment_root_successor (premise_only_program premise_only_literal) 1 (Finite_Payload [1]))"

text \<open>
  The closed-sibling control (task 689; DECISIONS.md, task 495's entry, correction (9)): site 3,
  c(X) :- r(Pair X Z), prod(Pair Z Y), chk(Y), over r(x,z1), r(x2,z2), prod(z1,a), prod(z1,b), prod(z2,c), prod(z2,d),
  chk(a), chk(b) (x = [1], x2 = [2], z1 = [3], z2 = [4], a to d = [5] to [8]), prod's socket declared with the kept
  head. The declaration is discharged: every answer of prod at z1 extends a true instance of the clause with the head
  kept, and at z2 the clause has no true instance. The selection takes r first, its call having one alternative at
  c(x) (F1, task 693; R3's former selection took it for its leaf); once r is
  closed its variables X and Z are among prod's inputs (prod's premise input Z, the head's input, the whole conclusion
  X, which is no pair), so the socket commits and keeps one of prod's answers at z1: one certificate against R4's two,
  where the test before correction (9), which asked every sibling pending, searched prod plainly and kept both (two,
  probed at task 689). c(x2) is refuted, as by R4: the kept answer fails chk.
\<close>

definition closed_sibling_clause :: "(nat,nat,nat) finite_factor_schema" where
  "closed_sibling_clause = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
      (2,(2,Finite_Variable 2))|},
    finite_schema_materials={||}\<rparr>"

abbreviation closed_sibling_fact :: "octets \<Rightarrow> octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "closed_sibling_fact u v \<equiv> commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload u) (Finite_Pattern_Payload v))"

definition closed_sibling_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "closed_sibling_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),closed_sibling_fact [1] [3]),((0,1),closed_sibling_fact [2] [4]),
      ((1,0),closed_sibling_fact [3] [5]),((1,1),closed_sibling_fact [3] [6]),
      ((1,2),closed_sibling_fact [4] [7]),((1,3),closed_sibling_fact [4] [8]),
      ((2,0),commitment_fact (Finite_Pattern_Payload [5])),((2,1),commitment_fact (Finite_Pattern_Payload [6])),
      ((3,0),closed_sibling_clause)|}\<rparr>"

definition closed_sibling_declarations :: "(nat,nat,nat) resolution_declarations" where
  "closed_sibling_declarations = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(3,closed_sibling_clause,1,True,view_identity,view_identity)|}\<rparr>"

text \<open>
  The given's registrations at the given's readers (W4b, task 636; @{text Development_Given_Registrations}): the
  construction from @{const given_witness_registrations} at @{const finite_given_readers}, where 77's and 561's
  registrations are complete (@{thm [source] given_readers_registrations_complete}). 561's clause stands in the
  request's program, not in the given's readers, so its registration is exercised by its collection alone, at the
  given's readers, whose meanings its completeness asks (@{thm [source] merge_witness_registration_complete}): at
  two compatible environments, one artifact row each at the uses None and Some [1], the collection at bound 80 finds
  no conflict and its value reads back as exactly the merge; at two environments holding different artifacts at the
  use None the artifact rows conflict, and the collected value, which keeps both rows, reads back as no formed
  environment. After the resolver's fix (task 718), both inclusion calls 113 are resolved at the collected merge
  (11.3 s at bound 2000) and refuted at the conflicting value (0.01 s), within @{text given_registration_controls},
  and R4 gives the same verdicts beside them (@{text merge_control_plain}: 8.6 s and 0.01 s; R4 is exact, and no
  registered site lies in 113's closure);
  77 resolved at a two-definition package (the program below, installed over the empty package) and refuted where
  the reach holds its selector, which is no definition, is stated by the predicates below and does not return within
  20 s at bound 2000 either way (task 718's result; escalated), nor after OS2 (task 857's held runs: at this form 2
  selections in 15.6 s, the collection construction taking the time, and R4 none in 15.7 s; at the narrowed commitment
  of the input record at O4's moded selection the true call 625 states in 15.9 s with the production of 12's input met,
  the false call left unresolved by a witnessed failure; escalated). Each verdict is taken by the search
  the exact forms hold for, R5's committed search at no commitment over the construction
  (@{text given_control_verdict}), which bars every node present at a construction step: there a @{text "Some False"}
  is a refutation by @{thm [source] given_readers_verdict_exact}, where R3's search with a construction is sound and
  not exact. The intended verdicts at bound n: @{text "given_control_verdict n 77 (registration_control_call
  [registration_control_site 1]) = Some True"}, and @{text "Some False"} with @{text registration_control_selector}
  added to the roots; @{text "merge_control_inclusions n"} at the compatible pair with @{text True}, and at the
  conflicting pair with @{text False}.
\<close>

definition given_control_verdict :: "nat \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "given_control_verdict n d t = finite_resolution_verdict (finite_committed_resolution
    (finite_collection_construction given_witness_registrations n) no_commitment finite_given_readers d t n)"

text \<open>
  The registrations' code is the library's, read from the programs' own clauses: 77's and the additions notion's
  (@{thm [source] given_readers_registrations_code}) and 561's (@{thm [source] first_request_registration_code}).
\<close>

definition registration_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "registration_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_fact (Finite_Pattern_Payload [])),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Variable 0,
        finite_schema_premises={|(0,(0,Finite_Variable 0))|}, finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition registration_control_installation ::
    "(local_address option finite_artifact_environment\<times>local_address option) option" where
  "registration_control_installation = finite_extend_mapped_native (fst empty_package_selection)
    empty_installation_program registration_control_program (\<lambda>_. (None,[]))"

definition registration_control_site :: "nat \<Rightarrow> local_address option definition_site" where
  "registration_control_site = finite_program_coordinates (fst empty_package_selection) {||}
    (finite_system_definitions registration_control_program) (\<lambda>_. (None,[]))"

definition registration_control_environment :: "local_address option finite_artifact_environment" where
  "registration_control_environment = (case registration_control_installation of Some (K,v) \<Rightarrow> K
    | None \<Rightarrow> finite_empty_environment)"

definition registration_control_selector :: "local_address option definition_site" where
  "registration_control_selector = (case registration_control_installation of Some (K,v) \<Rightarrow> (v,[])
    | None \<Rightarrow> (None,[]))"

abbreviation registration_control_call :: "local_address option definition_site list \<Rightarrow> finite_factor_term" where
  "registration_control_call rs \<equiv> Finite_Pair (finite_environment_value registration_control_environment)
    (finite_data_list (map finite_site_data rs))"

definition registration_control_other :: "local_address option finite_artifact_environment" where
  "registration_control_other = \<lparr>finite_environment_artifacts={|(Some [1],finite_empty_artifact)|},
    finite_environment_bindings={||}\<rparr>"

definition registration_control_conflict :: "local_address option finite_artifact_environment" where
  "registration_control_conflict = \<lparr>finite_environment_artifacts={|(None,finite_empty_artifact)|},
    finite_environment_bindings={||}\<rparr>"

abbreviation merge_control_bindings :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> (nat\<times>finite_factor_term) fset" where
  "merge_control_bindings E F \<equiv> {|(0,finite_environment_value E),(4,finite_environment_value F)|}"

definition merge_control_collected :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> local_address option finite_artifact_environment option option" where
  "merge_control_collected E F = map_option finite_environment_value_read
    (finite_registration_value finite_given_readers 80 merge_witness_registration (merge_control_bindings E F))"

definition merge_control_inclusions :: "nat \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> bool \<Rightarrow> bool" where
  "merge_control_inclusions n E F b = (case finite_registration_value finite_given_readers n merge_witness_registration
      (merge_control_bindings E F) of None \<Rightarrow> False
    | Some v \<Rightarrow> given_control_verdict n 113 (Finite_Pair (finite_environment_value E) v) = Some b \<and>
      given_control_verdict n 113 (Finite_Pair (finite_environment_value F) v) = Some b)"

definition merge_control_plain :: "nat \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> bool \<Rightarrow> bool" where
  "merge_control_plain n E F b = (case finite_registration_value finite_given_readers n merge_witness_registration
      (merge_control_bindings E F) of None \<Rightarrow> False
    | Some v \<Rightarrow> finite_resolution_verdict (finite_program_resolution no_witness_construction finite_given_readers 113
        (Finite_Pair (finite_environment_value E) v) n) = Some b \<and>
      finite_resolution_verdict (finite_program_resolution no_witness_construction finite_given_readers 113
        (Finite_Pair (finite_environment_value F) v) n) = Some b)"

definition merge_control_conflicts :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> bool" where
  "merge_control_conflicts E F = (case finite_family_collection finite_given_readers 80
      (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) (merge_control_bindings E F) of
    None \<Rightarrow> False | Some (es,cs) \<Rightarrow> cs\<noteq>[])"

text \<open>
  A refuted false call at 11 beside RD1's control (@{text Factor_Material_Reading_Controls}; review 809's follow-up 2):
  an artifact value with its first atom row dropped, so that an incidence row names an absent address (the chain of
  eight addresses, whose first incidence row names [1]) or the value is otherwise no presentation (77/1's 18-address
  value). R5's committed resolution refutes both, in 54 and 125 states counted at its selection (task 718's run), and
  R4 refutes them too: the corrected reading prunes the wrong leaf inside the search.
\<close>

definition reading_control_atom_dropped :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "reading_control_atom_dropped t = (case t of Finite_Pair (Finite_Pair a A) R \<Rightarrow> Finite_Pair A R | _ \<Rightarrow> t)"

text \<open>
  The reuse control (F3 of the addition "The resolver at the given's size" to task 495's entry): site 1 calls site 0 at
  one ground term at two sockets, and site 4 walks a list calling site 0 at each element, so both repeat one ground
  subderivation (site 0 at [7] over site 2 at [8]). Each is resolved and refuted as R4 resolves and refutes it; the
  found state holds each distinct node once — the second equal call closed by the first's derivation — while the
  certificate is the unfolded derivation, counted by its nodes.
\<close>

definition reuse_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "reuse_control_program = \<lparr>finite_system_interfaces=
      {|(0,Finite_Variable 0),(1,Finite_Variable 0),(2,Finite_Variable 0),(4,Finite_Variable 0)|},
    finite_system_clauses={|
      ((2,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [8], finite_schema_premises={||},
        finite_schema_materials={||}\<rparr>),
      ((0,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [7],
        finite_schema_premises={|(0,(2,Finite_Pattern_Payload [8]))|}, finite_schema_materials={||}\<rparr>),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [1],
        finite_schema_premises={|(0,(0,Finite_Pattern_Payload [7])),(1,(0,Finite_Pattern_Payload [7]))|},
        finite_schema_materials={||}\<rparr>),
      ((4,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload [], finite_schema_premises={||},
        finite_schema_materials={||}\<rparr>),
      ((4,1),\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
        finite_schema_premises={|(0,(0,Finite_Variable 0)),(1,(4,Finite_Variable 1))|},
        finite_schema_materials={||}\<rparr>)|}\<rparr>"

primrec control_proof_nodes :: "('a,'s,'c) finite_schema_proof \<Rightarrow> nat" where
  "control_proof_nodes (Schema_Proof c V B) = Suc (sum snd (fset (fimage (map_prod id control_proof_nodes) B)))"

definition reuse_control_found_nodes :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> nat fset" where
  "reuse_control_found_nodes d t n = fimage (\<lambda>st. fcard (resolution_nodes st))
    (resolution_found (finite_resolution_search no_witness_construction reuse_control_program n (finite_initial_state d t)))"

definition reuse_control_certificate_nodes :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> nat fset" where
  "reuse_control_certificate_nodes d t n = (case finite_program_resolution no_witness_construction reuse_control_program d t n of
      Finite_Resolved C \<Rightarrow> fimage control_proof_nodes C | _ \<Rightarrow> {||})"

abbreviation reuse_control_list :: "octets list \<Rightarrow> finite_factor_term" where
  "reuse_control_list as \<equiv> foldr (\<lambda>a t. Finite_Pair (Finite_Payload a) t) as (Finite_Payload [])"

text \<open>
  The controls, one lemma by one evaluation (@{text resolution_controls}), which compiles the resolver once for
  all of them; each named control is its projection.
\<close>

lemma resolution_controls:
  "(finite_resolution_verdict (finite_program_resolution no_witness_construction material_control_program 1
      (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment material_control_declarations) material_control_program 1
      (Finite_Payload []) 20) = None) \<and>
    (commitment_certificates (finite_program_resolution no_witness_construction
      (premise_only_program premise_only_literal) 1 (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment (premise_only_declarations premise_only_literal))
      (premise_only_program premise_only_literal) 1 (Finite_Payload [1]) 20) = 1 \<and>
    commitment_certificates (finite_program_resolution premise_only_construction
      (premise_only_program (Finite_Variable 2)) 1 (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution premise_only_construction
      (finite_declared_commitment (premise_only_declarations (Finite_Variable 2)))
      (premise_only_program (Finite_Variable 2)) 1 (Finite_Payload [1]) 20) = 2) \<and>
    (map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations premise_only_literal) None st [0])
      (commitment_root_successor (premise_only_program premise_only_literal) 1 (Finite_Payload [1])) =
      Some [True, False, True, True, True, True, True, True, True, True] \<and>
    map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations (Finite_Variable 2)) None st [0])
      premise_only_constructed_state = Some [False, False, False, True, False, True, True, True, True, True]) \<and>
    (map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations premise_only_literal) None st [0])
      narrowing_stray_state = Some [False, False, True, False, True, True, True, True, False, True] \<and>
    commitment_verdicts (premise_only_program premise_only_literal) (premise_only_declarations premise_only_literal) 1
      (Finite_Payload [1]) = [Some True, Some True] \<and>
    commitment_test_conjuncts (narrowing_declarations narrowing_kept_clause True) None
      (commitment_node_state narrowing_kept_node) [0] = [False, False, True, True, True, False, True, True, True, False] \<and>
    commitment_verdicts (narrowing_program narrowing_kept_clause) (narrowing_declarations narrowing_kept_clause True) 0
      commitment_other = [Some True, Some True] \<and>
    commitment_verdicts (narrowing_program narrowing_kept_clause) (narrowing_declarations narrowing_kept_clause True) 0
      commitment_canonical = [Some False, Some False] \<and>
    commitment_test_conjuncts (narrowing_declarations narrowing_free_clause False) (Some [])
      (commitment_node_state narrowing_free_node) [0] = [False, False, True, True, True, True, True, False, True, False] \<and>
    commitment_verdicts (narrowing_program narrowing_free_clause) (narrowing_declarations narrowing_free_clause False) 0
      (Finite_Pair commitment_other commitment_other) = [Some True, Some True] \<and>
    commitment_verdicts (narrowing_program narrowing_free_clause) (narrowing_declarations narrowing_free_clause False) 0
      (Finite_Pair commitment_canonical commitment_canonical) = [Some False, Some False]) \<and>
    (commitment_certificates (finite_program_resolution no_witness_construction closed_sibling_program 3
      (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [1]) 20) = 1 \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [1]) 20) =
      Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction closed_sibling_program 3
      (Finite_Payload [2]) 20) = Some False \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [2]) 20) =
      Some False) \<and>
    (finite_material_resolution (site_one_material [[1],[2]]) = Material_Solutions
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
      (Finite_Payload []) 20) = None) \<and>
    (registration_control_installation \<noteq> None \<and>
    \<not> merge_control_conflicts environment_reader_control_rooted registration_control_other \<and>
    merge_control_collected environment_reader_control_rooted registration_control_other =
      Some (Some (finite_merge_environment environment_reader_control_rooted registration_control_other)) \<and>
    merge_control_conflicts environment_reader_control_rooted registration_control_conflict \<and>
    merge_control_collected environment_reader_control_rooted registration_control_conflict = Some None \<and>
    merge_control_inclusions 2000 environment_reader_control_rooted registration_control_other True \<and>
    merge_control_inclusions 2000 environment_reader_control_rooted registration_control_conflict False \<and>
    merge_control_plain 2000 environment_reader_control_rooted registration_control_other True \<and>
    merge_control_plain 2000 environment_reader_control_rooted registration_control_conflict False) \<and>
    (finite_resolution_verdict (finite_committed_resolution no_witness_construction (finite_declared_commitment no_declarations)
      finite_rooted_given_readers 11 (reading_control_atom_dropped (reading_control_chain_value 8)) 3000) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_rooted_given_readers 11
      (reading_control_atom_dropped (reading_control_chain_value 8)) 3000) = Some False \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction (finite_declared_commitment no_declarations)
      finite_rooted_given_readers 11 (reading_control_atom_dropped reading_control_large) 3000) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_rooted_given_readers 11
      (reading_control_atom_dropped reading_control_large) 3000) = Some False) \<and>
    (finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 1
      (Finite_Payload [1]) 20) = Some True \<and>
    reuse_control_found_nodes 1 (Finite_Payload [1]) 20 = {|3|} \<and>
    reuse_control_certificate_nodes 1 (Finite_Payload [1]) 20 = {|5|} \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 1
      (Finite_Payload [2]) 20) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 4
      (reuse_control_list [[7],[7],[7]]) 40) = Some True \<and>
    reuse_control_found_nodes 4 (reuse_control_list [[7],[7],[7]]) 40 = {|6|} \<and>
    reuse_control_certificate_nodes 4 (reuse_control_list [[7],[7],[7]]) 40 = {|10|} \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 4
      (reuse_control_list [[7],[9]]) 40) = Some False)"
  by eval

lemma material_control:
  "finite_resolution_verdict (finite_program_resolution no_witness_construction material_control_program 1
      (Finite_Payload []) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment material_control_declarations) material_control_program 1
      (Finite_Payload []) 20) = None"
  by (rule resolution_controls[THEN conjunct1])

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
  by (rule resolution_controls[THEN conjunct2, THEN conjunct1])

lemma premise_only_conjuncts:
  "map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations premise_only_literal) None st [0])
      (commitment_root_successor (premise_only_program premise_only_literal) 1 (Finite_Payload [1])) =
      Some [True, False, True, True, True, True, True, True, True, True] \<and>
    map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations (Finite_Variable 2)) None st [0])
      premise_only_constructed_state = Some [False, False, False, True, False, True, True, True, True, True]"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma narrowing_controls:
  "map_option (\<lambda>st. commitment_test_conjuncts (premise_only_declarations premise_only_literal) None st [0])
      narrowing_stray_state = Some [False, False, True, False, True, True, True, True, False, True] \<and>
    commitment_verdicts (premise_only_program premise_only_literal) (premise_only_declarations premise_only_literal) 1
      (Finite_Payload [1]) = [Some True, Some True] \<and>
    commitment_test_conjuncts (narrowing_declarations narrowing_kept_clause True) None
      (commitment_node_state narrowing_kept_node) [0] = [False, False, True, True, True, False, True, True, True, False] \<and>
    commitment_verdicts (narrowing_program narrowing_kept_clause) (narrowing_declarations narrowing_kept_clause True) 0
      commitment_other = [Some True, Some True] \<and>
    commitment_verdicts (narrowing_program narrowing_kept_clause) (narrowing_declarations narrowing_kept_clause True) 0
      commitment_canonical = [Some False, Some False] \<and>
    commitment_test_conjuncts (narrowing_declarations narrowing_free_clause False) (Some [])
      (commitment_node_state narrowing_free_node) [0] = [False, False, True, True, True, True, True, False, True, False] \<and>
    commitment_verdicts (narrowing_program narrowing_free_clause) (narrowing_declarations narrowing_free_clause False) 0
      (Finite_Pair commitment_other commitment_other) = [Some True, Some True] \<and>
    commitment_verdicts (narrowing_program narrowing_free_clause) (narrowing_declarations narrowing_free_clause False) 0
      (Finite_Pair commitment_canonical commitment_canonical) = [Some False, Some False]"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma closed_sibling_control:
  "commitment_certificates (finite_program_resolution no_witness_construction closed_sibling_program 3
      (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [1]) 20) = 1 \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [1]) 20) =
      Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction closed_sibling_program 3
      (Finite_Payload [2]) 20) = Some False \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment closed_sibling_declarations) closed_sibling_program 3 (Finite_Payload [2]) 20) =
      Some False"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

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
      (Finite_Payload []) 20) = None"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma given_registration_controls:
  "registration_control_installation \<noteq> None \<and>
    \<not> merge_control_conflicts environment_reader_control_rooted registration_control_other \<and>
    merge_control_collected environment_reader_control_rooted registration_control_other =
      Some (Some (finite_merge_environment environment_reader_control_rooted registration_control_other)) \<and>
    merge_control_conflicts environment_reader_control_rooted registration_control_conflict \<and>
    merge_control_collected environment_reader_control_rooted registration_control_conflict = Some None \<and>
    merge_control_inclusions 2000 environment_reader_control_rooted registration_control_other True \<and>
    merge_control_inclusions 2000 environment_reader_control_rooted registration_control_conflict False \<and>
    merge_control_plain 2000 environment_reader_control_rooted registration_control_other True \<and>
    merge_control_plain 2000 environment_reader_control_rooted registration_control_conflict False"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma reading_control_refuted:
  "finite_resolution_verdict (finite_committed_resolution no_witness_construction (finite_declared_commitment no_declarations)
      finite_rooted_given_readers 11 (reading_control_atom_dropped (reading_control_chain_value 8)) 3000) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_rooted_given_readers 11
      (reading_control_atom_dropped (reading_control_chain_value 8)) 3000) = Some False \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction (finite_declared_commitment no_declarations)
      finite_rooted_given_readers 11 (reading_control_atom_dropped reading_control_large) 3000) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction finite_rooted_given_readers 11
      (reading_control_atom_dropped reading_control_large) 3000) = Some False"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma reuse_control:
  "finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 1
      (Finite_Payload [1]) 20) = Some True \<and>
    reuse_control_found_nodes 1 (Finite_Payload [1]) 20 = {|3|} \<and>
    reuse_control_certificate_nodes 1 (Finite_Payload [1]) 20 = {|5|} \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 1
      (Finite_Payload [2]) 20) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 4
      (reuse_control_list [[7],[7],[7]]) 40) = Some True \<and>
    reuse_control_found_nodes 4 (reuse_control_list [[7],[7],[7]]) 40 = {|6|} \<and>
    reuse_control_certificate_nodes 4 (reuse_control_list [[7],[7],[7]]) 40 = {|10|} \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction reuse_control_program 4
      (reuse_control_list [[7],[9]]) 40) = Some False"
  by (rule resolution_controls[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])

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

text \<open>
  The code route of the reads at a sharing state's table (task 1007): every decode, projection, unification and test
  reads the state's tree of positions only where @{text "share_state_table q"} stands under the reader's head as the
  code is generated (@{thm [source] share_state_projects}); a @{text let} that binds the bare table, or another reader
  of it, would read the whole table per call. The control reads the code equations this theory's context holds: the
  program of the shared search (@{const finite_resolution_search}), of R5's kept committed search
  (@{const finite_committed_search}) and of @{const table_carry} reaches no @{const share_state_table}. The deferred
  route's code equations (@{text Factor_Deferred_Search}, @{text Factor_Deferred_Commitments}) stand outside this
  context and are not checked here.
\<close>

ML \<open>
  val _ =
    let
      val program = Code_Thingol.consts_program @{context}
        [@{const_name finite_resolution_search}, @{const_name finite_committed_search}, @{const_name table_carry}]
    in
      if Code_Symbol.Graph.defined program (Code_Symbol.Constant @{const_name share_state_table})
      then error "The resolver's code reaches share_state_table: a reader reads a sharing state's table whole"
      else ()
    end
\<close>

end
