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
  certificate at n = 4 and at n = 6, and at n = 6 it refutes a list that is not a permutation. The declarations'
  discharge and the refutation's exactness are R5b's (task 565).
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
      (control_payload_list [[1],[2]]) 30) = Some True"
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

corollary implemented_base_control_resolved:
  "native_call_evaluation implemented_base_control {|((None,[3]),Finite_Payload [])|}=(implemented_base_control_demand,None)"
  "((None,[3]),decode_finite_term (Finite_Payload [])) \<in> positive_meaning (decode_finite_system implemented_base_control)"
  using implemented_base_control_plain site_one_material_controls
    finite_resolution_verdict_exact[of implemented_base_control "(None,[3])" "Finite_Payload []" 12 True]
  by simp_all

end
