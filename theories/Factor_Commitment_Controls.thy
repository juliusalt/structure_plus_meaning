theory Factor_Commitment_Controls
  imports Factor_Resolution_Controls Factor_Resolution_Carriers
begin

text \<open>
  The controls of views, carriers and narrowed sockets (R5d and R5e of DECISIONS.md "The native evaluator constructs
  the missing witnesses by resolution", its addition "The given's remaining producers: views, carriers and narrowed
  sockets"), one lemma proved by one evaluation; no library theory imports this theory.

  The carrier control is 79's clause in small. Site 7, P((e,r),w) :- perm(e,rows), keys(rows,ks),
  back((e,ks),rows'), rd(r,rows'), vals(rows',w), a producer read at the view whose right side holds an input: the
  pattern Pair e (Pair r w), its input Pair e r, its output w. The rows are selected (perm, sites 1 and 0 of the
  commitment control), carried from rows to keys (keys, site 2, a function), from keys to rows (back, site 3, read
  against the keys' direction: the rows of e in the keys' order, through mem, site 4), read (rd, site 6, a consumer:
  r is the key of some row) and carried to w (vals, site 5). Site 8, root(e,r) :- P((e,r),w). The permutation's
  socket at P's clause is declared free, its class carried to P's head output w, which P's view declares; P is
  declared a producer at its view, and the selection's socket at the permutation's clause is declared as in the
  commitment control.
\<close>


definition carrier_keys_cons :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_keys_cons = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2))
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3)),
    finite_schema_premises={|(0,(2,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_vals_cons :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_vals_cons = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2))
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)),
    finite_schema_premises={|(0,(5,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_mem_here :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_mem_here = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)),
    finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition carrier_mem_later :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_mem_later = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    finite_schema_premises={|(0,(4,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_back_nil :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_back_nil = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Payload [])) (Finite_Pattern_Payload []),
    finite_schema_premises={||}, finite_schema_materials={||}\<rparr>"

definition carrier_back_cons :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_back_cons = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)) (Finite_Variable 4)),
    finite_schema_premises={|(0,(4,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))
        (Finite_Variable 0))),
      (1,(3,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)) (Finite_Variable 4)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_read :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_read = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises={|(0,(4,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))
      (Finite_Variable 1)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_family :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_family = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3))),
      (1,(2,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
      (2,(3,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 4)) (Finite_Variable 5))),
      (3,(6,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 5))),
      (4,(5,Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 2)))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_root :: "(nat,nat,nat) finite_factor_schema" where
  "carrier_root = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises={|(0,(7,Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>"

definition carrier_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "carrier_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0),(4,Finite_Variable 0),(5,Finite_Variable 0),(6,Finite_Variable 0),
      (7,Finite_Variable 0),(8,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),commitment_permutation_cons),
      ((2,0),commitment_permutation_nil),((2,1),carrier_keys_cons),((3,0),carrier_back_nil),((3,1),carrier_back_cons),
      ((4,0),carrier_mem_here),((4,1),carrier_mem_later),((5,0),commitment_permutation_nil),((5,1),carrier_vals_cons),
      ((6,0),carrier_read),((7,0),carrier_family),((8,0),carrier_root)|}\<rparr>"

definition carrier_control_declarations :: "(nat,nat,nat) resolution_declarations" where
  "carrier_control_declarations = \<lparr>declared_producers={|(7,join_view,[Finite_Variable 2])|},
    declared_consumers={||},
    declared_sockets={|(7,carrier_family,0,False,view_identity,join_view),
      (1,commitment_permutation_cons,0,False,view_identity,view_identity)|}\<rparr>"

definition carrier_control_call :: "octets \<Rightarrow> finite_factor_term" where
  "carrier_control_call r = Finite_Pair (foldr (\<lambda>k t. Finite_Pair (Finite_Pair (Finite_Payload [k]) (Finite_Payload [k + 10])) t)
    [1,2,3,4,5] (Finite_Payload [])) (Finite_Payload r)"

text \<open>
  At five rows the committed resolution resolves root(e,[3]) and refutes root(e,[9]), each verdict R4's: P committed at
  its view, the permutation committed at its free socket, its least answer carried through keys, back, rd and vals to
  w, one certificate where R4 keeps one per permutation (120). The false call is refuted, not left unresolved, and the
  true one resolved: #519's counterexample, a commitment refuting a true call, does not arise at a socket its carriers
  discharge (@{thm [source] socket_discharged_carried}).
\<close>

lemma carrier_controls:
  "finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment carrier_control_declarations) carrier_control_program 8 (carrier_control_call [3]) 60) =
      Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction carrier_control_program 8
      (carrier_control_call [3]) 60) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_declared_commitment carrier_control_declarations) carrier_control_program 8 (carrier_control_call [9]) 60) =
      Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction carrier_control_program 8
      (carrier_control_call [9]) 60) = Some False \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment carrier_control_declarations) carrier_control_program 8 (carrier_control_call [3]) 60) = 1 \<and>
    commitment_certificates (finite_program_resolution no_witness_construction carrier_control_program 8
      (carrier_control_call [3]) 60) = 120"
  by eval

end
