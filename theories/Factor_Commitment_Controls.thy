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
  w, one certificate where R4 keeps one per permutation (120). R4 resolves root(e,[3]) at bound 60 and refutes
  root(e,[9]) at 90; under F1's selection (task 693) its search of the false call at 60 is cut, unresolved, where R3's
  former selection refuted it there. The false call is refuted, not left unresolved, and the
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
      (carrier_control_call [9]) 60) = None \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction carrier_control_program 8
      (carrier_control_call [9]) 90) = Some False \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment carrier_control_declarations) carrier_control_program 8 (carrier_control_call [3]) 60) = 1 \<and>
    commitment_certificates (finite_program_resolution no_witness_construction carrier_control_program 8
      (carrier_control_call [3]) 60) = 120"
  by eval

text \<open>
  The controls of the framed test (B2b of DECISIONS.md, task 495's entry, "Committed choice, for refusals", correction
  (10)), each beside R4's values and the test at no frames.

  The remainder control is 61.0/4's shape in small: site 3, c(X) :- r(Pair X (Pair Z R)), prod(Pair Z Y), chk(Y), over
  r(x,(z1,m1)), r(x2,(z2,m2)), prod(z1,a), prod(z1,b), prod(z2,c), prod(z2,d), chk(a), chk(b) (x = [1], x2 = [2],
  z1 = [3], z2 = [4], a to d = [5] to [8], m1 = [9], m2 = [10]), prod's socket declared with the kept head and framed at
  its own output {Y}. Once r is closed it holds the private remainder R, premise-only and no input of prod, so the test
  at the default frame (the clause's variables outside prod's inputs, {R, Y}) keeps prod uncommitted, as correction (9)'s
  test does: two certificates, R4's. At the frame {Y} r's variables lie outside the frame and R is bound ground, so prod
  commits: one certificate. c(x2) is refuted, as by R4: the kept answer fails chk.

  The fixed-output control is 62.0/0's term in small: the variant control's program with q(X) :- perm(X,[a|W]),
  c(Pair X [a|W]), the caller fixing the head's element a, which is the selection's own output at the permutation's
  clause (its head output (x1, x3), the selection's output (x1, x2)); the selection socket framed at {x1, x2, x3}, the
  variables its answer changes. The variant test refuses a fixed head output; at the frame the head output x3 outside the
  selection's output is bound to the fresh W and the fixed x1 is the socket's own, so the selection commits. Over
  [[1],[2],[1]] at a = [1] the kept answer's certificates are one (one selection), two under the test at no frames (both
  selections of [1] give the kept permutation), four by R4; a = [9] is refuted by both. Correction (1)'s variant control
  (the caller fixing an element inside x3) stays refused at the frame: resolved at a = [1] and refuted at a = [3], each
  R4's verdict.
\<close>

definition framed_remainder_clause :: "(nat,nat,nat) finite_factor_schema" where
  "framed_remainder_clause = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(0,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)))),
      (1,(1,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))),
      (2,(2,Finite_Variable 2))|},
    finite_schema_materials={||}\<rparr>"

abbreviation framed_remainder_fact :: "octets \<Rightarrow> octets \<Rightarrow> octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "framed_remainder_fact u v w \<equiv> commitment_fact (Finite_Pattern_Pair (Finite_Pattern_Payload u)
    (Finite_Pattern_Pair (Finite_Pattern_Payload v) (Finite_Pattern_Payload w)))"

definition framed_remainder_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "framed_remainder_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),framed_remainder_fact [1] [3] [9]),((0,1),framed_remainder_fact [2] [4] [10]),
      ((1,0),closed_sibling_fact [3] [5]),((1,1),closed_sibling_fact [3] [6]),
      ((1,2),closed_sibling_fact [4] [7]),((1,3),closed_sibling_fact [4] [8]),
      ((2,0),commitment_fact (Finite_Pattern_Payload [5])),((2,1),commitment_fact (Finite_Pattern_Payload [6])),
      ((3,0),framed_remainder_clause)|}\<rparr>"

definition framed_remainder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "framed_remainder_declarations = \<lparr>declared_producers={||}, declared_consumers={||},
    declared_sockets={|(3,framed_remainder_clause,1,True,view_identity,view_identity)|}\<rparr>"

definition framed_remainder_frames :: "(nat,nat,nat) resolution_frames" where
  "framed_remainder_frames = {|(3,framed_remainder_clause,1,{|2|})|}"

definition framed_fixed_root :: "octets \<Rightarrow> (nat,nat,nat) finite_factor_schema" where
  "framed_fixed_root a = \<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable 2)))),
      (1,(5,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload a) (Finite_Variable 2))))|},
    finite_schema_materials={||}\<rparr>"

definition framed_fixed_program :: "octets \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "framed_fixed_program a = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (5,Finite_Variable 0),(7,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),commitment_permutation_cons),((5,0),commitment_exchange_consumer),
      ((7,0),framed_fixed_root a)|}\<rparr>"

definition framed_permutation_frames :: "(nat,nat,nat) resolution_frames" where
  "framed_permutation_frames = {|(1,commitment_permutation_cons,0,{|1,2,3|})|}"

lemma framed_controls:
  "commitment_certificates (finite_program_resolution no_witness_construction framed_remainder_program 3
      (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment framed_remainder_declarations) framed_remainder_program 3 (Finite_Payload [1]) 20) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_framed_commitment framed_remainder_declarations framed_remainder_frames) framed_remainder_program 3
      (Finite_Payload [1]) 20) = 1 \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment framed_remainder_declarations framed_remainder_frames) framed_remainder_program 3
      (Finite_Payload [1]) 20) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment framed_remainder_declarations framed_remainder_frames) framed_remainder_program 3
      (Finite_Payload [2]) 20) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction framed_remainder_program 3
      (Finite_Payload [2]) 20) = Some False \<and>
    commitment_certificates (finite_program_resolution no_witness_construction (framed_fixed_program [1]) 7
      (control_payload_list [[1],[2],[1]]) 30) = 4 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_declared_commitment commitment_variant_declarations) (framed_fixed_program [1]) 7
      (control_payload_list [[1],[2],[1]]) 30) = 2 \<and>
    commitment_certificates (finite_committed_resolution no_witness_construction
      (finite_framed_commitment commitment_variant_declarations framed_permutation_frames) (framed_fixed_program [1]) 7
      (control_payload_list [[1],[2],[1]]) 30) = 1 \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment commitment_variant_declarations framed_permutation_frames) (framed_fixed_program [1]) 7
      (control_payload_list [[1],[2],[1]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment commitment_variant_declarations framed_permutation_frames) (framed_fixed_program [9]) 7
      (control_payload_list [[1],[2],[1]]) 30) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (framed_fixed_program [9]) 7
      (control_payload_list [[1],[2],[1]]) 30) = Some False \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment commitment_variant_declarations framed_permutation_frames) (commitment_variant_program [1]) 7
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (commitment_variant_program [1]) 7
      (control_payload_list [[1],[2]]) 30) = Some True \<and>
    finite_resolution_verdict (finite_committed_resolution no_witness_construction
      (finite_framed_commitment commitment_variant_declarations framed_permutation_frames) (commitment_variant_program [3]) 7
      (control_payload_list [[1],[2]]) 30) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction (commitment_variant_program [3]) 7
      (control_payload_list [[1],[2]]) 30) = Some False"
  by eval

end
