theory Factor_Mode_Controls
  imports Factor_Committed_Registrations Factor_Commitment_Controls
begin

text \<open>
  The control of modes (O1 of correction (12) of "Committed choice, for refusals", DECISIONS.md, task 495's entry), one
  lemma proved by one evaluation; no library theory imports this theory.

  It is 37's clause in small: a keyed lookup beside an identity producer. Site 0 is the selection of the commitment
  control, its argument (list, (element, rest)); site 1 walks a list to a stated end, walk((l,e)) with walk(([],[])) and
  walk(((h,t),e)) :- walk((t,e)); site 2, the identity producer, id((x,x)) :- walk((x,[])), declared a producer at the
  identity view; site 3, the lookup, look(((k,rows),out)) :- id((x,out)), sel((rows,((k,x),rest))), the producer's
  socket before the selection's as 12's is taken before 5 in 37's; site 4, root(a) :- look((a,out)), the free
  remainder control's root clause. One mode: the
  selection at the row view, its input the key and the list, its output the row's value and the rest. The producer's
  input x is a waiting variable, so the selection binds it before the producer runs: at the moded selection it is taken
  first, the identity is committed with its input ground and its sub-search checks the value. At R5's default the
  identity is taken first (one alternative), and its walk on a free input, a call holding a leaf, stands before the
  selection in R3's classes: it enumerates lists until the selection's key fixes one.
\<close>

definition mode_walk_cons :: "(nat,nat,nat) finite_factor_schema" where
  "mode_walk_cons = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))|},
    finite_schema_materials={||}\<rparr>"

definition mode_identity :: "(nat,nat,nat) finite_factor_schema" where
  "mode_identity = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 0),
    finite_schema_premises={|(0,(1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Payload [])))|},
    finite_schema_materials={||}\<rparr>"

definition mode_lookup :: "(nat,nat,nat) finite_factor_schema" where
  "mode_lookup = \<lparr>finite_schema_conclusion=Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises={|(0,(2,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 2))),
      (1,(0,Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 3)) (Finite_Variable 4))))|},
    finite_schema_materials={||}\<rparr>"


definition mode_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "mode_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),
      (2,Finite_Variable 0),(3,Finite_Variable 0),(4,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),commitment_selection_here),((0,1),commitment_selection_later),
      ((1,0),commitment_permutation_nil),((1,1),mode_walk_cons),((2,0),mode_identity),((3,0),mode_lookup),((4,0),free_remainder_root)|}\<rparr>"

definition mode_control_declarations :: "(nat,nat,nat) resolution_declarations" where
  "mode_control_declarations = \<lparr>declared_producers={|(2,view_identity,[view_output])|},
    declared_consumers={||}, declared_sockets={||}\<rparr>"

definition mode_row_view :: "nat resolution_view" where
  "mode_row_view = (Finite_Pattern_Pair (Finite_Variable 0)
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 0), Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))"

definition mode_control_modes :: "nat resolution_modes" where
  "mode_control_modes = {|(0,mode_row_view)|}"

definition mode_control_value :: "nat \<Rightarrow> finite_factor_term" where
  "mode_control_value k = foldr Finite_Pair (replicate k (Finite_Payload [k])) (Finite_Payload [])"

definition mode_control_call :: "nat \<Rightarrow> finite_factor_term" where
  "mode_control_call k = Finite_Pair (Finite_Payload [k]) (foldr (\<lambda>i t. Finite_Pair
    (Finite_Pair (Finite_Payload [i]) (mode_control_value i)) t) [1,2,3,4,5] (Finite_Payload []))"

abbreviation mode_control_commitment :: "(nat,nat,nat,nat) resolution_commitment" where
  "mode_control_commitment \<equiv> finite_declared_commitment mode_control_declarations"

definition mode_control_row :: "nat \<Rightarrow> nat \<Rightarrow> bool option \<times> nat \<times> bool option \<times> nat \<times> bool option" where
  "mode_control_row k n = (finite_resolution_verdict (finite_moded_resolution no_witness_construction
      mode_control_commitment mode_control_declarations mode_control_modes mode_control_program 4 (mode_control_call k) n),
    committed_resolution_states (finite_moded_select no_witness_construction mode_control_commitment
      mode_control_declarations mode_control_modes mode_control_program) no_witness_construction
      mode_control_commitment mode_control_program 4 (mode_control_call k) n,
    finite_resolution_verdict (finite_committed_resolution no_witness_construction mode_control_commitment
      mode_control_program 4 (mode_control_call k) n),
    committed_resolution_states (finite_committed_select no_witness_construction mode_control_commitment
      mode_control_program) no_witness_construction mode_control_commitment mode_control_program 4 (mode_control_call k) n,
    finite_resolution_verdict (finite_program_resolution no_witness_construction mode_control_program 4
      (mode_control_call k) n))"

lemma mode_control_modes_formed: "modes_formed mode_control_modes"
  by eval

lemma mode_control_identity:
  assumes "(2,t) \<in> positive_meaning (decode_finite_system mode_control_program)"
  shows "\<exists>x. t = Pair_Term x x"
proof -
  have consequence: "(2,t) \<in> schema_consequences (decode_finite_system mode_control_program)
      (positive_meaning (decode_finite_system mode_control_program))"
    using assms positive_meaning_unfold by blast
  obtain c S h where clause: "((2,c),S) \<in> system_clauses (decode_finite_system mode_control_program)"
    and head: "t = evaluate_pattern h (schema_conclusion S)"
    using schema_consequences_valuationD[OF consequence] by blast
  have "S = decode_finite_schema mode_identity"
    using clause by (auto simp: mode_control_program_def decode_finite_system_def)
  then show ?thesis using head by (auto simp: mode_identity_def decode_finite_schema_def)
qed

text \<open>The producer's declaration is discharged at the control's program: the identity is functional.\<close>

lemma mode_control_discharged:
  "declarations_discharged (positive_meaning (decode_finite_system mode_control_program)) mode_control_declarations
    (\<lambda>d i. (=))"
proof -
  have formed: "declarations_formed mode_control_declarations"
    by eval
  have "producer_discharged (positive_meaning (decode_finite_system mode_control_program)) 2 view_identity
      [view_output] (\<lambda>i. (=))"
    unfolding producer_discharged_identity
  proof (intro allI impI)
    fix x y y'
    assume a: "(2,Pair_Term x y) \<in> positive_meaning (decode_finite_system mode_control_program)"
      and b: "(2,Pair_Term x y') \<in> positive_meaning (decode_finite_system mode_control_program)"
    from mode_control_identity[OF a] have "y = x" by auto
    moreover from mode_control_identity[OF b] have "y' = x" by auto
    ultimately show "y = y'" by simp
  qed
  then show ?thesis using formed by (simp add: declarations_discharged_def mode_control_declarations_def)
qed

text \<open>
  Each row: the verdict and the states at the moded selection, the verdict and the states at R5's default
  (@{const finite_committed_select}), and R4's verdict. At bound 20 the true call look(3) is resolved in 16 states at
  the moded selection against 30 at R5's default, and the false call look(9), whose key no row holds, is refuted in 8
  against 9; R4 resolves and refutes them too. Both counts stand at bound 40 as at 20: each search ends.
\<close>

lemma mode_controls:
  "mode_control_row 3 20 = (Some True, 16, Some True, 30, Some True) \<and>
    mode_control_row 9 20 = (Some False, 8, Some False, 9, Some False)"
  by eval

text \<open>
  The false call is refuted at the moded selection (O3 of correction (12)): the declared commitment exchanges at the
  moded priority under the control's discharged declarations (@{thm [source] registered_commitment_moded_declared}), so
  the moded verdict the evaluation above computed is exact, the refutation read from that one evaluation; R4's value
  stands beside it.
\<close>

lemma mode_control_registered:
  "registered_commitment_at (finite_moded_priority mode_control_commitment mode_control_declarations mode_control_modes)
    no_witness_construction mode_control_program mode_control_commitment"
  by (rule registered_commitment_moded_declared[OF no_witness_construction_formed no_witness_construction_complete
    mode_control_discharged])

lemma mode_control_refuted:
  "(4,decode_finite_term (mode_control_call 9)) \<notin> positive_meaning (decode_finite_system mode_control_program) \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction mode_control_program 4
      (mode_control_call 9) 20) = Some False"
proof -
  have row: "finite_resolution_verdict (finite_moded_resolution no_witness_construction mode_control_commitment
      mode_control_declarations mode_control_modes mode_control_program 4 (mode_control_call 9) 20) = Some False \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction mode_control_program 4
      (mode_control_call 9) 20) = Some False"
    using mode_controls unfolding mode_control_row_def prod.inject by blast
  have "False \<longleftrightarrow> (4,decode_finite_term (mode_control_call 9)) \<in> positive_meaning (decode_finite_system mode_control_program)"
    by (rule registered_commitment_at.committed_registered_verdict_exact[OF mode_control_registered conjunct1[OF row]])
  with row show ?thesis by blast
qed

end
