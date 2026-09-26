theory Factor_Committed_Registrations
  imports Factor_Narrowed_Productions
begin

section \<open>The committed resolution with complete registrations\<close>

text \<open>
  Two local contracts compose here, neither proved again. R5's committed search is exact under a commitment that
  exchanges (@{const finite_commitment_exchanges}: at a committed goal a derivation is exchanged for one using the
  kept answer) and a construction that lifts (@{const finite_construction_lifts}); W4a's completeness of every
  registration at the program (@{const finite_construction_complete}) is a construction that lifts
  (@{thm [source] finite_construction_complete_lifts}): a derivation is carried at a registered variable from any value
  to the constructed one. The committed resolution taking a complete construction is therefore exact wherever its
  commitment exchanges: resolved, the call holds; refuted (no success, every diagnosis a witnessed failure) it does
  not; unresolved asserts nothing. The two carryings meet in R5's lifting (@{thm [source] finite_committed_lifting}),
  which takes both premises at every state it reaches, a constructed value among a committed goal's outputs included,
  so no premise joins them.

  The contract is stated once over any commitment that exchanges (@{text registered_commitment}); the declared
  commitment at narrowed sockets with productions (@{const finite_narrowed_commitment}) exchanges under the
  declarations', frames' and productions' discharges at a program whose registrations are premise-only
  (@{thm [source] finite_narrowed_commitment_exchanges}), which a complete construction's are
  (@{thm [source] finite_complete_registrations_premise_only}): that is @{text committed_registrations}. R5's exactness is
  its instance at the empty construction; W4a's is the instance at the record declaring nothing, whose commitment is
  none and exchanges with no premise.
\<close>

locale registered_commitment =
  fixes \<kappa> :: "('a,'s::linorder,'d,'c) finite_witness_construction"
    and P :: "('a,'s,'d,'c) finite_schema_system"
    and K :: "('a,'s,'d,'c) resolution_commitment"
  assumes formed: "finite_witness_construction_formed \<kappa>"
    and complete: "finite_construction_complete \<kappa> P"
    and exchanges: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
begin

lemma lifts: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  by (rule finite_construction_complete_lifts[OF complete])

text \<open>(1): per call, in the shape of @{thm [source] finite_program_resolution_exact}.\<close>

theorem committed_registered_resolution_exact:
  shows "finite_committed_resolution \<kappa> K P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_committed_resolution \<kappa> K P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  using finite_committed_resolution_sound(2)[of \<kappa> K P d t n C]
    finite_committed_resolution_refutation_exact[OF formed exchanges lifts, of d t n]
  by blast+

theorem committed_registered_verdict_exact:
  assumes "finite_resolution_verdict (finite_committed_resolution \<kappa> K P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_verdict_exact[OF formed exchanges lifts assms])

text \<open>(2): at the demand, in the shape of @{thm [source] finite_program_evaluation_exact}.\<close>

theorem committed_registered_demand_exact:
  assumes "finite_committed_demand \<kappa> K P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_committed_demand_exact[OF formed exchanges lifts assms] by blast+

end

text \<open>A collection construction is formed (@{thm [source] finite_collection_construction_formed}): its completeness
  at the program and the commitment's exchange are all it needs.\<close>

lemma registered_commitment_collection:
  assumes "finite_construction_complete (finite_collection_construction Rs k) P"
    and "finite_commitment_exchanges (\<lambda>_. False) (finite_collection_construction Rs k) K P"
  shows "registered_commitment (finite_collection_construction Rs k) P K"
  by (rule registered_commitment.intro[OF finite_collection_construction_formed assms])

section \<open>The declared commitment at narrowed sockets with productions\<close>

locale committed_registrations =
  fixes \<kappa> :: "('a,'s::linorder,'d,'c) finite_witness_construction"
    and P :: "('a,'s,'d,'c) finite_schema_system"
    and m :: nat
    and D :: "('a,'s,'d,'v) produced_declarations"
    and \<Phi> :: "('a,'s,'d) resolution_frames"
    and corr :: "'d \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool"
  assumes formed: "finite_witness_construction_formed \<kappa>"
    and complete: "finite_construction_complete \<kappa> P"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
begin

lemma only: "finite_registrations_premise_only \<kappa> P"
  by (rule finite_complete_registrations_premise_only[OF complete])

lemma registered: "registered_commitment \<kappa> P (finite_narrowed_commitment P m D \<Phi>)"
  by (rule registered_commitment.intro[OF formed complete
    finite_narrowed_commitment_exchanges[OF formed discharged frames productions declared only]])

sublocale registered_commitment \<kappa> P "finite_narrowed_commitment P m D \<Phi>"
  by (rule registered)

end

lemma committed_registrations_collection:
  assumes "finite_construction_complete (finite_collection_construction Rs k) P"
    and "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and "narrowed_frames_discharged (positive_meaning (decode_finite_system P)) (narrowed_declarations.truncate D) \<Phi>"
    and "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and "narrowed_productions_declared D"
  shows "committed_registrations (finite_collection_construction Rs k) P m D \<Phi> corr"
  by (rule committed_registrations.intro[OF finite_collection_construction_formed assms])

section \<open>(4): R5's and W4a's exactness as the two instances\<close>

text \<open>At the empty construction every registration is complete and premise-only, so the declared commitment's
  contract is R5's forms (@{thm [source] finite_narrowed_forms_exact}) at that construction.\<close>

lemma committed_registrations_empty:
  assumes "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and "narrowed_frames_discharged (positive_meaning (decode_finite_system P)) (narrowed_declarations.truncate D) \<Phi>"
    and "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and "narrowed_productions_declared D"
  shows "committed_registrations no_witness_construction P m D \<Phi> corr"
  by (rule committed_registrations.intro[OF no_witness_construction_formed no_witness_construction_complete assms])

lemmas committed_registered_empty_construction_exact =
  registered_commitment.committed_registered_resolution_exact[OF committed_registrations.registered[OF
    committed_registrations_empty]]
  registered_commitment.committed_registered_demand_exact[OF committed_registrations.registered[OF
    committed_registrations_empty]]

text \<open>At the record declaring nothing the declared commitment is none, whose exchange holds with no premise, so the
  contract is W4a's forms (@{thm [source] finite_complete_resolution_refutation_exact},
  @{thm [source] finite_complete_demand_exact}) under W4a's premises alone.\<close>

lemma finite_narrowed_commitment_none:
  "finite_narrowed_commitment P m (unproduced (unnarrowed no_declarations)) \<Phi> = no_commitment"
  by (simp add: finite_unproduced_commitment finite_framed_commitment_none)

lemma registered_commitment_none:
  assumes "finite_witness_construction_formed \<kappa>" and "finite_construction_complete \<kappa> P"
  shows "registered_commitment \<kappa> P (finite_narrowed_commitment P m (unproduced (unnarrowed no_declarations)) \<Phi>)"
  unfolding finite_narrowed_commitment_none
  by (rule registered_commitment.intro[OF assms finite_commitment_exchanges_none])

lemmas committed_registered_no_declaration_exact =
  registered_commitment.committed_registered_resolution_exact[OF registered_commitment_none,
    unfolded finite_narrowed_commitment_none]
  registered_commitment.committed_registered_demand_exact[OF registered_commitment_none,
    unfolded finite_narrowed_commitment_none]

end
