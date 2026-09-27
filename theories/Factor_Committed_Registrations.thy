theory Factor_Committed_Registrations
  imports Factor_Narrowed_Productions Factor_Resolution_Modes
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

  Every form is stated once at a priority @{text pr} of F1's selection (@{const finite_resolution_select_at}), under
  the exchange at that priority (@{const finite_commitment_exchanges_at}, task 802): @{text registered_commitment_at}.
  The default statements are its instances at the commitment's own priority (@{const finite_commitment_priority}),
  by name and statement; the declared and the narrowed commitments exchange at every priority
  (@{thm [source] finite_declared_commitment_exchanges_at}, @{thm [source] finite_narrowed_commitment_exchanges_at}),
  so their forms hold at any priority, the moded one (@{const finite_moded_priority}, O1) among them: a mode is never
  a premise of exactness.
\<close>

locale registered_commitment_at =
  fixes pr :: "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and \<kappa> :: "('a,'s,'d,'c) finite_witness_construction"
    and P :: "('a,'s,'d,'c) finite_schema_system"
    and K :: "('a,'s,'d,'c) resolution_commitment"
  assumes formed: "finite_witness_construction_formed \<kappa>"
    and complete: "finite_construction_complete \<kappa> P"
    and exchanges: "finite_commitment_exchanges_at pr (\<lambda>_. False) \<kappa> K P"
begin

lemma lifts: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  by (rule finite_construction_complete_lifts[OF complete])

lemma exact_premises: "finite_committed_exact_premises
    (\<lambda>d t s. resolution_invariant P d t s \<and> resolution_registrations_held \<kappa> s) (finite_resolution_select_at pr \<kappa> P) \<kappa> K P"
  by (rule finite_committed_exact_premises_select_at[OF formed exchanges lifts])

theorem committed_registered_resolution_exact:
  shows "finite_committed_resolution_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_committed_resolution_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (erule finite_committed_resolution_by_sound(3)) (erule finite_committed_resolution_by_refutation_exact[OF exact_premises])

theorem committed_registered_verdict_exact:
  assumes "finite_resolution_verdict (finite_committed_resolution_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_verdict_by_exact[OF exact_premises assms])

theorem committed_registered_demand_exact:
  assumes "finite_committed_demand_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_committed_demand_by_exact[OF exact_premises assms] by blast+

end

text \<open>
  At a table (DECISIONS.md, task 495's entry, "The given's calls are decided once", GT2): the same contract over the
  committed forms at the table, from the exchange and the construction premise at the table
  (@{const finite_commitment_exchanges_at_in}, @{const finite_construction_lifts_in}); every form above is its instance
  at the empty table (@{text registered_commitment_at_in_empty}). A resolution is sound at every table; a refutation
  and a verdict exact from the premises at the table.
\<close>

locale registered_commitment_at_in =
  fixes \<Theta> :: "('a,'s::linorder,'d,'c) resolution_table"
    and pr :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and \<kappa> :: "('a,'s,'d,'c) finite_witness_construction"
    and P :: "('a,'s,'d,'c) finite_schema_system"
    and K :: "('a,'s,'d,'c) resolution_commitment"
  assumes formed: "finite_witness_construction_formed \<kappa>"
    and lifts_in: "finite_construction_lifts_in \<Theta> (\<lambda>_. False) \<kappa> P"
    and exchanges_in: "finite_commitment_exchanges_at_in \<Theta> pr (\<lambda>_. False) \<kappa> K P"
begin

lemma exact_premises_in: "finite_committed_exact_premises_in \<Theta>
    (\<lambda>d t s. resolution_invariant_in \<Theta> P d t s \<and> resolution_registrations_held \<kappa> s) (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P"
  by (rule finite_committed_exact_premises_select_at_in[OF formed exchanges_in lifts_in])

theorem committed_registered_resolution_exact_in:
  shows "finite_committed_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_committed_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (erule finite_committed_resolution_by_sound_in(3))
    (erule finite_committed_resolution_by_refutation_exact_in[OF exact_premises_in])

theorem committed_registered_verdict_exact_in:
  assumes "finite_resolution_verdict (finite_committed_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_verdict_by_exact_in[OF exact_premises_in assms])

theorem committed_registered_demand_exact_in:
  assumes "finite_committed_demand_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_committed_demand_by_exact_in[OF exact_premises_in assms] by blast+

end

lemma registered_commitment_at_in_empty:
  assumes registered: "registered_commitment_at pr \<kappa> P K"
  shows "registered_commitment_at_in resolution_empty_table pr \<kappa> P K"
  by (rule registered_commitment_at_in.intro[OF registered_commitment_at.formed[OF registered]
    registered_commitment_at.lifts[OF registered] registered_commitment_at.exchanges[OF registered]])

text \<open>The declared commitment exchanges at every priority: its forms hold at any, a complete construction given.\<close>

lemma registered_commitment_at_declared:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> P"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "registered_commitment_at pr \<kappa> P (finite_declared_commitment D)"
  by (rule registered_commitment_at.intro[OF \<kappa> complete finite_declared_commitment_exchanges_at[OF \<kappa> discharged
    finite_complete_registrations_premise_only[OF complete]]])

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

text \<open>The default is the commitment's own priority: every form below is the instance there.\<close>

lemma registered_at_default: "registered_commitment_at (finite_commitment_priority K) \<kappa> P K"
  by (rule registered_commitment_at.intro[OF formed complete exchanges[unfolded finite_commitment_exchanges_priority]])

text \<open>(1): per call, in the shape of @{thm [source] finite_program_resolution_exact}.\<close>

theorem committed_registered_resolution_exact:
  shows "finite_committed_resolution \<kappa> K P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_committed_resolution \<kappa> K P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  unfolding finite_committed_resolution_select
  by (erule registered_commitment_at.committed_registered_resolution_exact(1)[OF registered_at_default])
    (erule registered_commitment_at.committed_registered_resolution_exact(2)[OF registered_at_default])

theorem committed_registered_verdict_exact:
  assumes "finite_resolution_verdict (finite_committed_resolution \<kappa> K P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule registered_commitment_at.committed_registered_verdict_exact[OF registered_at_default
    assms[unfolded finite_committed_resolution_select]])

text \<open>(2): at the demand, in the shape of @{thm [source] finite_program_evaluation_exact}.\<close>

theorem committed_registered_demand_exact:
  assumes "finite_committed_demand \<kappa> K P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using registered_commitment_at.committed_registered_demand_exact[OF registered_at_default
    assms[unfolded finite_committed_demand_select]] by blast+

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

text \<open>At a priority: the narrowed exchange holds at every one (O2), so the forms hold at any.\<close>

lemma registered_at: "registered_commitment_at pr \<kappa> P (finite_narrowed_commitment P m D \<Phi>)"
  by (rule registered_commitment_at.intro[OF formed complete
    finite_narrowed_commitment_exchanges_at[OF formed discharged frames productions declared only]])

lemmas committed_registered_resolution_exact_at =
  registered_commitment_at.committed_registered_resolution_exact[OF registered_at]

lemmas committed_registered_verdict_exact_at =
  registered_commitment_at.committed_registered_verdict_exact[OF registered_at]

lemmas committed_registered_demand_exact_at =
  registered_commitment_at.committed_registered_demand_exact[OF registered_at]

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

text \<open>A record declaring no narrowing and no production is one: its discharges are R5d's
  (@{thm [source] declarations_discharged_unnarrowed}, @{thm [source] frames_discharged_unnarrowed}).\<close>

lemma committed_registrations_unnarrowed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> P"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
  shows "committed_registrations \<kappa> P m (unproduced (unnarrowed D)) \<Phi> corr"
proof (rule committed_registrations.intro[OF \<kappa> complete])
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D))) corr"
    using discharged by (simp add: declarations_discharged_unnarrowed)
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D))) \<Phi>"
    using frames by (simp add: frames_discharged_unnarrowed)
  show "productions_discharged (positive_meaning (decode_finite_system P)) P m (unproduced (unnarrowed D))"
    by (rule productions_discharged_none) simp
  show "narrowed_productions_declared (unproduced (unnarrowed D))" by (rule narrowed_productions_declared_unnarrowed)
qed

text \<open>The record declaring nothing is one at W4a's premises alone: nothing is declared, so nothing is to discharge.\<close>

lemma committed_registrations_none:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> P"
  shows "committed_registrations \<kappa> P m (unproduced (unnarrowed no_declarations)) \<Phi> corr"
  by (rule committed_registrations_unnarrowed[OF \<kappa> complete no_declarations_discharged])
    (simp add: frames_discharged_def no_declarations_def)

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

text \<open>W4a's instance is rc's own at that record (@{text committed_registrations_none}).\<close>

lemmas committed_registered_no_declaration_exact =
  registered_commitment.committed_registered_resolution_exact[OF committed_registrations.registered[OF
    committed_registrations_none], unfolded finite_narrowed_commitment_none]
  registered_commitment.committed_registered_demand_exact[OF committed_registrations.registered[OF
    committed_registrations_none], unfolded finite_narrowed_commitment_none]

section \<open>(3): the forms at the moded selection\<close>

text \<open>
  The moded selection (@{const finite_moded_select}, O1) is F1's selection at the moded priority, so its forms are
  the forms at a priority there. The declared and the narrowed commitments exchange at every priority, so no premise
  reads a mode: at no modes each form is the default's (@{thm [source] finite_moded_priority_none}), and a wrong mode
  costs work, never a verdict.
\<close>

lemma registered_commitment_moded_declared:
  assumes "finite_witness_construction_formed \<kappa>" and "finite_construction_complete \<kappa> P"
    and "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "registered_commitment_at (finite_moded_priority (finite_declared_commitment D) Dm M) \<kappa> P
    (finite_declared_commitment D)"
  by (rule registered_commitment_at_declared[OF assms])

context committed_registrations
begin

lemma registered_moded:
  "registered_commitment_at (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P
    (finite_narrowed_commitment P m D \<Phi>)"
  by (rule registered_at)

theorem committed_moded_resolution_exact:
  shows "finite_moded_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_moded_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (erule registered_commitment_at.committed_registered_resolution_exact(1)[OF registered_moded])
    (erule registered_commitment_at.committed_registered_resolution_exact(2)[OF registered_moded])

theorem committed_moded_verdict_exact:
  assumes "finite_resolution_verdict (finite_moded_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n) =
    Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule registered_commitment_at.committed_registered_verdict_exact[OF registered_moded assms])

theorem committed_moded_demand_exact:
  assumes "finite_committed_demand_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
    (finite_narrowed_commitment P m D \<Phi>) P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using registered_commitment_at.committed_registered_demand_exact[OF registered_moded assms] by blast+

end

text \<open>
  The moded form at two valid tables of the same calls returns an outcome of the same kind: its selection at the two
  tables is one (@{thm [source] finite_resolution_select_calls}), and the committed form's calls-alone statement
  (@{thm [source] finite_committed_resolution_by_calls}) applies.
\<close>

theorem finite_moded_resolution_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
    and valid: "finite_table_valid P \<Theta>" and valid': "finite_table_valid P \<Theta>'"
    and Pf: "finite_system_formed P" and tf: "finite_term_formed t" and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_resolution_verdict (finite_moded_resolution_in \<Theta> \<kappa> K Dm M P d t n) =
      finite_resolution_verdict (finite_moded_resolution_in \<Theta>' \<kappa> K Dm M P d t n)"
    and "finite_moded_resolution_in \<Theta> \<kappa> K Dm M P d t n = Finite_Unresolved E \<longleftrightarrow>
      finite_moded_resolution_in \<Theta>' \<kappa> K Dm M P d t n = Finite_Unresolved E"
proof -
  have S: "finite_resolution_select_in \<Theta>' (finite_moded_priority K Dm M) \<kappa> P =
      finite_resolution_select_in \<Theta> (finite_moded_priority K Dm M) \<kappa> P"
    by (rule finite_resolution_select_calls[OF calls[symmetric]])
  note c = finite_committed_resolution_by_calls[OF calls valid valid' Pf tf \<kappa> finite_resolution_select_goals_in,
    where K=K and d=d and n=n]
  show "finite_resolution_verdict (finite_moded_resolution_in \<Theta> \<kappa> K Dm M P d t n) =
      finite_resolution_verdict (finite_moded_resolution_in \<Theta>' \<kappa> K Dm M P d t n)"
    unfolding S by (rule c(1))
  show "finite_moded_resolution_in \<Theta> \<kappa> K Dm M P d t n = Finite_Unresolved E \<longleftrightarrow>
      finite_moded_resolution_in \<Theta>' \<kappa> K Dm M P d t n = Finite_Unresolved E"
    unfolding S by (rule c(2))
qed

section \<open>rc's forms at a table\<close>

text \<open>
  rc's premises at a table: the construction premise and the narrowed commitment's exchange at every priority at the
  table, beside rc's own. At the empty table they are rc's (@{text committed_registrations_in_empty}); at a table their
  discharges are the exchange's (GT2b's). The moded forms there are the forms at the table at the moded priority.
\<close>

locale committed_registrations_in = committed_registrations \<kappa> P m D \<Phi> corr
  for \<kappa> :: "('a,'s::linorder,'d,'c) finite_witness_construction" and P m and D :: "('a,'s,'d,'v) produced_declarations"
    and \<Phi> corr +
  fixes \<Theta> :: "('a,'s,'d,'c) resolution_table"
  assumes lifts_at_table: "finite_construction_lifts_in \<Theta> (\<lambda>_. False) \<kappa> P"
    and exchanges_at_table: "\<And>pr. finite_commitment_exchanges_at_in \<Theta> pr (\<lambda>_. False) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P"
begin

lemma registered_at_in: "registered_commitment_at_in \<Theta> pr \<kappa> P (finite_narrowed_commitment P m D \<Phi>)"
  by (rule registered_commitment_at_in.intro[OF formed lifts_at_table exchanges_at_table])

theorem committed_moded_resolution_exact_in:
  shows "finite_moded_resolution_in \<Theta> \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (finite_moded_resolution_in \<Theta> \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (erule registered_commitment_at_in.committed_registered_resolution_exact_in(1)[OF registered_at_in])
    (erule registered_commitment_at_in.committed_registered_resolution_exact_in(2)[OF registered_at_in])

theorem committed_moded_verdict_exact_in:
  assumes "finite_resolution_verdict (finite_moded_resolution_in \<Theta> \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n) =
    Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule registered_commitment_at_in.committed_registered_verdict_exact_in[OF registered_at_in assms])

theorem committed_moded_demand_exact_in:
  assumes "finite_committed_demand_by_in \<Theta> (finite_resolution_select_in \<Theta>
    (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using registered_commitment_at_in.committed_registered_demand_exact_in[OF registered_at_in assms] by blast+

end

lemma committed_registrations_in_empty:
  assumes registered: "committed_registrations \<kappa> P m D \<Phi> corr"
  shows "committed_registrations_in \<kappa> P m D \<Phi> corr resolution_empty_table"
  by (rule committed_registrations_in.intro[OF registered committed_registrations_in_axioms.intro[OF
    registered_commitment.lifts[OF committed_registrations.registered[OF registered]]
    registered_commitment_at.exchanges[OF committed_registrations.registered_at[OF registered]]]])

end
