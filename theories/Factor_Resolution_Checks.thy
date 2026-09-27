theory Factor_Resolution_Checks
imports Factor_Committed_Registrations Factor_Native_Committed_Registrations Factor_Narrowed_Productions
  Factor_Access_Commitments
  Factor_Input_Productions Factor_Shared_Commitments Factor_Framed_Commitment_Index
begin

section \<open>The check forms: the committed search started at the root's own focus\<close>

text \<open>
  Correction (14) of task 495's entry, build K2. A verdict's root call is ground: the root goal stands at
  @{term "[]"} (@{const finite_initial_state}), the focus @{term "Some []"} holds every goal as @{term None} does
  (@{text finite_check_root_focus}), and the root call is ground, so every join below it keeps its first found state
  (K1's @{const finite_search_join}). The check forms are the committed forms at a selection parameter with the search
  started there, each read as the committed form reads its outcome; the committed forms at @{term None} stay as they
  are, for pattern roots. No switch and no field of the commitment says which is meant: the focus a search starts at
  is its argument.
\<close>

lemma finite_check_root_focus: "finite_focus_pending (Some []) st = resolution_pending st"
  by (simp add: finite_focus_pending_def)

lemma finite_check_root_focused: "resolution_focused (Some []) q"
  by simp

definition finite_check_resolution_by ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_check_resolution_by sel \<kappa> K P d t n =
    finite_outcome_result P d t (finite_committed_search_by sel \<kappa> K P n (Some []) {||} (finite_initial_state d t))"

definition finite_check_verdict_by ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "finite_check_verdict_by sel \<kappa> K P d t n = finite_resolution_verdict (finite_check_resolution_by sel \<kappa> K P d t n)"

definition finite_check_demand_by ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "finite_check_demand_by sel \<kappa> K P D n = (let V = fimage (\<lambda>q. (q,finite_check_verdict_by sel \<kappa> K P (fst q) (snd q) n)) D in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"

definition native_check_resolution_by ::
    "((local_address,local_address,local_address option definition_site,local_address) resolution_state \<Rightarrow>
        (local_address,local_address,local_address option definition_site,local_address) resolution_selection) \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) resolution_commitment \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      nat \<Rightarrow> ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_check_resolution_by sel \<kappa> K P R n =
    (fimage (\<lambda>q. (q,finite_check_resolution_by sel \<kappa> K P (fst q) (snd q) n)) R, finite_check_demand_by sel \<kappa> K P R n)"

section \<open>Exact from the committed forms' premises\<close>

text \<open>
  The committed forms' premises (@{const finite_committed_exact_premises}) make the check forms exact, as they make the
  committed forms exact at @{term None}: the lifting (@{text finite_committed_lifting_by}) is stated at every focus, its
  join case K1's, and at @{term "Some []"} the initial state is supported exactly as at @{term None}. A found state is
  the checker's certificate; a refutation (no found state, every diagnosis witnessed) refutes; unresolved never
  refutes and never admits. No premise reads the focus: exactness rests on the committed forms' premises alone. Each
  proof is the committed form's statement at a focus that focuses the root
  (@{text finite_focused_resolution_certificates}, @{text finite_focused_resolution_refutation_exact},
  @{text finite_focused_verdict_exact}), the demand-level form the argument from exact per-call verdicts
  (@{text finite_verdict_demand_exact}) and the native form the argument from exact per-call results
  (@{text native_resolution_calls_exact}), each at @{term "Some []"}.
\<close>

theorem finite_check_resolution_by_sound:
  assumes res: "finite_check_resolution_by sel \<kappa> K P d t n = Finite_Resolved C"
  shows "C\<noteq>{||}" and "\<And>p. p |\<in>| C \<Longrightarrow> finite_checks_schema_proof P p d t"
    and "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  using finite_outcome_result_sound[OF res[unfolded finite_check_resolution_by_def]] by blast+

theorem finite_check_resolution_by_certificates:
  assumes Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
  shows "finite_check_resolution_by sel \<kappa> K P d t n =
    (let R = finite_committed_search_by sel \<kappa> K P n (Some []) {||} (finite_initial_state d t);
      C = ffUnion (fimage finite_state_proofs (resolution_found R)) in
    if C\<noteq>{||} then Finite_Resolved C else if resolution_diagnoses R={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R))"
  unfolding finite_check_resolution_by_def
  by (rule finite_focused_resolution_certificates[OF Pf tf \<kappa> goals, where F="Some []"])
    (simp_all add: resolution_focused_def)

theorem finite_check_resolution_by_refutation_exact:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and refutes: "finite_resolution_refutes (finite_check_resolution_by sel \<kappa> K P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (rule finite_focused_resolution_refutation_exact[OF given _ refutes[unfolded finite_check_resolution_by_def]])
    (simp add: resolution_focused_def)

lemmas finite_check_resolution_by_exact =
  finite_check_resolution_by_sound(3) finite_check_resolution_by_refutation_exact

lemma finite_check_verdict_by_exact:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and verdict: "finite_check_verdict_by sel \<kappa> K P d t n = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_focused_verdict_exact[OF given _
    verdict[unfolded finite_check_verdict_by_def finite_check_resolution_by_def]]) (simp add: resolution_focused_def)

theorem finite_check_demand_by_exact:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and result: "finite_check_demand_by sel \<kappa> K P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  note demand = finite_verdict_demand_exact[OF result[unfolded finite_check_demand_by_def]]
  show "schema_system_formed (decode_finite_system P)"
    by (rule demand(1)) (rule finite_check_verdict_by_exact[OF given])
  show "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    by (rule demand(2)) (rule finite_check_verdict_by_exact[OF given])
qed

theorem native_check_resolution_by_exact:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and result: "native_check_resolution_by sel \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  from result have T: "T = fimage (\<lambda>q. (q,finite_check_resolution_by sel \<kappa> K P (fst q) (snd q) n)) R"
    and A: "A = finite_check_demand_by sel \<kappa> K P R n"
    by (simp_all add: native_check_resolution_by_def)
  have resolved: "C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    if res: "finite_check_resolution_by sel \<kappa> K P (fst q) (snd q) n = Finite_Resolved C" for q C
    using finite_check_resolution_by_sound[OF res] by (simp add: decode_finite_call_term_fields)
  have refuted: "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    if "finite_resolution_refutes (finite_check_resolution_by sel \<kappa> K P (fst q) (snd q) n)" for q
    using finite_check_resolution_by_refutation_exact[OF given that] by (simp add: decode_finite_call_term_fields)
  have demand: "schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    if "A = Some B" for B
    using finite_check_demand_by_exact[OF given that[unfolded A]] by blast
  note exact = native_resolution_calls_exact[OF T resolved refuted demand]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    by (rule exact(4))
qed

text \<open>
  The four forms whose first premise is the committed forms' premises, stated once: every instance below is this
  bundle at an instance's premises, nothing proved again.
\<close>

lemmas finite_check_forms_exact = finite_check_resolution_by_refutation_exact finite_check_verdict_by_exact
  finite_check_demand_by_exact native_check_resolution_by_exact

section \<open>The check instances\<close>

text \<open>
  Each instance is the bundle at the premises its committed form is exact from, given where the committed form's
  proof gives them: at a priority (@{text finite_committed_exact_premises_select_at}); at the declared, framed,
  narrowed and unproduced commitments at a priority, through their exchanges at a priority, as the committed
  @{text finite_declared_forms_exact_at}, @{text finite_framed_forms_exact_at}, @{text finite_narrowed_forms_exact_at}
  and the unproduced forms take them; at rc's numbered and native forms at a priority, through
  @{text registered_commitment_at.exact_premises}. The moded check forms are these at the moded priority
  (@{const finite_moded_priority}) and are no third copy: a mode is never a premise of exactness.
\<close>

lemmas finite_check_forms_exact_select_at = finite_check_forms_exact[OF finite_committed_exact_premises_select_at]

lemma finite_declared_check_premises_at:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  shows "finite_committed_exact_premises (\<lambda>d t s. resolution_invariant P d t s \<and> resolution_registrations_held \<kappa> s)
    (finite_resolution_select_at pr \<kappa> P) \<kappa> (finite_declared_commitment D) P"
  by (rule finite_committed_exact_premises_select_at[OF \<kappa> finite_declared_commitment_exchanges_at[OF \<kappa> discharged only]
    constructions])

lemma finite_framed_check_premises_at:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  shows "finite_committed_exact_premises (\<lambda>d t s. resolution_invariant P d t s \<and> resolution_registrations_held \<kappa> s)
    (finite_resolution_select_at pr \<kappa> P) \<kappa> (finite_framed_commitment D \<Phi>) P"
  by (rule finite_committed_exact_premises_select_at[OF \<kappa>
    finite_framed_commitment_exchanges_at[OF \<kappa> discharged frames only] constructions])

lemma finite_narrowed_check_premises_at:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  shows "finite_committed_exact_premises (\<lambda>d t s. resolution_invariant P d t s \<and> resolution_registrations_held \<kappa> s)
    (finite_resolution_select_at pr \<kappa> P) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P"
  by (rule finite_committed_exact_premises_select_at[OF \<kappa>
    finite_narrowed_commitment_exchanges_at[OF \<kappa> discharged frames productions declared only] constructions])

lemma finite_unproduced_check_premises_at:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  shows "finite_committed_exact_premises (\<lambda>d t s. resolution_invariant P d t s \<and> resolution_registrations_held \<kappa> s)
    (finite_resolution_select_at pr \<kappa> P) \<kappa>
    (finite_narrowed_commitment P m (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations) \<Phi>) P"
  by (rule finite_committed_exact_premises_select_at[OF \<kappa>
    finite_unproduced_commitment_exchanges_at[OF \<kappa> discharged frames only] constructions])

lemmas finite_declared_checks_exact_at = finite_check_forms_exact[OF finite_declared_check_premises_at]
lemmas finite_framed_checks_exact_at = finite_check_forms_exact[OF finite_framed_check_premises_at]
lemmas finite_narrowed_checks_exact_at = finite_check_forms_exact[OF finite_narrowed_check_premises_at]
lemmas finite_unproduced_checks_exact_at = finite_check_forms_exact[OF finite_unproduced_check_premises_at]

text \<open>
  At a record whose productions are input registrations (I2), the narrowed check forms at the productions I2
  discharges (@{text input_productions_discharged}).
\<close>

lemmas finite_input_checks_exact_at =
  finite_check_forms_exact[OF finite_narrowed_check_premises_at[OF _ _ _ input_productions_discharged]]

text \<open>rc's numbered and native forms at a priority (O3), the moded ones among them at the moded priority.\<close>

lemmas registered_checks_exact_at = finite_check_forms_exact[OF registered_commitment_at.exact_premises]

lemmas finite_check_numbered_exact = finite_check_resolution_by_refutation_exact finite_check_verdict_by_exact
  finite_check_demand_by_exact

context committed_registrations
begin

lemmas committed_registered_checks_exact_at =
  finite_check_numbered_exact[OF registered_commitment_at.exact_premises[OF registered_at]]

end

lemmas native_committed_registered_check_at =
  native_check_resolution_by_exact[OF registered_commitment_at.exact_premises[OF committed_registrations.registered_at]]

section \<open>The transfers at an installed program\<close>

text \<open>
  Where a route build calls a check form at a program an installed site reads (R7 #547 at the first request's installed
  program, #707 and #399 at the asked relation's), the native check form there is exact at every priority, and at the
  moded selection with the modes relocated: inside #820's locale of rc's relocated premise block, as O3's
  @{text committed_registrations_relocated_at}, @{text native_committed_registered_relocated_at} and
  @{text native_committed_moded_relocated} are its instances.
\<close>

context relocated_registrations
begin

lemmas native_installed_check_at =
  native_check_resolution_by_exact[OF registered_commitment_at.exact_premises[OF registered_installed_at]]

lemmas installed_checks_exact_at =
  finite_check_forms_exact[OF registered_commitment_at.exact_premises[OF registered_installed_at]]

end

text \<open>
  Two check verdicts on programs agreeing on a dependency-closed set holding the called site are equal, and so are the
  check verdicts of a program and its relocation by a map injective on its definitions and the called one, each
  consuming only the two programs' exact premises (#542's verdict on the rooted readers against the given's), as the
  committed transfers consume theirs: each is @{text finite_exact_verdicts_equal} at the two verdicts' exactness and
  the calls' equal meaning (the locality of positive meaning, @{text finite_renamed_meaning_at}). An installed program
  is not the relocation itself but an alpha variant of it (V3's @{text installed_variant}): relating a program's
  numbered course with its installation's native course composes both exactness facts with the meaning at the
  installed entry (@{text asked_entry_contract}, @{text installed_entry_exact}, or @{text system_alpha_positive_meaning}
  after @{text finite_renamed_meaning_at}), which #547, #707 and #399 take so.
\<close>

corollary finite_check_agreement_transfer:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and given': "finite_committed_exact_premises J' sel' \<kappa>' K' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and v: "finite_check_verdict_by sel \<kappa> K P d t n = Some b"
    and v': "finite_check_verdict_by sel' \<kappa>' K' Q d t m = Some b'"
  shows "b = b'"
  by (rule finite_exact_verdicts_equal[OF finite_check_verdict_by_exact[OF given v] finite_check_verdict_by_exact[OF given' v']
    positive_meaning_dependency_locality[OF Pf Qf agree closed dV, symmetric]])

corollary finite_check_relocation_transfer:
  assumes given: "finite_committed_exact_premises J sel \<kappa> K P"
    and given': "finite_committed_exact_premises J' sel' \<kappa>' K' (finite_rename_system g P)"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    and v: "finite_check_verdict_by sel \<kappa> K P d t n = Some b"
    and v': "finite_check_verdict_by sel' \<kappa>' K' (finite_rename_system g P) (g d) t m = Some b'"
  shows "b = b'"
  by (rule finite_exact_verdicts_equal[OF finite_check_verdict_by_exact[OF given v] finite_check_verdict_by_exact[OF given' v']
    finite_renamed_meaning_at[OF Pf injective]])

section \<open>The guard from the declarations\<close>

text \<open>
  Review 702's follow-up 1. A goal the declarations do not name is refused by every commitment test at every state:
  the direct test commits only a goal at a declared producer's site, and a socket test only a goal whose socket (the
  last component of its position) is a declared socket's, whatever node stands at its parent's position. The guard
  reads the goal alone, its site and its socket, never a state: it is sound at every state, as the shared search's
  guard premise asks (@{text shared_committed_search}). A consumer's declaration commits no goal at the consumer's
  own site (it is read at a producer's commitment, of the producer's output), so a guard naming consumers too would
  only refuse less. The moded priority also takes a binder, which stands at a mode's site. The guard is read by the
  shared search's step alone, as its projection is, never by a test or a form.
\<close>

definition finite_declared_guard ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_declared_guard D g \<longleftrightarrow>
    (case g of Resolution_Call_Goal q r d p \<Rightarrow> fBex (declared_producers D) (\<lambda>z. fst z = d)
      | Resolution_Material_Goal q r M \<Rightarrow> False) \<or>
    (resolution_goal_position g \<noteq> [] \<and>
      fBex (declared_sockets D) (\<lambda>z. fst (snd (snd z)) = last (resolution_goal_position g)))"

definition finite_moded_guard ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_moded_guard D M g \<longleftrightarrow> finite_declared_guard D g \<or>
    (case g of Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>z. fst z = d) | Resolution_Material_Goal q r N \<Rightarrow> False)"

lemma finite_direct_commitment_guard:
  assumes "finite_direct_commitment D F st g"
  shows "finite_declared_guard D g"
proof -
  from assms obtain d V hs where m: "(d,V,hs) |\<in>| declared_producers D"
    and c: "finite_producer_commits D F st g d V hs"
    unfolding finite_direct_commitment_def by blast
  from c obtain q r p where "g = Resolution_Call_Goal q r d p"
    by (cases g) (auto simp: finite_producer_commits_def)
  with m show ?thesis unfolding finite_declared_guard_def by force
qed

lemma finite_socket_commitment_guard:
  "finite_socket_commitment D Vp Vh F st g \<Longrightarrow> finite_declared_guard D g"
  by (cases g) (force simp: finite_socket_commitment_def finite_socket_declared_def finite_socket_kept_def
    finite_socket_free_def finite_declared_guard_def split: option.splits prod.splits)+

lemma finite_socket_commitment_framed_guard:
  "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<Longrightarrow> finite_declared_guard D g"
  by (cases g) (force simp: finite_socket_commitment_framed_def finite_socket_declared_framed_def
    finite_socket_kept_framed_def finite_socket_free_framed_def finite_declared_guard_def split: option.splits prod.splits)+

theorem finite_declared_guard_refuses:
  assumes "\<not> finite_declared_guard D g"
  shows "\<not> commit_call (finite_declared_commitment D) F st g" and "\<not> commit_material (finite_declared_commitment D) F st g"
  using assms by (auto simp: finite_declared_commitment_def
    dest: finite_direct_commitment_guard finite_socket_commitment_guard)

theorem finite_framed_guard_refuses:
  assumes "\<not> finite_declared_guard D g"
  shows "\<not> commit_call (finite_framed_commitment D \<Phi>) F st g" and "\<not> commit_material (finite_framed_commitment D \<Phi>) F st g"
  using assms by (auto simp: finite_framed_commitment_def
    dest: finite_direct_commitment_guard finite_socket_commitment_framed_guard)

theorem finite_narrowed_guard_refuses:
  assumes "\<not> finite_declared_guard (resolution_declarations.truncate D) g"
  shows "\<not> commit_call (finite_narrowed_commitment P m D \<Phi>) F st g"
    and "\<not> commit_material (finite_narrowed_commitment P m D \<Phi>) F st g"
  using finite_framed_guard_refuses[OF assms] by (simp_all add: finite_narrowed_commitment_def)

lemma finite_commitment_priority_refused:
  assumes "\<And>F. \<not> commit_call K F st g" and "\<And>F. \<not> commit_material K F st g"
  shows "\<not> finite_commitment_priority K st g"
  using assms by (cases g) (simp_all add: finite_commitment_priority_def Let_def)

lemma finite_moded_priority_refused:
  assumes "\<And>F. \<not> commit_call K F st g" and "\<And>F. \<not> commit_material K F st g"
    and "\<not> (case g of Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>z. fst z = d) | Resolution_Material_Goal q r N \<Rightarrow> False)"
  shows "\<not> finite_moded_priority K Dm M st g"
  using finite_commitment_priority_refused[OF assms(1,2)] assms(3)
  by (cases g) (auto simp: finite_moded_priority_def finite_mode_binder_def)

theorem finite_moded_guard_refuses:
  assumes "\<not> finite_moded_guard (resolution_declarations.truncate D) M g"
  shows "\<not> commit_call (finite_narrowed_commitment P m D \<Phi>) F st g \<and>
    \<not> commit_material (finite_narrowed_commitment P m D \<Phi>) F st g \<and>
    \<not> finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M st g"
proof -
  have g: "\<not> finite_declared_guard (resolution_declarations.truncate D) g"
    and s: "\<not> (case g of Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>z. fst z = d) | Resolution_Material_Goal q r N \<Rightarrow> False)"
    using assms unfolding finite_moded_guard_def by blast+
  have c: "\<not> commit_call (finite_narrowed_commitment P m D \<Phi>) F' st g" for F'
    by (rule finite_narrowed_guard_refuses(1)[OF g])
  have n: "\<not> commit_material (finite_narrowed_commitment P m D \<Phi>) F' st g" for F'
    by (rule finite_narrowed_guard_refuses(2)[OF g])
  show ?thesis using c n finite_moded_priority_refused[OF c n s] by blast
qed

text \<open>The shared search's guard premise at the moded priority of a narrowed commitment, discharged by the guard.\<close>

lemma shared_moded_guard:
  "search_formed \<kappa> P s \<and> search_placeable (search_project s) \<Longrightarrow> h |\<in>| access_goals (shared_access \<kappa> P s) \<Longrightarrow>
    \<not> finite_moded_guard (resolution_declarations.truncate D) M (access_goal (shared_access \<kappa> P s) h) \<Longrightarrow>
    \<not> commit_call (finite_narrowed_commitment P m D \<Phi>) F st (access_goal (shared_access \<kappa> P s) h) \<and>
    \<not> commit_material (finite_narrowed_commitment P m D \<Phi>) F st (access_goal (shared_access \<kappa> P s) h) \<and>
    \<not> finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M st (access_goal (shared_access \<kappa> P s) h)"
  by (rule finite_moded_guard_refuses)

corollary shared_moded_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
  shows "represented_committed_search (shared_committed_representation \<kappa> P)
      (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
      (\<lambda>s h. finite_moded_guard (resolution_declarations.truncate D) M (access_goal (shared_access \<kappa> P s) h))
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n F B (search_of P st) =
    finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P n F B st"
  by (rule shared_committed_search[OF sock pl shared_moded_guard])

section \<open>The guard from a goal's raising socket\<close>

text \<open>
  Review 824's follow-up 1 (task 869). A goal a clause's premise raised names the site and clause that raised it and
  its socket (its raiser, @{text rr}); at every state the shared search reaches, each node at the goal's parent position
  is that clause's node, and each node's schema is its clause's in the program (@{text finite_goals_raised}, kept by
  every step, @{text shared_raised_structure}). A socket test commits a goal only where the declarations name a socket
  at its parent node's site and schema and the goal's socket, so at those states only where they name one at the
  raising clause's schema (@{text finite_declared_raisers}). The guard reads the goal's site and raiser against those,
  never a decoded goal: sound at the invariant's states (@{text finite_raising_moded_refuses}), where
  @{const finite_declared_guard} admits a goal whose socket is any declared socket's.
\<close>

fun resolution_goal_raiser :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> ('d \<times> 'c \<times> 's) option" where
  "resolution_goal_raiser (Resolution_Call_Goal q r d p) = r"
| "resolution_goal_raiser (Resolution_Material_Goal q r M) = Some r"

definition resolution_goal_key :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> 's list \<times> ('d \<times> 'c \<times> 's) option" where
  "resolution_goal_key g = (resolution_goal_position g,resolution_goal_raiser g)"

definition resolution_node_key ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> 's list \<times> 'd \<times> 'c \<times> ('a,'s,'d) finite_factor_schema" where
  "resolution_node_key nd = (resolution_node_position nd,resolution_node_site nd,resolution_node_clause nd,
    resolution_node_schema nd)"

definition finite_nodes_raised ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('s list \<times> 'd \<times> 'c \<times> ('a,'s,'d) finite_factor_schema) fset \<Rightarrow> bool" where
  "finite_nodes_raised P N \<longleftrightarrow>
    fBall N (\<lambda>z. ((fst (snd z),fst (snd (snd z))),snd (snd (snd z))) |\<in>| finite_system_clauses P)"

definition finite_raised_key ::
    "('s list \<times> 'd \<times> 'c \<times> ('a,'s,'d) finite_factor_schema) fset \<Rightarrow> 's list \<times> ('d \<times> 'c \<times> 's) option \<Rightarrow> bool" where
  "finite_raised_key N k \<longleftrightarrow> fst k \<noteq> [] \<longrightarrow> (case snd k of None \<Rightarrow> False
    | Some (e,c,s) \<Rightarrow> s = last (fst k) \<and>
      fBall N (\<lambda>z. fst z = butlast (fst k) \<longrightarrow> fst (snd z) = e \<and> fst (snd (snd z)) = c))"

definition finite_goals_raised :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_goals_raised P st \<longleftrightarrow> (let N = fimage resolution_node_key (resolution_nodes st) in
    finite_nodes_raised P N \<and> fBall (fimage resolution_goal_key (resolution_pending st)) (finite_raised_key N))"

lemma resolution_node_key_substitute [simp]:
  "resolution_node_key (resolution_node_substitute \<sigma> nd) = resolution_node_key nd"
  by (simp add: resolution_node_key_def)

lemma resolution_goal_key_substitute [simp]:
  "resolution_goal_key (resolution_goal_substitute \<sigma> g) = resolution_goal_key g"
  by (cases g) (simp_all add: resolution_goal_key_def)

lemma finite_goals_raised_substitute [simp]:
  "finite_goals_raised P (resolution_state_substitute \<sigma> st) \<longleftrightarrow> finite_goals_raised P st"
  by (simp add: finite_goals_raised_def resolution_state_substitute_def fset.map_comp comp_def)

lemma finite_goals_raised_fewer:
  assumes raised: "finite_goals_raised P st" and sub: "G |\<subseteq>| resolution_pending st"
  shows "finite_goals_raised P (Resolution_State G (resolution_nodes st) W)"
  using raised sub unfolding finite_goals_raised_def Let_def
  by (auto simp: fimage.rep_eq less_eq_fset.rep_eq)

lemma finite_goals_raised_clause:
  assumes raised: "finite_goals_raised P st" and pl: "search_placeable st"
    and g: "Resolution_Call_Goal q r d p |\<in>| resolution_pending st"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "finite_goals_raised P (Resolution_State (finite_clause_goals q d c S |\<union>|
      (resolution_pending st |-| {|Resolution_Call_Goal q r d p|})) (finsert (finite_clause_node q d c S) (resolution_nodes st)) W)"
proof -
  let ?N = "fimage resolution_node_key (resolution_nodes st)"
  let ?N' = "fimage resolution_node_key (finsert (finite_clause_node q d c S) (resolution_nodes st))"
  have noq: "resolution_node_position nd \<noteq> q" if "nd |\<in>| resolution_nodes st" for nd
    using pl g that unfolding search_placeable_def resolution_positions_distinct_def by force
  have par: "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = butlast (resolution_goal_position g')"
    if "g' |\<in>| resolution_pending st" "resolution_goal_position g' \<noteq> []" for g'
    using pl that unfolding search_placeable_def by (force simp: fimage_iff)
  have nodes: "finite_nodes_raised P ?N'"
    using raised clause unfolding finite_goals_raised_def finite_nodes_raised_def Let_def
    by (auto simp: fimage.rep_eq resolution_node_key_def finite_clause_node_def)
  have new: "finite_raised_key ?N' (q@[s],Some (d,c,s))" for s
    using noq by (auto simp: finite_raised_key_def fimage.rep_eq resolution_node_key_def
      finite_clause_node_def)
  have old: "finite_raised_key ?N' (resolution_goal_key g')" if g': "g' |\<in>| resolution_pending st" for g'
  proof (cases "resolution_goal_position g' = []")
    case True
    then show ?thesis by (simp add: finite_raised_key_def resolution_goal_key_def)
  next
    case False
    have k: "finite_raised_key ?N (resolution_goal_key g')"
      using raised fimageI[OF g', of resolution_goal_key] unfolding finite_goals_raised_def Let_def by blast
    obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g')"
      using par[OF g' False] by blast
    have nq: "butlast (resolution_goal_position g') \<noteq> q" using noq[OF nd(1)] nd(2) by simp
    show ?thesis using k nq
      by (auto simp: finite_raised_key_def resolution_goal_key_def fimage.rep_eq resolution_node_key_def
        finite_clause_node_def split: option.splits)
  qed
  have cg: "\<exists>s. resolution_goal_key x = (q@[s],Some (d,c,s))" if "x |\<in>| finite_clause_goals q d c S" for x
    using that by (auto simp: finite_clause_goals_def resolution_goal_key_def fimage.rep_eq)
  have gk: "fBall (fimage resolution_goal_key (finite_clause_goals q d c S |\<union>|
      (resolution_pending st |-| {|Resolution_Call_Goal q r d p|}))) (finite_raised_key ?N')"
  proof (rule fBallI)
    fix k assume "k |\<in>| fimage resolution_goal_key (finite_clause_goals q d c S |\<union>|
        (resolution_pending st |-| {|Resolution_Call_Goal q r d p|}))"
    then obtain x where x: "x |\<in>| finite_clause_goals q d c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r d p|})"
      and k: "k = resolution_goal_key x" by (auto elim: fimageE)
    show "finite_raised_key ?N' k"
    proof (cases "x |\<in>| finite_clause_goals q d c S")
      case True
      then obtain s where "resolution_goal_key x = (q@[s],Some (d,c,s))" using cg by blast
      then show ?thesis using new k by simp
    next
      case False
      then have "x |\<in>| resolution_pending st" using x by simp
      then show ?thesis using old k by simp
    qed
  qed
  show ?thesis using nodes gk unfolding finite_goals_raised_def Let_def by simp
qed

lemma finite_goals_raised_call:
  assumes raised: "finite_goals_raised P st" and pl: "search_placeable st"
    and g: "Resolution_Call_Goal q r d p |\<in>| resolution_pending st" and s: "st' |\<in>| finite_call_successors P st q r d p"
  shows "finite_goals_raised P st'"
proof -
  obtain c S u where cl: "((d,c),S) |\<in>| finite_system_clauses P"
    and st': "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q d c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r d p|}))
        (finsert (finite_clause_node q d c S) (resolution_nodes st)) (resolution_witnesses st))"
    using finite_call_successors_member[OF s] by blast
  show ?thesis unfolding st' finite_goals_raised_substitute by (rule finite_goals_raised_clause[OF raised pl g cl])
qed

lemma finite_goals_raised_material_state:
  assumes "finite_goals_raised P st"
  shows "finite_goals_raised P (finite_material_alternative_state st q r M z)"
  using assms by (cases z) (auto simp: finite_material_alternative_state_def intro!: finite_goals_raised_fewer)

lemma finite_goals_raised_successors:
  assumes raised: "finite_goals_raised P st" and pl: "search_placeable st" and g: "g |\<in>| resolution_pending st"
    and s: "st' |\<in>| finite_goal_successors P st g"
  shows "finite_goals_raised P st'"
proof (cases g)
  case (Resolution_Call_Goal q r d p)
  show ?thesis
  proof (cases "finite_reusable st g \<or> finite_table_closes resolution_empty_table g")
    case True
    then have "st' = finite_goal_closed st g" using s by (simp add: finite_closed_successors)
    then show ?thesis using raised by (auto simp: finite_goal_closed_def intro!: finite_goals_raised_fewer)
  next
    case False
    then have "st' |\<in>| finite_call_successors P st q r d p" using s Resolution_Call_Goal by simp
    then show ?thesis using finite_goals_raised_call[OF raised pl] g Resolution_Call_Goal by blast
  qed
next
  case (Resolution_Material_Goal q r M)
  then have "st' |\<in>| finite_material_successors st q r M" using s by simp
  then show ?thesis unfolding finite_material_successors_alternatives
    using finite_goals_raised_material_state[OF raised, of q r M] by (auto simp: fimage_iff)
qed

lemma finite_goals_raised_solutions:
  assumes raised: "finite_goals_raised P st" and s: "st' |\<in>| finite_solution_successors st q r M Ws"
  shows "finite_goals_raised P st'"
  using s unfolding finite_solution_successors_alternatives
  using finite_goals_raised_material_state[OF raised, of q r M] by (auto simp: fimage_iff)

lemma finite_goals_raised_construction:
  "finite_goals_raised P st \<Longrightarrow> finite_goals_raised P (finite_construction_step \<kappa> P' st nd)"
  by (auto simp: finite_construction_step_def Let_def intro!: finite_goals_raised_fewer)

lemma finite_initial_state_raised: "finite_goals_raised P (finite_initial_state d t)"
  by (simp add: finite_goals_raised_def finite_initial_state_def finite_nodes_raised_def finite_raised_key_def
    resolution_goal_key_def fimage.rep_eq)

definition shared_raised :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "shared_raised \<kappa> P r \<longleftrightarrow> search_formed \<kappa> P r \<and> search_placeable (search_project r) \<and>
    finite_goals_raised P (search_project r)"

lemma shared_raised_structure:
  assumes sock: "clause_sockets_distinct P"
  shows "committed_representation_structure (shared_committed_representation \<kappa> P) (shared_raised \<kappa> P) \<kappa> P"
proof -
  have pj: "rep_project (shared_committed_representation \<kappa> P) = search_project"
    by (simp add: shared_committed_representation_def)
  have e: "shared_raised \<kappa> P = (\<lambda>s. (search_formed \<kappa> P s \<and> search_placeable (search_project s)) \<and>
      finite_goals_raised P (rep_project (shared_committed_representation \<kappa> P) s))"
    by (simp add: fun_eq_iff shared_raised_def pj)
  show ?thesis unfolding e
  proof (rule committed_structure_invariant[where I = "finite_goals_raised P", OF shared_committed_structure[OF sock]],
      goal_cases)
    case (1 s nd)
    then show ?case by (simp add: finite_goals_raised_construction)
  next
    case (2 s g st')
    then show ?case using finite_goals_raised_successors[of P "search_project s" g st'] by (simp add: pj)
  next
    case (3 s q rr d p st')
    then show ?case using finite_goals_raised_call[of P "search_project s" q rr d p st'] by (simp add: pj)
  next
    case (4 s q rr M Ws st')
    then show ?case using finite_goals_raised_solutions[of P "search_project s" st' q rr M Ws] by (simp add: pj)
  next
    case (5 st \<sigma>)
    then show ?case by simp
  qed
qed

definition finite_declared_raisers ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> ('d \<times> 'c \<times> 's) fset" where
  "finite_declared_raisers P D = ffUnion (fimage (\<lambda>((e,c),S). fimage (\<lambda>z. (e,c,fst (snd (snd z))))
      (ffilter (\<lambda>z. fst z = e \<and> fst (snd z) = S) (declared_sockets D))) (finite_system_clauses P))"

lemma finite_declared_raisers_member:
  assumes "((e,c),S) |\<in>| finite_system_clauses P" and "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
  shows "(e,c,s) |\<in>| finite_declared_raisers P D"
  using assms unfolding finite_declared_raisers_def
  by (force simp: ffUnion.rep_eq fimage.rep_eq ffilter.rep_eq Set.filter_eq)

definition finite_raising_guard ::
    "('d \<times> 'c \<times> 's) fset \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_raising_guard X D M g \<longleftrightarrow> (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> fBex (declared_producers D) (\<lambda>z. fst z = d) \<or> fBex M (\<lambda>z. fst z = d) \<or>
        (case r of None \<Rightarrow> False | Some z \<Rightarrow> z |\<in>| X)
    | Resolution_Material_Goal q r N \<Rightarrow> r |\<in>| X)"

text \<open>The guard read on a shared goal, whose site and raiser the shared state keeps as they are.\<close>

definition shared_raising_guard ::
    "('d \<times> 'c \<times> 's) fset \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow>
      ('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_raising_guard X D M e \<longleftrightarrow> (case e of
      Shared_Call_Goal q r d p \<Rightarrow> fBex (declared_producers D) (\<lambda>z. fst z = d) \<or> fBex M (\<lambda>z. fst z = d) \<or>
        (case r of None \<Rightarrow> False | Some z \<Rightarrow> z |\<in>| X)
    | Shared_Material_Goal q r N \<Rightarrow> r |\<in>| X)"

lemma shared_raising_guard_project:
  "finite_raising_guard X D M (shared_goal_project T e) \<longleftrightarrow> shared_raising_guard X D M e"
  by (cases e) (simp_all add: finite_raising_guard_def shared_raising_guard_def)

lemma finite_socket_commitment_framed_node:
  assumes "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
  shows "\<exists>nd keep. resolution_goal_position g \<noteq> [] \<and> nd |\<in>| resolution_nodes st \<and>
    resolution_node_position nd = butlast (resolution_goal_position g) \<and>
    (resolution_node_site nd,resolution_node_schema nd,last (resolution_goal_position g),keep,Vp,Vh) |\<in>| declared_sockets D"
  using assms by (cases g) (force simp: finite_socket_commitment_framed_def finite_socket_declared_framed_def
    finite_socket_kept_framed_def finite_socket_free_framed_def split: option.splits prod.splits)+

theorem finite_raising_guard_refuses:
  assumes nodes: "finite_nodes_raised P (fimage resolution_node_key (resolution_nodes st))"
    and key: "finite_raised_key (fimage resolution_node_key (resolution_nodes st)) (resolution_goal_key g)"
    and ng: "\<not> finite_raising_guard (finite_declared_raisers P D) D M g"
  shows "\<not> commit_call (finite_framed_commitment D \<Phi>) F st g" and "\<not> commit_material (finite_framed_commitment D \<Phi>) F st g"
proof -
  have sock: "\<not> finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g" for Vp Vh ch
  proof
    assume "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
    then obtain nd keep where nq: "resolution_goal_position g \<noteq> []" and nd: "nd |\<in>| resolution_nodes st"
        "resolution_node_position nd = butlast (resolution_goal_position g)"
      and dec: "(resolution_node_site nd,resolution_node_schema nd,last (resolution_goal_position g),keep,Vp,Vh) |\<in>|
        declared_sockets D"
      using finite_socket_commitment_framed_node by blast
    obtain e c s where r: "resolution_goal_raiser g = Some (e,c,s)" and sl: "s = last (resolution_goal_position g)"
      and par: "fBall (fimage resolution_node_key (resolution_nodes st))
        (\<lambda>z. fst z = butlast (resolution_goal_position g) \<longrightarrow> fst (snd z) = e \<and> fst (snd (snd z)) = c)"
      using key nq by (auto simp: finite_raised_key_def resolution_goal_key_def split: option.splits)
    have nk: "resolution_node_key nd |\<in>| fimage resolution_node_key (resolution_nodes st)" using nd(1) by (rule fimageI)
    have "fst (resolution_node_key nd) = butlast (resolution_goal_position g) \<longrightarrow>
        fst (snd (resolution_node_key nd)) = e \<and> fst (snd (snd (resolution_node_key nd))) = c"
      using par nk by blast
    then have ec: "resolution_node_site nd = e" "resolution_node_clause nd = c" using nd(2) by (simp_all add: resolution_node_key_def)
    have "((fst (snd (resolution_node_key nd)),fst (snd (snd (resolution_node_key nd)))),snd (snd (snd (resolution_node_key nd))))
        |\<in>| finite_system_clauses P"
      using nodes nk unfolding finite_nodes_raised_def by blast
    then have cl: "((e,c),resolution_node_schema nd) |\<in>| finite_system_clauses P" using ec by (simp add: resolution_node_key_def)
    have "(e,c,s) |\<in>| finite_declared_raisers P D"
      using finite_declared_raisers_member[OF cl] dec ec sl by simp
    then show False using ng r by (cases g) (auto simp: finite_raising_guard_def)
  qed
  have dir: "\<not> finite_direct_commitment D F st g"
  proof
    assume "finite_direct_commitment D F st g"
    then obtain d V hs where m: "(d,V,hs) |\<in>| declared_producers D" and c: "finite_producer_commits D F st g d V hs"
      unfolding finite_direct_commitment_def by blast
    from c obtain q r p where "g = Resolution_Call_Goal q r d p"
      by (cases g) (auto simp: finite_producer_commits_def)
    with m ng show False unfolding finite_raising_guard_def by force
  qed
  show "\<not> commit_call (finite_framed_commitment D \<Phi>) F st g" and "\<not> commit_material (finite_framed_commitment D \<Phi>) F st g"
    using sock dir by (auto simp: finite_framed_commitment_def)
qed

theorem finite_raising_moded_refuses:
  assumes nodes: "finite_nodes_raised P (fimage resolution_node_key (resolution_nodes st))"
    and key: "finite_raised_key (fimage resolution_node_key (resolution_nodes st)) (resolution_goal_key g)"
    and ng: "\<not> finite_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M g"
  shows "\<not> commit_call (finite_narrowed_commitment Pg m D \<Phi>) F st g \<and>
    \<not> commit_material (finite_narrowed_commitment Pg m D \<Phi>) F st g \<and>
    \<not> finite_moded_priority (finite_narrowed_commitment Pg m D \<Phi>) Dm M st g"
proof -
  have c: "\<not> commit_call (finite_narrowed_commitment Pg m D \<Phi>) F' st g" for F'
    using finite_raising_guard_refuses(1)[OF nodes key ng] by simp
  have n: "\<not> commit_material (finite_narrowed_commitment Pg m D \<Phi>) F' st g" for F'
    using finite_raising_guard_refuses(2)[OF nodes key ng] by simp
  have s: "\<not> (case g of Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>z. fst z = d) | Resolution_Material_Goal q r N \<Rightarrow> False)"
    using ng by (cases g) (simp_all add: finite_raising_guard_def)
  show ?thesis using c n finite_moded_priority_refused[OF c n s] by blast
qed

text \<open>
  The route's committed step: the narrowed commitment's tests and moded priority read through the access, at the
  guard read on the shared goal, over the shared states that keep the raising invariant. Its search is R5's committed
  search at the moded selection.
\<close>

theorem shared_raising_formed:
  assumes sock: "clause_sockets_distinct P"
  shows "tested_representation_formed (shared_committed_representation \<kappa> P) (shared_raised \<kappa> P) \<kappa> P
    (finite_narrowed_commitment P m D \<Phi>) (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
    (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
      Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)))
    (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M (shared_entry_goal h))"
proof (rule commitment_tests_formed[OF shared_raised_structure[OF sock]], goal_cases)
  case (1 s)
  then show ?case using shared_commitment_formed[of \<kappa> P s]
    by (simp add: shared_raised_def shared_committed_representation_def)
next
  case 2
  show ?case by (rule access_narrowed_commitment_exact)
next
  case (3 s h F)
  let ?st = "search_project s" let ?g = "access_goal (shared_access \<kappa> P s) h"
  have f: "search_formed \<kappa> P s" and rs: "finite_goals_raised P ?st" using 3(1) by (simp_all add: shared_raised_def)
  interpret v: access_formed \<kappa> P "shared_access \<kappa> P s" ?st by (rule shared_access_formed[OF f])
  have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" using 3(2) by (simp add: shared_committed_representation_def)
  have g: "?g |\<in>| resolution_pending ?st" by (rule v.goal_in_pending[OF h'])
  have nd: "finite_nodes_raised P (fimage resolution_node_key (resolution_nodes ?st))"
    using rs by (simp add: finite_goals_raised_def Let_def)
  have key: "finite_raised_key (fimage resolution_node_key (resolution_nodes ?st)) (resolution_goal_key ?g)"
    using rs fimageI[OF g, of resolution_goal_key] unfolding finite_goals_raised_def Let_def by blast
  have ng: "\<not> finite_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M ?g"
    using 3(3) by (simp add: shared_access_simps shared_raising_guard_project)
  have fn: "resolution_nodes (finite_focused F ?st) = resolution_nodes ?st" by (simp add: finite_focused_def)
  have ndF: "finite_nodes_raised P (fimage resolution_node_key (resolution_nodes (finite_focused F ?st)))" using nd fn by simp
  have keyF: "finite_raised_key (fimage resolution_node_key (resolution_nodes (finite_focused F ?st))) (resolution_goal_key ?g)"
    using key fn by simp
  have a: "\<not> commit_call (finite_narrowed_commitment P m D \<Phi>) F ?st ?g \<and>
      \<not> commit_material (finite_narrowed_commitment P m D \<Phi>) F ?st ?g"
    using finite_raising_moded_refuses[OF nd key ng] by blast
  have b: "\<not> finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M (finite_focused F ?st) ?g"
    using finite_raising_moded_refuses[OF ndF keyF ng] by blast
  show ?case using a b by (simp add: shared_committed_representation_def)
qed

corollary shared_raising_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and rs: "finite_goals_raised P st"
  shows "tested_committed_search (shared_committed_representation \<kappa> P)
      (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
        Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
          (resolution_declarations.truncate D) M (shared_entry_goal h)))
      (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)) \<kappa> P n F B (search_of P st) =
    finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P n F B st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have f: "shared_raised \<kappa> P (search_of P st)" using search_of[OF d] pl rs by (simp add: shared_raised_def)
  show ?thesis using tested_representation_formed.tested_search[OF shared_raising_formed[OF sock] f] search_of(2)[OF d]
    by (simp add: shared_committed_representation_def)
qed

section \<open>The route forms' constants and their code\<close>

text \<open>
  Review 702's follow-up 3 (F2c's option (a)). Each form a route consumer calls is a constant defined equal to its
  form, at a narrowed commitment and the moded selection: the moded committed forms at @{term None}, for pattern roots,
  and the moded check forms, numbered and native. Its code equation runs the shared committed search at the moded
  priority and the guard above (@{text shared_moded_search}), so code generation runs no abstract search at a form
  the route calls; a program whose clause sockets are not distinct keeps the form's own equation. No form's statement
  changes: each constant's contract is its form's, through its definition.
\<close>

definition moded_committed_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n =
    finite_moded_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P d t n"

definition moded_check_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n =
    finite_check_resolution_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P d t n"

definition moded_committed_demand ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "moded_committed_demand \<kappa> P m D \<Phi> Dm M Q n =
    finite_committed_demand_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P Q n"

definition moded_check_demand ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "moded_check_demand \<kappa> P m D \<Phi> Dm M Q n =
    finite_check_demand_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P Q n"

definition native_moded_committed_resolution ::
    "(local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> nat \<Rightarrow>
      (local_address,local_address,local_address option definition_site,'v) produced_declarations \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_frames \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_declarations \<Rightarrow>
      local_address option definition_site resolution_modes \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow>
      ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_moded_committed_resolution \<kappa> P m D \<Phi> Dm M R n =
    native_committed_resolution_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P R n"

definition native_moded_check_resolution ::
    "(local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> nat \<Rightarrow>
      (local_address,local_address,local_address option definition_site,'v) produced_declarations \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_frames \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_declarations \<Rightarrow>
      local_address option definition_site resolution_modes \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow>
      ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n =
    native_check_resolution_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P R n"

lemma moded_committed_resolution_code [code]:
  "moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n = finite_outcome_result P d t (if clause_sockets_distinct P
    then represented_committed_search (shared_committed_representation \<kappa> P)
      (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
      (\<lambda>s h. finite_moded_guard (resolution_declarations.truncate D) M (access_goal (shared_access \<kappa> P s) h))
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n None {||} (search_of P (finite_initial_state d t))
    else finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P n None {||} (finite_initial_state d t))"
  by (simp add: moded_committed_resolution_def finite_committed_resolution_by_def
    shared_moded_search[OF _ finite_initial_state_placeable])

lemma moded_check_resolution_code [code]:
  "moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n = finite_outcome_result P d t (if clause_sockets_distinct P
    then represented_committed_search (shared_committed_representation \<kappa> P)
      (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
      (\<lambda>s h. finite_moded_guard (resolution_declarations.truncate D) M (access_goal (shared_access \<kappa> P s) h))
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n (Some []) {||} (search_of P (finite_initial_state d t))
    else finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P n (Some []) {||} (finite_initial_state d t))"
  by (simp add: moded_check_resolution_def finite_check_resolution_by_def
    shared_moded_search[OF _ finite_initial_state_placeable])

lemma moded_committed_demand_code [code]:
  "moded_committed_demand \<kappa> P m D \<Phi> Dm M Q n = (let V = fimage (\<lambda>q. (q,finite_resolution_verdict
      (moded_committed_resolution \<kappa> P m D \<Phi> Dm M (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_committed_demand_def finite_committed_demand_by_def moded_committed_resolution_def)

lemma moded_check_demand_code [code]:
  "moded_check_demand \<kappa> P m D \<Phi> Dm M Q n = (let V = fimage (\<lambda>q. (q,finite_resolution_verdict
      (moded_check_resolution \<kappa> P m D \<Phi> Dm M (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_check_demand_def finite_check_demand_by_def finite_check_verdict_by_def moded_check_resolution_def)

lemma native_moded_committed_resolution_code [code]:
  "native_moded_committed_resolution \<kappa> P m D \<Phi> Dm M R n =
    (fimage (\<lambda>q. (q,moded_committed_resolution \<kappa> P m D \<Phi> Dm M (fst q) (snd q) n)) R,
      moded_committed_demand \<kappa> P m D \<Phi> Dm M R n)"
  by (simp add: native_moded_committed_resolution_def native_committed_resolution_by_def
    moded_committed_resolution_def moded_committed_demand_def)

lemma native_moded_check_resolution_code [code]:
  "native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n =
    (fimage (\<lambda>q. (q,moded_check_resolution \<kappa> P m D \<Phi> Dm M (fst q) (snd q) n)) R,
      moded_check_demand \<kappa> P m D \<Phi> Dm M R n)"
  by (simp add: native_moded_check_resolution_def native_check_resolution_by_def
    moded_check_resolution_def moded_check_demand_def)

text \<open>
  Task 869. The route's search at a commitment through the access and the raising guard's declared raisers, both
  given as arguments, so that a call builds the access commitment (its framed index) and the raisers once, and a demand
  or a native form once for all its calls. At the narrowed commitment's access form and the declarations' raisers it is
  R5's committed search at the moded selection (@{text moded_route_resolution_exact}), so the constants' code
  equations below take it; the code equations above keep their statements.
\<close>

definition moded_route_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow>
      (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) access_commitment \<Rightarrow>
      ('d \<times> 'c \<times> 's) fset \<Rightarrow> 's list option \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "moded_route_resolution \<kappa> P m D \<Phi> Dm M Kc X F0 d t n =
    (let gd = (\<lambda>r h. shared_raising_guard X (resolution_declarations.truncate D) M (shared_entry_goal h)) in
    finite_outcome_result P d t (if clause_sockets_distinct P
      then tested_committed_search (shared_committed_representation \<kappa> P)
        (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access Kc Dm M gd) gd \<kappa> P n F0 {||}
        (search_of P (finite_initial_state d t))
      else finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
        (finite_narrowed_commitment P m D \<Phi>) P n F0 {||} (finite_initial_state d t)))"

theorem moded_route_resolution_exact:
  "moded_route_resolution \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
      (finite_declared_raisers P (resolution_declarations.truncate D)) F0 d t n =
    finite_outcome_result P d t (finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P)
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n F0 {||} (finite_initial_state d t))"
  by (simp add: moded_route_resolution_def Let_def
    shared_raising_search[OF _ finite_initial_state_placeable finite_initial_state_raised])

declare moded_committed_resolution_code [code del] moded_check_resolution_code [code del]
  moded_committed_demand_code [code del] moded_check_demand_code [code del]
  native_moded_committed_resolution_code [code del] native_moded_check_resolution_code [code del]

lemma moded_committed_resolution_route [code]:
  "moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n = moded_route_resolution \<kappa> P m D \<Phi> Dm M
    (access_narrowed_commitment P m D \<Phi>) (finite_declared_raisers P (resolution_declarations.truncate D)) None d t n"
  by (simp add: moded_route_resolution_exact moded_committed_resolution_def finite_committed_resolution_by_def)

lemma moded_check_resolution_route [code]:
  "moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n = moded_route_resolution \<kappa> P m D \<Phi> Dm M
    (access_narrowed_commitment P m D \<Phi>) (finite_declared_raisers P (resolution_declarations.truncate D)) (Some []) d t n"
  by (simp add: moded_route_resolution_exact moded_check_resolution_def finite_check_resolution_by_def)

lemma moded_committed_demand_route [code]:
  "moded_committed_demand \<kappa> P m D \<Phi> Dm M Q n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D);
      V = fimage (\<lambda>q. (q,finite_resolution_verdict (moded_route_resolution \<kappa> P m D \<Phi> Dm M Kc X None (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_committed_demand_code moded_committed_resolution_route Let_def)

lemma moded_check_demand_route [code]:
  "moded_check_demand \<kappa> P m D \<Phi> Dm M Q n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D);
      V = fimage (\<lambda>q. (q,finite_resolution_verdict (moded_route_resolution \<kappa> P m D \<Phi> Dm M Kc X (Some []) (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_check_demand_code moded_check_resolution_route Let_def)

lemma native_moded_committed_resolution_route [code]:
  "native_moded_committed_resolution \<kappa> P m D \<Phi> Dm M R n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D);
      T = fimage (\<lambda>q. (q,moded_route_resolution \<kappa> P m D \<Phi> Dm M Kc X None (fst q) (snd q) n)) R;
      V = fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) T in
    (T,if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
      then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None))"
  by (simp add: native_moded_committed_resolution_code moded_committed_demand_code moded_committed_resolution_route
    Let_def fset.map_comp comp_def)

lemma native_moded_check_resolution_route [code]:
  "native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D);
      T = fimage (\<lambda>q. (q,moded_route_resolution \<kappa> P m D \<Phi> Dm M Kc X (Some []) (fst q) (snd q) n)) R;
      V = fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) T in
    (T,if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
      then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None))"
  by (simp add: native_moded_check_resolution_code moded_check_demand_code moded_check_resolution_route
    Let_def fset.map_comp comp_def)

export_code moded_committed_resolution moded_check_resolution moded_committed_demand moded_check_demand
  native_moded_committed_resolution native_moded_check_resolution checking SML

text \<open>
  The constants' contracts are their forms' at the moded priority of a narrowed commitment: at rc's premises
  (@{text committed_registrations}) the numbered forms are exact by rc's moded forms and the check instances above,
  and the native forms by O3's and the native check instance, each through the constant's definition.
\<close>

context committed_registrations
begin

lemma moded_check_resolution_exact:
  shows "moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  unfolding moded_check_resolution_def
  by (erule finite_check_resolution_by_sound(3))
    (erule finite_check_resolution_by_refutation_exact[OF registered_commitment_at.exact_premises[OF registered_at]])

lemma moded_check_demand_exact:
  assumes "moded_check_demand \<kappa> P m D \<Phi> Dm M Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_check_demand_by_exact[OF registered_commitment_at.exact_premises[OF registered_at]
    assms[unfolded moded_check_demand_def]] by blast+

lemma moded_committed_resolution_exact:
  shows "moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    and "finite_resolution_refutes (moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  unfolding moded_committed_resolution_def
  by (erule committed_moded_resolution_exact(1)) (erule committed_moded_resolution_exact(2))

lemma moded_committed_demand_exact:
  assumes "moded_committed_demand \<kappa> P m D \<Phi> Dm M Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using committed_moded_demand_exact[OF assms[unfolded moded_committed_demand_def]] by blast+

end

theorem native_moded_check_exact:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "committed_registrations \<kappa> P m D \<Phi> corr"
    and result: "native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_registered_check_at[OF registered result[unfolded native_moded_check_resolution_def]]
  by blast+

lemmas native_moded_committed_exact = native_committed_moded_exact[folded native_moded_committed_resolution_def]

end
