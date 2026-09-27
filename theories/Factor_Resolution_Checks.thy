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

text \<open>
  The check forms at a table (DECISIONS.md, task 495's entry, "The given's calls are decided once", GT2): the committed
  search at the table started at the root's own focus, read by the result at the table. Each form above is its
  instance at the empty table (@{text finite_check_resolution_by_in_empty} and its siblings), and every statement
  below at a table has the form above's as that instance, by name and statement.
\<close>

definition finite_check_resolution_by_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n =
    finite_outcome_result_in \<Theta> P d t (finite_committed_search_by_in \<Theta> sel \<kappa> K P n (Some []) {||} (finite_initial_state d t))"

lemma finite_check_resolution_by_in_empty:
  "finite_check_resolution_by_in resolution_empty_table sel \<kappa> K P d t n = finite_check_resolution_by sel \<kappa> K P d t n"
  by (simp only: finite_check_resolution_by_in_def finite_check_resolution_by_def finite_outcome_result_def)

definition finite_check_verdict_by_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "finite_check_verdict_by_in \<Theta> sel \<kappa> K P d t n = finite_resolution_verdict (finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n)"

lemma finite_check_verdict_by_in_empty:
  "finite_check_verdict_by_in resolution_empty_table sel \<kappa> K P d t n = finite_check_verdict_by sel \<kappa> K P d t n"
  by (simp only: finite_check_verdict_by_in_def finite_check_verdict_by_def finite_check_resolution_by_in_empty)

definition finite_check_demand_by_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "finite_check_demand_by_in \<Theta> sel \<kappa> K P D n = (let V = fimage (\<lambda>q. (q,finite_check_verdict_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n)) D in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"

lemma finite_check_demand_by_in_empty:
  "finite_check_demand_by_in resolution_empty_table sel \<kappa> K P D n = finite_check_demand_by sel \<kappa> K P D n"
  by (simp only: finite_check_demand_by_in_def finite_check_demand_by_def finite_check_verdict_by_in_empty)

definition native_check_resolution_by_in ::
    "(local_address,local_address,local_address option definition_site,local_address) resolution_table \<Rightarrow>
      ((local_address,local_address,local_address option definition_site,local_address) resolution_state \<Rightarrow>
        (local_address,local_address,local_address option definition_site,local_address) resolution_selection) \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) resolution_commitment \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      nat \<Rightarrow> ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_check_resolution_by_in \<Theta> sel \<kappa> K P R n =
    (fimage (\<lambda>q. (q,finite_check_resolution_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n)) R, finite_check_demand_by_in \<Theta> sel \<kappa> K P R n)"

lemma native_check_resolution_by_in_empty:
  "native_check_resolution_by_in resolution_empty_table sel \<kappa> K P R n = native_check_resolution_by sel \<kappa> K P R n"
  by (simp only: native_check_resolution_by_in_def native_check_resolution_by_def finite_check_resolution_by_in_empty
    finite_check_demand_by_in_empty)

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

theorem finite_check_resolution_by_sound_in:
  assumes res: "finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n = Finite_Resolved C"
  shows "C\<noteq>{||}" and "\<And>p. p |\<in>| C \<Longrightarrow> finite_checks_schema_proof P p d t"
    and "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  using finite_outcome_result_sound_in[OF res[unfolded finite_check_resolution_by_in_def]] by blast+

lemmas finite_check_resolution_by_sound =
  finite_check_resolution_by_sound_in[where \<Theta>=resolution_empty_table, unfolded finite_check_resolution_by_in_empty]

theorem finite_check_resolution_by_certificates_in:
  assumes valid: "finite_table_valid P \<Theta>" and Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
  shows "finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n =
    (let R = finite_committed_search_by_in \<Theta> sel \<kappa> K P n (Some []) {||} (finite_initial_state d t);
      C = ffUnion (fimage (finite_state_proofs_in \<Theta>) (resolution_found R)) in
    if C\<noteq>{||} then Finite_Resolved C else if resolution_diagnoses R={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R))"
  unfolding finite_check_resolution_by_in_def
  by (rule finite_focused_resolution_certificates_in[OF valid Pf tf \<kappa> goals, where F="Some []"])
    (simp_all add: resolution_focused_def)

lemmas finite_check_resolution_by_certificates = finite_check_resolution_by_certificates_in[where \<Theta>=resolution_empty_table,
  OF finite_table_valid_empty, unfolded finite_check_resolution_by_in_empty finite_state_proofs_empty]

theorem finite_check_resolution_by_refutation_exact_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and refutes: "finite_resolution_refutes (finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (rule finite_focused_resolution_refutation_exact_in[OF given _ refutes[unfolded finite_check_resolution_by_in_def]])
    (simp add: resolution_focused_def)

lemmas finite_check_resolution_by_refutation_exact =
  finite_check_resolution_by_refutation_exact_in[where \<Theta>=resolution_empty_table, unfolded finite_check_resolution_by_in_empty]

lemmas finite_check_resolution_by_exact =
  finite_check_resolution_by_sound(3) finite_check_resolution_by_refutation_exact

lemma finite_check_verdict_by_exact_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and verdict: "finite_check_verdict_by_in \<Theta> sel \<kappa> K P d t n = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_focused_verdict_exact_in[OF given _
    verdict[unfolded finite_check_verdict_by_in_def finite_check_resolution_by_in_def]]) (simp add: resolution_focused_def)

lemmas finite_check_verdict_by_exact =
  finite_check_verdict_by_exact_in[where \<Theta>=resolution_empty_table, unfolded finite_check_verdict_by_in_empty]

theorem finite_check_demand_by_exact_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and result: "finite_check_demand_by_in \<Theta> sel \<kappa> K P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  note demand = finite_verdict_demand_exact[OF result[unfolded finite_check_demand_by_in_def]]
  show "schema_system_formed (decode_finite_system P)"
    by (rule demand(1)) (rule finite_check_verdict_by_exact_in[OF given])
  show "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    by (rule demand(2)) (rule finite_check_verdict_by_exact_in[OF given])
qed

lemmas finite_check_demand_by_exact =
  finite_check_demand_by_exact_in[where \<Theta>=resolution_empty_table, unfolded finite_check_demand_by_in_empty]

theorem native_check_resolution_by_exact_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and result: "native_check_resolution_by_in \<Theta> sel \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  from result have T: "T = fimage (\<lambda>q. (q,finite_check_resolution_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n)) R"
    and A: "A = finite_check_demand_by_in \<Theta> sel \<kappa> K P R n"
    by (simp_all add: native_check_resolution_by_in_def)
  have resolved: "C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    if res: "finite_check_resolution_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n = Finite_Resolved C" for q C
    using finite_check_resolution_by_sound_in[OF res] by (simp add: decode_finite_call_term_fields)
  have refuted: "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    if "finite_resolution_refutes (finite_check_resolution_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n)" for q
    using finite_check_resolution_by_refutation_exact_in[OF given that] by (simp add: decode_finite_call_term_fields)
  have demand: "schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    if "A = Some B" for B
    using finite_check_demand_by_exact_in[OF given that[unfolded A]] by blast
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

lemmas native_check_resolution_by_exact =
  native_check_resolution_by_exact_in[where \<Theta>=resolution_empty_table, unfolded native_check_resolution_by_in_empty]

text \<open>
  The four forms whose first premise is the committed forms' premises, stated once: every instance below is this
  bundle at an instance's premises, nothing proved again; at a table, the bundle at the committed forms' premises there.
\<close>

lemmas finite_check_forms_exact_in = finite_check_resolution_by_refutation_exact_in finite_check_verdict_by_exact_in
  finite_check_demand_by_exact_in native_check_resolution_by_exact_in

lemmas finite_check_forms_exact = finite_check_resolution_by_refutation_exact finite_check_verdict_by_exact
  finite_check_demand_by_exact native_check_resolution_by_exact

section \<open>The check forms at a table read by its calls alone\<close>

text \<open>
  A resolution at a table is sound whatever the table holds, the result keeping only certificates the checker accepts
  (@{text finite_check_resolution_by_sound_in}); a found state of the check search at a table whose calls are true
  makes the root call true (@{text finite_check_found_true}), whatever certificates the entries hold, the search being
  the one at the valid table of the same calls (@{text finite_check_search_certified}). That is where the route's
  verdicts read a table whose calls are true but whose certificates the checker does not accept (GT6 retains none,
  an installation's relocated table carries none): GT4's graph verdicts of such a found state
  (@{text finite_state_graph_verdicts_in}), sound wherever the table's calls are true
  (@{text finite_state_graph_verdicts_in_true}). At two valid tables of the same calls the check forms return an
  outcome of the same kind (GT2a's calls-alone statement, @{text finite_committed_resolution_by_calls}, carried to them).
\<close>

lemma finite_check_search_certified:
  "finite_committed_search_by_in (finite_table_certified P \<Theta>) sel \<kappa> K P n (Some []) B st =
    finite_committed_search_by_in \<Theta> sel \<kappa> K P n (Some []) B st"
  by (simp only: finite_committed_search_calls[OF finite_table_certified_calls])

theorem finite_check_found_true:
  assumes true: "finite_table_true P \<Theta>" and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
    and Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and found: "st |\<in>| resolution_found (finite_committed_search_by_in \<Theta> sel \<kappa> K P n (Some []) {||} (finite_initial_state d t))"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_found_true[OF true \<kappa> goals Pf tf finite_check_root_focused found])

theorem finite_check_resolution_by_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
    and valid: "finite_table_valid P \<Theta>" and valid': "finite_table_valid P \<Theta>'"
    and Pf: "finite_system_formed P" and tf: "finite_term_formed t" and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
  shows "finite_resolution_verdict (finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n) =
      finite_resolution_verdict (finite_check_resolution_by_in \<Theta>' sel \<kappa> K P d t n)"
    and "finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n = Finite_Unresolved D \<longleftrightarrow>
      finite_check_resolution_by_in \<Theta>' sel \<kappa> K P d t n = Finite_Unresolved D"
proof -
  note c = finite_focused_resolution_calls[OF calls valid valid' Pf tf \<kappa> goals finite_check_root_focused]
  show "finite_resolution_verdict (finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n) =
      finite_resolution_verdict (finite_check_resolution_by_in \<Theta>' sel \<kappa> K P d t n)"
    unfolding finite_check_resolution_by_in_def by (rule c(1))
  show "finite_check_resolution_by_in \<Theta> sel \<kappa> K P d t n = Finite_Unresolved D \<longleftrightarrow>
      finite_check_resolution_by_in \<Theta>' sel \<kappa> K P d t n = Finite_Unresolved D"
    unfolding finite_check_resolution_by_in_def by (rule c(2))
qed

theorem finite_check_demand_by_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
    and valid: "finite_table_valid P \<Theta>" and valid': "finite_table_valid P \<Theta>'" and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
    and tfs: "\<And>q. q |\<in>| D \<Longrightarrow> finite_term_formed (snd q)"
  shows "finite_check_demand_by_in \<Theta> sel \<kappa> K P D n = finite_check_demand_by_in \<Theta>' sel \<kappa> K P D n"
proof -
  have v: "finite_check_verdict_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n = finite_check_verdict_by_in \<Theta>' sel \<kappa> K P (fst q) (snd q) n"
    if "q |\<in>| D" "finite_system_formed P" for q
    unfolding finite_check_verdict_by_in_def
    by (rule finite_check_resolution_by_calls(1)[OF calls valid valid' that(2) tfs[OF that(1)] \<kappa> goals])
  show ?thesis unfolding finite_check_demand_by_in_def by (rule finite_verdict_demand_agree) (rule v)
qed

theorem native_check_resolution_by_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
    and valid: "finite_table_valid P \<Theta>" and valid': "finite_table_valid P \<Theta>'"
    and Pf: "finite_system_formed P" and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and goals: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
    and tfs: "\<And>q. q |\<in>| R \<Longrightarrow> finite_term_formed (snd q)"
  shows "snd (native_check_resolution_by_in \<Theta> sel \<kappa> K P R n) = snd (native_check_resolution_by_in \<Theta>' sel \<kappa> K P R n)"
    and "fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) (fst (native_check_resolution_by_in \<Theta> sel \<kappa> K P R n)) =
      fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) (fst (native_check_resolution_by_in \<Theta>' sel \<kappa> K P R n))"
proof -
  show "snd (native_check_resolution_by_in \<Theta> sel \<kappa> K P R n) = snd (native_check_resolution_by_in \<Theta>' sel \<kappa> K P R n)"
    by (simp only: native_check_resolution_by_in_def snd_conv finite_check_demand_by_calls[OF calls valid valid' \<kappa> goals tfs])
  have v: "finite_resolution_verdict (finite_check_resolution_by_in \<Theta> sel \<kappa> K P (fst q) (snd q) n) =
      finite_resolution_verdict (finite_check_resolution_by_in \<Theta>' sel \<kappa> K P (fst q) (snd q) n)" if "q |\<in>| R" for q
    by (rule finite_check_resolution_by_calls(1)[OF calls valid valid' Pf tfs[OF that] \<kappa> goals])
  show "fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) (fst (native_check_resolution_by_in \<Theta> sel \<kappa> K P R n)) =
      fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) (fst (native_check_resolution_by_in \<Theta>' sel \<kappa> K P R n))"
    unfolding native_check_resolution_by_in_def fst_conv by (rule native_resolution_verdicts_agree) (erule v)
qed

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

text \<open>At a table, rc's forms at a priority and their check instances, from the premises at the table.\<close>

lemmas registered_checks_exact_in = finite_check_forms_exact_in[OF registered_commitment_at_in.exact_premises_in]

context committed_registrations_in
begin

lemmas committed_registered_checks_exact_in =
  finite_check_resolution_by_refutation_exact_in[OF registered_commitment_at_in.exact_premises_in[OF registered_at_in]]
  finite_check_verdict_by_exact_in[OF registered_commitment_at_in.exact_premises_in[OF registered_at_in]]
  finite_check_demand_by_exact_in[OF registered_commitment_at_in.exact_premises_in[OF registered_at_in]]

end

section \<open>The transfers at an installed program\<close>

text \<open>
  Where a route build calls a check form at a program an installed site reads (#547, the first request's, at its
  installed program; #707 and #399 at the asked relation's), the native check form there is exact at every priority, and at the
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
  after @{text finite_renamed_meaning_at}), which #547, #707 and #399 take so. The relocation transfer alone does not
  relate them. At a table the same holds between the check verdicts at the two programs' tables, each exact from the
  premises there; a table's calls are carried to the agreeing, relocated and installed programs by the table's own
  transfers (@{text finite_table_true_agreement}, @{text finite_table_true_relocated}), so the numbered table's validity
  makes the relocated table's calls true where the installed program is read.
\<close>

corollary finite_check_agreement_transfer_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and given': "finite_committed_exact_premises_in \<Theta>' J' sel' \<kappa>' K' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and v: "finite_check_verdict_by_in \<Theta> sel \<kappa> K P d t n = Some b"
    and v': "finite_check_verdict_by_in \<Theta>' sel' \<kappa>' K' Q d t m = Some b'"
  shows "b = b'"
  by (rule finite_exact_verdicts_equal[OF finite_check_verdict_by_exact_in[OF given v]
    finite_check_verdict_by_exact_in[OF given' v'] positive_meaning_dependency_locality[OF Pf Qf agree closed dV, symmetric]])

lemmas finite_check_agreement_transfer = finite_check_agreement_transfer_in[where \<Theta>=resolution_empty_table
  and \<Theta>'=resolution_empty_table, unfolded finite_check_verdict_by_in_empty]

corollary finite_check_relocation_transfer_in:
  assumes given: "finite_committed_exact_premises_in \<Theta> J sel \<kappa> K P"
    and given': "finite_committed_exact_premises_in \<Theta>' J' sel' \<kappa>' K' (finite_rename_system g P)"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    and v: "finite_check_verdict_by_in \<Theta> sel \<kappa> K P d t n = Some b"
    and v': "finite_check_verdict_by_in \<Theta>' sel' \<kappa>' K' (finite_rename_system g P) (g d) t m = Some b'"
  shows "b = b'"
  by (rule finite_exact_verdicts_equal[OF finite_check_verdict_by_exact_in[OF given v]
    finite_check_verdict_by_exact_in[OF given' v'] finite_renamed_meaning_at[OF Pf injective]])

lemmas finite_check_relocation_transfer = finite_check_relocation_transfer_in[where \<Theta>=resolution_empty_table
  and \<Theta>'=resolution_empty_table, unfolded finite_check_verdict_by_in_empty]

subsection \<open>The table's own transfers\<close>

text \<open>
  A table is read by its calls alone. Its calls true at a program are true at every program agreeing with it on a
  dependency-closed set holding their sites (the locality of positive meaning), and there the certified table of the
  same calls is valid (@{thm [source] finite_table_certified_valid}): so a table valid at the numbered readers serves
  every numbered program agreeing with them on its calls' sites and their callee closure, the check forms reading it
  there as the valid table of its calls (@{text finite_check_resolution_by_calls}). A table relocated by a placement —
  each call's site mapped, its term unchanged — has its calls true at the relocated program where the numbered table's
  are true (@{text finite_renamed_meaning_at}), and at every alpha variant of that program, as the program an installed
  site reads is (V3's @{text installed_variant}, @{text system_alpha_positive_meaning}): the installation's meaning
  correspondence, with no second production and no second check (decision 5; Q33 (d), provisional).
\<close>

theorem finite_table_true_agreement:
  assumes true: "finite_table_true P \<Theta>"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V"
    and sites: "\<And>d t. (d,t) \<in> finite_table_calls \<Theta> \<Longrightarrow> d \<in> V"
  shows "finite_table_true Q \<Theta>"
  unfolding finite_table_true_def
proof (intro allI impI)
  fix e u c assume l: "resolution_table_lookup \<Theta> (e,u) = Some c"
  have eV: "e \<in> V" using sites[of e u] l by (simp add: finite_table_calls_def)
  have "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
    using true l unfolding finite_table_true_def by blast
  then show "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system Q)"
    using positive_meaning_dependency_locality[OF Pf Qf agree closed eV] by blast
qed

corollary finite_table_valid_agreement:
  assumes valid: "finite_table_valid P \<Theta>"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V"
    and sites: "\<And>d t. (d,t) \<in> finite_table_calls \<Theta> \<Longrightarrow> d \<in> V"
  shows "finite_table_true Q \<Theta>" and "finite_table_valid Q (finite_table_certified Q \<Theta>)"
    and "finite_table_calls (finite_table_certified Q \<Theta>) = finite_table_calls \<Theta>"
proof -
  show t: "finite_table_true Q \<Theta>"
    by (rule finite_table_true_agreement[OF finite_table_valid_true[OF valid] Pf Qf agree closed sites])
  show "finite_table_valid Q (finite_table_certified Q \<Theta>)" by (rule finite_table_certified_valid[OF t])
  show "finite_table_calls (finite_table_certified Q \<Theta>) = finite_table_calls \<Theta>" by (rule finite_table_certified_calls)
qed

definition finite_table_relocates ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s,'e,'c) resolution_table \<Rightarrow> bool" where
  "finite_table_relocates g \<Theta> \<Theta>' \<longleftrightarrow> finite_table_calls \<Theta>' = (\<lambda>(d,t). (g d,t)) ` finite_table_calls \<Theta>"

theorem finite_table_true_relocated:
  assumes true: "finite_table_true P \<Theta>" and relocates: "finite_table_relocates g \<Theta> \<Theta>'"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union> fst ` finite_table_calls \<Theta>)"
  shows "finite_table_true (finite_rename_system g P) \<Theta>'"
  unfolding finite_table_true_def
proof (intro allI impI)
  fix e u c assume l: "resolution_table_lookup \<Theta>' (e,u) = Some c"
  then have "(e,u) \<in> finite_table_calls \<Theta>'" by (simp add: finite_table_calls_def)
  then obtain d where d: "(d,u) \<in> finite_table_calls \<Theta>" and e: "e = g d"
    using relocates by (auto simp: finite_table_relocates_def)
  then obtain c0 where "resolution_table_lookup \<Theta> (d,u) = Some c0" by (auto simp: finite_table_calls_def)
  then have tr: "(d,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
    using true unfolding finite_table_true_def by blast
  have inj: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    by (rule inj_on_subset[OF injective]) (use d in force)
  show "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system (finite_rename_system g P))"
    unfolding e using finite_renamed_meaning_at[OF Pf inj] tr by blast
qed

text \<open>
  An alpha variant may present its clauses at other binder, socket and clause coordinates, so its table is one of
  another type holding the same calls: the table is read by its calls alone.
\<close>

theorem finite_table_true_alpha:
  assumes true: "finite_table_true P \<Theta>"
    and alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system Q)"
    and calls: "finite_table_calls \<Theta>' = finite_table_calls \<Theta>"
  shows "finite_table_true Q \<Theta>'"
  unfolding finite_table_true_def
proof (intro allI impI)
  fix e u c assume "resolution_table_lookup \<Theta>' (e,u) = Some c"
  then have "(e,u) \<in> finite_table_calls \<Theta>'" by (simp add: finite_table_calls_def)
  then have "(e,u) \<in> finite_table_calls \<Theta>" by (simp only: calls)
  then obtain c0 where "resolution_table_lookup \<Theta> (e,u) = Some c0" by (auto simp: finite_table_calls_def)
  then have tP: "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
    using true unfolding finite_table_true_def by blast
  show "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system Q)"
    using tP by (simp only: system_alpha_positive_meaning[OF alpha])
qed

text \<open>
  The two composed: a table whose calls are true at a program, relocated by a placement, has its calls true at the
  relocated program and at an alpha variant of it; its premise is truth, which the agreement transfer gives and a
  valid table meets (@{thm [source] finite_table_valid_true}).
\<close>

corollary finite_table_true_relocated_alpha:
  assumes true: "finite_table_true P \<Theta>" and relocates: "finite_table_relocates g \<Theta> \<Theta>'"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union> fst ` finite_table_calls \<Theta>)"
    and alpha: "system_alpha_variant (decode_finite_system (finite_rename_system g P)) (decode_finite_system Q)"
    and calls: "finite_table_calls \<Theta>'' = finite_table_calls \<Theta>'"
  shows "finite_table_true (finite_rename_system g P) \<Theta>'" and "finite_table_true Q \<Theta>''"
proof -
  show t: "finite_table_true (finite_rename_system g P) \<Theta>'"
    by (rule finite_table_true_relocated[OF true relocates Pf injective])
  show "finite_table_true Q \<Theta>''" by (rule finite_table_true_alpha[OF t alpha calls])
qed

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

theorem shared_raising_formed_at:
  assumes st: "committed_representation_structure (shared_committed_representation \<kappa> P) Fi \<kappa> P"
    and fi: "\<And>s. Fi s \<Longrightarrow> shared_raised \<kappa> P s"
  shows "tested_representation_formed (shared_committed_representation \<kappa> P) Fi \<kappa> P
    (finite_narrowed_commitment P m D \<Phi>) (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
    (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
      Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)))
    (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M (shared_entry_goal h))"
proof (rule commitment_tests_formed[OF st], goal_cases)
  case (1 s)
  then show ?case using shared_commitment_formed[of \<kappa> P s] fi[OF 1]
    by (simp add: shared_raised_def shared_committed_representation_def)
next
  case 2
  show ?case by (rule access_narrowed_commitment_exact)
next
  case (3 s h F)
  let ?st = "search_project s" let ?g = "access_goal (shared_access \<kappa> P s) h"
  have f: "search_formed \<kappa> P s" and rs: "finite_goals_raised P ?st" using fi[OF 3(1)] by (simp_all add: shared_raised_def)
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

theorem shared_raising_formed:
  assumes sock: "clause_sockets_distinct P"
  shows "tested_representation_formed (shared_committed_representation \<kappa> P) (shared_raised \<kappa> P) \<kappa> P
    (finite_narrowed_commitment P m D \<Phi>) (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
    (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
      Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)))
    (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M (shared_entry_goal h))"
  by (rule shared_raising_formed_at[OF shared_raised_structure[OF sock]])

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

text \<open>
  The two check constants the route calls, at a table: the check forms at the moded selection at the table, each
  constant above its instance at the empty table. Their code equations at a table are GT3's.
\<close>

definition moded_check_resolution_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M d t n =
    finite_check_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P)
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P d t n"

lemma moded_check_resolution_in_empty:
  "moded_check_resolution_in resolution_empty_table \<kappa> P m D \<Phi> Dm M d t n = moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n"
  by (simp only: moded_check_resolution_in_def moded_check_resolution_def finite_check_resolution_by_in_empty)

definition native_moded_check_resolution_in ::
    "(local_address,local_address,local_address option definition_site,local_address) resolution_table \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> nat \<Rightarrow>
      (local_address,local_address,local_address option definition_site,'v) produced_declarations \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_frames \<Rightarrow>
      (local_address,local_address,local_address option definition_site) resolution_declarations \<Rightarrow>
      local_address option definition_site resolution_modes \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow>
      ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M R n =
    native_check_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P)
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P R n"

lemma native_moded_check_resolution_in_empty:
  "native_moded_check_resolution_in resolution_empty_table \<kappa> P m D \<Phi> Dm M R n = native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n"
  by (simp only: native_moded_check_resolution_in_def native_moded_check_resolution_def native_check_resolution_by_in_empty)

text \<open>At two valid tables of the same calls the moded check returns an outcome of the same kind (its selection is one).\<close>

theorem moded_check_resolution_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
    and valid: "finite_table_valid P \<Theta>" and valid': "finite_table_valid P \<Theta>'"
    and Pf: "finite_system_formed P" and tf: "finite_term_formed t" and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_resolution_verdict (moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M d t n) =
      finite_resolution_verdict (moded_check_resolution_in \<Theta>' \<kappa> P m D \<Phi> Dm M d t n)"
    and "moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M d t n = Finite_Unresolved E \<longleftrightarrow>
      moded_check_resolution_in \<Theta>' \<kappa> P m D \<Phi> Dm M d t n = Finite_Unresolved E"
proof -
  have S: "finite_resolution_select_in \<Theta>' (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P =
      finite_resolution_select_in \<Theta> (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M) \<kappa> P"
    by (rule finite_resolution_select_calls[OF calls[symmetric]])
  note c = finite_check_resolution_by_calls[OF calls valid valid' Pf tf \<kappa> finite_resolution_select_goals_in,
    where K="finite_narrowed_commitment P m D \<Phi>" and d=d and n=n]
  show "finite_resolution_verdict (moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M d t n) =
      finite_resolution_verdict (moded_check_resolution_in \<Theta>' \<kappa> P m D \<Phi> Dm M d t n)"
    unfolding moded_check_resolution_in_def S by (rule c(1))
  show "moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M d t n = Finite_Unresolved E \<longleftrightarrow>
      moded_check_resolution_in \<Theta>' \<kappa> P m D \<Phi> Dm M d t n = Finite_Unresolved E"
    unfolding moded_check_resolution_in_def S by (rule c(2))
qed

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

subsection \<open>The route's committed step through the kept classes\<close>

text \<open>
  Task 871 (#830's fix (1) (b) in F2c). The route's priority reads the whole focus once a step: whether some admitted
  goal passes the commitment's priority. Its class (@{text admitted_priority_class}) asks the guard of each goal of
  the focus once and the commitment's priority of each admitted goal once, and is made only where the selection
  reaches the priority, from the candidates the kept classes give (@{text route_select}). The goals' outcomes read only
  the commitment access of the prepared value (@{text commitment_tests_outcome}), so the route prepares that alone.
  Its search is R5's committed search at the moded selection (@{text shared_route_search}).
\<close>

definition admitted_priority_class where
  "admitted_priority_class Kc Dm M gd W E A = (let G = ffilter gd (access_goals W);
      Gp = ffilter (access_commitment_priority Kc W E) G in
    if Gp \<noteq> {||} then ffilter (\<lambda>h. h |\<in>| A) Gp else ffilter (\<lambda>h. h |\<in>| A \<and> access_mode_binder Dm M W E h) G)"

lemma admitted_priority_class:
  assumes A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_goals W"
  shows "admitted_priority_class Kc Dm M gd W E A = ffilter (\<lambda>h. gd h \<and>
    access_moded_priority_at Kc Dm M W E (fBex (access_goals W) (\<lambda>h. gd h \<and> access_commitment_priority Kc W E h)) h) A"
  using A by (auto simp: admitted_priority_class_def access_moded_priority_at_def Let_def fset_eq_iff ffilter.rep_eq
    split: if_splits)

lemma commitment_tests_prepare:
  "tests_prepare (commitment_tests R ce Kc Dm M gd) F r V = (ce r,
    fBex (access_goals (access_focused F V)) (\<lambda>h. gd r h \<and> access_commitment_priority Kc (access_focused F V) (ce r) h))"
  by (simp add: commitment_tests_def Let_def)

lemma commitment_tests_outcome:
  "tested_committed_goal_outcome R (commitment_tests R ce Kc Dm M gd) gd rec F B r V (E,b) =
    tested_committed_goal_outcome R (commitment_tests R ce Kc Dm M gd) gd rec F B r V (E,b')"
  by (rule ext) (simp add: tested_committed_goal_outcome_def commitment_tests_def Let_def)

text \<open>
  At the whole focus the priority's class reads the state's access (@{thm [source] access_focused_whole}), so the route
  builds no focused record there; at a proper focus the focused record is built once, its goals the range of the goal
  tree under the focus (@{text shared_focused}), and both the priority's class and the selection read it (task 892).
\<close>

definition route_select where
  "route_select \<kappa> P Kc Dm M gd F r V x = (if F = None \<or> F = Some []
    then committed_kept_select \<kappa> P (admitted_priority_class Kc Dm M (gd r) V (fst x)) F r V
    else let W = shared_focused (the F) r V in
      focused_kept_select (admitted_priority_class Kc Dm M (gd r) W (fst x)) (the F) r V W)"

lemma route_kept_formed:
  assumes tf: "tested_representation_formed (shared_committed_representation \<kappa> P) Fi \<kappa> P K pr
      (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access Kc Dm M gd) gd"
    and fi: "\<And>s. Fi s \<Longrightarrow> search_formed \<kappa> P s \<and> search_classes_formed s"
  shows "selected_representation_formed (shared_committed_representation \<kappa> P) Fi \<kappa> P K pr
    (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access Kc Dm M gd) gd (shared_focus_empty \<kappa> P)
    (route_select \<kappa> P Kc Dm M gd) (\<lambda>F r V. (shared_commitment_access r,True))"
proof (rule selected_representation_formed.intro[OF tf], unfold_locales, goal_cases)
  case (1 s F)
  then show ?case by (simp add: shared_focus_empty shared_committed_representation_def)
next
  case (2 s F)
  have f: "search_formed \<kappa> P s" "search_classes_formed s" using fi[OF 2] by simp_all
  let ?V = "shared_access \<kappa> P s" let ?W = "access_focused F ?V" let ?E = "shared_commitment_access s"
  have "route_select \<kappa> P Kc Dm M gd F s ?V (?E,True) = access_select (\<lambda>h. gd s h \<and> access_moded_priority_at Kc Dm M ?W ?E
      (fBex (access_goals ?W) (\<lambda>h. gd s h \<and> access_commitment_priority Kc ?W ?E h)) h) ?W"
  proof (cases "F = None \<or> F = Some []")
    case True
    have "route_select \<kappa> P Kc Dm M gd F s ?V (?E,True) =
        committed_kept_select \<kappa> P (admitted_priority_class Kc Dm M (gd s) ?W ?E) F s ?V"
      using True by (simp add: route_select_def access_focused_whole)
    also have "\<dots> = access_select (\<lambda>h. gd s h \<and> access_moded_priority_at Kc Dm M ?W ?E
        (fBex (access_goals ?W) (\<lambda>h. gd s h \<and> access_commitment_priority Kc ?W ?E h)) h) ?W"
      by (rule committed_kept_select[OF f]) (rule admitted_priority_class, simp)
    finally show ?thesis .
  next
    case False
    obtain g where g: "F = Some g" and gne: "g \<noteq> []" using False by (cases F) auto
    have "route_select \<kappa> P Kc Dm M gd F s ?V (?E,True) =
        focused_kept_select (admitted_priority_class Kc Dm M (gd s) ?W ?E) g s ?V ?W"
      by (simp add: route_select_def g gne shared_focused[OF f(1)] Let_def)
    also have "\<dots> = access_select (\<lambda>h. gd s h \<and> access_moded_priority_at Kc Dm M ?W ?E
        (fBex (access_goals ?W) (\<lambda>h. gd s h \<and> access_commitment_priority Kc ?W ?E h)) h) ?W"
      unfolding g by (rule focused_kept_select[OF f]) (rule admitted_priority_class, simp)
    finally show ?thesis .
  qed
  then show ?case by (simp add: shared_committed_representation_def commitment_tests_def Let_def)
next
  case (3 s F B rec)
  show ?case by (simp only: commitment_tests_prepare) (rule commitment_tests_outcome)
qed

theorem shared_route_formed:
  assumes sock: "clause_sockets_distinct P"
  shows "selected_representation_formed (shared_committed_representation \<kappa> P)
    (\<lambda>s. shared_raised \<kappa> P s \<and> search_classes_formed s) \<kappa> P
    (finite_narrowed_commitment P m D \<Phi>) (finite_moded_priority (finite_narrowed_commitment P m D \<Phi>) Dm M)
    (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
      Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)))
    (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
      (resolution_declarations.truncate D) M (shared_entry_goal h)) (shared_focus_empty \<kappa> P)
    (route_select \<kappa> P (access_narrowed_commitment P m D \<Phi>) Dm M
      (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h))) (\<lambda>F r V. (shared_commitment_access r,True))"
proof -
  have st: "committed_representation_structure (shared_committed_representation \<kappa> P)
      (\<lambda>s. shared_raised \<kappa> P s \<and> search_classes_formed s) \<kappa> P"
    by (rule shared_kept_structure[OF shared_raised_structure[OF sock] sock]) (simp add: shared_raised_def)
  show ?thesis by (rule route_kept_formed[OF shared_raising_formed_at[OF st]]) (simp_all add: shared_raised_def)
qed

corollary shared_route_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and rs: "finite_goals_raised P st"
  shows "selected_committed_search (shared_committed_representation \<kappa> P)
      (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access (access_narrowed_commitment P m D \<Phi>)
        Dm M (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
          (resolution_declarations.truncate D) M (shared_entry_goal h)))
      (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
        (resolution_declarations.truncate D) M (shared_entry_goal h)) (shared_focus_empty \<kappa> P)
      (route_select \<kappa> P (access_narrowed_commitment P m D \<Phi>) Dm M
        (\<lambda>s h. shared_raising_guard (finite_declared_raisers P (resolution_declarations.truncate D))
          (resolution_declarations.truncate D) M (shared_entry_goal h))) (\<lambda>F r V. (shared_commitment_access r,True))
      \<kappa> P n F B (search_of P st) =
    finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P n F B st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have f: "shared_raised \<kappa> P (search_of P st) \<and> search_classes_formed (search_of P st)"
    using search_of[OF d] pl rs search_of_classes[OF d] by (simp add: shared_raised_def)
  show ?thesis using selected_representation_formed.selected_committed[OF shared_route_formed[OF sock] f] search_of(2)[OF d]
    by (simp add: shared_committed_representation_def)
qed

text \<open>
  Whether the program's clause sockets are distinct is computed once a call and once a demand: the route's form takes
  it as an argument beside the commitment's tests and the guard's raisers (@{text moded_route_with}), and the
  constants' code equations below bind it where they bind those. The six code equations above keep their statements.
\<close>

definition moded_route_with ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      'd resolution_modes \<Rightarrow>
      (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) access_commitment \<Rightarrow>
      ('d \<times> 'c \<times> 's) fset \<Rightarrow> bool \<Rightarrow> 's list option \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "moded_route_with \<kappa> P m D \<Phi> Dm M Kc X cs F0 d t n =
    (let gd = (\<lambda>r h. shared_raising_guard X (resolution_declarations.truncate D) M (shared_entry_goal h)) in
    finite_outcome_result P d t (if cs
      then selected_committed_search (shared_committed_representation \<kappa> P)
        (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access Kc Dm M gd) gd
        (shared_focus_empty \<kappa> P) (route_select \<kappa> P Kc Dm M gd) (\<lambda>F r V. (shared_commitment_access r,True)) \<kappa> P n F0 {||}
        (search_of P (finite_initial_state d t))
      else finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
        (finite_narrowed_commitment P m D \<Phi>) P n F0 {||} (finite_initial_state d t)))"

theorem moded_route_with_exact:
  "moded_route_with \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
      (finite_declared_raisers P (resolution_declarations.truncate D)) (clause_sockets_distinct P) F0 d t n =
    finite_outcome_result P d t (finite_committed_search_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P)
      \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n F0 {||} (finite_initial_state d t))"
  by (simp add: moded_route_with_def Let_def
    shared_route_search[OF _ finite_initial_state_placeable finite_initial_state_raised])

lemma moded_route_with_route:
  "moded_route_with \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
      (finite_declared_raisers P (resolution_declarations.truncate D)) (clause_sockets_distinct P) F0 d t n =
    moded_route_resolution \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
      (finite_declared_raisers P (resolution_declarations.truncate D)) F0 d t n"
  by (simp only: moded_route_with_exact moded_route_resolution_exact)

declare moded_committed_resolution_route [code del] moded_check_resolution_route [code del]
  moded_committed_demand_route [code del] moded_check_demand_route [code del]
  native_moded_committed_resolution_route [code del] native_moded_check_resolution_route [code del]

lemma moded_committed_resolution_kept [code]:
  "moded_committed_resolution \<kappa> P m D \<Phi> Dm M d t n = moded_route_with \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
    (finite_declared_raisers P (resolution_declarations.truncate D)) (clause_sockets_distinct P) None d t n"
  by (simp only: moded_committed_resolution_route moded_route_with_route)

lemma moded_check_resolution_kept [code]:
  "moded_check_resolution \<kappa> P m D \<Phi> Dm M d t n = moded_route_with \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
    (finite_declared_raisers P (resolution_declarations.truncate D)) (clause_sockets_distinct P) (Some []) d t n"
  by (simp only: moded_check_resolution_route moded_route_with_route)

lemma moded_committed_demand_kept [code]:
  "moded_committed_demand \<kappa> P m D \<Phi> Dm M Q n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D); cs = clause_sockets_distinct P;
      V = fimage (\<lambda>q. (q,finite_resolution_verdict (moded_route_with \<kappa> P m D \<Phi> Dm M Kc X cs None (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_committed_demand_route moded_route_with_route Let_def)

lemma moded_check_demand_kept [code]:
  "moded_check_demand \<kappa> P m D \<Phi> Dm M Q n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D); cs = clause_sockets_distinct P;
      V = fimage (\<lambda>q. (q,finite_resolution_verdict (moded_route_with \<kappa> P m D \<Phi> Dm M Kc X cs (Some []) (fst q) (snd q) n))) Q in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"
  by (simp add: moded_check_demand_route moded_route_with_route Let_def)

lemma native_moded_committed_resolution_kept [code]:
  "native_moded_committed_resolution \<kappa> P m D \<Phi> Dm M R n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D); cs = clause_sockets_distinct P;
      T = fimage (\<lambda>q. (q,moded_route_with \<kappa> P m D \<Phi> Dm M Kc X cs None (fst q) (snd q) n)) R;
      V = fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) T in
    (T,if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
      then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None))"
  by (simp add: native_moded_committed_resolution_route moded_route_with_route Let_def)

lemma native_moded_check_resolution_kept [code]:
  "native_moded_check_resolution \<kappa> P m D \<Phi> Dm M R n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D); cs = clause_sockets_distinct P;
      T = fimage (\<lambda>q. (q,moded_route_with \<kappa> P m D \<Phi> Dm M Kc X cs (Some []) (fst q) (snd q) n)) R;
      V = fimage (\<lambda>(q,r). (q,finite_resolution_verdict r)) T in
    (T,if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
      then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None))"
  by (simp add: native_moded_check_resolution_route moded_route_with_route Let_def)

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

text \<open>At a table: the native moded check at rc's premises at the table.\<close>

theorem native_moded_check_exact_in:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "committed_registrations_in \<kappa> P m D \<Phi> corr \<Theta>"
    and result: "native_moded_check_resolution_in \<Theta> \<kappa> P m D \<Phi> Dm M R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_check_resolution_by_exact_in[OF registered_commitment_at_in.exact_premises_in[OF
    committed_registrations_in.registered_at_in[OF registered]] result[unfolded native_moded_check_resolution_in_def]]
  by blast+

text \<open>
  The native moded forms at the program an installed site reads (review 824's follow-up 5): rc's premises there are
  #820's @{text registrations_installed}, so the route's consumers (#547, #707, #399) cite these instances.
\<close>

text \<open>
  A table's calls at an installation, stated once for every mapped extension: a table whose calls are true at the
  numbered program @{text Q}, its calls at @{text Q}'s definitions, relocated by the placement, has its calls true at
  the placed program and at the program the installed site reads, an alpha variant of it (@{text installed_variant}),
  at any table of those calls there. It reads the installation's result and the installed reading alone.
\<close>

context finite_mapped_native_extension
begin

lemma mapped_installed_table_true:
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system R)"
    and true: "finite_table_true Q \<Theta>" and relocates: "finite_table_relocates placement \<Theta> \<Theta>'"
    and sites: "fst ` finite_table_calls \<Theta> \<subseteq> system_definitions (decode_finite_system Q)"
    and calls: "finite_table_calls \<Theta>'' = finite_table_calls \<Theta>'"
  shows "finite_table_true goal \<Theta>'" and "finite_table_true R \<Theta>''"
proof -
  have Qf: "schema_system_formed (decode_finite_system Q)" using target by (simp only: finite_system_formed_correct)
  have inj: "inj_on placement (system_definitions (decode_finite_system Q) \<union> fst ` finite_table_calls \<Theta>)"
    using coordinates by (simp only: Un_absorb2[OF sites] finite_system_definitions_correct)
  note r = finite_table_true_relocated_alpha[OF true relocates Qf inj installed_variant[OF result read] calls]
  show "finite_table_true goal \<Theta>'" by (rule r(1))
  show "finite_table_true R \<Theta>''" by (rule r(2))
qed

end

context relocated_registrations
begin

lemmas native_moded_check_installed = native_moded_check_exact_in[OF committed_registrations_in_empty[OF
  registrations_installed], unfolded native_moded_check_resolution_in_empty]

lemmas native_moded_committed_installed = native_moded_committed_exact[OF registrations_installed]

text \<open>
  The numbered table's calls at the installed program: a table whose calls are true at the numbered program @{text Q}
  (a valid one's are; the agreement transfer gives them at an agreeing program), its calls at
  @{text Q}'s definitions, relocated by the placement, has its calls true at the placed program and at the program the
  installed site reads, an alpha variant of it (@{text installed_variant}), at any table of those calls there.
\<close>

lemma installed_table_true:
  assumes true: "finite_table_true Q \<Theta>" and relocates: "finite_table_relocates placement \<Theta> \<Theta>'"
    and sites: "fst ` finite_table_calls \<Theta> \<subseteq> system_definitions (decode_finite_system Q)"
    and calls: "finite_table_calls \<Theta>'' = finite_table_calls \<Theta>'"
  shows "finite_table_true goal \<Theta>'" and "finite_table_true Inst \<Theta>''"
proof -
  note r = mapped_installed_table_true[OF result read true relocates sites calls]
  show "finite_table_true goal \<Theta>'" by (rule r(1))
  show "finite_table_true Inst \<Theta>''" by (rule r(2))
qed

end

text \<open>At a table at the installed program (#547, #707, #399): the native moded check there, from rc's premises at the
  table at the installed program (@{text relocated_registrations_in.registrations_installed_in}).\<close>

context relocated_registrations_in
begin

lemmas native_moded_check_installed_in = native_moded_check_exact_in[OF registrations_installed_in]

end

end
