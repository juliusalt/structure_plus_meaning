theory Factor_Resolution_Completeness
  imports Factor_Resolution_Lifting
begin

text \<open>
  A finite pattern renamed by a binder map is read, decoded, as the pattern at the valuation composed with the map:
  the renaming's decoding (@{thm [source] decode_finite_pattern_map}) read by @{thm [source] evaluate_rename_pattern}.
\<close>

lemma evaluate_map_finite_pattern:
  "evaluate_pattern v (decode_finite_pattern (map_finite_term_pattern f p)) = evaluate_pattern (v \<circ> f) (decode_finite_pattern p)"
  by (simp add: decode_finite_pattern_map evaluate_rename_pattern)

text \<open>
  Completeness and exactness of the resolving evaluator (R4 of DECISIONS.md "The native evaluator constructs the
  missing witnesses by resolution", items 5 and 6). A refuted call has no derivation: every true call of a
  formed program is the root of a branch the search keeps, down to the bound, so a search that neither
  succeeded nor was cut or stuck proves the call false. The argument is the lifting of derivations, made on a
  state through a support: a ground value for every variable under which every pending call holds and every
  pending material premise is satisfied. A true call is resolved by the clause and bindings of one of its
  least-round derivations, so its premises hold at smaller rounds than it, and a ground goal equal to the call
  of an ancestor, which pruning removes, would hold at no smaller round than itself: pruning keeps one branch.
  The search keeps every alternative of every goal it selects, so no goal is resolved once. The empty witness
  construction is the one the statements take; soundness holds for every construction (R3).
\<close>

section \<open>The lifting of derivations\<close>

text \<open>
  For any selection that never selects a construction and selects a nonempty set of pending goals none of which
  is a waiting material premise, the search from a supported state keeps a branch down to the bound: it
  returns a successful state or a diagnosis. The bound counts the search's steps.
\<close>

text \<open>
  The lifting is stated for a support that may leave the variables F allows unplaced, and keeps the root value:
  the successful state it reaches is supported, and every value the root takes under the start's support it takes
  there under the found one. The ground lifting below is its instance at a support allowing no unplaced variable.
\<close>

theorem finite_resolution_lifting_by:
  assumes selection: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
    and plain: "\<And>st N. sel st \<noteq> Select_Construction N"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
  shows "resolution_pattern_invariant P d \<pi> st \<Longrightarrow> resolution_supported_by F P st \<theta> \<Longrightarrow>
    (\<exists>st' \<theta>'. st' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<and>
      resolution_supported_by F P st' \<theta>' \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
proof (induction n arbitrary: st \<theta>)
  case 0
  show ?case
  proof (cases "resolution_pending st = {||}")
    case True
    then show ?thesis using "0.prems"(2) by auto
  next
    case False
    then show ?thesis by simp
  qed
next
  case (Suc n)
  show ?case
  proof (cases "resolution_pending st = {||}")
    case True
    then show ?thesis using Suc.prems(2) by auto
  next
    case False
    show ?thesis
    proof (cases "sel st")
      case (Select_Construction N)
      with plain show ?thesis by blast
    next
      case Select_None
      with False show ?thesis by simp
    next
      case (Select_Goals G)
      from selection[OF Select_Goals] obtain g where g: "g |\<in>| G" and gp: "g |\<in>| resolution_pending st"
        and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
        by (metis all_not_fin_conv)
      show ?thesis
      proof (rule resolution_goal_lifted_by[OF Suc.prems foreign gp kind])
      fix st' \<theta>' assume succ: "st' |\<in>| finite_goal_successors P st g" and sup': "resolution_supported_by F P st' \<theta>'"
        and rv': "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
      have I': "resolution_pattern_invariant P d \<pi> st'" by (rule resolution_pattern_goal_step[OF Suc.prems(1) gp succ])
      have rec: "(\<exists>st'' \<theta>''. st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st') \<and>
          resolution_supported_by F P st'' \<theta>'' \<and> (\<forall>v. resolution_root_value st' \<theta>' v \<longrightarrow> resolution_root_value st'' \<theta>'' v)) \<or>
        resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st') \<noteq> {||}"
        by (rule Suc.IH[OF I' sup'])
      have unpruned: "\<not> finite_pruned st g" by (rule resolution_supported_by_unpruned[OF Suc.prems(2) gp])
      have ne: "finite_goal_successors P st g \<noteq> {||}" using succ by auto
      define Og where "Og = finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st g"
      have Oeq: "Og = finite_outcome_union (fimage (finite_resolution_search_by sel \<kappa> P n) (finite_goal_successors P st g))"
        unfolding Og_def finite_goal_outcome_in_def using unpruned ne by (simp add: Let_def)
      have mem: "finite_resolution_search_by sel \<kappa> P n st' |\<in>|
          fimage (finite_resolution_search_by sel \<kappa> P n) (finite_goal_successors P st g)"
        by (rule fimageI[OF succ])
      have memg: "Og |\<in>| fimage (finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st) G"
        unfolding Og_def by (rule fimageI[OF g])
      have eqS: "finite_resolution_search_by sel \<kappa> P (Suc n) st =
          finite_outcome_union (fimage (finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st) G)"
        using False Select_Goals by simp
      from rec show ?thesis
      proof (elim disjE exE conjE)
        fix st'' \<theta>'' assume f: "st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st')"
          and s'': "resolution_supported_by F P st'' \<theta>''"
          and r'': "\<forall>v. resolution_root_value st' \<theta>' v \<longrightarrow> resolution_root_value st'' \<theta>'' v"
        have "st'' |\<in>| resolution_found Og"
          unfolding Oeq finite_outcome_union_fields by (rule resolution_union_member[OF mem]) (rule f)
        then have "st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P (Suc n) st)"
          unfolding eqS finite_outcome_union_fields by (rule resolution_union_member[OF memg])
        moreover have "\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st'' \<theta>'' v" using r'' rv' by blast
        ultimately show ?thesis using s'' by blast
      next
        assume "resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st') \<noteq> {||}"
        then have "resolution_diagnoses Og \<noteq> {||}"
          using resolution_union_nonempty[OF mem, of resolution_diagnoses] unfolding Oeq finite_outcome_union_fields by blast
        then show ?thesis unfolding eqS finite_outcome_union_fields
          using resolution_union_nonempty[OF memg, of resolution_diagnoses] by blast
      qed
      qed
    qed
  qed
qed

theorem finite_resolution_lifting:
  assumes selection: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
    and plain: "\<And>st N. sel st \<noteq> Select_Construction N"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported P st \<theta> \<Longrightarrow>
    resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||} \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
proof -
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported P st \<theta>"
  have "(\<exists>st' \<theta>'. st' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<and>
      resolution_supported_by (\<lambda>_. False) P st' \<theta>' \<and>
      (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
    by (rule finite_resolution_lifting_by[OF selection plain resolution_no_foreign
      I[unfolded resolution_invariant_pattern] sup[unfolded resolution_supported_none]])
  then show "resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||} \<or>
      resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}" by auto
qed

section \<open>The selection meets the lifting's conditions\<close>


lemma finite_resolution_select_lifts:
  assumes sel: "finite_resolution_select_at pr \<kappa> P st = Select_Goals G"
  shows "G \<noteq> {||} \<and>
    (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
  using finite_resolution_select_at_exact(1)[OF sel] by (simp add: finite_candidate_goal_def)

section \<open>Exactness of the per-call result\<close>

theorem finite_program_resolution_refutation_exact:
  assumes refuted: "finite_program_resolution no_witness_construction P d t n = Finite_Refuted"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
proof
  assume holds: "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  have Pf: "finite_system_formed P"
    using positive_meaning_has_formed_system[OF holds] by (simp add: finite_system_formed_correct)
  have tf: "finite_term_formed t"
    using positive_meaning_formed[OF holds]
    by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
  let ?sel = "finite_resolution_select no_witness_construction P"
  let ?R = "finite_resolution_search no_witness_construction P n (finite_initial_state d t)"
  have R: "?R = finite_resolution_search_by ?sel no_witness_construction P n (finite_initial_state d t)"
    by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
  have I0: "resolution_invariant P d t (finite_initial_state d t)" by (rule resolution_initial_invariant[OF Pf tf])
  have S0: "resolution_supported P (finite_initial_state d t) (\<lambda>_. Finite_Payload [])"
    using holds by (simp add: resolution_supported_def finite_initial_state_def resolution_value_ground)
  have "resolution_found ?R \<noteq> {||} \<or> resolution_diagnoses ?R \<noteq> {||}"
    unfolding R
    by (rule finite_resolution_lifting[OF finite_resolution_select_lifts finite_resolution_select_none_construction I0 S0])
  moreover have diag: "resolution_diagnoses ?R = {||}"
    and C: "ffUnion (fimage finite_state_proofs (resolution_found ?R)) = {||}"
    using refuted finite_program_resolution_certificates[OF Pf tf no_witness_construction_formed, of d n]
    by (auto simp: Let_def split: if_splits)
  ultimately obtain st' where st': "st' |\<in>| resolution_found ?R" by (metis all_not_fin_conv)
  have "resolution_invariant P d t st' \<and> resolution_pending st' = {||}"
    using finite_resolution_search_found[OF no_witness_construction_formed I0] st'
    by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
  then obtain nd where nd: "nd |\<in>| resolution_nodes st'" "resolution_node_position nd = []"
    by (auto simp: resolution_invariant_in_def resolution_root_held_def)
  then have "finite_node_proof (fcard (resolution_nodes st')) (resolution_nodes st') nd |\<in>| finite_state_proofs st'"
    by (auto simp: finite_state_proofs_def finite_state_proofs_in_def)
  then have "finite_state_proofs st' \<noteq> {||}" by auto
  with st' C show False using resolution_union_nonempty[of st' "resolution_found ?R" finite_state_proofs] by blast
qed

text \<open>
  The contract the route consumes: a resolved call holds, for every witness construction (R3), and a call
  refuted at the empty construction does not.
\<close>

lemmas finite_program_resolution_exact =
  finite_program_resolution_sound(2) finite_program_resolution_refutation_exact

text \<open>The verdict of a result: resolved is true, refuted false, and unresolved no verdict.\<close>

definition finite_resolution_verdict :: "('a,'s,'d,'c) finite_resolution_result \<Rightarrow> bool option" where
  "finite_resolution_verdict r = (case r of Finite_Resolved C \<Rightarrow> Some True | Finite_Refuted \<Rightarrow> Some False
    | Finite_Unresolved D \<Rightarrow> None)"

lemma finite_resolution_verdict_exact:
  assumes "finite_resolution_verdict (finite_program_resolution no_witness_construction P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof (cases "finite_program_resolution no_witness_construction P d t n")
  case (Finite_Resolved C)
  with assms show ?thesis using finite_program_resolution_sound(2)[OF Finite_Resolved]
    by (simp add: finite_resolution_verdict_def)
next
  case Finite_Refuted
  with assms show ?thesis using finite_program_resolution_refutation_exact[OF Finite_Refuted]
    by (simp add: finite_resolution_verdict_def)
next
  case (Finite_Unresolved D)
  with assms show ?thesis by (simp add: finite_resolution_verdict_def)
qed

text \<open>
  Where it answers, the resolver's answer is the program's meaning, so two programs of one meaning, as two
  presentations differing in their clause keys, variable names or sockets are, receive the same answers
  wherever both answer.
\<close>

corollary finite_program_resolution_meaning_determined:
  assumes "positive_meaning (decode_finite_system P) = positive_meaning (decode_finite_system P')"
    and "finite_resolution_verdict (finite_program_resolution no_witness_construction P d t n) = Some b"
    and "finite_resolution_verdict (finite_program_resolution no_witness_construction P' d t m) = Some b'"
  shows "b = b'"
  using finite_resolution_verdict_exact[OF assms(2)] finite_resolution_verdict_exact[OF assms(3)] assms(1) by blast

text \<open>
  A generator of the accepted candidates (@{text Candidate_Generators}): over a finite set of calls, the calls
  the resolver does not refute generate the true ones. It is sound, every generated call a candidate, and
  complete, no true call refuted; it is not tight, an unresolved call being generated true or false.
\<close>

lemma finite_program_resolution_generator:
  "candidate_generator D (\<lambda>q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P))
    (ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D)"
proof (unfold_locales)
  fix q assume "q |\<in>| ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D"
  then show "q |\<in>| D" by simp
next
  fix q assume q: "q |\<in>| D" and holds: "decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  have "finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted"
    using finite_program_resolution_refutation_exact[of P "fst q" "snd q" n] holds
    by (auto simp: decode_finite_call_term_fields)
  with q show "q |\<in>| ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D"
    by simp
qed

section \<open>A pattern goal\<close>

text \<open>
  A search started at a pattern goal (@{const finite_pattern_state}) keeps the lifting of every true instance of
  the pattern, when the pattern's variables are no program variables: it returns a diagnosis, or a found state
  whose root call has, under some support, the instance's value. Every formed instance of a found root call is
  certified: the found state substituted by the instance's values keeps the branch invariant, so the certificate of
  its root node is accepted at the instance. The instances of the found root calls therefore generate the true
  instances of the pattern (@{text Candidate_Generators}): tight by that acceptance, complete where the search
  reports no diagnosis.
\<close>

lemma resolution_value_instance:
  "resolution_value \<theta> (finite_pattern_substitute \<rho> p) = resolution_value (\<lambda>z. resolution_value \<theta> (\<rho> z)) p"
proof -
  have unfolded: "resolution_value \<theta> (finite_pattern_substitute \<rho> p) =
      finite_residual_term (finite_pattern_substitute (resolution_substitution \<theta>) (finite_pattern_substitute \<rho> p))"
    by (rule resolution_value_def)
  have composed: "finite_pattern_substitute (resolution_substitution \<theta>) (finite_pattern_substitute \<rho> p) =
      finite_pattern_substitute (\<lambda>z. finite_exact_term_pattern (resolution_value \<theta> (\<rho> z))) p"
    by (simp add: finite_pattern_substitute_composes resolution_value_exact)
  show ?thesis unfolding unfolded composed by (rule finite_residual_substitute_value)
qed

theorem finite_resolution_pattern_lifting:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and foreign: "\<And>z. z |\<in>| finite_pattern_variables \<pi> \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and holds: "(d,decode_finite_term (resolution_value \<theta> \<pi>)) \<in> positive_meaning (decode_finite_system P)"
  shows "resolution_diagnoses (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) \<noteq> {||} \<or>
    (\<exists>st nd \<theta>' \<rho>. st |\<in>| resolution_found (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) \<and>
      nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = [] \<and> resolution_node_site nd = d \<and>
      resolution_node_call nd = finite_pattern_substitute \<rho> \<pi> \<and>
      resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>)"
proof -
  let ?sel = "finite_resolution_select no_witness_construction P"
  let ?st0 = "finite_pattern_state d \<pi> :: ('a,'b,'c,'d) resolution_state"
  let ?R = "finite_resolution_search no_witness_construction P n ?st0"
  have R: "?R = finite_resolution_search_by ?sel no_witness_construction P n ?st0" by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
  have I0: "resolution_pattern_invariant P d \<pi> ?st0" by (rule resolution_pattern_initial_invariant[OF Pf \<pi>f])
  have S0: "resolution_supported_by (\<lambda>z. snd z |\<notin>| finite_program_variables P) P ?st0 \<theta>"
    unfolding resolution_supported_by_def using holds foreign by (auto simp: finite_pattern_state_def)
  have V0: "resolution_root_value ?st0 \<theta> (resolution_value \<theta> \<pi>)"
    by (auto simp: resolution_root_value_def finite_pattern_state_def)
  have lifted: "(\<exists>st' \<theta>'. st' |\<in>| resolution_found ?R \<and>
      resolution_supported_by (\<lambda>z. snd z |\<notin>| finite_program_variables P) P st' \<theta>' \<and>
      (\<forall>v. resolution_root_value ?st0 \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses ?R \<noteq> {||}"
  proof -
    have F0: "\<And>z. snd z |\<notin>| finite_program_variables P \<Longrightarrow> snd z |\<notin>| finite_program_variables P" by simp
    note L = finite_resolution_lifting_by[where sel="finite_resolution_select no_witness_construction P",
      OF finite_resolution_select_lifts finite_resolution_select_none_construction F0 I0 S0]
    show ?thesis unfolding R by (rule L) simp_all
  qed
  from lifted show ?thesis
  proof (elim disjE exE conjE)
    fix st' \<theta>' assume found: "st' |\<in>| resolution_found ?R"
      and rv: "\<forall>v. resolution_root_value ?st0 \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v"
    have "resolution_pattern_invariant P d \<pi> st' \<and> resolution_pending st' = {||}"
      using finite_resolution_pattern_search_found[OF no_witness_construction_formed I0] found
      by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
    then have I: "resolution_pattern_invariant P d \<pi> st'" and closed: "resolution_pending st' = {||}" by blast+
    obtain nd where nd: "nd |\<in>| resolution_nodes st'" "resolution_node_position nd = []"
      using I closed by (auto simp: resolution_pattern_invariant_in_def resolution_pattern_root_held_def)
    obtain \<rho> where site: "resolution_node_site nd = d" and call: "resolution_node_call nd = finite_pattern_substitute \<rho> \<pi>"
      using I nd unfolding resolution_pattern_invariant_in_def resolution_pattern_nodes_placed_in_def by blast
    have "resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>"
      using rv V0 nd unfolding resolution_root_value_def by blast
    then show ?thesis using found nd site call by blast
  next
    assume "resolution_diagnoses ?R \<noteq> {||}"
    then show ?thesis by blast
  qed
qed

definition finite_pattern_answer ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow>
      ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_pattern_answer \<kappa> P d \<pi> n x \<longleftrightarrow> finite_term_formed x \<and>
    (\<exists>st nd \<theta>. st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d \<pi>)) \<and>
      nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = [] \<and> resolution_value \<theta> (resolution_node_call nd) = x)"

theorem finite_pattern_answer_true:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and \<kappa>: "finite_witness_construction_formed \<kappa>" and answer: "finite_pattern_answer \<kappa> P d \<pi> n x"
  shows "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
proof -
  obtain st nd \<theta> where found: "st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d \<pi>))"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = []"
    and x: "resolution_value \<theta> (resolution_node_call nd) = x" and xf: "finite_term_formed x"
    using answer unfolding finite_pattern_answer_def by blast
  have "resolution_pattern_invariant P d \<pi> st \<and> resolution_pending st = {||}"
    using finite_resolution_pattern_search_found[OF \<kappa> resolution_pattern_initial_invariant[OF Pf \<pi>f]] found
    by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
  then have I: "resolution_pattern_invariant P d \<pi> st" and closed: "resolution_pending st = {||}" by blast+
  obtain \<rho> where site: "resolution_node_site nd = d" and call: "resolution_node_call nd = finite_pattern_substitute \<rho> \<pi>"
    using I nd unfolding resolution_pattern_invariant_in_def resolution_pattern_nodes_placed_in_def by blast
  have eq: "finite_pattern_substitute (resolution_substitution \<theta>) (resolution_node_call nd) = finite_exact_term_pattern x"
    using resolution_value_exact[of \<theta> "resolution_node_call nd"] x by simp
  have vars_formed: "finite_term_formed (\<theta> z)" if z: "z |\<in>| finite_pattern_variables (resolution_node_call nd)" for z
    using finite_pattern_substitute_formed_variable[of "resolution_substitution \<theta>" "resolution_node_call nd" z] eq xf z
    by (simp add: finite_exact_pattern_formed)
  define \<sigma> where "\<sigma> = resolution_substitution (\<lambda>z. if finite_term_formed (\<theta> z) then \<theta> z else Finite_Payload [])"
  have \<sigma>f: "\<And>z. finite_pattern_formed (\<sigma> z)" by (simp add: \<sigma>_def octets_formed_def finite_exact_pattern_formed)
  have \<sigma>call: "finite_pattern_substitute \<sigma> (resolution_node_call nd) = finite_exact_term_pattern x"
  proof -
    have "finite_pattern_substitute \<sigma> (resolution_node_call nd) =
        finite_pattern_substitute (resolution_substitution \<theta>) (resolution_node_call nd)"
      by (rule finite_pattern_substitute_cong) (simp add: \<sigma>_def vars_formed)
    then show ?thesis using eq by simp
  qed
  let ?st = "resolution_state_substitute \<sigma> st"
  have I': "resolution_pattern_invariant P d \<pi> ?st" by (rule resolution_pattern_invariant_substitute[OF I \<sigma>f])
  have closed': "resolution_pending ?st = {||}" using closed by simp
  have nd': "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes ?st"
    unfolding resolution_state_substitute_fields by (rule fimageI[OF nd(1)])
  have "fcard (resolution_reach (resolution_nodes ?st) (resolution_node_substitute \<sigma> nd)) \<le> fcard (resolution_nodes ?st)"
    by (rule fcard_mono) auto
  from finite_node_proof_pattern_accepted[OF I' closed' nd' this]
  have "finite_checks_schema_proof P (finite_node_proof (fcard (resolution_nodes ?st)) (resolution_nodes ?st)
      (resolution_node_substitute \<sigma> nd)) d x"
    by (simp add: site \<sigma>call)
  then have "checks_schema_proof (decode_finite_system P) (decode_finite_proof (finite_node_proof
      (fcard (resolution_nodes ?st)) (resolution_nodes ?st) (resolution_node_substitute \<sigma> nd))) d (decode_finite_term x)"
    by (simp only: finite_checks_schema_proof_exact)
  then have holds: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P)" by (rule schema_proof_sound)
  have "resolution_value (\<lambda>z. resolution_value \<theta> (\<rho> z)) \<pi> = x" using x call by (simp add: resolution_value_instance)
  then show ?thesis using holds by blast
qed

text \<open>
  The goal-level generator of item 5: over any finite space of candidate terms, the formed instances of the found
  root calls generate the true instances of the pattern. It is tight, every generated candidate true, by the
  acceptance of the substituted certificates (@{text finite_pattern_answer_true}); its soundness in the locale's
  sense is membership of the space, which the filter gives; it is complete where the search reports no diagnosis, by
  the answer-preserving lifting (@{text finite_resolution_pattern_lifting}).
\<close>

theorem finite_pattern_resolution_generator:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and foreign: "\<And>z. z |\<in>| finite_pattern_variables \<pi> \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and complete: "resolution_diagnoses (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) = {||}"
  shows "tight_candidate_generator D
    (\<lambda>x. (d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x))
    (ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D)"
proof (unfold_locales)
  fix x assume "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D"
  then show "x |\<in>| D" by simp
next
  fix x assume member: "x |\<in>| D"
    and accepted: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
  then obtain \<theta> where holds: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P)"
    and x: "resolution_value \<theta> \<pi> = x" by blast
  have xf: "finite_term_formed x"
    using positive_meaning_formed[OF holds]
    by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
  have holds': "(d,decode_finite_term (resolution_value \<theta> \<pi>)) \<in> positive_meaning (decode_finite_system P)"
    using holds x by simp
  obtain st nd \<theta>' where "st |\<in>| resolution_found (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>))"
    "nd |\<in>| resolution_nodes st" "resolution_node_position nd = []"
    "resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>"
    using finite_resolution_pattern_lifting[OF Pf \<pi>f foreign holds', of n] complete by blast
  then have "finite_pattern_answer no_witness_construction P d \<pi> n x"
    unfolding finite_pattern_answer_def using xf x by blast
  with member show "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D" by simp
next
  fix x assume "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D"
  then have "finite_pattern_answer no_witness_construction P d \<pi> n x" by simp
  then show "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
    by (rule finite_pattern_answer_true[OF Pf \<pi>f no_witness_construction_formed])
qed

section \<open>The demand-level form\<close>

lemma fimage_fst_filter_graph:
  "fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)) = ffilter (\<lambda>q. R (f q)) D"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)) \<longleftrightarrow>
      x |\<in>| ffilter (\<lambda>q. R (f q)) D"
  proof
    assume "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))"
    then show "x |\<in>| ffilter (\<lambda>q. R (f q)) D" by (auto simp: fimage.rep_eq ffilter.rep_eq)
  next
    assume "x |\<in>| ffilter (\<lambda>q. R (f q)) D"
    then have "(x,f x) |\<in>| ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)" by (auto intro: fimageI)
    then have "fst (x,f x) |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))" by (rule fimageI)
    then show "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))" by simp
  qed
qed

text \<open>
  A demand is resolved when the program is formed and every call of it is resolved or refuted; the result is
  then the set of resolved calls, in the shape of @{const finite_program_evaluation}, and nothing otherwise.
\<close>

definition finite_demand_resolution ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow>
      ('d\<times>finite_factor_term) fset option" where
  "finite_demand_resolution P D n = (let V = fimage (\<lambda>q. (q,finite_resolution_verdict
      (finite_program_resolution no_witness_construction P (fst q) (snd q) n))) D in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"

theorem finite_demand_resolution_exact:
  assumes result: "finite_demand_resolution P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  let ?v = "\<lambda>q. finite_resolution_verdict (finite_program_resolution no_witness_construction P (fst q) (snd q) n)"
  from result have Pf: "finite_system_formed P" and answered: "\<And>q. q |\<in>| D \<Longrightarrow> ?v q \<noteq> None"
    and A: "A = fimage fst (ffilter (\<lambda>(q,v). v = Some True) (fimage (\<lambda>q. (q,?v q)) D))"
    by (auto simp: finite_demand_resolution_def Let_def split: if_splits)
  show "schema_system_formed (decode_finite_system P)" using Pf by (simp add: finite_system_formed_correct)
  have key: "\<And>q. q |\<in>| D \<Longrightarrow>
      ?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    fix q assume q: "q |\<in>| D"
    obtain b where b: "?v q = Some b" using answered[OF q] by auto
    have "b \<longleftrightarrow> (fst q,decode_finite_term (snd q)) \<in> positive_meaning (decode_finite_system P)"
      by (rule finite_resolution_verdict_exact[OF b])
    then show "?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
      using b by (simp add: decode_finite_call_term_fields)
  qed
  show "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    unfolding A fimage_fst_filter_graph ffilter.rep_eq Set.filter_eq
    by (rule Collect_cong) (simp add: key cong: conj_cong)
qed

text \<open>
  Where both answer, the resolver and @{const finite_program_evaluation} agree: an equation of results, both
  being exact at the demand.
\<close>

theorem finite_demand_resolution_evaluation:
  assumes "finite_demand_resolution P D n = Some A" and "finite_program_evaluation P D = Some B"
  shows "A = B"
proof -
  have "fset A = fset B"
    using finite_demand_resolution_exact(2)[OF assms(1)] finite_program_evaluation_exact(2)[OF assms(2)] by simp
  then show ?thesis by (simp only: fset_inject)
qed

section \<open>The native form\<close>

text \<open>
  The native form reads a program and its requested calls, as @{text native_call_evaluation} does, with the
  bound: each requested call with its result (its certificates or its diagnosis) and the demand-level answer.
  Native sockets are ordered lexicographically (@{text List_Lexorder}), which orders which goal is worked
  first and never which alternative is kept.
\<close>

type_synonym native_resolution_result =
  "(local_address,local_address,local_address option definition_site,local_address) finite_resolution_result"

definition native_call_resolution ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      nat \<Rightarrow> ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_call_resolution P R n =
    (fimage (\<lambda>q. (q,finite_program_resolution no_witness_construction P (fst q) (snd q) n)) R,
     finite_demand_resolution P R n)"

theorem native_call_resolution_exact:
  assumes result: "native_call_resolution P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,Finite_Refuted) |\<in>| T \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  have T: "T = fimage (\<lambda>q. (q,finite_program_resolution no_witness_construction P (fst q) (snd q) n)) R"
    and A: "A = finite_demand_resolution P R n"
    using result by (simp_all add: native_call_resolution_def)
  show "fimage fst T = R" unfolding T fset.map_comp by (simp add: comp_def)
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,Finite_Resolved C) |\<in>| T"
    then have res: "finite_program_resolution no_witness_construction P (fst q) (snd q) n = Finite_Resolved C"
      unfolding T by auto
    show "C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
        decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
      using finite_program_resolution_sound[OF res] finite_program_resolution_accepted[OF res]
      by (simp add: decode_finite_call_term_fields)
  qed
  show "(q,Finite_Refuted) |\<in>| T \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,Finite_Refuted) |\<in>| T"
    then have res: "finite_program_resolution no_witness_construction P (fst q) (snd q) n = Finite_Refuted"
      unfolding T by auto
    show "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
      using finite_program_resolution_refutation_exact[OF res] by (simp add: decode_finite_call_term_fields)
  qed
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  proof -
    assume "A = Some B"
    then have res: "finite_demand_resolution P R n = Some B" using A by simp
    show "schema_system_formed (decode_finite_system P) \<and>
        fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
      using finite_demand_resolution_exact[OF res] by simp
  qed
qed

end
