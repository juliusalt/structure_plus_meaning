theory Factor_Resolution_Modes
  imports Factor_Resolution_Commitments
begin

section \<open>Modes: an order on goals the selection reads\<close>

text \<open>
  A mode is a site and a view, a producer declaration's view (DECISIONS.md, task 495's entry, correction (12) of
  "Committed choice, for refusals"): where a goal's viewed input at the mode is ground, the goal binds its viewed output
  with the alternatives a lookup has. Modes are declared beside the records, in neither @{typ "('a,'s,'d)
  resolution_declarations"} nor @{typ "('a,'s,'d,'c) resolution_commitment"}: a declaration licenses a commitment, a
  mode orders the search. A mode carries no obligation: exactness does not rest on the order, so a wrong mode costs work
  and never a verdict. The modes are read by the selection alone, never by a test, a discharge or a construction.
\<close>

type_synonym 'd resolution_modes = "('d \<times> nat resolution_view) fset"

definition modes_formed :: "'d resolution_modes \<Rightarrow> bool" where
  "modes_formed M \<longleftrightarrow> fBall M (\<lambda>(d,V). view_formed V)"

section \<open>Declared goals, waiting variables and binders\<close>

text \<open>
  A declared goal is a pending call goal where R5's tests read a declaration: at a declared producer's site, or at a
  socket its parent's clause declares at its key, the socket read at the parent node's site and clause and the goal's
  key as the socket test reads it (@{const finite_socket_kept}). The waiting variables of a goal are the variables of
  the declared goals other than it, inputs and outputs alike: a producer waits for its input, and a producer the tests
  cannot commit waits for its output rather than enumerating it. A binder is a pending call goal at a mode's site whose
  viewed input at the mode is ground and whose viewed output holds a waiting variable.
\<close>

definition finite_declared_goal ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_declared_goal D st g \<longleftrightarrow> g |\<in>| resolution_pending st \<and> (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> fBex (declared_producers D) (\<lambda>(e,V,hs). e = d) \<or>
        (q \<noteq> [] \<and> fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
          fBex (declared_sockets D) (\<lambda>(e,S,s,keep,Vp,Vh).
            e = resolution_node_site nd \<and> S = resolution_node_schema nd \<and> s = last q)))
    | Resolution_Material_Goal q r N \<Rightarrow> False)"

definition finite_waiting_variables ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      ('s,'a) resolution_variable fset" where
  "finite_waiting_variables D st g = ffUnion (fimage resolution_goal_variables
    (ffilter (\<lambda>h. h \<noteq> g \<and> finite_declared_goal D st h) (resolution_pending st)))"

definition finite_mode_binder ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_mode_binder D M st g \<longleftrightarrow> g |\<in>| resolution_pending st \<and> (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>(e,V). e = d \<and> (case resolution_view_pattern V p of
          Some (x,y) \<Rightarrow> finite_pattern_variables x = {||} \<and>
            finite_pattern_variables y |\<inter>| finite_waiting_variables D st g \<noteq> {||}
        | None \<Rightarrow> False))
    | Resolution_Material_Goal q r N \<Rightarrow> False)"

lemma finite_mode_binder_none [simp]: "finite_mode_binder D {||} st g = False"
  by (cases g) (simp_all add: finite_mode_binder_def)

section \<open>The moded priority and the moded selection\<close>

text \<open>
  Commitments first, then binders: a goal passes the moded priority where it passes R5's default priority, or where it
  is a binder and no pending goal passes the default priority. So a goal is committed at the first state it is
  committable in (F1's item 5), and a binder is taken, in F1's class (ii) at the least position, only where nothing is
  committable. The moded selection is F1's selection at that priority, read on the focused state the committed search
  hands it, as R5's default reads its tests.
\<close>

definition finite_moded_priority ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_moded_priority K D M st g \<longleftrightarrow> finite_commitment_priority K st g \<or>
    (finite_mode_binder D M st g \<and> \<not> fBex (resolution_pending st) (finite_commitment_priority K st))"

abbreviation finite_moded_select ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_moded_select \<kappa> K D M P \<equiv> finite_resolution_select_at (finite_moded_priority K D M) \<kappa> P"

abbreviation finite_moded_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d) resolution_declarations \<Rightarrow> 'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_moded_resolution \<kappa> K D M P \<equiv> finite_committed_resolution_by (finite_moded_select \<kappa> K D M P) \<kappa> K P"

text \<open>At no modes the moded priority is R5's default, and the moded search is R5's committed search.\<close>

lemma finite_moded_priority_none [simp]: "finite_moded_priority K D {||} = finite_commitment_priority K"
  by (intro ext) (simp add: finite_moded_priority_def)

lemma finite_moded_select_none: "finite_moded_select \<kappa> K D {||} P = finite_committed_select \<kappa> K P"
  by simp

lemma finite_moded_resolution_none:
  "finite_moded_resolution \<kappa> K D {||} P d t n = finite_committed_resolution \<kappa> K P d t n"
  by (simp add: finite_committed_resolution_def finite_committed_resolution_by_def finite_committed_search_def)

section \<open>The selection facts at the moded selection\<close>

text \<open>F1's lemmas at the moded priority: nothing about the selection is proved again.\<close>

lemmas finite_moded_select_exact =
  finite_resolution_select_at_exact[where pr="finite_moded_priority K D M" for K D M]

lemmas finite_moded_select_lifts =
  finite_resolution_select_lifts[where pr="finite_moded_priority K D M" for K D M]

lemmas finite_moded_select_unheld =
  finite_resolution_select_unheld[where pr="finite_moded_priority K D M" for K D M]

lemma finite_moded_select_goals:
  "finite_moded_select \<kappa> K D M P st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
  by (auto intro!: fsubsetI dest!: finite_moded_select_exact(1))

lemma finite_moded_search_found:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and inv: "resolution_invariant P d t st"
    and found: "st' |\<in>| resolution_found (finite_committed_search_by (finite_moded_select \<kappa> K D M P) \<kappa> K P n F B st)"
  shows "resolution_invariant P d t st' \<and> finite_focus_pending F st'={||}"
  using finite_committed_search_by_found[OF \<kappa> finite_moded_select_goals inv found] .

section \<open>The states a committed search visits\<close>

text \<open>
  The count of the states the committed search visits at a selection: one for every call of the search, the states it
  reaches following its own recursion — its constructions, the goals it selects, a committed goal's sub-search and the
  continuations of the states it keeps, a plain goal's successors. The count reads the library's search for the kept
  states and computes no outcome of its own; it is how the moded selection and R5's default are compared.
\<close>

definition committed_goal_states ::
    "('s::linorder list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> nat) \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> nat" where
  "committed_goal_states cnt rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then 0
     else if finite_pruned (finite_barred B st) g then 0
     else if finite_goal_committing K F st g then
       (let q = resolution_goal_position g; B' = finite_goal_sub_barring K F B st g;
          s0 = finite_produced_state K F st g in
        cnt (Some q) B' s0 +
          sum (\<lambda>s. cnt F (finite_committed_barring B s) s) (fset (finite_kept q (resolution_found (rec (Some q) B' s0)))))
     else sum (cnt F (finite_goal_barring K F B st g)) (fset (finite_committed_successors K P F st g)))"

primrec committed_search_states ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> nat" where
  "committed_search_states sel \<kappa> K P 0 F B st = 1"
| "committed_search_states sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||} then 1
    else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then 1
        else Suc (sum (committed_search_states sel \<kappa> K P n F (finite_committed_barring B st))
          (fset (fimage (finite_construction_step \<kappa> P st) M))))
    | Select_Goals G \<Rightarrow> Suc (sum (committed_goal_states (committed_search_states sel \<kappa> K P n)
        (finite_committed_search_by sel \<kappa> K P n) K P F B st) (fset G))
    | Select_None \<Rightarrow> 1))"

abbreviation committed_resolution_states ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> nat" where
  "committed_resolution_states sel \<kappa> K P d t n \<equiv> committed_search_states sel \<kappa> K P n None {||} (finite_initial_state d t)"

section \<open>Modes relocated\<close>

text \<open>
  A site map moves a mode's site as it moves a record's sites (@{text declarations_relocated}); the view is kept, and
  the clause match leaves a view as it is, a view reading the call and not the clause. A mode carries no obligation,
  so nothing beyond the member equation is stated.
\<close>

definition modes_relocated :: "('d \<Rightarrow> 'e) \<Rightarrow> 'd resolution_modes \<Rightarrow> 'e resolution_modes" where
  "modes_relocated g M = fimage (\<lambda>(d,V). (g d,V)) M"

lemma modes_relocated_member: "(e,V) |\<in>| modes_relocated g M \<longleftrightarrow> (\<exists>d. (d,V) |\<in>| M \<and> e = g d)"
  unfolding modes_relocated_def by force

end
