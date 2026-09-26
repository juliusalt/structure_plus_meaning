theory Factor_Resolution_Commitments
  imports Factor_Resolution_Completeness Presentation_Contracts Ordered_Finite_Terms Factor_Rule_Instances
    Factor_Positive_Locality Factor_System_Relocation Factor_Finite_System_Fields Factor_Construction_Holders
begin

text \<open>
  Committed choice (R5 of DECISIONS.md "The native evaluator constructs the missing witnesses by resolution",
  its section "Committed choice, for refusals"). A presentation-free producer answers a true call at every
  presentation of its output, and the resolver of @{text Factor_Program_Resolution} keeps every answer, so a
  consumer that does not hold is refuted only after every presentation. A declaration steers the search on the
  producing side: a site declared functional up to a class at its output (its call a pair of an input and an
  output) is resolved in its own subtree first, its answers collected, and one kept; the rest of the search
  continues from the kept answer alone. The declaration is read by the search and by nothing else: no clause of
  any program changes, and every certificate of a resolved call is checked by the existing finite proof checker
  in the program as given.
\<close>

section \<open>Declarations and their discharge\<close>

text \<open>
  A producer is declared at a site; a consumer of a producer's output at a site and at the side of its call's
  pair that holds the output (@{const True}, the right side). A declaration is discharged at a program's
  meaning by a correspondence per producer: every two answers of the producer at one input correspond, and a
  consumer's truth is unchanged when the output it holds is replaced by a corresponding one. The obligations
  take the form the notions' contracts give: a presented function contract's output equivalence at a producer
  (@{text function_contract_producer}), a presented relation contract's invariance at a consumer
  (@{text relation_contract_consumer}, @{text relation_contract_consumer_left}), the correspondence being the
  class's @{const presentation_transport}.
\<close>

record ('a,'s,'d) resolution_declarations =
  declared_producers :: "'d fset"
  declared_consumers :: "('d \<times> 'd \<times> bool) fset"
  declared_sockets :: "('d \<times> ('a,'s,'d) finite_factor_schema \<times> 's \<times> bool) fset"

definition no_declarations :: "('a,'s,'d) resolution_declarations" where
  "no_declarations = \<lparr>declared_producers={||}, declared_consumers={||}, declared_sockets={||}\<rparr>"

definition producer_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "producer_discharged M d corr \<longleftrightarrow>
    (\<forall>x y y'. (d,Pair_Term x y) \<in> M \<longrightarrow> (d,Pair_Term x y') \<in> M \<longrightarrow> corr y y')"

definition consumer_argument :: "bool \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "consumer_argument right x y = (if right then Pair_Term x y else Pair_Term y x)"

definition consumer_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> bool \<Rightarrow> (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "consumer_discharged M e right corr \<longleftrightarrow>
    (\<forall>x y y'. corr y y' \<longrightarrow> ((e,consumer_argument right x y) \<in> M \<longleftrightarrow> (e,consumer_argument right x y') \<in> M))"

text \<open>
  An inner commitment is declared at a clause's socket, the clause named by its site and its schema compared as a
  value: the premise at the socket is a call whose argument pairs an input and an output, or a material premise.
  Its obligation is the clause's (task 518's correction of task 495's entry): for every true instance of the
  clause and every answer of the socket's goal at the same input (every solution of the material premise at the
  same source), the clause has a true instance with that answer and the same head input, and the same head output
  too when the declaration keeps the head. At a traversal over the remainder of a selection (32's rows, 79's root
  lists) the traversal's function contract, its totality, discharges it.
\<close>

definition clause_true :: "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> bool" where
  "clause_true M S h \<longleftrightarrow> (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
    (\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern h p) \<in> M) \<and>
    (\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction h N)"

definition head_kept ::
    "bool \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> ('a \<Rightarrow> factor_term) \<Rightarrow> bool" where
  "head_kept keep S h h' \<longleftrightarrow> (case schema_conclusion S of
      Pattern_Pair ci co \<Rightarrow> evaluate_pattern h' ci = evaluate_pattern h ci \<and>
        (keep \<longrightarrow> evaluate_pattern h' co = evaluate_pattern h co)
    | _ \<Rightarrow> evaluate_pattern h' (schema_conclusion S) = evaluate_pattern h (schema_conclusion S))"

definition socket_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> bool" where
  "socket_discharged M S s keep \<longleftrightarrow> (\<forall>h. clause_true M S h \<longrightarrow>
    (\<forall>d xi yo y'. (s,d,Pattern_Pair xi yo) \<in> schema_premises S \<longrightarrow>
      (d,Pair_Term (evaluate_pattern h xi) y') \<in> M \<longrightarrow>
      (\<exists>h'. clause_true M S h' \<and> head_kept keep S h h' \<and>
        evaluate_pattern h' xi = evaluate_pattern h xi \<and> evaluate_pattern h' yo = y')) \<and>
    (\<forall>N g. (s,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction g N \<longrightarrow>
      evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N) \<longrightarrow>
      (\<exists>h'. clause_true M S h' \<and> head_kept keep S h h' \<and> (\<forall>a\<in>material_variables N. h' a = g a))))"

definition declarations_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow>
      ('d \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "declarations_discharged M D corr \<longleftrightarrow>
    (\<forall>d. d |\<in>| declared_producers D \<longrightarrow> producer_discharged M d (corr d)) \<and>
    (\<forall>d e b. (d,e,b) |\<in>| declared_consumers D \<longrightarrow> consumer_discharged M e b (corr d)) \<and>
    (\<forall>e S s keep. (e,S,s,keep) |\<in>| declared_sockets D \<longrightarrow>
      socket_discharged M (decode_finite_schema S) s keep)"

lemma no_declarations_discharged: "declarations_discharged M no_declarations corr"
  by (simp add: declarations_discharged_def no_declarations_def)

theorem function_contract_producer:
  assumes contract: "presented_function_contract R D A S E B f operation"
    and at: "\<And>p q. operation p q \<longleftrightarrow> (d,Pair_Term p q) \<in> M"
  shows "producer_discharged M d (presentation_transport S S)"
  unfolding producer_discharged_def using presented_function_contract.output_equivalence[OF contract] at by blast

theorem relation_contract_consumer:
  assumes contract: "presented_relation_contract R D A S E B L observe"
    and member: "\<And>p q. observe p q \<longleftrightarrow> (e,Pair_Term p q) \<in> M"
  shows "consumer_discharged M e True (presentation_transport S S)"
proof -
  interpret presented_relation_contract R D A S E B L observe by (rule contract)
  have step: "observe x y'" if t: "presentation_transport S S y y'" and o: "observe x y" for x y y'
  proof -
    from t obtain b where b: "S b y" "S b y'" by (auto simp: presentation_transport_def)
    from boundaries[OF o] have "A x" by simp
    then obtain a where a: "R a x" using left.admitted by blast
    show ?thesis using invariance[OF a b(1) a b(2)] o by simp
  qed
  show ?thesis unfolding consumer_discharged_def consumer_argument_def if_True
  proof (intro allI impI)
    fix x y y' assume t: "presentation_transport S S y y'"
    have t': "presentation_transport S S y' y" using presentation_transport_reverse[of S S y y'] t by blast
    have "observe x y \<longleftrightarrow> observe x y'" using step[OF t] step[OF t'] by blast
    then show "((e,Pair_Term x y) \<in> M) = ((e,Pair_Term x y') \<in> M)" by (simp only: member)
  qed
qed

theorem relation_contract_consumer_left:
  assumes contract: "presented_relation_contract R D A S E B L observe"
    and member: "\<And>p q. observe p q \<longleftrightarrow> (e,Pair_Term p q) \<in> M"
  shows "consumer_discharged M e False (presentation_transport R R)"
proof -
  interpret presented_relation_contract R D A S E B L observe by (rule contract)
  have step: "observe x' y" if t: "presentation_transport R R x x'" and o: "observe x y" for x x' y
  proof -
    from t obtain a where a: "R a x" "R a x'" by (auto simp: presentation_transport_def)
    from boundaries[OF o] have "B y" by simp
    then obtain b where b: "S b y" using right.admitted by blast
    show ?thesis using invariance[OF a(1) b a(2) b] o by simp
  qed
  show ?thesis unfolding consumer_discharged_def consumer_argument_def if_False
  proof (intro allI impI)
    fix x y y' assume t: "presentation_transport R R y y'"
    have t': "presentation_transport R R y' y" using presentation_transport_reverse[of R R y y'] t by blast
    have "observe y x \<longleftrightarrow> observe y' x" using step[OF t] step[OF t'] by blast
    then show "((e,Pair_Term y x) \<in> M) = ((e,Pair_Term y' x) \<in> M)" by (simp only: member)
  qed
qed

section \<open>The committed search\<close>

text \<open>
  A commitment decides, at a state and a focus, whether a call goal is committed and whether a material goal
  takes its single solution. The search is R3's, with a focus: a committed goal at a position is solved first
  in the subtree under it (the search with that position as its focus, which is done when no goal under it is
  pending); of the states so reached, those whose answer at the position is the least by the term key order of
  @{text Ordered_Finite_Terms} are kept, a function of the set of answers alone; the search goes on from them
  with the focus it had. At a commitment every node then present is barred: a ground goal equal to the call of
  an unbarred ancestor is pruned as in R3, and one equal to the call of a barred ancestor ends its branch with a
  diagnosis, never a refutation, since the ranks that justify pruning do not decrease across a commitment. A
  committed material goal whose source is a ground whole artifact takes the solution of the artifact's
  canonical rows, a member of R1's solutions.
\<close>

record ('a,'s,'d,'c) resolution_commitment =
  commit_call :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
  commit_material :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"

definition no_commitment :: "('a,'s,'d,'c) resolution_commitment" where
  "no_commitment = \<lparr>commit_call=(\<lambda>F st g. False), commit_material=(\<lambda>F st g. False)\<rparr>"

definition finite_focus_pending ::
    "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_focus_pending F st = (case F of None \<Rightarrow> resolution_pending st
    | Some q \<Rightarrow> ffilter (\<lambda>g. take (length q) (resolution_goal_position g) = q) (resolution_pending st))"

definition finite_focused :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_focused F st = Resolution_State (finite_focus_pending F st) (resolution_nodes st) (resolution_witnesses st)"

definition finite_unbarred :: "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_unbarred B st = Resolution_State (resolution_pending st)
    (ffilter (\<lambda>nd. resolution_node_position nd |\<notin>| B) (resolution_nodes st)) (resolution_witnesses st)"

definition finite_barred :: "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_barred B st = Resolution_State (resolution_pending st)
    (ffilter (\<lambda>nd. resolution_node_position nd |\<in>| B) (resolution_nodes st)) (resolution_witnesses st)"

lemma finite_focus_pending_subset: "finite_focus_pending F st |\<subseteq>| resolution_pending st"
  by (auto simp: finite_focus_pending_def split: option.splits)

lemma finite_focus_none [simp]:
  "finite_focus_pending None st = resolution_pending st" "finite_focused None st = st"
  by (simp_all add: finite_focus_pending_def finite_focused_def)

lemma finite_unbarred_empty [simp]: "finite_unbarred {||} st = st"
  by (cases st) (simp add: finite_unbarred_def fset_eq_iff)

lemma finite_barred_empty [simp]: "\<not> finite_pruned (finite_barred {||} st) g"
  by (auto simp: finite_pruned_def finite_barred_def split: resolution_goal.splits)

text \<open>The answers of a state at a position, and the states keeping the least answer.\<close>

definition finite_committed_answers :: "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ordered_factor_term fset" where
  "finite_committed_answers q st = fimage (\<lambda>nd. Ordered_Factor_Term (finite_residual_term (resolution_node_call nd)))
    (ffilter (\<lambda>nd. resolution_node_position nd = q) (resolution_nodes st))"

definition finite_kept :: "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state fset \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_kept q S = (let A = ffUnion (fimage (finite_committed_answers q) S) in
    ffilter (\<lambda>st. fBex (finite_committed_answers q st) (\<lambda>a. fBall A (\<lambda>b. a \<le> b))) S)"

lemma finite_kept_subset: "finite_kept q S |\<subseteq>| S"
  by (auto simp: finite_kept_def Let_def)

text \<open>The material successors of a family of solutions; R1's are those of all its solutions.\<close>

definition finite_solution_successors ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> 'd \<times> 'c \<times> 's \<Rightarrow>
      ('s,'a) resolution_variable finite_material_pattern \<Rightarrow> (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state fset" where
  "finite_solution_successors st q r M Ws = ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E.
      case finite_unify_pairs E of
        None \<Rightarrow> {||}
      | Some u \<Rightarrow> {|resolution_state_substitute (finite_binding_substitution u)
          (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|})
            (resolution_nodes st) (resolution_witnesses st))|})
    (finite_material_instance_pairs W M))) Ws)"

lemma finite_material_successors_solutions:
  "finite_material_successors st q r M = (case finite_material_resolution M of Material_Waits \<Rightarrow> {||}
    | Material_Solutions Ws \<Rightarrow> finite_solution_successors st q r M Ws)"
  by (simp add: finite_material_successors_def finite_solution_successors_def split: finite_material_outcome.split)

lemma finite_solution_successors_mono:
  "Ws' |\<subseteq>| Ws \<Longrightarrow> finite_solution_successors st q r M Ws' |\<subseteq>| finite_solution_successors st q r M Ws"
  unfolding finite_solution_successors_def by (auto simp: resolution_fset_simps less_eq_fset.rep_eq)

lemma finite_artifact_rows_enumerated: "finite_artifact_rows C \<in> set (finite_artifact_enumerations C)"
proof -
  obtain A E B F where r: "finite_artifact_rows C = (A,E,B,F)" by (cases "finite_artifact_rows C") auto
  have "A \<in> set (rearrangements A)" "E \<in> set (rearrangements E)" "B \<in> set (rearrangements B)"
    "F \<in> set (rearrangements F)" by (simp_all add: rearrangements_member)
  then show ?thesis by (force simp: finite_artifact_enumerations_def r)
qed

text \<open>
  The single solution of a material goal whose skeleton is open and whose source is a ground whole artifact:
  the candidate of the artifact's canonical rows (@{const finite_artifact_rows}), one of R1's solutions.
\<close>

definition finite_canonical_solutions ::
    "'v finite_material_pattern \<Rightarrow> ('v \<times> finite_factor_term) fset fset option" where
  "finite_canonical_solutions M = (case finite_material_source M of
      Finite_Pattern_Target x \<Rightarrow> (case x of
          Finite_Whole C \<Rightarrow> if finite_material_skeleton M = Open_Reading
            then Some (finite_material_candidates M [finite_material_tuple C (finite_artifact_rows C)]) else None
        | Finite_Anchor C a \<Rightarrow> None)
    | _ \<Rightarrow> None)"

lemma finite_canonical_solutions_member:
  assumes canonical: "finite_canonical_solutions M = Some Ws'"
  obtains Ws where "finite_material_resolution M = Material_Solutions Ws" "Ws' |\<subseteq>| Ws"
proof -
  from canonical obtain C where source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
    and skeleton: "finite_material_skeleton M = Open_Reading"
    and Ws': "Ws' = finite_material_candidates M [finite_material_tuple C (finite_artifact_rows C)]"
    by (auto simp: finite_canonical_solutions_def split: finite_term_pattern.splits finite_exact_target.splits if_splits)
  have "finite_material_tuple C (finite_artifact_rows C) \<in> set (map (finite_material_tuple C) (finite_artifact_enumerations C))"
    using finite_artifact_rows_enumerated by simp
  have mono: "set ts \<subseteq> set ts' \<Longrightarrow> finite_material_candidates M ts |\<subseteq>| finite_material_candidates M ts'" for ts ts'
    unfolding finite_material_candidates_def by (auto simp: less_eq_fset.rep_eq ffilter.rep_eq fset_of_list.rep_eq)
  then have "Ws' |\<subseteq>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))"
    unfolding Ws' using \<open>finite_material_tuple C (finite_artifact_rows C) \<in> _\<close> by simp
  with finite_material_resolution_source(1)[OF skeleton source] show ?thesis using that by blast
qed

definition finite_committed_successors ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_committed_successors K P F st g = (case g of
      Resolution_Material_Goal q r M \<Rightarrow> (case finite_canonical_solutions M of
          Some Ws \<Rightarrow> if commit_material K F st g then finite_solution_successors st q r M Ws
            else finite_goal_successors P st g
        | None \<Rightarrow> finite_goal_successors P st g)
    | Resolution_Call_Goal q r d p \<Rightarrow> finite_goal_successors P st g)"

lemma finite_committed_successors_subset:
  "finite_committed_successors K P F st g |\<subseteq>| finite_goal_successors P st g"
proof (cases g)
  case (Resolution_Material_Goal q r M)
  show ?thesis
  proof (cases "finite_canonical_solutions M")
    case (Some Ws')
    then obtain Ws where Ws: "finite_material_resolution M = Material_Solutions Ws" "Ws' |\<subseteq>| Ws"
      by (rule finite_canonical_solutions_member)
    show ?thesis using Some Ws finite_solution_successors_mono[OF Ws(2), of st q r M]
      by (simp add: Resolution_Material_Goal finite_committed_successors_def finite_material_successors_solutions)
  qed (simp add: Resolution_Material_Goal finite_committed_successors_def)
qed (simp add: finite_committed_successors_def)

lemma no_commitment_successors [simp]:
  "finite_committed_successors no_commitment P F st g = finite_goal_successors P st g"
  by (simp add: finite_committed_successors_def no_commitment_def split: resolution_goal.split option.split)

definition finite_goal_committed ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_committed K F st g \<longleftrightarrow>
    resolution_is_call g \<and> F \<noteq> Some (resolution_goal_position g) \<and> commit_call K F st g"

lemma no_commitment_committed [simp]: "\<not> finite_goal_committed no_commitment F st g"
  by (simp add: finite_goal_committed_def no_commitment_def)

text \<open>
  One barring rule for every committed step (task 621, q112): a committed goal, a committed material premise and a
  construction step each bar, for the rest of the search, the nodes present where the search goes on after it, beside
  those already barred (@{text finite_committed_barring}). The ranks that justify pruning do not carry across any of
  them: a commitment abandons the derivation a pruning's rank rests on, and a construction's value bound is its own.
  A committed material premise is one whose goal takes the canonical solution (@{text finite_material_committed});
  the barred set after a goal's step is the rule's where the goal is a committed material premise, and the one
  before otherwise (@{text finite_goal_barring}).
\<close>

definition finite_committed_barring ::
    "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list fset" where
  "finite_committed_barring B st = B |\<union>| fimage resolution_node_position (resolution_nodes st)"

definition finite_material_committed ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_material_committed K F st g \<longleftrightarrow> (case g of
      Resolution_Material_Goal q r M \<Rightarrow> finite_canonical_solutions M \<noteq> None \<and> commit_material K F st g
    | Resolution_Call_Goal q r d p \<Rightarrow> False)"

definition finite_goal_barring ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> 's list fset" where
  "finite_goal_barring K F B st g = (if finite_material_committed K F st g then finite_committed_barring B st else B)"

lemma finite_committed_barring_subset: "B |\<subseteq>| finite_committed_barring B st"
  by (auto simp: finite_committed_barring_def)

lemma no_commitment_barring [simp]: "finite_goal_barring no_commitment F B st g = B"
  by (simp add: finite_goal_barring_def finite_material_committed_def no_commitment_def split: resolution_goal.split)

definition finite_committed_goal_outcome ::
    "('s list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_goal_outcome rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
     else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
     else if finite_goal_committed K F st g then
       (let q = resolution_goal_position g; sub = rec (Some q) B st in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found sub)))))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_outcome_union (fimage (rec F (finite_goal_barring K F B st g)) S))"

text \<open>
  A construction step is committed as a goal is: every node present at it is barred in the rest of the search, for
  the ranks that justify pruning do not carry across a construction (task 526, q110), and it constructs at the
  selected nodes in the focus alone. Selection reads the focus and the step the whole state; at a node in the
  focus, under the holders invariant of @{text Factor_Construction_Holders}, every goal holding a registered variable
  of the node stands at one of its premises and so in the focus, and the two read the same holders. A selected node
  outside the focus is not constructed inside the sub-search: the branch stops as stuck, unresolved.
\<close>

primrec finite_committed_search_by ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search_by sel \<kappa> K P 0 F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else Resolution_Outcome {||} {|Resolution_Cut (finite_focus_pending F st)|})"
| "finite_committed_search_by sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}
        else finite_outcome_union (fimage (finite_committed_search_by sel \<kappa> K P n F
            (finite_committed_barring B st)) (fimage (finite_construction_step \<kappa> P st) M)))
    | Select_Goals G \<Rightarrow> finite_outcome_union
        (fimage (finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F B st) G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))))"

definition finite_committed_search ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search \<kappa> K P = finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P"

section \<open>At no commitment and no construction the search is R3's\<close>

text \<open>
  At no commitment the search differs from R3's only at a construction step, which it bars; a search whose selection
  never constructs is R3's (task 526: with a registered construction R3's search is sound and not exact).
\<close>

theorem finite_committed_search_by_plain:
  assumes free: "\<And>st N. sel st \<noteq> Select_Construction N"
  shows "finite_committed_search_by sel \<kappa> no_commitment P n None {||} = finite_resolution_search_by sel \<kappa> P n"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  have out: "finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> no_commitment P n) no_commitment P None {||} st =
      finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st" for st
    by (rule ext) (simp add: finite_committed_goal_outcome_def finite_goal_outcome_def Suc.IH Let_def)
  show ?case by (rule ext) (simp add: out Suc.IH free split: resolution_selection.split)
qed

corollary finite_committed_search_plain:
  assumes free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "finite_committed_search \<kappa> no_commitment P n None {||} = finite_resolution_search \<kappa> P n"
  by (simp add: finite_committed_search_def finite_resolution_search_def finite_committed_search_by_plain[OF free])

lemma finite_resolution_select_none_construction:
  "finite_resolution_select no_witness_construction P st \<noteq> Select_Construction N"
  by (simp add: no_witness_selection finite_plain_selection_construction)

section \<open>Every found state keeps the invariant\<close>

lemma finite_committed_search_found:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_invariant P d t st \<Longrightarrow>
    st' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n F B st) \<Longrightarrow>
    resolution_invariant P d t st' \<and> finite_focus_pending F st'={||}"
proof (induction n arbitrary: F B st st')
  case 0
  then show ?case by (auto simp: resolution_fset_simps split: if_splits)
next
  case (Suc n)
  let ?rec = "finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n"
  show ?case
  proof (cases "finite_focus_pending F st={||}")
    case True
    with Suc.prems show ?thesis by (simp add: resolution_fset_simps)
  next
    case False
    show ?thesis
    proof (cases "finite_resolution_select \<kappa> P (finite_focused F st)")
      case (Select_Construction N)
      with Suc.prems False obtain nd where
        "st' |\<in>| resolution_found (?rec F (finite_committed_barring B st)
          (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps Let_def split: if_splits)
      then show ?thesis using Suc.IH resolution_construction_step[OF Suc.prems(1) \<kappa>] by blast
    next
      case (Select_Goals G)
      with Suc.prems False obtain g where g: "g |\<in>| G"
        and found: "st' |\<in>| resolution_found (finite_committed_goal_outcome ?rec K P F B st g)"
        by (auto simp: resolution_fset_simps)
      have "g |\<in>| finite_focus_pending F st"
        using finite_resolution_select_goals[OF Select_Goals] g by (auto simp: finite_focused_def)
      then have pending: "g |\<in>| resolution_pending st" using finite_focus_pending_subset by blast
      show ?thesis
      proof (cases "finite_goal_committed K F st g")
        case True
        from found True obtain s where
          s: "s |\<in>| resolution_found (?rec (Some (resolution_goal_position g)) B st)"
          and st': "st' |\<in>| resolution_found (?rec F (finite_committed_barring B s) s)"
          using finite_kept_subset
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have "resolution_invariant P d t s" using Suc.IH[OF Suc.prems(1) s] by blast
        then show ?thesis using Suc.IH st' by blast
      next
        case False
        from found False obtain s where s: "s |\<in>| finite_committed_successors K P F st g"
          and st': "st' |\<in>| resolution_found (?rec F (finite_goal_barring K F B st g) s)"
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have "s |\<in>| finite_goal_successors P st g" using s finite_committed_successors_subset by blast
        then show ?thesis using Suc.IH st' resolution_goal_step[OF Suc.prems(1) pending] by blast
      qed
    next
      case Select_None
      with Suc.prems False show ?thesis by (simp add: resolution_fset_simps)
    qed
  qed
qed

text \<open>
  A goal the search selects holds no free registered variable, so the holders invariant of
  @{text Factor_Construction_Holders} is kept by every step of the search and holds at every found state.
\<close>

lemma finite_resolution_select_unheld:
  assumes sel: "finite_resolution_select \<kappa> P (finite_focused F st) = Select_Goals G" and g: "g |\<in>| G"
  shows "\<not> finite_held \<kappa> st g"
proof -
  let ?st = "finite_focused F st"
  let ?A = "ffilter (\<lambda>g. \<not> finite_held \<kappa> ?st g) (resolution_pending ?st)"
  have G: "G = finite_goal_selection (resolution_pending ?st) ?A"
    using sel by (auto simp: finite_resolution_select_def Let_def split: if_splits)
  have "g |\<in>| ?A"
    using G g finite_goal_selection_member[where G="resolution_pending ?st" and A="?A"] by (auto simp: resolution_fset_simps)
  then show ?thesis by (auto simp: finite_held_def finite_focused_def resolution_fset_simps)
qed

lemma finite_committed_search_found_held:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_registrations_held \<kappa> st \<Longrightarrow>
    st' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n F B st) \<Longrightarrow>
    resolution_registrations_held \<kappa> st'"
proof (induction n arbitrary: F B st st')
  case 0
  then show ?case by (auto simp: resolution_fset_simps split: if_splits)
next
  case (Suc n)
  let ?rec = "finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n"
  have distinct: "resolution_positions_distinct st" using Suc.prems(1) unfolding resolution_invariant_def by blast
  show ?case
  proof (cases "finite_focus_pending F st={||}")
    case True
    with Suc.prems show ?thesis by (simp add: resolution_fset_simps)
  next
    case False
    show ?thesis
    proof (cases "finite_resolution_select \<kappa> P (finite_focused F st)")
      case (Select_Construction N)
      with Suc.prems False obtain nd where
        "st' |\<in>| resolution_found (?rec F (finite_committed_barring B st)
          (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps Let_def split: if_splits)
      then show ?thesis using Suc.IH resolution_construction_step[OF Suc.prems(1) \<kappa>]
          resolution_registrations_construction_step[OF Suc.prems(2)] by blast
    next
      case (Select_Goals G)
      with Suc.prems False obtain g where g: "g |\<in>| G"
        and found: "st' |\<in>| resolution_found (finite_committed_goal_outcome ?rec K P F B st g)"
        by (auto simp: resolution_fset_simps)
      have "g |\<in>| finite_focus_pending F st"
        using finite_resolution_select_goals[OF Select_Goals] g by (auto simp: finite_focused_def)
      then have pending: "g |\<in>| resolution_pending st" using finite_focus_pending_subset by blast
      have unheld: "\<not> finite_held \<kappa> st g" by (rule finite_resolution_select_unheld[OF Select_Goals g])
      show ?thesis
      proof (cases "finite_goal_committed K F st g")
        case True
        from found True obtain s where
          s: "s |\<in>| resolution_found (?rec (Some (resolution_goal_position g)) B st)"
          and st': "st' |\<in>| resolution_found (?rec F (finite_committed_barring B s) s)"
          using finite_kept_subset
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have Is: "resolution_invariant P d t s" using finite_committed_search_found[OF \<kappa> Suc.prems(1) s] by blast
        have Hs: "resolution_registrations_held \<kappa> s" by (rule Suc.IH[OF Suc.prems(1,2) s])
        show ?thesis by (rule Suc.IH[OF Is Hs st'])
      next
        case False
        from found False obtain s where s: "s |\<in>| finite_committed_successors K P F st g"
          and st': "st' |\<in>| resolution_found (?rec F (finite_goal_barring K F B st g) s)"
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have gs: "s |\<in>| finite_goal_successors P st g" using s finite_committed_successors_subset by blast
        have Is: "resolution_invariant P d t s" by (rule resolution_goal_step[OF Suc.prems(1) pending gs])
        have Hs: "resolution_registrations_held \<kappa> s"
          by (rule resolution_registrations_goal_step[OF distinct Suc.prems(2) pending unheld gs])
        show ?thesis by (rule Suc.IH[OF Is Hs st'])
      qed
    next
      case Select_None
      with Suc.prems False show ?thesis by (simp add: resolution_fset_simps)
    qed
  qed
qed

text \<open>A closed state's certificates are accepted: every found state of a search from a call's initial state is one.\<close>

lemma finite_closed_state_proofs_accepted:
  assumes I: "resolution_invariant P d t st" and closed: "resolution_pending st={||}"
    and cert: "p |\<in>| finite_state_proofs st"
  shows "finite_checks_schema_proof P p d t"
proof -
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd=[]"
    and p: "p=finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st) nd"
    using cert by (auto simp: finite_state_proofs_def resolution_fset_simps)
  have root: "resolution_node_site nd=d" "resolution_node_call nd=finite_exact_term_pattern t"
    using I nd unfolding resolution_invariant_def resolution_nodes_placed_def by blast+
  have "fcard (resolution_subtree (resolution_nodes st) nd) \<le> fcard (resolution_nodes st)"
    by (rule fcard_mono) auto
  from finite_node_proof_accepted[OF I closed nd(1) this] show ?thesis by (simp add: p root)
qed

section \<open>The result of a search, and the committed resolution per call\<close>

text \<open>
  The result R3 gives a search's outcome at a call (@{const finite_program_resolution}), stated once for any
  outcome: resolved with the certificates the checker accepts, refuted when nothing was found and nothing
  diagnosed, unresolved otherwise.
\<close>

definition finite_outcome_result ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_outcome \<Rightarrow>
      ('a,'s,'d,'c) finite_resolution_result" where
  "finite_outcome_result P d t R = (let C = ffUnion (fimage finite_state_proofs (resolution_found R));
      A = ffilter (\<lambda>p. finite_checks_schema_proof P p d t) C in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R |\<union>| fimage Resolution_Refused C))"

lemma finite_program_resolution_outcome:
  "finite_program_resolution \<kappa> P d t n = finite_outcome_result P d t (finite_resolution_search \<kappa> P n (finite_initial_state d t))"
  by (simp add: finite_program_resolution_def finite_outcome_result_def Let_def)

theorem finite_outcome_result_sound:
  assumes res: "finite_outcome_result P d t R = Finite_Resolved C"
  shows "C\<noteq>{||}" and "\<And>p. p |\<in>| C \<Longrightarrow> finite_checks_schema_proof P p d t"
    and "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  show nonempty: "C\<noteq>{||}" using res unfolding finite_outcome_result_def Let_def by (auto split: if_splits)
  show accepted: "\<And>p. p |\<in>| C \<Longrightarrow> finite_checks_schema_proof P p d t"
    using res unfolding finite_outcome_result_def Let_def by (auto split: if_splits)
  from nonempty obtain p where "p |\<in>| C" by (metis all_not_fin_conv)
  then have "checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
    using accepted by (simp only: finite_checks_schema_proof_exact)
  then show "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)" by (rule schema_proof_sound)
qed

definition finite_committed_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_committed_resolution \<kappa> K P d t n =
    finite_outcome_result P d t (finite_committed_search \<kappa> K P n None {||} (finite_initial_state d t))"

theorem finite_committed_resolution_plain:
  assumes free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "finite_committed_resolution \<kappa> no_commitment P d t n = finite_program_resolution \<kappa> P d t n"
  by (simp add: finite_committed_resolution_def finite_committed_search_plain[OF free] finite_program_resolution_outcome)

theorem finite_committed_resolution_accepted:
  assumes res: "finite_committed_resolution \<kappa> K P d t n = Finite_Resolved C" and p: "p |\<in>| C"
  shows "finite_checks_schema_proof P p d t"
  by (rule finite_outcome_result_sound(2)[OF res[unfolded finite_committed_resolution_def] p])

theorem finite_committed_resolution_sound:
  assumes res: "finite_committed_resolution \<kappa> K P d t n = Finite_Resolved C"
  shows "C\<noteq>{||}" and "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  note r = res[unfolded finite_committed_resolution_def]
  show "C\<noteq>{||}" by (rule finite_outcome_result_sound(1)[OF r])
  show "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)" by (rule finite_outcome_result_sound(3)[OF r])
qed

text \<open>
  At a formed program, a formed call and a formed construction, every certificate of a found state is accepted:
  the committed resolution resolves exactly when a branch succeeds, with all of their certificates.
\<close>

theorem finite_committed_resolution_certificates:
  assumes Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_committed_resolution \<kappa> K P d t n = (let R = finite_committed_search \<kappa> K P n None {||} (finite_initial_state d t);
      C = ffUnion (fimage finite_state_proofs (resolution_found R)) in
    if C\<noteq>{||} then Finite_Resolved C else if resolution_diagnoses R={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R))"
proof -
  let ?R = "finite_committed_search \<kappa> K P n None {||} (finite_initial_state d t)"
  let ?C = "ffUnion (fimage finite_state_proofs (resolution_found ?R))"
  have closed: "resolution_invariant P d t s \<and> resolution_pending s={||}" if s: "s |\<in>| resolution_found ?R" for s
  proof -
    have "s |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n None {||}
        (finite_initial_state d t))"
      using s by (simp add: finite_committed_search_def)
    from finite_committed_search_found[OF \<kappa> resolution_initial_invariant[OF Pf tf] this] show ?thesis by simp
  qed
  have accepted: "finite_checks_schema_proof P p d t" if "p |\<in>| ?C" for p
  proof -
    from that obtain s where s: "s |\<in>| resolution_found ?R" and p: "p |\<in>| finite_state_proofs s"
      by (auto simp: resolution_fset_simps)
    from closed[OF s] have I: "resolution_invariant P d t s" and closed_s: "resolution_pending s={||}" by blast+
    show ?thesis by (rule finite_closed_state_proofs_accepted[OF I closed_s p])
  qed
  have all: "ffilter (\<lambda>p. finite_checks_schema_proof P p d t) ?C = ?C" using accepted by (auto simp: fset_eq_iff)
  show ?thesis by (auto simp: finite_committed_resolution_def finite_outcome_result_def Let_def all)
qed

section \<open>The demand-level and native forms\<close>

definition finite_committed_demand ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "finite_committed_demand \<kappa> K P D n = (let V = fimage (\<lambda>q. (q,finite_resolution_verdict
      (finite_committed_resolution \<kappa> K P (fst q) (snd q) n))) D in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"

theorem finite_committed_demand_plain:
  "finite_committed_demand no_witness_construction no_commitment P D n = finite_demand_resolution P D n"
  by (simp add: finite_committed_demand_def finite_demand_resolution_def
    finite_committed_resolution_plain[OF finite_resolution_select_none_construction])

lemma finite_resolution_verdict_true:
  "finite_resolution_verdict r = Some True \<longleftrightarrow> (\<exists>C. r = Finite_Resolved C)"
  by (cases r) (simp_all add: finite_resolution_verdict_def)

theorem finite_committed_demand_sound:
  assumes result: "finite_committed_demand \<kappa> K P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A \<subseteq> {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  let ?v = "\<lambda>q. finite_resolution_verdict (finite_committed_resolution \<kappa> K P (fst q) (snd q) n)"
  from result have Pf: "finite_system_formed P"
    and A: "A = fimage fst (ffilter (\<lambda>(q,v). v = Some True) (fimage (\<lambda>q. (q,?v q)) D))"
    by (auto simp: finite_committed_demand_def Let_def split: if_splits)
  show "schema_system_formed (decode_finite_system P)" using Pf by (simp add: finite_system_formed_correct)
  have "decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)" if "?v q = Some True" for q
    using that finite_committed_resolution_sound(2)[of \<kappa> K P "fst q" "snd q" n]
    by (auto simp: finite_resolution_verdict_true decode_finite_call_term_fields)
  then show "fset A \<subseteq> {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    unfolding A fimage_fst_filter_graph by (auto simp: ffilter.rep_eq)
qed

definition native_committed_resolution ::
    "(local_address,local_address,local_address option definition_site,local_address) finite_witness_construction \<Rightarrow>
      (local_address,local_address,local_address option definition_site,local_address) resolution_commitment \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      nat \<Rightarrow> ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_committed_resolution \<kappa> K P R n =
    (fimage (\<lambda>q. (q,finite_committed_resolution \<kappa> K P (fst q) (snd q) n)) R, finite_committed_demand \<kappa> K P R n)"

theorem native_committed_resolution_plain:
  "native_committed_resolution no_witness_construction no_commitment P R n = native_call_resolution P R n"
  by (simp add: native_committed_resolution_def native_call_resolution_def
    finite_committed_resolution_plain[OF finite_resolution_select_none_construction] finite_committed_demand_plain)

theorem native_committed_resolution_sound:
  assumes result: "native_committed_resolution \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B \<subseteq> {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  from result have T: "T = fimage (\<lambda>q. (q,finite_committed_resolution \<kappa> K P (fst q) (snd q) n)) R"
    and A: "A = finite_committed_demand \<kappa> K P R n"
    by (simp_all add: native_committed_resolution_def)
  show "fimage fst T = R" unfolding T by (simp add: fset.map_comp comp_def)
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,Finite_Resolved C) |\<in>| T"
    then have res: "finite_committed_resolution \<kappa> K P (fst q) (snd q) n = Finite_Resolved C" unfolding T by auto
    show ?thesis using finite_committed_resolution_sound[OF res] finite_committed_resolution_accepted[OF res]
      by (simp add: decode_finite_call_term_fields)
  qed
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B \<subseteq> {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    using finite_committed_demand_sound unfolding A by blast
qed

section \<open>The commitment a declaration gives\<close>

text \<open>
  A call goal is committed directly when its site is a declared producer, its call is a pair whose input is
  ground and whose output holds a variable, and every other pending goal in the focus that holds a variable of the
  output is a declared consumer of that producer holding the output pattern itself at its declared side, its other
  side sharing no variable with it. A goal is committed at a declared socket when the node at its parent position
  holds the declared site and schema and its position ends at the socket; the declaration without the kept head
  applies only where the parent is the focus root and its call output, as it stands, is a variant of its clause's
  head output (`finite_variant`), the holders test then covering the variables of that output as well. Its call is a pair with a ground input, or it is a material premise whose source is a
  ground whole artifact and whose four other fields are distinct variables; every other pending goal in the focus
  holding a variable of its output is a sibling, and every node whose call holds one is its parent or an ancestor.
  The tests read sites for equality, the schema as a value, positions, where variables occur and the call's pair
  shape: no clause key, no variable name and no position of an answer.
\<close>

definition finite_output_consumer ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_output_consumer D d y h = (case h of
      Resolution_Call_Goal q r e p \<Rightarrow> (case p of
          Finite_Pattern_Pair x z \<Rightarrow>
            ((d,e,True) |\<in>| declared_consumers D \<and> z = y \<and>
              finite_pattern_variables x |\<inter>| finite_pattern_variables y = {||}) \<or>
            ((d,e,False) |\<in>| declared_consumers D \<and> x = y \<and>
              finite_pattern_variables z |\<inter>| finite_pattern_variables y = {||})
        | _ \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

definition finite_direct_commitment ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_direct_commitment D F st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> (case p of
          Finite_Pattern_Pair x y \<Rightarrow> d |\<in>| declared_producers D \<and>
            finite_pattern_variables x = {||} \<and> finite_pattern_variables y \<noteq> {||} \<and>
            fBall (finite_focus_pending F st) (\<lambda>h. h = g \<or>
              resolution_goal_variables h |\<inter>| finite_pattern_variables y = {||} \<or> finite_output_consumer D d y h)
        | _ \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"


definition finite_socket_holders ::
    "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_holders F st q Y g \<longleftrightarrow>
    fBall (finite_focus_pending F st) (\<lambda>h. h = g \<or> resolution_goal_variables h |\<inter>| Y = {||} \<or>
      (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = butlast q)) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. finite_pattern_variables (resolution_node_call nd) |\<inter>| Y = {||} \<or>
      take (length (resolution_node_position nd)) (butlast q) = resolution_node_position nd)"

text \<open>
  A pattern is a variant of another when they have the same shape, the same leaves, and their variables correspond
  one to one (`finite_variant_pairs` lists the corresponding variables, position by position). The parent's call
  output is a variant of its clause's head output exactly when every head output an extending instance of the clause
  gives is an instance of the parent's call: a head output that the call constrains (a leaf, or two positions sharing
  one variable where the head's are distinct) is refused. The test reads leaves as values and variables for equality
  within one pattern: no variable name.
\<close>

fun finite_variant_pairs :: "'a finite_term_pattern \<Rightarrow> 'v finite_term_pattern \<Rightarrow> ('a \<times> 'v) list option" where
  "finite_variant_pairs (Finite_Variable a) (Finite_Variable v) = Some [(a,v)]"
| "finite_variant_pairs (Finite_Pattern_Target t) (Finite_Pattern_Target u) = (if t = u then Some [] else None)"
| "finite_variant_pairs (Finite_Pattern_Payload b) (Finite_Pattern_Payload c) = (if b = c then Some [] else None)"
| "finite_variant_pairs (Finite_Pattern_Pair a b) (Finite_Pattern_Pair c e) =
    (case (finite_variant_pairs a c,finite_variant_pairs b e) of (Some l,Some m) \<Rightarrow> Some (l @ m) | _ \<Rightarrow> None)"
| "finite_variant_pairs _ _ = None"

definition finite_variant :: "'a finite_term_pattern \<Rightarrow> 'v finite_term_pattern \<Rightarrow> bool" where
  "finite_variant p p' \<longleftrightarrow> (case finite_variant_pairs p p' of None \<Rightarrow> False
    | Some l \<Rightarrow> list_all (\<lambda>(a,v). list_all (\<lambda>(b,w). (a = b) = (v = w)) l) l)"

definition finite_parent_output ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern option" where
  "finite_parent_output nd = (case (finite_schema_conclusion (resolution_node_schema nd),resolution_node_call nd) of
      (Finite_Pattern_Pair hi ho,Finite_Pattern_Pair x out) \<Rightarrow> if finite_variant ho out then Some out else None
    | _ \<Rightarrow> None)"

text \<open>
  A socket is committed only while every other premise of its parent clause, ordinary or material, is a pending goal:
  a sibling resolved first may have fixed a clause variable the obligation's new instance must change, and a pruning
  in its subtree rests on the ranks of a derivation the commitment then abandons (task 589: with a leaf-bearing sibling
  selected first, the committed resolution refuted a true call, `Factor_Resolution_Controls`, the order control).
\<close>

text \<open>
  A socket commits only while its clause's premise-only variables are free at its parent node (task 621, q112): each
  is bound at the node to its own variable, so they are distinct and unbound, and every pending goal holding one is a
  child of the parent, a pending sibling or the goal itself. A construction binding one first, or a goal outside the
  clause holding one, would make the obligation's new instance of the clause change what another goal holds
  (#593's counterexample (ii), DECISIONS.md, task 495's entry, corrections (5) and (6)).
\<close>

definition finite_premise_only_free ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_premise_only_free st nd \<longleftrightarrow>
    fBall (finite_schema_variables (resolution_node_schema nd) |-|
        finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))) (\<lambda>a.
      (a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd \<and>
      fBall (resolution_pending st) (\<lambda>h. ((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables h \<longrightarrow>
        resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position nd))"

definition finite_siblings_pending ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> bool" where
  "finite_siblings_pending st q S \<longleftrightarrow>
    fBall (finite_schema_premises S) (\<lambda>(s,e,p). s = last q \<or>
      fBex (resolution_pending st) (\<lambda>h. resolution_goal_position h = butlast q @ [s])) \<and>
    fBall (finite_schema_materials S) (\<lambda>(s,M). s = last q \<or>
      fBex (resolution_pending st) (\<lambda>h. resolution_goal_position h = butlast q @ [s]))"

text \<open>
  A socket declared with the kept head commits by the holders test at the goal's output alone. A socket declared
  without it commits only where its parent is the focus root, the parent's call output is a variant of its clause's
  head output, and the holders test covers the variables of that output beside the goal's: an extending instance
  changes the parent's head output, which then is the focus goal's answer, absorbed by that goal's own commitment.
\<close>

definition finite_socket_kept ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow>
      ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_kept D F st q Y g \<longleftrightarrow> q \<noteq> [] \<and> fBex (resolution_nodes st) (\<lambda>nd.
    resolution_node_position nd = butlast q \<and>
    (resolution_node_site nd,resolution_node_schema nd,last q,True) |\<in>| declared_sockets D \<and>
    finite_siblings_pending st q (resolution_node_schema nd) \<and> finite_premise_only_free st nd) \<and>
    finite_socket_holders F st q Y g"

definition finite_socket_free ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow>
      ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_free D F st q Y g \<longleftrightarrow> q \<noteq> [] \<and> F = Some (butlast q) \<and> fBex (resolution_nodes st) (\<lambda>nd.
    resolution_node_position nd = butlast q \<and>
    (resolution_node_site nd,resolution_node_schema nd,last q,False) |\<in>| declared_sockets D \<and>
    finite_siblings_pending st q (resolution_node_schema nd) \<and> finite_premise_only_free st nd \<and>
    (case finite_parent_output nd of None \<Rightarrow> False
      | Some out \<Rightarrow> finite_socket_holders F st q (Y |\<union>| finite_pattern_variables out) g))"

definition finite_socket_declared ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow>
      ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_declared D F st q Y g \<longleftrightarrow> finite_socket_kept D F st q Y g \<or> finite_socket_free D F st q Y g"

fun finite_free_fields :: "'v finite_material_pattern \<Rightarrow> bool" where
  "finite_free_fields M = (case (finite_material_atoms M,finite_material_edges M,finite_material_counts M,
      finite_material_functions M) of
    (Finite_Variable a,Finite_Variable b,Finite_Variable c,Finite_Variable e) \<Rightarrow> distinct [a,b,c,e]
  | _ \<Rightarrow> False)"

definition finite_socket_commitment ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_commitment D F st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> (case p of
          Finite_Pattern_Pair x y \<Rightarrow> finite_pattern_variables x = {||} \<and> finite_pattern_variables y \<noteq> {||} \<and>
            finite_socket_declared D F st q (finite_pattern_variables y) g
        | _ \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> finite_canonical_solutions M \<noteq> None \<and> finite_free_fields M \<and>
        finite_socket_declared D F st q (finite_material_variables M) g)"

text \<open>
  The test checks, at every commitment, that the committed goal is a premise of the node at its parent position
  (task 621, q112): the invariant links a node to its premises, not a goal to its parent, and a committed goal's
  exchange rebuilds the answer through that link (@{text Factor_Resolution_Producer_Discharge}). A call goal is its
  parent clause's ordinary premise, a material goal its material premise. The root goal has no parent and passes.
\<close>

definition finite_goal_premise :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_premise st g \<longleftrightarrow> resolution_goal_position g \<noteq> [] \<longrightarrow>
    (\<exists>np e0 p0. np |\<in>| resolution_nodes st \<and> resolution_node_position np = butlast (resolution_goal_position g) \<and>
      (last (resolution_goal_position g),e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np))"

lemma finite_goal_premise_code [code]:
  "finite_goal_premise st g \<longleftrightarrow> resolution_goal_position g = [] \<or>
    fBex (resolution_nodes st) (\<lambda>np. resolution_node_position np = butlast (resolution_goal_position g) \<and>
      fBex (finite_schema_premises (resolution_node_schema np)) (\<lambda>z. fst z = last (resolution_goal_position g)))"
proof
  assume a: "finite_goal_premise st g"
  show "resolution_goal_position g = [] \<or>
    fBex (resolution_nodes st) (\<lambda>np. resolution_node_position np = butlast (resolution_goal_position g) \<and>
      fBex (finite_schema_premises (resolution_node_schema np)) (\<lambda>z. fst z = last (resolution_goal_position g)))"
  proof (cases "resolution_goal_position g = []")
    case False
    with a obtain np e0 p0 where "np |\<in>| resolution_nodes st"
      "resolution_node_position np = butlast (resolution_goal_position g)"
      "(last (resolution_goal_position g),e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
      unfolding finite_goal_premise_def by blast
    then show ?thesis by force
  qed simp
next
  assume "resolution_goal_position g = [] \<or>
    fBex (resolution_nodes st) (\<lambda>np. resolution_node_position np = butlast (resolution_goal_position g) \<and>
      fBex (finite_schema_premises (resolution_node_schema np)) (\<lambda>z. fst z = last (resolution_goal_position g)))"
  then show "finite_goal_premise st g"
  proof
    assume "resolution_goal_position g = []"
    then show ?thesis by (simp add: finite_goal_premise_def)
  next
    assume "fBex (resolution_nodes st) (\<lambda>np. resolution_node_position np = butlast (resolution_goal_position g) \<and>
      fBex (finite_schema_premises (resolution_node_schema np)) (\<lambda>z. fst z = last (resolution_goal_position g)))"
    then obtain np z where "np |\<in>| resolution_nodes st"
      "resolution_node_position np = butlast (resolution_goal_position g)"
      "z |\<in>| finite_schema_premises (resolution_node_schema np)" "fst z = last (resolution_goal_position g)"
      by blast
    then show ?thesis unfolding finite_goal_premise_def by (cases z) auto
  qed
qed

definition finite_material_premise :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_material_premise st g \<longleftrightarrow> resolution_goal_position g = [] \<or>
    fBex (resolution_nodes st) (\<lambda>np. resolution_node_position np = butlast (resolution_goal_position g) \<and>
      fBex (finite_schema_materials (resolution_node_schema np)) (\<lambda>z. fst z = last (resolution_goal_position g)))"

definition finite_declared_commitment ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_commitment" where
  "finite_declared_commitment D = \<lparr>commit_call=(\<lambda>F st g. finite_goal_premise st g \<and>
      (finite_direct_commitment D F st g \<or> (resolution_is_call g \<and> finite_socket_commitment D F st g))),
    commit_material=(\<lambda>F st g. finite_material_premise st g \<and> \<not> resolution_is_call g \<and>
      finite_socket_commitment D F st g)\<rparr>"

text \<open>
  Three state conditions the material single solution's discharge needs beyond those the test checks
  (\<open>Factor_Resolution_Material_Discharge\<close>, task 631; DECISIONS.md, task 495's entry, correction (7)): the pending
  children of the parent node are its clause's instances under its bindings, no premise-only variable of the parent stands
  in its call, and, at a socket declared without the kept head, the parent call's input and output share no variable.
  Each is true where the search commits and a counterexample to the exchange premise where it fails; the test conjoins them
  where it commits (task 630).
\<close>

definition finite_node_binding ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern" where
  "finite_node_binding nd a = (case finite_singleton_option
      (fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd))) of
      Some p \<Rightarrow> p | None \<Rightarrow> Finite_Variable ((resolution_node_position nd,True),a))"

text \<open>
  The node's one row at the key gives the binding; where the rows at the key are not one value, the node's own image of the
  variable stands in.
\<close>

lemma finite_node_binding_row:
  assumes sv: "single_valued (fset (resolution_node_bindings nd))"
    and row: "(a,p) |\<in>| resolution_node_bindings nd"
  shows "finite_node_binding nd a = p"
proof -
  have "fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd)) = {|p|}"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd)) \<longleftrightarrow> x |\<in>| {|p|}"
    proof
      assume "x |\<in>| fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd))"
      then obtain z where z: "z |\<in>| ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd)" "x = snd z" by blast
      obtain c y where zc: "z = (c,y)" by (cases z)
      have "(a,x) |\<in>| resolution_node_bindings nd" using z unfolding zc by auto
      then have "x = p" using sv row unfolding single_valued_def by blast
      then show "x |\<in>| {|p|}" by simp
    next
      assume "x |\<in>| {|p|}"
      then have xp: "x = p" by simp
      have "(a,p) |\<in>| ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd)" using row by simp
      then have "snd (a,p) |\<in>| fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd))" by (rule fimageI)
      then show "x |\<in>| fimage snd (ffilter (\<lambda>z. fst z = a) (resolution_node_bindings nd))" using xp by simp
    qed
  qed
  then show ?thesis by (simp add: finite_node_binding_def)
qed

definition finite_children_instances ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_children_instances st nd \<longleftrightarrow>
    fBall (finite_schema_premises (resolution_node_schema nd)) (\<lambda>(s,e,p).
      Resolution_Call_Goal (resolution_node_position nd@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
        (finite_pattern_substitute (finite_node_binding nd) p) |\<in>| resolution_pending st) \<and>
    fBall (finite_schema_materials (resolution_node_schema nd)) (\<lambda>(s,N).
      Resolution_Material_Goal (resolution_node_position nd@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
        (finite_material_pattern_substitute (finite_node_binding nd) N) |\<in>| resolution_pending st) \<and>
    fBall (resolution_pending st) (\<lambda>h. resolution_goal_position h \<noteq> [] \<longrightarrow>
      butlast (resolution_goal_position h) = resolution_node_position nd \<longrightarrow>
      fBex (finite_schema_premises (resolution_node_schema nd)) (\<lambda>(s,e,p).
        h = Resolution_Call_Goal (resolution_node_position nd@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute (finite_node_binding nd) p)) \<or>
      fBex (finite_schema_materials (resolution_node_schema nd)) (\<lambda>(s,N).
        h = Resolution_Material_Goal (resolution_node_position nd@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute (finite_node_binding nd) N)))"

definition finite_premise_only_unshared :: "('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_premise_only_unshared nd \<longleftrightarrow>
    fBall (finite_schema_variables (resolution_node_schema nd) |-|
        finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))) (\<lambda>a.
      ((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (resolution_node_call nd))"

definition finite_input_output_apart :: "('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_input_output_apart nd \<longleftrightarrow> (case resolution_node_call nd of
      Finite_Pattern_Pair x y \<Rightarrow> finite_pattern_variables x |\<inter>| finite_pattern_variables y = {||}
    | _ \<Rightarrow> True)"

definition finite_material_narrowed ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_material_narrowed D F st g \<longleftrightarrow> (case g of
      Resolution_Material_Goal q r M \<Rightarrow> fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        finite_children_instances st nd \<and> finite_premise_only_unshared nd \<and>
        (finite_socket_kept D F st q (finite_material_variables M) g \<or> finite_input_output_apart nd))
    | Resolution_Call_Goal q r e p \<Rightarrow> True)"

export_code finite_material_narrowed checking SML

lemma finite_declared_commitment_premise:
  assumes "commit_call (finite_declared_commitment D) F st g"
  shows "finite_goal_premise st g"
  using assms by (simp add: finite_declared_commitment_def)

theorem finite_declared_commitment_none:
  "finite_declared_commitment no_declarations = no_commitment"
proof -
  have nd [simp]: "\<not> finite_direct_commitment no_declarations F st g" for F st g
    by (simp add: finite_direct_commitment_def no_declarations_def split: resolution_goal.split finite_term_pattern.split)
  have ns [simp]: "\<not> finite_socket_commitment no_declarations F st g" for F st g
    by (simp add: finite_socket_commitment_def finite_socket_declared_def finite_socket_kept_def
      finite_socket_free_def no_declarations_def
      split: resolution_goal.split finite_term_pattern.split)
  have c: "(\<lambda>F st g. finite_goal_premise st g \<and> (finite_direct_commitment no_declarations F st g \<or>
      (resolution_is_call g \<and> finite_socket_commitment no_declarations F st g))) = (\<lambda>F st g. False)"
    by (intro ext) simp
  have m: "(\<lambda>F st g. finite_material_premise st g \<and> \<not> resolution_is_call g \<and>
      finite_socket_commitment no_declarations F st g) = (\<lambda>F st g. False)"
    by (intro ext) simp
  show ?thesis unfolding finite_declared_commitment_def no_commitment_def c m ..
qed

text \<open>
  A committed call's input is ground as the call stands: the direct test and the socket test both demand it. The
  exchange quantifies over every supported state, and output equivalence relates a producer's answers at one input
  only; a variable of the input held by another pending goal could be bound otherwise by the sub-search than by the
  support, but no committed input holds one, so every grounding gives it the one value the call states.
\<close>

lemma finite_declared_commitment_input_ground:
  assumes committed: "commit_call (finite_declared_commitment D) F st g"
  obtains q r d x y where "g = Resolution_Call_Goal q r d (Finite_Pattern_Pair x y)"
    "finite_pattern_variables x = {||}" "finite_pattern_variables y \<noteq> {||}"
proof -
  from committed have c: "finite_direct_commitment D F st g \<or> (resolution_is_call g \<and> finite_socket_commitment D F st g)"
    by (simp add: finite_declared_commitment_def)
  show thesis
  proof (cases g)
    case (Resolution_Call_Goal q r d p)
    show thesis
    proof (cases p)
      case (Finite_Pattern_Pair x y)
      show thesis using c that Resolution_Call_Goal Finite_Pattern_Pair
        by (auto simp: finite_direct_commitment_def finite_socket_commitment_def)
    qed (use c Resolution_Call_Goal in \<open>simp_all add: finite_direct_commitment_def finite_socket_commitment_def\<close>)
  next
    case (Resolution_Material_Goal q r M)
    then show thesis using c by (simp add: finite_direct_commitment_def)
  qed
qed

corollary finite_declared_commitment_input_value:
  assumes committed: "commit_call (finite_declared_commitment D) F st (Resolution_Call_Goal q r d (Finite_Pattern_Pair x y))"
  shows "resolution_value \<theta> x = resolution_value \<theta>' x"
proof -
  obtain q' r' d' x' y' where g: "Resolution_Call_Goal q r d (Finite_Pattern_Pair x y) =
      Resolution_Call_Goal q' r' d' (Finite_Pattern_Pair x' y')" and ground: "finite_pattern_variables x' = {||}"
    by (rule finite_declared_commitment_input_ground[OF committed])
  from g ground have "finite_pattern_variables x = {||}" by simp
  then show ?thesis by (auto intro: resolution_value_cong)
qed

corollary finite_declared_resolution_none:
  "(\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N) \<Longrightarrow>
    finite_committed_resolution \<kappa> (finite_declared_commitment no_declarations) P d t n = finite_program_resolution \<kappa> P d t n"
  "finite_committed_demand no_witness_construction (finite_declared_commitment no_declarations) P D n =
    finite_demand_resolution P D n"
  "native_committed_resolution no_witness_construction (finite_declared_commitment no_declarations) P R n =
    native_call_resolution P R n"
  by (simp_all add: finite_declared_commitment_none finite_committed_resolution_plain finite_committed_demand_plain
    native_committed_resolution_plain)

section \<open>The lifting at a focused barred support\<close>

text \<open>
  The committed search solves the goals of its focus, prunes a ground goal equal to an unbarred ancestor's call and
  ends a branch reaching a barred ancestor's call with a diagnosis. Its lifting is stated at a support of the focus
  whose ranks cover the unbarred ancestors only (@{const resolution_supported_at}): from such a support the search
  returns a found state supported at its focus, or a diagnosis that is not a witnessed failure. It rests on two
  premises, each a property of the commitment and the construction and not of the search: the exchange
  (@{text finite_commitment_exchanges}), that at a committed call some kept state of the committed goal's sub-search
  is supported with every node then present barred, and at a committed material premise some canonical successor is
  supported; and that a selected construction keeps a support (@{text finite_construction_lifts}). Both hold at no
  commitment and at the empty construction. The steps are R4's, at the focused barred support.
\<close>

definition finite_witnessed_diagnosis :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> bool" where
  "finite_witnessed_diagnosis D \<longleftrightarrow> (case D of Resolution_Witnessed W g \<Rightarrow> True | _ \<Rightarrow> False)"

definition finite_lifted_outcome ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome \<Rightarrow> bool" where
  "finite_lifted_outcome U F P R \<longleftrightarrow>
    (\<exists>st' B' \<theta>'. st' |\<in>| resolution_found R \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
    (\<exists>D. D |\<in>| resolution_diagnoses R \<and> \<not> finite_witnessed_diagnosis D)"

lemma finite_lifted_outcome_union:
  assumes mem: "Oc |\<in>| Os" and lifted: "finite_lifted_outcome U F P Oc"
  shows "finite_lifted_outcome U F P (finite_outcome_union Os)"
  using lifted unfolding finite_lifted_outcome_def
proof (elim disjE exE conjE)
  fix st' B' \<theta>' assume f: "st' |\<in>| resolution_found Oc" and s: "resolution_supported_at U F B' P st' \<theta>'"
  have "st' |\<in>| resolution_found (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_found, OF mem f] by simp
  then show "(\<exists>st' B' \<theta>'. st' |\<in>| resolution_found (finite_outcome_union Os) \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
      (\<exists>D. D |\<in>| resolution_diagnoses (finite_outcome_union Os) \<and> \<not> finite_witnessed_diagnosis D)"
    using s by blast
next
  fix D assume d: "D |\<in>| resolution_diagnoses Oc" and w: "\<not> finite_witnessed_diagnosis D"
  have "D |\<in>| resolution_diagnoses (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_diagnoses, OF mem d] by simp
  then show "(\<exists>st' B' \<theta>'. st' |\<in>| resolution_found (finite_outcome_union Os) \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
      (\<exists>D. D |\<in>| resolution_diagnoses (finite_outcome_union Os) \<and> \<not> finite_witnessed_diagnosis D)"
    using w by blast
qed

lemma finite_lifted_diagnosis:
  "D |\<in>| resolution_diagnoses R \<Longrightarrow> \<not> finite_witnessed_diagnosis D \<Longrightarrow> finite_lifted_outcome U F P R"
  unfolding finite_lifted_outcome_def by blast

lemma resolution_focused_some [simp]: "resolution_focused (Some f) q \<longleftrightarrow> take (length f) q = f"
  by (simp add: resolution_focused_def)

lemma resolution_focused_within:
  assumes focus: "resolution_focused F q" and within: "take (length q) q' = q"
  shows "resolution_focused F q'"
proof (cases F)
  case None
  then show ?thesis by simp
next
  case (Some f)
  with focus have f: "take (length f) q = f" by simp
  then have le: "length f \<le> length q" by (metis length_take min.cobounded1)
  have "take (length f) q' = take (length f) (take (length q) q')" using le by (simp add: min.absorb1)
  also have "\<dots> = f" using within f by simp
  finally show ?thesis using Some by simp
qed

lemma finite_focus_pending_focused:
  "g |\<in>| finite_focus_pending F st \<longleftrightarrow> g |\<in>| resolution_pending st \<and> resolution_focused F (resolution_goal_position g)"
  by (cases F) (auto simp: finite_focus_pending_def resolution_fset_simps)

lemma resolution_supported_at_narrow:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and focus: "resolution_focused F q"
  shows "resolution_supported_at U (Some q) B P st \<theta>"
proof -
  have w: "\<And>q'. resolution_focused (Some q) q' \<Longrightarrow> resolution_focused F q'"
    using resolution_focused_within[OF focus] by simp
  show ?thesis using sup w unfolding resolution_supported_at_def by blast
qed

lemma resolution_supported_at_unbarred:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and g: "g |\<in>| resolution_pending st"
    and focus: "resolution_focused F (resolution_goal_position g)"
  shows "\<not> finite_pruned (finite_unbarred B st) g"
proof
  assume pruned: "finite_pruned (finite_unbarred B st) g"
  then obtain q r e p where gq: "g = Resolution_Call_Goal q r e p"
    by (auto simp: finite_pruned_def split: resolution_goal.splits)
  with pruned obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd |\<notin>| B"
    "resolution_before (resolution_node_position nd) q" "resolution_node_site nd = e" "resolution_node_call nd = p"
    by (auto simp: finite_pruned_def finite_unbarred_def resolution_before_def resolution_fset_simps)
  have fq: "resolution_focused F q" using focus gq by simp
  have "resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
      resolution_rank (decode_finite_system P)
        (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
    using sup g fq nd(1,2,3) unfolding gq resolution_supported_at_def by blast
  with nd(4,5) show False by simp
qed

lemma finite_resolution_select_lifts:
  assumes sel: "finite_resolution_select \<kappa> P st = Select_Goals G"
  shows "G \<noteq> {||} \<and>
    (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
proof -
  let ?A = "ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) (resolution_pending st)"
  have G: "G = finite_goal_selection (resolution_pending st) ?A \<and> G \<noteq> {||}"
    using sel by (auto simp: finite_resolution_select_def Let_def split: if_splits)
  show ?thesis
    using G finite_goal_selection_member[where G="resolution_pending st" and A="?A"]
    by (auto simp: resolution_fset_simps)
qed

text \<open>
  At a committed call the premise asks for a kept state only where the lifting applies it (task 621, q115): at a state
  keeping the holders invariant of @{text Factor_Construction_Holders} and at a call no free registered variable holds,
  as every call the search selects is (@{thm [source] finite_resolution_select_unheld}).
\<close>

definition finite_commitment_exchanges ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_commitment_exchanges U \<kappa> K P \<longleftrightarrow>
    (\<forall>n F B st \<theta> g d t. resolution_invariant P d t st \<longrightarrow> resolution_supported_at U F B P st \<theta> \<longrightarrow>
      g |\<in>| finite_focus_pending F st \<longrightarrow>
      (finite_goal_committed K F st g \<longrightarrow> resolution_registrations_held \<kappa> st \<longrightarrow> \<not> finite_held \<kappa> st g \<longrightarrow>
        (\<forall>s0 B0 \<theta>0. s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st) \<longrightarrow>
          resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0 \<longrightarrow>
          (\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g)
              (resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)) \<and>
            resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'))) \<and>
      (\<forall>q r M Ws. g = Resolution_Material_Goal q r M \<longrightarrow> finite_canonical_solutions M = Some Ws \<longrightarrow>
        commit_material K F st g \<longrightarrow>
        (\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
          resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>')))"

text \<open>
  A construction lifts at a state keeping the holders invariant: every selected node in the focus has a construction
  step whose successor is supported with every node present at the step barred (task 526). Complete registrations
  give it (@{text Factor_Least_Witness_Registrations}).
\<close>

definition finite_construction_lifts ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_construction_lifts U \<kappa> P \<longleftrightarrow>
    (\<forall>F B st \<theta> d t N nd. resolution_invariant P d t st \<longrightarrow> resolution_registrations_held \<kappa> st \<longrightarrow>
      resolution_supported_at U F B P st \<theta> \<longrightarrow>
      finite_resolution_select \<kappa> P (finite_focused F st) = Select_Construction N \<longrightarrow>
      nd |\<in>| N \<longrightarrow> resolution_focused F (resolution_node_position nd) \<longrightarrow>
      (\<exists>\<theta>'. resolution_supported_at U F (B |\<union>| fimage resolution_node_position (resolution_nodes st)) P
        (finite_construction_step \<kappa> P st nd) \<theta>'))"

lemma finite_commitment_exchanges_call:
  assumes "finite_commitment_exchanges U \<kappa> K P" "resolution_invariant P d t st" "resolution_supported_at U F B P st \<theta>"
    "g |\<in>| finite_focus_pending F st" "finite_goal_committed K F st g"
    "resolution_registrations_held \<kappa> st" "\<not> finite_held \<kappa> st g"
    "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)"
    "resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
  obtains s \<theta>' where "s |\<in>| finite_kept (resolution_goal_position g)
      (resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st))"
    "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
  using assms unfolding finite_commitment_exchanges_def by blast

lemma finite_commitment_exchanges_material:
  assumes "finite_commitment_exchanges U \<kappa> K P" "resolution_invariant P d t st" "resolution_supported_at U F B P st \<theta>"
    "g |\<in>| finite_focus_pending F st" "g = Resolution_Material_Goal q r M" "finite_canonical_solutions M = Some Ws"
    "commit_material K F st g"
  obtains st' \<theta>' where "st' |\<in>| finite_solution_successors st q r M Ws"
    "resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
  using assms unfolding finite_commitment_exchanges_def by blast

lemma finite_commitment_exchanges_none: "finite_commitment_exchanges U \<kappa> no_commitment P"
  by (simp add: finite_commitment_exchanges_def no_commitment_def finite_goal_committed_def)

lemma finite_construction_lifts_free:
  assumes free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "finite_construction_lifts U \<kappa> P"
  unfolding finite_construction_lifts_def using free by blast

lemma finite_construction_lifts_none: "finite_construction_lifts U no_witness_construction P"
  by (rule finite_construction_lifts_free[OF finite_resolution_select_none_construction])

lemma resolution_supported_at_barred_mono:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and sub: "B |\<subseteq>| B'"
  shows "resolution_supported_at U F B' P st \<theta>"
proof -
  have out: "x |\<notin>| B" if "x |\<notin>| B'" for x using sub that by (auto dest: fsubsetD)
  show ?thesis using sup out unfolding resolution_supported_at_def by blast
qed

theorem finite_committed_lifting:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and foreign: "\<And>z. U z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and exchanges: "finite_commitment_exchanges U \<kappa> K P"
    and constructions: "finite_construction_lifts U \<kappa> P"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_registrations_held \<kappa> st \<Longrightarrow>
    resolution_supported_at U F B P st \<theta> \<Longrightarrow> finite_lifted_outcome U F P (finite_committed_search \<kappa> K P n F B st)"
proof (induction n arbitrary: F B st \<theta>)
  case 0
  show ?case
  proof (cases "finite_focus_pending F st = {||}")
    case True
    then show ?thesis using "0.prems"(3)
      unfolding finite_lifted_outcome_def by (auto simp: finite_committed_search_def)
  next
    case False
    then show ?thesis
      by (intro finite_lifted_diagnosis[where D="Resolution_Cut (finite_focus_pending F st)"])
        (simp_all add: finite_committed_search_def finite_witnessed_diagnosis_def)
  qed
next
  case (Suc n)
  let ?sel = "finite_resolution_select \<kappa> P"
  let ?rec = "finite_committed_search \<kappa> K P n"
  have I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and sup: "resolution_supported_at U F B P st \<theta>" by (rule Suc.prems)+
  have distinct: "resolution_positions_distinct st" using I unfolding resolution_invariant_def by blast
  have Ip: "resolution_pattern_invariant P d (finite_exact_term_pattern t) st"
    using I by (simp add: resolution_invariant_pattern)
  show ?case
  proof (cases "finite_focus_pending F st = {||}")
    case True
    then show ?thesis using sup unfolding finite_lifted_outcome_def by (auto simp: finite_committed_search_def)
  next
    case False
    show ?thesis
    proof (cases "?sel (finite_focused F st)")
      case (Select_Construction N)
      let ?B' = "finite_committed_barring B st"
      let ?M = "ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N"
      show ?thesis
      proof (cases "?M = {||}")
        case True
        have eq: "finite_committed_search \<kappa> K P (Suc n) F B st =
            Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}"
          using False Select_Construction True by (simp add: finite_committed_search_def Let_def)
        show ?thesis unfolding eq
          by (rule finite_lifted_diagnosis[where D="Resolution_Stuck (finite_focus_pending F st)"])
            (simp_all add: finite_witnessed_diagnosis_def)
      next
        case nonempty: False
        then obtain nd where ndM: "nd |\<in>| ?M" by (metis all_not_fin_conv)
        then have nd: "nd |\<in>| N" and focus: "resolution_focused F (resolution_node_position nd)"
          by (auto simp: resolution_fset_simps)
        obtain \<theta>' where sup': "resolution_supported_at U F ?B' P (finite_construction_step \<kappa> P st nd) \<theta>'"
          using constructions I H sup Select_Construction nd focus
          unfolding finite_construction_lifts_def finite_committed_barring_def by blast
        have I': "resolution_invariant P d t (finite_construction_step \<kappa> P st nd)"
          by (rule resolution_construction_step[OF I \<kappa>])
        have H': "resolution_registrations_held \<kappa> (finite_construction_step \<kappa> P st nd)"
          by (rule resolution_registrations_construction_step[OF H])
        have lifted: "finite_lifted_outcome U F P (?rec F ?B' (finite_construction_step \<kappa> P st nd))"
          by (rule Suc.IH[OF I' H' sup'])
        have mem: "?rec F ?B' (finite_construction_step \<kappa> P st nd) |\<in>|
            fimage (?rec F ?B') (fimage (finite_construction_step \<kappa> P st) ?M)"
          by (rule fimageI, rule fimageI[OF ndM])
        have eq: "finite_committed_search \<kappa> K P (Suc n) F B st =
            finite_outcome_union (fimage (?rec F ?B') (fimage (finite_construction_step \<kappa> P st) ?M))"
          using False Select_Construction nonempty by (simp add: finite_committed_search_def Let_def)
        show ?thesis unfolding eq by (rule finite_lifted_outcome_union[OF mem lifted])
      qed
    next
      case Select_None
      have eq: "finite_committed_search \<kappa> K P (Suc n) F B st = Resolution_Outcome {||}
          (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))"
        using False Select_None by (simp add: finite_committed_search_def)
      show ?thesis unfolding eq
        by (rule finite_lifted_diagnosis[where D="Resolution_Stuck (finite_focus_pending F st)"])
          (simp_all add: finite_witnessed_diagnosis_def)
    next
      case (Select_Goals G)
      have focused_pending: "resolution_pending (finite_focused F st) = finite_focus_pending F st"
        by (simp add: finite_focused_def)
      obtain g where g: "g |\<in>| G" and gp: "g |\<in>| finite_focus_pending F st"
        and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
        using finite_resolution_select_lifts[OF Select_Goals] focused_pending by (metis all_not_fin_conv)
      have pending: "g |\<in>| resolution_pending st" and focus: "resolution_focused F (resolution_goal_position g)"
        using gp by (simp_all add: finite_focus_pending_focused)
      have unheld: "\<not> finite_held \<kappa> st g" by (rule finite_resolution_select_unheld[OF Select_Goals g])
      define Og where "Og = finite_committed_goal_outcome ?rec K P F B st g"
      have eq: "finite_committed_search \<kappa> K P (Suc n) F B st =
          finite_outcome_union (fimage (finite_committed_goal_outcome ?rec K P F B st) G)"
        using False Select_Goals by (simp add: finite_committed_search_def)
      have memg: "Og |\<in>| fimage (finite_committed_goal_outcome ?rec K P F B st) G"
        unfolding Og_def by (rule fimageI[OF g])
      have unpruned: "\<not> finite_pruned (finite_unbarred B st) g"
        by (rule resolution_supported_at_unbarred[OF sup pending focus])
      have "finite_lifted_outcome U F P Og"
      proof (cases "finite_pruned (finite_barred B st) g")
        case True
        have "Og = Resolution_Outcome {||} {|Resolution_Cut {|g|}|}"
          unfolding Og_def finite_committed_goal_outcome_def using unpruned True by simp
        then show ?thesis
          by (simp only:) (rule finite_lifted_diagnosis[where D="Resolution_Cut {|g|}"],
            simp_all add: finite_witnessed_diagnosis_def)
      next
        case barred: False
        show ?thesis
        proof (cases "finite_goal_committed K F st g")
          case True
          define q where "q = resolution_goal_position g"
          define sub where "sub = ?rec (Some q) B st"
          have Og: "Og = finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
              (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                (finite_kept q (resolution_found sub))))"
            unfolding Og_def finite_committed_goal_outcome_def sub_def q_def using unpruned barred True
            by (simp add: Let_def)
          have supq: "resolution_supported_at U (Some q) B P st \<theta>"
            unfolding q_def by (rule resolution_supported_at_narrow[OF sup focus])
          have "finite_lifted_outcome U (Some q) P sub" unfolding sub_def by (rule Suc.IH[OF I H supq])
          then consider (found) s0 B0 \<theta>0 where "s0 |\<in>| resolution_found sub"
              "resolution_supported_at U (Some q) B0 P s0 \<theta>0"
            | (diag) D where "D |\<in>| resolution_diagnoses sub" "\<not> finite_witnessed_diagnosis D"
            unfolding finite_lifted_outcome_def by blast
          then show ?thesis
          proof cases
            case diag
            have mem: "Resolution_Outcome {||} (resolution_diagnoses sub) |\<in>|
                finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
                  (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                    (finite_kept q (resolution_found sub)))" by simp
            have "finite_lifted_outcome U F P (Resolution_Outcome {||} (resolution_diagnoses sub))"
              by (rule finite_lifted_diagnosis[where D=D]) (simp_all add: diag)
            then show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem])
          next
            case found
            obtain s \<theta>' where s: "s |\<in>| finite_kept q (resolution_found sub)"
              and sups: "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
                by (rule finite_commitment_exchanges_call[OF exchanges I sup gp True H unheld
                  found(1)[unfolded sub_def q_def] found(2)[unfolded q_def]])
                (simp_all add: sub_def q_def)
            have sf: "s |\<in>| resolution_found (finite_committed_search_by ?sel \<kappa> K P n (Some q) B st)"
              using s finite_kept_subset unfolding sub_def finite_committed_search_def by blast
            have Is: "resolution_invariant P d t s"
              using finite_committed_search_found[OF \<kappa> I sf] by blast
            have Hs: "resolution_registrations_held \<kappa> s" by (rule finite_committed_search_found_held[OF \<kappa> I H sf])
            have sups': "resolution_supported_at U F (finite_committed_barring B s) P s \<theta>'"
              by (rule resolution_supported_at_barred_mono[OF sups]) (auto simp: finite_committed_barring_def)
            have lifted: "finite_lifted_outcome U F P (?rec F (finite_committed_barring B s) s)"
              by (rule Suc.IH[OF Is Hs sups'])
            have mem: "?rec F (finite_committed_barring B s) s |\<in>|
                finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
                  (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                    (finite_kept q (resolution_found sub)))"
              by (rule finsertI2, rule fimageI[OF s])
            show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem lifted])
          qed
        next
          case uncommitted: False
          obtain st' \<theta>' where st': "st' |\<in>| finite_committed_successors K P F st g"
            and sup': "resolution_supported_at U F (finite_goal_barring K F B st g) P st' \<theta>'"
          proof (cases "\<exists>q r M Ws. g = Resolution_Material_Goal q r M \<and> finite_canonical_solutions M = Some Ws \<and>
              commit_material K F st g")
            case True
            then obtain q r M Ws where gm: "g = Resolution_Material_Goal q r M"
              and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material K F st g" by blast
            obtain st' \<theta>' where s: "st' |\<in>| finite_solution_successors st q r M Ws"
              and u: "resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
              by (rule finite_commitment_exchanges_material[OF exchanges I sup gp gm Ws cm])
            have eqS: "finite_committed_successors K P F st g = finite_solution_successors st q r M Ws"
              using gm Ws cm by (simp add: finite_committed_successors_def)
            have eqB: "finite_goal_barring K F B st g = finite_committed_barring B st"
              using gm Ws cm by (simp add: finite_goal_barring_def finite_material_committed_def)
            show thesis by (rule that[of st' \<theta>']) (simp_all only: eqS eqB s u)
          next
            case False
            have eqS: "finite_committed_successors K P F st g = finite_goal_successors P st g"
              using False by (auto simp: finite_committed_successors_def split: resolution_goal.splits option.splits)
            have eqB: "finite_goal_barring K F B st g = B"
              using False by (auto simp: finite_goal_barring_def finite_material_committed_def split: resolution_goal.splits)
            show thesis
            proof (rule resolution_goal_lifted_at[OF Ip sup foreign pending focus kind])
              fix st' \<theta>' assume s: "st' |\<in>| finite_goal_successors P st g"
                and u: "resolution_supported_at U F B P st' \<theta>'"
                and "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
              show thesis using that s u eqS eqB by simp
            qed
          qed
          have gs: "st' |\<in>| finite_goal_successors P st g" using st' finite_committed_successors_subset by blast
          have I': "resolution_invariant P d t st'" by (rule resolution_goal_step[OF I pending gs])
          have H': "resolution_registrations_held \<kappa> st'"
            by (rule resolution_registrations_goal_step[OF distinct H pending unheld gs])
          have lifted: "finite_lifted_outcome U F P (?rec F (finite_goal_barring K F B st g) st')"
            by (rule Suc.IH[OF I' H' sup'])
          have ne: "finite_committed_successors K P F st g \<noteq> {||}" using st' by auto
          have Og: "Og = finite_outcome_union (fimage (?rec F (finite_goal_barring K F B st g))
              (finite_committed_successors K P F st g))"
            unfolding Og_def finite_committed_goal_outcome_def using unpruned barred uncommitted ne
            by (simp add: Let_def)
          have mem: "?rec F (finite_goal_barring K F B st g) st' |\<in>|
              fimage (?rec F (finite_goal_barring K F B st g)) (finite_committed_successors K P F st g)"
            by (rule fimageI[OF st'])
          show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem lifted])
        qed
      qed
      then show ?thesis unfolding eq by (rule finite_lifted_outcome_union[OF memg])
    qed
  qed
qed

text \<open>
  R4's lifting is the committed lifting's instance at no commitment, the empty focus and no barred node, where the
  selection never constructs.
\<close>

corollary finite_resolution_lifting_committed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
    and I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and sup: "resolution_supported P st \<theta>"
  shows "resolution_found (finite_resolution_search \<kappa> P n st) \<noteq> {||} \<or>
    resolution_diagnoses (finite_resolution_search \<kappa> P n st) \<noteq> {||}"
proof -
  have "finite_lifted_outcome (\<lambda>_. False) None P (finite_committed_search \<kappa> no_commitment P n None {||} st)"
    by (rule finite_committed_lifting[OF \<kappa> resolution_no_foreign finite_commitment_exchanges_none
      finite_construction_lifts_free[OF free] I H sup[unfolded resolution_supported_none resolution_supported_by_at]])
  then show ?thesis unfolding finite_committed_search_plain[OF free] finite_lifted_outcome_def by auto
qed

section \<open>The three forms are exact\<close>

text \<open>
  A result refutes a call when it is a refutation, or when no branch succeeded and every diagnosis is a witnessed
  failure: under the two premises the supported branch of a true call ends neither way. A result resolved holds;
  any other result asserts nothing.
\<close>

definition finite_resolution_refutes :: "('a,'s,'d,'c) finite_resolution_result \<Rightarrow> bool" where
  "finite_resolution_refutes r \<longleftrightarrow> r = Finite_Refuted \<or>
    (\<exists>D. r = Finite_Unresolved D \<and> (\<forall>E. E |\<in>| D \<longrightarrow> finite_witnessed_diagnosis E))"

theorem finite_committed_resolution_refutation_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and exchanges: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and refutes: "finite_resolution_refutes (finite_committed_resolution \<kappa> K P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
proof
  assume holds: "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  have Pf: "finite_system_formed P"
    using positive_meaning_has_formed_system[OF holds] by (simp add: finite_system_formed_correct)
  have tf: "finite_term_formed t"
    using positive_meaning_formed[OF holds]
    by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
  let ?R = "finite_committed_search \<kappa> K P n None {||} (finite_initial_state d t)"
  let ?C = "ffUnion (fimage finite_state_proofs (resolution_found ?R))"
  have I0: "resolution_invariant P d t (finite_initial_state d t)" by (rule resolution_initial_invariant[OF Pf tf])
  have S0: "resolution_supported_at (\<lambda>_. False) None {||} P (finite_initial_state d t) (\<lambda>_. Finite_Payload [])"
    using holds by (simp add: resolution_supported_at_def finite_initial_state_def resolution_value_ground)
  have lifted: "finite_lifted_outcome (\<lambda>_. False) None P ?R"
    by (rule finite_committed_lifting[OF \<kappa> resolution_no_foreign exchanges constructions I0
      resolution_registrations_initial S0])
  have res: "finite_committed_resolution \<kappa> K P d t n = (if ?C\<noteq>{||} then Finite_Resolved ?C
      else if resolution_diagnoses ?R={||} then Finite_Refuted else Finite_Unresolved (resolution_diagnoses ?R))"
    using finite_committed_resolution_certificates[OF Pf tf \<kappa>, of K d n] by (simp add: Let_def)
  from lifted show False unfolding finite_lifted_outcome_def
  proof (elim disjE exE conjE)
    fix st' B' \<theta>' assume st': "st' |\<in>| resolution_found ?R"
    have "resolution_invariant P d t st' \<and> finite_focus_pending None st' = {||}"
      using finite_committed_search_found[OF \<kappa> I0, of st' K n None "{||}"] st'
      by (simp add: finite_committed_search_def)
    then obtain nd where nd: "nd |\<in>| resolution_nodes st'" "resolution_node_position nd = []"
      by (auto simp: resolution_invariant_def resolution_root_held_def)
    then have "finite_node_proof (fcard (resolution_nodes st')) (resolution_nodes st') nd |\<in>| finite_state_proofs st'"
      by (auto simp: finite_state_proofs_def)
    then have "?C \<noteq> {||}" using resolution_union_nonempty[of st' "resolution_found ?R" finite_state_proofs] st' by auto
    then show False using res refutes by (simp add: finite_resolution_refutes_def)
  next
    fix D assume d: "D |\<in>| resolution_diagnoses ?R" and w: "\<not> finite_witnessed_diagnosis D"
    show False using res refutes d w by (auto simp: finite_resolution_refutes_def split: if_splits)
  qed
qed

lemmas finite_committed_resolution_exact =
  finite_committed_resolution_sound(2) finite_committed_resolution_refutation_exact

lemma finite_committed_verdict_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and exchanges: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and verdict: "finite_resolution_verdict (finite_committed_resolution \<kappa> K P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof (cases "finite_committed_resolution \<kappa> K P d t n")
  case (Finite_Resolved C)
  then show ?thesis using verdict finite_committed_resolution_sound(2)[OF Finite_Resolved]
    by (simp add: finite_resolution_verdict_def)
next
  case Finite_Refuted
  have r: "finite_resolution_refutes (finite_committed_resolution \<kappa> K P d t n)"
    using Finite_Refuted by (simp add: finite_resolution_refutes_def)
  have "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
    by (rule finite_committed_resolution_refutation_exact[OF \<kappa> exchanges constructions r])
  then show ?thesis using verdict Finite_Refuted by (simp add: finite_resolution_verdict_def)
next
  case (Finite_Unresolved D)
  then show ?thesis using verdict by (simp add: finite_resolution_verdict_def)
qed

theorem finite_committed_demand_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and exchanges: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "finite_committed_demand \<kappa> K P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  let ?v = "\<lambda>q. finite_resolution_verdict (finite_committed_resolution \<kappa> K P (fst q) (snd q) n)"
  from result have Pf: "finite_system_formed P" and answered: "\<And>q. q |\<in>| D \<Longrightarrow> ?v q \<noteq> None"
    and A: "A = fimage fst (ffilter (\<lambda>(q,v). v = Some True) (fimage (\<lambda>q. (q,?v q)) D))"
    by (auto simp: finite_committed_demand_def Let_def split: if_splits)
  show "schema_system_formed (decode_finite_system P)" using Pf by (simp add: finite_system_formed_correct)
  have key: "\<And>q. q |\<in>| D \<Longrightarrow>
      ?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    fix q assume q: "q |\<in>| D"
    obtain b where b: "?v q = Some b" using answered[OF q] by auto
    have "b \<longleftrightarrow> (fst q,decode_finite_term (snd q)) \<in> positive_meaning (decode_finite_system P)"
      by (rule finite_committed_verdict_exact[OF \<kappa> exchanges constructions b])
    then show "?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
      using b by (simp add: decode_finite_call_term_fields)
  qed
  show "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    unfolding A fimage_fst_filter_graph ffilter.rep_eq Set.filter_eq
    by (rule Collect_cong) (simp add: key cong: conj_cong)
qed

theorem native_committed_resolution_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and exchanges: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "native_committed_resolution \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  from result have T: "T = fimage (\<lambda>q. (q,finite_committed_resolution \<kappa> K P (fst q) (snd q) n)) R"
    and A: "A = finite_committed_demand \<kappa> K P R n"
    by (simp_all add: native_committed_resolution_def)
  show "fimage fst T = R" by (rule native_committed_resolution_sound(1)[OF result])
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    by (rule native_committed_resolution_sound(2)[OF result])
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,r) |\<in>| T" and rr: "finite_resolution_refutes r"
    then have "r = finite_committed_resolution \<kappa> K P (fst q) (snd q) n" unfolding T by auto
    with rr have "finite_resolution_refutes (finite_committed_resolution \<kappa> K P (fst q) (snd q) n)" by simp
    then show "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
      using finite_committed_resolution_refutation_exact[OF \<kappa> exchanges constructions]
      by (simp add: decode_finite_call_term_fields)
  qed
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    using finite_committed_demand_exact[OF \<kappa> exchanges constructions] unfolding A by blast
qed

section \<open>Agreement with R4 at no declaration\<close>

text \<open>
  At no declaration the committed forms are R4's (@{text finite_declared_resolution_none}), and the premises of
  exactness hold at every construction whose selected constructions keep a support: R4's refutation exactness,
  stated at the empty construction, holds there.
\<close>

corollary finite_declared_none_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "finite_resolution_refutes (finite_program_resolution \<kappa> P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
    and "finite_program_resolution \<kappa> P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  using finite_committed_resolution_refutation_exact[OF \<kappa> finite_commitment_exchanges_none
      finite_construction_lifts_free[OF free], of d t n]
    finite_committed_resolution_sound(2)[of \<kappa> no_commitment P d t n C]
  by (simp_all add: finite_committed_resolution_plain[OF free])

section \<open>The transfer by agreement and by relocation\<close>

text \<open>
  Where the committed verdicts of two programs are both given, exactness makes each the call's positive meaning:
  two programs agreeing on a dependency-closed set holding the called definition give the same verdict, and so do
  a program and its relocation by a map injective on its definitions and the called one. Each consumes the
  program's own contract, the locality of positive meaning and the relocation of the consequence operator.
\<close>

corollary finite_committed_agreement_transfer:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'" and ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>' K' Q"
    and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> K P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' K' Q d t m) = Some b'"
  shows "b = b'"
  using finite_committed_verdict_exact[OF \<kappa> ex cl v] finite_committed_verdict_exact[OF \<kappa>' ex' cl' v']
    positive_meaning_dependency_locality[OF Pf Qf agree closed dV] by blast

corollary finite_committed_relocation_transfer:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
    and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>' K' (finite_rename_system g P)"
    and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' (finite_rename_system g P)"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> K P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' K' (finite_rename_system g P) (g d) t m) = Some b'"
  shows "b = b'"
proof -
  have ren: "decode_finite_system (finite_rename_system g P) = rename_system g (decode_finite_system P)"
    by (simp add: finite_rename_system_correct)
  have PM: "positive_meaning (rename_system g (decode_finite_system P)) =
      map_prod g id ` positive_meaning (decode_finite_system P)"
    by (rule renamed_system_positive_meaning[OF Pf inj_on_subset[OF injective subset_insertI]])
  have backward: "(d,x) \<in> positive_meaning (decode_finite_system P)"
    if "(g d,x) \<in> map_prod g id ` positive_meaning (decode_finite_system P)" for x
  proof -
    from that obtain d0 where d0: "(d0,x) \<in> positive_meaning (decode_finite_system P)" "g d0 = g d" by auto
    have "d0 \<in> system_definitions (decode_finite_system P)"
      using positive_meaning_formed[OF d0(1)] by (auto simp: schema_call_formed_def system_definitions_def rel_dom_def)
    then have "d0 = d" using inj_onD[OF injective d0(2)] by simp
    then show ?thesis using d0(1) by simp
  qed
  have fwd: "(g d,x) \<in> map_prod g id ` positive_meaning (decode_finite_system P)"
    if "(d,x) \<in> positive_meaning (decode_finite_system P)" for x
    using that by force
  have eq: "(g d,decode_finite_term t) \<in> positive_meaning (decode_finite_system (finite_rename_system g P)) \<longleftrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    unfolding ren PM by (rule iffI[OF backward fwd])
  show ?thesis
    using finite_committed_verdict_exact[OF \<kappa> ex cl v] finite_committed_verdict_exact[OF \<kappa>' ex' cl' v'] eq by blast
qed

section \<open>The committed sub-search's frame and its kept states\<close>

text \<open>
  A committed goal is solved by a sub-search focused at its position (task 589). Every binding such a search makes is
  of a variable of a goal under its focus, of a variable no node yet places, or of a construction's registered
  variable, bound to a ground value; goals and nodes outside the focus change by those bindings alone; every position a
  node holds keeps one, and a node the search adds stands where none stood. Each step of the search — resolution at a
  focused call (the most general unifier binds only variables of its equations, R2), a solution of a focused material
  premise, a construction at a node — is a substitution step of one shape (@{text finite_substitution_step}), and any
  relation a substitution step gives, reflexive, transitive and kept from a nested focus to an enclosing one, holds
  between a state and every found state of a search from it (@{text finite_committed_search_relation}): the nested
  commitments are the relation's weakening. A construction step reads every pending goal, the focus's and the rest,
  so a variable it binds may be held outside the focus, by goals holding it alone: the frame names those bindings.
\<close>

lemma resolution_goal_substitute_composes:
  "resolution_goal_substitute \<tau> (resolution_goal_substitute \<sigma> g) =
    resolution_goal_substitute (\<lambda>a. finite_pattern_substitute \<tau> (\<sigma> a)) g"
  by (cases g) (simp_all add: finite_pattern_substitute_composes finite_material_pattern_substitute_composes)

lemma resolution_node_substitute_composes:
  "resolution_node_substitute \<tau> (resolution_node_substitute \<sigma> nd) =
    resolution_node_substitute (\<lambda>a. finite_pattern_substitute \<tau> (\<sigma> a)) nd"
  by (cases nd) (simp add: finite_pattern_substitute_composes fset.map_comp comp_def split_def)

lemma resolution_goal_substitute_identity: "resolution_goal_substitute Finite_Variable g = g"
proof (cases g)
  case (Resolution_Material_Goal q r M)
  then show ?thesis by (cases M) (simp add: finite_material_pattern_substitute_def)
qed simp

lemma resolution_node_substitute_identity: "resolution_node_substitute Finite_Variable nd = nd"
proof (cases nd)
  case (Resolution_Node q d c S p B)
  have "fimage (\<lambda>(a,x). (a,finite_pattern_substitute Finite_Variable x)) B = B"
    by (auto simp: fset_eq_iff resolution_fset_simps image_iff)
  then show ?thesis using Resolution_Node by simp
qed

lemma finite_rename_apart_position:
  "z |\<in>| finite_pattern_variables (finite_rename_apart w p) \<Longrightarrow> fst z = w"
  by (auto simp: finite_rename_apart_variables)

lemma finite_rename_material_position:
  assumes "z |\<in>| finite_material_variables (finite_rename_material (Pair w) M)"
  shows "fst z = w"
  using finite_material_substitute_variable_origin[OF assms[unfolded finite_rename_material_as_substitute]] by auto

lemma finite_clause_goals_member:
  assumes "g |\<in>| finite_clause_goals q e c S"
  shows "\<exists>s. resolution_goal_position g = q @ [s]"
    "\<And>z. z |\<in>| resolution_goal_variables g \<Longrightarrow> fst z = (q,True)"
proof -
  have cases: "(\<exists>s e' p. (s,e',p) |\<in>| finite_schema_premises S \<and>
      g = Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_rename_apart (q,True) p)) \<or>
    (\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and>
      g = Resolution_Material_Goal (q@[s]) (e,c,s) (finite_rename_material (Pair (q,True)) M))"
    using assms unfolding finite_clause_goals_def by (auto simp: resolution_fset_simps)
  then show "\<exists>s. resolution_goal_position g = q @ [s]" by auto
  show "fst z = (q,True)" if "z |\<in>| resolution_goal_variables g" for z
    using cases that by (elim disjE exE conjE)
      (metis finite_rename_apart_position resolution_goal_variables.simps(1),
       metis finite_rename_material_position resolution_goal_variables.simps(2))
qed

lemma finite_outside_pending_substitute:
  "ffilter (\<lambda>g. \<not> resolution_focused F (resolution_goal_position g)) (fimage (resolution_goal_substitute \<sigma>) A) =
    fimage (resolution_goal_substitute \<sigma>) (ffilter (\<lambda>g. \<not> resolution_focused F (resolution_goal_position g)) A)"
  by (auto simp: fset_eq_iff resolution_fset_simps)

lemma finite_outside_nodes_substitute:
  "ffilter (\<lambda>nd. \<not> resolution_focused F (resolution_node_position nd)) (fimage (resolution_node_substitute \<sigma>) A) =
    fimage (resolution_node_substitute \<sigma>) (ffilter (\<lambda>nd. \<not> resolution_focused F (resolution_node_position nd)) A)"
  by (auto simp: fset_eq_iff resolution_fset_simps)

lemma finite_solution_successors_member:
  assumes "st' |\<in>| finite_solution_successors st q r M Ws"
  obtains W E u where "W |\<in>| Ws" "E |\<in>| finite_material_instance_pairs W M" "finite_unify_pairs E = Some u"
    "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
  using assms that unfolding finite_solution_successors_def
  by (auto simp: resolution_fset_simps split: option.splits)

lemma finite_material_instance_pairs_variables:
  assumes "E |\<in>| finite_material_instance_pairs W M"
  shows "finite_pairs_variables E \<subseteq> fset (finite_material_variables M)"
  using assms unfolding finite_material_instance_pairs_def
  by (auto simp: resolution_fset_simps finite_material_variables_def bot_fset.rep_eq)

lemma finite_committed_successors_material:
  assumes "st' |\<in>| finite_committed_successors K P F st (Resolution_Material_Goal q r M)"
  obtains Ws where "st' |\<in>| finite_solution_successors st q r M Ws"
  using assms that
  by (auto simp: finite_committed_successors_def finite_material_successors_solutions
    split: option.splits if_splits finite_material_outcome.splits)

lemma finite_resolution_select_construction:
  "finite_resolution_select \<kappa> P st = Select_Construction N \<Longrightarrow> N |\<subseteq>| resolution_nodes st"
  by (auto simp: finite_resolution_select_def finite_first_nodes_def Let_def resolution_fset_simps split: if_splits)

subsection \<open>A substitution step\<close>

definition finite_focus_variables ::
    "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('s,'a) resolution_variable set" where
  "finite_focus_variables q st = (\<Union>g\<in>fset (finite_focus_pending (Some q) st). fset (resolution_goal_variables g))"

definition finite_outside_pending ::
    "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_outside_pending q st =
    ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) (resolution_pending st)"

definition finite_outside_nodes ::
    "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_outside_nodes q st =
    ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) (resolution_nodes st)"

definition finite_registered_at ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('s,'a) resolution_variable \<Rightarrow> bool" where
  "finite_registered_at \<kappa> st z \<longleftrightarrow> (\<exists>nd. nd |\<in>| resolution_nodes st \<and>
    fst z = (resolution_node_position nd,True) \<and>
    snd z |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd))"

lemma finite_focus_variables_member:
  "z \<in> finite_focus_variables q st \<longleftrightarrow> (\<exists>g. g |\<in>| resolution_pending st \<and>
    resolution_focused (Some q) (resolution_goal_position g) \<and> z |\<in>| resolution_goal_variables g)"
  by (auto simp: finite_focus_variables_def finite_focus_pending_focused)

text \<open>
  The shape of a step: a substitution applied to a new goal family, node family and witness set. The substitution
  fixes every variable outside a set V of the step's own variables (those of the focused goal it solves and the fresh
  variables of the clause it applies), or binds a construction's registered variable to a ground value; V's variables
  map to patterns over V. The goals outside the focus are the old ones; a new goal stands under the focus and holds
  only fresh variables, placed by a new node; a goal removed is not a call or leaves a node at its position; the old
  nodes stay and a new node stands where none stood, its call over fresh variables.
\<close>

definition finite_substitution_step ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_substitution_step \<kappa> q st st' \<longleftrightarrow> (\<exists>\<sigma> G N W V.
    st' = resolution_state_substitute \<sigma> (Resolution_State G N W) \<and>
    V \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z} \<and>
    (\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))) \<and>
    (\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V) \<and>
    (\<forall>z. z \<in> V \<longrightarrow> (\<exists>g. g |\<in>| resolution_pending st \<and> z |\<in>| resolution_goal_variables g) \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))) \<and>
    ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G = finite_outside_pending q st \<and>
    (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))))) \<and>
    (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> h |\<in>| G \<or> \<not> resolution_is_call h \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = resolution_goal_position h)) \<and>
    ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) N = finite_outside_nodes q st \<and>
    resolution_nodes st |\<subseteq>| N \<and>
    (\<forall>nd. nd |\<in>| N \<longrightarrow> nd |\<in>| resolution_nodes st \<or>
      ((\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd) \<and>
       (\<forall>z. z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst z))))))"

lemma finite_call_substitution_step:
  assumes I: "resolution_invariant P d t st"
    and g: "Resolution_Call_Goal q' r e p |\<in>| resolution_pending st" and focus: "resolution_focused (Some q) q'"
    and s: "st' |\<in>| finite_call_successors P st q' r e p"
  shows "finite_substitution_step \<kappa> q st st'"
proof -
  obtain i c S u where "(e,i) |\<in>| finite_system_interfaces P" "((e,c),S) |\<in>| finite_system_clauses P"
    and uni: "finite_unify_pairs [(finite_rename_apart (q',False) i,p),
      (finite_rename_apart (q',True) (finite_schema_conclusion S),p)] = Some u"
    and st0: "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q' e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q' r e p|}))
        (finsert (finite_clause_node q' e c S) (resolution_nodes st)) (resolution_witnesses st))"
    by (rule finite_call_successors_member[OF s])
  define E where "E = [(finite_rename_apart (q',False) i,p), (finite_rename_apart (q',True) (finite_schema_conclusion S),p)]"
  define \<sigma> where "\<sigma> = finite_binding_substitution u"
  define G where "G = finite_clause_goals q' e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q' r e p|})"
  define N where "N = finsert (finite_clause_node q' e c S) (resolution_nodes st)"
  define V where "V = finite_pairs_variables E"
  have uniE: "finite_unify_pairs E = Some u" using uni by (simp add: E_def)
  have st': "st' = resolution_state_substitute \<sigma> (Resolution_State G N (resolution_witnesses st))"
    by (simp add: st0 \<sigma>_def G_def N_def)
  have nonode: "resolution_node_position m \<noteq> q'" if "m |\<in>| resolution_nodes st" for m
    using I g that unfolding resolution_invariant_def resolution_positions_distinct_def by fastforce
  have fresh: "\<not> resolution_placed st z" if "fst (fst z) = q'" for z
    using nonode that unfolding resolution_placed_def by auto
  have node_at: "\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = q'"
    by (simp add: N_def finite_clause_node_def conj_disj_distribR ex_disj_distrib)
  have gfoc: "fset (finite_pattern_variables p) \<subseteq> finite_focus_variables q st"
    using g focus by (force simp: finite_focus_variables_member)
  have Vvars: "z \<in> fset (finite_pattern_variables p) \<or> fst (fst z) = q'" if "z \<in> V" for z
    using that unfolding V_def E_def by (auto simp: finite_rename_apart_variables)
  have Vsub: "V \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}" using Vvars gfoc fresh by blast
  have fixed: "\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    using finite_unify_pairs_outside[OF uniE] unfolding \<sigma>_def V_def by blast
  have range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V"
    using finite_unifier_variable[OF uniE] unfolding \<sigma>_def V_def by blast
  have origin: "\<forall>z. z \<in> V \<longrightarrow> (\<exists>g. g |\<in>| resolution_pending st \<and> z |\<in>| resolution_goal_variables g) \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))"
    using Vvars g node_at by fastforce
  have clause_goal: "resolution_focused (Some q) (resolution_goal_position g0) \<and>
      (\<forall>z. z |\<in>| resolution_goal_variables g0 \<longrightarrow> fst (fst z) = q')" if g0: "g0 |\<in>| finite_clause_goals q' e c S" for g0
  proof -
    obtain s0 where s0: "resolution_goal_position g0 = q' @ [s0]" using finite_clause_goals_member(1)[OF g0] by blast
    have "resolution_focused (Some q) (q' @ [s0])"
      using resolution_focused_within[of "Some q" q' "q' @ [s0]"] focus by simp
    then show ?thesis using s0 finite_clause_goals_member(2)[OF g0] by simp
  qed
  have gout: "ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G = finite_outside_pending q st"
    using clause_goal focus unfolding G_def finite_outside_pending_def by (auto simp: fset_eq_iff)
  have gin: "\<forall>g0. g0 |\<in>| G \<longrightarrow> g0 |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g0) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g0 \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))))"
    using clause_goal fresh node_at unfolding G_def by fastforce
  have removed: "\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> h |\<in>| G \<or> \<not> resolution_is_call h \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = resolution_goal_position h)"
    using node_at unfolding G_def by auto
  have nout: "ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) N = finite_outside_nodes q st"
    using focus unfolding N_def finite_outside_nodes_def by (auto simp: fset_eq_iff finite_clause_node_def)
  have nsub: "resolution_nodes st |\<subseteq>| N" by (auto simp: N_def)
  have nnew: "\<forall>nd. nd |\<in>| N \<longrightarrow> nd |\<in>| resolution_nodes st \<or>
      ((\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd) \<and>
       (\<forall>z. z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst z))))"
  proof (intro allI impI)
    fix nd assume "nd |\<in>| N"
    then consider "nd |\<in>| resolution_nodes st" | "nd = finite_clause_node q' e c S" by (auto simp: N_def)
    then show "nd |\<in>| resolution_nodes st \<or>
      ((\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd) \<and>
       (\<forall>z. z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst z))))"
    proof cases
      case 1
      then show ?thesis by blast
    next
      case 2
      have pos: "resolution_node_position nd = q'" by (simp add: 2 finite_clause_node_def)
      have vars: "fst (fst z) = q'" if "z |\<in>| finite_pattern_variables (resolution_node_call nd)" for z
        using that finite_rename_apart_position[of z "(q',True)"] by (simp add: 2 finite_clause_node_def)
      show ?thesis using nonode fresh node_at pos vars by (intro disjI2 conjI allI impI) auto
    qed
  qed
  show ?thesis unfolding finite_substitution_step_def
    by (rule exI[of _ \<sigma>], rule exI[of _ G], rule exI[of _ N], rule exI[of _ "resolution_witnesses st"], rule exI[of _ V])
      (use st' Vsub fixed range origin gout gin removed nout nsub nnew in blast)
qed

lemma finite_material_substitution_step:
  assumes g: "Resolution_Material_Goal q' r M |\<in>| resolution_pending st" and focus: "resolution_focused (Some q) q'"
    and s: "st' |\<in>| finite_solution_successors st q' r M Ws"
  shows "finite_substitution_step \<kappa> q st st'"
proof -
  obtain W0 E u where E: "E |\<in>| finite_material_instance_pairs W0 M" and uniE: "finite_unify_pairs E = Some u"
    and st0: "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q' r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
    by (rule finite_solution_successors_member[OF s])
  define \<sigma> where "\<sigma> = finite_binding_substitution u"
  define G where "G = resolution_pending st |-| {|Resolution_Material_Goal q' r M|}"
  define V where "V = finite_pairs_variables E"
  have st': "st' = resolution_state_substitute \<sigma> (Resolution_State G (resolution_nodes st) (resolution_witnesses st))"
    by (simp add: st0 \<sigma>_def G_def)
  have Vm: "V \<subseteq> fset (finite_material_variables M)"
    unfolding V_def by (rule finite_material_instance_pairs_variables[OF E])
  have mfoc: "fset (finite_material_variables M) \<subseteq> finite_focus_variables q st"
    using g focus by (force simp: finite_focus_variables_member)
  have Vsub: "V \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}" using Vm mfoc by blast
  have fixed: "\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    using finite_unify_pairs_outside[OF uniE] unfolding \<sigma>_def V_def by blast
  have range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V"
    using finite_unifier_variable[OF uniE] unfolding \<sigma>_def V_def by blast
  have origin: "\<forall>z. z \<in> V \<longrightarrow> (\<exists>g. g |\<in>| resolution_pending st \<and> z |\<in>| resolution_goal_variables g) \<or>
      (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = fst (fst z))"
    using Vm g by fastforce
  have gout: "ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G = finite_outside_pending q st"
    using focus unfolding G_def finite_outside_pending_def by (auto simp: fset_eq_iff)
  have gin: "\<forall>g0. g0 |\<in>| G \<longrightarrow> g0 |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g0) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g0 \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = fst (fst z))))"
    unfolding G_def by auto
  have removed: "\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> h |\<in>| G \<or> \<not> resolution_is_call h \<or>
      (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = resolution_goal_position h)"
    unfolding G_def by auto
  have nout: "ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) (resolution_nodes st) =
      finite_outside_nodes q st" by (simp add: finite_outside_nodes_def)
  show ?thesis unfolding finite_substitution_step_def
    by (rule exI[of _ \<sigma>], rule exI[of _ G], rule exI[of _ "resolution_nodes st"], rule exI[of _ "resolution_witnesses st"],
      rule exI[of _ V]) (use st' Vsub fixed range origin gout gin removed nout in \<open>intro conjI; fastforce\<close>)
qed

lemma finite_construction_substitution_step:
  assumes nd: "nd |\<in>| resolution_nodes st"
  shows "finite_substitution_step \<kappa> q st (finite_construction_step \<kappa> P st nd)"
proof -
  define \<sigma> where "\<sigma> = finite_construction_substitution \<kappa> P (resolution_pending st) nd"
  define W where "W = resolution_witnesses st |\<union>|
    ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
        Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||})
      (finite_constructed \<kappa> P (resolution_pending st) nd))"
  have st': "finite_construction_step \<kappa> P st nd =
      resolution_state_substitute \<sigma> (Resolution_State (resolution_pending st) (resolution_nodes st) W)"
    by (simp add: finite_construction_step_def \<sigma>_def W_def Let_def)
  have fixed: "\<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))" for z
  proof -
    obtain q0 b a where z: "z = ((q0,b),a)" by (cases z) auto
    show ?thesis
    proof (cases "b \<and> q0 = resolution_node_position nd \<and> a |\<in>| finite_constructed \<kappa> P (resolution_pending st) nd")
      case True
      then have b: "b" and q0: "q0 = resolution_node_position nd"
        and a: "a |\<in>| finite_constructed \<kappa> P (resolution_pending st) nd" by blast+
      have reg: "finite_registered_at \<kappa> st z"
        using a b nd unfolding z q0 finite_registered_at_def finite_constructed_def finite_free_registered_def
        by (auto simp: resolution_fset_simps)
      have zz: "z = ((resolution_node_position nd,True),a)" using z q0 b by simp
      have eq: "\<sigma> z = (case finite_registered_value \<kappa> P nd a of Some v \<Rightarrow> finite_exact_term_pattern v
          | None \<Rightarrow> Finite_Variable z)"
        using a unfolding zz by (simp add: \<sigma>_def finite_construction_substitution_def)
      show ?thesis using reg by (cases "finite_registered_value \<kappa> P nd a") (simp_all add: eq)
    next
      case False
      then show ?thesis unfolding z by (auto simp: \<sigma>_def finite_construction_substitution_def)
    qed
  qed
  have range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w {}"
  proof
    fix w
    from fixed[of w] show "fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w {}"
      by (auto simp: resolution_fset_simps bot_fset.rep_eq)
  qed
  have gout: "ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) (resolution_pending st) =
      finite_outside_pending q st" by (simp add: finite_outside_pending_def)
  have nout: "ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) (resolution_nodes st) =
      finite_outside_nodes q st" by (simp add: finite_outside_nodes_def)
  show ?thesis unfolding finite_substitution_step_def
    by (rule exI[of _ \<sigma>], rule exI[of _ "resolution_pending st"], rule exI[of _ "resolution_nodes st"], rule exI[of _ W],
      rule exI[of _ "{}"]) (use st' fixed range gout nout in \<open>intro conjI; fastforce\<close>)
qed

subsection \<open>The frame\<close>

definition finite_focus_frame ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_focus_frame \<kappa> q st st' \<longleftrightarrow>
    (\<exists>\<sigma>. (\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
        \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))) \<and>
      (\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq>
        insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})) \<and>
      finite_outside_pending q st' = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q st) \<and>
      finite_outside_nodes q st' = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q st)) \<and>
    finite_focus_variables q st' \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z} \<and>
    (\<forall>z. resolution_placed st z \<longrightarrow> resolution_placed st' z) \<and>
    (\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd))"

lemma finite_focus_frame_refl: "finite_focus_frame \<kappa> q st st"
proof -
  have gid: "resolution_goal_substitute Finite_Variable = id" by (rule ext) (simp add: resolution_goal_substitute_identity)
  have nid: "resolution_node_substitute Finite_Variable = id" by (rule ext) (simp add: resolution_node_substitute_identity)
  have "finite_outside_pending q st = fimage (resolution_goal_substitute Finite_Variable) (finite_outside_pending q st)"
    by (simp add: gid)
  moreover have "finite_outside_nodes q st = fimage (resolution_node_substitute Finite_Variable) (finite_outside_nodes q st)"
    by (simp add: nid)
  ultimately show ?thesis unfolding finite_focus_frame_def
    by (intro conjI exI[of _ Finite_Variable]) (auto simp: resolution_fset_simps bot_fset.rep_eq)
qed

lemma finite_substitution_step_frame:
  assumes step: "finite_substitution_step \<kappa> q st st'"
  shows "finite_focus_frame \<kappa> q st st'"
proof -
  obtain \<sigma> G N W V where st': "st' = resolution_state_substitute \<sigma> (Resolution_State G N W)"
    and Vsub: "V \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    and fixed: "\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    and range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V"
    and gout: "ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G = finite_outside_pending q st"
    and gin: "\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))))"
    and nout: "ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) N = finite_outside_nodes q st"
    and nsub: "resolution_nodes st |\<subseteq>| N"
    and nnew: "\<forall>nd. nd |\<in>| N \<longrightarrow> nd |\<in>| resolution_nodes st \<or>
      ((\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd) \<and>
       (\<forall>z. z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst z))))"
    using step unfolding finite_substitution_step_def by (elim exE conjE) (rule that; assumption)
  have pend: "resolution_pending st' = fimage (resolution_goal_substitute \<sigma>) G"
    and nods: "resolution_nodes st' = fimage (resolution_node_substitute \<sigma>) N" by (simp_all add: st')
  have A: "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
      \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    using Vsub fixed by blast
  have G: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq>
      insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" using range Vsub by blast
  have "finite_outside_pending q st' =
      fimage (resolution_goal_substitute \<sigma>) (ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G)"
    by (simp only: finite_outside_pending_def pend finite_outside_pending_substitute)
  then have B: "finite_outside_pending q st' = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q st)"
    by (simp only: gout)
  have "finite_outside_nodes q st' =
      fimage (resolution_node_substitute \<sigma>) (ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) N)"
    by (simp only: finite_outside_nodes_def nods finite_outside_nodes_substitute)
  then have C: "finite_outside_nodes q st' = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q st)"
    by (simp only: nout)
  have D: "finite_focus_variables q st' \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
  proof
    fix z assume "z \<in> finite_focus_variables q st'"
    then obtain g' where g': "g' |\<in>| resolution_pending st'" "resolution_focused (Some q) (resolution_goal_position g')"
      "z |\<in>| resolution_goal_variables g'" by (auto simp: finite_focus_variables_member)
    from g'(1) obtain g where g: "g |\<in>| G" "g' = resolution_goal_substitute \<sigma> g" by (auto simp: pend)
    from g'(3) g(2) obtain w where w: "w |\<in>| resolution_goal_variables g" "z \<in> fset (finite_pattern_variables (\<sigma> w))"
      using resolution_goal_substitute_variable_origin[of z \<sigma> g] by auto
    have fg: "resolution_focused (Some q) (resolution_goal_position g)" using g'(2) g(2) by simp
    have wv: "w \<in> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    proof (cases "g |\<in>| resolution_pending st")
      case True
      have "w \<in> finite_focus_variables q st" unfolding finite_focus_variables_member using True fg w(1) by blast
      then show ?thesis by blast
    next
      case False
      then have "\<forall>z. z |\<in>| resolution_goal_variables g \<longrightarrow> \<not> resolution_placed st z"
        using gin g(1) by blast
      then show ?thesis using w(1) by blast
    qed
    have "z \<in> insert w V" using range w(2) by blast
    then show "z \<in> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}" using wv Vsub by blast
  qed
  have E: "\<forall>z. resolution_placed st z \<longrightarrow> resolution_placed st' z"
  proof (intro allI impI)
    fix z assume "resolution_placed st z"
    then obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = fst (fst z)"
      unfolding resolution_placed_def by blast
    have "resolution_node_substitute \<sigma> m |\<in>| resolution_nodes st'" using m(1) nsub by (auto simp: nods)
    then show "resolution_placed st' z" using m(2) unfolding resolution_placed_def by force
  qed
  have F: "\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
  proof (intro allI impI)
    fix nd assume "nd |\<in>| resolution_nodes st'"
    then obtain m where m: "m |\<in>| N" "nd = resolution_node_substitute \<sigma> m" by (auto simp: nods)
    from nnew m(1) show "(\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
      using m(2) by auto
  qed
  show ?thesis unfolding finite_focus_frame_def
    by (intro conjI exI[of _ \<sigma>]) (fact A | fact G | fact B | fact C | fact D | fact E | fact F)+
qed

lemma finite_focus_frame_weaken:
  assumes frame: "finite_focus_frame \<kappa> q' st s" and within: "take (length q) q' = q"
  shows "finite_focus_frame \<kappa> q st s"
proof -
  have narrow: "resolution_focused (Some q) p" if "resolution_focused (Some q') p" for p
    using resolution_focused_within[of "Some q" q' p] within that by simp
  have FV: "finite_focus_variables q' x \<subseteq> finite_focus_variables q x" for x
  proof
    fix z assume "z \<in> finite_focus_variables q' x"
    then obtain g where g: "g |\<in>| resolution_pending x" "resolution_focused (Some q') (resolution_goal_position g)"
      "z |\<in>| resolution_goal_variables g" unfolding finite_focus_variables_member by blast
    have "resolution_focused (Some q) (resolution_goal_position g)" by (rule narrow[OF g(2)])
    then show "z \<in> finite_focus_variables q x" using g(1,3) unfolding finite_focus_variables_member by blast
  qed
  obtain \<sigma> where A: "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q' st \<longrightarrow>
        \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    and G: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq>
        insert w (finite_focus_variables q' st \<union> {z. \<not> resolution_placed st z})"
    and B: "finite_outside_pending q' s = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q' st)"
    and C: "finite_outside_nodes q' s = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q' st)"
    and D: "finite_focus_variables q' s \<subseteq> finite_focus_variables q' st \<union> {z. \<not> resolution_placed st z}"
    and E: "\<forall>z. resolution_placed st z \<longrightarrow> resolution_placed s z"
    and F: "\<forall>nd. nd |\<in>| resolution_nodes s \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
    using frame unfolding finite_focus_frame_def by (elim exE conjE) (rule that; assumption)
  have A': "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
        \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    using A FV by blast
  have G': "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq>
      insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" using G FV by blast
  have pout: "finite_outside_pending q x =
      ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) (finite_outside_pending q' x)" for x
    using narrow unfolding finite_outside_pending_def by (auto simp: fset_eq_iff)
  have nout: "finite_outside_nodes q x =
      ffilter (\<lambda>nd. \<not> resolution_focused (Some q) (resolution_node_position nd)) (finite_outside_nodes q' x)" for x
    using narrow unfolding finite_outside_nodes_def by (auto simp: fset_eq_iff)
  have B': "finite_outside_pending q s = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q st)"
    by (simp only: pout[of s] pout[of st] B finite_outside_pending_substitute)
  have C': "finite_outside_nodes q s = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q st)"
    by (simp only: nout[of s] nout[of st] C finite_outside_nodes_substitute)
  have D': "finite_focus_variables q s \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
  proof
    fix z assume "z \<in> finite_focus_variables q s"
    then obtain g where g: "g |\<in>| resolution_pending s" "resolution_focused (Some q) (resolution_goal_position g)"
      "z |\<in>| resolution_goal_variables g" by (auto simp: finite_focus_variables_member)
    show "z \<in> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    proof (cases "resolution_focused (Some q') (resolution_goal_position g)")
      case True
      then have "z \<in> finite_focus_variables q' s" using g by (auto simp: finite_focus_variables_member)
      then show ?thesis using D FV by blast
    next
      case False
      then have "g |\<in>| finite_outside_pending q' s" using g(1) by (simp add: finite_outside_pending_def)
      then obtain g0 where g0: "g0 |\<in>| finite_outside_pending q' st" "g = resolution_goal_substitute \<sigma> g0"
        by (auto simp: B)
      from g(3) g0(2) obtain w where w: "w |\<in>| resolution_goal_variables g0" "z \<in> fset (finite_pattern_variables (\<sigma> w))"
        using resolution_goal_substitute_variable_origin[of z \<sigma> g0] by auto
      have "w \<in> finite_focus_variables q st"
        using g0 g(2) w(1) by (auto simp: finite_outside_pending_def finite_focus_variables_member)
      moreover have "z \<in> insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" using G' w(2) by blast
      ultimately show ?thesis by blast
    qed
  qed
  show ?thesis unfolding finite_focus_frame_def
    by (intro conjI exI[of _ \<sigma>]) (fact A' | fact G' | fact B' | fact C' | fact D' | fact E | fact F)+
qed

lemma finite_focus_frame_trans:
  assumes first: "finite_focus_frame \<kappa> q st s1" and second: "finite_focus_frame \<kappa> q s1 s2"
  shows "finite_focus_frame \<kappa> q st s2"
proof -
  obtain \<sigma>1 where A1: "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
        \<sigma>1 z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma>1 z = finite_exact_term_pattern v))"
    and G1: "\<forall>w. fset (finite_pattern_variables (\<sigma>1 w)) \<subseteq>
        insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})"
    and B1: "finite_outside_pending q s1 = fimage (resolution_goal_substitute \<sigma>1) (finite_outside_pending q st)"
    and C1: "finite_outside_nodes q s1 = fimage (resolution_node_substitute \<sigma>1) (finite_outside_nodes q st)"
    and D1: "finite_focus_variables q s1 \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    and E1: "\<forall>z. resolution_placed st z \<longrightarrow> resolution_placed s1 z"
    and F1: "\<forall>nd. nd |\<in>| resolution_nodes s1 \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
    using first unfolding finite_focus_frame_def by (elim exE conjE) (rule that; assumption)
  obtain \<sigma>2 where A2: "\<forall>z. resolution_placed s1 z \<longrightarrow> z \<notin> finite_focus_variables q s1 \<longrightarrow>
        \<sigma>2 z = Finite_Variable z \<or> (finite_registered_at \<kappa> s1 z \<and> (\<exists>v. \<sigma>2 z = finite_exact_term_pattern v))"
    and G2: "\<forall>w. fset (finite_pattern_variables (\<sigma>2 w)) \<subseteq>
        insert w (finite_focus_variables q s1 \<union> {z. \<not> resolution_placed s1 z})"
    and B2: "finite_outside_pending q s2 = fimage (resolution_goal_substitute \<sigma>2) (finite_outside_pending q s1)"
    and C2: "finite_outside_nodes q s2 = fimage (resolution_node_substitute \<sigma>2) (finite_outside_nodes q s1)"
    and D2: "finite_focus_variables q s2 \<subseteq> finite_focus_variables q s1 \<union> {z. \<not> resolution_placed s1 z}"
    and E2: "\<forall>z. resolution_placed s1 z \<longrightarrow> resolution_placed s2 z"
    and F2: "\<forall>nd. nd |\<in>| resolution_nodes s2 \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes s1 \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes s1 \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
    using second unfolding finite_focus_frame_def by (elim exE conjE) (rule that; assumption)
  define \<sigma> where "\<sigma> = (\<lambda>a. finite_pattern_substitute \<sigma>2 (\<sigma>1 a))"
  have np: "{z. \<not> resolution_placed s1 z} \<subseteq> {z. \<not> resolution_placed st z}" using E1 by blast
  have reg: "finite_registered_at \<kappa> st z" if r: "finite_registered_at \<kappa> s1 z" and p: "resolution_placed st z" for z
  proof -
    from r obtain nd where nd: "nd |\<in>| resolution_nodes s1" "fst z = (resolution_node_position nd,True)"
      "snd z |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
      unfolding finite_registered_at_def by blast
    from p obtain m0 where m0: "m0 |\<in>| resolution_nodes st" "resolution_node_position m0 = fst (fst z)"
      unfolding resolution_placed_def by blast
    have "(\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
      using F1 nd(1) by blast
    then show ?thesis
    proof
      assume "\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd"
      then show ?thesis using nd unfolding finite_registered_at_def by metis
    next
      assume "\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd"
      then show ?thesis using m0 nd(2) by auto
    qed
  qed
  have A: "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
      \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
  proof (intro allI impI)
    fix z assume p: "resolution_placed st z" and n: "z \<notin> finite_focus_variables q st"
    from A1 p n have "\<sigma>1 z = Finite_Variable z \<or>
        (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma>1 z = finite_exact_term_pattern v))" by blast
    then show "\<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    proof
      assume v1: "\<sigma>1 z = Finite_Variable z"
      have p1: "resolution_placed s1 z" using E1 p by blast
      have n1: "z \<notin> finite_focus_variables q s1" using D1 n p by blast
      from A2 p1 n1 have "\<sigma>2 z = Finite_Variable z \<or>
          (finite_registered_at \<kappa> s1 z \<and> (\<exists>v. \<sigma>2 z = finite_exact_term_pattern v))" by blast
      then show ?thesis using reg[OF _ p] by (auto simp: \<sigma>_def v1)
    next
      assume r: "finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma>1 z = finite_exact_term_pattern v)"
      then obtain v where "\<sigma>1 z = finite_exact_term_pattern v" by blast
      then have "\<sigma> z = finite_exact_term_pattern v" by (simp add: \<sigma>_def finite_pattern_substitute_ground)
      with r show ?thesis by blast
    qed
  qed
  have G: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq>
      insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})"
  proof (intro allI subsetI)
    fix w z assume "z \<in> fset (finite_pattern_variables (\<sigma> w))"
    then obtain u where u: "u \<in> fset (finite_pattern_variables (\<sigma>1 w))" and z: "z \<in> fset (finite_pattern_variables (\<sigma>2 u))"
      using finite_substitute_variable_origin[of z \<sigma>2 "\<sigma>1 w"] unfolding \<sigma>_def by blast
    have "z \<in> insert u (finite_focus_variables q s1 \<union> {z. \<not> resolution_placed s1 z})" using G2 z by blast
    then have zu: "z \<in> insert u (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" using D1 np by blast
    have "u \<in> insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" using G1 u by blast
    with zu show "z \<in> insert w (finite_focus_variables q st \<union> {z. \<not> resolution_placed st z})" by blast
  qed
  have B: "finite_outside_pending q s2 = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q st)"
    by (simp add: B2 B1 fset.map_comp comp_def resolution_goal_substitute_composes \<sigma>_def)
  have C: "finite_outside_nodes q s2 = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q st)"
    by (simp add: C2 C1 fset.map_comp comp_def resolution_node_substitute_composes \<sigma>_def)
  have D: "finite_focus_variables q s2 \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    using D1 D2 np by blast
  have E: "\<forall>z. resolution_placed st z \<longrightarrow> resolution_placed s2 z" using E1 E2 by blast
  have F: "\<forall>nd. nd |\<in>| resolution_nodes s2 \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
  proof (intro allI impI)
    fix nd assume nd: "nd |\<in>| resolution_nodes s2"
    have none: "\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd"
      if absent: "\<forall>m. m |\<in>| resolution_nodes s1 \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd"
    proof (intro allI impI)
      fix m assume m: "m |\<in>| resolution_nodes st"
      have "resolution_placed st ((resolution_node_position m,True),undefined)"
        using m unfolding resolution_placed_def by auto
      then have "resolution_placed s1 ((resolution_node_position m,True),undefined)" using E1 by blast
      then show "resolution_node_position m \<noteq> resolution_node_position nd"
        using absent unfolding resolution_placed_def by auto
    qed
    have "(\<exists>m. m |\<in>| resolution_nodes s1 \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes s1 \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
      using F2 nd by blast
    then show "(\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd) \<or>
      (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd)"
    proof
      assume "\<exists>m. m |\<in>| resolution_nodes s1 \<and> resolution_node_position m = resolution_node_position nd \<and>
        resolution_node_site m = resolution_node_site nd \<and> resolution_node_schema m = resolution_node_schema nd"
      then obtain m1 where m1: "m1 |\<in>| resolution_nodes s1" "resolution_node_position m1 = resolution_node_position nd"
        "resolution_node_site m1 = resolution_node_site nd" "resolution_node_schema m1 = resolution_node_schema nd" by blast
      from F1 m1(1) show ?thesis using m1(2-4) by fastforce
    next
      assume "\<forall>m. m |\<in>| resolution_nodes s1 \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd"
      then show ?thesis using none by blast
    qed
  qed
  show ?thesis unfolding finite_focus_frame_def
    by (intro conjI exI[of _ \<sigma>]) (fact A | fact G | fact B | fact C | fact D | fact E | fact F)+
qed

subsection \<open>Every found state of a focused search keeps what a substitution step keeps\<close>

lemma finite_committed_search_relation:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and refl: "\<And>q st. R q st st"
    and trans: "\<And>q st s1 s2. R q st s1 \<Longrightarrow> R q s1 s2 \<Longrightarrow> R q st s2"
    and weaken: "\<And>q q' st s. R q' st s \<Longrightarrow> take (length q) q' = q \<Longrightarrow> R q st s"
    and step: "\<And>q st st'. resolution_invariant P d t st \<Longrightarrow> finite_substitution_step \<kappa> q st st' \<Longrightarrow> R q st st'"
  shows "resolution_invariant P d t st \<Longrightarrow>
    s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st) \<Longrightarrow>
    R q st s'"
proof (induction n arbitrary: q B st s')
  case 0
  then show ?case using refl by (auto simp: resolution_fset_simps split: if_splits)
next
  case (Suc n)
  let ?rec = "finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n"
  show ?case
  proof (cases "finite_focus_pending (Some q) st={||}")
    case True
    with Suc.prems show ?thesis using refl by (simp add: resolution_fset_simps)
  next
    case False
    show ?thesis
    proof (cases "finite_resolution_select \<kappa> P (finite_focused (Some q) st)")
      case (Select_Construction N)
      with Suc.prems False obtain nd where nd: "nd |\<in>| N"
        and found: "s' |\<in>| resolution_found (?rec (Some q) (finite_committed_barring B st)
          (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps Let_def split: if_splits)
      have ndst: "nd |\<in>| resolution_nodes st"
        using finite_resolution_select_construction[OF Select_Construction] nd by (auto simp: finite_focused_def)
      have I': "resolution_invariant P d t (finite_construction_step \<kappa> P st nd)"
        by (rule resolution_construction_step[OF Suc.prems(1) \<kappa>])
      have "R q st (finite_construction_step \<kappa> P st nd)"
        by (rule step[OF Suc.prems(1) finite_construction_substitution_step[OF ndst]])
      moreover have "R q (finite_construction_step \<kappa> P st nd) s'" by (rule Suc.IH[OF I' found])
      ultimately show ?thesis by (rule trans)
    next
      case (Select_Goals G)
      with Suc.prems False obtain g where g: "g |\<in>| G"
        and found: "s' |\<in>| resolution_found (finite_committed_goal_outcome ?rec K P (Some q) B st g)"
        by (auto simp: resolution_fset_simps)
      have gf: "g |\<in>| finite_focus_pending (Some q) st"
        using finite_resolution_select_goals[OF Select_Goals] g by (auto simp: finite_focused_def)
      then have pending: "g |\<in>| resolution_pending st" and focus: "resolution_focused (Some q) (resolution_goal_position g)"
        by (simp_all add: finite_focus_pending_focused)
      show ?thesis
      proof (cases "finite_goal_committed K (Some q) st g")
        case True
        from found True obtain s where
          s: "s |\<in>| resolution_found (?rec (Some (resolution_goal_position g)) B st)"
          and s': "s' |\<in>| resolution_found (?rec (Some q) (finite_committed_barring B s) s)"
          using finite_kept_subset
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have "R (resolution_goal_position g) st s" by (rule Suc.IH[OF Suc.prems(1) s])
        then have first: "R q st s" by (rule weaken) (use focus in simp)
        have Is: "resolution_invariant P d t s"
          using finite_committed_search_found[OF \<kappa> Suc.prems(1) s] by blast
        have "R q s s'" by (rule Suc.IH[OF Is s'])
        with first show ?thesis by (rule trans)
      next
        case False
        from found False obtain s1 where s1: "s1 |\<in>| finite_committed_successors K P (Some q) st g"
          and s': "s' |\<in>| resolution_found (?rec (Some q) (finite_goal_barring K (Some q) B st g) s1)"
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have gs: "s1 |\<in>| finite_goal_successors P st g" using s1 finite_committed_successors_subset by blast
        have I1: "resolution_invariant P d t s1" by (rule resolution_goal_step[OF Suc.prems(1) pending gs])
        have "finite_substitution_step \<kappa> q st s1"
        proof (cases g)
          case (Resolution_Call_Goal q' r e p)
          have cs: "s1 |\<in>| finite_call_successors P st q' r e p" using gs by (simp add: Resolution_Call_Goal)
          have fq: "resolution_focused (Some q) q'" using focus Resolution_Call_Goal by simp
          show ?thesis
            by (rule finite_call_substitution_step[OF Suc.prems(1) pending[unfolded Resolution_Call_Goal] fq cs])
        next
          case (Resolution_Material_Goal q' r M)
          obtain Ws where sol: "s1 |\<in>| finite_solution_successors st q' r M Ws"
            by (rule finite_committed_successors_material[OF s1[unfolded Resolution_Material_Goal]])
          have fq: "resolution_focused (Some q) q'" using focus Resolution_Material_Goal by simp
          show ?thesis
            by (rule finite_material_substitution_step[OF pending[unfolded Resolution_Material_Goal] fq sol])
        qed
        then have "R q st s1" by (rule step[OF Suc.prems(1)])
        moreover have "R q s1 s'" by (rule Suc.IH[OF I1 s'])
        ultimately show ?thesis by (rule trans)
      qed
    next
      case Select_None
      with Suc.prems False show ?thesis by (simp add: resolution_fset_simps)
    qed
  qed
qed

subsection \<open>A committed sub-search binds no registered variable held outside its focus\<close>

text \<open>
  The course of q113 for #593's hypothesis (b), which is not a fact of the states the search reaches (a registered
  premise-only variable held by an unselected sibling while a producer commits, the least-witness pattern itself).
  What holds: a committed sub-search at a position constructs only at nodes under it, where every goal holding the
  constructed variable stands (@{text resolution_registrations_held_focused}), and its goal steps bind only variables
  of the focus's goals and variables no node places. So a variable a node already places and no focused goal holds
  keeps every holder outside the focus and gains none (@{text finite_focus_confined}); at a commitment the search
  makes, a registered variable of a node present that a goal outside the focus holds is such a variable, the committed
  call being unheld and alone under its position (@{text finite_call_goal_alone_under}), and no node standing under it
  (@{text finite_call_goal_no_node_under}).
\<close>

definition finite_focus_confined ::
    "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_focus_confined q st s' \<longleftrightarrow> (\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> finite_focus_variables q st \<longrightarrow>
    resolution_placed s' z \<and>
    (\<forall>h. h |\<in>| resolution_pending s' \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
      (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0)) \<and>
    (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h0) \<longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<longrightarrow>
      (\<exists>h. h |\<in>| resolution_pending s' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h)))"

lemma finite_focus_confined_refl: "finite_focus_confined q st st"
  unfolding finite_focus_confined_def by blast

lemma finite_focus_confined_unfocused:
  assumes R: "finite_focus_confined q st s'" and pl: "resolution_placed st z"
    and nf: "z \<notin> finite_focus_variables q st"
  shows "z \<notin> finite_focus_variables q s'"
proof
  assume "z \<in> finite_focus_variables q s'"
  then obtain h where h: "h |\<in>| resolution_pending s'" "resolution_focused (Some q) (resolution_goal_position h)"
    "z |\<in>| resolution_goal_variables h" by (auto simp: finite_focus_variables_member)
  obtain h0 where "h0 |\<in>| resolution_pending st" "resolution_goal_position h0 = resolution_goal_position h"
      "z |\<in>| resolution_goal_variables h0"
    using R pl nf h(1,3) unfolding finite_focus_confined_def by blast
  then show False using nf h(2) by (auto simp: finite_focus_variables_member)
qed

lemma finite_focus_confined_trans:
  assumes R1: "finite_focus_confined q st s1" and R2: "finite_focus_confined q s1 s2"
  shows "finite_focus_confined q st s2"
proof -
  have X: "resolution_placed s2 z \<and>
    (\<forall>h. h |\<in>| resolution_pending s2 \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
      (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0)) \<and>
    (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h0) \<longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<longrightarrow>
      (\<exists>h. h |\<in>| resolution_pending s2 \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h))"
    if pl: "resolution_placed st z" and nf: "z \<notin> finite_focus_variables q st" for z
  proof -
    have pl1: "resolution_placed s1 z" using R1 pl nf unfolding finite_focus_confined_def by blast
    have nf1: "z \<notin> finite_focus_variables q s1" by (rule finite_focus_confined_unfocused[OF R1 pl nf])
    have A: "resolution_placed s2 z" using R2 pl1 nf1 unfolding finite_focus_confined_def by blast
    have B: "\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0"
      if h: "h |\<in>| resolution_pending s2" "z |\<in>| resolution_goal_variables h" for h
    proof -
      obtain h1 where h1: "h1 |\<in>| resolution_pending s1" "resolution_goal_position h1 = resolution_goal_position h"
          "z |\<in>| resolution_goal_variables h1"
        using R2 pl1 nf1 h unfolding finite_focus_confined_def by blast
      obtain h0 where h0: "h0 |\<in>| resolution_pending st" "resolution_goal_position h0 = resolution_goal_position h1"
          "z |\<in>| resolution_goal_variables h0"
        using R1 pl nf h1(1,3) unfolding finite_focus_confined_def by blast
      show ?thesis using h0 h1(2) by auto
    qed
    have C: "\<exists>h. h |\<in>| resolution_pending s2 \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h"
      if h0: "h0 |\<in>| resolution_pending st" "\<not> resolution_focused (Some q) (resolution_goal_position h0)"
        "z |\<in>| resolution_goal_variables h0" for h0
    proof -
      obtain h1 where h1: "h1 |\<in>| resolution_pending s1" "resolution_goal_position h1 = resolution_goal_position h0"
          "z |\<in>| resolution_goal_variables h1"
        using R1 pl nf h0 unfolding finite_focus_confined_def by blast
      have out1: "\<not> resolution_focused (Some q) (resolution_goal_position h1)" using h0(2) h1(2) by simp
      obtain h where h: "h |\<in>| resolution_pending s2" "resolution_goal_position h = resolution_goal_position h1"
          "z |\<in>| resolution_goal_variables h"
        using R2 pl1 nf1 h1(1,3) out1 unfolding finite_focus_confined_def by blast
      show ?thesis using h h1(2) by auto
    qed
    show ?thesis using A B C by blast
  qed
  show ?thesis unfolding finite_focus_confined_def using X by blast
qed

lemma finite_focus_confined_weaken:
  assumes R: "finite_focus_confined q' st s" and prefix: "take (length q) q' = q"
  shows "finite_focus_confined q st s"
proof -
  have len: "length q \<le> length q'" using arg_cong[OF prefix, of length] by (simp add: min_def split: if_splits)
  have within: "take (length q) p = q" if "take (length q') p = q'" for p
  proof -
    have "take (length q) p = take (length q) (take (length q') p)" using len by (simp add: min_absorb1)
    also have "\<dots> = q" using that prefix by simp
    finally show ?thesis .
  qed
  have X: "resolution_placed s z \<and>
    (\<forall>h. h |\<in>| resolution_pending s \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
      (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0)) \<and>
    (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h0) \<longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<longrightarrow>
      (\<exists>h. h |\<in>| resolution_pending s \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h))"
    if pl: "resolution_placed st z" and nf: "z \<notin> finite_focus_variables q st" for z
  proof -
    have nf': "z \<notin> finite_focus_variables q' st"
      using nf within by (auto simp: finite_focus_variables_member)
    have R': "resolution_placed s z \<and>
      (\<forall>h. h |\<in>| resolution_pending s \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
        (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
          z |\<in>| resolution_goal_variables h0)) \<and>
      (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q') (resolution_goal_position h0) \<longrightarrow>
        z |\<in>| resolution_goal_variables h0 \<longrightarrow>
        (\<exists>h. h |\<in>| resolution_pending s \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
          z |\<in>| resolution_goal_variables h))"
      using R pl nf' unfolding finite_focus_confined_def by blast
    have out: "\<not> resolution_focused (Some q') p" if "\<not> resolution_focused (Some q) p" for p
      using that within by auto
    show ?thesis using R' out by blast
  qed
  show ?thesis unfolding finite_focus_confined_def using X by blast
qed

lemma finite_pattern_substitute_keeps:
  "z |\<in>| finite_pattern_variables p \<Longrightarrow> \<sigma> z = Finite_Variable z \<Longrightarrow>
    z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)"
  by (induction p) auto

lemma resolution_goal_substitute_keeps:
  assumes z: "z |\<in>| resolution_goal_variables g" and fixed: "\<sigma> z = Finite_Variable z"
  shows "z |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g)"
  using z fixed finite_pattern_substitute_keeps[of z _ \<sigma>]
  by (cases g) (auto simp: finite_material_variables_def)

text \<open>A step of the search's plain shape, whose substitution binds no registered variable, keeps the confinement.\<close>

lemma finite_plain_step_confined:
  assumes step: "finite_substitution_step no_witness_construction q st st'"
  shows "finite_focus_confined q st st'"
proof -
  obtain \<sigma> G N W V where st': "st' = resolution_state_substitute \<sigma> (Resolution_State G N W)"
    and Vsub: "V \<subseteq> finite_focus_variables q st \<union> {z. \<not> resolution_placed st z}"
    and fixed: "\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at no_witness_construction st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    and range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V"
    and gout: "ffilter (\<lambda>g. \<not> resolution_focused (Some q) (resolution_goal_position g)) G = finite_outside_pending q st"
    and gin: "\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))))"
    and nsub: "resolution_nodes st |\<subseteq>| N"
    using step unfolding finite_substitution_step_def by (elim exE conjE) (rule that; assumption)
  have none: "\<not> finite_registered_at no_witness_construction st z" for z
    by (simp add: finite_registered_at_def no_witness_construction_def)
  have fix0: "\<sigma> z = Finite_Variable z" if "z \<notin> V" for z
    using fixed that none by blast
  have X: "resolution_placed st' z \<and>
    (\<forall>h. h |\<in>| resolution_pending st' \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
      (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0)) \<and>
    (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h0) \<longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<longrightarrow>
      (\<exists>h. h |\<in>| resolution_pending st' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h))"
    if pl: "resolution_placed st z" and nf: "z \<notin> finite_focus_variables q st" for z
  proof -
    have zV: "z \<notin> V" using Vsub pl nf by blast
    have \<sigma>z: "\<sigma> z = Finite_Variable z" by (rule fix0[OF zV])
    have A: "resolution_placed st' z"
    proof -
      obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = fst (fst z)"
        using pl unfolding resolution_placed_def by blast
      have "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes st'" unfolding st' using nd(1) nsub by auto
      then show ?thesis using nd(2) unfolding resolution_placed_def by (metis resolution_node_substitute_fields(1))
    qed
    have B: "\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0"
      if h: "h |\<in>| resolution_pending st'" "z |\<in>| resolution_goal_variables h" for h
    proof -
      obtain g where g: "g |\<in>| G" "h = resolution_goal_substitute \<sigma> g" using h(1) unfolding st' by auto
      obtain y where y: "y |\<in>| resolution_goal_variables g" "z |\<in>| finite_pattern_variables (\<sigma> y)"
        using resolution_goal_substitute_variable_origin[OF h(2)[unfolded g(2)]] by blast
      have "z = y" using range y(2) zV by blast
      then have zg: "z |\<in>| resolution_goal_variables g" using y(1) by simp
      have "g |\<in>| resolution_pending st" using gin g(1) zg pl by blast
      then show ?thesis using zg g(2) by auto
    qed
    have C: "\<exists>h. h |\<in>| resolution_pending st' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h"
      if h0: "h0 |\<in>| resolution_pending st" "\<not> resolution_focused (Some q) (resolution_goal_position h0)"
        "z |\<in>| resolution_goal_variables h0" for h0
    proof -
      have "h0 |\<in>| finite_outside_pending q st" using h0(1,2) by (simp add: finite_outside_pending_def)
      then have "h0 |\<in>| G" unfolding gout[symmetric] by (auto simp: resolution_fset_simps)
      then have "resolution_goal_substitute \<sigma> h0 |\<in>| resolution_pending st'" unfolding st' by simp
      moreover have "z |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> h0)"
        by (rule resolution_goal_substitute_keeps[where \<sigma>=\<sigma>, OF h0(3) \<sigma>z])
      ultimately show ?thesis by (metis resolution_goal_substitute_fields(1))
    qed
    show ?thesis using A B C by blast
  qed
  show ?thesis unfolding finite_focus_confined_def using X by blast
qed

text \<open>A construction at a node in the focus keeps the confinement, under the holders invariant.\<close>

lemma finite_construction_step_confined:
  assumes I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and only: "\<And>e c S a. ((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> a |\<in>| witness_registered \<kappa> e S \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion S)"
    and nd: "nd |\<in>| resolution_nodes st" and focus: "resolution_focused (Some q) (resolution_node_position nd)"
  shows "finite_focus_confined q st (finite_construction_step \<kappa> P st nd)"
proof -
  let ?\<sigma> = "finite_construction_substitution \<kappa> P (resolution_pending st) nd"
  let ?st' = "finite_construction_step \<kappa> P st nd"
  define W where "W = resolution_witnesses st |\<union>|
      ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
          Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||})
        (finite_constructed \<kappa> P (resolution_pending st) nd))"
  have step: "?st' = resolution_state_substitute ?\<sigma> (Resolution_State (resolution_pending st) (resolution_nodes st) W)"
    by (simp add: finite_construction_step_def W_def Let_def)
  have clause: "((resolution_node_site nd,resolution_node_clause nd),resolution_node_schema nd) |\<in>| finite_system_clauses P"
    using I nd unfolding resolution_invariant_def resolution_nodes_placed_def resolution_node_linked_def by blast
  have exact_vars: "finite_pattern_variables (finite_exact_term_pattern v) = {||}" for v :: finite_factor_term
    by (induction v) auto
  have vars\<sigma>: "fset (finite_pattern_variables (?\<sigma> y)) \<subseteq> {y}" for y
    by (auto simp: finite_construction_substitution_def exact_vars split: prod.splits if_splits option.splits)
  have fixz: "?\<sigma> z = Finite_Variable z" if nf: "z \<notin> finite_focus_variables q st" for z
  proof (rule ccontr)
    assume ne: "?\<sigma> z \<noteq> Finite_Variable z"
    obtain q' b a where z: "z = ((q',b),a)" by (cases z) auto
    have c: "b \<and> q' = resolution_node_position nd \<and> a |\<in>| finite_constructed \<kappa> P (resolution_pending st) nd"
      using ne z by (auto simp: finite_construction_substitution_def split: if_splits option.splits)
    then have free: "a |\<in>| finite_free_registered \<kappa> nd" and ready: "finite_registration_ready (resolution_pending st) nd a"
      by (auto simp: finite_constructed_def resolution_fset_simps)
    obtain h where h: "h |\<in>| resolution_pending st" "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables h"
      using ready unfolding finite_registration_ready_def Let_def finite_goal_holders_def by (auto simp: resolution_fset_simps)
    have reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
      using free by (simp add: finite_free_registered_def resolution_fset_simps)
    have "resolution_focused (Some q) (resolution_goal_position h)"
      by (rule resolution_registrations_held_focused[OF H nd focus reg only[OF clause reg] h(1) h(2)])
    then have "z \<in> finite_focus_variables q st" using h z c by (auto simp: finite_focus_variables_member)
    with nf show False by blast
  qed
  have X: "resolution_placed ?st' z \<and>
    (\<forall>h. h |\<in>| resolution_pending ?st' \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
      (\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0)) \<and>
    (\<forall>h0. h0 |\<in>| resolution_pending st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h0) \<longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<longrightarrow>
      (\<exists>h. h |\<in>| resolution_pending ?st' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h))"
    if pl: "resolution_placed st z" and nf: "z \<notin> finite_focus_variables q st" for z
  proof -
    have \<sigma>z: "?\<sigma> z = Finite_Variable z" by (rule fixz[OF nf])
    have A: "resolution_placed ?st' z"
    proof -
      obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = fst (fst z)"
        using pl unfolding resolution_placed_def by blast
      have "resolution_node_substitute ?\<sigma> m |\<in>| resolution_nodes ?st'" unfolding step using m(1) by auto
      then show ?thesis using m(2) unfolding resolution_placed_def by (metis resolution_node_substitute_fields(1))
    qed
    have B: "\<exists>h0. h0 |\<in>| resolution_pending st \<and> resolution_goal_position h0 = resolution_goal_position h \<and>
        z |\<in>| resolution_goal_variables h0"
      if h: "h |\<in>| resolution_pending ?st'" "z |\<in>| resolution_goal_variables h" for h
    proof -
      obtain g where g: "g |\<in>| resolution_pending st" "h = resolution_goal_substitute ?\<sigma> g"
        using h(1) unfolding step by auto
      obtain y where y: "y |\<in>| resolution_goal_variables g" "z |\<in>| finite_pattern_variables (?\<sigma> y)"
        using resolution_goal_substitute_variable_origin[OF h(2)[unfolded g(2)]] by blast
      have "z = y" using vars\<sigma>[of y] y(2) by blast
      then show ?thesis using y(1) g by auto
    qed
    have C: "\<exists>h. h |\<in>| resolution_pending ?st' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
        z |\<in>| resolution_goal_variables h"
      if h0: "h0 |\<in>| resolution_pending st" "z |\<in>| resolution_goal_variables h0" for h0
    proof -
      have "resolution_goal_substitute ?\<sigma> h0 |\<in>| resolution_pending ?st'" unfolding step using h0(1) by simp
      moreover have "z |\<in>| resolution_goal_variables (resolution_goal_substitute ?\<sigma> h0)"
        by (rule resolution_goal_substitute_keeps[where \<sigma>="finite_construction_substitution \<kappa> P (resolution_pending st) nd",
          OF h0(2) \<sigma>z])
      ultimately show ?thesis by (metis resolution_goal_substitute_fields(1))
    qed
    show ?thesis using A B C by blast
  qed
  show ?thesis unfolding finite_focus_confined_def using X by blast
qed

text \<open>
  (b\<Zprime>): along the committed search, under the holders invariant and at a program whose registered variables are
  premise-only, every found state of a sub-search focused at a position keeps the confinement.
\<close>

theorem finite_committed_search_confined:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and only: "\<And>e c S a. ((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> a |\<in>| witness_registered \<kappa> e S \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion S)"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_registrations_held \<kappa> st \<Longrightarrow>
    s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st) \<Longrightarrow>
    finite_focus_confined q st s'"
proof (induction n arbitrary: q B st s')
  case 0
  then show ?case using finite_focus_confined_refl by (auto simp: resolution_fset_simps split: if_splits)
next
  case (Suc n)
  let ?rec = "finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n"
  have I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st" by (rule Suc.prems)+
  have distinct: "resolution_positions_distinct st" using I unfolding resolution_invariant_def by blast
  show ?case
  proof (cases "finite_focus_pending (Some q) st={||}")
    case True
    with Suc.prems show ?thesis using finite_focus_confined_refl by (simp add: resolution_fset_simps)
  next
    case False
    show ?thesis
    proof (cases "finite_resolution_select \<kappa> P (finite_focused (Some q) st)")
      case (Select_Construction N)
      with Suc.prems False obtain nd where nd: "nd |\<in>| N"
        and focus: "resolution_focused (Some q) (resolution_node_position nd)"
        and found: "s' |\<in>| resolution_found (?rec (Some q) (finite_committed_barring B st)
          (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps Let_def split: if_splits)
      have ndst: "nd |\<in>| resolution_nodes st"
        using finite_resolution_select_construction[OF Select_Construction] nd by (auto simp: finite_focused_def)
      have I': "resolution_invariant P d t (finite_construction_step \<kappa> P st nd)"
        by (rule resolution_construction_step[OF I \<kappa>])
      have H': "resolution_registrations_held \<kappa> (finite_construction_step \<kappa> P st nd)"
        by (rule resolution_registrations_construction_step[OF H])
      have "finite_focus_confined q st (finite_construction_step \<kappa> P st nd)"
        by (rule finite_construction_step_confined[OF I H only ndst focus])
      moreover have "finite_focus_confined q (finite_construction_step \<kappa> P st nd) s'" by (rule Suc.IH[OF I' H' found])
      ultimately show ?thesis by (rule finite_focus_confined_trans)
    next
      case (Select_Goals G)
      with Suc.prems False obtain g where g: "g |\<in>| G"
        and found: "s' |\<in>| resolution_found (finite_committed_goal_outcome ?rec K P (Some q) B st g)"
        by (auto simp: resolution_fset_simps)
      have gf: "g |\<in>| finite_focus_pending (Some q) st"
        using finite_resolution_select_goals[OF Select_Goals] g by (auto simp: finite_focused_def)
      then have pending: "g |\<in>| resolution_pending st" and focus: "resolution_focused (Some q) (resolution_goal_position g)"
        by (simp_all add: finite_focus_pending_focused)
      have unheld: "\<not> finite_held \<kappa> st g" by (rule finite_resolution_select_unheld[OF Select_Goals g])
      show ?thesis
      proof (cases "finite_goal_committed K (Some q) st g")
        case True
        from found True obtain s where
          s: "s |\<in>| resolution_found (?rec (Some (resolution_goal_position g)) B st)"
          and s': "s' |\<in>| resolution_found (?rec (Some q) (finite_committed_barring B s) s)"
          using finite_kept_subset
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have "finite_focus_confined (resolution_goal_position g) st s" by (rule Suc.IH[OF I H s])
        then have first: "finite_focus_confined q st s" by (rule finite_focus_confined_weaken) (use focus in simp)
        have Is: "resolution_invariant P d t s" using finite_committed_search_found[OF \<kappa> I s] by blast
        have Hs: "resolution_registrations_held \<kappa> s" by (rule finite_committed_search_found_held[OF \<kappa> I H s])
        have "finite_focus_confined q s s'" by (rule Suc.IH[OF Is Hs s'])
        with first show ?thesis by (rule finite_focus_confined_trans)
      next
        case False
        from found False obtain s1 where s1: "s1 |\<in>| finite_committed_successors K P (Some q) st g"
          and s': "s' |\<in>| resolution_found (?rec (Some q) (finite_goal_barring K (Some q) B st g) s1)"
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have gs: "s1 |\<in>| finite_goal_successors P st g" using s1 finite_committed_successors_subset by blast
        have I1: "resolution_invariant P d t s1" by (rule resolution_goal_step[OF I pending gs])
        have H1: "resolution_registrations_held \<kappa> s1"
          by (rule resolution_registrations_goal_step[OF distinct H pending unheld gs])
        have "finite_substitution_step no_witness_construction q st s1"
        proof (cases g)
          case (Resolution_Call_Goal q' r e p)
          have cs: "s1 |\<in>| finite_call_successors P st q' r e p" using gs by (simp add: Resolution_Call_Goal)
          have fq: "resolution_focused (Some q) q'" using focus Resolution_Call_Goal by simp
          show ?thesis by (rule finite_call_substitution_step[OF I pending[unfolded Resolution_Call_Goal] fq cs])
        next
          case (Resolution_Material_Goal q' r M)
          obtain Ws where sol: "s1 |\<in>| finite_solution_successors st q' r M Ws"
            by (rule finite_committed_successors_material[OF s1[unfolded Resolution_Material_Goal]])
          have fq: "resolution_focused (Some q) q'" using focus Resolution_Material_Goal by simp
          show ?thesis by (rule finite_material_substitution_step[OF pending[unfolded Resolution_Material_Goal] fq sol])
        qed
        then have "finite_focus_confined q st s1" by (rule finite_plain_step_confined)
        moreover have "finite_focus_confined q s1 s'" by (rule Suc.IH[OF I1 H1 s'])
        ultimately show ?thesis by (rule finite_focus_confined_trans)
      qed
    next
      case Select_None
      with Suc.prems False show ?thesis by (simp add: resolution_fset_simps)
    qed
  qed
qed

text \<open>
  At a commitment the search makes — a pending call, unheld — every registered variable of a node present that a goal
  outside the call's position holds stays held at that goal's position in every found state of the sub-search.
\<close>

corollary finite_committed_search_registered_unbound:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and only: "\<And>e c S a. ((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> a |\<in>| witness_registered \<kappa> e S \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion S)"
    and I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and g: "g |\<in>| resolution_pending st" "resolution_is_call g" and unheld: "\<not> finite_held \<kappa> st g"
    and found: "s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n
      (Some (resolution_goal_position g)) B st)"
    and h0: "h0 |\<in>| resolution_pending st" "\<not> resolution_focused (Some (resolution_goal_position g)) (resolution_goal_position h0)"
    and z: "z |\<in>| resolution_goal_variables h0" and reg: "finite_registered_at \<kappa> st z"
  shows "\<exists>h. h |\<in>| resolution_pending s' \<and> resolution_goal_position h = resolution_goal_position h0 \<and>
    z |\<in>| resolution_goal_variables h"
proof -
  let ?q = "resolution_goal_position g"
  obtain q0 r0 e0 p0 where gc: "g = Resolution_Call_Goal q0 r0 e0 p0" using g(2) by (cases g) auto
  obtain m a where m: "m |\<in>| resolution_nodes st" and za: "z = ((resolution_node_position m,True),a)"
    and reg': "a |\<in>| witness_registered \<kappa> (resolution_node_site m) (resolution_node_schema m)"
    using reg by (cases z) (auto simp: finite_registered_at_def)
  have pl: "resolution_placed st z" using m za unfolding resolution_placed_def by auto
  have clause: "((resolution_node_site m,resolution_node_clause m),resolution_node_schema m) |\<in>| finite_system_clauses P"
    using I m unfolding resolution_invariant_def resolution_nodes_placed_def resolution_node_linked_def by blast
  have nf: "z \<notin> finite_focus_variables ?q st"
  proof
    assume "z \<in> finite_focus_variables ?q st"
    then obtain g' where g': "g' |\<in>| resolution_pending st" "resolution_focused (Some ?q) (resolution_goal_position g')"
      "z |\<in>| resolution_goal_variables g'" by (auto simp: finite_focus_variables_member)
    have "g' = g" using finite_call_goal_alone_under[OF I g(1)[unfolded gc] g'(1)] g'(2) gc by simp
    then have zg: "z |\<in>| resolution_goal_variables g" using g'(3) by simp
    have held: "resolution_variable_held st m a"
      using resolution_registrations_heldD(2)[OF H m reg'] only[OF clause reg']
        resolution_state_variables_goal[OF g(1) zg[unfolded za]] by blast
    have "(a,Finite_Variable ((resolution_node_position m,True),a)) |\<in>| resolution_node_bindings m"
      by (rule resolution_variable_heldD(1)[OF held])
    then have "a |\<in>| finite_free_registered \<kappa> m" using reg' by (simp add: finite_free_registered_def resolution_fset_simps)
    then have "finite_held \<kappa> st g" using m zg za by (force simp: finite_held_def)
    with unheld show False by blast
  qed
  have "finite_focus_confined ?q st s'" by (rule finite_committed_search_confined[OF \<kappa> only I H found])
  then show ?thesis using pl nf h0 z unfolding finite_focus_confined_def by blast
qed

theorem finite_committed_search_frame:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and found: "s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st)"
  shows "finite_focus_frame \<kappa> q st s'"
proof (rule finite_committed_search_relation[where R="finite_focus_frame \<kappa>", OF \<kappa> _ _ _ _ I found])
  show "finite_focus_frame \<kappa> q st st" for q st by (rule finite_focus_frame_refl)
  show "finite_focus_frame \<kappa> q st s2" if "finite_focus_frame \<kappa> q st s1" "finite_focus_frame \<kappa> q s1 s2"
    for q st s1 s2 using that by (rule finite_focus_frame_trans)
  show "finite_focus_frame \<kappa> q st s" if "finite_focus_frame \<kappa> q' st s" "take (length q) q' = q" for q q' st s
    using that by (rule finite_focus_frame_weaken)
  show "finite_focus_frame \<kappa> q st st'" if "resolution_invariant P d t st" "finite_substitution_step \<kappa> q st st'"
    for q st st' using that(2) by (rule finite_substitution_step_frame)
qed

subsection \<open>Positions, placement and kept states\<close>

definition finite_positions_kept :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_positions_kept st st' \<longleftrightarrow> (\<forall>p.
    ((\<exists>h. h |\<in>| resolution_pending st \<and> resolution_is_call h \<and> resolution_goal_position h = p) \<or>
     (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = p)) \<longrightarrow>
    ((\<exists>h. h |\<in>| resolution_pending st' \<and> resolution_is_call h \<and> resolution_goal_position h = p) \<or>
     (\<exists>nd. nd |\<in>| resolution_nodes st' \<and> resolution_node_position nd = p)))"

lemma finite_substitution_step_positions:
  assumes step: "finite_substitution_step \<kappa> q st st'"
  shows "finite_positions_kept st st'"
proof -
  obtain \<sigma> G N W where st': "st' = resolution_state_substitute \<sigma> (Resolution_State G N W)"
    and removed: "\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> h |\<in>| G \<or> \<not> resolution_is_call h \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = resolution_goal_position h)"
    and nsub: "resolution_nodes st |\<subseteq>| N"
    using step unfolding finite_substitution_step_def by (elim exE conjE) (rule that; assumption)
  have goal: "resolution_goal_substitute \<sigma> h |\<in>| resolution_pending st'" if "h |\<in>| G" for h
    using that by (simp add: st')
  have node: "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes st'" if "nd |\<in>| N" for nd
    using that by (simp add: st')
  show ?thesis unfolding finite_positions_kept_def
  proof (intro allI impI)
    fix p assume "(\<exists>h. h |\<in>| resolution_pending st \<and> resolution_is_call h \<and> resolution_goal_position h = p) \<or>
      (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = p)"
    then show "(\<exists>h. h |\<in>| resolution_pending st' \<and> resolution_is_call h \<and> resolution_goal_position h = p) \<or>
      (\<exists>nd. nd |\<in>| resolution_nodes st' \<and> resolution_node_position nd = p)"
    proof (elim disjE exE conjE)
      fix h assume h: "h |\<in>| resolution_pending st" "resolution_is_call h" "resolution_goal_position h = p"
      from removed h(1) h(2) consider "h |\<in>| G" | "\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = resolution_goal_position h"
        by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using goal[OF 1] h by (intro disjI1 exI[of _ "resolution_goal_substitute \<sigma> h"]) simp
      next
        case 2
        then obtain nd where "nd |\<in>| N" "resolution_node_position nd = p" using h(3) by blast
        then show ?thesis using node by (intro disjI2 exI[of _ "resolution_node_substitute \<sigma> nd"]) simp
      qed
    next
      fix nd assume "nd |\<in>| resolution_nodes st" "resolution_node_position nd = p"
      then show ?thesis using node nsub by (intro disjI2 exI[of _ "resolution_node_substitute \<sigma> nd"]) auto
    qed
  qed
qed

theorem finite_committed_search_positions:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and found: "s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st)"
  shows "finite_positions_kept st s'"
proof (rule finite_committed_search_relation[where R="\<lambda>q. finite_positions_kept", OF \<kappa> _ _ _ _ I found])
  show "finite_positions_kept st st" for q st unfolding finite_positions_kept_def by blast
  show "finite_positions_kept st s2" if "finite_positions_kept st s1" "finite_positions_kept s1 s2" for q st s1 s2
    using that unfolding finite_positions_kept_def by blast
  show "finite_positions_kept st s" if "finite_positions_kept st s" "take (length q) q' = q" for q q' st s
    using that(1) .
  show "finite_positions_kept st st'" if "resolution_invariant P d t st" "finite_substitution_step \<kappa> q st st'"
    for q st st' using that(2) by (rule finite_substitution_step_positions)
qed

definition finite_state_placed ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_state_placed U st \<longleftrightarrow>
    (\<forall>g z. g |\<in>| resolution_pending st \<longrightarrow> z |\<in>| resolution_goal_variables g \<longrightarrow> resolution_placed st z \<or> U z) \<and>
    (\<forall>nd z. nd |\<in>| resolution_nodes st \<longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow>
      resolution_placed st z \<or> U z)"

lemma resolution_supported_at_placed:
  "resolution_supported_at U F B P st \<theta> \<Longrightarrow> finite_state_placed U st"
  by (simp add: resolution_supported_at_def finite_state_placed_def)

lemma finite_substitution_step_placed:
  assumes step: "finite_substitution_step \<kappa> q st st'" and placed: "finite_state_placed U st"
  shows "finite_state_placed U st'"
proof -
  obtain \<sigma> G N W V where st': "st' = resolution_state_substitute \<sigma> (Resolution_State G N W)"
    and fixed: "\<forall>z. z \<notin> V \<longrightarrow> \<sigma> z = Finite_Variable z \<or>
      (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
    and range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w V"
    and origin: "\<forall>z. z \<in> V \<longrightarrow> (\<exists>g. g |\<in>| resolution_pending st \<and> z |\<in>| resolution_goal_variables g) \<or>
      (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))"
    and gin: "\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<or>
      (resolution_focused (Some q) (resolution_goal_position g) \<and>
       (\<forall>z. z |\<in>| resolution_goal_variables g \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))))"
    and nsub: "resolution_nodes st |\<subseteq>| N"
    and nnew: "\<forall>nd. nd |\<in>| N \<longrightarrow> nd |\<in>| resolution_nodes st \<or>
      ((\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position m \<noteq> resolution_node_position nd) \<and>
       (\<forall>z. z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow> \<not> resolution_placed st z \<and>
         (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst z))))"
    using step unfolding finite_substitution_step_def by (elim exE conjE) (rule that; assumption)
  have placed': "resolution_placed st' z" if "\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z)" for z
  proof -
    from that obtain nd where nd: "nd |\<in>| N" "resolution_node_position nd = fst (fst z)" by blast
    have "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes st'" using nd(1) by (simp add: st')
    then show ?thesis using nd(2) unfolding resolution_placed_def by force
  qed
  have good: "resolution_placed st' z \<or> U z"
    if "resolution_placed st z \<or> U z \<or> (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))" for z
  proof -
    have "resolution_placed st z \<Longrightarrow> \<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z)"
      using nsub unfolding resolution_placed_def by blast
    then show ?thesis using that placed' by blast
  qed
  have pg: "resolution_placed st z \<or> U z" if "g |\<in>| resolution_pending st" "z |\<in>| resolution_goal_variables g" for g z
    using placed that unfolding finite_state_placed_def by blast
  have image: "resolution_placed st' z \<or> U z"
    if w: "resolution_placed st w \<or> U w \<or> (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst w))"
      and z: "z \<in> fset (finite_pattern_variables (\<sigma> w))" for w z
  proof (cases "w \<in> V")
    case True
    have "z \<in> insert w V" using range z by blast
    then show ?thesis
    proof
      assume "z = w" then show ?thesis using good w by blast
    next
      assume zV: "z \<in> V"
      then show ?thesis using origin pg good by blast
    qed
  next
    case False
    from fixed False have "\<sigma> w = Finite_Variable w \<or> (\<exists>v. \<sigma> w = finite_exact_term_pattern v)" by blast
    then have "z = w" using z by (auto simp: resolution_fset_simps bot_fset.rep_eq)
    then show ?thesis using good w by blast
  qed
  show ?thesis unfolding finite_state_placed_def
  proof (intro conjI allI impI)
    fix g' z assume g': "g' |\<in>| resolution_pending st'" and z: "z |\<in>| resolution_goal_variables g'"
    from g' obtain g where g: "g |\<in>| G" "g' = resolution_goal_substitute \<sigma> g" by (auto simp: st')
    from z g(2) obtain w where w: "w |\<in>| resolution_goal_variables g" "z \<in> fset (finite_pattern_variables (\<sigma> w))"
      using resolution_goal_substitute_variable_origin[of z \<sigma> g] by auto
    have "resolution_placed st w \<or> U w \<or> (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst w))"
      using gin g(1) w(1) pg by blast
    then show "resolution_placed st' z \<or> U z" using image w(2) by blast
  next
    fix nd' z assume nd': "nd' |\<in>| resolution_nodes st'"
      and z: "z |\<in>| finite_pattern_variables (resolution_node_call nd')"
    from nd' obtain nd where nd: "nd |\<in>| N" "nd' = resolution_node_substitute \<sigma> nd" by (auto simp: st')
    from z nd(2) obtain w where w: "w |\<in>| finite_pattern_variables (resolution_node_call nd)"
      "z \<in> fset (finite_pattern_variables (\<sigma> w))"
      using finite_substitute_variable_origin[of z \<sigma> "resolution_node_call nd"] by (auto simp: nd(2))
    have "resolution_placed st w \<or> U w \<or> (\<exists>m. m |\<in>| N \<and> resolution_node_position m = fst (fst w))"
      using nnew nd(1) w(1) placed unfolding finite_state_placed_def by blast
    then show "resolution_placed st' z \<or> U z" using image w(2) by blast
  qed
qed

theorem finite_committed_search_placed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and found: "s' |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st)"
    and placed: "finite_state_placed U st"
  shows "finite_state_placed U s'"
proof -
  have "finite_state_placed U st \<longrightarrow> finite_state_placed U s'"
  proof (rule finite_committed_search_relation[where R="\<lambda>q st s. finite_state_placed U st \<longrightarrow> finite_state_placed U s",
      OF \<kappa> _ _ _ _ I found])
    show "finite_state_placed U st \<longrightarrow> finite_state_placed U st" for q st by blast
    show "finite_state_placed U st \<longrightarrow> finite_state_placed U s2"
      if "finite_state_placed U st \<longrightarrow> finite_state_placed U s1" "finite_state_placed U s1 \<longrightarrow> finite_state_placed U s2"
      for q st s1 s2 using that by blast
    show "finite_state_placed U st \<longrightarrow> finite_state_placed U s"
      if "finite_state_placed U st \<longrightarrow> finite_state_placed U s" "take (length q) q' = q" for q q' st s using that(1) .
    show "finite_state_placed U st \<longrightarrow> finite_state_placed U st'"
      if "resolution_invariant P d t st" "finite_substitution_step \<kappa> q st st'" for q st st'
      using finite_substitution_step_placed[OF that(2)] by blast
  qed
  with placed show ?thesis by blast
qed

text \<open>
  A found state of a sub-search focused at a pending call holds a node at the call's position, so it has an answer
  there, and the states kept of a nonempty family with an answer are not empty.
\<close>

lemma finite_kept_nonempty:
  assumes s: "s |\<in>| S" and a: "finite_committed_answers q s \<noteq> {||}"
  shows "finite_kept q S \<noteq> {||}"
proof -
  let ?A = "ffUnion (fimage (finite_committed_answers q) S)"
  from a obtain x where x: "x |\<in>| finite_committed_answers q s" by auto
  have xA: "x \<in> fset ?A" using s x unfolding ffUnion.rep_eq fimage.rep_eq by blast
  define m where "m = Min (fset ?A)"
  have ne: "fset ?A \<noteq> {}" using xA by blast
  have mA: "m \<in> fset ?A" using ne unfolding m_def by (intro Min_in) simp_all
  have low: "m \<le> b" if "b \<in> fset ?A" for b using that unfolding m_def by (intro Min_le) simp_all
  from mA obtain s0 where s0: "s0 |\<in>| S" "m |\<in>| finite_committed_answers q s0"
    unfolding ffUnion.rep_eq fimage.rep_eq by blast
  have "s0 |\<in>| finite_kept q S"
    unfolding finite_kept_def Let_def using s0 low by (auto simp: resolution_fset_simps)
  then show ?thesis by auto
qed

theorem finite_committed_kept_nonempty:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and g: "g |\<in>| resolution_pending st" "resolution_is_call g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n
      (Some (resolution_goal_position g)) B st)"
  shows "finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search_by
      (finite_resolution_select \<kappa> P) \<kappa> K P n (Some (resolution_goal_position g)) B st)) \<noteq> {||}"
proof -
  have kept: "finite_positions_kept st s0" by (rule finite_committed_search_positions[OF \<kappa> I s0])
  have closed: "finite_focus_pending (Some (resolution_goal_position g)) s0 = {||}"
    using finite_committed_search_found[OF \<kappa> I s0] by blast
  have "(\<exists>h. h |\<in>| resolution_pending s0 \<and> resolution_is_call h \<and> resolution_goal_position h = resolution_goal_position g) \<or>
      (\<exists>nd. nd |\<in>| resolution_nodes s0 \<and> resolution_node_position nd = resolution_goal_position g)"
    using kept g unfolding finite_positions_kept_def by blast
  then obtain nd where nd: "nd |\<in>| resolution_nodes s0" "resolution_node_position nd = resolution_goal_position g"
  proof (elim disjE exE conjE)
    fix h assume "h |\<in>| resolution_pending s0" "resolution_goal_position h = resolution_goal_position g"
    then have "h |\<in>| finite_focus_pending (Some (resolution_goal_position g)) s0"
      by (simp add: finite_focus_pending_focused)
    then show thesis using closed by simp
  qed
  then have "Ordered_Factor_Term (finite_residual_term (resolution_node_call nd)) |\<in>|
      finite_committed_answers (resolution_goal_position g) s0"
    by (auto simp: finite_committed_answers_def resolution_fset_simps)
  then have "finite_committed_answers (resolution_goal_position g) s0 \<noteq> {||}" by auto
  then show ?thesis by (rule finite_kept_nonempty[OF s0])
qed

end
