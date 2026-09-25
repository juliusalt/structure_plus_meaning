theory Factor_Resolution_Commitments
  imports Factor_Resolution_Completeness Presentation_Contracts Ordered_Finite_Terms Factor_Rule_Instances
    Factor_Positive_Locality Factor_System_Relocation Factor_Finite_System_Fields
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
          (fimage (\<lambda>s. rec F (fimage resolution_node_position (resolution_nodes s)) s)
            (finite_kept q (resolution_found sub)))))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_outcome_union (fimage (rec F B) S))"

primrec finite_committed_search_by ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search_by sel \<kappa> K P 0 F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else Resolution_Outcome {||} {|Resolution_Cut (finite_focus_pending F st)|})"
| "finite_committed_search_by sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> finite_outcome_union
        (fimage (finite_committed_search_by sel \<kappa> K P n F B) (fimage (finite_construction_step \<kappa> P st) N))
    | Select_Goals G \<Rightarrow> finite_outcome_union
        (fimage (finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F B st) G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))))"

definition finite_committed_search ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search \<kappa> K P = finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P"

section \<open>At no commitment the search is R3's\<close>

theorem finite_committed_search_by_plain:
  "finite_committed_search_by sel \<kappa> no_commitment P n None {||} = finite_resolution_search_by sel \<kappa> P n"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  have out: "finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> no_commitment P n) no_commitment P None {||} st =
      finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st" for st
    by (rule ext) (simp add: finite_committed_goal_outcome_def finite_goal_outcome_def Suc.IH Let_def)
  show ?case by (rule ext) (simp add: out Suc.IH split: resolution_selection.split)
qed

corollary finite_committed_search_plain:
  "finite_committed_search \<kappa> no_commitment P n None {||} = finite_resolution_search \<kappa> P n"
  by (simp add: finite_committed_search_def finite_resolution_search_def finite_committed_search_by_plain)

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
      with Suc.prems False obtain nd where "st' |\<in>| resolution_found (?rec F B (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps)
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
          and st': "st' |\<in>| resolution_found (?rec F (fimage resolution_node_position (resolution_nodes s)) s)"
          using finite_kept_subset
          by (auto simp: finite_committed_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
        have "resolution_invariant P d t s" using Suc.IH[OF Suc.prems(1) s] by blast
        then show ?thesis using Suc.IH st' by blast
      next
        case False
        from found False obtain s where s: "s |\<in>| finite_committed_successors K P F st g"
          and st': "st' |\<in>| resolution_found (?rec F B s)"
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
  "finite_committed_resolution \<kappa> no_commitment P d t n = finite_program_resolution \<kappa> P d t n"
  by (simp add: finite_committed_resolution_def finite_committed_search_plain finite_program_resolution_outcome)

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
  by (simp add: finite_committed_demand_def finite_demand_resolution_def finite_committed_resolution_plain)

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
  by (simp add: native_committed_resolution_def native_call_resolution_def finite_committed_resolution_plain
    finite_committed_demand_plain)

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
    (resolution_node_site nd,resolution_node_schema nd,last q,True) |\<in>| declared_sockets D) \<and>
    finite_socket_holders F st q Y g"

definition finite_socket_free ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow>
      ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_free D F st q Y g \<longleftrightarrow> q \<noteq> [] \<and> F = Some (butlast q) \<and> fBex (resolution_nodes st) (\<lambda>nd.
    resolution_node_position nd = butlast q \<and>
    (resolution_node_site nd,resolution_node_schema nd,last q,False) |\<in>| declared_sockets D \<and>
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

definition finite_declared_commitment ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_commitment" where
  "finite_declared_commitment D = \<lparr>commit_call=(\<lambda>F st g. finite_direct_commitment D F st g \<or>
      (resolution_is_call g \<and> finite_socket_commitment D F st g)),
    commit_material=(\<lambda>F st g. \<not> resolution_is_call g \<and> finite_socket_commitment D F st g)\<rparr>"

theorem finite_declared_commitment_none:
  "finite_declared_commitment no_declarations = no_commitment"
proof -
  have nd [simp]: "\<not> finite_direct_commitment no_declarations F st g" for F st g
    by (simp add: finite_direct_commitment_def no_declarations_def split: resolution_goal.split finite_term_pattern.split)
  have ns [simp]: "\<not> finite_socket_commitment no_declarations F st g" for F st g
    by (simp add: finite_socket_commitment_def finite_socket_declared_def finite_socket_kept_def
      finite_socket_free_def no_declarations_def
      split: resolution_goal.split finite_term_pattern.split)
  have c: "(\<lambda>F st g. finite_direct_commitment no_declarations F st g \<or>
      (resolution_is_call g \<and> finite_socket_commitment no_declarations F st g)) = (\<lambda>F st g. False)"
    by (intro ext) simp
  have m: "(\<lambda>F st g. \<not> resolution_is_call g \<and> finite_socket_commitment no_declarations F st g) = (\<lambda>F st g. False)"
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
  "finite_committed_resolution \<kappa> (finite_declared_commitment no_declarations) P d t n = finite_program_resolution \<kappa> P d t n"
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

definition finite_commitment_exchanges ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_commitment_exchanges U \<kappa> K P \<longleftrightarrow>
    (\<forall>n F B st \<theta> g d t. resolution_invariant P d t st \<longrightarrow> resolution_supported_at U F B P st \<theta> \<longrightarrow>
      g |\<in>| finite_focus_pending F st \<longrightarrow>
      (finite_goal_committed K F st g \<longrightarrow>
        (\<forall>s0 B0 \<theta>0. s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st) \<longrightarrow>
          resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0 \<longrightarrow>
          (\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g)
              (resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)) \<and>
            resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'))) \<and>
      (\<forall>q r M Ws. g = Resolution_Material_Goal q r M \<longrightarrow> finite_canonical_solutions M = Some Ws \<longrightarrow>
        commit_material K F st g \<longrightarrow>
        (\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and> resolution_supported_at U F B P st' \<theta>')))"

definition finite_construction_lifts ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_construction_lifts U \<kappa> P \<longleftrightarrow>
    (\<forall>F B st \<theta> d t N. resolution_invariant P d t st \<longrightarrow> resolution_supported_at U F B P st \<theta> \<longrightarrow>
      finite_resolution_select \<kappa> P (finite_focused F st) = Select_Construction N \<longrightarrow>
      (\<exists>nd \<theta>'. nd |\<in>| N \<and> resolution_supported_at U F B P (finite_construction_step \<kappa> P st nd) \<theta>'))"

lemma finite_commitment_exchanges_call:
  assumes "finite_commitment_exchanges U \<kappa> K P" "resolution_invariant P d t st" "resolution_supported_at U F B P st \<theta>"
    "g |\<in>| finite_focus_pending F st" "finite_goal_committed K F st g"
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
  obtains st' \<theta>' where "st' |\<in>| finite_solution_successors st q r M Ws" "resolution_supported_at U F B P st' \<theta>'"
  using assms unfolding finite_commitment_exchanges_def by blast

lemma finite_commitment_exchanges_none: "finite_commitment_exchanges U \<kappa> no_commitment P"
  by (simp add: finite_commitment_exchanges_def no_commitment_def finite_goal_committed_def)

lemma finite_construction_lifts_none: "finite_construction_lifts U no_witness_construction P"
  by (simp add: finite_construction_lifts_def no_witness_selection finite_plain_selection_construction)

theorem finite_committed_lifting:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and foreign: "\<And>z. U z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and exchanges: "finite_commitment_exchanges U \<kappa> K P"
    and constructions: "finite_construction_lifts U \<kappa> P"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    finite_lifted_outcome U F P (finite_committed_search \<kappa> K P n F B st)"
proof (induction n arbitrary: F B st \<theta>)
  case 0
  show ?case
  proof (cases "finite_focus_pending F st = {||}")
    case True
    then show ?thesis using "0.prems"(2)
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
  have I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>" by (rule Suc.prems)+
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
      obtain nd \<theta>' where nd: "nd |\<in>| N"
        and sup': "resolution_supported_at U F B P (finite_construction_step \<kappa> P st nd) \<theta>'"
        using constructions I sup Select_Construction unfolding finite_construction_lifts_def by blast
      have I': "resolution_invariant P d t (finite_construction_step \<kappa> P st nd)"
        by (rule resolution_construction_step[OF I \<kappa>])
      have lifted: "finite_lifted_outcome U F P (?rec F B (finite_construction_step \<kappa> P st nd))"
        by (rule Suc.IH[OF I' sup'])
      have mem: "?rec F B (finite_construction_step \<kappa> P st nd) |\<in>|
          fimage (?rec F B) (fimage (finite_construction_step \<kappa> P st) N)"
        by (rule fimageI, rule fimageI[OF nd])
      have eq: "finite_committed_search \<kappa> K P (Suc n) F B st =
          finite_outcome_union (fimage (?rec F B) (fimage (finite_construction_step \<kappa> P st) N))"
        using False Select_Construction by (simp add: finite_committed_search_def)
      show ?thesis unfolding eq by (rule finite_lifted_outcome_union[OF mem lifted])
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
              (fimage (\<lambda>s. ?rec F (fimage resolution_node_position (resolution_nodes s)) s)
                (finite_kept q (resolution_found sub))))"
            unfolding Og_def finite_committed_goal_outcome_def sub_def q_def using unpruned barred True
            by (simp add: Let_def)
          have supq: "resolution_supported_at U (Some q) B P st \<theta>"
            unfolding q_def by (rule resolution_supported_at_narrow[OF sup focus])
          have "finite_lifted_outcome U (Some q) P sub" unfolding sub_def by (rule Suc.IH[OF I supq])
          then consider (found) s0 B0 \<theta>0 where "s0 |\<in>| resolution_found sub"
              "resolution_supported_at U (Some q) B0 P s0 \<theta>0"
            | (diag) D where "D |\<in>| resolution_diagnoses sub" "\<not> finite_witnessed_diagnosis D"
            unfolding finite_lifted_outcome_def by blast
          then show ?thesis
          proof cases
            case diag
            have mem: "Resolution_Outcome {||} (resolution_diagnoses sub) |\<in>|
                finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
                  (fimage (\<lambda>s. ?rec F (fimage resolution_node_position (resolution_nodes s)) s)
                    (finite_kept q (resolution_found sub)))" by simp
            have "finite_lifted_outcome U F P (Resolution_Outcome {||} (resolution_diagnoses sub))"
              by (rule finite_lifted_diagnosis[where D=D]) (simp_all add: diag)
            then show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem])
          next
            case found
            obtain s \<theta>' where s: "s |\<in>| finite_kept q (resolution_found sub)"
              and sups: "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
              by (rule finite_commitment_exchanges_call[OF exchanges I sup gp True
                  found(1)[unfolded sub_def q_def] found(2)[unfolded q_def]])
                (simp_all add: sub_def q_def)
            have sf: "s |\<in>| resolution_found (finite_committed_search_by ?sel \<kappa> K P n (Some q) B st)"
              using s finite_kept_subset unfolding sub_def finite_committed_search_def by blast
            have Is: "resolution_invariant P d t s"
              using finite_committed_search_found[OF \<kappa> I sf] by blast
            have lifted: "finite_lifted_outcome U F P (?rec F (fimage resolution_node_position (resolution_nodes s)) s)"
              by (rule Suc.IH[OF Is sups])
            have mem: "?rec F (fimage resolution_node_position (resolution_nodes s)) s |\<in>|
                finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
                  (fimage (\<lambda>s. ?rec F (fimage resolution_node_position (resolution_nodes s)) s)
                    (finite_kept q (resolution_found sub)))"
              by (rule finsertI2, rule fimageI[OF s])
            show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem lifted])
          qed
        next
          case uncommitted: False
          obtain st' \<theta>' where st': "st' |\<in>| finite_committed_successors K P F st g"
            and sup': "resolution_supported_at U F B P st' \<theta>'"
          proof (cases "\<exists>q r M Ws. g = Resolution_Material_Goal q r M \<and> finite_canonical_solutions M = Some Ws \<and>
              commit_material K F st g")
            case True
            then obtain q r M Ws where gm: "g = Resolution_Material_Goal q r M"
              and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material K F st g" by blast
            obtain st' \<theta>' where s: "st' |\<in>| finite_solution_successors st q r M Ws"
              and u: "resolution_supported_at U F B P st' \<theta>'"
              by (rule finite_commitment_exchanges_material[OF exchanges I sup gp gm Ws cm])
            have "finite_committed_successors K P F st g = finite_solution_successors st q r M Ws"
              using gm Ws cm by (simp add: finite_committed_successors_def)
            then show thesis using that s u by simp
          next
            case False
            have eqS: "finite_committed_successors K P F st g = finite_goal_successors P st g"
              using False by (auto simp: finite_committed_successors_def split: resolution_goal.splits option.splits)
            show thesis
            proof (rule resolution_goal_lifted_at[OF Ip sup foreign pending focus kind])
              fix st' \<theta>' assume s: "st' |\<in>| finite_goal_successors P st g"
                and u: "resolution_supported_at U F B P st' \<theta>'"
                and "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
              show thesis using that s u eqS by simp
            qed
          qed
          have gs: "st' |\<in>| finite_goal_successors P st g" using st' finite_committed_successors_subset by blast
          have I': "resolution_invariant P d t st'" by (rule resolution_goal_step[OF I pending gs])
          have lifted: "finite_lifted_outcome U F P (?rec F B st')" by (rule Suc.IH[OF I' sup'])
          have ne: "finite_committed_successors K P F st g \<noteq> {||}" using st' by auto
          have Og: "Og = finite_outcome_union (fimage (?rec F B) (finite_committed_successors K P F st g))"
            unfolding Og_def finite_committed_goal_outcome_def using unpruned barred uncommitted ne
            by (simp add: Let_def)
          have mem: "?rec F B st' |\<in>| fimage (?rec F B) (finite_committed_successors K P F st g)"
            by (rule fimageI[OF st'])
          show ?thesis unfolding Og by (rule finite_lifted_outcome_union[OF mem lifted])
        qed
      qed
      then show ?thesis unfolding eq by (rule finite_lifted_outcome_union[OF memg])
    qed
  qed
qed

text \<open>R4's lifting is the committed lifting's instance at no commitment, the empty focus and no barred node.\<close>

corollary finite_resolution_lifting_committed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and I: "resolution_invariant P d t st" and sup: "resolution_supported P st \<theta>"
  shows "resolution_found (finite_resolution_search \<kappa> P n st) \<noteq> {||} \<or>
    resolution_diagnoses (finite_resolution_search \<kappa> P n st) \<noteq> {||}"
proof -
  have "finite_lifted_outcome (\<lambda>_. False) None P (finite_committed_search \<kappa> no_commitment P n None {||} st)"
    by (rule finite_committed_lifting[OF \<kappa> resolution_no_foreign finite_commitment_exchanges_none constructions I
      sup[unfolded resolution_supported_none resolution_supported_by_at]])
  then show ?thesis unfolding finite_committed_search_plain finite_lifted_outcome_def by auto
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
    by (rule finite_committed_lifting[OF \<kappa> resolution_no_foreign exchanges constructions I0 S0])
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
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
  shows "finite_resolution_refutes (finite_program_resolution \<kappa> P d t n) \<Longrightarrow>
      (d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
    and "finite_program_resolution \<kappa> P d t n = Finite_Resolved C \<Longrightarrow>
      (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  using finite_committed_resolution_refutation_exact[OF \<kappa> finite_commitment_exchanges_none constructions, of d t n]
    finite_committed_resolution_sound(2)[of \<kappa> no_commitment P d t n C]
  by (simp_all add: finite_committed_resolution_plain)

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

end
