theory Development_Given_Checks_Execution
  imports Development_Given_Productions Development_Given_Execution_Fixtures Factor_Resolution_Checks Factor_Shared_Resolution
    Factor_Shared_Commitments Factor_Shared_Search Factor_Indexed_Resolution Factor_Resolution_Graph_Checks
    Native_Execution_Refinements "HOL-Library.Product_Plus"
begin

text \<open>
  K3 of correction (14) of "Committed choice, for refusals" (DECISIONS.md, task 495's entry), with correction (15):
  #779's calls 77/1, 77/2 and 113/7 over the given's rooted readers, at the moded selection with @{const given_modes},
  under the narrowed commitment of the record declaring 12's input production at 37.0/2
  (@{const given_input_declarations}) at the producing socket's frame (@{const lookup_frames}) and at the record's own
  frames (@{const given_input_frames}), with O4's fixtures and 77's least bound handed in beside
  @{const given_witness_registrations}; each at the check form (@{const moded_check_resolution}, the search started at
  the root's own focus) and at the committed form at @{term None} (@{const moded_committed_resolution}), through K2's
  constants. A thin theory no library theory imports.
\<close>

declare [[code abort: finite_object_of union_class]]

section \<open>The search, counted\<close>

text \<open>
  The committed search at a selection with, beside its outcome, seven counts: the states it visits (counted as O1's
  count @{const committed_search_states} counts them; the correspondence is checked by evaluation at the rows below,
  not proved), at a goal at 5 the search takes uncommitted its successors' number: none (a dead end), one (a single
  step), more (a branching); the committed goals at 12 whose production is met (the commitment's production defined
  at the goal); the dead ends at 5 below a ground focus (@{const finite_focus_ground}); and the blocks a first join
  searched after a block that found nothing and was cut. The outcome is the committed search's
  (the theorem @{text given_checks_search_outcome} below); the counts read the goal's site, the focus and the successors'
  number, no position.
\<close>

type_synonym given_checks_counts = "nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat"

definition given_checks_cut :: "(nat,nat,nat,nat) resolution_outcome \<Rightarrow> bool" where
  "given_checks_cut R \<longleftrightarrow> fBex (resolution_diagnoses R) (\<lambda>D. case D of Resolution_Cut G \<Rightarrow> True | _ \<Rightarrow> False)"

primrec given_checks_first ::
    "('x \<Rightarrow> (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts) \<Rightarrow> 'x fset list \<Rightarrow>
      (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts" where
  "given_checks_first f [] = (Resolution_Outcome {||} {||}, 0)"
| "given_checks_first f (X # Xs) = (let Q = fimage (\<lambda>x. (x, f x)) X;
      R = finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q); c = sum (\<lambda>z. snd (snd z)) (fset Q) in
    if resolution_found R \<noteq> {||} then (R, c)
    else let R' = given_checks_first f Xs in
      (Resolution_Outcome (resolution_found (fst R')) (resolution_diagnoses R |\<union>| resolution_diagnoses (fst R')),
        c + (0,0,0,0,0,0, if Xs \<noteq> [] \<and> given_checks_cut R then 1 else 0) + snd R'))"

definition given_checks_join ::
    "nat list option \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow>
      ('x \<Rightarrow> (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts) \<Rightarrow> 'x fset \<Rightarrow>
      (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts" where
  "given_checks_join F st key f X = (if finite_focus_ground F st
    then given_checks_first f (finite_key_blocks key X)
    else let Q = fimage (\<lambda>x. (x, f x)) X in
      (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), sum (\<lambda>z. snd (snd z)) (fset Q)))"

definition given_checks_at_5 :: "bool \<Rightarrow> (nat,nat,nat,nat) resolution_goal \<Rightarrow> nat \<Rightarrow> given_checks_counts" where
  "given_checks_at_5 gr g k = (case g of Resolution_Call_Goal q r d p \<Rightarrow>
      if d = 5 then (0, if k = 0 then 1 else 0, if k = 1 then 1 else 0, if 2 \<le> k then 1 else 0, 0,
        if gr \<and> k = 0 then 1 else 0, 0) else 0
    | Resolution_Material_Goal q r M \<Rightarrow> 0)"

definition given_checks_produced :: "(nat,nat,nat,nat) resolution_commitment \<Rightarrow> nat list option \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_goal \<Rightarrow> given_checks_counts" where
  "given_checks_produced K F st g = (case g of Resolution_Call_Goal q r d p \<Rightarrow>
      if d = 12 \<and> commit_production K F st g \<noteq> None then (0,0,0,0,1,0,0) else 0
    | Resolution_Material_Goal q r M \<Rightarrow> 0)"

definition given_checks_goal ::
    "(nat list option \<Rightarrow> nat list fset \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow>
        (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts) \<Rightarrow>
      (nat,nat,nat,nat) resolution_commitment \<Rightarrow> (nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat list option \<Rightarrow>
      nat list fset \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_goal \<Rightarrow>
      (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts" where
  "given_checks_goal rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then (Resolution_Outcome {||} {||}, 0)
     else if finite_pruned (finite_barred B st) g then (Resolution_Outcome {||} {|Resolution_Cut {|g|}|}, 0)
     else if finite_goal_committing K F st g then
       (let q = resolution_goal_position g;
          sub = rec (Some q) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g);
          C = given_checks_join F st (\<lambda>_. 0) (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found (fst sub))) in
        (finite_outcome_union {|Resolution_Outcome {||} (resolution_diagnoses (fst sub)), fst C|},
          given_checks_produced K F st g + snd sub + snd C))
     else let S = finite_committed_successors K P F st g; c = given_checks_at_5 (finite_focus_ground F st) g (fcard S) in
       if S={||} then (if resolution_witnesses st={||} then (Resolution_Outcome {||} {||}, c)
         else (Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|}, c))
       else let J = given_checks_join F st (finite_determinate_key (resolution_goal_position g))
         (rec F (finite_goal_barring K F B st g)) S in (fst J, c + snd J))"

primrec given_checks_search ::
    "((nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection) \<Rightarrow>
      (nat,nat,nat,nat) finite_witness_construction \<Rightarrow> (nat,nat,nat,nat) resolution_commitment \<Rightarrow>
      (nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> nat list option \<Rightarrow> nat list fset \<Rightarrow>
      (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_outcome \<times> given_checks_counts" where
  "given_checks_search sel \<kappa> K P 0 F B st = (finite_committed_search_by sel \<kappa> K P 0 F B st, (1,0,0,0,0,0,0))"
| "given_checks_search sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then (Resolution_Outcome {|st|} {||}, (1,0,0,0,0,0,0)) else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then (Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}, (1,0,0,0,0,0,0))
        else let Q = fimage (\<lambda>s. (s, given_checks_search sel \<kappa> K P n F (finite_committed_barring B st) s))
            (fimage (finite_construction_step \<kappa> P st) M) in
          (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), (1,0,0,0,0,0,0) + sum (\<lambda>z. snd (snd z)) (fset Q)))
    | Select_Goals G \<Rightarrow> (let Q = fimage (\<lambda>g. (g, given_checks_goal (given_checks_search sel \<kappa> K P n)
          K P F B st g)) G in
        (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), (1,0,0,0,0,0,0) + sum (\<lambda>z. snd (snd z)) (fset Q)))
    | Select_None \<Rightarrow> (Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st)), (1,0,0,0,0,0,0))))"

text \<open>The counts leave the outcome the committed search's.\<close>

lemma given_checks_first_outcome:
  "fst (given_checks_first f Ys) = finite_first_outcome (\<lambda>x. fst (f x)) Ys"
  by (induction Ys) (auto simp: Let_def fset.map_comp comp_def split: if_split)

lemma given_checks_join_outcome:
  "fst (given_checks_join F st key f X) = finite_search_join F st key (\<lambda>x. fst (f x)) X"
  by (simp add: given_checks_join_def finite_search_join_def given_checks_first_outcome Let_def
    fset.map_comp comp_def)

lemma given_checks_goal_outcome:
  assumes rec: "\<And>F' B' s. fst (rec F' B' s) = rec' F' B' s"
  shows "fst (given_checks_goal rec K P F B st g) = finite_committed_goal_outcome rec' K P F B st g"
  unfolding given_checks_goal_def finite_committed_goal_outcome_in_def Let_def
  by (simp add: rec given_checks_join_outcome split: if_split)

theorem given_checks_search_outcome:
  "fst (given_checks_search sel \<kappa> K P n F B st) = finite_committed_search_by sel \<kappa> K P n F B st"
proof (induction n arbitrary: F B st)
  case 0
  show ?case by simp
next
  case (Suc n)
  have g: "fst (given_checks_goal (given_checks_search sel \<kappa> K P n) K P F' B' s g) =
      finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F' B' s g" for F' B' s g
    by (rule given_checks_goal_outcome) (rule Suc.IH)
  show ?case
    by (simp add: g Suc.IH Let_def fset.map_comp comp_def split: if_split resolution_selection.split)
qed

section \<open>The calls\<close>

definition given_checks_call :: "nat \<Rightarrow> nat \<times> local_address option definition_site list option \<times> finite_factor_term" where
  "given_checks_call k = (if k = 7 then (113, None, modes_113_call 3)
    else (case productions_call k of (bound,t) \<Rightarrow> (77, bound, t)))"

fun given_checks_kinds :: "(nat,nat,nat,nat) finite_resolution_result \<Rightarrow> nat list" where
  "given_checks_kinds (Finite_Unresolved D) = sorted_list_of_fset (fimage modes_diagnosis_kind D)"
| "given_checks_kinds R = []"

text \<open>
  A row: the verdict through K2's constant at the form (@{term True} the check form, @{term False} the committed form
  at @{term None}), the diagnoses' kinds (0 a cut at the bound, 2 a witnessed failure), O1's count at the form's
  focus, and the five counts of @{const given_checks_search} at the same focus.
\<close>

definition given_checks_result :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) finite_resolution_result" where
  "given_checks_result check D \<Phi> k n = (case given_checks_call k of (d,bound,t) \<Rightarrow>
    let \<kappa> = modes_construction bound n; P = finite_rooted_given_readers; Dm = resolution_declarations.truncate D in
    if check then moded_check_resolution \<kappa> P n D \<Phi> Dm given_modes d t n
    else moded_committed_resolution \<kappa> P n D \<Phi> Dm given_modes d t n)"

definition given_checks_states :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "given_checks_states check D \<Phi> k n = (case given_checks_call k of (d,bound,t) \<Rightarrow>
    let \<kappa> = modes_construction bound n; P = finite_rooted_given_readers; K = finite_narrowed_commitment P n D \<Phi>;
      sel = finite_moded_select \<kappa> K (resolution_declarations.truncate D) given_modes P in
    committed_search_states sel \<kappa> K P n (if check then Some [] else None) {||} (finite_initial_state d t))"

definition given_checks_counted :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> given_checks_counts" where
  "given_checks_counted check D \<Phi> k n = (case given_checks_call k of (d,bound,t) \<Rightarrow>
    let \<kappa> = modes_construction bound n; P = finite_rooted_given_readers; K = finite_narrowed_commitment P n D \<Phi>;
      sel = finite_moded_select \<kappa> K (resolution_declarations.truncate D) given_modes P in
    snd (given_checks_search sel \<kappa> K P n (if check then Some [] else None) {||} (finite_initial_state d t)))"

definition given_checks_run :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow> (nat,nat,nat) resolution_frames \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> bool option \<times> nat list \<times> nat \<times> given_checks_counts" where
  "given_checks_run check D \<Phi> k n = (let R = given_checks_result check D \<Phi> k n in
    (finite_resolution_verdict R, given_checks_kinds R, given_checks_states check D \<Phi> k n,
     given_checks_counted check D \<Phi> k n))"

section \<open>The rows\<close>

text \<open>
  Each row: the verdict (resolved: @{term "Some True"}; unresolved: @{term None}), the diagnoses' kinds, O1's count and
  the five counts (states, and at 5 dead ends, single steps and branchings; productions met at 12).

  113/7 at 230, R3's least bound: resolved at both forms, in 394 states at the check form against 401 at the committed
  form at @{term None}: below the ground root 5's four dead ends go and 7's bag checks keep their first found state.
  77/1 and 77/2 are unresolved at both forms, with the same states and counts: 77's search stands under 37's committed
  goal at 75.0/1, whose output is free until 12's production, so its joins are unions at both forms; 12(t4,t4), the
  produced check, stands under its own ground focus at both. The production of 12's input at 37.0/2 is met once at
  77/1 at 200 and 400 and at 77/2 at 300 and 400 (77/2 at 200 is cut before 37), as correction (15) predicts. Past it
  77/1 at 400 spends its states in 12's check: 249 single steps, 34 dead ends and 34 branchings at 5 (correction (15)'s
  census: 246, 31, 32), 33 of the dead ends below a ground focus, and 33 blocks searched after a block cut at the bound:
  where the check is cut, its first join searches the next block as a union does. Every row is cut at the bound or
  left by a witnessed failure; none refutes. Since M2 (task 998), 10 calls 0 alone beside its material premise: 113/7
  takes fewer states (400 and 413 before), and within the same bounds 77's searches reach further (77/2 at 300: 308
  states before; 77/1 at 400: 830, with 31 dead ends, 32 branchings, 30 and 31; 77/2 at 400: 430).
\<close>

lemma given_checks_controls:
  "given_checks_run True given_input_declarations lookup_frames 7 230 = (Some True, [], 394, (394,0,3,4,0,0,0)) \<and>
   given_checks_run False given_input_declarations lookup_frames 7 230 = (Some True, [], 401, (401,4,6,4,0,0,0)) \<and>
   given_checks_run True given_input_declarations lookup_frames 1 200 = (None, [0,2], 220, (220,2,22,2,1,1,1)) \<and>
   given_checks_run True given_input_declarations lookup_frames 2 200 = (None, [0], 201, (201,0,12,0,0,0,0)) \<and>
   given_checks_run True given_input_declarations lookup_frames 2 300 = (None, [0,2], 330, (330,2,41,2,1,1,1)) \<and>
   given_checks_run False given_input_declarations lookup_frames 2 300 = (None, [0,2], 330, (330,2,41,2,1,1,1)) \<and>
   given_checks_kinds (given_checks_result True given_input_declarations lookup_frames 1 400) = [0,2] \<and>
   given_checks_counted True given_input_declarations lookup_frames 1 400 = (875,34,249,34,1,33,33) \<and>
   given_checks_counted False given_input_declarations lookup_frames 1 400 = (875,34,249,34,1,33,33) \<and>
   given_checks_kinds (given_checks_result True given_input_declarations lookup_frames 2 400) = [0,2] \<and>
   given_checks_counted True given_input_declarations lookup_frames 2 400 = (451,2,50,5,1,1,4)"
  by eval




end
