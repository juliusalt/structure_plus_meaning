theory Factor_Committed_Traces
  imports Factor_Resolution_Lifting
begin

text \<open>
  The committed search (@{const finite_committed_search_by}), traced: at every goal the search selects, what a probe
  reads of the goal in its state, with the focus beside it. The traced search computes the search's outcome and the
  trace together, so it takes the search's course and no other: its constructions and selected goals, a committed
  goal's sub-search from its produced state and the states it keeps, and every join as @{const finite_search_join}
  takes it — below a ground focus block by block (@{const finite_key_blocks}), no block after the first that finds
  (as @{const finite_first_outcome}); elsewhere every successor. Its outcome is the search's
  (@{text committed_traced_search_outcome}); the trace is its second component (@{text committed_trace}).
\<close>

type_synonym ('a,'s,'d,'c,'x) traced_outcome = "('a,'s,'d,'c) resolution_outcome \<times> 'x fset"

primrec committed_traced_first ::
    "('y \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome) \<Rightarrow> 'y fset list \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome" where
  "committed_traced_first f [] = (Resolution_Outcome {||} {||}, {||})"
| "committed_traced_first f (X # Xs) = (let Q = fimage f X; R = finite_outcome_union (fimage fst Q);
      c = ffUnion (fimage snd Q) in
    if resolution_found R \<noteq> {||} then (R, c)
    else let R' = committed_traced_first f Xs in
      (Resolution_Outcome (resolution_found (fst R')) (resolution_diagnoses R |\<union>| resolution_diagnoses (fst R')),
        c |\<union>| snd R'))"

definition committed_traced_join ::
    "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('y \<Rightarrow> nat) \<Rightarrow>
      ('y \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome) \<Rightarrow> 'y fset \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome" where
  "committed_traced_join F st key f X = (if finite_focus_ground F st
    then committed_traced_first f (finite_key_blocks key X)
    else let Q = fimage f X in (finite_outcome_union (fimage fst Q), ffUnion (fimage snd Q)))"

definition committed_traced_goal ::
    "('s::linorder list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> 'x fset) \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome) \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      ('a,'s,'d,'c,'x) traced_outcome" where
  "committed_traced_goal probe rec K P F B st g = (let R =
    (if finite_pruned (finite_unbarred B st) g then (Resolution_Outcome {||} {||}, {||})
     else if finite_pruned (finite_barred B st) g then (Resolution_Outcome {||} {|Resolution_Cut {|g|}|}, {||})
     else if finite_goal_committing K F st g then
       (let q = resolution_goal_position g;
          sub = rec (Some q) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g);
          C = committed_traced_join F st (\<lambda>_. 0) (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found (fst sub))) in
        (finite_outcome_union {|Resolution_Outcome {||} (resolution_diagnoses (fst sub)), fst C|}, snd sub |\<union>| snd C))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then (Resolution_Outcome {||} {||}, {||})
         else (Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|}, {||}))
       else committed_traced_join F st (finite_determinate_key (resolution_goal_position g))
         (rec F (finite_goal_barring K F B st g)) S) in
    (fst R, probe F st g |\<union>| snd R))"

primrec committed_traced_search ::
    "('s::linorder list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> 'x fset) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c,'x) traced_outcome" where
  "committed_traced_search probe sel \<kappa> K P 0 F B st = (finite_committed_search_by sel \<kappa> K P 0 F B st, {||})"
| "committed_traced_search probe sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then (Resolution_Outcome {|st|} {||}, {||}) else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then (Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}, {||})
        else let Q = fimage (committed_traced_search probe sel \<kappa> K P n F (finite_committed_barring B st))
            (fimage (finite_construction_step \<kappa> P st) M) in
          (finite_outcome_union (fimage fst Q), ffUnion (fimage snd Q)))
    | Select_Goals G \<Rightarrow> (let Q = fimage (committed_traced_goal probe (committed_traced_search probe sel \<kappa> K P n)
          K P F B st) G in
        (finite_outcome_union (fimage fst Q), ffUnion (fimage snd Q)))
    | Select_None \<Rightarrow> (Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st)), {||})))"

definition committed_trace ::
    "('s::linorder list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> 'x fset) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> 'x fset" where
  "committed_trace probe sel \<kappa> K P n F B st = snd (committed_traced_search probe sel \<kappa> K P n F B st)"

text \<open>The traced search's outcome is the committed search's: the trace follows its course.\<close>

lemma committed_traced_first_outcome:
  "fst (committed_traced_first f Ys) = finite_first_outcome (\<lambda>x. fst (f x)) Ys"
  by (induction Ys) (auto simp: Let_def fset.map_comp comp_def split: if_split)

lemma committed_traced_join_outcome:
  "fst (committed_traced_join F st key f X) = finite_search_join F st key (\<lambda>x. fst (f x)) X"
  by (simp add: committed_traced_join_def finite_search_join_def committed_traced_first_outcome Let_def
    fset.map_comp comp_def)

lemma committed_traced_goal_outcome:
  assumes rec: "\<And>F' B' s. fst (rec F' B' s) = rec' F' B' s"
  shows "fst (committed_traced_goal probe rec K P F B st g) = finite_committed_goal_outcome rec' K P F B st g"
  unfolding committed_traced_goal_def finite_committed_goal_outcome_in_def Let_def
  by (simp add: rec committed_traced_join_outcome split: if_split)

theorem committed_traced_search_outcome:
  "fst (committed_traced_search probe sel \<kappa> K P n F B st) = finite_committed_search_by sel \<kappa> K P n F B st"
proof (induction n arbitrary: F B st)
  case 0
  show ?case by simp
next
  case (Suc n)
  have g: "fst (committed_traced_goal probe (committed_traced_search probe sel \<kappa> K P n) K P F' B' s g) =
      finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F' B' s g" for F' B' s g
    by (rule committed_traced_goal_outcome) (rule Suc.IH)
  show ?case
    by (simp add: g Suc.IH Let_def fset.map_comp comp_def split: if_split resolution_selection.split)
qed

end
