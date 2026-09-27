theory Factor_Check_Controls
  imports Factor_Resolution_Checks Development_Given_Modes_Execution
begin

text \<open>
  The check form against the committed form at a bag check (K2 of correction (14), task 495's entry): 7, the
  four-field comparison, at the largest artifact of 77/2's environment (#794's draft builds it so) with itself and
  with its fields reversed, and at a pair with one entry changed, over the given's rooted readers and the given's
  record under the narrowed commitment at the moded selection with @{const given_modes}, through the route forms'
  constants. Each row runs each form once, through the shared representation the constants' code runs
  (@{const moded_route_resolution}), and reads the verdict and the count of the states it visits from that one run.
\<close>

section \<open>The count of a search through the shared representation\<close>

text \<open>
  Task 832 (review 824's follow-up 6). The count of the states the route's search visits, read through the shared
  representation beside the outcome it returns: O1's count (@{const committed_counted_search}) over the tested step
  (@{const tested_committed_step}), one for every call of the search, a committed goal's sub-search and the
  continuations of its kept states, a plain goal's successors, and at a first join below a ground focus only the
  blocks the join evaluates (@{const committed_first_counted}). Its outcome is the tested search's
  (@{text tested_counted_search_outcome}), so a row's verdict is the constant's (@{text check_control_row_forms}).
\<close>

definition tested_counted_goal where
  "tested_counted_goal R T gd rec F B r V x h =
    (if access_pruned_among (\<lambda>q. q |\<notin>| B) V h then (Resolution_Outcome {||} {||}, 0)
     else if access_pruned_among (\<lambda>q. q |\<in>| B) V h then (Resolution_Outcome {||} {|Resolution_Cut {|access_goal V h|}|}, 0)
     else if gd r h \<and> tests_committing T F r V x h then
       (case tests_produced T F B r V x h of (q,B',r') \<Rightarrow> let sub = rec (Some q) B' r';
          Q = fimage (\<lambda>s. (s, rec F (finite_committed_barring B s) (rep_share R s))) (finite_kept q (resolution_found (fst sub))) in
        (finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses (fst sub)))
          (fimage (\<lambda>z. fst (snd z)) Q)), snd sub + sum (\<lambda>z. snd (snd z)) (fset Q)))
     else let cm = gd r h \<and> tests_material T F r V x h;
       S = represented_committed_successors R F cm r V h in
       if S = {||} then (if access_witnesses V = {||} then (Resolution_Outcome {||} {||}, 0)
         else (Resolution_Outcome {||} {|Resolution_Witnessed (access_witnesses V) (access_goal V h)|}, 0))
       else if access_focus_ground F V
         then committed_first_counted (rec F (if cm then B |\<union>| rep_node_positions R r else B))
           (finite_key_blocks (\<lambda>s'. access_determinate_key (tests_position T r V x h) (rep_access R s')) S)
         else let Q = fimage (\<lambda>s. (s, rec F (if cm then B |\<union>| rep_node_positions R r else B) s)) S in
           (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), sum (\<lambda>z. snd (snd z)) (fset Q)))"

lemma tested_counted_goal_outcome:
  assumes rec: "\<And>F' B' s. fst (rec F' B' s) = rec' F' B' s"
  shows "fst (tested_counted_goal R T gd rec F B r V x h) = tested_committed_goal_outcome R T gd rec' F B r V x h"
  unfolding tested_counted_goal_def tested_committed_goal_outcome_def Let_def
  by (simp add: rec committed_first_counted_outcome fset.map_comp comp_def split: if_split prod.split)

definition tested_counted_step where
  "tested_counted_step R T gd \<kappa> P rec F B r = (let V = rep_access R r; x = tests_prepare T F r V in
    case access_select (\<lambda>h. gd r h \<and> tests_priority T F r V x h) (access_focused F V) of
      Access_Construction N \<Rightarrow> (let M = ffilter (\<lambda>m. resolution_focused F (access_node_position V m)) N in
        if M = {||} then (Resolution_Outcome {||} {|Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))|}, 1)
        else let Q = fimage (\<lambda>s. (s, rec F (B |\<union>| rep_node_positions R r) s)) (fimage (rep_construct R r) M) in
          (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), Suc (sum (\<lambda>z. snd (snd z)) (fset Q))))
    | Access_Goals G \<Rightarrow> (let Q = fimage (\<lambda>h. (h, tested_counted_goal R T gd rec F B r V x h)) G in
        (finite_outcome_union (fimage (\<lambda>z. fst (snd z)) Q), Suc (sum (\<lambda>z. snd (snd z)) (fset Q))))
    | Access_None \<Rightarrow> (Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))) (finite_unconstructed \<kappa> P (rep_project R r))), 1))"

lemma tested_counted_step_outcome:
  assumes rec: "\<And>F' B' s. fst (rec F' B' s) = rec' F' B' s"
  shows "fst (tested_counted_step R T gd \<kappa> P rec F B r) = tested_committed_step R T gd \<kappa> P rec' F B r"
  unfolding tested_counted_step_def tested_committed_step_def Let_def
  by (simp add: rec tested_counted_goal_outcome[OF rec] fset.map_comp comp_def split: access_selection.split if_split)

primrec tested_counted_search where
  "tested_counted_search R T gd \<kappa> P 0 F B r = (tested_committed_search R T gd \<kappa> P 0 F B r, 1)"
| "tested_counted_search R T gd \<kappa> P (Suc n) F B r =
    (if access_focus_goals F (rep_access R r) = {||} then (Resolution_Outcome {|rep_project R r|} {||}, 1)
     else tested_counted_step R T gd \<kappa> P (tested_counted_search R T gd \<kappa> P n) F B (rep_refresh R r))"

theorem tested_counted_search_outcome:
  "fst (tested_counted_search R T gd \<kappa> P n F B r) = tested_committed_search R T gd \<kappa> P n F B r"
proof (induction n arbitrary: F B r)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case by (simp add: tested_counted_step_outcome[OF Suc.IH] split: if_split)
qed

definition check_control_counted where
  "check_control_counted \<kappa> P m D \<Phi> Dm M F0 d t n = (let Kc = access_narrowed_commitment P m D \<Phi>;
      X = finite_declared_raisers P (resolution_declarations.truncate D);
      gd = (\<lambda>r h. shared_raising_guard X (resolution_declarations.truncate D) M (shared_entry_goal h)) in
    tested_counted_search (shared_committed_representation \<kappa> P)
      (commitment_tests (shared_committed_representation \<kappa> P) shared_commitment_access Kc Dm M gd) gd \<kappa> P n F0 {||}
      (search_of P (finite_initial_state d t)))"

lemma check_control_counted_route:
  assumes distinct: "clause_sockets_distinct P"
  shows "moded_route_resolution \<kappa> P m D \<Phi> Dm M (access_narrowed_commitment P m D \<Phi>)
      (finite_declared_raisers P (resolution_declarations.truncate D)) F0 d t n =
    finite_outcome_result P d t (fst (check_control_counted \<kappa> P m D \<Phi> Dm M F0 d t n))"
  using distinct by (simp add: moded_route_resolution_def check_control_counted_def tested_counted_search_outcome Let_def)

section \<open>The artifacts of 77/2's environment\<close>

definition check_control_artifacts :: "finite_factor_term list" where
  "check_control_artifacts = (case finite_environment_value (fst (modes_fixture_install modes_fixture_two [1,0])) of
      Finite_Pair rs bs \<Rightarrow> (case finite_data_list_read rs of
        Some xs \<Rightarrow> map (\<lambda>r. case r of Finite_Pair u a \<Rightarrow> a | _ \<Rightarrow> r) xs | None \<Rightarrow> [])
    | _ \<Rightarrow> [])"

definition check_control_fields :: "finite_factor_term \<Rightarrow> finite_factor_term list list" where
  "check_control_fields t = (case t of Finite_Pair a (Finite_Pair e (Finite_Pair b f)) \<Rightarrow>
      map (\<lambda>x. case finite_data_list_read x of Some ys \<Rightarrow> ys | None \<Rightarrow> []) [a,e,b,f]
    | _ \<Rightarrow> [])"

definition check_control_rebuilt :: "finite_factor_term list list \<Rightarrow> finite_factor_term" where
  "check_control_rebuilt fs = (case map finite_data_list fs of [a,e,b,f] \<Rightarrow>
      Finite_Pair a (Finite_Pair e (Finite_Pair b f)) | _ \<Rightarrow> Finite_Payload [])"

definition check_control_sized :: "nat list \<Rightarrow> finite_factor_term" where
  "check_control_sized ns = (case filter (\<lambda>a. map length (check_control_fields a) = ns) check_control_artifacts of
      a # as \<Rightarrow> a | [] \<Rightarrow> Finite_Payload [])"

definition check_control_reversed :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "check_control_reversed t = check_control_rebuilt (map rev (check_control_fields t))"

definition check_control_changed :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "check_control_changed t = check_control_rebuilt (case check_control_fields t of
      (x # xs) # fs \<Rightarrow> (Finite_Payload [255,255] # xs) # fs | fs \<Rightarrow> fs)"

definition check_control_changed_value :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "check_control_changed_value t = check_control_rebuilt (case check_control_fields t of
      [a,e,b,Finite_Pair k v # f] \<Rightarrow> [a,e,b,Finite_Pair k (Finite_Payload [255]) # f] | fs \<Rightarrow> fs)"

section \<open>The two forms\<close>

definition check_control_row :: "finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option \<times> nat \<times> bool option \<times> nat" where
  "check_control_row t n = (let P = finite_rooted_given_readers;
      c = check_control_counted no_witness_construction P n given_declarations {||}
        (resolution_declarations.truncate given_declarations) given_modes (Some []) 7 t n;
      a = check_control_counted no_witness_construction P n given_declarations {||}
        (resolution_declarations.truncate given_declarations) given_modes None 7 t n in
    (finite_resolution_verdict (finite_outcome_result P 7 t (fst c)), snd c,
     finite_resolution_verdict (finite_outcome_result P 7 t (fst a)), snd a))"

lemma check_control_row_forms:
  assumes "clause_sockets_distinct finite_rooted_given_readers"
  shows "fst (check_control_row t n) = finite_resolution_verdict (moded_check_resolution no_witness_construction
      finite_rooted_given_readers n given_declarations {||} (resolution_declarations.truncate given_declarations)
      given_modes 7 t n)"
    and "fst (snd (snd (check_control_row t n))) = finite_resolution_verdict (moded_committed_resolution
      no_witness_construction finite_rooted_given_readers n given_declarations {||}
      (resolution_declarations.truncate given_declarations) given_modes 7 t n)"
  using assms by (simp_all add: check_control_row_def Let_def moded_check_resolution_route
    moded_committed_resolution_route check_control_counted_route)

definition check_control_r4 :: "finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "check_control_r4 t n = finite_resolution_verdict
    (finite_program_resolution no_witness_construction finite_rooted_given_readers 7 t n)"

section \<open>The rows\<close>

text \<open>
  The environment holds four artifacts, their fields of (1,0,0,0), (9,6,0,2), (27,23,0,1) and (18,14,0,1) entries. The
  rooted readers' clause sockets are distinct, so each row's verdicts are the constants' (@{text check_control_row_forms}).
  At the largest, (27,23,0,1), with itself the check form resolves in 649 states against 1,655 at the committed form at
  @{term None}: below the ground root every join keeps its first found state, so 5's dead "later" walks at 6.1/0 go
  (#794's prototype: 695 against 1,701). With its fields reversed the largest was not run (it exceeded the probe's bound
  beside the first row when each row ran each form twice); (18,14,0,1) reversed was not tried; at (9,6,0,2) reversed
  the check form resolves in 284 states against 309, each entry walked to its displaced position, the certificate's own
  size. A pair whose first carrier address is changed (the incidence left at the old address, so the term presents no
  formed artifact) is refuted by both forms in 12 states, as R4 refutes it; R4's verdict stands beside this pair only,
  R4 being infeasible at the true rows. A pair whose first functional value is changed (formation kept: the address and
  every other field as they were) is refuted by both forms in 217 states, through the comparison of the two artifacts'
  fields. Unresolved never refutes and never admits. The bound is 2000, never reached. The counts are those O1's
  count gave at the same rows when read beside the abstract search (task 823).
\<close>

lemma check_controls:
  "clause_sockets_distinct finite_rooted_given_readers \<and>
    check_control_row (Finite_Pair (check_control_sized [27,23,0,1]) (check_control_sized [27,23,0,1])) 2000 =
      (Some True, 649, Some True, 1655) \<and>
    check_control_row (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_reversed (check_control_sized [9,6,0,2]))) 2000 = (Some True, 284, Some True, 309) \<and>
    check_control_row (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_changed (check_control_sized [9,6,0,2]))) 2000 = (Some False, 12, Some False, 12) \<and>
    check_control_r4 (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_changed (check_control_sized [9,6,0,2]))) 2000 = Some False \<and>
    check_control_row (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_changed_value (check_control_sized [9,6,0,2]))) 2000 = (Some False, 217, Some False, 217)"
  by eval

end
