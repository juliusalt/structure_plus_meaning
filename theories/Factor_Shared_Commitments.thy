theory Factor_Shared_Commitments
  imports Factor_Shared_Search Factor_Resolution_Commitments Ranged_Carrier_Indexes
begin

section \<open>R5's committed search over a representation\<close>

text \<open>
  Build F2c of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size". R5's committed search
  (@{const finite_committed_search_by}) is stated here once over a representation of R3's state, as R3's search is
  (@{const represented_search}), at every priority of F1's selection (@{const finite_resolution_select_at}). What the
  committed step reads of a state is read through the access: its focus (the goals at or under the focus, and the
  access of the focused state, @{text access_focused}) and the pruning among the barred or the unbarred nodes
  (@{text access_pruned_among}). What it writes is the representation's own, fields added to R3's representation
  (@{text committed_representation}): the positions of the state's nodes the barring adds, the successors of a call
  at the focus, the successors of a committed material premise at its canonical solutions, the substitution a
  production makes, and the representation of a state a committed sub-search found. The commitment's tests are read
  on the state's projection, and only at goals a guard admits: a goal the guard does not admit is one no test of the
  commitment and no priority accepts (the locale's @{text guard}), so the projection is made at a step only where some
  goal is admitted. By induction on the bound over the committed step, the search over a formed representation is R5's
  at the projection (@{text committed_representation_formed.search}); the shared state is its instance, and gives the
  committed search's code equation.
\<close>

lemma take_prefix_cases:
  assumes f: "take (length f) g = f" and p: "take (length p) g = p"
  shows "take (length f) p = f \<or> take (length p) f = p"
proof (cases "length f \<le> length p")
  case True
  then have "take (length f) p = take (length f) (take (length p) g)" using p by simp
  then show ?thesis using True f by (simp add: min_def)
next
  case False
  then have "take (length p) f = take (length p) (take (length f) g)" using f by simp
  then show ?thesis using False p by (simp add: min_def)
qed


subsection \<open>The focus and the barring, read through the access\<close>

definition access_focus_goals :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g fset" where
  "access_focus_goals F V = ffilter (\<lambda>h. resolution_focused F (access_goal_position V h)) (access_goals V)"

text \<open>
  The access of the focused state keeps the goals at or under the focus, and counts at a position the goals of the
  focus at or under it: all of them at a position the focus lies under, none at a position apart from it.
\<close>

text \<open>
  The focused access at goals given (@{text access_focused_by}); the focused access is its instance at the focus's
  goals, and the shared state gives them as a range of its goal tree (task 892, @{text shared_focused}).
\<close>

definition access_focused_by :: "'g fset \<Rightarrow> 's list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow>
    ('g,'n,'k,'a,'s,'d,'c) search_access" where
  "access_focused_by G F V = V\<lparr>access_goals := G,
    access_goals_at := (\<lambda>q. if resolution_focused F q then access_goals_at V q else {||}),
    access_open := (\<lambda>q. case F of None \<Rightarrow> access_open V q
      | Some f \<Rightarrow> if take (length f) q = f then access_open V q
        else if take (length q) f = q \<and> G \<noteq> {||} then 1 else 0)\<rparr>"

definition access_focused :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access" where
  "access_focused F V = access_focused_by (access_focus_goals F V) F V"

lemma access_focused_simps [simp]:
  "access_goals (access_focused F V) = access_focus_goals F V"
  "access_goals_at (access_focused F V) q = (if resolution_focused F q then access_goals_at V q else {||})"
  "access_open (access_focused F V) q = (case F of None \<Rightarrow> access_open V q
      | Some f \<Rightarrow> if take (length f) q = f then access_open V q
        else if take (length q) f = q \<and> access_focus_goals F V \<noteq> {||} then 1 else 0)"
  "access_nodes_at (access_focused F V) = access_nodes_at V"
  "access_goal (access_focused F V) = access_goal V"
  "access_node (access_focused F V) = access_node V"
  "access_goal_position (access_focused F V) = access_goal_position V"
  "access_node_position (access_focused F V) = access_node_position V"
  "access_variables (access_focused F V) = access_variables V"
  "access_alternatives (access_focused F V) = access_alternatives V"
  "access_is_call (access_focused F V) = access_is_call V"
  "access_solvable (access_focused F V) = access_solvable V"
  "access_leaf (access_focused F V) = access_leaf V"
  "access_key (access_focused F V) = access_key V"
  "access_closes (access_focused F V) = access_closes V"
  "access_same (access_focused F V) = access_same V"
  "access_goal_calls (access_focused F V) = access_goal_calls V"
  "access_node_calls (access_focused F V) = access_node_calls V"
  "access_holders (access_focused F V) = access_holders V"
  "access_free (access_focused F V) = access_free V"
  "access_value_none (access_focused F V) = access_value_none V"
  "access_registered (access_focused F V) = access_registered V"
  "access_holdable (access_focused F V) = access_holdable V"
  "access_call_variables (access_focused F V) = access_call_variables V"
  "access_witnesses (access_focused F V) = access_witnesses V"
  by (simp_all add: access_focused_def access_focused_by_def)

context access_formed
begin

lemma focus_goals: "fimage (access_goal V) (access_focus_goals F V) = finite_focus_pending F st"
proof (rule fset_eqI, rule iffI)
  fix g assume "g |\<in>| fimage (access_goal V) (access_focus_goals F V)"
  then obtain h where h: "h |\<in>| access_goals V" "resolution_focused F (access_goal_position V h)" "g = access_goal V h"
    by (auto simp: access_focus_goals_def)
  have "g |\<in>| resolution_pending st" using h(1,3) pending by simp
  then show "g |\<in>| finite_focus_pending F st" using h goal_position[OF h(1)] by (simp add: finite_focus_pending_focused)
next
  fix g assume g: "g |\<in>| finite_focus_pending F st"
  then have "g |\<in>| fimage (access_goal V) (access_goals V)" using pending by (simp add: finite_focus_pending_focused)
  then obtain h where h: "h |\<in>| access_goals V" "g = access_goal V h" by blast
  have "h |\<in>| access_focus_goals F V" using g h goal_position[OF h(1)] by (simp add: access_focus_goals_def finite_focus_pending_focused)
  then show "g |\<in>| fimage (access_goal V) (access_focus_goals F V)" using fimageI[of h "access_focus_goals F V" "access_goal V"] h(2) by simp
qed

lemma focus_goals_empty: "access_focus_goals F V = {||} \<longleftrightarrow> finite_focus_pending F st = {||}"
  using focus_goals[of F] fimage_is_fempty[of "access_goal V" "access_focus_goals F V"] by simp

lemma focused: "access_formed \<kappa> P (access_focused F V) (finite_focused F st)"
proof -
  have fp: "resolution_pending (finite_focused F st) = fimage (access_goal V) (access_focus_goals F V)"
    using focus_goals[of F] by (simp add: finite_focused_def)
  have fn: "resolution_nodes (finite_focused F st) = resolution_nodes st"
      "resolution_witnesses (finite_focused F st) = resolution_witnesses st"
    by (simp_all add: finite_focused_def)
  have held: "finite_held \<kappa> (finite_focused F st) g = finite_held \<kappa> st g" for g by (simp add: finite_held_def fn)
  have fb: "fBex (finite_focus_pending F st) (\<lambda>g. take (length p) (resolution_goal_position g) = p) \<longleftrightarrow>
      (case F of None \<Rightarrow> fBex (resolution_pending st) (\<lambda>g. take (length p) (resolution_goal_position g) = p)
        | Some f \<Rightarrow> if take (length f) p = f then fBex (resolution_pending st) (\<lambda>g. take (length p) (resolution_goal_position g) = p)
          else take (length p) f = p \<and> finite_focus_pending F st \<noteq> {||})" for p
  proof (cases F)
    case None
    then show ?thesis by simp
  next
    case (Some f)
    have fpend: "g |\<in>| finite_focus_pending F st \<longleftrightarrow> g |\<in>| resolution_pending st \<and> take (length f) (resolution_goal_position g) = f" for g
      using Some by (auto simp: finite_focus_pending_def)
    consider (under) "take (length f) p = f" | (above) "take (length f) p \<noteq> f" "take (length p) f = p"
      | (apart) "take (length f) p \<noteq> f" "take (length p) f \<noteq> p" by blast
    then show ?thesis
    proof cases
      case under
      have "take (length p) (resolution_goal_position g) = p \<Longrightarrow> take (length f) (resolution_goal_position g) = f" for g
        using resolution_focused_within[where F="Some f" for f, unfolded resolution_focused_some, OF under] by blast
      then show ?thesis using Some under fpend by auto
    next
      case above
      have "take (length f) (resolution_goal_position g) = f \<Longrightarrow> take (length p) (resolution_goal_position g) = p" for g
        using resolution_focused_within[where F="Some f" for f, unfolded resolution_focused_some, OF above(2)] by blast
      then show ?thesis using Some above fpend by (auto simp: fset_eq_iff)
    next
      case apart
      have "\<not> (take (length f) (resolution_goal_position g) = f \<and> take (length p) (resolution_goal_position g) = p)" for g
        using take_prefix_cases[of f "resolution_goal_position g" p] apart by blast
      then show ?thesis using Some apart fpend by auto
    qed
  qed
  have solved_f: "access_open (access_focused F V) (resolution_node_position nd) = 0 \<longleftrightarrow> finite_solved_node (finite_focused F st) nd"
    if nd: "nd |\<in>| resolution_nodes st" for nd
    using fb[of "resolution_node_position nd"] solved[OF nd] focus_goals_empty[of F]
    by (cases F) (simp_all add: finite_solved_node_def finite_focused_def)
  show ?thesis
    apply unfold_locales
    subgoal using fp by simp
    subgoal for h q using goals_at[of h q] by (auto simp: access_focus_goals_def)
    subgoal for h h' using goal_inj by (simp add: access_focus_goals_def)
    subgoal for h using goal_position by (simp add: access_focus_goals_def)
    subgoal for h using variables by (simp add: access_focus_goals_def)
    subgoal for h using alternatives by (simp add: access_focus_goals_def)
    subgoal for h using is_call by (simp add: access_focus_goals_def)
    subgoal for h using solvable by (simp add: access_focus_goals_def)
    subgoal for h using leaf by (simp add: access_focus_goals_def)
    subgoal for n q using node_call_variables by simp
    subgoal for h using holdable by (simp add: access_focus_goals_def held)
    subgoal for nd using nodes by (simp add: fn)
    subgoal for n q using node_at by simp
    subgoal for n q using free by simp
    subgoal for n q a using value_none by simp
    subgoal for h q rr d p n q' using closes by (simp add: access_focus_goals_def)
    subgoal for h q rr d p n q' using node_calls by (simp add: access_focus_goals_def)
    subgoal for h h' q rr d p using same by (simp add: access_focus_goals_def)
    subgoal for h h' q rr d p using goal_calls by (simp add: access_focus_goals_def)
    subgoal for nd using solved_f by (simp add: fn)
    subgoal for h x using holders by (simp add: access_focus_goals_def)
    subgoal for g z b using registered[of g z b] finite_focus_pending_subset[of F st] by (auto simp: finite_focused_def)
    subgoal using witnesses by (simp add: fn)
    done
qed

lemma node_positions: "q |\<in>| fimage resolution_node_position (resolution_nodes st) \<longleftrightarrow> access_nodes_at V q \<noteq> {||}"
proof
  assume "q |\<in>| fimage resolution_node_position (resolution_nodes st)"
  then obtain nd where nd: "nd |\<in>| resolution_nodes st" "q = resolution_node_position nd" by blast
  obtain n where "n |\<in>| access_nodes_at V (resolution_node_position nd)" by (rule node_set_at[OF nd(1)])
  then show "access_nodes_at V q \<noteq> {||}" using nd(2) by auto
next
  assume "access_nodes_at V q \<noteq> {||}"
  then obtain n where n: "n |\<in>| access_nodes_at V q" by blast
  show "q |\<in>| fimage resolution_node_position (resolution_nodes st)"
    using fimageI[OF node_in[OF n], of resolution_node_position] node_at[OF n] by simp
qed

end

subsection \<open>The committed operations a representation writes\<close>

text \<open>
  A committed representation is R3's representation with the committed step's own writes: the positions of the
  state's nodes, the successors of a call at the focus (its clause alternatives, without reuse), the successors of a
  material premise at given solutions, the state under a substitution identical outside a given set of variables, and
  the representation of a state its search found.
\<close>

record ('r,'g,'n,'k,'a,'s,'d,'c) committed_representation = "('r,'g,'n,'k,'a,'s,'d,'c) resolution_representation" +
  rep_node_positions :: "'r \<Rightarrow> 's list fset"
  rep_call_successors :: "'r \<Rightarrow> 'g \<Rightarrow> 'r fset"
  rep_solution_successors :: "'r \<Rightarrow> 'g \<Rightarrow> (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow> 'r fset"
  rep_substitute :: "'r \<Rightarrow> (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> 'r"
  rep_share :: "('a,'s,'d,'c) resolution_state \<Rightarrow> 'r"

text \<open>
  The production (R5f1) is read on the projection and written by the representation's substitution: the production's
  substitution binds only variables of the committed goal's pattern.
\<close>

lemma finite_production_substitution_outside:
  assumes "finite_production_substitution W p v = Some \<sigma>" and "a |\<notin>| finite_pattern_variables p"
  shows "\<sigma> a = Finite_Variable a"
  using assms by (auto simp: finite_production_substitution_def finite_output_substitution_def split: option.splits if_splits)

definition represented_produced ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      's list option \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> 'r" where
  "represented_produced R K F r st g = (case g of
      Resolution_Call_Goal q rr d p \<Rightarrow> (case commit_production K F st g of
          Some (W,v) \<Rightarrow> (case finite_production_substitution W p v of
              Some \<sigma> \<Rightarrow> rep_substitute R r \<sigma> (finite_pattern_variables p)
            | None \<Rightarrow> r)
        | None \<Rightarrow> r)
    | Resolution_Material_Goal q rr M \<Rightarrow> r)"

text \<open>
  The committed successors: a committed material premise's at its canonical solutions, a call's at the focus by its
  clause alternatives, any other goal's by R3's successors. Whether the material premise is committed is read on the
  projection by the step and passed in.
\<close>

definition represented_committed_successors ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> 's list option \<Rightarrow> bool \<Rightarrow> 'r \<Rightarrow>
      ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> 'r fset" where
  "represented_committed_successors R F cm r V h = (if cm then (case access_goal V h of
        Resolution_Material_Goal q rr M \<Rightarrow> (case finite_canonical_solutions M of
            Some Ws \<Rightarrow> rep_solution_successors R r h Ws
          | None \<Rightarrow> rep_successors R r h)
      | Resolution_Call_Goal q rr d p \<Rightarrow> rep_successors R r h)
    else if access_is_call V h \<and> F = Some (access_goal_position V h) then rep_call_successors R r h
    else rep_successors R r h)"

text \<open>
  The first join below a ground focus over the representation (task 821, K1): whether the call at the focus holds a
  variable, and the determinate key of a successor, are read through the access, as R5's step reads them on the state
  (@{text access_formed.focus_ground}, @{text access_formed.determinate_key}): no projection is made for them.
\<close>

definition access_focus_ground :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> bool" where
  "access_focus_ground F V = (case F of None \<Rightarrow> False | Some q \<Rightarrow>
    fBall (access_goals_at V q) (\<lambda>h. access_variables V h = {||}) \<and>
    fBall (access_nodes_at V q) (\<lambda>n. access_call_variables V n = {||}))"

definition access_determinate_key :: "'s list \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> nat" where
  "access_determinate_key q V = fcard (ffilter (\<lambda>h. take (length q) (access_goal_position V h) = q \<and>
    access_goal_position V h \<noteq> q \<and> access_variables V h \<noteq> {||}) (access_goals V))"

text \<open>
  The committed step at a goal: pruned among the unbarred nodes it is closed, among the barred ones cut; committing,
  its sub-search runs from the produced state with the goal's position as the focus and the states keeping the least
  answer are continued; otherwise its committed successors are searched. The commitment's tests read the projection
  @{text so}, made at the step where some goal is admitted by the guard, and are asked only of an admitted goal.
\<close>

definition represented_committed_goal_outcome ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow>
      ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('a,'s,'d,'c) resolution_state option \<Rightarrow> 'g \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome" where
  "represented_committed_goal_outcome R gd rec K F B r V so h =
    (if access_pruned_among (\<lambda>q. q |\<notin>| B) V h then Resolution_Outcome {||} {||}
     else if access_pruned_among (\<lambda>q. q |\<in>| B) V h then Resolution_Outcome {||} {|Resolution_Cut {|access_goal V h|}|}
     else if gd r h \<and> finite_goal_committing K F (the so) (access_goal V h) then
       (let g = access_goal V h; st = the so; q = resolution_goal_position g;
          sub = rec (Some q) (finite_goal_sub_barring K F B st g) (represented_produced R K F r st g) in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. rec F (finite_committed_barring B s) (rep_share R s)) (finite_kept q (resolution_found sub)))))
     else let cm = gd r h \<and> finite_material_committed K F (the so) (access_goal V h);
       S = represented_committed_successors R F cm r V h in
       if S = {||} then (if access_witnesses V = {||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (access_witnesses V) (access_goal V h)|})
       else if access_focus_ground F V
         then finite_first_outcome (rec F (if cm then B |\<union>| rep_node_positions R r else B))
           (finite_key_blocks (\<lambda>s'. access_determinate_key (resolution_goal_position (access_goal V h)) (rep_access R s')) S)
         else finite_outcome_union (fimage (rec F (if cm then B |\<union>| rep_node_positions R r else B)) S))"

text \<open>
  The committed step at a state: the selection at the priority reads the access of the focused state, a construction
  is made at the selected nodes in the focus with every node present barred, and each selected goal is stepped.
\<close>

definition represented_committed_step ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "represented_committed_step R pr gd \<kappa> K P rec F B r = (let V = rep_access R r;
      so = (if fBex (access_goals V) (gd r) then Some (rep_project R r) else None);
      fo = map_option (finite_focused F) so in
    case access_select (\<lambda>h. gd r h \<and> pr (the fo) (access_goal V h)) (access_focused F V) of
      Access_Construction N \<Rightarrow> (let M = ffilter (\<lambda>m. resolution_focused F (access_node_position V m)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))|}
        else finite_outcome_union (fimage (\<lambda>m. rec F (B |\<union>| rep_node_positions R r) (rep_construct R r m)) M))
    | Access_Goals G \<Rightarrow> finite_outcome_union (fimage (represented_committed_goal_outcome R gd rec K F B r V so) G)
    | Access_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))) (finite_unconstructed \<kappa> P (rep_project R r))))"

primrec represented_committed_search ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome" where
  "represented_committed_search R pr gd \<kappa> K P 0 F B r = (let V = rep_access R r; G = access_focus_goals F V in
    if G = {||} then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal V) G)|})"
| "represented_committed_search R pr gd \<kappa> K P (Suc n) F B r =
    (if access_focus_goals F (rep_access R r) = {||} then Resolution_Outcome {|rep_project R r|} {||}
     else represented_committed_step R pr gd \<kappa> K P (represented_committed_search R pr gd \<kappa> K P n) F B (rep_refresh R r))"

subsection \<open>The committed step over tests read through the access\<close>

text \<open>
  Task 869, fix (3) of task 830. The committed step reads, of a goal, the priority and the commitment's tests; F2c's
  step reads them on the projection of the state it steps. Here they are parameters (@{text committed_tests}), read
  at a representation, its access and a value the step prepares once: a goal's priority at the focus, whether a call
  is committed, whether a material premise is committed, the committed goal's position, sub-barring and produced
  representation, and the position whose determinate key joins a successor. The step projects nothing but the
  diagnosis of a branch that ends with nothing to select. F2c's step is its instance at the tests read on the
  projection (@{text projected_tests}, @{text represented_committed_step_tested}); the tests the route reads through
  the access are @{text Factor_Access_Commitments}'.
\<close>

record ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests =
  tests_prepare :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x"
  tests_priority :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> bool"
  tests_committing :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> bool"
  tests_material :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> bool"
  tests_produced :: "'s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow>
    's list \<times> 's list fset \<times> 'r"
  tests_position :: "'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> 's list"

definition tested_committed_goal_outcome ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome" where
  "tested_committed_goal_outcome R T gd rec F B r V x h =
    (if access_pruned_among (\<lambda>q. q |\<notin>| B) V h then Resolution_Outcome {||} {||}
     else if access_pruned_among (\<lambda>q. q |\<in>| B) V h then Resolution_Outcome {||} {|Resolution_Cut {|access_goal V h|}|}
     else if gd r h \<and> tests_committing T F r V x h then
       (case tests_produced T F B r V x h of (q,B',r') \<Rightarrow> let sub = rec (Some q) B' r' in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. rec F (finite_committed_barring B s) (rep_share R s)) (finite_kept q (resolution_found sub)))))
     else let cm = gd r h \<and> tests_material T F r V x h;
       S = represented_committed_successors R F cm r V h in
       if S = {||} then (if access_witnesses V = {||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (access_witnesses V) (access_goal V h)|})
       else if access_focus_ground F V
         then finite_first_outcome (rec F (if cm then B |\<union>| rep_node_positions R r else B))
           (finite_key_blocks (\<lambda>s'. access_determinate_key (tests_position T r V x h) (rep_access R s')) S)
         else finite_outcome_union (fimage (rec F (if cm then B |\<union>| rep_node_positions R r else B)) S))"

text \<open>
  The step selecting through a selection the representation gives (@{text selected_committed_step}): the selection and
  the value the goals' outcomes read are passed in, so that a representation keeping the selection's classes reads them
  rather than testing every goal of its focus. The tested step is its instance at the selection over the focused access
  and the prepared tests (@{text tested_committed_step}), the step stated once (task 891).
\<close>

definition selected_committed_step ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> ('n,'g) access_selection) \<Rightarrow>
      ('s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "selected_committed_step R T gd sel xp \<kappa> P rec F B r = (let V = rep_access R r; x = xp F r V in
    case sel F r V x of
      Access_Construction N \<Rightarrow> (let M = ffilter (\<lambda>m. resolution_focused F (access_node_position V m)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))|}
        else finite_outcome_union (fimage (\<lambda>m. rec F (B |\<union>| rep_node_positions R r) (rep_construct R r m)) M))
    | Access_Goals G \<Rightarrow> finite_outcome_union (fimage (tested_committed_goal_outcome R T gd rec F B r V x) G)
    | Access_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_focus_goals F V))) (finite_unconstructed \<kappa> P (rep_project R r))))"

definition tested_committed_step ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "tested_committed_step R T gd \<kappa> P rec F B r = selected_committed_step R T gd
    (\<lambda>F r V x. access_select (\<lambda>h. gd r h \<and> tests_priority T F r V x h) (access_focused F V)) (tests_prepare T) \<kappa> P rec F B r"

primrec tested_committed_search ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "tested_committed_search R T gd \<kappa> P 0 F B r = (let V = rep_access R r; G = access_focus_goals F V in
    if G = {||} then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal V) G)|})"
| "tested_committed_search R T gd \<kappa> P (Suc n) F B r =
    (if access_focus_goals F (rep_access R r) = {||} then Resolution_Outcome {|rep_project R r|} {||}
     else tested_committed_step R T gd \<kappa> P (tested_committed_search R T gd \<kappa> P n) F B (rep_refresh R r))"

text \<open>
  The tests read on the projection: the prepared value is the projection, made where some goal is admitted by the
  guard, and each test reads the commitment, the priority or the production on it. F2c's step, goal outcome and search
  are the step's at these tests.
\<close>

definition projected_tests ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('r,'g,'n,'k,'a,'s,'d,'c,('a,'s,'d,'c) resolution_state option) committed_tests" where
  "projected_tests R K pr gd = \<lparr>
    tests_prepare = (\<lambda>F r V. if fBex (access_goals V) (gd r) then Some (rep_project R r) else None),
    tests_priority = (\<lambda>F r V so h. pr (the (map_option (finite_focused F) so)) (access_goal V h)),
    tests_committing = (\<lambda>F r V so h. finite_goal_committing K F (the so) (access_goal V h)),
    tests_material = (\<lambda>F r V so h. finite_material_committed K F (the so) (access_goal V h)),
    tests_produced = (\<lambda>F B r V so h. (resolution_goal_position (access_goal V h),
      finite_goal_sub_barring K F B (the so) (access_goal V h), represented_produced R K F r (the so) (access_goal V h))),
    tests_position = (\<lambda>r V so h. resolution_goal_position (access_goal V h))\<rparr>"

lemma represented_committed_goal_outcome_tested:
  "represented_committed_goal_outcome R gd rec K F B r V so =
    tested_committed_goal_outcome R (projected_tests R K pr gd) gd rec F B r V so"
  by (rule ext) (simp add: represented_committed_goal_outcome_def tested_committed_goal_outcome_def projected_tests_def
    Let_def)

lemma represented_committed_step_tested:
  "represented_committed_step R pr gd \<kappa> K P rec F B r = tested_committed_step R (projected_tests R K pr gd) gd \<kappa> P rec F B r"
  unfolding represented_committed_step_def tested_committed_step_def selected_committed_step_def
    represented_committed_goal_outcome_tested[where pr=pr]
  by (simp add: projected_tests_def Let_def)

lemma represented_committed_search_tested:
  "represented_committed_search R pr gd \<kappa> K P n F B r =
    tested_committed_search R (projected_tests R K pr gd) gd \<kappa> P n F B r"
proof (induction n arbitrary: F B r)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "represented_committed_search R pr gd \<kappa> K P n = tested_committed_search R (projected_tests R K pr gd) gd \<kappa> P n"
    by (intro ext) (rule Suc.IH)
  then show ?case by (simp add: represented_committed_step_tested)
qed

text \<open>
  The search stops where the focus, read as the representation gives it, holds no goal. The tested step is the
  selected step at the selection over the focused access and the prepared tests (@{text tested_committed_step_selected}).
\<close>

primrec selected_committed_search ::
    "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('s list option \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow>
      ('s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> ('n,'g) access_selection) \<Rightarrow>
      ('s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "selected_committed_search R T gd em sel xp \<kappa> P 0 F B r = (if em F r then Resolution_Outcome {|rep_project R r|} {||}
    else let V = rep_access R r in Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal V) (access_focus_goals F V))|})"
| "selected_committed_search R T gd em sel xp \<kappa> P (Suc n) F B r = (if em F r then Resolution_Outcome {|rep_project R r|} {||}
    else selected_committed_step R T gd sel xp \<kappa> P (selected_committed_search R T gd em sel xp \<kappa> P n) F B (rep_refresh R r))"

lemma tested_committed_step_selected:
  "tested_committed_step R T gd \<kappa> P rec F B r = selected_committed_step R T gd
    (\<lambda>F r V x. access_select (\<lambda>h. gd r h \<and> tests_priority T F r V x h) (access_focused F V)) (tests_prepare T) \<kappa> P rec F B r"
  by (simp add: tested_committed_step_def selected_committed_step_def Let_def)
text \<open>The two reads through a formed access are those on the state.\<close>

context access_formed
begin

lemma focus_ground: "access_focus_ground F V \<longleftrightarrow> finite_focus_ground F st"
proof (cases F)
  case None
  then show ?thesis by (simp add: access_focus_ground_def)
next
  case (Some q)
  have g: "fBall (access_goals_at V q) (\<lambda>h. access_variables V h = {||}) \<longleftrightarrow>
      fBall (resolution_pending st) (\<lambda>g. resolution_goal_position g = q \<longrightarrow> resolution_goal_variables g = {||})"
    unfolding pending using goals_at goal_position variables by auto
  have n: "fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||}) \<longleftrightarrow>
      fBall (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<longrightarrow>
        finite_pattern_variables (resolution_node_call nd) = {||})"
  proof
    assume a: "fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||})"
    show "fBall (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<longrightarrow>
        finite_pattern_variables (resolution_node_call nd) = {||})"
    proof (intro fBallI impI)
      fix nd assume nd: "nd |\<in>| resolution_nodes st" and p: "resolution_node_position nd = q"
      from nd obtain m where "m |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V m = nd"
        using nodes by blast
      then show "finite_pattern_variables (resolution_node_call nd) = {||}" using a p by auto
    qed
  next
    assume a: "fBall (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<longrightarrow>
        finite_pattern_variables (resolution_node_call nd) = {||})"
    show "fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||})"
    proof (intro fBallI)
      fix m assume m: "m |\<in>| access_nodes_at V q"
      have p: "resolution_node_position (access_node V m) = q" using node_at[OF m] by blast
      have "access_node V m |\<in>| resolution_nodes st" using nodes m p by blast
      then show "finite_pattern_variables (resolution_node_call (access_node V m)) = {||}" using a p by blast
    qed
  qed
  have nc: "fBall (access_nodes_at V q) (\<lambda>n. access_call_variables V n = {||}) \<longleftrightarrow>
      fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||})"
  proof
    assume a: "fBall (access_nodes_at V q) (\<lambda>n. access_call_variables V n = {||})"
    show "fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||})"
    proof (intro fBallI)
      fix m assume m: "m |\<in>| access_nodes_at V q"
      then show "finite_pattern_variables (resolution_node_call (access_node V m)) = {||}"
        using a node_call_variables[OF m] by auto
    qed
  next
    assume a: "fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||})"
    show "fBall (access_nodes_at V q) (\<lambda>n. access_call_variables V n = {||})"
    proof (intro fBallI)
      fix m assume m: "m |\<in>| access_nodes_at V q"
      then show "access_call_variables V m = {||}" using a node_call_variables[OF m] by auto
    qed
  qed
  show ?thesis using Some g n nc by (simp add: access_focus_ground_def finite_focus_ground_def)
qed

lemma determinate_key: "access_determinate_key q V = finite_determinate_key q st"
proof -
  let ?P = "\<lambda>g. take (length q) (resolution_goal_position g) = q \<and> resolution_goal_position g \<noteq> q \<and>
    resolution_goal_variables g \<noteq> {||}"
  let ?H = "ffilter (\<lambda>h. ?P (access_goal V h)) (access_goals V)"
  have filt: "ffilter (\<lambda>h. take (length q) (access_goal_position V h) = q \<and> access_goal_position V h \<noteq> q \<and>
      access_variables V h \<noteq> {||}) (access_goals V) = ?H"
    by (rule ffilter_cong_on) (simp add: goal_position variables)
  have img: "ffilter ?P (resolution_pending st) = fimage (access_goal V) ?H"
    unfolding pending by (rule fimage_ffilter_value)
  have inj: "inj_on (access_goal V) (fset ?H)"
    by (rule inj_onI) (auto intro: goal_inj simp: ffilter.rep_eq)
  show ?thesis unfolding access_determinate_key_def finite_determinate_key_def filt img
    using inj by (simp add: fcard.rep_eq fimage.rep_eq card_image)
qed

end

text \<open>The first join is congruent in its parts and its key on the joined set, and commutes with an image of it.\<close>


lemma finite_first_outcome_blocks_cong:
  assumes key: "\<And>x. x |\<in>| X \<Longrightarrow> key x = key' x" and f: "\<And>x. x |\<in>| X \<Longrightarrow> f x = g x"
  shows "finite_first_outcome f (finite_key_blocks key X) = finite_first_outcome g (finite_key_blocks key' X)"
proof -
  have i: "fimage key X = fimage key' X" by (rule fset.map_cong0) (simp add: key)
  have "ffilter (\<lambda>x. key x = k) X = ffilter (\<lambda>x. key' x = k) X" for k by (rule ffilter_cong_on) (simp add: key)
  then have "finite_key_blocks key X = finite_key_blocks key' X" unfolding finite_key_blocks_def i by simp
  moreover have "finite_first_outcome f (finite_key_blocks key' X) = finite_first_outcome g (finite_key_blocks key' X)"
    by (rule finite_first_outcome_cong) (blast intro: f finite_key_blocks_subset)
  ultimately show ?thesis by simp
qed

lemma finite_outcome_union_image_found:
  assumes "y |\<in>| resolution_found (finite_outcome_union (fimage f X))"
  shows "\<exists>x. x |\<in>| X \<and> y |\<in>| resolution_found (f x)"
  using assms by (auto simp: finite_outcome_union_def resolution_fset_simps)

lemma finite_key_blocks_first_found:
  assumes "y |\<in>| resolution_found (finite_first_outcome f (finite_key_blocks key X))"
  shows "\<exists>x. x |\<in>| X \<and> y |\<in>| resolution_found (f x)"
proof -
  have "\<exists>Y x. Y \<in> set (finite_key_blocks key X) \<and> x |\<in>| Y \<and> y |\<in>| resolution_found (f x)"
    using assms by (rule finite_first_outcome_found)
  then show ?thesis using finite_key_blocks_subset by metis
qed

lemma finite_first_outcome_image:
  "finite_first_outcome f (map (fimage h) Ys) = finite_first_outcome (\<lambda>y. f (h y)) Ys"
  by (induction Ys) (simp_all add: Let_def fset.map_comp comp_def)

lemma finite_search_join_image:
  "finite_search_join F st key f (fimage h Y) = (if finite_focus_ground F st
    then finite_first_outcome (\<lambda>y. f (h y)) (finite_key_blocks (\<lambda>y. key (h y)) Y)
    else finite_outcome_union (fimage (\<lambda>y. f (h y)) Y))"
proof -
  have "finite_key_blocks key (fimage h Y) = map (fimage h) (finite_key_blocks (\<lambda>y. key (h y)) Y)"
    unfolding finite_key_blocks_def by (simp add: fset.map_comp comp_def fimage_ffilter_value)
  then show ?thesis by (simp add: finite_search_join_def finite_first_outcome_image fset.map_comp comp_def)
qed

section \<open>A formed committed representation searches as R5 does\<close>

text \<open>
  A committed representation is structured at an invariant of its states when its accesses are formed at their
  projections and its steps project to R5's and keep the invariant. It is formed at a guard and at tests read through
  the access when moreover every goal the guard does not admit is one no test of the commitment and no priority
  accepts at the projection of an invariant state, and the tests prepared at an admitted goal are the commitment's and
  the priority's there (@{text tested_representation_formed}); F2c's form asks the guard's refusal at every state and
  reads the tests on the projection (@{text committed_representation_formed}).
\<close>

locale committed_representation_structure_in =
  fixes R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme"
    and Fi :: "'r \<Rightarrow> bool"
    and \<kappa> :: "('a,'s,'d,'c) finite_witness_construction" and P :: "('a,'s,'d,'c) finite_schema_system"
    and \<Theta> :: "('a,'s,'d,'c) resolution_table"
  assumes access: "\<And>s. Fi s \<Longrightarrow> access_formed \<kappa> P (rep_access R s) (rep_project R s)"
    and refresh: "\<And>s. Fi s \<Longrightarrow> Fi (rep_refresh R s) \<and> rep_project R (rep_refresh R s) = rep_project R s"
    and construct: "\<And>s m q. Fi s \<Longrightarrow> m |\<in>| access_nodes_at (rep_access R s) q \<Longrightarrow> Fi (rep_construct R s m) \<and>
      rep_project R (rep_construct R s m) = finite_construction_step \<kappa> P (rep_project R s) (access_node (rep_access R s) m)"
    and successors: "\<And>s h. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      fimage (rep_project R) (rep_successors R s h) = finite_goal_successors_in \<Theta> P (rep_project R s) (access_goal (rep_access R s) h) \<and>
      (\<forall>s'. s' |\<in>| rep_successors R s h \<longrightarrow> Fi s')"
    and call: "\<And>s h q rr d p. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      access_goal (rep_access R s) h = Resolution_Call_Goal q rr d p \<Longrightarrow>
      fimage (rep_project R) (rep_call_successors R s h) = finite_call_successors P (rep_project R s) q rr d p \<and>
      (\<forall>s'. s' |\<in>| rep_call_successors R s h \<longrightarrow> Fi s')"
    and solution: "\<And>s h q rr M Ws. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      access_goal (rep_access R s) h = Resolution_Material_Goal q rr M \<Longrightarrow>
      fimage (rep_project R) (rep_solution_successors R s h Ws) = finite_solution_successors (rep_project R s) q rr M Ws \<and>
      (\<forall>s'. s' |\<in>| rep_solution_successors R s h Ws \<longrightarrow> Fi s')"
    and positions: "\<And>s q. Fi s \<Longrightarrow> q |\<in>| rep_node_positions R s \<longleftrightarrow> access_nodes_at (rep_access R s) q \<noteq> {||}"
    and substitute: "\<And>s \<sigma> D. Fi s \<Longrightarrow> (\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a) \<Longrightarrow>
      Fi (rep_substitute R s \<sigma> D) \<and> rep_project R (rep_substitute R s \<sigma> D) = resolution_state_substitute \<sigma> (rep_project R s)"
    and share: "\<And>s. Fi s \<Longrightarrow> Fi (rep_share R (rep_project R s)) \<and> rep_project R (rep_share R (rep_project R s)) = rep_project R s"
begin

lemma produced:
  assumes Fr: "Fi r"
  shows "Fi (represented_produced R K F r st g)"
    and "rep_project R (represented_produced R K F r (rep_project R r) g) = finite_produced_state K F (rep_project R r) g"
proof -
  have sub: "Fi (rep_substitute R r \<sigma> (finite_pattern_variables p)) \<and>
      rep_project R (rep_substitute R r \<sigma> (finite_pattern_variables p)) = resolution_state_substitute \<sigma> (rep_project R r)"
    if "finite_production_substitution W p v = Some \<sigma>" for W p v \<sigma>
    by (rule substitute[OF Fr]) (rule finite_production_substitution_outside[OF that])
  show "Fi (represented_produced R K F r st g)"
    using Fr by (auto simp: sub represented_produced_def split: resolution_goal.splits option.splits prod.splits)
  show "rep_project R (represented_produced R K F r (rep_project R r) g) = finite_produced_state K F (rep_project R r) g"
    by (auto simp: sub represented_produced_def finite_produced_state_def split: resolution_goal.splits option.splits prod.splits)
qed

lemma committed_successors:
  assumes Fr: "Fi r" and h: "h |\<in>| access_goals (rep_access R r)"
  shows "fimage (rep_project R) (represented_committed_successors R F
      (finite_material_committed K F (rep_project R r) (access_goal (rep_access R r) h)) r (rep_access R r) h) =
    finite_committed_successors_in \<Theta> K P F (rep_project R r) (access_goal (rep_access R r) h)"
    and "s' |\<in>| represented_committed_successors R F cm r (rep_access R r) h \<Longrightarrow> Fi s'"
proof -
  let ?V = "rep_access R r" let ?st = "rep_project R r" let ?g = "access_goal ?V h"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  note sc = successors[OF Fr h]
  show "fimage (rep_project R) (represented_committed_successors R F (finite_material_committed K F ?st ?g) r ?V h) =
      finite_committed_successors_in \<Theta> K P F ?st ?g"
  proof (cases ?g)
    case (Resolution_Call_Goal q rr d p)
    have ic: "access_is_call ?V h" using v.is_call[OF h] Resolution_Call_Goal by simp
    have pos: "access_goal_position ?V h = q" using v.goal_position[OF h] Resolution_Call_Goal by simp
    show ?thesis using Resolution_Call_Goal ic pos sc call[OF Fr h Resolution_Call_Goal]
      by (cases "F = Some q")
        (simp_all add: represented_committed_successors_def finite_committed_successors_in_def finite_material_committed_def)
  next
    case (Resolution_Material_Goal q rr M)
    have ic: "\<not> access_is_call ?V h" using v.is_call[OF h] Resolution_Material_Goal by simp
    show ?thesis
    proof (cases "finite_canonical_solutions M")
      case None
      then show ?thesis using Resolution_Material_Goal ic sc
        by (simp add: represented_committed_successors_def finite_committed_successors_in_def finite_material_committed_def)
    next
      case (Some Ws)
      then show ?thesis using Resolution_Material_Goal ic sc solution[OF Fr h Resolution_Material_Goal, of Ws]
        by (cases "commit_material K F ?st (Resolution_Material_Goal q rr M)")
          (simp_all add: represented_committed_successors_def finite_committed_successors_in_def finite_material_committed_def)
    qed
  qed
  show "Fi s'" if s': "s' |\<in>| represented_committed_successors R F cm r ?V h"
  proof (cases ?g)
    case (Resolution_Call_Goal q rr d p)
    then show ?thesis using s' sc call[OF Fr h Resolution_Call_Goal] v.is_call[OF h]
      by (auto simp: represented_committed_successors_def split: if_splits)
  next
    case (Resolution_Material_Goal q rr M)
    then show ?thesis using s' sc solution[OF Fr h Resolution_Material_Goal] v.is_call[OF h]
      by (auto simp: represented_committed_successors_def split: if_splits option.splits)
  qed
qed

end

locale committed_representation_structure =
  fixes R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme"
    and Fi :: "'r \<Rightarrow> bool"
    and \<kappa> :: "('a,'s,'d,'c) finite_witness_construction" and P :: "('a,'s,'d,'c) finite_schema_system"
  assumes access: "\<And>s. Fi s \<Longrightarrow> access_formed \<kappa> P (rep_access R s) (rep_project R s)"
    and refresh: "\<And>s. Fi s \<Longrightarrow> Fi (rep_refresh R s) \<and> rep_project R (rep_refresh R s) = rep_project R s"
    and construct: "\<And>s m q. Fi s \<Longrightarrow> m |\<in>| access_nodes_at (rep_access R s) q \<Longrightarrow> Fi (rep_construct R s m) \<and>
      rep_project R (rep_construct R s m) = finite_construction_step \<kappa> P (rep_project R s) (access_node (rep_access R s) m)"
    and successors: "\<And>s h. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      fimage (rep_project R) (rep_successors R s h) = finite_goal_successors P (rep_project R s) (access_goal (rep_access R s) h) \<and>
      (\<forall>s'. s' |\<in>| rep_successors R s h \<longrightarrow> Fi s')"
    and call: "\<And>s h q rr d p. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      access_goal (rep_access R s) h = Resolution_Call_Goal q rr d p \<Longrightarrow>
      fimage (rep_project R) (rep_call_successors R s h) = finite_call_successors P (rep_project R s) q rr d p \<and>
      (\<forall>s'. s' |\<in>| rep_call_successors R s h \<longrightarrow> Fi s')"
    and solution: "\<And>s h q rr M Ws. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      access_goal (rep_access R s) h = Resolution_Material_Goal q rr M \<Longrightarrow>
      fimage (rep_project R) (rep_solution_successors R s h Ws) = finite_solution_successors (rep_project R s) q rr M Ws \<and>
      (\<forall>s'. s' |\<in>| rep_solution_successors R s h Ws \<longrightarrow> Fi s')"
    and positions: "\<And>s q. Fi s \<Longrightarrow> q |\<in>| rep_node_positions R s \<longleftrightarrow> access_nodes_at (rep_access R s) q \<noteq> {||}"
    and substitute: "\<And>s \<sigma> D. Fi s \<Longrightarrow> (\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a) \<Longrightarrow>
      Fi (rep_substitute R s \<sigma> D) \<and> rep_project R (rep_substitute R s \<sigma> D) = resolution_state_substitute \<sigma> (rep_project R s)"
    and share: "\<And>s. Fi s \<Longrightarrow> Fi (rep_share R (rep_project R s)) \<and> rep_project R (rep_share R (rep_project R s)) = rep_project R s"
begin

text \<open>A structure is the structure at the empty table, whose forms at a table are its forms.\<close>

sublocale structure_table: committed_representation_structure_in R Fi \<kappa> P resolution_empty_table
  by (rule committed_representation_structure_in.intro[OF access refresh construct successors call solution positions
    substitute share])

lemmas produced = structure_table.produced
lemmas committed_successors = structure_table.committed_successors

end

text \<open>
  Tests are exact at a goal and a prepared value when the priority at the focus, the call's and the material
  premise's commitment and the committed goal's production are the commitment's and the priority's at the projection.
\<close>

definition tests_exact_at ::
    "('r,'g,'n,'k,'a,'s,'d,'c,'z) committed_representation_scheme \<Rightarrow> ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow>
      ('r \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> 'g \<Rightarrow> bool" where
  "tests_exact_at R T Fi K pr F B r V x h \<longleftrightarrow> (let st = rep_project R r; g = access_goal V h in
    (h |\<in>| access_focus_goals F V \<longrightarrow> (tests_priority T F r V x h \<longleftrightarrow> pr (finite_focused F st) g)) \<and>
    (tests_committing T F r V x h \<longleftrightarrow> finite_goal_committing K F st g) \<and>
    (tests_material T F r V x h \<longleftrightarrow> finite_material_committed K F st g) \<and>
    (finite_goal_committing K F st g \<longrightarrow> (case tests_produced T F B r V x h of (q,B',r') \<Rightarrow>
      q = resolution_goal_position g \<and> B' = finite_goal_sub_barring K F B st g \<and> Fi r' \<and>
      rep_project R r' = finite_produced_state K F st g)))"

text \<open>
  The tested step at a table (GT3b, DECISIONS.md, task 495's entry, "The given's calls are decided once"): the selection
  reads a closing test through the access (@{const access_select_in}), the step stated once over the selected step. The
  tested step and search are its instances at the test closing nothing (@{text tested_committed_step_in_empty}).
\<close>

definition tested_committed_step_in ::
    "('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow>
      ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('s list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "tested_committed_step_in cl R T gd \<kappa> P rec F B r = selected_committed_step R T gd
    (\<lambda>F r V x. access_select_in (cl r) (\<lambda>h. gd r h \<and> tests_priority T F r V x h) (access_focused F V)) (tests_prepare T)
    \<kappa> P rec F B r"

primrec tested_committed_search_in ::
    "('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme \<Rightarrow>
      ('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      's list option \<Rightarrow> 's list fset \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "tested_committed_search_in cl R T gd \<kappa> P 0 F B r = (let V = rep_access R r; G = access_focus_goals F V in
    if G = {||} then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal V) G)|})"
| "tested_committed_search_in cl R T gd \<kappa> P (Suc n) F B r =
    (if access_focus_goals F (rep_access R r) = {||} then Resolution_Outcome {|rep_project R r|} {||}
     else tested_committed_step_in cl R T gd \<kappa> P (tested_committed_search_in cl R T gd \<kappa> P n) F B (rep_refresh R r))"


lemma tested_committed_step_in_empty: "tested_committed_step_in (\<lambda>r h. False) = tested_committed_step"
  by (intro ext) (simp only: tested_committed_step_in_def tested_committed_step_def access_select_in_empty)

lemma tested_committed_search_in_empty_at:
  "tested_committed_search_in (\<lambda>r h. False) R T gd \<kappa> P n = tested_committed_search R T gd \<kappa> P n"
proof (induction n)
  case 0
  show ?case by (intro ext) simp
next
  case (Suc n)
  show ?case by (intro ext) (simp only: tested_committed_search_in.simps tested_committed_search.simps Suc.IH
    tested_committed_step_in_empty)
qed

lemma tested_committed_search_in_empty: "tested_committed_search_in (\<lambda>r h. False) = tested_committed_search"
  by (intro ext) (simp only: tested_committed_search_in_empty_at)

locale tested_representation_formed_in = committed_representation_structure_in R Fi \<kappa> P \<Theta>
  for R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme" and Fi \<kappa> P \<Theta> +
  fixes K :: "('a,'s,'d,'c) resolution_commitment"
    and pr :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and T :: "('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests" and gd :: "'r \<Rightarrow> 'g \<Rightarrow> bool" and cl :: "'r \<Rightarrow> 'g \<Rightarrow> bool"
  assumes guard_at: "\<And>s h F. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F (rep_project R s) (access_goal (rep_access R s) h) \<and>
      \<not> commit_material K F (rep_project R s) (access_goal (rep_access R s) h) \<and>
      \<not> pr (finite_focused F (rep_project R s)) (access_goal (rep_access R s) h)"
    and prepared: "\<And>s h F B. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> gd s h \<Longrightarrow>
      tests_exact_at R T Fi K pr F B s (rep_access R s) (tests_prepare T F s (rep_access R s)) h"
    and position: "\<And>s h x. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      tests_position T s (rep_access R s) x h = resolution_goal_position (access_goal (rep_access R s) h)"
    and closes: "\<And>s h. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      cl s h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access R s) h)"
begin

lemma tested_goal_outcome:
  assumes Fr: "Fi r" and h: "h |\<in>| access_goals (rep_access R r)"
    and ex: "gd r h \<Longrightarrow> tests_exact_at R T Fi K pr F B r (rep_access R r) x h"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow> recI F' B' s = recA F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s y. Fi s \<Longrightarrow> y |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = y"
  shows "tested_committed_goal_outcome R T gd recI F B r (rep_access R r) x h =
    finite_committed_goal_outcome_in \<Theta> recA K P F B (rep_project R r) (access_goal (rep_access R r) h)"
proof -
  let ?V = "rep_access R r" let ?st = "rep_project R r" let ?g = "access_goal ?V h"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  have pu: "access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h \<longleftrightarrow> finite_pruned (finite_unbarred B ?st) ?g"
    using v.pruned_among[OF h, of "\<lambda>q. q |\<notin>| B"] by (simp add: finite_unbarred_def)
  have pb: "access_pruned_among (\<lambda>q. q |\<in>| B) ?V h \<longleftrightarrow> finite_pruned (finite_barred B ?st) ?g"
    using v.pruned_among[OF h, of "\<lambda>q. q |\<in>| B"] by (simp add: finite_barred_def)
  have ng: "\<not> gd r h \<Longrightarrow> \<not> commit_call K F ?st ?g \<and> \<not> commit_material K F ?st ?g"
    using guard_at[OF Fr h] by blast
  have comm: "(gd r h \<and> tests_committing T F r ?V x h) \<longleftrightarrow> finite_goal_committing K F ?st ?g"
  proof (cases "gd r h")
    case True
    then show ?thesis using ex[OF True] by (simp add: tests_exact_at_def Let_def)
  next
    case False
    then show ?thesis using ng by (simp add: finite_goal_committing_def)
  qed
  have cm: "(gd r h \<and> tests_material T F r ?V x h) \<longleftrightarrow> finite_material_committed K F ?st ?g"
  proof (cases "gd r h")
    case True
    then show ?thesis using ex[OF True] by (simp add: tests_exact_at_def Let_def)
  next
    case False
    then show ?thesis using ng by (cases ?g) (auto simp: finite_material_committed_def)
  qed
  have ps: "tests_position T r ?V x h = resolution_goal_position ?g" by (rule position[OF Fr h])
  have bar: "B |\<union>| rep_node_positions R r = finite_committed_barring B ?st"
  proof (rule fset_eqI)
    fix y show "y |\<in>| B |\<union>| rep_node_positions R r \<longleftrightarrow> y |\<in>| finite_committed_barring B ?st"
      using v.node_positions[of y] positions[OF Fr, of y] by (auto simp: finite_committed_barring_def)
  qed
  consider (closed) "finite_pruned (finite_unbarred B ?st) ?g"
    | (cut) "\<not> finite_pruned (finite_unbarred B ?st) ?g" "finite_pruned (finite_barred B ?st) ?g"
    | (unpruned) "\<not> finite_pruned (finite_unbarred B ?st) ?g" "\<not> finite_pruned (finite_barred B ?st) ?g" by blast
  then show ?thesis
  proof cases
    case closed
    then show ?thesis using pu by (simp add: tested_committed_goal_outcome_def finite_committed_goal_outcome_in_def)
  next
    case cut
    then show ?thesis using pu pb by (simp add: tested_committed_goal_outcome_def finite_committed_goal_outcome_in_def)
  next
    case unpruned
    have npu: "\<not> access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h" and npb: "\<not> access_pruned_among (\<lambda>q. q |\<in>| B) ?V h"
      using unpruned pu pb by simp_all
    show ?thesis
    proof (cases "finite_goal_committing K F ?st ?g")
      case True
      have c: "gd r h \<and> tests_committing T F r ?V x h" using True comm by simp
      obtain q B' r' where pd: "tests_produced T F B r ?V x h = (q,B',r')" by (metis prod_cases3)
      have pq: "q = resolution_goal_position ?g \<and> B' = finite_goal_sub_barring K F B ?st ?g \<and> Fi r' \<and>
          rep_project R r' = finite_produced_state K F ?st ?g"
        using ex[OF conjunct1[OF c]] True pd by (simp add: tests_exact_at_def Let_def)
      let ?q = "resolution_goal_position ?g" let ?B' = "finite_goal_sub_barring K F B ?st ?g"
      have pd': "tests_produced T F B r ?V x h = (?q,?B',r')" using pd pq by simp
      have Fr': "Fi r'" using pq by simp
      let ?subA = "recA (Some ?q) ?B' (finite_produced_state K F ?st ?g)"
      have sub: "recI (Some ?q) ?B' r' = ?subA" using rec[OF Fr', of "Some ?q" ?B'] pq by simp
      have kept: "fimage (\<lambda>s. recI F (finite_committed_barring B s) (rep_share R s)) (finite_kept ?q (resolution_found ?subA)) =
          fimage (\<lambda>s. recA F (finite_committed_barring B s) s) (finite_kept ?q (resolution_found ?subA))"
      proof (rule fset.map_cong0)
        fix s assume "s \<in> fset (finite_kept ?q (resolution_found ?subA))"
        then have "s |\<in>| resolution_found ?subA" using fsubsetD[OF finite_kept_subset] by blast
        then have "s |\<in>| resolution_found (recI (Some ?q) ?B' r')" using sub by simp
        then obtain r0 where r0: "Fi r0" "rep_project R r0 = s" using recfound[OF Fr'] by blast
        show "recI F (finite_committed_barring B s) (rep_share R s) = recA F (finite_committed_barring B s) s"
          using rec[OF conjunct1[OF share[OF r0(1)]]] conjunct2[OF share[OF r0(1)]] r0(2) by simp
      qed
      show ?thesis
        unfolding tested_committed_goal_outcome_def finite_committed_goal_outcome_eq_in Let_def
        by (simp only: if_not_P[OF npu] if_not_P[OF npb] if_P[OF c] pd' prod.case sub kept if_not_P[OF unpruned(1)]
          if_not_P[OF unpruned(2)] if_P[OF True])
    next
      case False
      have nc: "\<not> (gd r h \<and> tests_committing T F r ?V x h)" using False comm by simp
      let ?cm = "gd r h \<and> tests_material T F r ?V x h"
      let ?S = "represented_committed_successors R F ?cm r ?V h"
      have S0: "?S = represented_committed_successors R F (finite_material_committed K F ?st ?g) r ?V h" using cm by simp
      have S: "fimage (rep_project R) ?S = finite_committed_successors_in \<Theta> K P F ?st ?g"
        unfolding S0 by (rule committed_successors(1)[OF Fr h])
      have SF: "\<And>s'. s' |\<in>| ?S \<Longrightarrow> Fi s'" by (rule committed_successors(2)[OF Fr h])
      have gb: "(if ?cm then B |\<union>| rep_node_positions R r else B) = finite_goal_barring K F B ?st ?g"
        using cm bar by (simp add: finite_goal_barring_def)
      have e: "?S = {||} \<longleftrightarrow> finite_committed_successors_in \<Theta> K P F ?st ?g = {||}"
        using S fimage_is_fempty[of "rep_project R" ?S] by simp
      let ?Bc = "if ?cm then B |\<union>| rep_node_positions R r else B"
      let ?q = "resolution_goal_position ?g"
      have kS: "access_determinate_key ?q (rep_access R s') = finite_determinate_key ?q (rep_project R s')"
        if "s' |\<in>| ?S" for s'
      proof -
        interpret w: access_formed \<kappa> P "rep_access R s'" "rep_project R s'" by (rule access[OF SF[OF that]])
        show ?thesis by (rule w.determinate_key)
      qed
      have fS: "recI F ?Bc s' = recA F (finite_goal_barring K F B ?st ?g) (rep_project R s')" if "s' |\<in>| ?S" for s'
        using rec[OF SF[OF that]] gb by simp
      have fb: "finite_first_outcome (recI F ?Bc) (finite_key_blocks (\<lambda>s'. access_determinate_key ?q (rep_access R s')) ?S) =
          finite_first_outcome (\<lambda>y. recA F (finite_goal_barring K F B ?st ?g) (rep_project R y))
            (finite_key_blocks (\<lambda>y. finite_determinate_key ?q (rep_project R y)) ?S)"
        by (rule finite_first_outcome_blocks_cong) (simp_all add: kS fS)
      have im: "fimage (recI F ?Bc) ?S = fimage (\<lambda>y. recA F (finite_goal_barring K F B ?st ?g) (rep_project R y)) ?S"
        by (rule fset.map_cong0) (simp add: fS)
      have jn: "(if access_focus_ground F ?V
          then finite_first_outcome (recI F ?Bc) (finite_key_blocks (\<lambda>s'. access_determinate_key ?q (rep_access R s')) ?S)
          else finite_outcome_union (fimage (recI F ?Bc) ?S)) =
        finite_search_join F ?st (finite_determinate_key ?q) (recA F (finite_goal_barring K F B ?st ?g))
          (finite_committed_successors_in \<Theta> K P F ?st ?g)"
        unfolding S[symmetric] finite_search_join_image v.focus_ground fb im ..
      show ?thesis
        unfolding tested_committed_goal_outcome_def finite_committed_goal_outcome_eq_in Let_def ps
          if_not_P[OF npu] if_not_P[OF npb] if_not_P[OF nc] if_not_P[OF unpruned(1)] if_not_P[OF unpruned(2)]
          if_not_P[OF False]
        using jn e v.witnesses by simp
    qed
  qed
qed

lemma tested_step:
  assumes Fr: "Fi r" and ne: "finite_focus_pending F (rep_project R r) \<noteq> {||}"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow>
      recI F' B' s = finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P m F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  shows "tested_committed_step_in cl R T gd \<kappa> P recI F B r =
    finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P (Suc m) F B (rep_project R r)"
proof -
  let ?recA = "finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P m"
  let ?st = "rep_project R r" let ?V = "rep_access R r"
  let ?x = "tests_prepare T F r ?V"
  let ?rp = "\<lambda>h. gd r h \<and> tests_priority T F r ?V ?x h"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  interpret vf: access_formed \<kappa> P "access_focused F ?V" "finite_focused F ?st" by (rule v.focused)
  have rp: "?rp h \<longleftrightarrow> pr (finite_focused F ?st) (access_goal (access_focused F ?V) h)"
    if hf: "h |\<in>| access_goals (access_focused F ?V)" for h
  proof -
    have h: "h |\<in>| access_goals ?V" using hf by (simp add: access_focus_goals_def)
    have hF: "h |\<in>| access_focus_goals F ?V" using hf by simp
    show ?thesis
    proof (cases "gd r h")
      case True
      then show ?thesis using prepared[OF Fr h True, of F B] hF by (simp add: tests_exact_at_def Let_def)
    next
      case False
      then show ?thesis using guard_at[OF Fr h False, of F] by simp
    qed
  qed
  have E: "cl r h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (access_focused F ?V) h)"
    if hf: "h |\<in>| access_goals (access_focused F ?V)" for h
    using closes[OF Fr, of h] hf by (simp add: access_focus_goals_def)
  note sel = vf.select_in[where rp = ?rp and pr = pr and E = "cl r" and \<Theta> = \<Theta>, OF rp E]
  have fg: "fimage (access_goal ?V) (access_focus_goals F ?V) = finite_focus_pending F ?st" by (rule v.focus_goals)
  show ?thesis
  proof (cases "access_select_in (cl r) ?rp (access_focused F ?V)")
    case (Access_Construction N)
    have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (finite_focused F ?st) = Select_Construction (fimage (access_node ?V) N)"
      using sel(1) Access_Construction by simp
    have nd: "\<exists>q. m |\<in>| access_nodes_at ?V q" if m: "m |\<in>| N" for m
    proof -
      have "m |\<in>| access_construction_nodes (access_focused F ?V)" using Access_Construction m by (rule access_select_in_construction)
      then have "\<exists>q. m |\<in>| access_nodes_at (access_focused F ?V) q" by (rule access_construction_nodes_at)
      then show ?thesis by (simp only: access_focused_simps)
    qed
    have pm: "access_node_position ?V m = resolution_node_position (access_node ?V m)" if "m |\<in>| N" for m
    proof -
      from nd[OF that] obtain q where "m |\<in>| access_nodes_at ?V q" by (rule exE)
      then show ?thesis using v.node_at by simp
    qed
    let ?M = "ffilter (\<lambda>m. resolution_focused F (access_node_position ?V m)) N"
    have M0: "?M = ffilter (\<lambda>m. resolution_focused F (resolution_node_position (access_node ?V m))) N"
      by (rule ffilter_cong_on) (simp add: pm)
    have M: "ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) (fimage (access_node ?V) N) =
        fimage (access_node ?V) ?M"
      unfolding M0 by (rule fimage_ffilter_value)
    have bar: "B |\<union>| rep_node_positions R r = finite_committed_barring B ?st"
    proof (rule fset_eqI)
      fix x show "x |\<in>| B |\<union>| rep_node_positions R r \<longleftrightarrow> x |\<in>| finite_committed_barring B ?st"
        using v.node_positions[of x] positions[OF Fr, of x] by (auto simp: finite_committed_barring_def)
    qed
    have img: "fimage (\<lambda>m. recI F (B |\<union>| rep_node_positions R r) (rep_construct R r m)) ?M =
        fimage (?recA F (finite_committed_barring B ?st)) (fimage (finite_construction_step \<kappa> P ?st) (fimage (access_node ?V) ?M))"
      unfolding fset.map_comp comp_def
    proof (rule fset.map_cong0)
      fix m assume "m \<in> fset ?M"
      then have "m |\<in>| N" by simp
      from nd[OF this] obtain q where n: "m |\<in>| access_nodes_at ?V q" by (rule exE)
      note c = construct[OF Fr n]
      show "recI F (B |\<union>| rep_node_positions R r) (rep_construct R r m) =
          ?recA F (finite_committed_barring B ?st) (finite_construction_step \<kappa> P ?st (access_node ?V m))"
        using rec[OF conjunct1[OF c]] conjunct2[OF c] bar by simp
    qed
    show ?thesis
      unfolding tested_committed_step_in_def selected_committed_step_def Let_def Access_Construction finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s M img fg)
  next
    case (Access_Goals G)
    have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (finite_focused F ?st) = Select_Goals (fimage (access_goal ?V) G)"
      using sel(1) Access_Goals by simp
    have img: "fimage (tested_committed_goal_outcome R T gd recI F B r ?V ?x) G =
        fimage (finite_committed_goal_outcome_in \<Theta> ?recA K P F B ?st) (fimage (access_goal ?V) G)"
      unfolding fset.map_comp comp_def
    proof (rule fset.map_cong0)
      fix h assume hG: "h \<in> fset G"
      have "h |\<in>| access_goals (access_focused F ?V)" using Access_Goals hG by (rule access_select_in_goals)
      then have h: "h |\<in>| access_goals ?V" by (simp add: access_focus_goals_def)
      show "tested_committed_goal_outcome R T gd recI F B r ?V ?x h =
          finite_committed_goal_outcome_in \<Theta> ?recA K P F B ?st (access_goal ?V h)"
        by (rule tested_goal_outcome[where recA = ?recA and recI = recI, OF Fr h prepared[OF Fr h] rec recfound])
    qed
    show ?thesis
      unfolding tested_committed_step_in_def selected_committed_step_def Let_def Access_Goals finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s img)
  next
    case Access_None
    have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (finite_focused F ?st) = Select_None"
      using sel(1) Access_None by simp
    show ?thesis
      unfolding tested_committed_step_in_def selected_committed_step_def Let_def Access_None finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s fg)
  qed
qed

lemma tested_step_found:
  assumes Fr: "Fi r"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
    and x: "x |\<in>| resolution_found (tested_committed_step_in cl R T gd \<kappa> P recI F B r)"
  shows "\<exists>r0. Fi r0 \<and> rep_project R r0 = x"
proof -
  let ?V = "rep_access R r"
  let ?x = "tests_prepare T F r ?V"
  let ?rp = "\<lambda>h. gd r h \<and> tests_priority T F r ?V ?x h"
  have goal: "\<exists>r0. Fi r0 \<and> rep_project R r0 = y"
    if h: "h |\<in>| access_goals ?V" and y: "y |\<in>| resolution_found (tested_committed_goal_outcome R T gd recI F B r ?V ?x h)"
    for h y
  proof (cases "access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h \<or> access_pruned_among (\<lambda>q. q |\<in>| B) ?V h")
    case True
    then show ?thesis using y by (auto simp: tested_committed_goal_outcome_def split: if_splits)
  next
    case np: False
    show ?thesis
    proof (cases "gd r h \<and> tests_committing T F r ?V ?x h")
      case True
      obtain q B' r' where pd: "tests_produced T F B r ?V ?x h = (q,B',r')" by (metis prod_cases3)
      have ex: "tests_exact_at R T Fi K pr F B r ?V ?x h" by (rule prepared[OF Fr h conjunct1[OF True]])
      have fc: "finite_goal_committing K F (rep_project R r) (access_goal ?V h)"
        using ex True by (simp add: tests_exact_at_def Let_def)
      have Fr': "Fi r'" using ex fc pd by (simp add: tests_exact_at_def Let_def)
      let ?sub = "recI (Some q) B' r'"
      have "y |\<in>| resolution_found (finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses ?sub))
          (fimage (\<lambda>s. recI F (finite_committed_barring B s) (rep_share R s)) (finite_kept q (resolution_found ?sub)))))"
        using y np True pd by (simp add: tested_committed_goal_outcome_def Let_def)
      then obtain s where s: "s |\<in>| finite_kept q (resolution_found ?sub)"
        and ys: "y |\<in>| resolution_found (recI F (finite_committed_barring B s) (rep_share R s))"
        by (auto simp: finite_outcome_union_def)
      have "s |\<in>| resolution_found ?sub" by (rule fsubsetD[OF finite_kept_subset s])
      from recfound[OF Fr' this] obtain r0 where r0: "Fi r0 \<and> rep_project R r0 = s" by (rule exE)
      have "Fi (rep_share R s)" using share[OF conjunct1[OF r0]] conjunct2[OF r0] by simp
      from recfound[OF this ys] show ?thesis .
    next
      case nc: False
      let ?cm = "gd r h \<and> tests_material T F r ?V ?x h"
      let ?f = "recI F (if ?cm then B |\<union>| rep_node_positions R r else B)"
      let ?S = "represented_committed_successors R F ?cm r ?V h"
      let ?k = "\<lambda>s'. access_determinate_key (tests_position T r ?V ?x h) (rep_access R s')"
      have yj: "y |\<in>| resolution_found (if access_focus_ground F ?V
          then finite_first_outcome ?f (finite_key_blocks ?k ?S) else finite_outcome_union (fimage ?f ?S))"
        using y np nc by (auto simp: tested_committed_goal_outcome_def Let_def split: if_splits)
      have "\<exists>s'. s' |\<in>| ?S \<and> y |\<in>| resolution_found (?f s')"
      proof (cases "access_focus_ground F ?V")
        case True
        then have "y |\<in>| resolution_found (finite_first_outcome ?f (finite_key_blocks ?k ?S))" using yj by simp
        then show ?thesis by (rule finite_key_blocks_first_found)
      next
        case False
        then have "y |\<in>| resolution_found (finite_outcome_union (fimage ?f ?S))" using yj by simp
        then show ?thesis by (rule finite_outcome_union_image_found)
      qed
      then obtain s' where s': "s' |\<in>| represented_committed_successors R F ?cm r ?V h"
        and ys: "y |\<in>| resolution_found (recI F (if ?cm then B |\<union>| rep_node_positions R r else B) s')"
        by blast
      show ?thesis using recfound[OF committed_successors(2)[OF Fr h s'] ys] .
    qed
  qed
  show ?thesis
  proof (cases "access_select_in (cl r) ?rp (access_focused F ?V)")
    case (Access_Construction N)
    from x obtain m where m: "m |\<in>| N"
      and y: "x |\<in>| resolution_found (recI F (B |\<union>| rep_node_positions R r) (rep_construct R r m))"
      unfolding tested_committed_step_in_def selected_committed_step_def Let_def Access_Construction
      by (auto simp: finite_outcome_union_def split: if_splits)
    have "m |\<in>| access_construction_nodes (access_focused F ?V)" using Access_Construction m by (rule access_select_in_construction)
    then have "\<exists>q. m |\<in>| access_nodes_at (access_focused F ?V) q" by (rule access_construction_nodes_at)
    then have "\<exists>q. m |\<in>| access_nodes_at ?V q" by (simp only: access_focused_simps)
    then obtain q where n: "m |\<in>| access_nodes_at ?V q" by (rule exE)
    show ?thesis using recfound[OF conjunct1[OF construct[OF Fr n]] y] .
  next
    case (Access_Goals G)
    from x obtain h where hG: "h |\<in>| G"
      and y: "x |\<in>| resolution_found (tested_committed_goal_outcome R T gd recI F B r ?V ?x h)"
      unfolding tested_committed_step_in_def selected_committed_step_def Let_def Access_Goals by (auto simp: finite_outcome_union_def)
    have "h |\<in>| access_goals (access_focused F ?V)" using Access_Goals hG by (rule access_select_in_goals)
    then have h: "h |\<in>| access_goals ?V" by (simp add: access_focus_goals_def)
    show ?thesis by (rule goal[OF h y])
  next
    case Access_None
    then show ?thesis using x unfolding tested_committed_step_in_def selected_committed_step_def Let_def by simp
  qed
qed

lemma tested_found:
  assumes "Fi r" and "x |\<in>| resolution_found (tested_committed_search_in cl R T gd \<kappa> P n F B r)"
  shows "\<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  using assms
proof (induction n arbitrary: F B r x)
  case 0
  then show ?case by (auto simp: Let_def split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "access_focus_goals F (rep_access R r) = {||}")
    case True
    then show ?thesis using Suc.prems by auto
  next
    case False
    have f: "Fi (rep_refresh R r)" using refresh[OF Suc.prems(1)] by simp
    have x: "x |\<in>| resolution_found (tested_committed_step_in cl R T gd \<kappa> P
        (tested_committed_search_in cl R T gd \<kappa> P n) F B (rep_refresh R r))"
      using Suc.prems(2) False by simp
    show ?thesis
    proof (rule tested_step_found[OF f _ x])
      fix F' B' s y assume "Fi s" "y |\<in>| resolution_found (tested_committed_search_in cl R T gd \<kappa> P n F' B' s)"
      then show "\<exists>r0. Fi r0 \<and> rep_project R r0 = y" by (rule Suc.IH)
    qed
  qed
qed

theorem tested_search:
  assumes "Fi r"
  shows "tested_committed_search_in cl R T gd \<kappa> P n F B r =
    finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F B (rep_project R r)"
  using assms
proof (induction n arbitrary: F B r)
  case 0
  interpret v: access_formed \<kappa> P "rep_access R r" "rep_project R r" by (rule access[OF 0])
  show ?case using v.focus_goals[of F] v.focus_goals_empty[of F] by (simp add: Let_def)
next
  case (Suc n)
  have f: "Fi (rep_refresh R r)" and p: "rep_project R (rep_refresh R r) = rep_project R r"
    using refresh[OF Suc.prems] by simp_all
  interpret v: access_formed \<kappa> P "rep_access R r" "rep_project R r" by (rule access[OF Suc.prems])
  show ?case
  proof (cases "finite_focus_pending F (rep_project R r) = {||}")
    case True
    then show ?thesis using v.focus_goals_empty[of F] by simp
  next
    case False
    have ne: "access_focus_goals F (rep_access R r) \<noteq> {||}" using False v.focus_goals_empty[of F] by simp
    have e: "tested_committed_step_in cl R T gd \<kappa> P (tested_committed_search_in cl R T gd \<kappa> P n) F B (rep_refresh R r) =
        finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P (Suc n) F B (rep_project R (rep_refresh R r))"
    proof (rule tested_step)
      show "Fi (rep_refresh R r)" by (rule f)
    next
      show "finite_focus_pending F (rep_project R (rep_refresh R r)) \<noteq> {||}" using False p by simp
    next
      fix F' B' s assume "Fi s"
      then show "tested_committed_search_in cl R T gd \<kappa> P n F' B' s =
          finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F' B' (rep_project R s)" by (rule Suc.IH)
    next
      fix F' B' s x assume "Fi s" "x |\<in>| resolution_found (tested_committed_search_in cl R T gd \<kappa> P n F' B' s)"
      then show "\<exists>r0. Fi r0 \<and> rep_project R r0 = x" by (rule tested_found)
    qed
    have "tested_committed_search_in cl R T gd \<kappa> P (Suc n) F B r =
        tested_committed_step_in cl R T gd \<kappa> P (tested_committed_search_in cl R T gd \<kappa> P n) F B (rep_refresh R r)"
      using ne by simp
    then show ?thesis using e p by simp
  qed
qed

end

locale tested_representation_formed = committed_representation_structure R Fi \<kappa> P
  for R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme" and Fi \<kappa> P +
  fixes K :: "('a,'s,'d,'c) resolution_commitment"
    and pr :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and T :: "('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests" and gd :: "'r \<Rightarrow> 'g \<Rightarrow> bool"
  assumes guard_at: "\<And>s h F. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F (rep_project R s) (access_goal (rep_access R s) h) \<and>
      \<not> commit_material K F (rep_project R s) (access_goal (rep_access R s) h) \<and>
      \<not> pr (finite_focused F (rep_project R s)) (access_goal (rep_access R s) h)"
    and prepared: "\<And>s h F B. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> gd s h \<Longrightarrow>
      tests_exact_at R T Fi K pr F B s (rep_access R s) (tests_prepare T F s (rep_access R s)) h"
    and position: "\<And>s h x. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      tests_position T s (rep_access R s) x h = resolution_goal_position (access_goal (rep_access R s) h)"
begin

text \<open>The tested form at the empty table and the test closing nothing (@{text tested_representation_formed_in}).\<close>

sublocale tested_table: tested_representation_formed_in R Fi \<kappa> P resolution_empty_table K pr T gd "\<lambda>s h. False"
  by (rule tested_representation_formed_in.intro[OF committed_representation_structure_in.intro[OF access refresh construct
    successors call solution positions substitute share] tested_representation_formed_in_axioms.intro[OF guard_at prepared
    position]]) (simp_all add: finite_table_closes_empty)

lemmas tested_goal_outcome = tested_table.tested_goal_outcome
lemmas tested_step = tested_table.tested_step[unfolded tested_committed_step_in_empty]
lemmas tested_step_found = tested_table.tested_step_found[unfolded tested_committed_step_in_empty]
lemmas tested_found = tested_table.tested_found[unfolded tested_committed_search_in_empty]
lemmas tested_search = tested_table.tested_search[unfolded tested_committed_search_in_empty]

end

text \<open>
  A formed representation selects through what it gives when its selection at an invariant state is the tested
  step's, its focus reads empty exactly where the focused access holds no goal, and the goals' outcomes read the value
  it passes as they read the prepared tests. Its search is then R5's committed search (@{text selected_committed}), the
  tested search's value (@{text selected_tested}).
\<close>

locale selected_representation_formed_in = tested_representation_formed_in R Fi \<kappa> P \<Theta> K pr T gd cl
  for R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme" and Fi \<kappa> P \<Theta> K pr
    and T :: "('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests" and gd cl +
  fixes em :: "'s list option \<Rightarrow> 'r \<Rightarrow> bool"
    and sel :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> ('n,'g) access_selection"
    and xp :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x"
  assumes empty: "\<And>s F. Fi s \<Longrightarrow> em F s \<longleftrightarrow> access_focus_goals F (rep_access R s) = {||}"
    and select: "\<And>s F. Fi s \<Longrightarrow> sel F s (rep_access R s) (xp F s (rep_access R s)) =
      access_select_in (cl s) (\<lambda>h. gd s h \<and> tests_priority T F s (rep_access R s) (tests_prepare T F s (rep_access R s)) h)
        (access_focused F (rep_access R s))"
    and outcome: "\<And>s F B rec. Fi s \<Longrightarrow>
      tested_committed_goal_outcome R T gd rec F B s (rep_access R s) (xp F s (rep_access R s)) =
      tested_committed_goal_outcome R T gd rec F B s (rep_access R s) (tests_prepare T F s (rep_access R s))"
begin

lemma selected_step:
  assumes "Fi r"
  shows "selected_committed_step R T gd sel xp \<kappa> P rec F B r = tested_committed_step_in cl R T gd \<kappa> P rec F B r"
  unfolding tested_committed_step_in_def selected_committed_step_def Let_def select[OF assms] outcome[OF assms] ..

theorem selected_committed:
  assumes "Fi r"
  shows "selected_committed_search R T gd em sel xp \<kappa> P n F B r =
    finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F B (rep_project R r)"
  using assms
proof (induction n arbitrary: F B r)
  case 0
  have "selected_committed_search R T gd em sel xp \<kappa> P 0 F B r = tested_committed_search_in cl R T gd \<kappa> P 0 F B r"
    using empty[OF 0, of F] by (simp add: Let_def)
  also have "\<dots> = finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P 0 F B (rep_project R r)"
    by (rule tested_search[OF 0])
  finally show ?case .
next
  case (Suc n)
  have f: "Fi (rep_refresh R r)" and p: "rep_project R (rep_refresh R r) = rep_project R r"
    using refresh[OF Suc.prems] by simp_all
  interpret v: access_formed \<kappa> P "rep_access R r" "rep_project R r" by (rule access[OF Suc.prems])
  show ?case
  proof (cases "em F r")
    case True
    then have "finite_focus_pending F (rep_project R r) = {||}"
      using empty[OF Suc.prems, of F] v.focus_goals_empty[of F] by simp
    then show ?thesis using True by simp
  next
    case False
    have ne: "finite_focus_pending F (rep_project R (rep_refresh R r)) \<noteq> {||}"
      using False empty[OF Suc.prems, of F] v.focus_goals_empty[of F] p by simp
    have e: "tested_committed_step_in cl R T gd \<kappa> P (selected_committed_search R T gd em sel xp \<kappa> P n) F B (rep_refresh R r) =
        finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P (Suc n) F B (rep_project R (rep_refresh R r))"
    proof (rule tested_step[OF f ne])
      fix F' B' s assume "Fi s"
      then show "selected_committed_search R T gd em sel xp \<kappa> P n F' B' s =
          finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F' B' (rep_project R s)"
        by (rule Suc.IH)
    next
      fix F' B' s y assume s: "Fi s"
        and y: "y |\<in>| resolution_found (selected_committed_search R T gd em sel xp \<kappa> P n F' B' s)"
      have "selected_committed_search R T gd em sel xp \<kappa> P n F' B' s = tested_committed_search_in cl R T gd \<kappa> P n F' B' s"
        using Suc.IH[OF s] tested_search[OF s] by simp
      then have "y |\<in>| resolution_found (tested_committed_search_in cl R T gd \<kappa> P n F' B' s)" using y by simp
      then show "\<exists>r0. Fi r0 \<and> rep_project R r0 = y" by (rule tested_found[OF s])
    qed
    have "selected_committed_search R T gd em sel xp \<kappa> P (Suc n) F B r =
        tested_committed_step_in cl R T gd \<kappa> P (selected_committed_search R T gd em sel xp \<kappa> P n) F B (rep_refresh R r)"
      using False selected_step[OF f] by simp
    then show ?thesis using e p by simp
  qed
qed

corollary selected_tested:
  assumes "Fi r"
  shows "selected_committed_search R T gd em sel xp \<kappa> P n F B r = tested_committed_search_in cl R T gd \<kappa> P n F B r"
  using selected_committed[OF assms] tested_search[OF assms] by simp

end

locale selected_representation_formed = tested_representation_formed R Fi \<kappa> P K pr T gd
  for R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme" and Fi \<kappa> P K pr
    and T :: "('r,'g,'n,'k,'a,'s,'d,'c,'x) committed_tests" and gd +
  fixes em :: "'s list option \<Rightarrow> 'r \<Rightarrow> bool"
    and sel :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x \<Rightarrow> ('n,'g) access_selection"
    and xp :: "'s list option \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'x"
  assumes empty: "\<And>s F. Fi s \<Longrightarrow> em F s \<longleftrightarrow> access_focus_goals F (rep_access R s) = {||}"
    and select: "\<And>s F. Fi s \<Longrightarrow> sel F s (rep_access R s) (xp F s (rep_access R s)) =
      access_select (\<lambda>h. gd s h \<and> tests_priority T F s (rep_access R s) (tests_prepare T F s (rep_access R s)) h)
        (access_focused F (rep_access R s))"
    and outcome: "\<And>s F B rec. Fi s \<Longrightarrow>
      tested_committed_goal_outcome R T gd rec F B s (rep_access R s) (xp F s (rep_access R s)) =
      tested_committed_goal_outcome R T gd rec F B s (rep_access R s) (tests_prepare T F s (rep_access R s))"
begin

sublocale selected_table: selected_representation_formed_in R Fi \<kappa> P resolution_empty_table K pr T gd "\<lambda>s h. False"
    em sel xp
proof (rule selected_representation_formed_in.intro)
  show "tested_representation_formed_in R Fi \<kappa> P resolution_empty_table K pr T gd (\<lambda>s h. False)"
    by (rule tested_representation_formed_in.intro[OF committed_representation_structure_in.intro[OF access refresh
      construct successors call solution positions substitute share] tested_representation_formed_in_axioms.intro[OF
      guard_at prepared position]]) (simp_all add: finite_table_closes_empty)
qed (rule selected_representation_formed_in_axioms.intro; simp add: empty select outcome access_select_in_empty)

lemmas selected_step = selected_table.selected_step[unfolded tested_committed_step_in_empty]
lemmas selected_committed = selected_table.selected_committed
lemmas selected_tested = selected_table.selected_tested[unfolded tested_committed_search_in_empty]

end

lemma committed_representation_structure_in_empty:
  assumes "committed_representation_structure R Fi \<kappa> P"
  shows "committed_representation_structure_in R Fi \<kappa> P resolution_empty_table"
proof -
  interpret committed_representation_structure R Fi \<kappa> P by (rule assms)
  show ?thesis by (rule committed_representation_structure_in.intro[OF access refresh construct successors call solution
    positions substitute share])
qed

lemma committed_representation_structure_of_empty:
  assumes "committed_representation_structure_in R Fi \<kappa> P resolution_empty_table"
  shows "committed_representation_structure R Fi \<kappa> P"
proof -
  interpret committed_representation_structure_in R Fi \<kappa> P resolution_empty_table by (rule assms)
  show ?thesis by (rule committed_representation_structure.intro[OF access refresh construct successors call solution
    positions substitute share])
qed

lemma tested_representation_formed_of_empty:
  assumes "tested_representation_formed_in R Fi \<kappa> P resolution_empty_table K pr T gd cl"
  shows "tested_representation_formed R Fi \<kappa> P K pr T gd"
proof -
  interpret tested_representation_formed_in R Fi \<kappa> P resolution_empty_table K pr T gd cl by (rule assms)
  show ?thesis by (rule tested_representation_formed.intro[OF committed_representation_structure.intro[OF access refresh
    construct successors call solution positions substitute share] tested_representation_formed_axioms.intro[OF guard_at
    prepared position]])
qed

text \<open>
  A structure is kept at a further invariant of the representation's states that every step writing a state keeps.
\<close>

lemma committed_structure_kept:
  assumes st: "committed_representation_structure R Fi \<kappa> P"
    and refresh: "\<And>s. Fi s \<Longrightarrow> J s \<Longrightarrow> J (rep_refresh R s)"
    and construct: "\<And>s m q. Fi s \<Longrightarrow> J s \<Longrightarrow> m |\<in>| access_nodes_at (rep_access R s) q \<Longrightarrow> J (rep_construct R s m)"
    and successors: "\<And>s h s'. Fi s \<Longrightarrow> J s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      s' |\<in>| rep_successors R s h \<Longrightarrow> J s'"
    and call: "\<And>s h s'. Fi s \<Longrightarrow> J s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      s' |\<in>| rep_call_successors R s h \<Longrightarrow> J s'"
    and solution: "\<And>s h Ws s'. Fi s \<Longrightarrow> J s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      s' |\<in>| rep_solution_successors R s h Ws \<Longrightarrow> J s'"
    and substitute: "\<And>s \<sigma> D. Fi s \<Longrightarrow> J s \<Longrightarrow> (\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a) \<Longrightarrow>
      J (rep_substitute R s \<sigma> D)"
    and share: "\<And>s. Fi s \<Longrightarrow> J s \<Longrightarrow> J (rep_share R (rep_project R s))"
  shows "committed_representation_structure R (\<lambda>s. Fi s \<and> J s) \<kappa> P"
proof -
  interpret b: committed_representation_structure R Fi \<kappa> P by (rule st)
  show ?thesis
  proof (rule committed_representation_structure.intro, goal_cases)
    case (1 s) then show ?case using b.access by blast
  next
    case (2 s) then show ?case using b.refresh refresh by blast
  next
    case (3 s m q) then show ?case using b.construct construct by blast
  next
    case (4 s h) then show ?case using b.successors successors by blast
  next
    case (5 s h q rr d p) then show ?case using b.call call by blast
  next
    case (6 s h q rr M Ws) then show ?case using b.solution solution by blast
  next
    case (7 s q) then show ?case using b.positions by blast
  next
    case (8 s \<sigma> D) then show ?case using b.substitute substitute by blast
  next
    case (9 s) then show ?case using b.share share by blast
  qed
qed

text \<open>
  A structure strengthened by an invariant of the projected states that the steps' projections keep: the construction,
  a goal's successors, a call's at the focus, a committed material premise's and a substitution.
\<close>

lemma committed_structure_invariant_in:
  assumes st: "committed_representation_structure_in R Fi \<kappa> P \<Theta>"
    and construct: "\<And>s nd. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow> I (finite_construction_step \<kappa> P (rep_project R s) nd)"
    and successors: "\<And>s g st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow> g |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_goal_successors_in \<Theta> P (rep_project R s) g \<Longrightarrow> I st'"
    and call: "\<And>s q rr d p st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow>
      Resolution_Call_Goal q rr d p |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_call_successors P (rep_project R s) q rr d p \<Longrightarrow> I st'"
    and solution: "\<And>s q rr M Ws st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow>
      Resolution_Material_Goal q rr M |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_solution_successors (rep_project R s) q rr M Ws \<Longrightarrow> I st'"
    and substitute: "\<And>st \<sigma>. I st \<Longrightarrow> I (resolution_state_substitute \<sigma> st)"
  shows "committed_representation_structure_in R (\<lambda>s. Fi s \<and> I (rep_project R s)) \<kappa> P \<Theta>"
proof -
  interpret s: committed_representation_structure_in R Fi \<kappa> P \<Theta> by (rule st)
  have pend: "access_goal (rep_access R s) h |\<in>| resolution_pending (rep_project R s)"
    if "Fi s" "h |\<in>| access_goals (rep_access R s)" for s h
  proof -
    interpret v: access_formed \<kappa> P "rep_access R s" "rep_project R s" by (rule s.access[OF that(1)])
    show ?thesis by (rule v.goal_in_pending[OF that(2)])
  qed
  show ?thesis
  proof (rule committed_representation_structure_in.intro, goal_cases)
    case (1 s)
    then show ?case using s.access by blast
  next
    case (2 s)
    then show ?case using s.refresh[of s] by simp
  next
    case (3 s m q)
    then show ?case using s.construct[of s m q] construct[of s "access_node (rep_access R s) m"] by simp
  next
    case (4 s h)
    note c = s.successors[OF conjunct1[OF 4(1)] 4(2)]
    have i: "I (rep_project R s')" if s': "s' |\<in>| rep_successors R s h" for s'
    proof -
      have "rep_project R s' |\<in>| fimage (rep_project R) (rep_successors R s h)" using s' by (rule fimageI)
      then have "rep_project R s' |\<in>| finite_goal_successors_in \<Theta> P (rep_project R s) (access_goal (rep_access R s) h)"
        using c by simp
      then show ?thesis
        by (rule successors[OF conjunct1[OF 4(1)] conjunct2[OF 4(1)] pend[OF conjunct1[OF 4(1)] 4(2)]])
    qed
    show ?case using c i by blast
  next
    case (5 s h q rr d p)
    note c = s.call[OF conjunct1[OF 5(1)] 5(2) 5(3)]
    have g: "Resolution_Call_Goal q rr d p |\<in>| resolution_pending (rep_project R s)"
      using pend[OF conjunct1[OF 5(1)] 5(2)] 5(3) by simp
    have i: "I (rep_project R s')" if s': "s' |\<in>| rep_call_successors R s h" for s'
    proof -
      have "rep_project R s' |\<in>| fimage (rep_project R) (rep_call_successors R s h)" using s' by (rule fimageI)
      then have "rep_project R s' |\<in>| finite_call_successors P (rep_project R s) q rr d p" using c by simp
      then show ?thesis by (rule call[OF conjunct1[OF 5(1)] conjunct2[OF 5(1)] g])
    qed
    show ?case using c i by blast
  next
    case (6 s h q rr M Ws)
    note c = s.solution[OF conjunct1[OF 6(1)] 6(2) 6(3), of Ws]
    have g: "Resolution_Material_Goal q rr M |\<in>| resolution_pending (rep_project R s)"
      using pend[OF conjunct1[OF 6(1)] 6(2)] 6(3) by simp
    have i: "I (rep_project R s')" if s': "s' |\<in>| rep_solution_successors R s h Ws" for s'
    proof -
      have "rep_project R s' |\<in>| fimage (rep_project R) (rep_solution_successors R s h Ws)" using s' by (rule fimageI)
      then have "rep_project R s' |\<in>| finite_solution_successors (rep_project R s) q rr M Ws" using c by simp
      then show ?thesis by (rule solution[OF conjunct1[OF 6(1)] conjunct2[OF 6(1)] g])
    qed
    show ?case using c i by blast
  next
    case (7 s q)
    then show ?case using s.positions by blast
  next
    case (8 s \<sigma> D)
    then show ?case using s.substitute[OF conjunct1[OF 8(1)] 8(2)] substitute[OF conjunct2[OF 8(1)]] by simp
  next
    case (9 s)
    then show ?case using s.share[of s] by simp
  qed
qed

lemma committed_structure_invariant:
  assumes st: "committed_representation_structure R Fi \<kappa> P"
    and construct: "\<And>s nd. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow> I (finite_construction_step \<kappa> P (rep_project R s) nd)"
    and successors: "\<And>s g st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow> g |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_goal_successors P (rep_project R s) g \<Longrightarrow> I st'"
    and call: "\<And>s q rr d p st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow>
      Resolution_Call_Goal q rr d p |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_call_successors P (rep_project R s) q rr d p \<Longrightarrow> I st'"
    and solution: "\<And>s q rr M Ws st'. Fi s \<Longrightarrow> I (rep_project R s) \<Longrightarrow>
      Resolution_Material_Goal q rr M |\<in>| resolution_pending (rep_project R s) \<Longrightarrow>
      st' |\<in>| finite_solution_successors (rep_project R s) q rr M Ws \<Longrightarrow> I st'"
    and substitute: "\<And>st \<sigma>. I st \<Longrightarrow> I (resolution_state_substitute \<sigma> st)"
  shows "committed_representation_structure R (\<lambda>s. Fi s \<and> I (rep_project R s)) \<kappa> P"
proof -
  have "committed_representation_structure_in R (\<lambda>s. Fi s \<and> I (rep_project R s)) \<kappa> P resolution_empty_table"
    by (rule committed_structure_invariant_in[OF committed_representation_structure_in_empty[OF st] construct successors call
      solution substitute])
  then show ?thesis by (rule committed_representation_structure_of_empty)
qed

text \<open>
  F2c's form: the guard refuses at every state, and the tests are read on the projection. It is the tested form at
  @{const projected_tests} (@{text committed_representation_formed.tested}), and its step and search are the tested
  step's and search's there.
\<close>

locale committed_representation_formed = committed_representation_structure R Fi \<kappa> P
  for R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme" and Fi \<kappa> P +
  fixes K :: "('a,'s,'d,'c) resolution_commitment"
    and pr :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and gd :: "'r \<Rightarrow> 'g \<Rightarrow> bool"
  assumes guard: "\<And>s h F st. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (rep_access R s) h) \<and> \<not> commit_material K F st (access_goal (rep_access R s) h) \<and>
      \<not> pr st (access_goal (rep_access R s) h)"
begin

lemma projected_exact:
  assumes Fr: "Fi r" and so: "so = Some (rep_project R r)"
  shows "tests_exact_at R (projected_tests R K pr gd) Fi K pr F B r (rep_access R r) so h"
  using so by (simp add: tests_exact_at_def projected_tests_def Let_def produced[OF Fr])

lemma tested: "tested_representation_formed R Fi \<kappa> P K pr (projected_tests R K pr gd) gd"
proof (rule tested_representation_formed.intro[OF committed_representation_structure_axioms], unfold_locales, goal_cases)
  case (1 s h F)
  then show ?case using guard by blast
next
  case (2 s h F B)
  then have "tests_prepare (projected_tests R K pr gd) F s (rep_access R s) = Some (rep_project R s)"
    by (auto simp: projected_tests_def)
  then show ?case by (rule projected_exact[OF 2(1)])
next
  case (3 s h x)
  then show ?case by (simp add: projected_tests_def)
qed

lemma goal_outcome:
  assumes Fr: "Fi r" and h: "h |\<in>| access_goals (rep_access R r)"
    and so: "gd r h \<Longrightarrow> so = Some (rep_project R r)"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow> recI F' B' s = recA F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  shows "represented_committed_goal_outcome R gd recI K F B r (rep_access R r) so h =
    finite_committed_goal_outcome recA K P F B (rep_project R r) (access_goal (rep_access R r) h)"
proof -
  interpret t: tested_representation_formed R Fi \<kappa> P K pr "projected_tests R K pr gd" gd by (rule tested)
  have ex: "gd r h \<Longrightarrow> tests_exact_at R (projected_tests R K pr gd) Fi K pr F B r (rep_access R r) so h"
    by (rule projected_exact[OF Fr so])
  show ?thesis unfolding represented_committed_goal_outcome_tested[where pr=pr]
    by (rule t.tested_goal_outcome[where recA = recA and recI = recI, OF Fr h ex rec recfound])
qed

lemma step:
  assumes Fr: "Fi r" and ne: "finite_focus_pending F (rep_project R r) \<noteq> {||}"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow>
      recI F' B' s = finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P m F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  shows "represented_committed_step R pr gd \<kappa> K P recI F B r =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P (Suc m) F B (rep_project R r)"
proof -
  interpret t: tested_representation_formed R Fi \<kappa> P K pr "projected_tests R K pr gd" gd by (rule tested)
  show ?thesis unfolding represented_committed_step_tested by (rule t.tested_step[OF Fr ne rec recfound])
qed

lemma step_found:
  assumes Fr: "Fi r"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
    and x: "x |\<in>| resolution_found (represented_committed_step R pr gd \<kappa> K P recI F B r)"
  shows "\<exists>r0. Fi r0 \<and> rep_project R r0 = x"
proof -
  interpret t: tested_representation_formed R Fi \<kappa> P K pr "projected_tests R K pr gd" gd by (rule tested)
  show ?thesis by (rule t.tested_step_found[OF Fr recfound x[unfolded represented_committed_step_tested]])
qed

lemma found:
  assumes "Fi r" and "x |\<in>| resolution_found (represented_committed_search R pr gd \<kappa> K P n F B r)"
  shows "\<exists>r0. Fi r0 \<and> rep_project R r0 = x"
proof -
  interpret t: tested_representation_formed R Fi \<kappa> P K pr "projected_tests R K pr gd" gd by (rule tested)
  show ?thesis by (rule t.tested_found[OF assms(1) assms(2)[unfolded represented_committed_search_tested]])
qed

theorem search:
  assumes "Fi r"
  shows "represented_committed_search R pr gd \<kappa> K P n F B r =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B (rep_project R r)"
proof -
  interpret t: tested_representation_formed R Fi \<kappa> P K pr "projected_tests R K pr gd" gd by (rule tested)
  show ?thesis unfolding represented_committed_search_tested by (rule t.tested_search[OF assms])
qed
text \<open>At no commitment, the empty priority and no construction the committed search is R3's search over the representation.\<close>

theorem plain:
  assumes Fr: "Fi r" and K: "K = no_commitment" and pr: "pr = (\<lambda>st g. False)"
    and empty: "\<And>s. Fi s \<Longrightarrow> rep_empty R s \<longleftrightarrow> resolution_pending (rep_project R s) = {||}"
    and free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "represented_committed_search R pr gd \<kappa> K P n None {||} r =
    represented_search (resolution_representation.truncate R) (\<lambda>r h. False) \<kappa> P n r"
proof -
  let ?T = "resolution_representation.truncate R"
  have "represented_search ?T (\<lambda>r h. False) \<kappa> P n r =
      finite_resolution_search_by (finite_resolution_select_at (\<lambda>st g. False) \<kappa> P) \<kappa> P n (rep_project ?T r)"
  proof (rule represented_search[where F = Fi])
    show "Fi r" by (rule Fr)
  next
    fix s assume "Fi s"
    then show "access_formed \<kappa> P (rep_access ?T s) (rep_project ?T s)"
      using access by (simp add: resolution_representation.truncate_def)
  next
    fix s assume "Fi s"
    then show "rep_empty ?T s \<longleftrightarrow> resolution_pending (rep_project ?T s) = {||}"
      using empty by (simp add: resolution_representation.truncate_def)
  next
    fix s assume "Fi s"
    then show "Fi (rep_refresh ?T s) \<and> rep_project ?T (rep_refresh ?T s) = rep_project ?T s"
      using refresh by (simp add: resolution_representation.truncate_def)
  next
    fix s m assume f: "Fi s" and m: "m |\<in>| access_construction_nodes (rep_access ?T s)"
    obtain q where "m |\<in>| access_nodes_at (rep_access R s) q"
      using access_construction_nodes_at[OF m] by (auto simp: resolution_representation.truncate_def)
    then show "Fi (rep_construct ?T s m) \<and> rep_project ?T (rep_construct ?T s m) =
        finite_construction_step \<kappa> P (rep_project ?T s) (access_node (rep_access ?T s) m)"
      using construct[OF f] by (simp add: resolution_representation.truncate_def)
  next
    fix s h assume "Fi s" "h |\<in>| access_goals (rep_access ?T s)"
    then show "fimage (rep_project ?T) (rep_successors ?T s h) =
        finite_goal_successors P (rep_project ?T s) (access_goal (rep_access ?T s) h) \<and>
        (\<forall>s'. s' |\<in>| rep_successors ?T s h \<longrightarrow> Fi s')"
      using successors by (simp add: resolution_representation.truncate_def)
  next
    fix s h show "False \<longleftrightarrow> False" by simp
  qed
  moreover have "represented_committed_search R pr gd \<kappa> K P n None {||} r =
      finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> no_commitment P n None {||} (rep_project R r)"
    using search[OF Fr] K pr by simp
  ultimately show ?thesis using finite_committed_search_by_plain[OF free]
    by (simp add: resolution_representation.truncate_def)
qed

end

section \<open>The shared state's committed search\<close>

text \<open>
  The shared state writes the committed operations with its own steps: the node positions are its node tree's keys,
  a call's successors at the focus are its shared unifier's alternatives' states (@{const search_call_successors}), a
  committed material premise's are its solutions' shared alternatives' states (@{const search_solution_successors}), a
  substitution is shared first (@{const search_substitute_plain}), and a found state is shared again
  (@{const search_of}).
\<close>


lemma finite_solution_successors_alternatives:
  "finite_solution_successors st q rr M Ws =
    fimage (finite_material_alternative_state st q rr M) (finite_solution_alternatives M Ws)"
  unfolding finite_solution_successors_def by (rule finite_solution_alternatives_states)

definition shared_committed_representation :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) committed_representation" where
  "shared_committed_representation \<kappa> P = \<lparr>rep_access = shared_access \<kappa> P,
    rep_empty = (\<lambda>r. RBT.is_empty (shared_goals (search_state r))),
    rep_project = (\<lambda>r. search_project r), rep_refresh = search_refresh \<kappa> P, rep_construct = search_construct \<kappa> P,
    rep_successors = search_successors \<kappa> P,
    rep_node_positions = (\<lambda>r. fset_of_list (RBT.keys (shared_nodes (search_state r)))),
    rep_call_successors = (\<lambda>r h. case shared_entry_goal h of
        Shared_Call_Goal q rr d gp \<Rightarrow> search_call_successors P r q d gp
      | Shared_Material_Goal q rr gM \<Rightarrow> {||}),
    rep_solution_successors = (\<lambda>r h Ws. case shared_entry_goal h of
        Shared_Material_Goal q rr gM \<Rightarrow> search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws
      | Shared_Call_Goal q rr d gp \<Rightarrow> {||}),
    rep_substitute = (\<lambda>r \<sigma> D. search_substitute_plain P \<sigma> D r),
    rep_share = search_of P\<rparr>"

lemma shared_committed_truncate:
  "resolution_representation.truncate (shared_committed_representation \<kappa> P) = shared_representation \<kappa> P"
  by (simp add: resolution_representation.truncate_def shared_committed_representation_def shared_representation_def)

lemma shared_goal_at:
  assumes r: "search_formed \<kappa> P r" and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
    and g: "shared_goal_project (search_table r) (shared_entry_goal h) = g"
  shows "RBT.lookup (shared_goals (search_state r)) (resolution_goal_position g) = Some h"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have at: "RBT.lookup (shared_goals (search_state r)) (shared_goal_position (shared_entry_goal h)) = Some h"
    using h by (auto simp: shared_access_simps tree_values_member dest: shared_goal_lookup_position[OF s])
  have "shared_goal_position (shared_entry_goal h) = resolution_goal_position g"
    using arg_cong[OF g, of resolution_goal_position] by simp
  then show ?thesis using at by simp
qed

lemma shared_committed_structure:
  assumes sock: "clause_sockets_distinct P"
  shows "committed_representation_structure (shared_committed_representation \<kappa> P)
    (\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<kappa> P"
proof (rule committed_representation_structure.intro, goal_cases)
  case (1 s)
  then show ?case using shared_access_formed[of \<kappa> P s] by (simp add: shared_committed_representation_def)
next
  case (2 s)
  then show ?case using search_refresh[of \<kappa> P s] by (simp add: shared_committed_representation_def)
next
  case (3 s m q)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)"
    and n: "m |\<in>| access_nodes_at (shared_access \<kappa> P s) q"
    by (simp_all add: shared_committed_representation_def)
  note c = search_construct[OF f(1) n]
  have "search_placeable (search_project (search_construct \<kappa> P s m))"
    unfolding c(2) finite_construction_step_def Let_def
    by (rule search_placeable_substitute, rule search_placeable_witnesses[OF f(2)])
  then show ?case using c by (simp add: shared_committed_representation_def)
next
  case (4 s h)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P s)" by (simp_all add: shared_committed_representation_def)
  then show ?case using search_successors[OF f(1) f(2) sock h] by (simp add: shared_committed_representation_def)
next
  case (5 s h q rr d p)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P s)"
    and g: "shared_goal_project (search_table s) (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
    by (simp_all add: shared_committed_representation_def shared_access_simps)
  have atq: "RBT.lookup (shared_goals (search_state s)) q = Some h" using shared_goal_at[OF f(1) h g] by simp
  obtain gp where eg: "shared_entry_goal h = Shared_Call_Goal q rr d gp"
    and pp: "shared_pattern_project (search_table s) gp = p" using g by (cases "shared_entry_goal h") auto
  note c = search_call_successors[OF f(1) f(2) sock atq eg]
  have e: "fimage search_project (search_call_successors P s q d gp) = finite_call_successors P (search_project s) q rr d p"
    using c(1) pp by (simp add: finite_call_successors_alternatives)
  have fo: "search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
    if "s' |\<in>| search_call_successors P s q d gp" for s'
    using c(2)[OF that] .
  show ?case using e fo by (simp add: shared_committed_representation_def eg)
next
  case (6 s h q rr M Ws)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P s)"
    and g: "shared_goal_project (search_table s) (shared_entry_goal h) = Resolution_Material_Goal q rr M"
    by (simp_all add: shared_committed_representation_def shared_access_simps)
  have atq: "RBT.lookup (shared_goals (search_state s)) q = Some h" using shared_goal_at[OF f(1) h g] by simp
  obtain gM where eg: "shared_entry_goal h = Shared_Material_Goal q rr gM"
    and pM: "shared_material_project (search_table s) gM = M" using g by (cases "shared_entry_goal h") auto
  note c = search_solution_successors[where Ws = Ws, OF f(1) f(2) atq eg]
  have e: "fimage search_project (search_solution_successors P s q gM M Ws) = finite_solution_successors (search_project s) q rr M Ws"
    using c(1) pM by (simp add: finite_solution_successors_alternatives)
  have fo: "search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
    if "s' |\<in>| search_solution_successors P s q gM M Ws" for s'
    using c(2) that pM by simp
  show ?case using e fo pM by (simp add: shared_committed_representation_def eg)
next
  case (7 s q)
  have k: "q |\<in>| fset_of_list (RBT.keys (shared_nodes (search_state s))) \<longleftrightarrow> RBT.lookup (shared_nodes (search_state s)) q \<noteq> None"
    by (auto simp: fset_of_list_elem RBT.lookup_keys[symmetric])
  have o: "option_fset (RBT.lookup (shared_nodes (search_state s)) q) \<noteq> {||} \<longleftrightarrow> RBT.lookup (shared_nodes (search_state s)) q \<noteq> None"
    by (cases "RBT.lookup (shared_nodes (search_state s)) q") simp_all
  show ?case using k o by (simp add: shared_committed_representation_def shared_access_simps)
next
  case (8 s \<sigma> D)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a" by (simp_all add: shared_committed_representation_def)
  note k = search_substitute_plain[OF f(1) out]
  show ?case using k(1,2) search_placeable_substitute[OF f(2)] by (simp add: shared_committed_representation_def)
next
  case (9 s)
  then have f: "search_formed \<kappa> P s" "search_placeable (search_project s)" by (simp_all add: shared_committed_representation_def)
  have d: "resolution_positions_distinct (search_project s)" using f(2) by (simp add: search_placeable_def)
  show ?case using search_of[OF d] f(2) by (simp add: shared_committed_representation_def)
qed

lemma shared_committed_formed:
  assumes sock: "clause_sockets_distinct P"
    and guard: "\<And>s h F st. search_formed \<kappa> P s \<and> search_placeable (search_project s) \<Longrightarrow>
      h |\<in>| access_goals (shared_access \<kappa> P s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (shared_access \<kappa> P s) h) \<and>
      \<not> commit_material K F st (access_goal (shared_access \<kappa> P s) h) \<and> \<not> pr st (access_goal (shared_access \<kappa> P s) h)"
  shows "committed_representation_formed (shared_committed_representation \<kappa> P)
    (\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<kappa> P K pr gd"
proof (rule committed_representation_formed.intro[OF shared_committed_structure[OF sock]], unfold_locales, goal_cases)
  case (1 s h F st)
  then show ?case using guard by (simp add: shared_committed_representation_def)
qed

theorem shared_committed_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and guard: "\<And>s h F st. search_formed \<kappa> P s \<and> search_placeable (search_project s) \<Longrightarrow>
      h |\<in>| access_goals (shared_access \<kappa> P s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (shared_access \<kappa> P s) h) \<and>
      \<not> commit_material K F st (access_goal (shared_access \<kappa> P s) h) \<and> \<not> pr st (access_goal (shared_access \<kappa> P s) h)"
  shows "represented_committed_search (shared_committed_representation \<kappa> P) pr gd \<kappa> K P n F B (search_of P st) =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B st"
proof -
  interpret committed_representation_formed "shared_committed_representation \<kappa> P"
      "\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r)" \<kappa> P K pr gd
    by (rule shared_committed_formed[OF sock guard])
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have f: "search_formed \<kappa> P (search_of P st) \<and> search_placeable (search_project (search_of P st))"
    using search_of[OF d] pl by simp
  show ?thesis using search[OF f] search_of(2)[OF d] by (simp add: shared_committed_representation_def)
qed

text \<open>With every goal admitted by the guard the equation holds at every priority and commitment.\<close>

corollary shared_committed_search_admitted:
  assumes "clause_sockets_distinct P" and "search_placeable st"
  shows "represented_committed_search (shared_committed_representation \<kappa> P) pr (\<lambda>r h. True) \<kappa> K P n F B (search_of P st) =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B st"
  by (rule shared_committed_search[OF assms]) simp

corollary shared_committed_search_plain:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "represented_committed_search (shared_committed_representation \<kappa> P) (\<lambda>st g. False) gd \<kappa> no_commitment P n None {||}
      (search_of P st) = represented_search (shared_representation \<kappa> P) (\<lambda>r h. False) \<kappa> P n (search_of P st)"
proof -
  have e: "represented_committed_search (shared_committed_representation \<kappa> P) (\<lambda>st g. False) gd \<kappa> no_commitment P n None {||}
      (search_of P st) = finite_committed_search_by (finite_resolution_select_at (\<lambda>st g. False) \<kappa> P) \<kappa> no_commitment P n None {||} st"
    by (rule shared_committed_search[OF sock pl]) (simp add: no_commitment_def)
  show ?thesis using e shared_search[OF sock pl] finite_committed_search_by_plain[OF free]
    by (simp add: finite_resolution_search_def finite_resolution_search_in_def)
qed

text \<open>
  R5's committed search is computed over the shared state where the program's sockets are distinct and the state is
  placeable, every goal admitted by the guard, and as R5's elsewhere; the forms at the committed selection
  (@{const finite_committed_resolution}, @{const finite_committed_demand}, @{const native_committed_resolution}) take it.
  A selection at another priority takes its own equation from @{thm [source] shared_committed_search}.
\<close>

declare finite_committed_search_def [code del]

lemma finite_committed_search_shared_code [code]:
  "finite_committed_search \<kappa> K P n F B st = (if clause_sockets_distinct P \<and> search_placeable st
    then represented_committed_search (shared_committed_representation \<kappa> P) (finite_commitment_priority K) (\<lambda>r h. True)
      \<kappa> K P n F B (search_of P st)
    else finite_committed_search_by (finite_committed_select \<kappa> K P) \<kappa> K P n F B st)"
  by (simp add: finite_committed_search_def shared_committed_search_admitted)

subsection \<open>The shared state's committed step through its kept classes\<close>

text \<open>
  Task 871 (#830's fix (1) (b) in F2c). At the whole focus (none, or the root) the focused access is the state's own
  (@{text access_focused_whole}), and the committed step selects through the kept classes as the plain step does
  (#865's @{const search_select}): the settled and single classes read at once, the priority's class computed only when
  the kept settled class is empty, from the candidates the classes keep (@{text kept_select_by}). At a proper focus a
  node whose goals lie outside it counts as solved, so the kept settled and single tests are not the focused ones:
  there (task 892) the step reads the focus's goals and its candidates as one key range of the goal tree and of the
  kept candidate class, the positions under the focus (@{text shared_focused}, @{text focused_kept_select}), and
  recomputes the settled and single tests, which read the counts of open nodes and the goals at a position, at those
  candidates alone. The priority enters as a class, a function of the candidates
  rather than a test of each (@{text access_goal_choice_by}), so that what it reads of the whole focus is computed once
  a step, and only where the selection reaches it. The shared state's classes are kept by every committed step
  (@{text shared_kept_structure}), so the selection over them is the focused access's at every state the search
  reaches (@{text committed_kept_select}).
\<close>

lemma access_focused_whole:
  assumes "F = None \<or> F = Some []"
  shows "access_focused F V = V"
  by (cases V) (use assms in \<open>auto simp: access_focused_def access_focused_by_def access_focus_goals_def fun_eq_iff fset_eq_iff
    ffilter.rep_eq\<close>)

text \<open>
  The shared state gives the focused access's goals as the range of its goal tree under the focus
  (@{text shared_focused}), read through the index notion's range (@{text Ranged_Carrier_Indexes.tree_prefix}).
\<close>

text \<open>A range of a tree keyed by positions lists its values in the order of their positions.\<close>

lemma prefix_first:
  assumes pos: "\<And>p h. RBT.lookup t p = Some h \<Longrightarrow> pos h = p"
  shows "positioned_first pos (fset_of_list (filter X (map snd (tree_prefix t f)))) =
    (case find X (map snd (tree_prefix t f)) of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})"
proof -
  let ?E = "tree_prefix t f"
  have E: "map (\<lambda>z. pos (snd z)) ?E = map fst ?E"
  proof (rule map_cong[OF refl])
    fix z assume z: "z \<in> set ?E"
    obtain k v where zz: "z = (k,v)" by (cases z)
    have "RBT.lookup t k = Some v" using z unfolding zz by (simp add: tree_prefix(1))
    then show "pos (snd z) = fst z" using pos zz by simp
  qed
  have "sorted_wrt (<) (map (\<lambda>z. pos (snd z)) ?E)" unfolding E by (rule tree_prefix(2))
  then have "sorted_wrt (\<lambda>x y. finite_position_less (pos x) (pos y)) (map snd ?E)"
    by (simp add: sorted_wrt_map finite_position_less_list)
  then show ?thesis by (rule positioned_first_sorted)
qed

definition shared_focused :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access" where
  "shared_focused f r V = access_focused_by (fset_of_list (map snd (tree_prefix (shared_goals (search_state r)) f))) (Some f) V"

lemma shared_focused:
  assumes r: "search_formed \<kappa> P r"
  shows "shared_focused f r (shared_access \<kappa> P r) = access_focused (Some f) (shared_access \<kappa> P r)"
proof -
  let ?V = "shared_access \<kappa> P r" and ?G = "shared_goals (search_state r)"
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF r] .
  have "fset_of_list (map snd (tree_prefix ?G f)) = access_focus_goals (Some f) ?V"
  proof (rule fset_eqI)
    fix h
    show "h |\<in>| fset_of_list (map snd (tree_prefix ?G f)) \<longleftrightarrow> h |\<in>| access_focus_goals (Some f) ?V"
      by (auto simp: fset_of_list.rep_eq tree_prefix(3) access_focus_goals_def ffilter.rep_eq shared_access_simps
        tree_values_member dest: shared_goal_lookup_position[OF s])
  qed
  then show ?thesis by (simp only: shared_focused_def access_focused_def)
qed

text \<open>
  The committed selection at a proper focus: the construction nodes as the focused access reads them, then the first
  kept candidate under the focus that is settled there, the goals the priority's class names among the kept candidates
  under the focus, the first of them single there, and the waiting rule over the focus's goals not held back. The
  candidates are one range of the kept candidate class, listed in the order of positions; the settled and single tests
  are the focused access's, asked of those candidates alone. It is the focused access's selection at every formed search
  with formed classes (@{text focused_kept_select}).
\<close>

text \<open>
  The focused selection at a closed class @{text Z} (GT3b, task 970): a goal of the class closes the focus first, with
  the settled ones; at the empty class it is today's (@{text focused_kept_select_in_empty}), so today's reading is
  its instance (task 989).
\<close>

definition focused_kept_select_in :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow>
    's list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "focused_kept_select_in Z pc f r V W = (let N = access_construction_nodes W in
    if N \<noteq> {||} then Access_Construction (access_first_nodes W N)
    else let H = search_held_over V r; L = map snd (tree_prefix (class_candidates (search_classes r)) f);
      c0 = access_first_goals W ((case find (\<lambda>h. h |\<notin>| H \<and> access_settled W h) L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) |\<union>|
        (case find (\<lambda>h. h |\<notin>| H) (map snd (tree_prefix Z f)) of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}));
      S = (if c0 \<noteq> {||} then c0 else
        let cp = pc (fset_of_list (filter (\<lambda>h. h |\<notin>| H) L)) in
        if cp \<noteq> {||} then access_first_goals W cp else
        let c1 = (case find (\<lambda>h. h |\<notin>| H \<and> access_single W h) L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) in
        if c1 \<noteq> {||} then c1 else access_waiting_selection W (access_goals W |-| H)) in
      if S = {||} then Access_None else Access_Goals S)"

theorem focused_kept_select_over_in:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and Z: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state r)) p"
    and EC: "\<And>h. E h \<Longrightarrow> shared_goal_is_call (shared_entry_goal h)"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  assumes pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals (Some f) V) \<Longrightarrow> pc A = ffilter rp A"
  shows "focused_kept_select_in Z pc f r V (access_focused (Some f) V) = access_select_in E rp (access_focused (Some f) V)"
proof -
  let ?V = V and ?W = "access_focused (Some f) V"
  let ?s = "search_state r" and ?G = "shared_goals (search_state r)" and ?K = "search_classes r"
  let ?H = "search_held_over V r" and ?L = "map snd (tree_prefix (class_candidates (search_classes r)) f)"
  let ?Lz = "map snd (tree_prefix Z f)"
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tst: "access_candidate ?V h = access_candidate (state_access ?s) h \<and>
      access_settled ?V h = access_settled (state_access ?s) h \<and> access_single ?V h = access_single (state_access ?s) h" for h
    by (simp add: V_def shared_access_def Let_def access_candidate_def access_settled_def access_single_def
      access_pruned_def access_pruned_among_def access_reusable_def access_waits_def access_ground_def)
  have tc: "RBT.lookup (class_candidates ?K) p = class_value (access_candidate ?V) ?G p" for p
  proof (cases "RBT.lookup ?G p")
    case None
    then show ?thesis using K by (simp add: classes_formed_def class_value_def)
  next
    case (Some h)
    then show ?thesis using K kept_tests[OF r Some] tst[of h] by (simp add: classes_formed_def class_value_def)
  qed
  have posc: "access_goal_position ?W h = p" if "RBT.lookup (class_candidates ?K) p = Some h" for p h
  proof -
    have "RBT.lookup ?G p = Some h" using that tc[of p] by (auto simp: class_value_def split: option.splits if_splits)
    then show ?thesis using shared_goal_lookup_position[OF s] by (simp add: V_def shared_access_simps)
  qed
  have posz: "access_goal_position ?W h = p" if "RBT.lookup Z p = Some h" for p h
  proof -
    have "RBT.lookup ?G p = Some h" using that Z[of p] by (auto simp: class_value_def split: option.splits if_splits)
    then show ?thesis using shared_goal_lookup_position[OF s] by (simp add: V_def shared_access_simps)
  qed
  have cw: "access_candidate ?W h = access_candidate ?V h" for h by (simp add: access_candidate_def)
  have Vg: "access_goals V = access_goals (shared_access \<kappa> P r)"
    "access_goal_position V = access_goal_position (shared_access \<kappa> P r)" by (simp_all add: V_def)
  have Lmem: "h \<in> snd ` set (tree_prefix (class_candidates (search_classes r)) f) \<longleftrightarrow>
      h |\<in>| access_goals ?W \<and> access_candidate ?W h" for h
  proof -
    have "h \<in> snd ` set (tree_prefix (class_candidates (search_classes r)) f) \<longleftrightarrow>
        (\<exists>p. RBT.lookup ?G p = Some h \<and> access_candidate ?V h \<and> take (length f) p = f)"
      unfolding tree_prefix(3) tc by (auto simp: class_value_def split: option.splits if_splits)
    also have "\<dots> \<longleftrightarrow> h |\<in>| access_goals ?W \<and> access_candidate ?W h"
      by (auto simp: cw Vg access_focus_goals_def ffilter.rep_eq shared_access_simps tree_values_member
        dest: shared_goal_lookup_position[OF s])
    finally show ?thesis .
  qed
  have Zmem: "h \<in> snd ` set (tree_prefix Z f) \<longleftrightarrow> h |\<in>| access_goals ?W \<and> E h" for h
  proof -
    have "h \<in> snd ` set (tree_prefix Z f) \<longleftrightarrow> (\<exists>p. RBT.lookup ?G p = Some h \<and> E h \<and> take (length f) p = f)"
      unfolding tree_prefix(3) Z by (auto simp: class_value_def split: option.splits if_splits)
    also have "\<dots> \<longleftrightarrow> h |\<in>| access_goals ?W \<and> E h"
      by (auto simp: Vg access_focus_goals_def ffilter.rep_eq shared_access_simps tree_values_member
        dest: shared_goal_lookup_position[OF s])
    finally show ?thesis .
  qed
  have hs: "access_holdable ?W h = access_holdable ?V h" "access_held ?W h = access_held ?V h" for h
    by (simp_all add: access_held_def)
  have held: "?H = ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
    unfolding V_def by (rule search_held_over_nodes[OF r])
  have A: "ffilter (\<lambda>h. \<not> (access_holdable ?W h \<and> access_held ?W h)) (access_goals ?W) = access_goals ?W |-| ?H"
    by (rule fset_eqI) (auto simp: hs held ffilter.rep_eq access_focus_goals_def)
  have hc: "fset_of_list (filter (\<lambda>h. h |\<notin>| ?H) ?L) = ffilter (access_candidate ?W) (access_goals ?W |-| ?H)"
    by (rule fset_eqI) (auto simp: fset_of_list.rep_eq ffilter.rep_eq Lmem)
  have h0: "fset_of_list (filter (\<lambda>h. h |\<notin>| ?H \<and> access_settled ?W h) ?L) =
      ffilter (\<lambda>h. access_candidate ?W h \<and> access_settled ?W h) (access_goals ?W |-| ?H)"
    by (rule fset_eqI) (auto simp: fset_of_list.rep_eq ffilter.rep_eq Lmem)
  have hz: "fset_of_list (filter (\<lambda>h. h |\<notin>| ?H) ?Lz) = ffilter E (access_goals ?W |-| ?H)"
    by (rule fset_eqI) (auto simp: fset_of_list.rep_eq ffilter.rep_eq Zmem)
  have h1: "fset_of_list (filter (\<lambda>h. h |\<notin>| ?H \<and> access_single ?W h) ?L) =
      ffilter (\<lambda>h. access_candidate ?W h \<and> access_single ?W h) (access_goals ?W |-| ?H)"
    by (rule fset_eqI) (auto simp: fset_of_list.rep_eq ffilter.rep_eq Lmem)
  have first: "access_first_goals ?W (fset_of_list (filter X ?L)) = (case find X ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})"
    for X unfolding access_first_goals_def by (rule prefix_first) (rule posc)
  have firstz: "access_first_goals ?W (fset_of_list (filter X ?Lz)) = (case find X ?Lz of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})"
    for X unfolding access_first_goals_def by (rule prefix_first) (rule posz)
  have none: "((case find X ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) = {||}) = (fset_of_list (filter X ?L) = {||})" for X
  proof -
    have "((case find X ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) = {||}) = (find X ?L = None)"
      by (cases "find X ?L") simp_all
    also have "\<dots> = (fset_of_list (filter X ?L) = {||})" by (auto simp: find_None_iff fset_eq_iff fset_of_list.rep_eq)
    finally show ?thesis .
  qed
  have e0: "(case find (\<lambda>h. h |\<notin>| ?H \<and> access_settled ?W h) ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) =
      access_first_goals ?W (ffilter (\<lambda>h. access_candidate ?W h \<and> access_settled ?W h) (access_goals ?W |-| ?H))"
    by (simp only: first[symmetric] h0)
  have ez: "(case find (\<lambda>h. h |\<notin>| ?H) ?Lz of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) =
      access_first_goals ?W (ffilter E (access_goals ?W |-| ?H))"
    by (simp only: firstz[symmetric] hz)
  have e1: "(case find (\<lambda>h. h |\<notin>| ?H \<and> access_single ?W h) ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) =
      access_first_goals ?W (ffilter (\<lambda>h. access_candidate ?W h \<and> access_single ?W h) (access_goals ?W |-| ?H))"
    by (simp only: first[symmetric] h1)
  have n1: "(access_first_goals ?W (ffilter (\<lambda>h. access_candidate ?W h \<and> access_single ?W h) (access_goals ?W |-| ?H)) = {||}) =
      (ffilter (\<lambda>h. access_candidate ?W h \<and> access_single ?W h) (access_goals ?W |-| ?H) = {||})"
    by (simp only: h1[symmetric] first none)
  have cand: "access_candidate ?W h" if "E h" for h
    using EC[OF that] by (simp add: cw V_def access_candidate_def shared_access_simps)
  have un: "ffilter (\<lambda>h. access_candidate ?W h \<and> (access_settled ?W h \<or> E h)) (access_goals ?W |-| ?H) =
      ffilter (\<lambda>h. access_candidate ?W h \<and> access_settled ?W h) (access_goals ?W |-| ?H) |\<union>| ffilter E (access_goals ?W |-| ?H)"
    using cand by (auto simp: ffilter.rep_eq)
  have c0: "access_first_goals ?W ((case find (\<lambda>h. h |\<notin>| ?H \<and> access_settled ?W h) ?L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) |\<union>|
        (case find (\<lambda>h. h |\<notin>| ?H) ?Lz of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})) =
      access_first_goals ?W (ffilter (\<lambda>h. access_candidate ?W h \<and> (access_settled ?W h \<or> E h)) (access_goals ?W |-| ?H))"
    unfolding e0 ez un access_first_goals_def by (rule positioned_first_union)
  have fe: "access_first_goals ?W X = {||} \<longleftrightarrow> X = {||}" for X
    unfolding access_first_goals_def by (rule positioned_first_empty_iff)
  have pcx: "pc (ffilter (access_candidate ?W) (access_goals ?W |-| ?H)) =
      ffilter rp (ffilter (access_candidate ?W) (access_goals ?W |-| ?H))"
    by (rule pc) (auto simp: ffilter.rep_eq)
  show ?thesis
    unfolding focused_kept_select_in_def Let_def
    by (simp only: access_select_in_def access_goal_choice_classes_in Let_def A hc pcx c0 fe e1 n1)
qed

definition focused_kept_select :: "(('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow>
    's list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "focused_kept_select pc f r V W = (let N = access_construction_nodes W in
    if N \<noteq> {||} then Access_Construction (access_first_nodes W N)
    else let H = search_held_over V r; L = map snd (tree_prefix (class_candidates (search_classes r)) f);
      c0 = (case find (\<lambda>h. h |\<notin>| H \<and> access_settled W h) L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|});
      S = (if c0 \<noteq> {||} then c0 else
        let cp = pc (fset_of_list (filter (\<lambda>h. h |\<notin>| H) L)) in
        if cp \<noteq> {||} then access_first_goals W cp else
        let c1 = (case find (\<lambda>h. h |\<notin>| H \<and> access_single W h) L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) in
        if c1 \<noteq> {||} then c1 else access_waiting_selection W (access_goals W |-| H)) in
      if S = {||} then Access_None else Access_Goals S)"

text \<open>
  The selection reads of the nodes only what the access gives, so it is stated over every access differing from the
  shared state's in its node fields alone (@{text focused_kept_select_over}), as the kept selection is
  (@{thm [source] kept_select_over}); the shared access is its instance, and so is the deferred search's.
\<close>

lemma focused_kept_select_in_empty:
  fixes r :: "('a,'s::linorder,'d,'c) shared_search"
  shows "focused_kept_select_in RBT.empty pc f r V W = focused_kept_select pc f r V W"
proof -
  have z: "find X (map snd (tree_prefix (RBT.empty :: ('s::linorder list,('a,'s,'d,'c) shared_goal_entry) rbt) f)) = None"
    for X
    by (auto simp: find_None_iff tree_prefix(3))
  have o: "access_first_goals W (case find X L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|}) =
      (case find X L of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})" for X and L :: "('a,'s,'d,'c) shared_goal_entry list"
    by (cases "find X L") (auto simp: access_first_goals_def positioned_first_def ffilter.rep_eq fset_eq_iff
      finite_position_less_list)
  show ?thesis by (simp add: focused_kept_select_in_def focused_kept_select_def z o Let_def)
qed

theorem focused_kept_select_over:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  assumes pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals (Some f) V) \<Longrightarrow> pc A = ffilter rp A"
  shows "focused_kept_select pc f r V (access_focused (Some f) V) = access_select rp (access_focused (Some f) V)"
proof -
  have Z: "RBT.lookup RBT.empty p = class_value (\<lambda>h. False) (shared_goals (search_state r)) p" for p
    by (simp add: class_value_def split: option.split)
  have "focused_kept_select_in RBT.empty pc f r V (access_focused (Some f) V) =
      access_select_in (\<lambda>h. False) rp (access_focused (Some f) V)"
    unfolding V_def by (rule focused_kept_select_over_in[OF r K Z]) (simp, rule pc[unfolded V_def], assumption)
  then show ?thesis by (simp only: focused_kept_select_in_empty access_select_in_empty)
qed

theorem focused_kept_select:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals (Some f) (shared_access \<kappa> P r)) \<Longrightarrow> pc A = ffilter rp A"
  shows "focused_kept_select pc f r (shared_access \<kappa> P r) (access_focused (Some f) (shared_access \<kappa> P r)) =
    access_select rp (access_focused (Some f) (shared_access \<kappa> P r))"
proof -
  have e: "(shared_access \<kappa> P r)\<lparr>access_node := access_node (shared_access \<kappa> P r),
      access_free := access_free (shared_access \<kappa> P r), access_value_none := access_value_none (shared_access \<kappa> P r),
      access_call_variables := access_call_variables (shared_access \<kappa> P r)\<rparr> = shared_access \<kappa> P r"
    by simp
  show ?thesis
    using focused_kept_select_over[OF r K, where N = "access_node (shared_access \<kappa> P r)"
      and Fr = "access_free (shared_access \<kappa> P r)" and VN = "access_value_none (shared_access \<kappa> P r)"
      and C = "access_call_variables (shared_access \<kappa> P r)", unfolded e, OF pc] .
qed

text \<open>The focused record the range gives, over every access differing from the shared state's in its node fields.\<close>

lemma shared_focused_over:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  shows "shared_focused f r V = access_focused (Some f) V"
proof -
  have X: "fset_of_list (map snd (tree_prefix (shared_goals (search_state r)) f)) =
      access_focus_goals (Some f) (shared_access \<kappa> P r)"
    using arg_cong[OF shared_focused[OF r, of f], of access_goals] by (simp add: shared_focused_def access_focused_by_def)
  have fg: "access_focus_goals (Some f) V = access_focus_goals (Some f) (shared_access \<kappa> P r)"
    by (simp add: V_def access_focus_goals_def)
  show ?thesis by (simp only: shared_focused_def access_focused_def X fg)
qed


text \<open>
  The committed selection at a closed class @{text Z}: the whole focus selected by the kept classes with @{text Z} first,
  a proper focus by @{const focused_kept_select_in}. At the empty class it is today's @{text committed_kept_select}, at
  the search's own closed class the selection at a table (@{text committed_kept_select_in}): both read through one
  statement (@{text committed_kept_select_at_over}, task 989).
\<close>

definition committed_kept_select_at :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt \<Rightarrow>
    ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow> 's list option \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "committed_kept_select_at Z \<kappa> P pc F r V = (if F = None \<or> F = Some [] then kept_select_by_in Z pc r V
    else focused_kept_select_in Z pc (the F) r V (shared_focused (the F) r V))"

theorem committed_kept_select_at_over:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and Z: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state r)) p"
    and EC: "\<And>h. E h \<Longrightarrow> shared_goal_is_call (shared_entry_goal h)"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  assumes pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals F V) \<Longrightarrow> pc A = ffilter rp A"
  shows "committed_kept_select_at Z \<kappa> P pc F r V = access_select_in E rp (access_focused F V)"
proof (cases "F = None \<or> F = Some []")
  case True
  let ?K = "search_classes r"
  let ?X = "fset_of_list (map snd (RBT.entries (class_candidates ?K))) |-| search_held_over V r"
  have tc: "\<And>p. RBT.lookup (class_candidates ?K) p = class_value (kept_candidate (search_table r)) (shared_goals (search_state r)) p"
    using K by (simp add: classes_formed_def)
  have fg: "access_focus_goals F V = access_goals V"
    using arg_cong[OF access_focused_whole[OF True, of V], of access_goals] by simp
  have goals: "access_goals V = tree_values (shared_goals (search_state r))" by (simp add: V_def shared_access_simps)
  have X: "h |\<in>| access_focus_goals F V" if "h |\<in>| ?X" for h
    using that class_tree_member[OF tc, of h] by (auto simp: fg goals fset_of_list.rep_eq)
  have e: "kept_select_by_in Z pc r V = kept_select_by_in Z (ffilter rp) r V"
    by (simp only: kept_select_by_in_def Let_def pc[OF X])
  have e1: "kept_select_by_in Z (ffilter rp) r V = access_select_in E rp V"
    unfolding V_def by (rule kept_select_over_in[OF r K Z]) (erule EC)
  show ?thesis using True by (simp only: committed_kept_select_at_def e e1 access_focused_whole[OF True] if_True)
next
  case False
  obtain g where g: "F = Some g" and gne: "g \<noteq> []" using False by (cases F) auto
  have "committed_kept_select_at Z \<kappa> P pc F r V = focused_kept_select_in Z pc g r V (access_focused F V)"
    using gne by (simp add: committed_kept_select_at_def g shared_focused_over[OF r] V_def)
  also have "\<dots> = access_select_in E rp (access_focused F V)"
    unfolding g V_def by (rule focused_kept_select_over_in[OF r K Z]) (erule EC, rule pc, simp add: g V_def)
  finally show ?thesis .
qed

definition committed_kept_select :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow> 's list option \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "committed_kept_select \<kappa> P pc F r V = (if F = None \<or> F = Some [] then kept_select_by pc r V
    else focused_kept_select pc (the F) r V (shared_focused (the F) r V))"

lemma committed_kept_select_at_empty:
  fixes r :: "('a,'s::linorder,'d,'c) shared_search"
  shows "committed_kept_select_at RBT.empty \<kappa> P pc F r V = committed_kept_select \<kappa> P pc F r V"
  by (simp add: committed_kept_select_at_def committed_kept_select_def kept_select_by_in_empty
    focused_kept_select_in_empty)

theorem committed_kept_select_over:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  assumes pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals F V) \<Longrightarrow> pc A = ffilter rp A"
  shows "committed_kept_select \<kappa> P pc F r V = access_select rp (access_focused F V)"
proof -
  have Z: "RBT.lookup RBT.empty p = class_value (\<lambda>h. False) (shared_goals (search_state r)) p" for p
    by (simp add: class_value_def split: option.split)
  have "committed_kept_select_at RBT.empty \<kappa> P pc F r V = access_select_in (\<lambda>h. False) rp (access_focused F V)"
    unfolding V_def by (rule committed_kept_select_at_over[OF r K Z]) (simp, rule pc[unfolded V_def], assumption)
  then show ?thesis by (simp add: committed_kept_select_at_empty access_select_in_empty)
qed

theorem committed_kept_select:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals F (shared_access \<kappa> P r)) \<Longrightarrow> pc A = ffilter rp A"
  shows "committed_kept_select \<kappa> P pc F r (shared_access \<kappa> P r) = access_select rp (access_focused F (shared_access \<kappa> P r))"
proof -
  have e: "(shared_access \<kappa> P r)\<lparr>access_node := access_node (shared_access \<kappa> P r),
      access_free := access_free (shared_access \<kappa> P r), access_value_none := access_value_none (shared_access \<kappa> P r),
      access_call_variables := access_call_variables (shared_access \<kappa> P r)\<rparr> = shared_access \<kappa> P r"
    by simp
  show ?thesis
    using committed_kept_select_over[OF r K, where N = "access_node (shared_access \<kappa> P r)"
      and Fr = "access_free (shared_access \<kappa> P r)" and VN = "access_value_none (shared_access \<kappa> P r)"
      and C = "access_call_variables (shared_access \<kappa> P r)", unfolded e, OF pc] .
qed

corollary committed_kept_select_filter:
  assumes "search_formed \<kappa> P r" "search_classes_formed r"
  shows "committed_kept_select \<kappa> P (ffilter rp) F r (shared_access \<kappa> P r) = access_select rp (access_focused F (shared_access \<kappa> P r))"
  by (rule committed_kept_select[OF assms]) (rule refl)

text \<open>Whether the focus holds a goal is read of the goal tree at the whole focus.\<close>

definition shared_focus_empty :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    's list option \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "shared_focus_empty \<kappa> P F r \<longleftrightarrow> (if F = None \<or> F = Some [] then RBT.is_empty (shared_goals (search_state r))
    else access_focus_goals F (shared_access \<kappa> P r) = {||})"

lemma shared_focus_empty: "shared_focus_empty \<kappa> P F r \<longleftrightarrow> access_focus_goals F (shared_access \<kappa> P r) = {||}"
proof (cases "F = None \<or> F = Some []")
  case True
  have a: "access_focus_goals F (shared_access \<kappa> P r) = tree_values (shared_goals (search_state r))"
    using arg_cong[OF access_focused_whole[OF True, of "shared_access \<kappa> P r"], of access_goals]
    by (simp add: shared_access_simps)
  have b: "(tree_values (shared_goals (search_state r)) = {||}) = RBT.is_empty (shared_goals (search_state r))"
    by (auto simp: fset_eq_iff tree_values_member fun_eq_iff simp flip: RBT.lookup_empty_empty) (meson not_None_eq)
  have c: "(F = None \<or> F = Some []) = True" using True by simp
  show ?thesis by (simp only: shared_focus_empty_def c if_True a b)
next
  case False
  have c: "(F = None \<or> F = Some []) = False" using False by simp
  show ?thesis by (simp only: shared_focus_empty_def c if_False)
qed

lemma shared_kept_structure:
  assumes st: "committed_representation_structure (shared_committed_representation \<kappa> P) Fi \<kappa> P"
    and sock: "clause_sockets_distinct P"
    and fi: "\<And>s. Fi s \<Longrightarrow> search_formed \<kappa> P s \<and> search_placeable (search_project s)"
  shows "committed_representation_structure (shared_committed_representation \<kappa> P) (\<lambda>s. Fi s \<and> search_classes_formed s) \<kappa> P"
proof (rule committed_structure_kept[OF st], goal_cases)
  case (1 s)
  have f: "search_formed \<kappa> P s" using fi[OF 1(1)] by simp
  show ?case using search_refresh_classes[OF f 1(2)] by (simp add: shared_committed_representation_def)
next
  case (2 s m q)
  have f: "search_formed \<kappa> P s" using fi[OF 2(1)] by simp
  show ?case using search_construct_classes[OF f 2(2)] by (simp add: shared_committed_representation_def)
next
  case (3 s h s')
  have f: "search_formed \<kappa> P s" "search_placeable (search_project s)" using fi[OF 3(1)] by simp_all
  have h: "h |\<in>| access_goals (shared_access \<kappa> P s)" and s': "s' |\<in>| search_successors \<kappa> P s h"
    using 3(3,4) by (simp_all add: shared_committed_representation_def)
  show ?case by (rule search_successors_classed(3)[OF f sock h s' 3(2)])
next
  case (4 s h s')
  have f: "search_formed \<kappa> P s" "search_placeable (search_project s)" using fi[OF 4(1)] by simp_all
  have h: "h |\<in>| access_goals (shared_access \<kappa> P s)" using 4(3) by (simp add: shared_committed_representation_def)
  have at: "RBT.lookup (shared_goals (search_state s)) (shared_goal_position (shared_entry_goal h)) = Some h"
    using h by (auto simp: shared_access_simps tree_values_member
      dest: shared_goal_lookup_position[OF search_formedD(1)[OF f(1)]])
  show ?case
  proof (cases "shared_entry_goal h")
    case (Shared_Call_Goal q rr d gp)
    have s': "s' |\<in>| search_call_successors P s q d gp"
      using 4(4) Shared_Call_Goal by (simp add: shared_committed_representation_def)
    show ?thesis
      by (rule search_call_successors_classed(3)[OF f sock _ Shared_Call_Goal s' 4(2)]) (use at Shared_Call_Goal in simp)
  next
    case (Shared_Material_Goal q rr gM)
    then show ?thesis using 4(4) by (simp add: shared_committed_representation_def)
  qed
next
  case (5 s h Ws s')
  have f: "search_formed \<kappa> P s" "search_placeable (search_project s)" using fi[OF 5(1)] by simp_all
  have h: "h |\<in>| access_goals (shared_access \<kappa> P s)" using 5(3) by (simp add: shared_committed_representation_def)
  have at: "RBT.lookup (shared_goals (search_state s)) (shared_goal_position (shared_entry_goal h)) = Some h"
    using h by (auto simp: shared_access_simps tree_values_member
      dest: shared_goal_lookup_position[OF search_formedD(1)[OF f(1)]])
  show ?case
  proof (cases "shared_entry_goal h")
    case (Shared_Material_Goal q rr gM)
    have s': "s' |\<in>| search_solution_successors P s q gM (shared_material_project (search_table s) gM) Ws"
      using 5(4) Shared_Material_Goal by (simp add: shared_committed_representation_def)
    show ?thesis
      by (rule search_solution_successors_classed(3)[OF f _ Shared_Material_Goal s' 5(2)])
        (use at Shared_Material_Goal in simp)
  next
    case (Shared_Call_Goal q rr d gp)
    then show ?thesis using 5(4) by (simp add: shared_committed_representation_def)
  qed
next
  case (6 s \<sigma> D)
  have f: "search_formed \<kappa> P s" using fi[OF 6(1)] by simp
  show ?case using search_substitute_plain_classes[OF f 6(2) 6(3)] by (simp add: shared_committed_representation_def)
next
  case (7 s)
  have d: "resolution_positions_distinct (search_project s)" using fi[OF 7(1)] by (simp add: search_placeable_def)
  show ?case using search_of_classes[OF d] by (simp add: shared_committed_representation_def)
qed

text \<open>
  At tests prepared as they stand, the kept selection is the one of the tests' priority as a filter: the shared state
  selects through its kept classes at every tests the committed step is formed at.
\<close>

definition kept_tests_select where
  "kept_tests_select \<kappa> P T gd F r V x = committed_kept_select \<kappa> P (ffilter (\<lambda>h. gd r h \<and> tests_priority T F r V x h)) F r V"

lemma kept_selected_formed:
  assumes tf: "tested_representation_formed (shared_committed_representation \<kappa> P) Fi \<kappa> P K pr T gd"
    and fi: "\<And>s. Fi s \<Longrightarrow> search_formed \<kappa> P s \<and> search_classes_formed s"
  shows "selected_representation_formed (shared_committed_representation \<kappa> P) Fi \<kappa> P K pr T gd (shared_focus_empty \<kappa> P)
    (kept_tests_select \<kappa> P T gd) (tests_prepare T)"
proof (rule selected_representation_formed.intro[OF tf], unfold_locales, goal_cases)
  case (1 s F)
  then show ?case by (simp add: shared_focus_empty shared_committed_representation_def)
next
  case (2 s F)
  have f: "search_formed \<kappa> P s" "search_classes_formed s" using fi[OF 2] by simp_all
  show ?case by (simp add: kept_tests_select_def shared_committed_representation_def committed_kept_select_filter[OF f])
next
  case (3 s F B rec)
  show ?case by (rule refl)
qed

theorem shared_kept_committed_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
  shows "selected_committed_search (shared_committed_representation \<kappa> P)
      (projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True)) (\<lambda>r h. True) (shared_focus_empty \<kappa> P)
      (kept_tests_select \<kappa> P (projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True)) (\<lambda>r h. True))
      (tests_prepare (projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True))) \<kappa> P n F B (search_of P st) =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B st"
proof -
  let ?Fi = "\<lambda>r. (search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r"
  have st: "committed_representation_structure (shared_committed_representation \<kappa> P) ?Fi \<kappa> P"
    by (rule shared_kept_structure[OF shared_committed_structure[OF sock] sock]) simp
  have cf: "committed_representation_formed (shared_committed_representation \<kappa> P) ?Fi \<kappa> P K pr (\<lambda>r h. True)"
    by (rule committed_representation_formed.intro[OF st], unfold_locales) simp
  interpret selected_representation_formed "shared_committed_representation \<kappa> P" ?Fi \<kappa> P K pr
      "projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True)" "\<lambda>r h. True" "shared_focus_empty \<kappa> P"
      "kept_tests_select \<kappa> P (projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True)) (\<lambda>r h. True)"
      "tests_prepare (projected_tests (shared_committed_representation \<kappa> P) K pr (\<lambda>r h. True))"
    by (rule kept_selected_formed[OF committed_representation_formed.tested[OF cf]]) simp
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have f: "?Fi (search_of P st)" using search_of[OF d] search_of_classes[OF d] pl by simp
  show ?thesis using selected_committed[OF f] search_of(2)[OF d] by (simp add: shared_committed_representation_def)
qed

declare finite_committed_search_shared_code [code del]

lemma finite_committed_search_kept_code [code]:
  "finite_committed_search \<kappa> K P n F B st = (if clause_sockets_distinct P \<and> search_placeable st
    then selected_committed_search (shared_committed_representation \<kappa> P)
      (projected_tests (shared_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True)) (\<lambda>r h. True)
      (shared_focus_empty \<kappa> P)
      (kept_tests_select \<kappa> P (projected_tests (shared_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True))
        (\<lambda>r h. True))
      (tests_prepare (projected_tests (shared_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True)))
      \<kappa> P n F B (search_of P st)
    else finite_committed_search_by (finite_committed_select \<kappa> K P) \<kappa> K P n F B st)"
  by (simp add: finite_committed_search_def shared_kept_committed_search)

section \<open>The committed search at a table of certified calls\<close>

text \<open>
  GT3b (DECISIONS.md, task 495's entry, "The given's calls are decided once", task 970): the committed side of the table.
  A structure is the structure at the empty table and back (@{text committed_representation_structure_in_empty},
  @{text committed_representation_structure_of_empty}), and so is a tested form. The shared state at a table
  (@{const search_of_in}) is the committed representation whose successors close a goal the index closes
  (@{const search_successors_in}) and whose found states are shared again from the table's sharing, made once
  (@{text table_carry}, @{text search_of_carried});
  a call at the focus keeps its clause alternatives and is never closed (GT2a's @{const finite_committed_successors_in}).
  Its selection reads the closed class beside the settled one, at a proper focus as a range of it
  (@{text committed_kept_select_over_in}), and its search is GT2a's committed search at the table at the projection
  (@{text shared_kept_committed_search_in}).
\<close>

text \<open>The tests read on the projection, at a table: formed wherever the closing test is the table's.\<close>

lemma projected_tested_in:
  assumes st: "committed_representation_structure_in R Fi \<kappa> P \<Theta>"
    and closes: "\<And>s h. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      cl s h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access R s) h)"
  shows "tested_representation_formed_in R Fi \<kappa> P \<Theta> K pr (projected_tests R K pr (\<lambda>r h. True)) (\<lambda>r h. True) cl"
proof (rule tested_representation_formed_in.intro[OF st], unfold_locales, goal_cases)
  case (1 s h F)
  then show ?case by simp
next
  case (2 s h F B)
  interpret s: committed_representation_structure_in R Fi \<kappa> P \<Theta> by (rule st)
  have "tests_prepare (projected_tests R K pr (\<lambda>r h. True)) F s (rep_access R s) = Some (rep_project R s)"
    using 2 by (auto simp: projected_tests_def)
  then show ?case by (simp add: tests_exact_at_def projected_tests_def Let_def s.produced[OF 2(1)])
next
  case (3 s h x)
  then show ?case by (simp add: projected_tests_def)
next
  case (4 s h)
  then show ?case by (rule closes)
qed

subsection \<open>The shared state's committed representation at a table\<close>

lemma search_calls_frame: "search_calls r = fst (search_frame r)"
  by (simp add: search_frame_def)

lemma search_call_successors_with_frame:
  assumes "s' |\<in>| search_call_successors_with \<beta> P r q d gp"
    and "\<And>s x. search_frame x = search_frame r \<Longrightarrow> g (\<beta> s x) = search_frame r"
  shows "g s' = search_frame r"
  using assms by (auto simp: search_call_successors_with_def Let_def)

lemma search_solution_successors_with_frame:
  assumes "s' |\<in>| search_solution_successors_with \<beta> P r q gM M Ws"
    and "\<And>s x. search_frame x = search_frame r \<Longrightarrow> g (\<beta> s x) = search_frame r"
  shows "g s' = search_frame r"
  using assms by (auto simp: search_solution_successors_with_def Let_def)

lemma shared_call_successors_frame:
  assumes "s' |\<in>| rep_call_successors (shared_committed_representation \<kappa> P) r h"
  shows "search_frame s' = search_frame r"
proof (cases "shared_entry_goal h")
  case (Shared_Call_Goal q rr d gp)
  have m: "s' |\<in>| search_call_successors_with (search_bind P) P r q d gp"
    using assms Shared_Call_Goal by (simp add: shared_committed_representation_def search_call_successors_def)
  show ?thesis by (rule search_call_successors_with_frame[where g = search_frame, OF m]) simp
next
  case (Shared_Material_Goal q rr gM)
  then show ?thesis using assms by (simp add: shared_committed_representation_def)
qed

lemma shared_solution_successors_frame:
  assumes "s' |\<in>| rep_solution_successors (shared_committed_representation \<kappa> P) r h Ws"
  shows "search_frame s' = search_frame r"
proof (cases "shared_entry_goal h")
  case (Shared_Material_Goal q rr gM)
  have m: "s' |\<in>| search_solution_successors_with (search_bind P) P r q gM
      (shared_material_project (search_table r) gM) Ws"
    using assms Shared_Material_Goal by (simp add: shared_committed_representation_def search_solution_successors_def)
  show ?thesis by (rule search_solution_successors_with_frame[where g = search_frame, OF m]) simp
next
  case (Shared_Call_Goal q rr d gp)
  then show ?thesis using assms by (simp add: shared_committed_representation_def)
qed

text \<open>
  The table carried through a re-share (task 989): the table's calls are shared and indexed once, from the empty
  sharing state (@{text table_carry}); a state the search shares again is shared from that sharing state
  (@{const share_resolution_state_from}), so every reference the table's index holds stays the same term
  (@{thm [source] share_term_preserves}, through @{thm [source] calls_indexed_extends}) and the table is not attached
  again.
\<close>

definition table_carry :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<times> (nat,'d fset) rbt" where
  "table_carry C = index_calls C (RBT.empty,0,[]) RBT.empty"

lemma table_carry:
  "share_state_formed (fst (table_carry C))" "table_extends [] (share_state_table (fst (table_carry C)))"
  "calls_indexed (share_state_table (fst (table_carry C))) (snd (table_carry C)) (set C)"
proof -
  have I0: "calls_indexed (share_state_table (RBT.empty,0,[])) RBT.empty ({} :: ('d \<times> finite_factor_term) set)"
    by (simp add: calls_indexed_def)
  note ix = index_calls[OF share_state_empty(1) I0, of C]
  show "share_state_formed (fst (table_carry C))" "table_extends [] (share_state_table (fst (table_carry C)))"
    "calls_indexed (share_state_table (fst (table_carry C))) (snd (table_carry C)) (set C)"
    using ix share_state_empty(2) by (simp_all add: table_carry_def)
qed

definition search_of_carried :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<times> (nat,'d fset) rbt \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_of_carried C X P st = (let s = share_resolution_state_from (fst X) P st in
    \<lparr>search_state = s, search_registered = fold (\<lambda>z t. tree_add (fst z) (shared_goal_registered (snd z)) t)
      (RBT.entries (shared_goals s)) RBT.empty, search_values = RBT.empty,
     search_classes = classes_update (map fst (RBT.entries (shared_goals s))) s empty_classes,
     search_calls = C, search_index = snd X,
     search_closed = fold (\<lambda>p t. closed_put p s (snd X) t) (RBT.keys (shared_goals s)) RBT.empty\<rparr>)"

lemma search_of_carried:
  assumes d: "resolution_positions_distinct st" and x: "share_state_formed (fst X)"
    and e: "table_extends [] (share_state_table (fst X))"
    and I: "calls_indexed (share_state_table (fst X)) (snd X) (set C)"
  shows "search_formed \<kappa> P (search_of_carried C X P st)" and "search_project (search_of_carried C X P st) = st"
    and "search_calls (search_of_carried C X P st) = C" and "search_classes_formed (search_of_carried C X P st)"
proof -
  let ?s = "share_resolution_state_from (fst X) P st"
  note sr = share_resolution_state_from[OF d x e]
  have ext: "table_extends (share_state_table (fst X)) (share_state_table (shared_sharing ?s))"
    using keyed_share_grounds[where G = "resolution_grounds st", OF x] sr(3) by simp
  have rf: "search_registered_formed (search_of_carried C X P st)"
    unfolding search_registered_formed_def search_of_carried_def Let_def
    by (auto simp: tree_add_fold_member RBT.lookup_in_tree)
  have vf: "search_values_formed \<kappa> P (search_of_carried C X P st)"
    by (simp add: search_values_formed_def search_of_carried_def Let_def)
  have keys: "p \<in> set (RBT.keys (shared_goals ?s)) \<longleftrightarrow> RBT.lookup (shared_goals ?s) p \<noteq> None" for p
    using RBT.lookup_keys[of "shared_goals ?s"] by (auto simp: dom_def)
  have cf: "search_closing_formed (search_of_carried C X P st)"
    unfolding search_closing_formed_def
  proof (intro conjI allI)
    show "calls_indexed (search_table (search_of_carried C X P st)) (search_index (search_of_carried C X P st))
        (set (search_calls (search_of_carried C X P st)))"
      using calls_indexed_extends[OF I ext] by (simp add: search_of_carried_def Let_def)
    fix p
    show "RBT.lookup (search_closed (search_of_carried C X P st)) p =
        (case RBT.lookup (shared_goals (search_state (search_of_carried C X P st))) p of
          None \<Rightarrow> None | Some h \<Rightarrow> if search_closes (search_of_carried C X P st) h then Some h else None)"
      using keys[of p] by (auto simp: search_of_carried_def Let_def closed_put_fold search_closes_def split: option.split)
  qed
  show f: "search_formed \<kappa> P (search_of_carried C X P st)"
    unfolding search_formed_def using sr(1) rf vf cf by (simp add: search_of_carried_def Let_def)
  show "search_project (search_of_carried C X P st) = st" using sr(2) by (simp add: search_of_carried_def Let_def)
  show "search_calls (search_of_carried C X P st) = C" by (simp add: search_of_carried_def Let_def)
  have none: "RBT.lookup t p = None" if "p \<notin> set (map fst (RBT.entries t))" for t :: "('x::linorder,'y) rbt" and p
    using that by (cases "RBT.lookup t p") (force simp: RBT.lookup_in_tree)+
  have "classes_formed (search_state (search_of_carried C X P st))
      (classes_update (map fst (RBT.entries (shared_goals (search_state (search_of_carried C X P st)))))
        (search_state (search_of_carried C X P st)) empty_classes)"
    by (rule classes_update_formed[OF f]) (simp add: none empty_classes_def class_value_def)
  then show "search_classes_formed (search_of_carried C X P st)" by (simp add: search_of_carried_def Let_def)
qed

lemmas search_of_carried_table = search_of_carried[OF _ table_carry]

definition shared_committed_representation_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d \<times> finite_factor_term) list \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) committed_representation" where
  "shared_committed_representation_in \<kappa> P C = (let X = table_carry C in (shared_committed_representation \<kappa> P)\<lparr>
    rep_successors := search_successors_in \<kappa> P, rep_share := search_of_carried C X P\<rparr>)"

lemma shared_committed_in_fields:
  "rep_access (shared_committed_representation_in \<kappa> P C) = shared_access \<kappa> P"
  "rep_empty (shared_committed_representation_in \<kappa> P C) = rep_empty (shared_committed_representation \<kappa> P)"
  "rep_project (shared_committed_representation_in \<kappa> P C) = search_project"
  "rep_refresh (shared_committed_representation_in \<kappa> P C) = search_refresh \<kappa> P"
  "rep_construct (shared_committed_representation_in \<kappa> P C) = search_construct \<kappa> P"
  "rep_successors (shared_committed_representation_in \<kappa> P C) = search_successors_in \<kappa> P"
  "rep_node_positions (shared_committed_representation_in \<kappa> P C) = rep_node_positions (shared_committed_representation \<kappa> P)"
  "rep_call_successors (shared_committed_representation_in \<kappa> P C) = rep_call_successors (shared_committed_representation \<kappa> P)"
  "rep_solution_successors (shared_committed_representation_in \<kappa> P C) =
    rep_solution_successors (shared_committed_representation \<kappa> P)"
  "rep_substitute (shared_committed_representation_in \<kappa> P C) = rep_substitute (shared_committed_representation \<kappa> P)"
  "rep_share (shared_committed_representation_in \<kappa> P C) = search_of_carried C (table_carry C) P"
  by (simp_all add: shared_committed_representation_in_def shared_committed_representation_def fun_eq_iff Let_def)

theorem shared_committed_structure_in:
  assumes sock: "clause_sockets_distinct P"
    and tbl: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "committed_representation_structure_in (shared_committed_representation_in \<kappa> P C)
    (\<lambda>r. ((search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r) \<and> search_calls r = C)
    \<kappa> P \<Theta>"
proof -
  let ?S = "shared_committed_representation \<kappa> P"
  interpret b: committed_representation_structure ?S
      "\<lambda>r. (search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" \<kappa> P
    by (rule shared_kept_structure[OF shared_committed_structure[OF sock] sock]) simp
  have ss: "rep_project ?S = search_project" "rep_access ?S = shared_access \<kappa> P" "rep_refresh ?S = search_refresh \<kappa> P"
    "rep_construct ?S = search_construct \<kappa> P" "rep_substitute ?S = (\<lambda>r \<sigma> D. search_substitute_plain P \<sigma> D r)"
    by (simp_all add: shared_committed_representation_def fun_eq_iff)
  note fd = shared_committed_in_fields[of \<kappa> P C]
  show ?thesis
  proof (rule committed_representation_structure_in.intro, goal_cases)
    case (1 s)
    then show ?case using b.access[of s] by (simp add: fd ss)
  next
    case (2 s)
    then show ?case using b.refresh[of s] by (simp add: fd ss search_calls_frame)
  next
    case (3 s m q)
    then show ?case using b.construct[of s m q] by (simp add: fd ss search_calls_frame, metis)
  next
    case (4 s h)
    have f: "search_formed \<kappa> P s" "search_placeable (search_project s)" "search_classes_formed s" "search_calls s = C"
      using 4(1) by simp_all
    have h: "h |\<in>| access_goals (shared_access \<kappa> P s)" using 4(2) by (simp add: fd)
    have D': "\<And>d t. (d,t) \<in> set (search_calls s) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None" using tbl f(4) by simp
    note c = search_successors_in[OF f(1) f(2) sock h D']
    show ?case using c(1) c(2) c(3)[OF _ f(3)] f(4) by (auto simp: fd search_calls_frame)
  next
    case (5 s h q rr d p)
    have f: "(search_formed \<kappa> P s \<and> search_placeable (search_project s)) \<and> search_classes_formed s" "search_calls s = C"
      using 5(1) by simp_all
    have h: "h |\<in>| access_goals (rep_access ?S s)" and g: "access_goal (rep_access ?S s) h = Resolution_Call_Goal q rr d p"
      using 5(2,3) by (simp_all add: fd ss)
    note c = b.call[OF f(1) h g]
    have k: "search_calls s' = C" if s': "s' |\<in>| rep_call_successors ?S s h" for s'
      using shared_call_successors_frame[OF s'] f(2) by (simp add: search_calls_frame)
    show ?case using c k by (auto simp: fd ss)
  next
    case (6 s h q rr M Ws)
    have f: "(search_formed \<kappa> P s \<and> search_placeable (search_project s)) \<and> search_classes_formed s" "search_calls s = C"
      using 6(1) by simp_all
    have h: "h |\<in>| access_goals (rep_access ?S s)" and g: "access_goal (rep_access ?S s) h = Resolution_Material_Goal q rr M"
      using 6(2,3) by (simp_all add: fd ss)
    note c = b.solution[OF f(1) h g, of Ws]
    have k: "search_calls s' = C" if s': "s' |\<in>| rep_solution_successors ?S s h Ws" for s'
      using shared_solution_successors_frame[OF s'] f(2) by (simp add: search_calls_frame)
    show ?case using c k by (auto simp: fd ss)
  next
    case (7 s q)
    then show ?case using b.positions[of s q] by (simp add: fd ss)
  next
    case (8 s \<sigma> D)
    have f: "(search_formed \<kappa> P s \<and> search_placeable (search_project s)) \<and> search_classes_formed s" "search_calls s = C"
      using 8(1) by simp_all
    note c = b.substitute[of s D \<sigma>, OF f(1) 8(2)]
    show ?case using c f(2) by (simp add: fd ss search_calls_frame, metis)
  next
    case (9 s)
    have pl: "search_placeable (search_project s)" using 9 by simp
    have d: "resolution_positions_distinct (search_project s)" using pl by (simp add: search_placeable_def)
    show ?case using search_of_carried_table[OF d] pl by (simp add: fd)
  qed
qed

subsection \<open>The closed class in the committed selection\<close>

text \<open>
  At a proper focus the first class at a table is the first of the settled candidates under the focus and the first
  closed goal under it, each read as one key range: of the kept candidate class, as FI reads it, and of the closed class
  (@{const search_closed}).
\<close>



definition committed_kept_select_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow> 's list option \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "committed_kept_select_in \<kappa> P pc F r V = (if F = None \<or> F = Some [] then kept_select_by_in (search_closed r) pc r V
    else focused_kept_select_in (search_closed r) pc (the F) r V (shared_focused (the F) r V))"

lemma committed_kept_select_in_at:
  "committed_kept_select_in \<kappa> P pc F r V = committed_kept_select_at (search_closed r) \<kappa> P pc F r V"
  by (simp add: committed_kept_select_in_def committed_kept_select_at_def)

theorem committed_kept_select_over_in:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  assumes pc: "\<And>A. (\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_focus_goals F V) \<Longrightarrow> pc A = ffilter rp A"
  shows "committed_kept_select_in \<kappa> P pc F r V = access_select_in (search_closes r) rp (access_focused F V)"
proof -
  have "committed_kept_select_at (search_closed r) \<kappa> P pc F r V =
      access_select_in (search_closes r) rp (access_focused F V)"
    unfolding V_def by (rule committed_kept_select_at_over[OF r K search_closed_class[OF r]])
      (erule search_closes_call, rule pc[unfolded V_def], assumption)
  then show ?thesis by (simp add: committed_kept_select_in_at)
qed

corollary committed_kept_select_in_filter:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "committed_kept_select_in \<kappa> P (ffilter rp) F r (shared_access \<kappa> P r) =
    access_select_in (search_closes r) rp (access_focused F (shared_access \<kappa> P r))"
proof -
  let ?V = "shared_access \<kappa> P r"
  have e: "?V\<lparr>access_node := access_node ?V, access_free := access_free ?V, access_value_none := access_value_none ?V,
      access_call_variables := access_call_variables ?V\<rparr> = ?V" by simp
  show ?thesis using committed_kept_select_over_in[OF r K, where N = "access_node ?V" and Fr = "access_free ?V"
      and VN = "access_value_none ?V" and C = "access_call_variables ?V" and pc = "ffilter rp" and rp = rp and F = F,
      unfolded e] by simp
qed

definition kept_tests_select_in where
  "kept_tests_select_in \<kappa> P T gd F r V x =
    committed_kept_select_in \<kappa> P (ffilter (\<lambda>h. gd r h \<and> tests_priority T F r V x h)) F r V"

lemma kept_selected_formed_in:
  assumes tf: "tested_representation_formed_in (shared_committed_representation_in \<kappa> P C) Fi \<kappa> P \<Theta> K pr T gd search_closes"
    and fi: "\<And>s. Fi s \<Longrightarrow> search_formed \<kappa> P s \<and> search_classes_formed s"
  shows "selected_representation_formed_in (shared_committed_representation_in \<kappa> P C) Fi \<kappa> P \<Theta> K pr T gd search_closes
    (shared_focus_empty \<kappa> P) (kept_tests_select_in \<kappa> P T gd) (tests_prepare T)"
proof (rule selected_representation_formed_in.intro[OF tf], unfold_locales, goal_cases)
  case (1 s F)
  then show ?case by (simp add: shared_focus_empty shared_committed_in_fields)
next
  case (2 s F)
  have f: "search_formed \<kappa> P s" "search_classes_formed s" using fi[OF 2] by simp_all
  show ?case by (simp add: kept_tests_select_in_def shared_committed_in_fields committed_kept_select_in_filter[OF f])
next
  case (3 s F B rec)
  show ?case by (rule refl)
qed

theorem shared_kept_committed_search_in:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and tbl: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "selected_committed_search (shared_committed_representation_in \<kappa> P C)
      (projected_tests (shared_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True)) (\<lambda>r h. True) (shared_focus_empty \<kappa> P)
      (kept_tests_select_in \<kappa> P (projected_tests (shared_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True)) (\<lambda>r h. True))
      (tests_prepare (projected_tests (shared_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True))) \<kappa> P n F B
      (search_of_in C P st) =
    finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F B st"
proof -
  let ?R = "shared_committed_representation_in \<kappa> P C"
  let ?Fi = "\<lambda>r. ((search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r) \<and> search_calls r = C"
  have st: "committed_representation_structure_in ?R ?Fi \<kappa> P \<Theta>" by (rule shared_committed_structure_in[OF sock tbl])
  have cl: "search_closes s h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access ?R s) h)"
    if s: "?Fi s" and h: "h |\<in>| access_goals (rep_access ?R s)" for s h
  proof -
    have f: "search_formed \<kappa> P s" and c: "search_calls s = C" using s by simp_all
    have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" using h by (simp add: shared_committed_in_fields)
    have D': "\<And>d t. (d,t) \<in> set (search_calls s) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None" using tbl c by simp
    show ?thesis using search_closes_table[OF f h' D'] by (simp add: shared_committed_in_fields)
  qed
  interpret selected_representation_formed_in ?R ?Fi \<kappa> P \<Theta> K pr "projected_tests ?R K pr (\<lambda>r h. True)" "\<lambda>r h. True"
      search_closes "shared_focus_empty \<kappa> P" "kept_tests_select_in \<kappa> P (projected_tests ?R K pr (\<lambda>r h. True)) (\<lambda>r h. True)"
      "tests_prepare (projected_tests ?R K pr (\<lambda>r h. True))"
    by (rule kept_selected_formed_in[OF projected_tested_in[OF st cl]]) simp_all
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have f: "?Fi (search_of_in C P st)" using search_of_in[OF d] pl by simp
  show ?thesis using selected_committed[OF f] search_of_in(2)[OF d] by (simp add: shared_committed_in_fields)
qed

export_code finite_committed_search checking SML

end
