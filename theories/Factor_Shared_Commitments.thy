theory Factor_Shared_Commitments
  imports Factor_Shared_Search Factor_Resolution_Commitments
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

definition access_focused :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access" where
  "access_focused F V = (let G = access_focus_goals F V in V\<lparr>access_goals := G,
    access_goals_at := (\<lambda>q. if resolution_focused F q then access_goals_at V q else {||}),
    access_open := (\<lambda>q. case F of None \<Rightarrow> access_open V q
      | Some f \<Rightarrow> if take (length f) q = f then access_open V q
        else if take (length q) f = q \<and> G \<noteq> {||} then 1 else 0)\<rparr>)"

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
  "access_witnesses (access_focused F V) = access_witnesses V"
  by (simp_all add: access_focused_def Let_def)

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
    fBall (access_nodes_at V q) (\<lambda>n. finite_pattern_variables (resolution_node_call (access_node V n)) = {||}))"

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
  show ?thesis using Some g n by (simp add: access_focus_ground_def finite_focus_ground_def)
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

lemma finite_first_outcome_cong:
  assumes "\<And>Y x. Y \<in> set Ys \<Longrightarrow> x |\<in>| Y \<Longrightarrow> f x = g x"
  shows "finite_first_outcome f Ys = finite_first_outcome g Ys"
  using assms
proof (induction Ys)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  have i: "fimage f X = fimage g X" by (rule fset.map_cong0) (use Cons.prems in auto)
  have "finite_first_outcome f Xs = finite_first_outcome g Xs" by (rule Cons.IH) (use Cons.prems in auto)
  then show ?case using i by (simp add: Let_def)
qed

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
  A committed representation is formed at an invariant of its states when its accesses are formed at their
  projections, its steps project to R5's and keep the invariant, and every goal its guard does not admit is one no
  test of the commitment and no priority accepts, at any focus and state.
\<close>

locale committed_representation_formed =
  fixes R :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c,'z) committed_representation_scheme"
    and Fi :: "'r \<Rightarrow> bool"
    and \<kappa> :: "('a,'s,'d,'c) finite_witness_construction" and P :: "('a,'s,'d,'c) finite_schema_system"
    and K :: "('a,'s,'d,'c) resolution_commitment"
    and pr :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
    and gd :: "'r \<Rightarrow> 'g \<Rightarrow> bool"
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
    and guard: "\<And>s h F st. Fi s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (rep_access R s) h) \<and> \<not> commit_material K F st (access_goal (rep_access R s) h) \<and>
      \<not> pr st (access_goal (rep_access R s) h)"
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
    finite_committed_successors K P F (rep_project R r) (access_goal (rep_access R r) h)"
    and "s' |\<in>| represented_committed_successors R F cm r (rep_access R r) h \<Longrightarrow> Fi s'"
proof -
  let ?V = "rep_access R r" let ?st = "rep_project R r" let ?g = "access_goal ?V h"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  note sc = successors[OF Fr h]
  show "fimage (rep_project R) (represented_committed_successors R F (finite_material_committed K F ?st ?g) r ?V h) =
      finite_committed_successors K P F ?st ?g"
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

lemma goal_outcome:
  assumes Fr: "Fi r" and h: "h |\<in>| access_goals (rep_access R r)"
    and so: "gd r h \<Longrightarrow> so = Some (rep_project R r)"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow> recI F' B' s = recA F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  shows "represented_committed_goal_outcome R gd recI K F B r (rep_access R r) so h =
    finite_committed_goal_outcome recA K P F B (rep_project R r) (access_goal (rep_access R r) h)"
proof -
  let ?V = "rep_access R r" let ?st = "rep_project R r" let ?g = "access_goal ?V h"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  have pu: "access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h \<longleftrightarrow> finite_pruned (finite_unbarred B ?st) ?g"
    using v.pruned_among[OF h, of "\<lambda>q. q |\<notin>| B"] by (simp add: finite_unbarred_def)
  have pb: "access_pruned_among (\<lambda>q. q |\<in>| B) ?V h \<longleftrightarrow> finite_pruned (finite_barred B ?st) ?g"
    using v.pruned_among[OF h, of "\<lambda>q. q |\<in>| B"] by (simp add: finite_barred_def)
  have ng: "\<not> gd r h \<Longrightarrow> \<not> commit_call K F' st' ?g \<and> \<not> commit_material K F' st' ?g" for F' st'
    using guard[OF Fr h] by blast
  have comm: "(gd r h \<and> finite_goal_committing K F (the so) ?g) \<longleftrightarrow> finite_goal_committing K F ?st ?g"
    using so ng by (cases "gd r h") (auto simp: finite_goal_committing_def)
  have cm: "(gd r h \<and> finite_material_committed K F (the so) ?g) \<longleftrightarrow> finite_material_committed K F ?st ?g"
    using so ng by (cases "gd r h") (auto simp: finite_material_committed_def split: resolution_goal.splits)
  have bar: "B |\<union>| rep_node_positions R r = finite_committed_barring B ?st"
  proof (rule fset_eqI)
    fix x show "x |\<in>| B |\<union>| rep_node_positions R r \<longleftrightarrow> x |\<in>| finite_committed_barring B ?st"
      using v.node_positions[of x] positions[OF Fr, of x] by (auto simp: finite_committed_barring_def)
  qed
  consider (closed) "finite_pruned (finite_unbarred B ?st) ?g"
    | (cut) "\<not> finite_pruned (finite_unbarred B ?st) ?g" "finite_pruned (finite_barred B ?st) ?g"
    | (unpruned) "\<not> finite_pruned (finite_unbarred B ?st) ?g" "\<not> finite_pruned (finite_barred B ?st) ?g" by blast
  then show ?thesis
  proof cases
    case closed
    then show ?thesis using pu by (simp add: represented_committed_goal_outcome_def finite_committed_goal_outcome_in_def)
  next
    case cut
    then show ?thesis using pu pb by (simp add: represented_committed_goal_outcome_def finite_committed_goal_outcome_in_def)
  next
    case unpruned
    have npu: "\<not> access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h" and npb: "\<not> access_pruned_among (\<lambda>q. q |\<in>| B) ?V h"
      using unpruned pu pb by simp_all
    show ?thesis
    proof (cases "finite_goal_committing K F ?st ?g")
      case True
      have c: "gd r h \<and> finite_goal_committing K F (the so) ?g" using True comm by simp
      have sost: "the so = ?st" using c so by simp
      have c': "gd r h \<and> finite_goal_committing K F ?st ?g" using c sost by simp
      let ?q = "resolution_goal_position ?g" let ?B' = "finite_goal_sub_barring K F B ?st ?g"
      have prd: "Fi (represented_produced R K F r ?st ?g)"
          "rep_project R (represented_produced R K F r ?st ?g) = finite_produced_state K F ?st ?g"
        using produced[OF Fr] by simp_all
      let ?subA = "recA (Some ?q) ?B' (finite_produced_state K F ?st ?g)"
      have sub: "recI (Some ?q) ?B' (represented_produced R K F r ?st ?g) = ?subA" using rec[OF prd(1)] prd(2) by simp
      have kept: "fimage (\<lambda>s. recI F (finite_committed_barring B s) (rep_share R s)) (finite_kept ?q (resolution_found ?subA)) =
          fimage (\<lambda>s. recA F (finite_committed_barring B s) s) (finite_kept ?q (resolution_found ?subA))"
      proof (rule fset.map_cong0)
        fix s assume "s \<in> fset (finite_kept ?q (resolution_found ?subA))"
        then have "s |\<in>| resolution_found ?subA" using fsubsetD[OF finite_kept_subset] by blast
        then have "s |\<in>| resolution_found (recI (Some ?q) ?B' (represented_produced R K F r ?st ?g))" using sub by simp
        then obtain r0 where r0: "Fi r0" "rep_project R r0 = s" using recfound[OF prd(1)] by blast
        show "recI F (finite_committed_barring B s) (rep_share R s) = recA F (finite_committed_barring B s) s"
          using rec[OF conjunct1[OF share[OF r0(1)]]] conjunct2[OF share[OF r0(1)]] r0(2) by simp
      qed
      show ?thesis
        unfolding represented_committed_goal_outcome_def finite_committed_goal_outcome_eq Let_def
        by (simp only: if_not_P[OF npu] if_not_P[OF npb] if_P[OF c] sost if_P[OF c'] if_not_P[OF unpruned(1)]
          if_not_P[OF unpruned(2)] if_P[OF True] sub kept)
    next
      case False
      have nc: "\<not> (gd r h \<and> finite_goal_committing K F (the so) ?g)" using False comm by simp
      let ?cm = "gd r h \<and> finite_material_committed K F (the so) ?g"
      let ?S = "represented_committed_successors R F ?cm r ?V h"
      have S0: "?S = represented_committed_successors R F (finite_material_committed K F ?st ?g) r ?V h" using cm by simp
      have S: "fimage (rep_project R) ?S = finite_committed_successors K P F ?st ?g"
        unfolding S0 by (rule committed_successors(1)[OF Fr h])
      have SF: "\<And>s'. s' |\<in>| ?S \<Longrightarrow> Fi s'" by (rule committed_successors(2)[OF Fr h])
      have gb: "(if ?cm then B |\<union>| rep_node_positions R r else B) = finite_goal_barring K F B ?st ?g"
        using cm bar by (simp add: finite_goal_barring_def)
      have img: "fimage (recI F (if ?cm then B |\<union>| rep_node_positions R r else B)) ?S =
          fimage (recA F (finite_goal_barring K F B ?st ?g)) (finite_committed_successors K P F ?st ?g)"
        unfolding gb S[symmetric] fset.map_comp comp_def by (rule fset.map_cong0) (simp add: rec SF)
      have e: "?S = {||} \<longleftrightarrow> finite_committed_successors K P F ?st ?g = {||}"
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
          (finite_committed_successors K P F ?st ?g)"
        unfolding S[symmetric] finite_search_join_image v.focus_ground fb im ..
      show ?thesis
        unfolding represented_committed_goal_outcome_def finite_committed_goal_outcome_eq Let_def
          if_not_P[OF npu] if_not_P[OF npb] if_not_P[OF nc] if_not_P[OF unpruned(1)] if_not_P[OF unpruned(2)]
          if_not_P[OF False]
        using jn e v.witnesses by simp
    qed
  qed
qed

lemma step:
  assumes Fr: "Fi r" and ne: "finite_focus_pending F (rep_project R r) \<noteq> {||}"
    and rec: "\<And>F' B' s. Fi s \<Longrightarrow>
      recI F' B' s = finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P m F' B' (rep_project R s)"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
  shows "represented_committed_step R pr gd \<kappa> K P recI F B r =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P (Suc m) F B (rep_project R r)"
proof -
  let ?recA = "finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P m"
  let ?st = "rep_project R r" let ?V = "rep_access R r"
  let ?so = "if fBex (access_goals ?V) (gd r) then Some ?st else None"
  let ?rp = "\<lambda>h. gd r h \<and> pr (the (map_option (finite_focused F) ?so)) (access_goal ?V h)"
  interpret v: access_formed \<kappa> P ?V ?st by (rule access[OF Fr])
  interpret vf: access_formed \<kappa> P "access_focused F ?V" "finite_focused F ?st" by (rule v.focused)
  have rp: "?rp h \<longleftrightarrow> pr (finite_focused F ?st) (access_goal (access_focused F ?V) h)"
    if hf: "h |\<in>| access_goals (access_focused F ?V)" for h
  proof -
    have h: "h |\<in>| access_goals ?V" using hf by (simp add: access_focus_goals_def)
    show ?thesis
    proof (cases "gd r h")
      case True
      then have "?so = Some ?st" using h by auto
      then show ?thesis using True by simp
    next
      case False
      then show ?thesis using guard[OF Fr h False] by simp
    qed
  qed
  note sel = vf.select[of ?rp pr, OF rp]
  have fg: "fimage (access_goal ?V) (access_focus_goals F ?V) = finite_focus_pending F ?st" by (rule v.focus_goals)
  show ?thesis
  proof (cases "access_select ?rp (access_focused F ?V)")
    case (Access_Construction N)
    have s: "finite_resolution_select_at pr \<kappa> P (finite_focused F ?st) = Select_Construction (fimage (access_node ?V) N)"
      using sel(1) Access_Construction by simp
    have nd: "\<exists>q. m |\<in>| access_nodes_at ?V q" if m: "m |\<in>| N" for m
    proof -
      have "m |\<in>| access_construction_nodes (access_focused F ?V)" using Access_Construction m by (rule access_select_construction)
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
      unfolding represented_committed_step_def Let_def Access_Construction finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s M img fg)
  next
    case (Access_Goals G)
    have s: "finite_resolution_select_at pr \<kappa> P (finite_focused F ?st) = Select_Goals (fimage (access_goal ?V) G)"
      using sel(1) Access_Goals by simp
    have img: "fimage (represented_committed_goal_outcome R gd recI K F B r ?V ?so) G =
        fimage (finite_committed_goal_outcome ?recA K P F B ?st) (fimage (access_goal ?V) G)"
      unfolding fset.map_comp comp_def
    proof (rule fset.map_cong0)
      fix h assume hG: "h \<in> fset G"
      have "h |\<in>| access_goals (access_focused F ?V)" using Access_Goals hG by (rule access_select_goals)
      then have h: "h |\<in>| access_goals ?V" by (simp add: access_focus_goals_def)
      have so: "gd r h \<Longrightarrow> ?so = Some ?st" using h by auto
      show "represented_committed_goal_outcome R gd recI K F B r ?V ?so h =
          finite_committed_goal_outcome ?recA K P F B ?st (access_goal ?V h)"
        by (rule goal_outcome[where recA = ?recA and recI = recI, OF Fr h so rec recfound])
    qed
    show ?thesis
      unfolding represented_committed_step_def Let_def Access_Goals finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s img)
  next
    case Access_None
    have s: "finite_resolution_select_at pr \<kappa> P (finite_focused F ?st) = Select_None"
      using sel(1) Access_None by simp
    show ?thesis
      unfolding represented_committed_step_def Let_def Access_None finite_committed_search_by_in.simps(2) if_not_P[OF ne]
      by (simp add: s fg)
  qed
qed

lemma step_found:
  assumes Fr: "Fi r"
    and recfound: "\<And>F' B' s x. Fi s \<Longrightarrow> x |\<in>| resolution_found (recI F' B' s) \<Longrightarrow> \<exists>r0. Fi r0 \<and> rep_project R r0 = x"
    and x: "x |\<in>| resolution_found (represented_committed_step R pr gd \<kappa> K P recI F B r)"
  shows "\<exists>r0. Fi r0 \<and> rep_project R r0 = x"
proof -
  let ?V = "rep_access R r"
  let ?so = "if fBex (access_goals ?V) (gd r) then Some (rep_project R r) else None"
  let ?rp = "\<lambda>h. gd r h \<and> pr (the (map_option (finite_focused F) ?so)) (access_goal ?V h)"
  have goal: "\<exists>r0. Fi r0 \<and> rep_project R r0 = y"
    if h: "h |\<in>| access_goals ?V" and y: "y |\<in>| resolution_found (represented_committed_goal_outcome R gd recI K F B r ?V ?so h)"
    for h y
  proof (cases "access_pruned_among (\<lambda>q. q |\<notin>| B) ?V h \<or> access_pruned_among (\<lambda>q. q |\<in>| B) ?V h")
    case True
    then show ?thesis using y by (auto simp: represented_committed_goal_outcome_def split: if_splits)
  next
    case np: False
    show ?thesis
    proof (cases "gd r h \<and> finite_goal_committing K F (the ?so) (access_goal ?V h)")
      case True
      let ?g = "access_goal ?V h" let ?q = "resolution_goal_position ?g"
      let ?sub = "recI (Some ?q) (finite_goal_sub_barring K F B (the ?so) ?g) (represented_produced R K F r (the ?so) ?g)"
      have "y |\<in>| resolution_found (finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses ?sub))
          (fimage (\<lambda>s. recI F (finite_committed_barring B s) (rep_share R s)) (finite_kept ?q (resolution_found ?sub)))))"
        using y np True by (simp add: represented_committed_goal_outcome_def Let_def)
      then obtain s where s: "s |\<in>| finite_kept ?q (resolution_found ?sub)"
        and ys: "y |\<in>| resolution_found (recI F (finite_committed_barring B s) (rep_share R s))"
        by (auto simp: finite_outcome_union_def)
      have "s |\<in>| resolution_found ?sub" by (rule fsubsetD[OF finite_kept_subset s])
      from recfound[OF produced(1)[OF Fr] this] obtain r0 where r0: "Fi r0 \<and> rep_project R r0 = s" by (rule exE)
      have "Fi (rep_share R s)" using share[OF conjunct1[OF r0]] conjunct2[OF r0] by simp
      from recfound[OF this ys] show ?thesis .
    next
      case nc: False
      let ?cm = "gd r h \<and> finite_material_committed K F (the ?so) (access_goal ?V h)"
      let ?f = "recI F (if ?cm then B |\<union>| rep_node_positions R r else B)"
      let ?S = "represented_committed_successors R F ?cm r ?V h"
      let ?k = "\<lambda>s'. access_determinate_key (resolution_goal_position (access_goal ?V h)) (rep_access R s')"
      have yj: "y |\<in>| resolution_found (if access_focus_ground F ?V
          then finite_first_outcome ?f (finite_key_blocks ?k ?S) else finite_outcome_union (fimage ?f ?S))"
        using y np nc by (auto simp: represented_committed_goal_outcome_def Let_def split: if_splits)
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
  proof (cases "access_select ?rp (access_focused F ?V)")
    case (Access_Construction N)
    from x obtain m where m: "m |\<in>| N"
      and y: "x |\<in>| resolution_found (recI F (B |\<union>| rep_node_positions R r) (rep_construct R r m))"
      unfolding represented_committed_step_def Let_def Access_Construction
      by (auto simp: finite_outcome_union_def split: if_splits)
    have "m |\<in>| access_construction_nodes (access_focused F ?V)" using Access_Construction m by (rule access_select_construction)
    then have "\<exists>q. m |\<in>| access_nodes_at (access_focused F ?V) q" by (rule access_construction_nodes_at)
    then have "\<exists>q. m |\<in>| access_nodes_at ?V q" by (simp only: access_focused_simps)
    then obtain q where n: "m |\<in>| access_nodes_at ?V q" by (rule exE)
    show ?thesis using recfound[OF conjunct1[OF construct[OF Fr n]] y] .
  next
    case (Access_Goals G)
    from x obtain h where hG: "h |\<in>| G"
      and y: "x |\<in>| resolution_found (represented_committed_goal_outcome R gd recI K F B r ?V ?so h)"
      unfolding represented_committed_step_def Let_def Access_Goals by (auto simp: finite_outcome_union_def)
    have "h |\<in>| access_goals (access_focused F ?V)" using Access_Goals hG by (rule access_select_goals)
    then have h: "h |\<in>| access_goals ?V" by (simp add: access_focus_goals_def)
    show ?thesis by (rule goal[OF h y])
  next
    case Access_None
    then show ?thesis using x unfolding represented_committed_step_def Let_def by simp
  qed
qed

lemma found:
  assumes "Fi r" and "x |\<in>| resolution_found (represented_committed_search R pr gd \<kappa> K P n F B r)"
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
    have x: "x |\<in>| resolution_found (represented_committed_step R pr gd \<kappa> K P
        (represented_committed_search R pr gd \<kappa> K P n) F B (rep_refresh R r))"
      using Suc.prems(2) False by simp
    show ?thesis
    proof (rule step_found[OF f _ x])
      fix F' B' s y assume "Fi s" "y |\<in>| resolution_found (represented_committed_search R pr gd \<kappa> K P n F' B' s)"
      then show "\<exists>r0. Fi r0 \<and> rep_project R r0 = y" by (rule Suc.IH)
    qed
  qed
qed

theorem search:
  assumes "Fi r"
  shows "represented_committed_search R pr gd \<kappa> K P n F B r =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B (rep_project R r)"
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
    have e: "represented_committed_step R pr gd \<kappa> K P (represented_committed_search R pr gd \<kappa> K P n) F B (rep_refresh R r) =
        finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P (Suc n) F B (rep_project R (rep_refresh R r))"
    proof (rule step)
      show "Fi (rep_refresh R r)" by (rule f)
    next
      show "finite_focus_pending F (rep_project R (rep_refresh R r)) \<noteq> {||}" using False p by simp
    next
      fix F' B' s assume "Fi s"
      then show "represented_committed_search R pr gd \<kappa> K P n F' B' s =
          finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F' B' (rep_project R s)" by (rule Suc.IH)
    next
      fix F' B' s x assume "Fi s" "x |\<in>| resolution_found (represented_committed_search R pr gd \<kappa> K P n F' B' s)"
      then show "\<exists>r0. Fi r0 \<and> rep_project R r0 = x" by (rule found)
    qed
    have "represented_committed_search R pr gd \<kappa> K P (Suc n) F B r =
        represented_committed_step R pr gd \<kappa> K P (represented_committed_search R pr gd \<kappa> K P n) F B (rep_refresh R r)"
      using ne by simp
    then show ?thesis using e p by simp
  qed
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

lemma shared_committed_formed:
  assumes sock: "clause_sockets_distinct P"
    and guard: "\<And>s h F st. search_formed \<kappa> P s \<and> search_placeable (search_project s) \<Longrightarrow>
      h |\<in>| access_goals (shared_access \<kappa> P s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (shared_access \<kappa> P s) h) \<and>
      \<not> commit_material K F st (access_goal (shared_access \<kappa> P s) h) \<and> \<not> pr st (access_goal (shared_access \<kappa> P s) h)"
  shows "committed_representation_formed (shared_committed_representation \<kappa> P)
    (\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<kappa> P K pr gd"
proof (rule committed_representation_formed.intro, goal_cases)
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
next
  case (10 s h F st)
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

export_code finite_committed_search checking SML

end
