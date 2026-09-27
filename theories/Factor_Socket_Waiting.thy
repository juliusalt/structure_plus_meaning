theory Factor_Socket_Waiting
  imports Factor_Resolution_Modes
begin

section \<open>F1's selection with a waiting predicate beside its priority\<close>

text \<open>
  DECISIONS.md, task 495's entry, correction (16) of "Committed choice, for refusals": a class of F1's selection of its
  own. A goal the search settles at once (F1's class (i): no alternative, pruned, reusable, closed by the table) never
  waits. Among the unheld pending goals, the goals a waiting predicate names and that are not settled at once are set
  aside: the choice is F1's over the goals not set aside, and where that choice is empty, F1's over all the unheld goals,
  so the class never empties the selection: where the waiting selection selects nothing, today's selects nothing
  (@{text finite_resolution_select_waiting_none_selected_in}). The predicate is read by the selection alone: exactness
  rests on F1's two facts, which hold at every predicate.
\<close>

definition finite_goal_settled_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_settled_in \<Theta> P st g \<longleftrightarrow> finite_goal_alternatives P g = 0 \<or> finite_pruned st g \<or>
    finite_reusable st g \<or> finite_table_closes \<Theta> g"

definition finite_waiting_choice_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_waiting_choice_in \<Theta> pr wt P st G A = (let S0 = finite_goal_choice_in \<Theta> pr P st G
      (ffilter (\<lambda>g. \<not> wt st g \<or> finite_goal_settled_in \<Theta> P st g) A) in
    if S0 \<noteq> {||} then S0 else finite_goal_choice_in \<Theta> pr P st G A)"

lemma finite_waiting_choice_member:
  "g |\<in>| finite_waiting_choice_in \<Theta> pr wt P st G A \<Longrightarrow> g |\<in>| A \<and> finite_candidate_goal g"
  using finite_goal_choice_candidate_in[of g \<Theta> pr P st G A]
    finite_goal_choice_candidate_in[of g \<Theta> pr P st G "ffilter (\<lambda>g. \<not> wt st g \<or> finite_goal_settled_in \<Theta> P st g) A"]
  by (auto simp: finite_waiting_choice_in_def Let_def split: if_splits)

lemma finite_waiting_choice_empty:
  "finite_waiting_choice_in \<Theta> pr wt P st G A = {||} \<Longrightarrow> finite_goal_choice_in \<Theta> pr P st G A = {||}"
  by (simp add: finite_waiting_choice_in_def Let_def split: if_splits)

lemma finite_waiting_choice_none:
  "finite_waiting_choice_in \<Theta> pr (\<lambda>st g. False) P st G A = finite_goal_choice_in \<Theta> pr P st G A"
proof -
  have "ffilter (\<lambda>g. True) A = A" by (rule fset_eqI) simp
  then show ?thesis by (simp add: finite_waiting_choice_in_def Let_def)
qed

definition finite_resolution_select_waiting_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = (let G = resolution_pending st;
      N = ffilter (\<lambda>nd. finite_constructed \<kappa> P G nd\<noteq>{||}) (resolution_nodes st) in
    if N\<noteq>{||} then Select_Construction (finite_first_nodes N)
    else let S = finite_waiting_choice_in \<Theta> pr wt P st G (ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) G) in
      if S={||} then Select_None else Select_Goals S)"

text \<open>Today's selection is the waiting selection at the empty predicate.\<close>

lemma finite_resolution_select_waiting_none_in:
  "finite_resolution_select_waiting_in \<Theta> pr (\<lambda>st g. False) \<kappa> P = finite_resolution_select_in \<Theta> pr \<kappa> P"
  by (rule ext) (simp add: finite_resolution_select_waiting_in_def finite_resolution_select_in_def
    finite_waiting_choice_none Let_def)

text \<open>F1's two facts, at every predicate: a nonempty set of pending, unheld candidates, and a construction R3's.\<close>

lemma finite_resolution_select_waiting_goals_in:
  assumes sel: "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Goals G"
  shows "G \<noteq> {||} \<and>
    (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> \<not> finite_held \<kappa> st g \<and> finite_candidate_goal g)"
proof -
  define A where "A = ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) (resolution_pending st)"
  define S where "S = finite_waiting_choice_in \<Theta> pr wt P st (resolution_pending st) A"
  have G: "G = S \<and> S \<noteq> {||}"
    using sel unfolding finite_resolution_select_waiting_in_def Let_def A_def S_def by (simp split: if_splits)
  have "g |\<in>| resolution_pending st \<and> \<not> finite_held \<kappa> st g \<and> finite_candidate_goal g" if g: "g |\<in>| G" for g
  proof -
    have "g |\<in>| S" using G g by simp
    then have "g |\<in>| A \<and> finite_candidate_goal g" unfolding S_def by (rule finite_waiting_choice_member)
    then show ?thesis unfolding A_def by auto
  qed
  then show ?thesis using G by blast
qed

lemma finite_resolution_select_waiting_construction_in:
  "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Construction N \<longleftrightarrow>
    finite_resolution_select_in \<Theta> pr \<kappa> P st = Select_Construction N"
  unfolding finite_resolution_select_waiting_in_def finite_resolution_select_in_def Let_def
  by (cases "ffilter (\<lambda>nd. finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}) (resolution_nodes st) = {||}")
    simp_all

lemma finite_resolution_select_waiting_exact_in:
  shows "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> \<not> finite_held \<kappa> st g \<and> finite_candidate_goal g)"
    and "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Construction N \<longleftrightarrow>
      finite_resolution_select \<kappa> P st = Select_Construction N"
  subgoal by (rule finite_resolution_select_waiting_goals_in)
  subgoal unfolding finite_resolution_select_waiting_construction_in
    by (rule finite_resolution_select_construction_table)
  done

text \<open>The class never empties the selection: where the waiting selection selects nothing, today's selects nothing.\<close>

lemma finite_resolution_select_waiting_none_selected_in:
  "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_None \<Longrightarrow>
    finite_resolution_select_in \<Theta> pr \<kappa> P st = Select_None"
  unfolding finite_resolution_select_waiting_in_def finite_resolution_select_in_def Let_def
  by (cases "ffilter (\<lambda>nd. finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}) (resolution_nodes st) = {||}")
    (auto dest: finite_waiting_choice_empty split: if_splits)

lemma finite_resolution_select_waiting_framed_in:
  "finite_selection_framed (finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P)"
  unfolding finite_selection_framed_def
proof (intro conjI allI impI)
  fix st G assume sel: "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Goals G"
  show "G |\<subseteq>| resolution_pending st"
  proof (rule fsubsetI)
    fix g assume "g |\<in>| G"
    then show "g |\<in>| resolution_pending st" using finite_resolution_select_waiting_exact_in(1)[OF sel] by blast
  qed
next
  fix st N assume sel: "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P st = Select_Construction N"
  then have "finite_resolution_select \<kappa> P st = Select_Construction N"
    by (rule finite_resolution_select_waiting_exact_in(2)[THEN iffD1])
  then show "N |\<subseteq>| resolution_nodes st" by (rule finite_resolution_select_construction_in)
qed

lemma finite_resolution_select_waiting_unheld_in:
  "finite_selection_unheld \<kappa> (finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P)"
  unfolding finite_selection_unheld_def
proof (intro allI impI)
  fix F st G g
  assume sel: "finite_resolution_select_waiting_in \<Theta> pr wt \<kappa> P (finite_focused F st) = Select_Goals G"
    and g: "g |\<in>| G"
  show "\<not> finite_held \<kappa> st g"
    using finite_resolution_select_waiting_exact_in(1)[OF sel] g by (auto simp: finite_held_def finite_focused_def)
qed

section \<open>The socket waiting class\<close>

text \<open>
  The rule of correction (16): a pending goal g at the position of a node nd followed by a key waits when a pending call
  goal h at nd's position followed by another key s is a socket the record declares at nd's site, nd's schema and s, with
  views Vp and Vh, a frame C is declared for it at the same coordinates, and (a) h's viewed output at Vp holds a variable,
  (b) g holds no variable of h's viewed input at Vp, (c) g holds a variable of C's image under nd's binding or, g being no
  socket the record declares for nd's clause, of the image of nd's head output at Vh, (d) g is no mode binder. The class
  reads the declared sockets, their frames and views, the modes and the state: positions compared for a node's
  children, sites, schemas and keys compared with the record's tuples, variable sets of patterns and the node binding's
  images. A default frame is not read; material sockets order nothing.
\<close>

definition finite_node_image ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> 'a fset \<Rightarrow> ('s,'a) resolution_variable fset" where
  "finite_node_image nd A = ffUnion (fimage (\<lambda>a. finite_pattern_variables (finite_node_binding nd a)) A)"

definition finite_socket_waits ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> 'd resolution_modes \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_socket_waits D \<Phi> M st g \<longleftrightarrow> (let q = resolution_goal_position g; Vg = resolution_goal_variables g in
    g |\<in>| resolution_pending st \<and> q \<noteq> [] \<and> \<not> finite_mode_binder D M st g \<and>
    fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
      fBex (declared_sockets D) (\<lambda>(e,S,s,keep,Vp,Vh). e = resolution_node_site nd \<and>
        S = resolution_node_schema nd \<and> s \<noteq> last q \<and>
        fBex \<Phi> (\<lambda>(e',S',s',C). e' = e \<and> S' = S \<and> s' = s \<and>
          fBex (resolution_pending st) (\<lambda>h. case h of
              Resolution_Call_Goal qh rh dh ph \<Rightarrow> qh = resolution_node_position nd @ [s] \<and>
                (case resolution_view_pattern Vp ph of None \<Rightarrow> False
                  | Some (x,y) \<Rightarrow> finite_pattern_variables y \<noteq> {||} \<and> Vg |\<inter>| finite_pattern_variables x = {||} \<and>
                    (Vg |\<inter>| finite_node_image nd C \<noteq> {||} \<or>
                     (\<not> fBex (declared_sockets D) (\<lambda>(e1,S1,s1,keep1,V1,V2). e1 = e \<and> S1 = S \<and> s1 = last q) \<and>
                      (case resolution_view_pattern Vh (finite_schema_conclusion S) of None \<Rightarrow> False
                        | Some (hi,ho) \<Rightarrow> Vg |\<inter>| finite_node_image nd (finite_pattern_variables ho) \<noteq> {||}))))
            | Resolution_Material_Goal qh rh N \<Rightarrow> False)))))"

text \<open>At no frames the class names no goal.\<close>

lemma finite_socket_waits_no_frames: "\<not> finite_socket_waits D {||} M st g"
  unfolding finite_socket_waits_def Let_def by (auto elim!: fBexE)

lemma finite_socket_waits_no_frames_eq: "finite_socket_waits D {||} M = (\<lambda>st g. False)"
  by (intro ext) (simp add: finite_socket_waits_no_frames)

lemma finite_socket_waits_pending: "finite_socket_waits D \<Phi> M st g \<Longrightarrow> g |\<in>| resolution_pending st"
  by (simp add: finite_socket_waits_def Let_def)

lemma finite_socket_waits_not_binder: "finite_socket_waits D \<Phi> M st g \<Longrightarrow> \<not> finite_mode_binder D M st g"
  by (simp add: finite_socket_waits_def Let_def)

section \<open>The waiting moded selection\<close>

text \<open>
  The moded priority beside the socket waiting class, at a table: at no frames the moded selection at the table, at the
  empty table and no frames @{const finite_moded_select}.
\<close>

definition finite_waiting_moded_select_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow>
      'd resolution_modes \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P =
    finite_resolution_select_waiting_in \<Theta> (finite_moded_priority K D M) (finite_socket_waits D \<Phi> M) \<kappa> P"

lemma finite_waiting_moded_select_no_frames:
  "finite_waiting_moded_select_in \<Theta> \<kappa> K D {||} M P = finite_resolution_select_in \<Theta> (finite_moded_priority K D M) \<kappa> P"
  by (simp add: finite_waiting_moded_select_in_def finite_socket_waits_no_frames_eq
    finite_resolution_select_waiting_none_in)

lemma finite_waiting_moded_select_empty_table:
  "finite_waiting_moded_select_in resolution_empty_table \<kappa> K D {||} M P = finite_moded_select \<kappa> K D M P"
  by (rule finite_waiting_moded_select_no_frames)

lemma finite_waiting_moded_select_exact_in:
  shows "finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> \<not> finite_held \<kappa> st g \<and> finite_candidate_goal g)"
    and "finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P st = Select_Construction N \<longleftrightarrow>
      finite_resolution_select \<kappa> P st = Select_Construction N"
  unfolding finite_waiting_moded_select_in_def by (fact finite_resolution_select_waiting_exact_in)+

lemma finite_waiting_moded_select_framed_in: "finite_selection_framed (finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P)"
  unfolding finite_waiting_moded_select_in_def by (rule finite_resolution_select_waiting_framed_in)

lemma finite_waiting_moded_select_none_selected_in:
  "finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P st = Select_None \<Longrightarrow>
    finite_resolution_select_in \<Theta> (finite_moded_priority K D M) \<kappa> P st = Select_None"
  unfolding finite_waiting_moded_select_in_def by (rule finite_resolution_select_waiting_none_selected_in)

lemma finite_waiting_moded_select_unheld_in:
  "finite_selection_unheld \<kappa> (finite_waiting_moded_select_in \<Theta> \<kappa> K D \<Phi> M P)"
  unfolding finite_waiting_moded_select_in_def by (rule finite_resolution_select_waiting_unheld_in)

end
