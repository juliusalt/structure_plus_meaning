theory Factor_Search_Representations
  imports Factor_Resolution_Acceptance Finite_Set_Composition Finite_Set_Transformations
begin

section \<open>What a search accesses of a state\<close>

text \<open>
  Build F2b2 (b) of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size" (divided at
  q135). R3's search (@{const finite_resolution_search_by}) is computed over more than one representation of its
  state: F2b1's indexed state, which keeps R3's own patterns, and F2b2's shared state, which keeps them over one
  table of shared terms. What the tests, the selection and the search read of a state is stated once here, as an access
  of it: its goals and its nodes by position; what each goal caches (its position, its variables, its count of
  alternatives, its kind and the key of its ground call); whether a node closes a goal's ground call and whether two
  goals make the same call; the indexes of ground calls by key; the holder index; the counts of the goal positions
  at or under each position; the positions of registered variables; and F4's construction, read through the
  registered variables a node leaves free and the values it kept. An access is formed at an R3 state when each of these
  is what it presents of that state (@{text access_formed}). The tests, the selection and the search defined over a
  access are then R3's, each proved here once, for every representation whose accesses are formed.
\<close>

subsection \<open>Accesses and their formation\<close>

record ('g,'n,'k,'a,'s,'d,'c) search_access =
  access_goals :: "'g fset"
  access_goals_at :: "'s list \<Rightarrow> 'g fset"
  access_nodes_at :: "'s list \<Rightarrow> 'n fset"
  access_goal :: "'g \<Rightarrow> ('a,'s,'d,'c) resolution_goal"
  access_node :: "'n \<Rightarrow> ('a,'s,'d,'c) resolution_node"
  access_goal_position :: "'g \<Rightarrow> 's list"
  access_node_position :: "'n \<Rightarrow> 's list"
  access_variables :: "'g \<Rightarrow> ('s,'a) resolution_variable fset"
  access_alternatives :: "'g \<Rightarrow> nat"
  access_is_call :: "'g \<Rightarrow> bool"
  access_solvable :: "'g \<Rightarrow> bool"
  access_leaf :: "'g \<Rightarrow> bool"
  access_key :: "'g \<Rightarrow> 'k"
  access_closes :: "'n \<Rightarrow> 'g \<Rightarrow> bool"
  access_same :: "'g \<Rightarrow> 'g \<Rightarrow> bool"
  access_goal_calls :: "'k \<Rightarrow> 's list fset"
  access_node_calls :: "'k \<Rightarrow> 's list fset"
  access_open :: "'s list \<Rightarrow> nat"
  access_holders :: "'s list \<Rightarrow> 's list fset"
  access_free :: "'n \<Rightarrow> 'a fset"
  access_value_none :: "'n \<Rightarrow> 'a \<Rightarrow> bool"
  access_registered :: "'s list fset"
  access_holdable :: "'g \<Rightarrow> bool"
  access_witnesses :: "(('s,'a) resolution_variable \<times> finite_factor_term) fset"
  access_call_variables :: "'n \<Rightarrow> ('s,'a) resolution_variable fset"

text \<open>
  An access is formed at a state when its goals are the state's pending goals, one handle for each, found at their
  positions; its nodes are the state's nodes at their positions; its caches are what they cache; a node closes a
  goal's ground call and a goal makes the same call exactly as the state's values say, and the indexes of ground calls
  find every position where one is closed or made; the counts are zero exactly at the solved nodes; the holder index
  finds every goal holding a variable at a position; every position where a pending goal holds a registered variable is
  registered; every goal the state holds back is one the access may hold back; and the witnesses are the state's. The
  two indexes of ground calls may hold more than they must: a test reads only what it finds there and confirms.
\<close>

locale access_formed =
  fixes \<kappa> :: "('a,'s::linorder,'d,'c) finite_witness_construction" and P :: "('a,'s,'d,'c) finite_schema_system"
    and V :: "('g,'n,'k,'a,'s,'d,'c) search_access" and st :: "('a,'s,'d,'c) resolution_state"
  assumes pending: "resolution_pending st = fimage (access_goal V) (access_goals V)"
    and goals_at: "h |\<in>| access_goals_at V q \<longleftrightarrow> h |\<in>| access_goals V \<and> access_goal_position V h = q"
    and goal_inj: "h |\<in>| access_goals V \<Longrightarrow> h' |\<in>| access_goals V \<Longrightarrow> access_goal V h = access_goal V h' \<Longrightarrow> h = h'"
    and goal_position: "h |\<in>| access_goals V \<Longrightarrow> access_goal_position V h = resolution_goal_position (access_goal V h)"
    and variables: "h |\<in>| access_goals V \<Longrightarrow> access_variables V h = resolution_goal_variables (access_goal V h)"
    and alternatives: "h |\<in>| access_goals V \<Longrightarrow> access_alternatives V h = finite_goal_alternatives P (access_goal V h)"
    and is_call: "h |\<in>| access_goals V \<Longrightarrow> access_is_call V h \<longleftrightarrow> resolution_is_call (access_goal V h)"
    and solvable: "h |\<in>| access_goals V \<Longrightarrow> access_solvable V h \<longleftrightarrow> finite_solvable_material_goal (access_goal V h)"
    and leaf: "h |\<in>| access_goals V \<Longrightarrow> access_leaf V h \<longleftrightarrow> finite_leaf_call_goal (access_goal V h)"
    and node_call_variables: "n |\<in>| access_nodes_at V q \<Longrightarrow>
      access_call_variables V n = finite_pattern_variables (resolution_node_call (access_node V n))"
    and holdable: "h |\<in>| access_goals V \<Longrightarrow> finite_held \<kappa> st (access_goal V h) \<Longrightarrow> access_holdable V h"
    and nodes: "nd |\<in>| resolution_nodes st \<longleftrightarrow>
      (\<exists>n. n |\<in>| access_nodes_at V (resolution_node_position nd) \<and> access_node V n = nd)"
    and node_at: "n |\<in>| access_nodes_at V q \<Longrightarrow> access_node_position V n = q \<and> resolution_node_position (access_node V n) = q"
    and free: "n |\<in>| access_nodes_at V q \<Longrightarrow> access_free V n = finite_free_registered \<kappa> (access_node V n)"
    and value_none: "n |\<in>| access_nodes_at V q \<Longrightarrow>
      access_value_none V n a \<longleftrightarrow> finite_registered_value \<kappa> P (access_node V n) a = None"
    and closes: "h |\<in>| access_goals V \<Longrightarrow> access_goal V h = Resolution_Call_Goal q rr d p \<Longrightarrow> finite_pattern_variables p = {||} \<Longrightarrow>
      n |\<in>| access_nodes_at V q' \<Longrightarrow>
      access_closes V n h \<longleftrightarrow> resolution_node_site (access_node V n) = d \<and> resolution_node_call (access_node V n) = p"
    and node_calls: "h |\<in>| access_goals V \<Longrightarrow> access_goal V h = Resolution_Call_Goal q rr d p \<Longrightarrow>
      finite_pattern_variables p = {||} \<Longrightarrow> n |\<in>| access_nodes_at V q' \<Longrightarrow> access_closes V n h \<Longrightarrow>
      q' |\<in>| access_node_calls V (access_key V h)"
    and same: "h |\<in>| access_goals V \<Longrightarrow> h' |\<in>| access_goals V \<Longrightarrow> access_goal V h = Resolution_Call_Goal q rr d p \<Longrightarrow>
      finite_pattern_variables p = {||} \<Longrightarrow>
      access_same V h' h \<longleftrightarrow> (case access_goal V h' of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    and goal_calls: "h |\<in>| access_goals V \<Longrightarrow> h' |\<in>| access_goals V \<Longrightarrow> access_goal V h = Resolution_Call_Goal q rr d p \<Longrightarrow>
      finite_pattern_variables p = {||} \<Longrightarrow> access_same V h' h \<Longrightarrow>
      access_goal_position V h' |\<in>| access_goal_calls V (access_key V h)"
    and solved: "nd |\<in>| resolution_nodes st \<Longrightarrow> access_open V (resolution_node_position nd) = 0 \<longleftrightarrow> finite_solved_node st nd"
    and holders: "h |\<in>| access_goals V \<Longrightarrow> x |\<in>| access_variables V h \<Longrightarrow>
      access_goal_position V h |\<in>| access_holders V (fst (fst x))"
    and registered: "g |\<in>| resolution_pending st \<Longrightarrow> ((z,True),b) |\<in>| resolution_goal_variables g \<Longrightarrow>
      z |\<in>| access_registered V"
    and witnesses: "access_witnesses V = resolution_witnesses st"

subsection \<open>The tests\<close>

text \<open>
  Each test reads the goal's caches and the indexes; each is R3's test of the goal's value at the state the access
  presents. A ground call is closed by a node to its left, reused from a solved one, and waits on a goal before it
  making the same call or on an unsolved node to its left; each is found through the indexes of ground calls.
\<close>

definition access_ground :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_ground V h \<longleftrightarrow> access_is_call V h \<and> access_variables V h = {||}"

text \<open>
  A ground call's pruning among the nodes at positions a test admits: the barred nodes of a commitment, or the others;
  R3's pruning admits every position. The closing nodes are found through the index of ground calls, as reuse and
  waiting find them: a position the index gives for the call's key that is a proper prefix of the goal's position, the
  test admits, and holds a node closing the call.
\<close>

definition access_pruned_among :: "('s list \<Rightarrow> bool) \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_pruned_among X V h \<longleftrightarrow> access_ground V h \<and> fBex (access_node_calls V (access_key V h)) (\<lambda>q'.
    length q' < length (access_goal_position V h) \<and> take (length q') (access_goal_position V h) = q' \<and> X q' \<and>
    fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"

definition access_pruned :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_pruned V h \<longleftrightarrow> access_pruned_among (\<lambda>q. True) V h"

definition access_reusable :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_reusable V h \<longleftrightarrow> access_ground V h \<and> fBex (access_node_calls V (access_key V h)) (\<lambda>q'.
    finite_position_left q' (access_goal_position V h) \<and> access_open V q' = 0 \<and>
    fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"

definition access_waits :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_waits V h \<longleftrightarrow> access_ground V h \<and>
    (fBex (access_goal_calls V (access_key V h)) (\<lambda>q'. finite_position_less q' (access_goal_position V h) \<and>
       fBex (access_goals_at V q') (\<lambda>h'. access_same V h' h)) \<or>
     fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' (access_goal_position V h) \<and>
       access_open V q' \<noteq> 0 \<and> fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h)))"

definition access_independent :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_independent V h \<longleftrightarrow> access_is_call V h \<and> access_variables V h \<noteq> {||} \<and>
    fBall (access_variables V h) (\<lambda>x. fBall (access_holders V (fst (fst x)))
      (\<lambda>q'. fBall (access_goals_at V q') (\<lambda>h'. h' = h \<or> x |\<notin>| access_variables V h')))"

definition access_held :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_held V h \<longleftrightarrow> fBex (access_variables V h) (\<lambda>x. snd (fst x) \<and>
    fBex (access_nodes_at V (fst (fst x))) (\<lambda>n. snd x |\<in>| access_free V n))"

definition access_goal_holders :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> 'g fset" where
  "access_goal_holders V x = ffilter (\<lambda>h. x |\<in>| access_variables V h)
    (ffUnion (fimage (access_goals_at V) (access_holders V (fst (fst x)))))"

definition access_ready :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 's list \<Rightarrow> 'a \<Rightarrow> bool" where
  "access_ready V p a = (let x = ((p,True),a); H = access_goal_holders V x in
    H \<noteq> {||} \<and> fBall H (\<lambda>h. access_variables V h |\<subseteq>| {|x|}))"

definition access_constructed :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'n \<Rightarrow> 'a fset" where
  "access_constructed V n = ffilter (\<lambda>a. access_ready V (access_node_position V n) a \<and> \<not> access_value_none V n a)
    (access_free V n)"

definition access_construction_nodes :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'n fset" where
  "access_construction_nodes V = ffilter (\<lambda>n. access_constructed V n \<noteq> {||})
    (ffUnion (fimage (access_nodes_at V) (access_registered V)))"

lemma access_goal_holders_at:
  "h |\<in>| access_goal_holders V x \<longleftrightarrow>
    (\<exists>q. q |\<in>| access_holders V (fst (fst x)) \<and> h |\<in>| access_goals_at V q) \<and> x |\<in>| access_variables V h"
  by (auto simp: access_goal_holders_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)

lemma access_construction_nodes_at: "n |\<in>| access_construction_nodes V \<Longrightarrow> \<exists>q. n |\<in>| access_nodes_at V q"
  by (auto simp: access_construction_nodes_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)

text \<open>
  The construction nodes are filtered at each registered position before the union: the union is of the few nodes that
  construct, not of every node the registered positions hold.
\<close>

lemma access_construction_nodes_code [code]:
  "access_construction_nodes V =
    ffUnion (fimage (\<lambda>q. ffilter (\<lambda>n. access_constructed V n \<noteq> {||}) (access_nodes_at V q)) (access_registered V))"
  by (rule fset_eqI) (auto simp: access_construction_nodes_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)

context access_formed
begin

lemma goal_at: "h |\<in>| access_goals_at V q \<Longrightarrow> h |\<in>| access_goals V \<and> access_goal_position V h = q"
  using goals_at by blast

lemma goal_in_pending: "h |\<in>| access_goals V \<Longrightarrow> access_goal V h |\<in>| resolution_pending st"
  unfolding pending by (rule fimageI)

lemma pending_at:
  assumes g: "g |\<in>| resolution_pending st"
  obtains h where "h |\<in>| access_goals_at V (resolution_goal_position g)" "access_goal V h = g"
proof -
  obtain h where h: "h |\<in>| access_goals V" "access_goal V h = g" using g unfolding pending by (auto elim: fimageE)
  have "h |\<in>| access_goals_at V (resolution_goal_position g)" using h goal_position[OF h(1)] goals_at by simp
  then show ?thesis using h(2) that by blast
qed

lemma node_in:
  assumes n: "n |\<in>| access_nodes_at V q"
  shows "access_node V n |\<in>| resolution_nodes st"
proof -
  have "resolution_node_position (access_node V n) = q" using node_at[OF n] by simp
  then show ?thesis using nodes[of "access_node V n"] n by blast
qed

lemma node_set_at:
  assumes "nd |\<in>| resolution_nodes st"
  obtains n where "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
  using assms nodes by blast

lemma ground:
  assumes h: "h |\<in>| access_goals V"
  shows "access_ground V h \<longleftrightarrow> finite_ground_call_goal (access_goal V h)"
  using is_call[OF h] variables[OF h] by (cases "access_goal V h") (simp_all add: access_ground_def)

lemma pruned_among:
  assumes h: "h |\<in>| access_goals V"
  shows "access_pruned_among X V h \<longleftrightarrow> finite_pruned (Resolution_State (resolution_pending st)
    (ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)) (resolution_witnesses st)) (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q rr d p)
  have pos: "access_goal_position V h = q" using goal_position[OF h] Resolution_Call_Goal by simp
  have gr: "access_ground V h \<longleftrightarrow> finite_pattern_variables p = {||}" using ground[OF h] Resolution_Call_Goal by simp
  have eq: "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. length q' < length q \<and> take (length q') q = q' \<and> X q' \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h)) \<longleftrightarrow>
      fBex (ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    if g: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. length q' < length q \<and> take (length q') q = q' \<and> X q' \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
    then obtain q' n where i: "length q' < length q" "take (length q') q = q'" and x: "X q'"
      and n: "n |\<in>| access_nodes_at V q'" and c: "access_closes V n h" by blast
    have np: "resolution_node_position (access_node V n) = q'" using node_at[OF n] by simp
    have m: "resolution_node_site (access_node V n) = d" "resolution_node_call (access_node V n) = p"
      using closes[OF h Resolution_Call_Goal g n] c by simp_all
    have mem: "access_node V n |\<in>| ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)"
      using node_in[OF n] np x by simp
    show "fBex (ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    proof (rule rev_bexI[OF mem])
      show "length (resolution_node_position (access_node V n)) < length q \<and>
          take (length (resolution_node_position (access_node V n))) q = resolution_node_position (access_node V n) \<and>
          resolution_node_site (access_node V n) = d \<and> resolution_node_call (access_node V n) = p"
        using np i m by simp
    qed
  next
    assume "fBex (ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    then obtain nd where nd: "nd |\<in>| ffilter (\<lambda>nd. X (resolution_node_position nd)) (resolution_nodes st)"
        "length (resolution_node_position nd) < length q"
        "take (length (resolution_node_position nd)) q = resolution_node_position nd"
        "resolution_node_site nd = d" "resolution_node_call nd = p" by blast
    have nd0: "nd |\<in>| resolution_nodes st" and xn: "X (resolution_node_position nd)" using nd(1) by simp_all
    obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
      by (rule node_set_at[OF nd0])
    have c: "access_closes V n h" using closes[OF h Resolution_Call_Goal g n(1)] n(2) nd(4,5) by simp
    have k: "resolution_node_position nd |\<in>| access_node_calls V (access_key V h)"
      by (rule node_calls[OF h Resolution_Call_Goal g n(1) c])
    show "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. length q' < length q \<and> take (length q') q = q' \<and> X q' \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
      using k nd(2,3) xn n(1) c by blast
  qed
  show ?thesis
  proof (cases "finite_pattern_variables p = {||}")
    case True
    then show ?thesis using eq[OF True] pos gr Resolution_Call_Goal
      by (simp add: access_pruned_among_def finite_pruned_def)
  next
    case False
    then show ?thesis using gr Resolution_Call_Goal by (simp add: access_pruned_among_def finite_pruned_def)
  qed
next
  case (Resolution_Material_Goal q rr M)
  then show ?thesis using ground[OF h] by (simp add: access_pruned_among_def finite_pruned_def)
qed

lemma pruned:
  assumes h: "h |\<in>| access_goals V"
  shows "access_pruned V h \<longleftrightarrow> finite_pruned st (access_goal V h)"
proof -
  have e: "ffilter (\<lambda>nd. True) (resolution_nodes st) = resolution_nodes st" by (simp add: fset_eq_iff ffilter.rep_eq)
  show ?thesis using pruned_among[OF h, of "\<lambda>q. True"] e by (simp add: access_pruned_def finite_pruned_def)
qed

lemma reusable:
  assumes h: "h |\<in>| access_goals V"
  shows "access_reusable V h \<longleftrightarrow> finite_reusable st (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q rr d p)
  have pos: "access_goal_position V h = q" using goal_position[OF h] Resolution_Call_Goal by simp
  have gr: "access_ground V h \<longleftrightarrow> finite_pattern_variables p = {||}" using ground[OF h] Resolution_Call_Goal by simp
  have eq: "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' = 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h)) \<longleftrightarrow>
      fBex (resolution_nodes st) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node st nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    if g: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' = 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
    then obtain q' n where q': "finite_position_left q' q" "access_open V q' = 0"
      and n: "n |\<in>| access_nodes_at V q'" and c: "access_closes V n h" by auto
    have np: "resolution_node_position (access_node V n) = q'" using node_at[OF n] by simp
    have m: "resolution_node_site (access_node V n) = d" "resolution_node_call (access_node V n) = p"
      using closes[OF h Resolution_Call_Goal g n] c by simp_all
    have "finite_solved_node st (access_node V n)" using solved[OF node_in[OF n]] np q'(2) by simp
    then show "fBex (resolution_nodes st) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node st nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
      using node_in[OF n] np q'(1) m by auto
  next
    assume "fBex (resolution_nodes st) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node st nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    then obtain nd where nd: "nd |\<in>| resolution_nodes st" "finite_position_left (resolution_node_position nd) q"
        "finite_solved_node st nd" "resolution_node_site nd = d" "resolution_node_call nd = p" by auto
    obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
      by (rule node_set_at[OF nd(1)])
    have c: "access_closes V n h" using closes[OF h Resolution_Call_Goal g n(1)] n(2) nd(4,5) by simp
    have found: "resolution_node_position nd |\<in>| access_node_calls V (access_key V h)"
      by (rule node_calls[OF h Resolution_Call_Goal g n(1) c])
    have "access_open V (resolution_node_position nd) = 0" using solved[OF nd(1)] nd(3) by simp
    then show "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' = 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
      using found nd n c by auto
  qed
  show ?thesis
  proof (cases "finite_pattern_variables p = {||}")
    case True
    then show ?thesis using eq[OF True] pos gr Resolution_Call_Goal by (simp add: access_reusable_def finite_reusable_def)
  next
    case False
    then show ?thesis using gr Resolution_Call_Goal by (simp add: access_reusable_def finite_reusable_def)
  qed
next
  case (Resolution_Material_Goal q rr M)
  then show ?thesis using ground[OF h] by (simp add: access_reusable_def finite_reusable_def)
qed

lemma waits:
  assumes h: "h |\<in>| access_goals V"
  shows "access_waits V h \<longleftrightarrow> finite_goal_waits st (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q rr d p)
  have pos: "access_goal_position V h = q" using goal_position[OF h] Resolution_Call_Goal by simp
  have gr: "access_ground V h \<longleftrightarrow> finite_pattern_variables p = {||}" using ground[OF h] Resolution_Call_Goal by simp
  have goals: "fBex (access_goal_calls V (access_key V h)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (access_goals_at V q') (\<lambda>h'. access_same V h' h)) \<longleftrightarrow>
      fBex (resolution_pending st) (\<lambda>g. case g of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    if g: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (access_goal_calls V (access_key V h)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (access_goals_at V q') (\<lambda>h'. access_same V h' h))"
    then obtain q' h' where q': "finite_position_less q' q" and h': "h' |\<in>| access_goals_at V q'"
      and m: "access_same V h' h" by auto
    have h'g: "h' |\<in>| access_goals V" and p': "access_goal_position V h' = q'" using goal_at[OF h'] by simp_all
    have c: "case access_goal V h' of Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p
        | Resolution_Material_Goal q'' r'' M \<Rightarrow> False"
      using same[OF h h'g Resolution_Call_Goal g] m by simp
    have pp: "resolution_goal_position (access_goal V h') = q'" using goal_position[OF h'g] p' by simp
    show "fBex (resolution_pending st) (\<lambda>g. case g of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    proof (rule rev_bexI[OF goal_in_pending[OF h'g]])
      show "case access_goal V h' of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
          | Resolution_Material_Goal q' r' M \<Rightarrow> False"
        using c pp q' by (cases "access_goal V h'") auto
    qed
  next
    assume "fBex (resolution_pending st) (\<lambda>g. case g of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    then obtain g' where g': "g' |\<in>| resolution_pending st" and m: "case g' of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False" by auto
    then obtain q' r' where e: "g' = Resolution_Call_Goal q' r' d p" and less: "finite_position_less q' q"
      by (cases g') auto
    obtain h' where h': "h' |\<in>| access_goals_at V (resolution_goal_position g')" "access_goal V h' = g'"
      by (rule pending_at[OF g'])
    have h'g: "h' |\<in>| access_goals V" and p': "access_goal_position V h' = q'" using goal_at[OF h'(1)] e by simp_all
    have s: "access_same V h' h" using same[OF h h'g Resolution_Call_Goal g] h'(2) e by simp
    have "q' |\<in>| access_goal_calls V (access_key V h)" using goal_calls[OF h h'g Resolution_Call_Goal g s] p' by simp
    moreover have "h' |\<in>| access_goals_at V q'" using h'(1) e by simp
    ultimately show "fBex (access_goal_calls V (access_key V h)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (access_goals_at V q') (\<lambda>h'. access_same V h' h))"
      using less s by blast
  qed
  have nodes: "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' \<noteq> 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h)) \<longleftrightarrow>
      fBex (resolution_nodes st) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and> \<not> finite_solved_node st nd)"
    if g: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' \<noteq> 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
    then obtain q' n where q': "finite_position_left q' q" "access_open V q' \<noteq> 0"
      and n: "n |\<in>| access_nodes_at V q'" and c: "access_closes V n h" by auto
    have np: "resolution_node_position (access_node V n) = q'" using node_at[OF n] by simp
    have m: "resolution_node_site (access_node V n) = d" "resolution_node_call (access_node V n) = p"
      using closes[OF h Resolution_Call_Goal g n] c by simp_all
    have "\<not> finite_solved_node st (access_node V n)" using solved[OF node_in[OF n]] np q'(2) by simp
    then show "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and> \<not> finite_solved_node st nd)"
      using node_in[OF n] np q'(1) m by auto
  next
    assume "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and> \<not> finite_solved_node st nd)"
    then obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_site nd = d" "resolution_node_call nd = p"
        "finite_position_left (resolution_node_position nd) q" "\<not> finite_solved_node st nd" by auto
    obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
      by (rule node_set_at[OF nd(1)])
    have c: "access_closes V n h" using closes[OF h Resolution_Call_Goal g n(1)] n(2) nd(2,3) by simp
    have found: "resolution_node_position nd |\<in>| access_node_calls V (access_key V h)"
      by (rule node_calls[OF h Resolution_Call_Goal g n(1) c])
    have "access_open V (resolution_node_position nd) \<noteq> 0" using solved[OF nd(1)] nd(5) by simp
    then show "fBex (access_node_calls V (access_key V h)) (\<lambda>q'. finite_position_left q' q \<and> access_open V q' \<noteq> 0 \<and>
        fBex (access_nodes_at V q') (\<lambda>n. access_closes V n h))"
      using found nd n c by auto
  qed
  show ?thesis
  proof (cases "finite_pattern_variables p = {||}")
    case True
    then show ?thesis using goals[OF True] nodes[OF True] pos gr Resolution_Call_Goal
      by (simp add: access_waits_def finite_goal_waits_def)
  next
    case False
    then show ?thesis using gr Resolution_Call_Goal by (simp add: access_waits_def finite_goal_waits_def)
  qed
next
  case (Resolution_Material_Goal q rr M)
  then show ?thesis using ground[OF h] by (simp add: access_waits_def finite_goal_waits_def)
qed

lemma independent:
  assumes h: "h |\<in>| access_goals V"
  shows "access_independent V h \<longleftrightarrow> finite_independent_goal (resolution_pending st) (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q rr d p)
  have vars: "access_variables V h = finite_pattern_variables p" using variables[OF h] Resolution_Call_Goal by simp
  have call: "access_is_call V h" using is_call[OF h] Resolution_Call_Goal by simp
  have eq: "fBall (access_variables V h) (\<lambda>x. fBall (access_holders V (fst (fst x)))
          (\<lambda>q'. fBall (access_goals_at V q') (\<lambda>h'. h' = h \<or> x |\<notin>| access_variables V h'))) \<longleftrightarrow>
      fBall (resolution_pending st) (\<lambda>g. g = access_goal V h \<or>
        resolution_goal_variables g |\<inter>| resolution_goal_variables (access_goal V h) = {||})"
  proof
    assume all: "fBall (access_variables V h) (\<lambda>x. fBall (access_holders V (fst (fst x)))
          (\<lambda>q'. fBall (access_goals_at V q') (\<lambda>h'. h' = h \<or> x |\<notin>| access_variables V h')))"
    show "fBall (resolution_pending st) (\<lambda>g. g = access_goal V h \<or>
        resolution_goal_variables g |\<inter>| resolution_goal_variables (access_goal V h) = {||})"
    proof
      fix g assume g: "g \<in> fset (resolution_pending st)"
      obtain h' where h': "h' |\<in>| access_goals_at V (resolution_goal_position g)" "access_goal V h' = g"
        by (rule pending_at[OF g])
      have h'g: "h' |\<in>| access_goals V" and p': "access_goal_position V h' = resolution_goal_position g"
        using goal_at[OF h'(1)] by simp_all
      show "g = access_goal V h \<or> resolution_goal_variables g |\<inter>| resolution_goal_variables (access_goal V h) = {||}"
      proof (cases "g = access_goal V h")
        case False
        have "x |\<notin>| resolution_goal_variables g" if x: "x |\<in>| resolution_goal_variables (access_goal V h)" for x
        proof
          assume xg: "x |\<in>| resolution_goal_variables g"
          have xh': "x |\<in>| access_variables V h'" using xg h'(2) variables[OF h'g] by simp
          have xh: "x |\<in>| access_variables V h" using x variables[OF h] by simp
          have "access_goal_position V h' |\<in>| access_holders V (fst (fst x))" by (rule holders[OF h'g xh'])
          then have "h' = h \<or> x |\<notin>| access_variables V h'" using all xh h'(1) p' by auto
          then show False using False h'(2) xh' by auto
        qed
        then have "resolution_goal_variables g |\<inter>| resolution_goal_variables (access_goal V h) = {||}"
          unfolding fset_eq_iff finter_iff fempty_iff by blast
        then show ?thesis by simp
      qed simp
    qed
  next
    assume all: "fBall (resolution_pending st) (\<lambda>g. g = access_goal V h \<or>
        resolution_goal_variables g |\<inter>| resolution_goal_variables (access_goal V h) = {||})"
    show "fBall (access_variables V h) (\<lambda>x. fBall (access_holders V (fst (fst x)))
          (\<lambda>q'. fBall (access_goals_at V q') (\<lambda>h'. h' = h \<or> x |\<notin>| access_variables V h')))"
    proof (intro ballI)
      fix x q' h' assume x: "x \<in> fset (access_variables V h)" and q': "q' \<in> fset (access_holders V (fst (fst x)))"
        and h': "h' \<in> fset (access_goals_at V q')"
      have h'g: "h' |\<in>| access_goals V" using goal_at[of h' q'] h' by simp
      show "h' = h \<or> x |\<notin>| access_variables V h'"
      proof (cases "h' = h")
        case False
        then have ne: "access_goal V h' \<noteq> access_goal V h" using goal_inj[OF h'g h] by blast
        have "access_goal V h' |\<in>| resolution_pending st" by (rule goal_in_pending[OF h'g])
        then have dj: "resolution_goal_variables (access_goal V h') |\<inter>| resolution_goal_variables (access_goal V h) = {||}"
          using all ne by blast
        have "x |\<in>| resolution_goal_variables (access_goal V h)" using x variables[OF h] by simp
        then have "x |\<notin>| resolution_goal_variables (access_goal V h')" using dj by (metis finter_iff fempty_iff)
        then show ?thesis using variables[OF h'g] by simp
      qed simp
    qed
  qed
  then show ?thesis using vars call Resolution_Call_Goal
    by (simp add: access_independent_def finite_independent_goal_def)
next
  case (Resolution_Material_Goal q rr M)
  then show ?thesis using is_call[OF h] by (simp add: access_independent_def finite_independent_goal_def)
qed

lemma held:
  assumes h: "h |\<in>| access_goals V"
  shows "access_held V h \<longleftrightarrow> finite_held \<kappa> st (access_goal V h)"
proof
  assume "access_held V h"
  then obtain x n where x: "x |\<in>| access_variables V h" "snd (fst x)"
    and n: "n |\<in>| access_nodes_at V (fst (fst x))" and a: "snd x |\<in>| access_free V n"
    unfolding access_held_def by blast
  have pos: "resolution_node_position (access_node V n) = fst (fst x)" using node_at[OF n] by simp
  have xe: "((resolution_node_position (access_node V n), True), snd x) = x" using x(2) pos by (cases x) auto
  have fr: "snd x |\<in>| finite_free_registered \<kappa> (access_node V n)" using a free[OF n] by simp
  show "finite_held \<kappa> st (access_goal V h)"
    unfolding finite_held_def using node_in[OF n] fr x(1) xe variables[OF h] by force
next
  assume "finite_held \<kappa> st (access_goal V h)"
  then obtain nd a where nd: "nd |\<in>| resolution_nodes st" and a: "a |\<in>| finite_free_registered \<kappa> nd"
    and x: "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables (access_goal V h)"
    by (auto simp: finite_held_def)
  obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
    by (rule node_set_at[OF nd])
  have "a |\<in>| access_free V n" using a free[OF n(1)] n(2) by simp
  then show "access_held V h" unfolding access_held_def using n x variables[OF h] by force
qed

lemma goal_holders:
  "fimage (access_goal V) (access_goal_holders V x) = finite_goal_holders (resolution_pending st) x"
proof -
  have "g |\<in>| fimage (access_goal V) (access_goal_holders V x) \<longleftrightarrow> g |\<in>| finite_goal_holders (resolution_pending st) x" for g
  proof
    assume "g |\<in>| fimage (access_goal V) (access_goal_holders V x)"
    then obtain h q where h: "h |\<in>| access_goals_at V q" "x |\<in>| access_variables V h" "g = access_goal V h"
      by (auto simp: access_goal_holders_at fimage.rep_eq)
    have hg: "h |\<in>| access_goals V" using goal_at[OF h(1)] by simp
    show "g |\<in>| finite_goal_holders (resolution_pending st) x"
      using goal_in_pending[OF hg] h variables[OF hg] by (auto simp: finite_goal_holders_def ffilter.rep_eq)
  next
    assume "g |\<in>| finite_goal_holders (resolution_pending st) x"
    then have g: "g |\<in>| resolution_pending st" "x |\<in>| resolution_goal_variables g"
      by (auto simp: finite_goal_holders_def ffilter.rep_eq)
    obtain h where h: "h |\<in>| access_goals_at V (resolution_goal_position g)" "access_goal V h = g"
      by (rule pending_at[OF g(1)])
    have hg: "h |\<in>| access_goals V" and p: "access_goal_position V h = resolution_goal_position g"
      using goal_at[OF h(1)] by simp_all
    have xh: "x |\<in>| access_variables V h" using g(2) h(2) variables[OF hg] by simp
    have "resolution_goal_position g |\<in>| access_holders V (fst (fst x))" using holders[OF hg xh] p by simp
    then have "h |\<in>| access_goal_holders V x" using h(1) xh by (auto simp: access_goal_holders_at)
    then show "g |\<in>| fimage (access_goal V) (access_goal_holders V x)" using h(2) by (force simp: fimage.rep_eq)
  qed
  then show ?thesis by (auto simp: fset_eq_iff)
qed

lemma ready: "access_ready V (resolution_node_position nd) a \<longleftrightarrow> finite_registration_ready (resolution_pending st) nd a"
proof -
  let ?x = "((resolution_node_position nd,True),a)"
  let ?H = "access_goal_holders V ?x"
  have H: "finite_goal_holders (resolution_pending st) ?x = fimage (access_goal V) ?H" by (rule goal_holders[symmetric])
  have v: "access_variables V h = resolution_goal_variables (access_goal V h)" if "h |\<in>| ?H" for h
    using that goal_at variables by (auto simp: access_goal_holders_at)
  have e: "fimage (access_goal V) ?H = {||} \<longleftrightarrow> ?H = {||}" by (auto simp: fset_eq_iff fimage.rep_eq)
  have b: "fBall (fimage (access_goal V) ?H) (\<lambda>g. resolution_goal_variables g |\<subseteq>| {|?x|}) \<longleftrightarrow>
      fBall ?H (\<lambda>h. access_variables V h |\<subseteq>| {|?x|})"
    using v by (auto simp: fimage.rep_eq)
  show ?thesis unfolding access_ready_def finite_registration_ready_def Let_def H e b by simp
qed

lemma constructed:
  assumes n: "n |\<in>| access_nodes_at V q"
  shows "access_constructed V n = finite_constructed \<kappa> P (resolution_pending st) (access_node V n)"
proof -
  have pos: "access_node_position V n = resolution_node_position (access_node V n)" using node_at[OF n] by simp
  show ?thesis
    by (auto simp: fset_eq_iff access_constructed_def finite_constructed_def ffilter.rep_eq pos ready
        free[OF n] value_none[OF n])
qed

lemma construction_nodes:
  shows "fimage (access_node V) (access_construction_nodes V) =
      ffilter (\<lambda>nd. finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}) (resolution_nodes st)"
proof -
  have "nd |\<in>| fimage (access_node V) (access_construction_nodes V) \<longleftrightarrow>
      nd |\<in>| resolution_nodes st \<and> finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}" for nd
  proof
    assume "nd |\<in>| fimage (access_node V) (access_construction_nodes V)"
    then obtain n where n: "n |\<in>| access_construction_nodes V" "nd = access_node V n" by (auto simp: fimage.rep_eq)
    obtain q where q: "n |\<in>| access_nodes_at V q" using access_construction_nodes_at[OF n(1)] by blast
    have "access_constructed V n \<noteq> {||}" using n(1) by (auto simp: access_construction_nodes_def ffilter.rep_eq)
    then show "nd |\<in>| resolution_nodes st \<and> finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}"
      using node_in[OF q] n(2) constructed[OF q] by simp
  next
    assume a: "nd |\<in>| resolution_nodes st \<and> finite_constructed \<kappa> P (resolution_pending st) nd \<noteq> {||}"
    then obtain b where b: "b |\<in>| finite_constructed \<kappa> P (resolution_pending st) nd" by (metis all_not_fin_conv)
    let ?x = "((resolution_node_position nd,True),b)"
    have "finite_goal_holders (resolution_pending st) ?x \<noteq> {||}"
      using b by (auto simp: finite_constructed_def finite_registration_ready_def Let_def ffilter.rep_eq)
    then obtain g where g: "g |\<in>| resolution_pending st" "?x |\<in>| resolution_goal_variables g"
      by (auto simp: finite_goal_holders_def ffilter.rep_eq fset_eq_iff)
    have reg: "resolution_node_position nd |\<in>| access_registered V" by (rule registered[OF g])
    obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
      by (rule node_set_at[OF conjunct1[OF a]])
    have "access_constructed V n \<noteq> {||}" using a constructed[OF n(1)] n(2) by simp
    then have "n |\<in>| access_construction_nodes V"
      using n(1) reg by (force simp: access_construction_nodes_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)
    then show "nd |\<in>| fimage (access_node V) (access_construction_nodes V)" using n(2) by (force simp: fimage.rep_eq)
  qed
  then show ?thesis by (auto simp: fset_eq_iff ffilter.rep_eq)
qed

end

subsection \<open>The selection\<close>

text \<open>
  R3's goal selection (@{const finite_goal_selection}) forms its classes in order — ground calls, independent calls,
  solvable material goals, calls holding a leaf — each only when the ones before it are empty, and takes the first
  goals of the class; the waiting rule (@{const finite_waiting_selection}) asks it first of the goals that do not wait,
  and only when it takes none of those of all the goals. The choice at a priority (@{const finite_goal_choice}), stated
  here as @{text access_goal_choice}, has four classes, each formed only when the ones before it are empty: (i) the
  goals with no alternative, pruned or reusable; (ii) the goals the priority names; (iii) the goals with one
  alternative that do not wait; (iv) the waiting rule's selection. Classes (i) and (ii) take a ground call that waits
  as they take any other goal, unfiltered by waiting; class (iii) takes a goal only when it does not wait; class (iv)
  asks the goals that do not wait first.
\<close>

text \<open>
  The first of a finite set of things placed at positions reads their positions alone: it is stated over the position
  map, and the first goals and the first nodes of an access are its instances at the access's position maps.
\<close>

definition positioned_first :: "('x \<Rightarrow> 's::linorder list) \<Rightarrow> 'x fset \<Rightarrow> 'x fset" where
  "positioned_first pos H = ffilter (\<lambda>h. \<not> fBex H (\<lambda>h'. finite_position_less (pos h') (pos h))) H"

lemma positioned_first_member: "h |\<in>| positioned_first pos H \<Longrightarrow> h |\<in>| H"
  by (simp add: positioned_first_def ffilter.rep_eq)

definition access_first_goals :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_first_goals V H = positioned_first (access_goal_position V) H"

definition access_first_nodes :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'n fset \<Rightarrow> 'n fset" where
  "access_first_nodes V N = positioned_first (access_node_position V) N"

definition access_goal_selection :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_goal_selection V A = (let c1 = ffilter (access_ground V) A; c2 = ffilter (access_independent V) A;
      c3 = ffilter (access_solvable V) A; c4 = ffilter (access_leaf V) A in
    access_first_goals V (if c1 \<noteq> {||} then c1 else if c2 \<noteq> {||} then c2 else if c3 \<noteq> {||} then c3 else c4))"

definition access_waiting_selection :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_waiting_selection V A = (let W = access_goal_selection V (ffilter (\<lambda>h. \<not> access_waits V h) A) in
    if W \<noteq> {||} then W else access_goal_selection V A)"

definition access_goal_choice :: "('g \<Rightarrow> bool) \<Rightarrow> ('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_goal_choice rp V A = (let C = ffilter (\<lambda>h. access_is_call V h \<or> access_solvable V h) A;
      c0 = ffilter (\<lambda>h. access_alternatives V h = 0 \<or> access_pruned V h \<or> access_reusable V h) C in
    if c0 \<noteq> {||} then access_first_goals V c0
    else let cp = ffilter rp C in if cp \<noteq> {||} then access_first_goals V cp
    else let c1 = ffilter (\<lambda>h. access_alternatives V h = 1 \<and> \<not> access_waits V h) C in
      if c1 \<noteq> {||} then access_first_goals V c1
    else access_waiting_selection V A)"

datatype ('n,'g) access_selection = Access_Construction "'n fset" | Access_Goals "'g fset" | Access_None

fun access_selection_value :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('n,'g) access_selection \<Rightarrow>
    ('a,'s,'d,'c) resolution_selection" where
  "access_selection_value V (Access_Construction N) = Select_Construction (fimage (access_node V) N)"
| "access_selection_value V (Access_Goals G) = Select_Goals (fimage (access_goal V) G)"
| "access_selection_value V Access_None = Select_None"

text \<open>
  A goal the access may hold back is tested; any other is taken unfiltered: it holds no registered variable that a node
  leaves free.
\<close>

definition access_select :: "('g \<Rightarrow> bool) \<Rightarrow> ('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> ('n,'g) access_selection" where
  "access_select rp V = (let N = access_construction_nodes V in
    if N \<noteq> {||} then Access_Construction (access_first_nodes V N)
    else let S = access_goal_choice rp V (ffilter (\<lambda>h. \<not> (access_holdable V h \<and> access_held V h)) (access_goals V)) in
      if S = {||} then Access_None else Access_Goals S)"

text \<open>
  The choice and the selection at a table of certified calls (task 876): a ground call the table closes joins the first
  class, as R3's choice at a table has it (@{const finite_goal_choice_in}). The test is an argument, a goal's closing as
  the representation reads it; today's choice and selection are their instances at the test that closes nothing.
\<close>

definition access_goal_choice_in ::
    "('g \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> bool) \<Rightarrow> ('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_goal_choice_in E rp V A = (let C = ffilter (\<lambda>h. access_is_call V h \<or> access_solvable V h) A;
      c0 = ffilter (\<lambda>h. access_alternatives V h = 0 \<or> access_pruned V h \<or> access_reusable V h \<or> E h) C in
    if c0 \<noteq> {||} then access_first_goals V c0
    else let cp = ffilter rp C in if cp \<noteq> {||} then access_first_goals V cp
    else let c1 = ffilter (\<lambda>h. access_alternatives V h = 1 \<and> \<not> access_waits V h) C in
      if c1 \<noteq> {||} then access_first_goals V c1
    else access_waiting_selection V A)"

lemma access_goal_choice_in_empty: "access_goal_choice_in (\<lambda>h. False) rp V A = access_goal_choice rp V A"
  by (simp add: access_goal_choice_in_def access_goal_choice_def)

definition access_select_in ::
    "('g \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> bool) \<Rightarrow> ('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> ('n,'g) access_selection" where
  "access_select_in E rp V = (let N = access_construction_nodes V in
    if N \<noteq> {||} then Access_Construction (access_first_nodes V N)
    else let S = access_goal_choice_in E rp V (ffilter (\<lambda>h. \<not> (access_holdable V h \<and> access_held V h)) (access_goals V)) in
      if S = {||} then Access_None else Access_Goals S)"

lemma access_select_in_empty: "access_select_in (\<lambda>h. False) rp V = access_select rp V"
  by (simp add: access_select_in_def access_select_def access_goal_choice_in_empty Let_def)

lemma access_first_goals_member: "h |\<in>| access_first_goals V H \<Longrightarrow> h |\<in>| H"
  unfolding access_first_goals_def by (rule positioned_first_member)

lemma access_first_nodes_member: "n |\<in>| access_first_nodes V N \<Longrightarrow> n |\<in>| N"
  unfolding access_first_nodes_def by (rule positioned_first_member)

lemma access_goal_selection_member: "h |\<in>| access_goal_selection V A \<Longrightarrow> h |\<in>| A"
  by (auto simp: access_goal_selection_def Let_def ffilter.rep_eq dest: access_first_goals_member split: if_splits)

lemma access_waiting_selection_member: "h |\<in>| access_waiting_selection V A \<Longrightarrow> h |\<in>| A"
  by (auto simp: access_waiting_selection_def Let_def ffilter.rep_eq dest: access_goal_selection_member split: if_splits)

lemma access_goal_choice_member: "h |\<in>| access_goal_choice rp V A \<Longrightarrow> h |\<in>| A"
  by (auto simp: access_goal_choice_def Let_def ffilter.rep_eq
    dest: access_first_goals_member access_waiting_selection_member split: if_splits)

lemma access_select_construction:
  "access_select rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V"
  by (auto simp: access_select_def Let_def dest: access_first_nodes_member split: if_splits)

lemma access_select_goals: "access_select rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V"
  by (auto simp: access_select_def Let_def ffilter.rep_eq dest: access_goal_choice_member split: if_splits)

lemma access_goal_choice_in_member: "h |\<in>| access_goal_choice_in E rp V A \<Longrightarrow> h |\<in>| A"
  by (auto simp: access_goal_choice_in_def Let_def ffilter.rep_eq
    dest: access_first_goals_member access_waiting_selection_member split: if_splits)

lemma access_select_in_construction:
  "access_select_in E rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V"
  by (auto simp: access_select_in_def Let_def dest: access_first_nodes_member split: if_splits)

lemma access_select_in_goals: "access_select_in E rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V"
  by (auto simp: access_select_in_def Let_def ffilter.rep_eq dest: access_goal_choice_in_member split: if_splits)

context access_formed
begin

lemma first_goals:
  assumes H: "\<And>h. h |\<in>| H \<Longrightarrow> h |\<in>| access_goals V"
  shows "fimage (access_goal V) (access_first_goals V H) = finite_first_goals (fimage (access_goal V) H)"
proof -
  have pos: "\<And>h. h |\<in>| H \<Longrightarrow> access_goal_position V h = resolution_goal_position (access_goal V h)"
    using H goal_position by blast
  have "access_first_goals V H = ffilter (\<lambda>h. \<not> fBex H (\<lambda>h'. finite_position_less
      (resolution_goal_position (access_goal V h')) (resolution_goal_position (access_goal V h)))) H"
    unfolding access_first_goals_def positioned_first_def
  proof (rule ffilter_cong_on)
    fix h assume h: "h |\<in>| H"
    show "(\<not> fBex H (\<lambda>h'. finite_position_less (access_goal_position V h') (access_goal_position V h))) \<longleftrightarrow>
        (\<not> fBex H (\<lambda>h'. finite_position_less (resolution_goal_position (access_goal V h'))
          (resolution_goal_position (access_goal V h))))"
      using pos[OF h] pos by auto
  qed
  then show ?thesis by (auto simp: finite_first_goals_def fset_eq_iff fimage.rep_eq ffilter.rep_eq)
qed

lemma first_nodes:
  assumes N: "\<And>n. n |\<in>| N \<Longrightarrow> \<exists>q. n |\<in>| access_nodes_at V q"
  shows "fimage (access_node V) (access_first_nodes V N) = finite_first_nodes (fimage (access_node V) N)"
proof -
  have pos: "\<And>n. n |\<in>| N \<Longrightarrow> access_node_position V n = resolution_node_position (access_node V n)"
    using N node_at by metis
  have "access_first_nodes V N = ffilter (\<lambda>n. \<not> fBex N (\<lambda>m. finite_position_less
      (resolution_node_position (access_node V m)) (resolution_node_position (access_node V n)))) N"
    unfolding access_first_nodes_def positioned_first_def
  proof (rule ffilter_cong_on)
    fix n assume n: "n |\<in>| N"
    show "(\<not> fBex N (\<lambda>m. finite_position_less (access_node_position V m) (access_node_position V n))) \<longleftrightarrow>
        (\<not> fBex N (\<lambda>m. finite_position_less (resolution_node_position (access_node V m))
          (resolution_node_position (access_node V n))))"
      using pos[OF n] pos by auto
  qed
  then show ?thesis by (auto simp: finite_first_nodes_def fset_eq_iff fimage.rep_eq ffilter.rep_eq)
qed

lemma first_goals_filter:
  assumes B: "\<And>h. h |\<in>| B \<Longrightarrow> h |\<in>| access_goals V"
  shows "fimage (access_goal V) (access_first_goals V (ffilter F B)) = finite_first_goals (fimage (access_goal V) (ffilter F B))"
  by (rule first_goals) (use B in \<open>simp add: ffilter.rep_eq\<close>)

lemma goal_selection:
  assumes A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_goals V"
  shows "fimage (access_goal V) (access_goal_selection V A) =
      finite_goal_selection (resolution_pending st) (fimage (access_goal V) A)"
proof -
  have c1: "ffilter (access_ground V) A = ffilter (\<lambda>h. finite_ground_call_goal (access_goal V h)) A"
    by (rule ffilter_cong_on) (rule ground[OF A])
  have c2: "ffilter (access_independent V) A =
      ffilter (\<lambda>h. finite_independent_goal (resolution_pending st) (access_goal V h)) A"
    by (rule ffilter_cong_on) (rule independent[OF A])
  have c3: "ffilter (access_solvable V) A = ffilter (\<lambda>h. finite_solvable_material_goal (access_goal V h)) A"
    by (rule ffilter_cong_on) (rule solvable[OF A])
  have c4: "ffilter (access_leaf V) A = ffilter (\<lambda>h. finite_leaf_call_goal (access_goal V h)) A"
    by (rule ffilter_cong_on) (rule leaf[OF A])
  show ?thesis
    unfolding access_goal_selection_def finite_goal_selection_def Let_def c1 c2 c3 c4
    by (simp add: fimage_ffilter_value first_goals_filter[OF A] if_distrib[of "fimage (access_goal V)"]
        if_distrib[of "access_first_goals V"])
qed

lemma waiting_selection:
  assumes A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_goals V"
  shows "fimage (access_goal V) (access_waiting_selection V A) =
      finite_waiting_selection st (resolution_pending st) (fimage (access_goal V) A)"
proof -
  let ?A = "ffilter (\<lambda>h. \<not> finite_goal_waits st (access_goal V h)) A"
  have w: "ffilter (\<lambda>h. \<not> access_waits V h) A = ?A" by (rule ffilter_cong_on) (use waits[OF A] in simp)
  have A': "\<And>h. h |\<in>| ?A \<Longrightarrow> h |\<in>| access_goals V" using A by (simp add: ffilter.rep_eq)
  note s1 = goal_selection[where A="?A", OF A'] and s2 = goal_selection[where A=A, OF A]
  show ?thesis
    unfolding access_waiting_selection_def finite_waiting_selection_def Let_def w
    using s1[symmetric] s2[symmetric] by (simp add: fimage_ffilter_value if_distrib[of "fimage (access_goal V)"])
qed

lemma goal_choice_in:
  assumes A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_goals V"
    and rp: "\<And>h. h |\<in>| A \<Longrightarrow> rp h \<longleftrightarrow> pr st (access_goal V h)"
    and E: "\<And>h. h |\<in>| A \<Longrightarrow> E h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal V h)"
  shows "fimage (access_goal V) (access_goal_choice_in E rp V A) =
      finite_goal_choice_in \<Theta> pr P st (resolution_pending st) (fimage (access_goal V) A)"
proof -
  let ?C = "ffilter (\<lambda>h. finite_candidate_goal (access_goal V h)) A"
  have C: "ffilter (\<lambda>h. access_is_call V h \<or> access_solvable V h) A = ?C"
  proof (rule ffilter_cong_on)
    fix h assume h: "h |\<in>| A"
    show "(access_is_call V h \<or> access_solvable V h) \<longleftrightarrow> finite_candidate_goal (access_goal V h)"
      using is_call[OF A[OF h]] solvable[OF A[OF h]] by (simp add: finite_candidate_goal_def)
  qed
  have inC: "\<And>h. h |\<in>| ?C \<Longrightarrow> h |\<in>| access_goals V" using A by (simp add: ffilter.rep_eq)
  have c0: "ffilter (\<lambda>h. access_alternatives V h = 0 \<or> access_pruned V h \<or> access_reusable V h \<or> E h) ?C =
      ffilter (\<lambda>h. finite_goal_alternatives P (access_goal V h) = 0 \<or> finite_pruned st (access_goal V h) \<or>
        finite_reusable st (access_goal V h) \<or> finite_table_closes \<Theta> (access_goal V h)) ?C"
  proof (rule ffilter_cong_on)
    fix h assume hC: "h |\<in>| ?C"
    then have h: "h |\<in>| access_goals V" by (rule inC)
    have hA: "h |\<in>| A" using hC by (simp add: ffilter.rep_eq)
    show "(access_alternatives V h = 0 \<or> access_pruned V h \<or> access_reusable V h \<or> E h) \<longleftrightarrow>
        (finite_goal_alternatives P (access_goal V h) = 0 \<or> finite_pruned st (access_goal V h) \<or>
        finite_reusable st (access_goal V h) \<or> finite_table_closes \<Theta> (access_goal V h))"
      using alternatives[OF h] pruned[OF h] reusable[OF h] E[OF hA] by simp
  qed
  have cp: "ffilter rp ?C = ffilter (\<lambda>h. pr st (access_goal V h)) ?C"
    by (rule ffilter_cong_on) (use rp in \<open>auto simp: ffilter.rep_eq\<close>)
  have c1: "ffilter (\<lambda>h. access_alternatives V h = 1 \<and> \<not> access_waits V h) ?C =
      ffilter (\<lambda>h. finite_goal_alternatives P (access_goal V h) = 1 \<and> \<not> finite_goal_waits st (access_goal V h)) ?C"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| ?C"
    then have h: "h |\<in>| access_goals V" by (rule inC)
    show "(access_alternatives V h = 1 \<and> \<not> access_waits V h) \<longleftrightarrow>
        (finite_goal_alternatives P (access_goal V h) = 1 \<and> \<not> finite_goal_waits st (access_goal V h))"
      using alternatives[OF h] waits[OF h] by simp
  qed
  note w = waiting_selection[where A=A, OF A]
  let ?D0 = "ffilter (\<lambda>h. finite_goal_alternatives P (access_goal V h) = 0 \<or> finite_pruned st (access_goal V h) \<or>
        finite_reusable st (access_goal V h) \<or> finite_table_closes \<Theta> (access_goal V h)) ?C"
  let ?Dp = "ffilter (\<lambda>h. pr st (access_goal V h)) ?C"
  let ?D1 = "ffilter (\<lambda>h. finite_goal_alternatives P (access_goal V h) = 1 \<and> \<not> finite_goal_waits st (access_goal V h)) ?C"
  have l: "access_goal_choice_in E rp V A = (if ?D0 \<noteq> {||} then access_first_goals V ?D0
      else if ?Dp \<noteq> {||} then access_first_goals V ?Dp
      else if ?D1 \<noteq> {||} then access_first_goals V ?D1 else access_waiting_selection V A)"
    unfolding access_goal_choice_in_def Let_def C c0 cp c1 by (rule refl)
  have r: "finite_goal_choice_in \<Theta> pr P st (resolution_pending st) (fimage (access_goal V) A) =
      (if fimage (access_goal V) ?D0 \<noteq> {||} then finite_first_goals (fimage (access_goal V) ?D0)
       else if fimage (access_goal V) ?Dp \<noteq> {||} then finite_first_goals (fimage (access_goal V) ?Dp)
       else if fimage (access_goal V) ?D1 \<noteq> {||} then finite_first_goals (fimage (access_goal V) ?D1)
       else finite_waiting_selection st (resolution_pending st) (fimage (access_goal V) A))"
    unfolding finite_goal_choice_in_def Let_def fimage_snd_keyed by (simp add: fimage_ffilter_value)
  have f0: "fimage (access_goal V) (access_first_goals V ?D0) = finite_first_goals (fimage (access_goal V) ?D0)"
    by (rule first_goals) (use A in \<open>auto simp: ffilter.rep_eq\<close>)
  have fp: "fimage (access_goal V) (access_first_goals V ?Dp) = finite_first_goals (fimage (access_goal V) ?Dp)"
    by (rule first_goals) (use A in \<open>auto simp: ffilter.rep_eq\<close>)
  have f1: "fimage (access_goal V) (access_first_goals V ?D1) = finite_first_goals (fimage (access_goal V) ?D1)"
    by (rule first_goals) (use A in \<open>auto simp: ffilter.rep_eq\<close>)
  show ?thesis unfolding l r using f0 fp f1 w
    by (simp add: if_distrib[of "fimage (access_goal V)"])
qed

lemma goal_choice:
  assumes A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| access_goals V"
    and rp: "\<And>h. h |\<in>| A \<Longrightarrow> rp h \<longleftrightarrow> pr st (access_goal V h)"
  shows "fimage (access_goal V) (access_goal_choice rp V A) =
      finite_goal_choice pr P st (resolution_pending st) (fimage (access_goal V) A)"
proof -
  have E0: "\<And>h. h |\<in>| A \<Longrightarrow> False \<longleftrightarrow> finite_table_closes resolution_empty_table (access_goal V h)" by simp
  show ?thesis by (rule goal_choice_in[where pr=pr, OF A rp E0, unfolded access_goal_choice_in_empty])
qed

theorem select_in:
  assumes rp: "\<And>h. h |\<in>| access_goals V \<Longrightarrow> rp h \<longleftrightarrow> pr st (access_goal V h)"
    and E: "\<And>h. h |\<in>| access_goals V \<Longrightarrow> E h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal V h)"
  shows "access_selection_value V (access_select_in E rp V) = finite_resolution_select_in \<Theta> pr \<kappa> P st"
    and "access_select_in E rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V"
    and "access_select_in E rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V"
proof -
  let ?H = "ffilter (\<lambda>h. \<not> (access_holdable V h \<and> access_held V h)) (access_goals V)"
  have H: "\<And>h. h |\<in>| ?H \<Longrightarrow> h |\<in>| access_goals V" by (simp add: ffilter.rep_eq)
  have "?H = ffilter (\<lambda>h. \<not> finite_held \<kappa> st (access_goal V h)) (access_goals V)"
  proof (rule ffilter_cong_on)
    fix h assume h: "h |\<in>| access_goals V"
    show "(\<not> (access_holdable V h \<and> access_held V h)) \<longleftrightarrow> (\<not> finite_held \<kappa> st (access_goal V h))"
      using held[OF h] holdable[OF h] by blast
  qed
  then have hd: "fimage (access_goal V) ?H = ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) (resolution_pending st)"
    by (simp add: pending fimage_ffilter_value)
  have rpH: "\<And>h. h |\<in>| ?H \<Longrightarrow> rp h \<longleftrightarrow> pr st (access_goal V h)" using rp H by blast
  have EH: "\<And>h. h |\<in>| ?H \<Longrightarrow> E h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal V h)" using E H by blast
  note cn = construction_nodes and ch = goal_choice_in[where A="?H" and rp=rp and pr=pr, OF H rpH EH]
  have fn: "fimage (access_node V) (access_first_nodes V (access_construction_nodes V)) =
      finite_first_nodes (fimage (access_node V) (access_construction_nodes V))"
    by (rule first_nodes) (rule access_construction_nodes_at)
  show "access_selection_value V (access_select_in E rp V) = finite_resolution_select_in \<Theta> pr \<kappa> P st"
    unfolding access_select_in_def finite_resolution_select_in_def Let_def
    using cn[symmetric] hd[symmetric] ch[symmetric] fn
    by (simp add: if_distrib[of "access_selection_value V"])
  show "access_select_in E rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V"
    by (rule access_select_in_construction)
  show "access_select_in E rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V"
    by (rule access_select_in_goals)
qed

theorem select:
  assumes rp: "\<And>h. h |\<in>| access_goals V \<Longrightarrow> rp h \<longleftrightarrow> pr st (access_goal V h)"
  shows "access_selection_value V (access_select rp V) = finite_resolution_select_at pr \<kappa> P st"
    and "access_select rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V"
    and "access_select rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V"
proof -
  have E0: "\<And>h. h |\<in>| access_goals V \<Longrightarrow> False \<longleftrightarrow> finite_table_closes resolution_empty_table (access_goal V h)"
    by simp
  note s = select_in[where pr=pr, OF rp E0, unfolded access_select_in_empty]
  show "access_selection_value V (access_select rp V) = finite_resolution_select_at pr \<kappa> P st" by (rule s(1))
  show "access_select rp V = Access_Construction N \<Longrightarrow> n |\<in>| N \<Longrightarrow> n |\<in>| access_construction_nodes V" by (rule s(2))
  show "access_select rp V = Access_Goals G \<Longrightarrow> h |\<in>| G \<Longrightarrow> h |\<in>| access_goals V" by (rule s(3))
qed

end

subsection \<open>The selection through its classes\<close>

text \<open>
  Three of the choice's classes test a goal alone: a candidate is a call or a solvable material goal, a settled goal
  has no alternative or is pruned or reusable, and a single goal has one alternative and does not wait. The choice
  (@{const access_goal_choice}) is stated over these tests (@{text access_goal_choice_classes}), so that a
  representation keeping the goals that pass them reads its classes rather than testing every goal. Their R3 forms test
  the goal's value at the state (@{text goal_settled}, @{text goal_single}); a test of a ground call reads the state
  only through the nodes and the pending goals making that call and the solvedness of those nodes
  (@{text goal_tests_frame}). The first of a class read in the order of positions is its first member
  (@{text positioned_first_sorted}).
\<close>

definition access_candidate :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_candidate V h \<longleftrightarrow> access_is_call V h \<or> access_solvable V h"

definition access_settled :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_settled V h \<longleftrightarrow> access_alternatives V h = 0 \<or> access_pruned V h \<or> access_reusable V h"

definition access_single :: "('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow> bool" where
  "access_single V h \<longleftrightarrow> access_alternatives V h = 1 \<and> \<not> access_waits V h"

lemma access_goal_choice_classes_in:
  "access_goal_choice_in E rp V A = (let c0 = ffilter (\<lambda>h. access_candidate V h \<and> (access_settled V h \<or> E h)) A in
    if c0 \<noteq> {||} then access_first_goals V c0
    else let cp = ffilter rp (ffilter (access_candidate V) A) in if cp \<noteq> {||} then access_first_goals V cp
    else let c1 = ffilter (\<lambda>h. access_candidate V h \<and> access_single V h) A in
      if c1 \<noteq> {||} then access_first_goals V c1
    else access_waiting_selection V A)"
proof -
  have e: "ffilter F (ffilter G A) = ffilter (\<lambda>h. G h \<and> F h) A" for F G by (rule fset_eqI) (auto simp: ffilter.rep_eq)
  show ?thesis
    unfolding access_goal_choice_in_def access_candidate_def access_settled_def access_single_def Let_def
    by (simp add: e disj_assoc)
qed

lemma access_goal_choice_classes:
  "access_goal_choice rp V A = (let c0 = ffilter (\<lambda>h. access_candidate V h \<and> access_settled V h) A in
    if c0 \<noteq> {||} then access_first_goals V c0
    else let cp = ffilter rp (ffilter (access_candidate V) A) in if cp \<noteq> {||} then access_first_goals V cp
    else let c1 = ffilter (\<lambda>h. access_candidate V h \<and> access_single V h) A in
      if c1 \<noteq> {||} then access_first_goals V c1
    else access_waiting_selection V A)"
proof -
  have e: "ffilter F (ffilter G A) = ffilter (\<lambda>h. G h \<and> F h) A" for F G by (rule fset_eqI) (auto simp: ffilter.rep_eq)
  show ?thesis
    unfolding access_goal_choice_def access_candidate_def access_settled_def access_single_def Let_def by (simp add: e)
qed

text \<open>
  The choice at a priority given as a class of the candidates rather than a test of each (task 871): the choice at a
  test is its instance where the class filters the candidates by that test (@{text access_goal_choice_by}).
\<close>

definition access_goal_choice_by ::
    "('g fset \<Rightarrow> 'g fset) \<Rightarrow> ('g,'n,'k,'a,'s::linorder,'d,'c) search_access \<Rightarrow> 'g fset \<Rightarrow> 'g fset" where
  "access_goal_choice_by pc V A = (let c0 = ffilter (\<lambda>h. access_candidate V h \<and> access_settled V h) A in
    if c0 \<noteq> {||} then access_first_goals V c0
    else let cp = pc (ffilter (access_candidate V) A) in if cp \<noteq> {||} then access_first_goals V cp
    else let c1 = ffilter (\<lambda>h. access_candidate V h \<and> access_single V h) A in
      if c1 \<noteq> {||} then access_first_goals V c1
    else access_waiting_selection V A)"

lemma access_goal_choice_by:
  assumes "pc (ffilter (access_candidate V) A) = ffilter rp (ffilter (access_candidate V) A)"
  shows "access_goal_choice_by pc V A = access_goal_choice rp V A"
  by (simp only: access_goal_choice_by_def access_goal_choice_classes Let_def assms)

definition goal_settled :: "nat \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "goal_settled n st g \<longleftrightarrow> n = 0 \<or> finite_pruned st g \<or> finite_reusable st g"

definition goal_single :: "nat \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "goal_single n st g \<longleftrightarrow> n = 1 \<and> \<not> finite_goal_waits st g"

context access_formed
begin

lemma candidate: "h |\<in>| access_goals V \<Longrightarrow> access_candidate V h \<longleftrightarrow> finite_candidate_goal (access_goal V h)"
  by (simp add: access_candidate_def finite_candidate_goal_def is_call solvable)

lemma settled:
  "h |\<in>| access_goals V \<Longrightarrow> access_settled V h \<longleftrightarrow> goal_settled (access_alternatives V h) st (access_goal V h)"
  by (simp add: access_settled_def goal_settled_def pruned reusable)

lemma single:
  "h |\<in>| access_goals V \<Longrightarrow> access_single V h \<longleftrightarrow> goal_single (access_alternatives V h) st (access_goal V h)"
  by (simp add: access_single_def goal_single_def waits)

end

text \<open>
  A test of a ground call is the same at two states that hold nodes making the call at the same positions, solved alike,
  and pending goals making it at the same positions: it reads the nodes and the goals by their positions, and what a step
  changes elsewhere, or in a node or a goal there that keeps its call, leaves it as it is.
\<close>

lemma goal_tests_frame:
  assumes N: "\<And>q'. (\<exists>nd. nd |\<in>| resolution_nodes st' \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
        resolution_node_call nd = p) \<longleftrightarrow>
      (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
        resolution_node_call nd = p)"
    and S: "\<And>q'. (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
        resolution_node_call nd = p) \<Longrightarrow>
      fBex (resolution_pending st') (\<lambda>g. take (length q') (resolution_goal_position g) = q') \<longleftrightarrow>
      fBex (resolution_pending st) (\<lambda>g. take (length q') (resolution_goal_position g) = q')"
    and G: "\<And>q'. (\<exists>r'. Resolution_Call_Goal q' r' d p |\<in>| resolution_pending st') \<longleftrightarrow>
      (\<exists>r'. Resolution_Call_Goal q' r' d p |\<in>| resolution_pending st)"
  shows "finite_pruned st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_pruned st (Resolution_Call_Goal q r d p)"
    and "finite_reusable st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_reusable st (Resolution_Call_Goal q r d p)"
    and "finite_goal_waits st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_goal_waits st (Resolution_Call_Goal q r d p)"
proof -
  let ?at = "\<lambda>X q'. \<exists>nd. nd |\<in>| X \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
    resolution_node_call nd = p"
  let ?open = "\<lambda>Y q'. fBex Y (\<lambda>g. take (length q') (resolution_goal_position g) = q')"
  have pr: "fBex X (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p) \<longleftrightarrow>
      (\<exists>q'. ?at X q' \<and> length q' < length q \<and> take (length q') q = q')" for X by blast
  have re: "fBex X (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        \<not> ?open Y (resolution_node_position nd) \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p) \<longleftrightarrow>
      (\<exists>q'. ?at X q' \<and> finite_position_left q' q \<and> \<not> ?open Y q')" for X Y by blast
  have wa: "fBex X (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and> ?open Y (resolution_node_position nd)) \<longleftrightarrow>
      (\<exists>q'. ?at X q' \<and> finite_position_left q' q \<and> ?open Y q')" for X Y by blast
  have e: "fBex X (\<lambda>h. case h of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False) \<longleftrightarrow>
      (\<exists>q'. (\<exists>r'. Resolution_Call_Goal q' r' d p |\<in>| X) \<and> finite_position_less q' q)" for X
  proof
    assume "fBex X (\<lambda>h. case h of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    then obtain h where h: "h |\<in>| X" "case h of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and>
        finite_position_less q' q | Resolution_Material_Goal q' r' M \<Rightarrow> False" by blast
    then show "\<exists>q'. (\<exists>r'. Resolution_Call_Goal q' r' d p |\<in>| X) \<and> finite_position_less q' q" by (cases h) auto
  next
    assume "\<exists>q'. (\<exists>r'. Resolution_Call_Goal q' r' d p |\<in>| X) \<and> finite_position_less q' q"
    then show "fBex X (\<lambda>h. case h of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)" by force
  qed
  have opened: "\<And>A' A L U' U. (A' \<longleftrightarrow> A) \<Longrightarrow> (A \<Longrightarrow> U' \<longleftrightarrow> U) \<Longrightarrow> (A' \<and> L \<and> U' \<longleftrightarrow> A \<and> L \<and> U)"
    and closed: "\<And>A' A L U' U. (A' \<longleftrightarrow> A) \<Longrightarrow> (A \<Longrightarrow> U' \<longleftrightarrow> U) \<Longrightarrow> (A' \<and> L \<and> \<not> U' \<longleftrightarrow> A \<and> L \<and> \<not> U)"
    by blast+
  have W: "?at (resolution_nodes st') q' \<and> finite_position_left q' q \<and> ?open (resolution_pending st') q' \<longleftrightarrow>
      ?at (resolution_nodes st) q' \<and> finite_position_left q' q \<and> ?open (resolution_pending st) q'" for q'
    by (rule opened[OF N S])
  have R: "?at (resolution_nodes st') q' \<and> finite_position_left q' q \<and> \<not> ?open (resolution_pending st') q' \<longleftrightarrow>
      ?at (resolution_nodes st) q' \<and> finite_position_left q' q \<and> \<not> ?open (resolution_pending st) q'" for q'
    by (rule closed[OF N S])
  show "finite_pruned st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_pruned st (Resolution_Call_Goal q r d p)"
    unfolding finite_pruned_def resolution_goal.case pr by (simp only: N)
  show "finite_reusable st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_reusable st (Resolution_Call_Goal q r d p)"
    unfolding finite_reusable_def resolution_goal.case finite_solved_node_def re by (simp only: R)
  show "finite_goal_waits st' (Resolution_Call_Goal q r d p) \<longleftrightarrow> finite_goal_waits st (Resolution_Call_Goal q r d p)"
    unfolding finite_goal_waits_def resolution_goal.case finite_solved_node_def not_not e wa by (simp only: G W)
qed

lemma positioned_first_sorted:
  fixes pos :: "'x \<Rightarrow> 's::linorder list"
  assumes "sorted_wrt (\<lambda>x y. finite_position_less (pos x) (pos y)) xs"
  shows "positioned_first pos (fset_of_list (filter Q xs)) = (case find Q xs of None \<Rightarrow> {||} | Some x \<Rightarrow> {|x|})"
  using assms
proof (induction xs)
  case Nil
  then show ?case by (simp add: positioned_first_def fset_eq_iff ffilter.rep_eq)
next
  case (Cons x xs)
  have irr: "\<not> finite_position_less p p" for p :: "'s list"
    unfolding finite_position_less_def by (rule lexord_irreflexive) simp
  have tr: "finite_position_less a c" if "finite_position_less a b" "finite_position_less b c" for a b c :: "'s list"
    using that unfolding finite_position_less_def by (rule lexord_trans) (auto simp: trans_def)
  have after: "finite_position_less (pos x) (pos y)" if "y \<in> set xs" for y using Cons.prems that by simp
  show ?case
  proof (cases "Q x")
    case True
    have "positioned_first pos (fset_of_list (x # filter Q xs)) = {|x|}"
    proof (rule fset_eqI)
      fix h
      show "h |\<in>| positioned_first pos (fset_of_list (x # filter Q xs)) \<longleftrightarrow> h |\<in>| {|x|}"
      proof
        assume "h |\<in>| positioned_first pos (fset_of_list (x # filter Q xs))"
        then have hin: "h = x \<or> h \<in> set xs"
          and first: "\<not> (\<exists>h'\<in>set (x # filter Q xs). finite_position_less (pos h') (pos h))"
          by (auto simp: positioned_first_def ffilter.rep_eq fset_of_list.rep_eq)
        show "h |\<in>| {|x|}"
        proof (cases "h = x")
          case False
          then have "h \<in> set xs" using hin by simp
          then have "finite_position_less (pos x) (pos h)" by (rule after)
          then show ?thesis using first by simp
        qed simp
      next
        assume "h |\<in>| {|x|}"
        then have hx: "h = x" by simp
        have "\<not> finite_position_less (pos h') (pos x)" if "h' \<in> set (x # filter Q xs)" for h'
        proof (cases "h' = x")
          case True
          then show ?thesis using irr by simp
        next
          case False
          then have "h' \<in> set xs" using that by simp
          then have "finite_position_less (pos x) (pos h')" by (rule after)
          then show ?thesis using irr tr by blast
        qed
        then show "h |\<in>| positioned_first pos (fset_of_list (x # filter Q xs))"
          using hx by (auto simp: positioned_first_def ffilter.rep_eq fset_of_list.rep_eq)
      qed
    qed
    then show ?thesis using True by simp
  next
    case False
    then show ?thesis using Cons.IH Cons.prems by simp
  qed
qed

section \<open>The search over a representation\<close>

text \<open>
  A representation of R3's state gives each state its access, whether it holds goals, its projection, the refresh of
  F4's kept constructions, the construction step at a node and the successors of a goal. The search over it is R3's
  search written once: it refreshes, selects through the access, steps, and diagnoses through the access and the
  projection. By induction on the bound over the step equations, a representation whose steps are R3's and whose
  accesses are formed searches as R3 does.
\<close>

record ('r,'g,'n,'k,'a,'s,'d,'c) resolution_representation =
  rep_access :: "'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access"
  rep_empty :: "'r \<Rightarrow> bool"
  rep_project :: "'r \<Rightarrow> ('a,'s,'d,'c) resolution_state"
  rep_refresh :: "'r \<Rightarrow> 'r"
  rep_construct :: "'r \<Rightarrow> 'n \<Rightarrow> 'r"
  rep_successors :: "'r \<Rightarrow> 'g \<Rightarrow> 'r fset"

definition represented_goal_outcome :: "('r,'g,'n,'k,'a,'s,'d,'c) resolution_representation \<Rightarrow>
    ('r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow> 'r \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> 'g \<Rightarrow>
    ('a,'s,'d,'c) resolution_outcome" where
  "represented_goal_outcome R rec r V h = (if access_pruned V h then Resolution_Outcome {||} {||} else
    let S = rep_successors R r h in
    if S = {||} then (if access_witnesses V = {||} then Resolution_Outcome {||} {||}
      else Resolution_Outcome {||} {|Resolution_Witnessed (access_witnesses V) (access_goal V h)|})
    else finite_outcome_union (fimage rec S))"

text \<open>
  The search at a table of certified calls (task 876): its selection reads the table's closing test of the state it
  stands at, an argument as the priority is, and its successors are R3's at the table; today's search is its instance
  at the test that closes nothing (@{text represented_search_in_empty}).
\<close>

primrec represented_search_in :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c) resolution_representation \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
    ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 'r \<Rightarrow>
    ('a,'s,'d,'c) resolution_outcome" where
  "represented_search_in R E rp \<kappa> P 0 r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal (rep_access R r)) (access_goals (rep_access R r)))|})"
| "represented_search_in R E rp \<kappa> P (Suc n) r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else let r' = rep_refresh R r; V = rep_access R r' in (case access_select_in (E r') (rp r') V of
      Access_Construction N \<Rightarrow> finite_outcome_union (fimage (\<lambda>m. represented_search_in R E rp \<kappa> P n (rep_construct R r' m)) N)
    | Access_Goals G \<Rightarrow> finite_outcome_union (fimage (represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) r' V) G)
    | Access_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_goals V))) (finite_unconstructed \<kappa> P (rep_project R r')))))"

primrec represented_search :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c) resolution_representation \<Rightarrow> ('r \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow>
    ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 'r \<Rightarrow>
    ('a,'s,'d,'c) resolution_outcome" where
  "represented_search R rp \<kappa> P 0 r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal (rep_access R r)) (access_goals (rep_access R r)))|})"
| "represented_search R rp \<kappa> P (Suc n) r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else let r' = rep_refresh R r; V = rep_access R r' in (case access_select (rp r') V of
      Access_Construction N \<Rightarrow> finite_outcome_union (fimage (\<lambda>m. represented_search R rp \<kappa> P n (rep_construct R r' m)) N)
    | Access_Goals G \<Rightarrow> finite_outcome_union (fimage (represented_goal_outcome R (represented_search R rp \<kappa> P n) r' V) G)
    | Access_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_goals V))) (finite_unconstructed \<kappa> P (rep_project R r')))))"

lemma represented_search_in_empty:
  "represented_search_in R (\<lambda>s h. False) rp \<kappa> P n = represented_search R rp \<kappa> P n"
proof (induction n)
  case 0
  show ?case by (simp add: fun_eq_iff)
next
  case (Suc n)
  show ?case
  proof (rule ext)
    fix r
    show "represented_search_in R (\<lambda>s h. False) rp \<kappa> P (Suc n) r = represented_search R rp \<kappa> P (Suc n) r"
      unfolding represented_search_in.simps represented_search.simps Suc.IH access_select_in_empty by (rule refl)
  qed
qed

lemma represented_goal_outcome_in:
  assumes V: "access_formed \<kappa> P (rep_access R r) (rep_project R r)" and h: "h |\<in>| access_goals (rep_access R r)"
    and succ: "fimage (rep_project R) (rep_successors R r h) =
      finite_goal_successors_in \<Theta> P (rep_project R r) (access_goal (rep_access R r) h)"
    and rec: "\<And>s. s |\<in>| rep_successors R r h \<Longrightarrow> recI s = recA (rep_project R s)"
  shows "represented_goal_outcome R recI r (rep_access R r) h =
      finite_goal_outcome_in \<Theta> recA P (rep_project R r) (access_goal (rep_access R r) h)"
proof -
  interpret access_formed \<kappa> P "rep_access R r" "rep_project R r" by (rule V)
  have img: "fimage recI (rep_successors R r h) = fimage recA (fimage (rep_project R) (rep_successors R r h))"
    unfolding fset.map_comp comp_def by (rule fset.map_cong0) (simp add: rec)
  show ?thesis using img succ[symmetric] pruned[OF h] witnesses
    by (simp add: represented_goal_outcome_def finite_goal_outcome_in_def Let_def)
qed

lemma represented_goal_outcome:
  assumes V: "access_formed \<kappa> P (rep_access R r) (rep_project R r)" and h: "h |\<in>| access_goals (rep_access R r)"
    and succ: "fimage (rep_project R) (rep_successors R r h) =
      finite_goal_successors P (rep_project R r) (access_goal (rep_access R r) h)"
    and rec: "\<And>s. s |\<in>| rep_successors R r h \<Longrightarrow> recI s = recA (rep_project R s)"
  shows "represented_goal_outcome R recI r (rep_access R r) h =
      finite_goal_outcome recA P (rep_project R r) (access_goal (rep_access R r) h)"
  using V h succ rec by (rule represented_goal_outcome_in)

theorem represented_search_in:
  assumes F: "F r"
    and access: "\<And>s. F s \<Longrightarrow> access_formed \<kappa> P (rep_access R s) (rep_project R s)"
    and empty: "\<And>s. F s \<Longrightarrow> rep_empty R s \<longleftrightarrow> resolution_pending (rep_project R s) = {||}"
    and refresh: "\<And>s. F s \<Longrightarrow> F (rep_refresh R s) \<and> rep_project R (rep_refresh R s) = rep_project R s"
    and construct: "\<And>s m. F s \<Longrightarrow> m |\<in>| access_construction_nodes (rep_access R s) \<Longrightarrow>
      F (rep_construct R s m) \<and>
      rep_project R (rep_construct R s m) = finite_construction_step \<kappa> P (rep_project R s) (access_node (rep_access R s) m)"
    and successors: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      fimage (rep_project R) (rep_successors R s h) =
        finite_goal_successors_in \<Theta> P (rep_project R s) (access_goal (rep_access R s) h) \<and>
      (\<forall>s'. s' |\<in>| rep_successors R s h \<longrightarrow> F s')"
    and closes: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      E s h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access R s) h)"
    and rp: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> rp s h \<longleftrightarrow> pr (rep_project R s) (access_goal (rep_access R s) h)"
  shows "represented_search_in R E rp \<kappa> P n r =
      finite_resolution_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> P n (rep_project R r)"
  using F
proof (induction n arbitrary: r)
  case 0
  interpret access_formed \<kappa> P "rep_access R r" "rep_project R r" by (rule access[OF 0])
  show ?case using empty[OF 0] pending by simp
next
  case (Suc n)
  let ?r = "rep_refresh R r" let ?V = "rep_access R ?r"
  let ?rec = "finite_resolution_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> P n"
  have f: "F ?r" and p: "rep_project R ?r = rep_project R r" using refresh[OF Suc.prems] by simp_all
  interpret v: access_formed \<kappa> P ?V "rep_project R ?r" by (rule access[OF f])
  have rp': "\<And>h. h |\<in>| access_goals ?V \<Longrightarrow> rp ?r h \<longleftrightarrow> pr (rep_project R ?r) (access_goal ?V h)" by (rule rp[OF f])
  have sel1: "access_selection_value ?V (access_select_in (E ?r) (rp ?r) ?V) =
      finite_resolution_select_in \<Theta> pr \<kappa> P (rep_project R ?r)"
    using rp[OF f] closes[OF f] by (rule v.select_in(1))
  have rec: "\<And>s. F s \<Longrightarrow> represented_search_in R E rp \<kappa> P n s = ?rec (rep_project R s)" by (rule Suc.IH)
  show ?case
  proof (cases "resolution_pending (rep_project R r) = {||}")
    case True
    then show ?thesis using empty[OF Suc.prems] by simp
  next
    case False
    have ne: "\<not> rep_empty R r" using False empty[OF Suc.prems] by simp
    show ?thesis
    proof (cases "access_select_in (E ?r) (rp ?r) ?V")
      case (Access_Construction N)
      have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (rep_project R r) = Select_Construction (fimage (access_node ?V) N)"
        using sel1 Access_Construction p by simp
      have "fimage (\<lambda>m. represented_search_in R E rp \<kappa> P n (rep_construct R ?r m)) N =
          fimage ?rec (fimage (finite_construction_step \<kappa> P (rep_project R r)) (fimage (access_node ?V) N))"
        unfolding fset.map_comp comp_def
      proof (rule fset.map_cong0)
        fix m assume "m \<in> fset N"
        then have c: "m |\<in>| access_construction_nodes ?V" using access_select_in_construction[OF Access_Construction] by blast
        show "represented_search_in R E rp \<kappa> P n (rep_construct R ?r m) =
            ?rec (finite_construction_step \<kappa> P (rep_project R r) (access_node ?V m))"
          using rec construct[OF f c] p by simp
      qed
      then show ?thesis using ne False s Access_Construction by (simp add: Let_def)
    next
      case (Access_Goals G)
      have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (rep_project R r) = Select_Goals (fimage (access_goal ?V) G)"
        using sel1 Access_Goals p by simp
      have "fimage (represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) ?r ?V) G =
          fimage (finite_goal_outcome_in \<Theta> ?rec P (rep_project R r)) (fimage (access_goal ?V) G)"
        unfolding fset.map_comp comp_def
      proof (rule fset.map_cong0)
        fix h assume "h \<in> fset G"
        then have h: "h |\<in>| access_goals ?V" using access_select_in_goals[OF Access_Goals] by blast
        note sc = successors[OF f h]
        have "represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) ?r ?V h =
            finite_goal_outcome_in \<Theta> ?rec P (rep_project R ?r) (access_goal ?V h)"
          by (rule represented_goal_outcome_in[OF access[OF f] h conjunct1[OF sc]]) (use sc rec in blast)
        then show "represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) ?r ?V h =
            finite_goal_outcome_in \<Theta> ?rec P (rep_project R r) (access_goal ?V h)"
          using p by simp
      qed
      then show ?thesis using ne False s Access_Goals by (simp add: Let_def)
    next
      case Access_None
      have s: "finite_resolution_select_in \<Theta> pr \<kappa> P (rep_project R r) = Select_None"
        using sel1 Access_None p by simp
      then show ?thesis using ne False Access_None p v.pending by (simp add: Let_def)
    qed
  qed
qed

theorem represented_search:
  assumes F: "F r"
    and access: "\<And>s. F s \<Longrightarrow> access_formed \<kappa> P (rep_access R s) (rep_project R s)"
    and empty: "\<And>s. F s \<Longrightarrow> rep_empty R s \<longleftrightarrow> resolution_pending (rep_project R s) = {||}"
    and refresh: "\<And>s. F s \<Longrightarrow> F (rep_refresh R s) \<and> rep_project R (rep_refresh R s) = rep_project R s"
    and construct: "\<And>s m. F s \<Longrightarrow> m |\<in>| access_construction_nodes (rep_access R s) \<Longrightarrow>
      F (rep_construct R s m) \<and>
      rep_project R (rep_construct R s m) = finite_construction_step \<kappa> P (rep_project R s) (access_node (rep_access R s) m)"
    and successors: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      fimage (rep_project R) (rep_successors R s h) = finite_goal_successors P (rep_project R s) (access_goal (rep_access R s) h) \<and>
      (\<forall>s'. s' |\<in>| rep_successors R s h \<longrightarrow> F s')"
    and rp: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> rp s h \<longleftrightarrow> pr (rep_project R s) (access_goal (rep_access R s) h)"
  shows "represented_search R rp \<kappa> P n r =
      finite_resolution_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> P n (rep_project R r)"
proof -
  have closes: "\<And>s h. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow>
      False \<longleftrightarrow> finite_table_closes resolution_empty_table (access_goal (rep_access R s) h)" by simp
  have "represented_search_in R (\<lambda>s h. False) rp \<kappa> P n r =
      finite_resolution_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> P n (rep_project R r)"
    by (rule represented_search_in[where pr=pr, OF F access empty refresh construct successors closes rp])
  then show ?thesis by (simp only: represented_search_in_empty)
qed

text \<open>
  A search selecting through any function of its states searches as the representation's search wherever that
  function is the access's selection at the priority: the selection is the one step in which the two differ, and every
  state the search reaches keeps the invariant under which they agree.
\<close>

primrec selected_search :: "('r,'g,'n,'k,'a,'s::linorder,'d,'c) resolution_representation \<Rightarrow>
    ('r \<Rightarrow> ('n,'g) access_selection) \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 'r \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "selected_search R sel \<kappa> P 0 r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (fimage (access_goal (rep_access R r)) (access_goals (rep_access R r)))|})"
| "selected_search R sel \<kappa> P (Suc n) r = (if rep_empty R r then Resolution_Outcome {|rep_project R r|} {||}
    else let r' = rep_refresh R r; V = rep_access R r' in (case sel r' of
      Access_Construction N \<Rightarrow> finite_outcome_union (fimage (\<lambda>m. selected_search R sel \<kappa> P n (rep_construct R r' m)) N)
    | Access_Goals G \<Rightarrow> finite_outcome_union (fimage (represented_goal_outcome R (selected_search R sel \<kappa> P n) r' V) G)
    | Access_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (fimage (access_goal V) (access_goals V))) (finite_unconstructed \<kappa> P (rep_project R r')))))"

theorem selected_search_in:
  assumes F: "F r"
    and refresh: "\<And>s. F s \<Longrightarrow> F (rep_refresh R s)"
    and construct: "\<And>s m. F s \<Longrightarrow> m |\<in>| access_construction_nodes (rep_access R s) \<Longrightarrow> F (rep_construct R s m)"
    and successors: "\<And>s h s'. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> s' |\<in>| rep_successors R s h \<Longrightarrow> F s'"
    and sel: "\<And>s. F s \<Longrightarrow> sel s = access_select_in (E s) (rp s) (rep_access R s)"
  shows "selected_search R sel \<kappa> P n r = represented_search_in R E rp \<kappa> P n r"
  using F
proof (induction n arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?r = "rep_refresh R r" let ?V = "rep_access R ?r"
  have f: "F ?r" by (rule refresh[OF Suc.prems])
  have c: "fimage (\<lambda>m. selected_search R sel \<kappa> P n (rep_construct R ?r m)) N =
      fimage (\<lambda>m. represented_search_in R E rp \<kappa> P n (rep_construct R ?r m)) N"
    if "access_select_in (E ?r) (rp ?r) ?V = Access_Construction N" for N
  proof (rule fset.map_cong0)
    fix m assume "m \<in> fset N"
    then have "m |\<in>| access_construction_nodes ?V" using access_select_in_construction[OF that] by blast
    then show "selected_search R sel \<kappa> P n (rep_construct R ?r m) = represented_search_in R E rp \<kappa> P n (rep_construct R ?r m)"
      by (rule Suc.IH[OF construct[OF f]])
  qed
  have g: "fimage (represented_goal_outcome R (selected_search R sel \<kappa> P n) ?r ?V) G =
      fimage (represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) ?r ?V) G"
    if "access_select_in (E ?r) (rp ?r) ?V = Access_Goals G" for G
  proof (rule fset.map_cong0)
    fix h assume "h \<in> fset G"
    then have h: "h |\<in>| access_goals ?V" using access_select_in_goals[OF that] by blast
    have "fimage (selected_search R sel \<kappa> P n) (rep_successors R ?r h) =
        fimage (represented_search_in R E rp \<kappa> P n) (rep_successors R ?r h)"
      by (rule fset.map_cong0) (rule Suc.IH[OF successors[OF f h]], simp)
    then show "represented_goal_outcome R (selected_search R sel \<kappa> P n) ?r ?V h =
        represented_goal_outcome R (represented_search_in R E rp \<kappa> P n) ?r ?V h"
      by (simp add: represented_goal_outcome_def Let_def)
  qed
  show ?case
    unfolding selected_search.simps represented_search_in.simps Let_def sel[OF f]
    by (cases "access_select_in (E ?r) (rp ?r) ?V") (simp_all add: c g)
qed

theorem selected_search:
  assumes F: "F r"
    and refresh: "\<And>s. F s \<Longrightarrow> F (rep_refresh R s)"
    and construct: "\<And>s m. F s \<Longrightarrow> m |\<in>| access_construction_nodes (rep_access R s) \<Longrightarrow> F (rep_construct R s m)"
    and successors: "\<And>s h s'. F s \<Longrightarrow> h |\<in>| access_goals (rep_access R s) \<Longrightarrow> s' |\<in>| rep_successors R s h \<Longrightarrow> F s'"
    and sel: "\<And>s. F s \<Longrightarrow> sel s = access_select (rp s) (rep_access R s)"
  shows "selected_search R sel \<kappa> P n r = represented_search R rp \<kappa> P n r"
proof -
  have sel': "\<And>s. F s \<Longrightarrow> sel s = access_select_in (\<lambda>h. False) (rp s) (rep_access R s)"
    using sel by (simp add: access_select_in_empty)
  have "selected_search R sel \<kappa> P n r = represented_search_in R (\<lambda>s h. False) rp \<kappa> P n r"
    by (rule selected_search_in[OF F refresh construct successors sel'])
  then show ?thesis by (simp only: represented_search_in_empty)
qed

end
