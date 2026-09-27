theory Factor_Access_Commitments
  imports Factor_Shared_Commitments Factor_Framed_Commitment_Index Factor_Resolution_Modes
begin

section \<open>The commitment's tests and the moded priority, read through the access\<close>

text \<open>
  Task 867, fix (3) of task 830 (DECISIONS.md, task 495's entry, its addition "The resolver at the given's size";
  corrections (10), (12), (13), (14) and (15) of "Committed choice, for refusals"). The committed step hands the moded
  priority and the commitment's tests a state: F2c's step projects the representation's state for them wherever a goal
  passes the guard. Here the tests the route passes, those of the narrowed commitment
  (@{const finite_narrowed_commitment}) at framed declarations, and the moded priority
  (@{const finite_moded_priority}) are stated over an access (@{text Factor_Search_Representations}) and proved equal to
  their forms on the state at every formed access of it. What they read is the access's: the goals and their cached
  positions and variables, the nodes at a position, a goal and a node decoded one at a time where its pattern is read.
  What the access does not present and the tests read of every node or goal, cheaply, is given beside it
  (@{text commitment_access}, formed at the same state, @{text commitment_formed}): the positions holding a node, a
  node's site, clause and call variables, a call goal's site. Nothing here decodes the state.
\<close>

subsection \<open>What the tests read beside the access\<close>

record ('g,'n,'a,'s,'d) commitment_access =
  commitment_node_positions :: "'s list fset"
  commitment_node_site :: "'n \<Rightarrow> 'd"
  commitment_node_schema :: "'n \<Rightarrow> ('a,'s,'d) finite_factor_schema"
  commitment_call_variables :: "'n \<Rightarrow> ('s,'a) resolution_variable fset"
  commitment_goal_site :: "'g \<Rightarrow> 'd option"

locale commitment_formed = access_formed \<kappa> P V st
  for \<kappa> :: "('a,'s::linorder,'d,'c) finite_witness_construction" and P :: "('a,'s,'d,'c) finite_schema_system"
    and V :: "('g,'n,'k,'a,'s,'d,'c) search_access" and st :: "('a,'s,'d,'c) resolution_state" +
  fixes E :: "('g,'n,'a,'s,'d) commitment_access"
  assumes positions: "q |\<in>| commitment_node_positions E \<longleftrightarrow> access_nodes_at V q \<noteq> {||}"
    and node_site: "n |\<in>| access_nodes_at V q \<Longrightarrow> commitment_node_site E n = resolution_node_site (access_node V n)"
    and node_schema: "n |\<in>| access_nodes_at V q \<Longrightarrow> commitment_node_schema E n = resolution_node_schema (access_node V n)"
    and call_variables: "n |\<in>| access_nodes_at V q \<Longrightarrow>
      commitment_call_variables E n = finite_pattern_variables (resolution_node_call (access_node V n))"
    and goal_site: "h |\<in>| access_goals V \<Longrightarrow> commitment_goal_site E h = (case access_goal V h of
      Resolution_Call_Goal q r d p \<Rightarrow> Some d | Resolution_Material_Goal q r M \<Rightarrow> None)"

lemma commitment_fball_eq: "(\<And>x. x |\<in>| A \<Longrightarrow> R x \<longleftrightarrow> S x) \<Longrightarrow> fBall A R \<longleftrightarrow> fBall A S"
  by auto

lemma commitment_fbex_eq: "(\<And>x. x |\<in>| A \<Longrightarrow> R x \<longleftrightarrow> S x) \<Longrightarrow> fBex A R \<longleftrightarrow> fBex A S"
  by auto

lemma commitment_fball_cong: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B =simp=> R x \<longleftrightarrow> S x) \<Longrightarrow> fBall A R \<longleftrightarrow> fBall B S"
  by (auto simp: simp_implies_def)

lemma commitment_fbex_cong: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B =simp=> R x \<longleftrightarrow> S x) \<Longrightarrow> fBex A R \<longleftrightarrow> fBex B S"
  by (auto simp: simp_implies_def)

subsection \<open>The state's reads, through the access\<close>

definition access_pending :: "('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "access_pending V g \<longleftrightarrow> fBex (access_goals_at V (resolution_goal_position g)) (\<lambda>h. access_goal V h = g)"

context commitment_formed
begin

lemma commitment_self: "commitment_formed \<kappa> P V st E"
  using access_formed_axioms commitment_formed_axioms by (auto intro: commitment_formed.intro)

lemma commitment_focused: "commitment_formed \<kappa> P (access_focused F V) (finite_focused F st) E"
proof (rule commitment_formed.intro[OF focused], unfold_locales)
  show "q |\<in>| commitment_node_positions E \<longleftrightarrow> access_nodes_at (access_focused F V) q \<noteq> {||}" for q
    using positions by simp
  show "commitment_node_site E n = resolution_node_site (access_node (access_focused F V) n)"
    if "n |\<in>| access_nodes_at (access_focused F V) q" for n q using node_site that by simp
  show "commitment_node_schema E n = resolution_node_schema (access_node (access_focused F V) n)"
    if "n |\<in>| access_nodes_at (access_focused F V) q" for n q using node_schema that by simp
  show "commitment_call_variables E n = finite_pattern_variables (resolution_node_call (access_node (access_focused F V) n))"
    if "n |\<in>| access_nodes_at (access_focused F V) q" for n q using call_variables that by simp
  show "commitment_goal_site E h = (case access_goal (access_focused F V) h of
      Resolution_Call_Goal q r d p \<Rightarrow> Some d | Resolution_Material_Goal q r M \<Rightarrow> None)"
    if "h |\<in>| access_goals (access_focused F V)" for h
    using goal_site that by (simp add: access_focus_goals_def)
qed

lemma node_position: "n |\<in>| access_nodes_at V q \<Longrightarrow> resolution_node_position (access_node V n) = q"
  using node_at by blast

lemma focus_goal: "h |\<in>| access_focus_goals F V \<Longrightarrow> h |\<in>| access_goals V"
  by (simp add: access_focus_goals_def)

lemma goal_eq: "h |\<in>| access_goals V \<Longrightarrow> h' |\<in>| access_goals V \<Longrightarrow> h' = h \<longleftrightarrow> access_goal V h' = access_goal V h"
  using goal_inj by blast

lemma nodes_at_bex:
  "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<and> R nd) \<longleftrightarrow>
    fBex (access_nodes_at V q) (\<lambda>n. R (access_node V n))"
proof
  assume "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<and> R nd)"
  then obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = q" "R nd" by blast
  obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
    using nodes[of nd] nd(1) by blast
  show "fBex (access_nodes_at V q) (\<lambda>n. R (access_node V n))" using n nd by auto
next
  assume "fBex (access_nodes_at V q) (\<lambda>n. R (access_node V n))"
  then obtain n where n: "n |\<in>| access_nodes_at V q" "R (access_node V n)" by blast
  have at: "resolution_node_position (access_node V n) = q" using node_position[OF n(1)] .
  have "access_node V n |\<in>| resolution_nodes st" using nodes[of "access_node V n"] n(1) at by auto
  then show "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<and> R nd)" using n(2) at by auto
qed

lemma nodes_ball:
  "fBall (resolution_nodes st) R \<longleftrightarrow>
    fBall (commitment_node_positions E) (\<lambda>q. fBall (access_nodes_at V q) (\<lambda>n. R (access_node V n)))"
proof
  assume all: "fBall (resolution_nodes st) R"
  { fix q n assume n: "n |\<in>| access_nodes_at V q"
    then have "access_node V n |\<in>| resolution_nodes st" using nodes[of "access_node V n"] node_position[OF n] by auto
    then have "R (access_node V n)" using all by blast }
  then show "fBall (commitment_node_positions E) (\<lambda>q. fBall (access_nodes_at V q) (\<lambda>n. R (access_node V n)))" by blast
next
  assume all: "fBall (commitment_node_positions E) (\<lambda>q. fBall (access_nodes_at V q) (\<lambda>n. R (access_node V n)))"
  { fix nd assume nd: "nd |\<in>| resolution_nodes st"
    then obtain n where n: "n |\<in>| access_nodes_at V (resolution_node_position nd)" "access_node V n = nd"
      using nodes[of nd] by blast
    then have "resolution_node_position nd |\<in>| commitment_node_positions E" using positions by auto
    then have "R nd" using all n by blast }
  then show "fBall (resolution_nodes st) R" by blast
qed

lemma pending_ball: "fBall (resolution_pending st) R \<longleftrightarrow> fBall (access_goals V) (\<lambda>h. R (access_goal V h))"
  by (auto simp: pending)

lemma pending_bex: "fBex (resolution_pending st) R \<longleftrightarrow> fBex (access_goals V) (\<lambda>h. R (access_goal V h))"
  by (auto simp: pending)

lemma focus_ball: "fBall (finite_focus_pending F st) R \<longleftrightarrow> fBall (access_focus_goals F V) (\<lambda>h. R (access_goal V h))"
  by (auto simp flip: focus_goals)

lemma pending_access: "g |\<in>| resolution_pending st \<longleftrightarrow> access_pending V g"
proof
  assume "g |\<in>| resolution_pending st"
  then obtain h where h: "h |\<in>| access_goals V" "access_goal V h = g" using pending by auto
  then have "h |\<in>| access_goals_at V (resolution_goal_position g)" using goals_at goal_position[OF h(1)] by auto
  then show "access_pending V g" using h(2) by (auto simp: access_pending_def)
next
  assume "access_pending V g"
  then obtain h where "h |\<in>| access_goals_at V (resolution_goal_position g)" "access_goal V h = g"
    by (auto simp: access_pending_def)
  then show "g |\<in>| resolution_pending st" using goals_at pending by auto
qed

lemma under_ball: "fBall (resolution_pending_under st p) R \<longleftrightarrow>
    fBall (access_goals V) (\<lambda>h. take (length p) (access_goal_position V h) = p \<longrightarrow> R (access_goal V h))"
  by (auto simp: pending goal_position)

lemma under_empty: "resolution_pending_under st p = {||} \<longleftrightarrow>
    \<not> fBex (access_goals V) (\<lambda>h. take (length p) (access_goal_position V h) = p)"
proof -
  have "resolution_pending_under st p = {||} \<longleftrightarrow> fBall (resolution_pending_under st p) (\<lambda>g. False)"
    by (auto simp: fset_eq_iff)
  then show ?thesis unfolding under_ball by auto
qed

end

subsection \<open>The socket's tests\<close>

definition access_socket_holders where
  "access_socket_holders F V E q Y h \<longleftrightarrow>
    fBall (access_focus_goals F V) (\<lambda>h'. h' = h \<or> access_variables V h' |\<inter>| Y = {||} \<or>
      (access_goal_position V h' \<noteq> [] \<and> butlast (access_goal_position V h') = butlast q)) \<and>
    fBall (commitment_node_positions E) (\<lambda>q'. take (length q') (butlast q) = q' \<or>
      fBall (access_nodes_at V q') (\<lambda>n. commitment_call_variables E n |\<inter>| Y = {||}))"

definition access_free_premise_row where
  "access_free_premise_row V nd a \<longleftrightarrow>
    (a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd \<and>
    fBall (access_goals V) (\<lambda>h. ((resolution_node_position nd,True),a) |\<in>| access_variables V h \<longrightarrow>
      access_goal_position V h \<noteq> [] \<and> butlast (access_goal_position V h) = resolution_node_position nd)"

definition access_premise_only_framed where
  "access_premise_only_framed C V nd \<longleftrightarrow>
    fBall (finite_schema_variables (resolution_node_schema nd) |-|
        finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))) (\<lambda>a.
      access_free_premise_row V nd a \<or> (a |\<notin>| C \<and> finite_pattern_variables (finite_node_binding nd a) = {||}))"

definition access_children_framed where
  "access_children_framed C V nd s \<longleftrightarrow>
    fBall (finite_schema_premises (resolution_node_schema nd)) (\<lambda>(s',e,p).
      access_pending V (Resolution_Call_Goal (resolution_node_position nd@[s'])
        (Some (resolution_node_site nd,resolution_node_clause nd,s')) e (finite_pattern_substitute (finite_node_binding nd) p)) \<or>
      (s' \<noteq> s \<and> fBall (access_goals V) (\<lambda>h. take (length (resolution_node_position nd@[s'])) (access_goal_position V h) =
            resolution_node_position nd@[s'] \<longrightarrow>
          access_variables V h |\<inter>| finite_socket_binding_variables C nd s = {||}) \<and>
        finite_pattern_variables (finite_pattern_substitute (finite_node_binding nd) p) = {||} \<and>
        finite_pattern_variables p |\<inter>| C = {||})) \<and>
    fBall (finite_schema_materials (resolution_node_schema nd)) (\<lambda>(s',N).
      access_pending V (Resolution_Material_Goal (resolution_node_position nd@[s'])
        (resolution_node_site nd,resolution_node_clause nd,s') (finite_material_pattern_substitute (finite_node_binding nd) N)) \<or>
      (s' \<noteq> s \<and> \<not> fBex (access_goals V) (\<lambda>h. take (length (resolution_node_position nd@[s'])) (access_goal_position V h) =
          resolution_node_position nd@[s']) \<and>
        finite_material_variables (finite_material_pattern_substitute (finite_node_binding nd) N) = {||} \<and>
        finite_material_variables N |\<inter>| C = {||})) \<and>
    fBall (access_goals V) (\<lambda>h. access_goal_position V h \<noteq> [] \<longrightarrow>
      butlast (access_goal_position V h) = resolution_node_position nd \<longrightarrow>
      fBex (finite_schema_premises (resolution_node_schema nd)) (\<lambda>(s,e,p).
        access_goal V h = Resolution_Call_Goal (resolution_node_position nd@[s])
          (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute (finite_node_binding nd) p)) \<or>
      fBex (finite_schema_materials (resolution_node_schema nd)) (\<lambda>(s,N).
        access_goal V h = Resolution_Material_Goal (resolution_node_position nd@[s])
          (resolution_node_site nd,resolution_node_clause nd,s) (finite_material_pattern_substitute (finite_node_binding nd) N)))"

definition access_socket_kept_framed where
  "access_socket_kept_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow> q \<noteq> [] \<and>
    fBex (access_nodes_at V (butlast q)) (\<lambda>n.
      (commitment_node_site E n,commitment_node_schema E n,last q,True,Vp,Vh) |\<in>| declared_sockets D \<and>
      (case finite_frame_at \<Phi> Vp Vh (commitment_node_site E n) (commitment_node_schema E n) (last q) ch of None \<Rightarrow> False
        | Some C \<Rightarrow> access_premise_only_framed C V (access_node V n))) \<and>
    access_socket_holders F V E q Y h"

definition access_socket_free_framed where
  "access_socket_free_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow> q \<noteq> [] \<and> F = Some (butlast q) \<and>
    fBex (access_nodes_at V (butlast q)) (\<lambda>n.
      (commitment_node_site E n,commitment_node_schema E n,last q,False,Vp,Vh) |\<in>| declared_sockets D \<and>
      (case finite_frame_at \<Phi> Vp Vh (commitment_node_site E n) (commitment_node_schema E n) (last q) ch of None \<Rightarrow> False
        | Some C \<Rightarrow> access_premise_only_framed C V (access_node V n) \<and>
          finite_parent_absorbs Vp Vh C (access_node V n) (last q) \<and>
          access_socket_holders F V E q (Y |\<union>| finite_parent_absorbed Vp Vh C (access_node V n) (last q)) h))"

definition access_socket_declared_framed where
  "access_socket_declared_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow>
    access_socket_kept_framed D \<Phi> Vp Vh ch F V E q Y h \<or> access_socket_free_framed D \<Phi> Vp Vh ch F V E q Y h"

definition access_socket_commitment_framed where
  "access_socket_commitment_framed D \<Phi> Vp Vh ch F V E h = (case access_goal V h of
      Resolution_Call_Goal q r d p \<Rightarrow> (case resolution_view_pattern Vp p of
          Some (x,y) \<Rightarrow> finite_pattern_variables x = {||} \<and> finite_pattern_variables y \<noteq> {||} \<and>
            access_socket_declared_framed D \<Phi> Vp Vh ch F V E q (finite_pattern_variables y) h
        | None \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> finite_canonical_solutions M \<noteq> None \<and> finite_free_fields M \<and>
        access_socket_declared_framed D \<Phi> Vp Vh ch F V E q (finite_material_variables M) h)"

definition access_call_framed where
  "access_call_framed D \<Phi> Vp Vh ch F V E h \<longleftrightarrow> (case access_goal V h of
      Resolution_Call_Goal q r e p \<Rightarrow> (case resolution_view_pattern Vp p of
          Some (x,y) \<Rightarrow> fBex (access_nodes_at V (butlast q)) (\<lambda>n.
            (case finite_frame_at \<Phi> Vp Vh (commitment_node_site E n) (commitment_node_schema E n) (last q) ch of
                None \<Rightarrow> False
              | Some C \<Rightarrow> access_children_framed C V (access_node V n) (last q)) \<and>
            finite_premise_only_unshared (access_node V n) \<and>
            finite_socket_pair Vp q (commitment_node_schema E n) \<and>
            (access_socket_kept_framed D \<Phi> Vp Vh ch F V E q (finite_pattern_variables y) h \<or>
              finite_input_output_apart Vh (access_node V n)))
        | None \<Rightarrow> True)
    | Resolution_Material_Goal q r M \<Rightarrow> True)"

definition access_material_framed where
  "access_material_framed D \<Phi> Vp Vh ch F V E h \<longleftrightarrow> (case access_goal V h of
      Resolution_Material_Goal q r M \<Rightarrow> fBex (access_nodes_at V (butlast q)) (\<lambda>n.
        (case finite_frame_at \<Phi> Vp Vh (commitment_node_site E n) (commitment_node_schema E n) (last q) ch of
            None \<Rightarrow> False
          | Some C \<Rightarrow> access_children_framed C V (access_node V n) (last q)) \<and>
        finite_premise_only_unshared (access_node V n) \<and>
        (access_socket_kept_framed D \<Phi> Vp Vh ch F V E q (finite_material_variables M) h \<or>
          finite_input_output_apart Vh (access_node V n)))
    | Resolution_Call_Goal q r e p \<Rightarrow> True)"

definition access_goal_premise where
  "access_goal_premise V E h \<longleftrightarrow> access_goal_position V h = [] \<or>
    fBex (access_nodes_at V (butlast (access_goal_position V h))) (\<lambda>n.
      fBex (finite_schema_premises (commitment_node_schema E n)) (\<lambda>z. fst z = last (access_goal_position V h)))"

definition access_material_premise where
  "access_material_premise V E h \<longleftrightarrow> access_goal_position V h = [] \<or>
    fBex (access_nodes_at V (butlast (access_goal_position V h))) (\<lambda>n.
      fBex (finite_schema_materials (commitment_node_schema E n)) (\<lambda>z. fst z = last (access_goal_position V h)))"

definition access_producer_commits where
  "access_producer_commits D F V h d W hs = (case access_goal V h of
      Resolution_Call_Goal q r e p \<Rightarrow> e = d \<and>
        (case resolution_view_pattern W p of
            Some (x,y) \<Rightarrow> finite_pattern_variables x = {||} \<and> finite_pattern_variables y \<noteq> {||} \<and>
              fBall (access_focus_goals F V) (\<lambda>h'. h' = h \<or>
                access_variables V h' |\<inter>| finite_pattern_variables y = {||} \<or>
                finite_output_consumer D d (resolution_view_hole_patterns W hs p) (finite_pattern_variables y) (access_goal V h'))
          | None \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

text \<open>The direct test reads a producer's commitment only at a producer of the goal's own site.\<close>

definition access_direct_commitment where
  "access_direct_commitment D F V E h \<longleftrightarrow>
    fBex (declared_producers D) (\<lambda>(d,W,hs). commitment_goal_site E h = Some d \<and> access_producer_commits D F V h d W hs)"

context commitment_formed
begin

lemma socket_holders_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_holders F V E q Y h \<longleftrightarrow> finite_socket_holders F st q Y (access_goal V h)"
  unfolding access_socket_holders_def finite_socket_holders_def focus_ball nodes_ball
  by (intro conj_cong commitment_fball_eq refl)
    (auto simp: focus_goal goal_eq[OF h] variables goal_position node_position call_variables)

lemma free_premise_row_exact: "access_free_premise_row V nd a \<longleftrightarrow> finite_free_premise_row st nd a"
  unfolding access_free_premise_row_def finite_free_premise_row_def pending_ball
  by (intro conj_cong commitment_fball_eq refl) (simp_all add: variables goal_position)

lemma premise_only_framed_exact: "access_premise_only_framed C V nd \<longleftrightarrow> finite_premise_only_framed C st nd"
  by (simp add: access_premise_only_framed_def finite_premise_only_framed_def free_premise_row_exact)

lemma children_framed_exact: "access_children_framed C V nd s \<longleftrightarrow> finite_children_framed C st nd s"
  by (simp only: access_children_framed_def finite_children_framed_def pending_access under_ball under_empty pending_ball)
    (simp add: goal_position variables cong: commitment_fball_cong commitment_fbex_cong)

lemma socket_kept_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_kept_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow>
    finite_socket_kept_framed D \<Phi> Vp Vh ch F st q Y (access_goal V h)"
  unfolding access_socket_kept_framed_def finite_socket_kept_framed_def nodes_at_bex socket_holders_exact[OF h]
    premise_only_framed_exact
  by (simp add: node_site node_schema cong: commitment_fbex_cong)

lemma socket_free_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_free_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow>
    finite_socket_free_framed D \<Phi> Vp Vh ch F st q Y (access_goal V h)"
  unfolding access_socket_free_framed_def finite_socket_free_framed_def nodes_at_bex premise_only_framed_exact
    socket_holders_exact[OF h]
  by (simp add: node_site node_schema cong: commitment_fbex_cong)

lemma socket_declared_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_declared_framed D \<Phi> Vp Vh ch F V E q Y h \<longleftrightarrow>
    finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y (access_goal V h)"
  by (simp add: access_socket_declared_framed_def finite_socket_declared_framed_def
    socket_kept_framed_exact[OF h] socket_free_framed_exact[OF h])

lemma socket_commitment_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_commitment_framed D \<Phi> Vp Vh ch F V E h \<longleftrightarrow>
    finite_socket_commitment_framed D \<Phi> Vp Vh ch F st (access_goal V h)"
  unfolding access_socket_commitment_framed_def finite_socket_commitment_framed_def socket_declared_framed_exact[OF h]
  by (cases "access_goal V h") simp_all

lemma call_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_call_framed D \<Phi> Vp Vh ch F V E h \<longleftrightarrow> finite_call_framed D \<Phi> Vp Vh ch F st (access_goal V h)"
  unfolding access_call_framed_def finite_call_framed_def children_framed_exact socket_kept_framed_exact[OF h]
  by (cases "access_goal V h")
    (simp_all add: nodes_at_bex node_site node_schema cong: commitment_fbex_cong option.case_cong prod.case_cong)

lemma material_framed_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_material_framed D \<Phi> Vp Vh ch F V E h \<longleftrightarrow> finite_material_framed D \<Phi> Vp Vh ch F st (access_goal V h)"
  unfolding access_material_framed_def finite_material_framed_def children_framed_exact socket_kept_framed_exact[OF h]
  by (cases "access_goal V h")
    (simp_all add: nodes_at_bex node_site node_schema cong: commitment_fbex_cong option.case_cong prod.case_cong)

lemma goal_premise_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_goal_premise V E h \<longleftrightarrow> finite_goal_premise st (access_goal V h)"
  unfolding access_goal_premise_def finite_goal_premise_code nodes_at_bex goal_position[OF h]
  by (simp add: node_schema cong: commitment_fbex_cong)

lemma material_premise_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_material_premise V E h \<longleftrightarrow> finite_material_premise st (access_goal V h)"
  unfolding access_material_premise_def finite_material_premise_def nodes_at_bex goal_position[OF h]
  by (simp add: node_schema cong: commitment_fbex_cong)

lemma producer_commits_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_producer_commits D F V h d W hs \<longleftrightarrow> finite_producer_commits D F st (access_goal V h) d W hs"
  by (cases "access_goal V h")
    (simp_all add: access_producer_commits_def finite_producer_commits_def focus_ball focus_goal goal_eq[OF h] variables
      cong: commitment_fball_cong option.case_cong prod.case_cong)

lemma direct_commitment_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_direct_commitment D F V E h \<longleftrightarrow> finite_direct_commitment D F st (access_goal V h)"
proof -
  have site: "access_producer_commits D F V h d W hs \<Longrightarrow> commitment_goal_site E h = Some d" for d W hs
    using goal_site[OF h] by (auto simp: access_producer_commits_def split: resolution_goal.splits)
  have "commitment_goal_site E h = Some d \<and> access_producer_commits D F V h d W hs \<longleftrightarrow>
      finite_producer_commits D F st (access_goal V h) d W hs" for d W hs
    using site[of d W hs] producer_commits_exact[OF h, of D F d W hs] by blast
  then show ?thesis unfolding access_direct_commitment_def finite_direct_commitment_def by simp
qed

end

subsection \<open>The framed and the narrowed commitment over the access\<close>

record ('g,'n,'k,'a,'s,'d,'c) access_commitment =
  accessed_call :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('g,'n,'a,'s,'d) commitment_access \<Rightarrow>
    'g \<Rightarrow> bool"
  accessed_material :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow> ('g,'n,'a,'s,'d) commitment_access \<Rightarrow>
    'g \<Rightarrow> bool"
  accessed_production :: "'s list option \<Rightarrow> ('g,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow>
    ('g,'n,'a,'s,'d) commitment_access \<Rightarrow> 'g \<Rightarrow> (nat resolution_view \<times> finite_factor_term) option"

text \<open>
  The framed test reads the socket's views and frame choices at the goal's raising socket alone, through the index
  built once where the commitment is (@{thm [source] finite_framed_commitment_indexed}).
\<close>

definition access_framed_commitment ::
    "('a,'s::linorder,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow>
      ('g,'n,'k,'a,'s,'d,'c) access_commitment" where
  "access_framed_commitment D \<Phi> = (let T = framed_socket_index D \<Phi> in
    \<lparr>accessed_call = (\<lambda>F V E h. access_goal_premise V E h \<and> (access_direct_commitment D F V E h \<or>
       (access_is_call V h \<and> framed_socket_test T (\<lambda>Vp Vh ch. access_socket_commitment_framed D \<Phi> Vp Vh ch F V E h \<and>
          access_call_framed D \<Phi> Vp Vh ch F V E h) (access_goal_position V h)))),
     accessed_material = (\<lambda>F V E h. access_material_premise V E h \<and> \<not> access_is_call V h \<and>
       framed_socket_test T (\<lambda>Vp Vh ch. access_socket_commitment_framed D \<Phi> Vp Vh ch F V E h \<and>
         access_material_framed D \<Phi> Vp Vh ch F V E h) (access_goal_position V h)),
     accessed_production = (\<lambda>F V E h. None)\<rparr>)"

definition access_socket_productions where
  "access_socket_productions D \<Phi> F V E h = (case access_goal V h of
      Resolution_Call_Goal q r e p \<Rightarrow>
        (\<lambda>(e',S,s,keep,Vp,Vh). (Vp,the (declared_production D e' S s))) |`|
          ffilter (\<lambda>(e',S,s,keep,Vp,Vh). q \<noteq> [] \<and> s = last q \<and> declared_production D e' S s \<noteq> None \<and>
            fBex (access_nodes_at V (butlast q)) (\<lambda>n. commitment_node_site E n = e' \<and> commitment_node_schema E n = S) \<and>
            fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
              access_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F V E h \<and>
              access_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F V E h)) (declared_sockets D)
    | Resolution_Material_Goal q r M \<Rightarrow> {||})"

definition access_narrowed_production where
  "access_narrowed_production Pg n D \<Phi> Kc F V E h = (case access_goal V h of
      Resolution_Call_Goal q r e p \<Rightarrow>
        if accessed_call Kc F V E h then
          (case finite_singleton_option (access_socket_productions D \<Phi> F V E h) of None \<Rightarrow> None
          | Some VR \<Rightarrow> if finite_registration_applies (fst VR) (snd VR) e p then
              (case finite_registration_production Pg n (fst VR) (snd VR) p of None \<Rightarrow> None
              | Some v \<Rightarrow> if finite_production_substitution (fst VR) p v = None then None else Some (fst VR,v))
            else None)
        else None
    | Resolution_Material_Goal q r M \<Rightarrow> None)"

definition access_narrowed_commitment where
  "access_narrowed_commitment Pg n D \<Phi> = (let Kc = access_framed_commitment (resolution_declarations.truncate D) \<Phi> in
    Kc\<lparr>accessed_call := (\<lambda>F V E h. accessed_call Kc F V E h \<and>
       (access_socket_productions D \<Phi> F V E h = {||} \<or> access_narrowed_production Pg n D \<Phi> Kc F V E h \<noteq> None)),
     accessed_production := access_narrowed_production Pg n D \<Phi> Kc\<rparr>)"

context commitment_formed
begin

lemma framed_call_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "accessed_call (access_framed_commitment D \<Phi>) F V E h \<longleftrightarrow>
    commit_call (finite_framed_commitment D \<Phi>) F st (access_goal V h)"
  by (simp add: access_framed_commitment_def finite_framed_commitment_indexed Let_def goal_premise_exact[OF h]
    direct_commitment_exact[OF h] is_call[OF h] goal_position[OF h] socket_commitment_framed_exact[OF h]
    call_framed_exact[OF h])

lemma framed_material_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "accessed_material (access_framed_commitment D \<Phi>) F V E h \<longleftrightarrow>
    commit_material (finite_framed_commitment D \<Phi>) F st (access_goal V h)"
  by (simp add: access_framed_commitment_def finite_framed_commitment_indexed Let_def material_premise_exact[OF h]
    is_call[OF h] goal_position[OF h] socket_commitment_framed_exact[OF h] material_framed_exact[OF h])

lemma socket_productions_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_socket_productions D \<Phi> F V E h = finite_socket_productions D \<Phi> F st (access_goal V h)"
  unfolding access_socket_productions_def finite_socket_productions_def socket_commitment_framed_exact[OF h]
    call_framed_exact[OF h]
  by (cases "access_goal V h")
    (simp_all add: nodes_at_bex node_site node_schema cong: commitment_fbex_cong)

lemma narrowed_production_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_narrowed_production Pg n D \<Phi> (access_framed_commitment (resolution_declarations.truncate D) \<Phi>) F V E h =
    narrowed_production_under (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) Pg n D \<Phi> F st
      (access_goal V h)"
  by (cases "access_goal V h")
    (simp_all add: access_narrowed_production_def narrowed_production_under_def framed_call_exact[OF h]
      socket_productions_exact[OF h])

lemma narrowed_call_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "accessed_call (access_narrowed_commitment Pg n D \<Phi>) F V E h \<longleftrightarrow>
    commit_call (finite_narrowed_commitment Pg n D \<Phi>) F st (access_goal V h)"
  by (simp add: access_narrowed_commitment_def finite_narrowed_commitment_under Let_def framed_call_exact[OF h]
    socket_productions_exact[OF h] narrowed_production_exact[OF h])

lemma narrowed_material_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "accessed_material (access_narrowed_commitment Pg n D \<Phi>) F V E h \<longleftrightarrow>
    commit_material (finite_narrowed_commitment Pg n D \<Phi>) F st (access_goal V h)"
  by (simp add: access_narrowed_commitment_def finite_narrowed_commitment_under Let_def framed_material_exact[OF h])

lemma narrowed_production_field_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "accessed_production (access_narrowed_commitment Pg n D \<Phi>) F V E h =
    commit_production (finite_narrowed_commitment Pg n D \<Phi>) F st (access_goal V h)"
  by (simp add: access_narrowed_commitment_def finite_narrowed_commitment_under Let_def narrowed_production_exact[OF h])

end

text \<open>An access commitment is exact for a commitment when its three tests are the commitment's at every formed access.\<close>

definition access_commitment_exact where
  "access_commitment_exact Kc K \<longleftrightarrow> (\<forall>\<kappa> Pg V st E F h. commitment_formed \<kappa> Pg V st E \<longrightarrow> h |\<in>| access_goals V \<longrightarrow>
    (accessed_call Kc F V E h \<longleftrightarrow> commit_call K F st (access_goal V h)) \<and>
    (accessed_material Kc F V E h \<longleftrightarrow> commit_material K F st (access_goal V h)) \<and>
    accessed_production Kc F V E h = commit_production K F st (access_goal V h))"

lemma access_framed_production [simp]: "accessed_production (access_framed_commitment D \<Phi>) F V E h = None"
  by (simp add: access_framed_commitment_def Let_def)

theorem access_framed_commitment_exact:
  "access_commitment_exact (access_framed_commitment D \<Phi>) (finite_framed_commitment D \<Phi>)"
  unfolding access_commitment_exact_def
  by (intro allI impI conjI)
    (simp_all add: commitment_formed.framed_call_exact commitment_formed.framed_material_exact)

theorem access_narrowed_commitment_exact:
  "access_commitment_exact (access_narrowed_commitment Pg n D \<Phi>) (finite_narrowed_commitment Pg n D \<Phi>)"
  unfolding access_commitment_exact_def
  by (intro allI impI conjI)
    (simp_all add: commitment_formed.narrowed_call_exact commitment_formed.narrowed_material_exact
      commitment_formed.narrowed_production_field_exact)

subsection \<open>The moded priority over the access\<close>

definition access_commitment_priority where
  "access_commitment_priority Kc V E h = (let F = Some (butlast (access_goal_position V h)) in
    if access_is_call V h then accessed_call Kc None V E h \<or> accessed_call Kc F V E h
    else accessed_material Kc None V E h \<or> accessed_material Kc F V E h)"

text \<open>The priority's state-wide part: whether some goal passes the commitment's priority, computed once a step.\<close>

definition access_priority_pending where
  "access_priority_pending Kc V E \<longleftrightarrow> fBex (access_goals V) (access_commitment_priority Kc V E)"

definition access_declared_goal where
  "access_declared_goal D V E h \<longleftrightarrow> h |\<in>| access_goals V \<and> (case commitment_goal_site E h of None \<Rightarrow> False
    | Some d \<Rightarrow> fBex (declared_producers D) (\<lambda>(e,W,hs). e = d) \<or>
      (access_goal_position V h \<noteq> [] \<and> fBex (access_nodes_at V (butlast (access_goal_position V h))) (\<lambda>n.
        fBex (declared_sockets D) (\<lambda>(e,S,s,keep,Vp,Vh).
          e = commitment_node_site E n \<and> S = commitment_node_schema E n \<and> s = last (access_goal_position V h)))))"

definition access_waiting_variables where
  "access_waiting_variables D V E h = ffUnion (fimage (access_variables V)
    (ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V)))"

definition access_mode_binder where
  "access_mode_binder D M V E h \<longleftrightarrow> h |\<in>| access_goals V \<and>
    fBex M (\<lambda>(e,W). commitment_goal_site E h = Some e) \<and> (case access_goal V h of
      Resolution_Call_Goal q r d p \<Rightarrow> fBex M (\<lambda>(e,W). e = d \<and> (case resolution_view_pattern W p of
          Some (x,y) \<Rightarrow> finite_pattern_variables x = {||} \<and>
            finite_pattern_variables y |\<inter>| access_waiting_variables D V E h \<noteq> {||}
        | None \<Rightarrow> False))
    | Resolution_Material_Goal q r N \<Rightarrow> False)"

definition access_moded_priority_at where
  "access_moded_priority_at Kc D M V E c h \<longleftrightarrow> access_commitment_priority Kc V E h \<or> (access_mode_binder D M V E h \<and> \<not> c)"

definition access_moded_priority where
  "access_moded_priority Kc D M V E = access_moded_priority_at Kc D M V E (access_priority_pending Kc V E)"

context commitment_formed
begin

lemma commitment_priority_exact:
  assumes exact: "access_commitment_exact Kc K" and h: "h |\<in>| access_goals V"
  shows "access_commitment_priority Kc V E h \<longleftrightarrow> finite_commitment_priority K st (access_goal V h)"
proof -
  note ex = exact[unfolded access_commitment_exact_def, rule_format, OF commitment_self h]
  show ?thesis
    by (cases "access_goal V h")
      (simp_all add: access_commitment_priority_def finite_commitment_priority_def Let_def ex is_call[OF h]
        goal_position[OF h])
qed

lemma priority_pending_exact:
  assumes exact: "access_commitment_exact Kc K"
  shows "access_priority_pending Kc V E \<longleftrightarrow> fBex (resolution_pending st) (finite_commitment_priority K st)"
  unfolding access_priority_pending_def pending_bex
  by (rule commitment_fbex_eq) (rule commitment_priority_exact[OF exact])

lemma declared_goal_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_declared_goal D V E h \<longleftrightarrow> finite_declared_goal D st (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q r d p)
  have site: "commitment_goal_site E h = Some d" using goal_site[OF h] Resolution_Call_Goal by simp
  have pos: "access_goal_position V h = q" using goal_position[OF h] Resolution_Call_Goal by simp
  have mem: "access_goal V h |\<in>| resolution_pending st" using pending h by simp
  show ?thesis unfolding access_declared_goal_def finite_declared_goal_def
    using h site pos mem Resolution_Call_Goal
    by (simp add: nodes_at_bex node_site node_schema cong: commitment_fbex_cong)
next
  case (Resolution_Material_Goal q r M)
  then show ?thesis using goal_site[OF h] h by (simp add: access_declared_goal_def finite_declared_goal_def)
qed

lemma waiting_variables_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_waiting_variables D V E h = finite_waiting_variables D st (access_goal V h)"
proof -
  have "fimage (access_variables V) (ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V)) =
      fimage resolution_goal_variables
        (ffilter (\<lambda>g. g \<noteq> access_goal V h \<and> finite_declared_goal D st g) (resolution_pending st))"
  proof (rule fset_eqI, rule iffI)
    fix Y assume "Y |\<in>| fimage (access_variables V) (ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V))"
    then obtain h' where h': "h' |\<in>| access_goals V" "h' \<noteq> h" "access_declared_goal D V E h'"
      "Y = access_variables V h'" by auto
    have mem: "access_goal V h' |\<in>| resolution_pending st" by (rule goal_in_pending[OF h'(1)])
    have ne: "access_goal V h' \<noteq> access_goal V h" using goal_eq[OF h h'(1)] h'(2) by simp
    have dg: "finite_declared_goal D st (access_goal V h')" using declared_goal_exact[OF h'(1)] h'(3) by simp
    have "access_goal V h' |\<in>| ffilter (\<lambda>g. g \<noteq> access_goal V h \<and> finite_declared_goal D st g) (resolution_pending st)"
      unfolding ffilter.rep_eq Set.filter_eq mem_Collect_eq using mem ne dg by blast
    then have "resolution_goal_variables (access_goal V h') |\<in>| fimage resolution_goal_variables
        (ffilter (\<lambda>g. g \<noteq> access_goal V h \<and> finite_declared_goal D st g) (resolution_pending st))"
      by (rule fimageI)
    then show "Y |\<in>| fimage resolution_goal_variables
        (ffilter (\<lambda>g. g \<noteq> access_goal V h \<and> finite_declared_goal D st g) (resolution_pending st))"
      unfolding h'(4) variables[OF h'(1)] .
  next
    fix Y assume "Y |\<in>| fimage resolution_goal_variables
        (ffilter (\<lambda>g. g \<noteq> access_goal V h \<and> finite_declared_goal D st g) (resolution_pending st))"
    then obtain g where g: "g |\<in>| resolution_pending st" "g \<noteq> access_goal V h" "finite_declared_goal D st g"
      "Y = resolution_goal_variables g" by auto
    have "g |\<in>| fimage (access_goal V) (access_goals V)" using g(1) pending by simp
    then obtain h' where h': "h' |\<in>| access_goals V" "g = access_goal V h'" by blast
    have ne: "h' \<noteq> h" using g(2) h'(2) by blast
    have dg: "access_declared_goal D V E h'" using declared_goal_exact[OF h'(1)] g(3) h'(2) by simp
    have "h' |\<in>| ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V)"
      unfolding ffilter.rep_eq Set.filter_eq mem_Collect_eq using h'(1) ne dg by blast
    then have "access_variables V h' |\<in>|
        fimage (access_variables V) (ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V))"
      by (rule fimageI)
    then show "Y |\<in>| fimage (access_variables V) (ffilter (\<lambda>h'. h' \<noteq> h \<and> access_declared_goal D V E h') (access_goals V))"
      unfolding g(4) h'(2) variables[OF h'(1), symmetric] .
  qed
  then show ?thesis by (simp add: access_waiting_variables_def finite_waiting_variables_def)
qed

lemma mode_binder_exact:
  assumes h: "h |\<in>| access_goals V"
  shows "access_mode_binder D M V E h \<longleftrightarrow> finite_mode_binder D M st (access_goal V h)"
proof (cases "access_goal V h")
  case (Resolution_Call_Goal q r d p)
  have site: "commitment_goal_site E h = Some d" using goal_site[OF h] Resolution_Call_Goal by simp
  have mem: "access_goal V h |\<in>| resolution_pending st" by (rule goal_in_pending[OF h])
  show ?thesis unfolding access_mode_binder_def finite_mode_binder_def waiting_variables_exact[OF h]
    using h site mem Resolution_Call_Goal by auto
next
  case (Resolution_Material_Goal q r M)
  then show ?thesis using h by (simp add: access_mode_binder_def finite_mode_binder_def)
qed

theorem moded_priority_exact:
  assumes exact: "access_commitment_exact Kc K" and h: "h |\<in>| access_goals V"
  shows "access_moded_priority Kc D M V E h \<longleftrightarrow> finite_moded_priority K D M st (access_goal V h)"
  by (simp add: access_moded_priority_def access_moded_priority_at_def finite_moded_priority_def
    commitment_priority_exact[OF exact h] mode_binder_exact[OF h] priority_pending_exact[OF exact])

end

subsection \<open>What the shared state presents beside its access\<close>

text \<open>
  The shared state keeps a node's site and clause as they are, its call as a shared pattern whose variables are read
  without projecting it, and a goal's site in its constructor; the positions holding a node are the keys of its node
  tree. Formed at the state the shared access presents (@{thm [source] shared_access_formed}).
\<close>

definition shared_commitment_access :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,'a,'s,'d) commitment_access" where
  "shared_commitment_access r = \<lparr>commitment_node_positions = fset_of_list (RBT.keys (shared_nodes (search_state r))),
     commitment_node_site = (\<lambda>hn. shared_derivation_site (shared_entry_node hn)),
     commitment_node_schema = (\<lambda>hn. shared_derivation_schema (shared_entry_node hn)),
     commitment_call_variables = (\<lambda>hn. shared_pattern_variables (shared_derivation_call (shared_entry_node hn))),
     commitment_goal_site = (\<lambda>h. case shared_entry_goal h of Shared_Call_Goal q rr d p \<Rightarrow> Some d
       | Shared_Material_Goal q rr M \<Rightarrow> None)\<rparr>"

theorem shared_commitment_formed:
  assumes r: "search_formed \<kappa> P r"
  shows "commitment_formed \<kappa> P (shared_access \<kappa> P r) (search_project r) (shared_commitment_access r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF r] .
  have nf: "\<And>q hn. RBT.lookup (shared_nodes (search_state r)) q = Some hn \<Longrightarrow> node_entry_formed (search_table r) q hn"
    using s by (simp add: shared_state_formed_def)
  have at: "n |\<in>| access_nodes_at (shared_access \<kappa> P r) q \<Longrightarrow> RBT.lookup (shared_nodes (search_state r)) q = Some n" for n q
    by (cases "RBT.lookup (shared_nodes (search_state r)) q") (simp_all add: shared_access_simps)
  show ?thesis
    apply (rule commitment_formed.intro[OF shared_access_formed[OF r]])
    apply unfold_locales
    subgoal for q
      by (cases "RBT.lookup (shared_nodes (search_state r)) q")
        (simp_all add: shared_commitment_access_def shared_access_simps fset_of_list.rep_eq
          RBT.lookup_keys[symmetric] domIff)
    subgoal for n q by (simp add: shared_commitment_access_def shared_access_simps shared_derivation_project_def)
    subgoal for n q by (simp add: shared_commitment_access_def shared_access_simps shared_derivation_project_def)
    subgoal for n q
    proof -
      assume "n |\<in>| access_nodes_at (shared_access \<kappa> P r) q"
      then have "RBT.lookup (shared_nodes (search_state r)) q = Some n" by (rule at)
      then have "shared_pattern_formed (search_table r) (shared_derivation_call (shared_entry_node n))"
        using nf by (auto simp: node_entry_formed_def shared_derivation_formed_def)
      then show ?thesis
        by (simp add: shared_commitment_access_def shared_access_simps shared_derivation_project_def
          shared_pattern_variables_project)
    qed
    subgoal for h
      by (cases "shared_entry_goal h") (simp_all add: shared_commitment_access_def shared_access_simps)
    done
qed

text \<open>
  The route's instance: at a formed shared search and every focus, the narrowed commitment's moded priority read
  through the focused access and the shared state's commitment access is R5's at the focused projection.
\<close>

corollary shared_narrowed_moded_priority:
  assumes r: "search_formed \<kappa> P r" and h: "h |\<in>| access_focus_goals F (shared_access \<kappa> P r)"
  shows "access_moded_priority (access_narrowed_commitment Pg n D \<Phi>) Dm M (access_focused F (shared_access \<kappa> P r))
      (shared_commitment_access r) h \<longleftrightarrow>
    finite_moded_priority (finite_narrowed_commitment Pg n D \<Phi>) Dm M (finite_focused F (search_project r))
      (access_goal (shared_access \<kappa> P r) h)"
proof -
  interpret f: commitment_formed \<kappa> P "access_focused F (shared_access \<kappa> P r)" "finite_focused F (search_project r)"
    "shared_commitment_access r"
    by (rule commitment_formed.commitment_focused[OF shared_commitment_formed[OF r]])
  have h': "h |\<in>| access_goals (access_focused F (shared_access \<kappa> P r))" using h by simp
  show ?thesis
    using f.moded_priority_exact[OF access_narrowed_commitment_exact h', where D=Dm and M=M] by simp
qed

end
