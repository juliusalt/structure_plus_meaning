theory Factor_Resolution_Material_Discharge
  imports Factor_Resolution_Producer_Discharge
begin

section \<open>The material single solution's discharge of the exchange premise\<close>

text \<open>
  #565's exchange premise (\<open>finite_commitment_exchanges\<close>) asks, at a committed material premise, that some
  canonical successor be supported at the all-barred set. At that set every node is barred, so support is the truth of
  the successor's focused goals and their placement. The truth comes from the material socket's obligation
  (\<open>socket_discharged\<close>): the parent clause's instance under the support is true, the canonical answer satisfies the
  socket's material premise at the same source, so a true instance agrees with that answer on the material variables,
  keeps the socket's inputs (\<open>socket_inputs_kept\<close>), and re-grounds the pending siblings, which alone hold the free
  premise-only variables and the socket's variables.

  The test checks, where it commits at a socket, the three state conditions of correction (7) (DECISIONS.md, task 495's
  entry), the first in correction (9)'s form: each premise of the parent pending as its instance or closed
  (\<open>finite_children_closed\<close>), no premise-only
  variable of the parent stands in its call (\<open>finite_premise_only_unshared\<close>), and at a socket declared without the
  kept head the parent call's input and output, read at the head's view, share no variable
  (\<open>finite_input_output_apart\<close>); they are joined in \<open>finite_material_narrowed\<close> and \<open>finite_call_narrowed\<close>, each
  a counterexample to the premise where it fails. The discharge reads them through the parent node's context
  (\<open>finite_parent_context\<close>), stated once over correction (9)'s weaker conditions (\<open>finite_children_closed\<close>,
  \<open>finite_premise_only_inputs\<close>): a sibling resolved before the socket is closed, its instance ground and true
  (\<open>finite_closed_premise_true\<close>) and its variables among the inputs the obligation keeps. At a socket commitment of the
  test the context holds (\<open>finite_declared_socket_context\<close>); the discharge is stated at the socket's declared views,
  the parent's head read at the head's view, and at any discharged declarations. The same discharge is stated at the
  framed test of correction (10) (\<open>finite_framed_material_commitment_exchanges\<close>), today's its instance at no frames.
\<close>

subsection \<open>Values read as evaluations\<close>

lemma finite_material_ground_value:
  "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) N) \<longleftrightarrow>
    finite_material_observation (resolution_value \<theta> (finite_material_source N)) (resolution_value \<theta> (finite_material_atoms N))
      (resolution_value \<theta> (finite_material_edges N)) (resolution_value \<theta> (finite_material_counts N))
      (resolution_value \<theta> (finite_material_functions N))"
  by (simp add: finite_material_ground_satisfied_def resolution_value_exact[symmetric])

subsection \<open>A variant output is a renaming of the head output\<close>


lemma finite_variant_substitute_variable:
  assumes "finite_variant p (finite_pattern_substitute \<beta> p)" "b |\<in>| finite_pattern_variables p"
  obtains w where "\<beta> b = Finite_Variable w"
proof -
  obtain l where l: "finite_variant_pairs p (finite_pattern_substitute \<beta> p) = Some l"
    using assms(1) unfolding finite_variant_def by (auto split: option.splits)
  show thesis using finite_variant_pairs_substitute[OF l] assms(2) that by blast
qed

lemma list_all_pairs_consistent:
  assumes all: "list_all (\<lambda>(a,v). list_all (\<lambda>(b,w). (a = b) = (v = w)) l) l"
    and ax: "(a,x) \<in> set l" and cy: "(c,y) \<in> set l"
  shows "(a = c) = (x = y)"
proof -
  from all have A: "\<forall>(a',v')\<in>set l. \<forall>(b',w')\<in>set l. (a' = b') = (v' = w')"
    by (simp only: list_all_iff)
  have B: "\<forall>(b',w')\<in>set l. (a = b') = (x = w')" using bspec[OF A ax] by (simp only: prod.case)
  show ?thesis using bspec[OF B cy] by (simp only: prod.case)
qed

lemma finite_variant_substitute_injective:
  assumes v: "finite_variant p (finite_pattern_substitute \<beta> p)"
    and b: "b |\<in>| finite_pattern_variables p" and b': "b' |\<in>| finite_pattern_variables p" and eq: "\<beta> b = \<beta> b'"
  shows "b = b'"
proof -
  obtain l where l: "finite_variant_pairs p (finite_pattern_substitute \<beta> p) = Some l"
    using v unfolding finite_variant_def by (auto split: option.splits)
  have all: "list_all (\<lambda>(a,v). list_all (\<lambda>(b,w). (a = b) = (v = w)) l) l"
    using v unfolding finite_variant_def l by (simp only: option.case)
  have fv: "\<forall>b. b |\<in>| finite_pattern_variables p \<longrightarrow> (\<exists>w. \<beta> b = Finite_Variable w \<and> (b,w) \<in> set l)"
    using finite_variant_pairs_substitute[OF l] by (rule conjunct1)
  obtain w where w: "\<beta> b = Finite_Variable w \<and> (b,w) \<in> set l" using fv b by blast
  obtain w' where w': "\<beta> b' = Finite_Variable w' \<and> (b',w') \<in> set l" using fv b' by blast
  have "w = w'" using w w' eq by simp
  then show ?thesis using list_all_pairs_consistent[OF all conjunct2[OF w] conjunct2[OF w']] by simp
qed

subsection \<open>The canonical successor at the all-barred set\<close>

text \<open>
  A valuation under which the material goal takes the canonical tuple and every other focused goal holds supports one
  canonical successor, every node barred: the canonical binding is a candidate, the instance pairs it gives unify, and the
  most general unifier keeps the valuation, so each goal left pending holds as the goal it substitutes did.
\<close>

lemma finite_canonical_successor_supported:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
    and Ws: "finite_canonical_solutions M = Some Ws"
    and ground: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and canonical: "(resolution_value \<theta> (finite_material_source M),resolution_value \<theta> (finite_material_atoms M),
        resolution_value \<theta> (finite_material_edges M),resolution_value \<theta> (finite_material_counts M),
        resolution_value \<theta> (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C)"
    and placed: "finite_state_placed U st"
    and holds: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> h \<noteq> Resolution_Material_Goal q r M \<Longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
  shows "\<exists>st'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
    resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>"
proof -
  let ?\<sigma> = "resolution_substitution \<theta>"
  let ?g = "Resolution_Material_Goal q r M"
  have "resolution_goal_formed ?g"
    using I goal unfolding resolution_invariant_def resolution_goals_placed_def by blast
  then have Mf: "finite_material_formed M" by simp
  have Ws_eq: "Ws = finite_material_candidates M [finite_material_tuple C (finite_artifact_rows C)]"
    using Ws source by (simp add: finite_canonical_solutions_def split: if_splits)
  from ground obtain s a e b f where
      fs: "finite_pattern_substitute ?\<sigma> (finite_material_source M) = finite_exact_term_pattern s"
      and fa: "finite_pattern_substitute ?\<sigma> (finite_material_atoms M) = finite_exact_term_pattern a"
      and fe: "finite_pattern_substitute ?\<sigma> (finite_material_edges M) = finite_exact_term_pattern e"
      and fb: "finite_pattern_substitute ?\<sigma> (finite_material_counts M) = finite_exact_term_pattern b"
      and ff: "finite_pattern_substitute ?\<sigma> (finite_material_functions M) = finite_exact_term_pattern f"
      and obs: "finite_material_observation s a e b f"
    by (auto simp: finite_material_ground_satisfied_def)
  have tuple: "(s,a,e,b,f) = finite_material_tuple C (finite_artifact_rows C)"
  proof -
    have "resolution_value \<theta> (finite_material_source M) = s" "resolution_value \<theta> (finite_material_atoms M) = a"
      "resolution_value \<theta> (finite_material_edges M) = e" "resolution_value \<theta> (finite_material_counts M) = b"
      "resolution_value \<theta> (finite_material_functions M) = f"
      using fs fa fe fb ff by (simp_all add: resolution_value_eq)
    then show ?thesis using canonical by simp
  qed
  have formed_terms: "finite_term_formed s" "finite_term_formed a" "finite_term_formed e" "finite_term_formed b"
      "finite_term_formed f"
    using material_observation_formed obs finite_material_observation_correct finite_term_formed_correct by metis+
  have field_formed: "\<And>p y z. finite_pattern_substitute ?\<sigma> p = finite_exact_term_pattern y \<Longrightarrow> finite_term_formed y \<Longrightarrow>
      z |\<in>| finite_pattern_variables p \<Longrightarrow> finite_term_formed (\<theta> z)"
    using finite_pattern_substitute_formed_variable by (metis finite_exact_pattern_formed)
  have \<theta>f: "\<And>z. z |\<in>| finite_material_variables M \<Longrightarrow> finite_term_formed (\<theta> z)"
    using field_formed[OF fs formed_terms(1)] field_formed[OF fa formed_terms(2)] field_formed[OF fe formed_terms(3)]
      field_formed[OF fb formed_terms(4)] field_formed[OF ff formed_terms(5)]
    by (auto simp: finite_material_variables_def)
  define V where "V = finite_ground_bindings \<theta> (finite_material_variables M)"
  have Vf: "finite_term_bindings_formed (finite_material_variables M) V"
    unfolding V_def by (rule finite_ground_bindings_formed) (rule \<theta>f)
  have Mparts: "finite_pattern_formed (finite_material_source M)" "finite_pattern_formed (finite_material_atoms M)"
      "finite_pattern_formed (finite_material_edges M)" "finite_pattern_formed (finite_material_counts M)"
      "finite_pattern_formed (finite_material_functions M)"
    using Mf unfolding finite_material_formed_def by simp_all
  have inst: "\<And>p y. finite_pattern_formed p \<Longrightarrow> finite_pattern_variables p |\<subseteq>| finite_material_variables M \<Longrightarrow>
      finite_pattern_substitute ?\<sigma> p = finite_exact_term_pattern y \<Longrightarrow> finite_pattern_instance V p y"
    unfolding V_def by (rule resolution_ground_instance)
  have i_s: "finite_pattern_instance V (finite_material_source M) s"
    and ia: "finite_pattern_instance V (finite_material_atoms M) a"
    and ie: "finite_pattern_instance V (finite_material_edges M) e"
    and ib: "finite_pattern_instance V (finite_material_counts M) b"
    and iF: "finite_pattern_instance V (finite_material_functions M) f"
    using inst[OF Mparts(1) _ fs] inst[OF Mparts(2) _ fa] inst[OF Mparts(3) _ fe] inst[OF Mparts(4) _ fb]
      inst[OF Mparts(5) _ ff]
    by (auto simp: finite_material_variables_def)
  have sat: "finite_material_satisfied V M"
    unfolding finite_material_satisfied_def
    by (rule fBexI[where x=s], rule fBexI[where x=a], rule fBexI[where x=e], rule fBexI[where x=b],
      rule fBexI[where x=f], simp_all add: i_s ia ie ib iF obs finite_pattern_instances_member)
  have Vfil: "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V = V"
    unfolding V_def by (rule fset_eqI) auto
  have W_in: "V |\<in>| Ws"
  proof -
    have "(s,a,e,b,f) \<in> set [finite_material_tuple C (finite_artifact_rows C)]" using tuple by simp
    from finite_material_candidates_complete[OF Vf sat this i_s ia ie ib iF] show ?thesis
      using Vfil Ws_eq by simp
  qed
  define E :: "('s,'a) resolution_variable finite_pattern_pairs"
    where "E = [(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)]"
  have E_in: "E |\<in>| finite_material_instance_pairs V M"
    unfolding E_def by (rule finite_material_instance_pairs_intro[OF i_s ia ie ib iF])
  have unifies: "finite_unifies ?\<sigma> E"
    using fs fa fe fb ff by (simp add: E_def finite_pattern_substitute_ground)
  obtain u where u: "finite_unify_pairs E = Some u"
    using unifies finite_unify_pairs_none_iff[of E] by (cases "finite_unify_pairs E") auto
  have mgu: "\<And>y. finite_pattern_substitute ?\<sigma> (finite_binding_substitution u y) = ?\<sigma> y"
    by (rule finite_unify_pairs_most_general[OF u unifies])
  have keep: "\<And>y. resolution_value \<theta> (finite_pattern_substitute (finite_binding_substitution u) y) = resolution_value \<theta> y"
    by (rule resolution_value_unifier) (rule mgu)
  have keep_var: "(\<lambda>z. resolution_value \<theta> (finite_binding_substitution u z)) = \<theta>"
  proof
    fix z
    show "resolution_value \<theta> (finite_binding_substitution u z) = \<theta> z"
      using keep[of "Finite_Variable z"] by (simp add: resolution_value_def)
  qed
  have gp: "\<And>z. z |\<in>| resolution_goal_variables ?g \<Longrightarrow> resolution_placed st z \<or> U z"
    using placed goal unfolding finite_state_placed_def by blast
  have E_vars: "\<And>z. z \<in> finite_pairs_variables E \<Longrightarrow> resolution_placed st z \<or> U z"
    using gp by (auto simp: E_def finite_material_variables_def)
  have unified_var: "\<And>y z. z |\<in>| finite_pattern_variables (finite_binding_substitution u y) \<Longrightarrow>
      z = y \<or> resolution_placed st z \<or> U z"
    using finite_unifier_variable[OF u] E_vars by blast
  define st' where "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|?g|}) (resolution_nodes st) (resolution_witnesses st))"
  have member: "st' |\<in>| finite_solution_successors st q r M Ws"
    unfolding st'_def finite_solution_successors_def using W_in E_in u by (force simp: resolution_fset_simps)
  have placed': "\<And>z. resolution_placed st' z \<longleftrightarrow> resolution_placed st z"
    unfolding st'_def resolution_placed_substitute by (simp add: resolution_placed_def)
  have st'_nodes: "\<And>nd. nd |\<in>| resolution_nodes st' \<Longrightarrow>
      \<exists>m. m |\<in>| resolution_nodes st \<and> nd = resolution_node_substitute (finite_binding_substitution u) m"
    unfolding st'_def by (rule resolution_state_substitute_members(1))
  have st'_goals: "\<And>h. h |\<in>| resolution_pending st' \<Longrightarrow>
      \<exists>g0. g0 |\<in>| resolution_pending st \<and> g0 \<noteq> ?g \<and> h = resolution_goal_substitute (finite_binding_substitution u) g0"
  proof -
    fix h assume "h |\<in>| resolution_pending st'"
    then obtain g0 where "g0 |\<in>| resolution_pending st |-| {|?g|}"
      "h = resolution_goal_substitute (finite_binding_substitution u) g0"
      unfolding st'_def using resolution_state_substitute_members(2) by blast
    then show "\<exists>g0. g0 |\<in>| resolution_pending st \<and> g0 \<noteq> ?g \<and> h = resolution_goal_substitute (finite_binding_substitution u) g0"
      by auto
  qed
  have hold': "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    if h: "h |\<in>| resolution_pending st'" "resolution_focused F (resolution_goal_position h)" for h
  proof -
    obtain g0 where g0: "g0 |\<in>| resolution_pending st" "g0 \<noteq> ?g"
      and hg: "h = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF h(1)] by blast
    have "g0 |\<in>| finite_focus_pending F st" using g0(1) h(2) hg by (simp add: finite_focus_pending_focused)
    then have "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> g0" using holds g0(2) by blast
    then show ?thesis unfolding hg finite_goal_holds_substitute keep_var .
  qed
  have placed_st': "finite_state_placed U st'"
    unfolding finite_state_placed_def
  proof (intro conjI allI impI)
    fix h z assume h: "h |\<in>| resolution_pending st'" and z: "z |\<in>| resolution_goal_variables h"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and hg: "h = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF h] by blast
    obtain y where y: "y |\<in>| resolution_goal_variables g0" and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using resolution_goal_substitute_variable_origin z hg by blast
    have "resolution_placed st y \<or> U y" using placed g0 y unfolding finite_state_placed_def by blast
    then show "resolution_placed st' z \<or> U z" using unified_var[OF zy] placed' by blast
  next
    fix nd z assume nd: "nd |\<in>| resolution_nodes st'" and z: "z |\<in>| finite_pattern_variables (resolution_node_call nd)"
    obtain m where m: "m |\<in>| resolution_nodes st"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    obtain y where y: "y |\<in>| finite_pattern_variables (resolution_node_call m)"
      and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using finite_substitute_variable_origin z ndm by force
    have "resolution_placed st y \<or> U y" using placed m y unfolding finite_state_placed_def by blast
    then show "resolution_placed st' z \<or> U z" using unified_var[OF zy] placed' by blast
  qed
  have sup': "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes st')) P st' \<theta>"
    by (rule resolution_supported_at_barred_allI[OF hold' placed_st'])
  have sub: "fimage resolution_node_position (resolution_nodes st') |\<subseteq>| finite_committed_barring B st"
  proof
    fix x assume "x |\<in>| fimage resolution_node_position (resolution_nodes st')"
    then obtain nd where nd: "nd |\<in>| resolution_nodes st'" and x: "x = resolution_node_position nd" by auto
    obtain m where m: "m |\<in>| resolution_nodes st"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    have "x = resolution_node_position m" using x ndm by (cases m) simp
    then show "x |\<in>| finite_committed_barring B st" using m by (auto simp: finite_committed_barring_def)
  qed
  show ?thesis using member resolution_supported_at_barred_mono[OF sup' sub] by blast
qed

subsection \<open>Facts the discharge reads\<close>


lemma resolution_value_target: "resolution_value \<theta> (Finite_Pattern_Target x) = Finite_Target x"
  by (simp add: resolution_value_def)

lemma finite_pattern_substitute_variable_eq:
  "finite_pattern_substitute \<sigma> p = Finite_Variable w \<Longrightarrow> \<exists>x. p = Finite_Variable x \<and> \<sigma> x = Finite_Variable w"
  by (cases p) auto


lemma finite_free_fields_variables:
  assumes free: "finite_free_fields M"
  obtains w1 w2 w3 w4 where "finite_material_atoms M = Finite_Variable w1" "finite_material_edges M = Finite_Variable w2"
    "finite_material_counts M = Finite_Variable w3" "finite_material_functions M = Finite_Variable w4"
    "distinct [w1,w2,w3,w4]"
proof -
  obtain w1 where w1: "finite_material_atoms M = Finite_Variable w1"
    using free by (cases "finite_material_atoms M") auto
  obtain w2 where w2: "finite_material_edges M = Finite_Variable w2"
    using free w1 by (cases "finite_material_edges M") auto
  obtain w3 where w3: "finite_material_counts M = Finite_Variable w3"
    using free w1 w2 by (cases "finite_material_counts M") auto
  obtain w4 where w4: "finite_material_functions M = Finite_Variable w4"
    using free w1 w2 w3 by (cases "finite_material_functions M") auto
  have "distinct [w1,w2,w3,w4]" using free w1 w2 w3 w4 by simp
  then show thesis using that w1 w2 w3 w4 by blast
qed

lemma finite_material_source_formed:
  assumes "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
  shows "finite_exact_formed C"
proof -
  have obs: "finite_material_observation (Finite_Target (Finite_Whole C)) (resolution_value \<theta> (finite_material_atoms M))
      (resolution_value \<theta> (finite_material_edges M)) (resolution_value \<theta> (finite_material_counts M))
      (resolution_value \<theta> (finite_material_functions M))"
    using assms(1) unfolding finite_material_ground_value assms(2) resolution_value_target .
  from obs obtain A E B F where "finite_artifact_enumeration C A E B F"
    unfolding finite_material_observation_whole by blast
  then show ?thesis unfolding finite_artifact_enumeration_def by blast
qed

text \<open>The canonical tuple of a formed artifact is an observation of it: its rows are one of its enumerations.\<close>

lemma finite_canonical_observation:
  assumes formed: "finite_exact_formed C" and rows: "finite_artifact_rows C = (A,E,B,F)"
  shows "finite_material_observation (Finite_Target (Finite_Whole C))
    (finite_enumeration_term (map (finite_atom_term C) A)) (finite_enumeration_term (map (finite_incidence_term C) E))
    (finite_enumeration_term (map (finite_attachment_term C) B)) (finite_enumeration_term (map (finite_attachment_term C) F))"
proof -
  have en: "finite_artifact_enumeration C A E B F"
    using finite_artifact_enumerations_exact[OF formed, of A E B F] finite_artifact_rows_enumerated[of C] rows by simp
  have r: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    "finite_enumeration_read (finite_incidence_read C) (finite_enumeration_term (map (finite_incidence_term C) E)) = Some E"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) B)) = Some B"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) F)) = Some F"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)+
  show ?thesis unfolding finite_material_observation_whole using en r by blast
qed

subsection \<open>A closed sibling's instance is true\<close>

text \<open>
  A material premise done at a ground instance (\<open>resolution_material_done\<close>) is satisfied at that instance under every
  valuation: its fields' instances under the ground bindings are the residuals of their substitutions.
\<close>

lemma finite_material_done_ground_satisfied:
  assumes finished: "resolution_material_done \<beta> N"
  shows "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
    (finite_material_pattern_substitute \<beta> N))"
proof -
  let ?V = "finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) (finite_material_variables N)"
  have gr: "\<And>a. a |\<in>| finite_material_variables N \<Longrightarrow> finite_pattern_variables (\<beta> a) = {||}"
    and sat: "finite_material_satisfied ?V N" using finished by (simp_all add: resolution_material_done_def)
  have inst: "finite_pattern_instance ?V p y \<Longrightarrow> y = finite_residual_term (finite_pattern_substitute \<beta> p)" for p y
  proof (induction p arbitrary: y)
    case (Finite_Variable a)
    then show ?case by simp
  next
    case (Finite_Pattern_Target x)
    then show ?case by simp
  next
    case (Finite_Pattern_Payload v)
    then show ?case by simp
  next
    case (Finite_Pattern_Pair p1 p2)
    obtain y1 y2 where y: "y = Finite_Pair y1 y2" "finite_pattern_instance ?V p1 y1" "finite_pattern_instance ?V p2 y2"
      using Finite_Pattern_Pair.prems by (cases y) simp_all
    show ?case using Finite_Pattern_Pair.IH(1)[OF y(2)] Finite_Pattern_Pair.IH(2)[OF y(3)] y(1) by simp
  qed
  have val: "resolution_value \<theta> (finite_pattern_substitute \<beta> F) = finite_residual_term (finite_pattern_substitute \<beta> F)"
    if sub: "finite_pattern_variables F |\<subseteq>| finite_material_variables N" for F
  proof -
    have nz: "z |\<notin>| finite_pattern_variables (finite_pattern_substitute \<beta> F)" for z
    proof
      assume "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<beta> F)"
      from finite_substitute_variable_origin[OF this] obtain y where y: "y |\<in>| finite_pattern_variables F"
        "z |\<in>| finite_pattern_variables (\<beta> y)" by (elim exE conjE)
      have "y |\<in>| finite_material_variables N" using sub y(1) by (rule fsubsetD)
      then show False using gr y(2) by simp
    qed
    have "finite_pattern_variables (finite_pattern_substitute \<beta> F) = {||}" by (rule fset_eqI) (simp add: nz)
    then show ?thesis by (simp add: resolution_value_def finite_pattern_substitute_ground)
  qed
  from sat obtain s a e b f where
      i_s: "finite_pattern_instance ?V (finite_material_source N) s"
      and ia: "finite_pattern_instance ?V (finite_material_atoms N) a"
      and ie: "finite_pattern_instance ?V (finite_material_edges N) e"
      and ib: "finite_pattern_instance ?V (finite_material_counts N) b"
      and iF: "finite_pattern_instance ?V (finite_material_functions N) f"
      and obs: "finite_material_observation s a e b f"
    by (auto simp: finite_material_satisfied_def finite_pattern_instances_member)
  have sc: "finite_pattern_variables (finite_material_source N) |\<subseteq>| finite_material_variables N"
    "finite_pattern_variables (finite_material_atoms N) |\<subseteq>| finite_material_variables N"
    "finite_pattern_variables (finite_material_edges N) |\<subseteq>| finite_material_variables N"
    "finite_pattern_variables (finite_material_counts N) |\<subseteq>| finite_material_variables N"
    "finite_pattern_variables (finite_material_functions N) |\<subseteq>| finite_material_variables N"
    by (auto simp: finite_material_variables_def)
  show ?thesis unfolding finite_material_ground_value
    using obs inst[OF i_s] inst[OF ia] inst[OF ie] inst[OF ib] inst[OF iF] val[OF sc(1)] val[OF sc(2)] val[OF sc(3)]
      val[OF sc(4)] val[OF sc(5)]
    by (simp add: finite_material_pattern_substitute_fields)
qed

text \<open>
  A premise of a node with nothing pending at or under its position, whose instance under the node's bindings is ground,
  holds: a call premise by the solved-node acceptance of the node at its position (the linkage places one there, since no
  goal stands there), a material premise by the linkage, which marks it done.
\<close>

lemma finite_closed_premise_true:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st" and nd: "nd |\<in>| resolution_nodes st"
    and closed: "resolution_pending_under st (resolution_node_position nd @ [s]) = {||}"
  shows "\<And>e p. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd) \<Longrightarrow>
      finite_pattern_variables (finite_pattern_substitute (finite_node_binding nd) p) = {||} \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute (finite_node_binding nd) p)))
        \<in> positive_meaning (decode_finite_system P)"
    and "\<And>N. (s,N) |\<in>| finite_schema_materials (resolution_node_schema nd) \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute (finite_node_binding nd) N))"
proof -
  let ?S = "resolution_node_schema nd"
  let ?pos = "resolution_node_position nd"
  let ?\<beta> = "finite_node_binding nd"
  let ?SV = "finite_schema_variables ?S"
  have linked: "resolution_node_linked P st nd"
    using I nd unfolding resolution_invariant_def resolution_nodes_placed_def by blast
  obtain \<beta>0 where bind: "resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta>0 a)) ?SV"
    and prems: "\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow>
        Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
            (finite_pattern_substitute \<beta>0 p) |\<in>| resolution_pending st \<or>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=?pos@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta>0 p) \<or>
        resolution_premise_reused st (?pos@[s]) e (finite_pattern_substitute \<beta>0 p)"
    and mats: "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
        Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
            (finite_material_pattern_substitute \<beta>0 M) |\<in>| resolution_pending st \<or>
        resolution_material_done \<beta>0 M"
    using linked unfolding resolution_node_linked_def by blast
  have sv: "single_valued (fset (resolution_node_bindings nd))" unfolding bind by (auto simp: single_valued_def)
  have \<beta>0: "?\<beta> a = \<beta>0 a" if "a |\<in>| ?SV" for a
    by (rule finite_node_binding_row[OF sv]) (use that in \<open>auto simp: bind\<close>)
  have not_pending: "h |\<notin>| resolution_pending st" if "resolution_goal_position h = ?pos@[s]" for h
  proof
    assume "h |\<in>| resolution_pending st"
    then have "h |\<in>| resolution_pending_under st (?pos@[s])" using that by simp
    then have "h |\<in>| {||}" by (simp only: closed)
    then show False by simp
  qed
  show "(e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute ?\<beta> p))) \<in> positive_meaning (decode_finite_system P)"
    if p: "(s,e,p) |\<in>| finite_schema_premises ?S" and ground: "finite_pattern_variables (finite_pattern_substitute ?\<beta> p) = {||}"
    for e p
  proof -
    have pv: "a |\<in>| ?SV" if "a |\<in>| finite_pattern_variables p" for a
      using p that by (force simp: finite_schema_variables_def resolution_fset_simps)
    have eqp: "finite_pattern_substitute \<beta>0 p = finite_pattern_substitute ?\<beta> p"
      by (rule finite_pattern_substitute_cong) (simp add: \<beta>0 pv)
    have Ip: "resolution_pattern_invariant P d (finite_exact_term_pattern t) st"
      using I by (simp add: resolution_invariant_pattern)
    obtain m where m: "m |\<in>| resolution_nodes st" "finite_solved_node st m" "resolution_node_site m = e"
      "resolution_node_call m = finite_pattern_substitute ?\<beta> p"
    proof -
      from prems p consider
          (goal) "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
            (finite_pattern_substitute \<beta>0 p) |\<in>| resolution_pending st"
        | (node) m where "m |\<in>| resolution_nodes st" "resolution_node_position m=?pos@[s]" "resolution_node_site m=e"
            "resolution_node_call m=finite_pattern_substitute \<beta>0 p"
        | (reused) "resolution_premise_reused st (?pos@[s]) e (finite_pattern_substitute \<beta>0 p)"
        by blast
      then show thesis
      proof cases
        case goal
        then show thesis using not_pending[of "Resolution_Call_Goal (?pos@[s])
          (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute \<beta>0 p)"] by simp
      next
        case node
        have sol: "finite_solved_node st m" unfolding finite_solved_node_under node(2) by (rule closed)
        show thesis by (rule that[OF node(1) sol node(3)]) (simp add: node(4) eqp)
      next
        case reused
        then obtain m where "m |\<in>| resolution_nodes st" "finite_solved_node st m" "resolution_node_site m=e"
          "resolution_node_call m=finite_pattern_substitute \<beta>0 p" unfolding resolution_premise_reused_def by blast
        then show thesis using that eqp by simp
      qed
    qed
    have ans: "(e,decode_finite_term (finite_residual_term (finite_pattern_substitute ?\<beta> p))) \<in> positive_meaning (decode_finite_system P)"
      using resolution_solved_node_true[OF Ip m(1,2)] unfolding m(3,4) .
    then show ?thesis using ground by (simp add: resolution_value_def finite_pattern_substitute_ground)
  qed
  show "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
      (finite_material_pattern_substitute ?\<beta> N))"
    if N: "(s,N) |\<in>| finite_schema_materials ?S" for N
  proof -
    have nv: "a |\<in>| ?SV" if "a |\<in>| finite_material_variables N" for a
      using N that by (force simp: finite_schema_variables_def resolution_fset_simps)
    have done0: "resolution_material_done \<beta>0 N" using mats N not_pending by fastforce
    have gb: "finite_ground_bindings (\<lambda>a. finite_residual_term (?\<beta> a)) (finite_material_variables N) =
        finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta>0 a)) (finite_material_variables N)"
      using \<beta>0 nv by (auto simp: fset_eq_iff)
    have "resolution_material_done ?\<beta> N" using done0 gb \<beta>0 nv by (simp add: resolution_material_done_def)
    then show ?thesis by (rule finite_material_done_ground_satisfied)
  qed
qed

subsection \<open>The parent node's context\<close>

text \<open>
  What a socket's exchange reads of its parent node, stated once for the material socket and the call sockets: the node
  stands and is linked to its clause; each premise and material premise is pending as its instance under the node's
  bindings or, at another key, closed with a ground instance whose variables are among the socket's inputs, and every
  pending goal under the node is one of the instances (\<open>finite_children_closed\<close>); each premise-only variable is free
  or among the inputs with a ground binding (\<open>finite_premise_only_inputs\<close>); none stands in the node's call
  (\<open>finite_premise_only_unshared\<close>). The committed goal is the pending instance at the socket's key.
\<close>

definition finite_parent_context ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat resolution_view \<Rightarrow> nat resolution_view \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> bool" where
  "finite_parent_context P Vp Vh st nd s \<longleftrightarrow> nd |\<in>| resolution_nodes st \<and> resolution_node_linked P st nd \<and>
    finite_children_closed Vp Vh st nd s \<and> finite_premise_only_inputs Vp Vh st nd s \<and> finite_premise_only_unshared nd"

text \<open>
  At a socket commitment of the test the parent context holds, at the socket's views and key. This is the one lemma
  that reads the test's conditions on the parent node; a change of those conditions proves it again. The exchanges
  read the declaration and the holders from the test themselves.
\<close>

lemma finite_declared_socket_context:
  assumes I: "resolution_invariant P d t st"
    and sc: "finite_socket_commitment D Vp Vh F st g"
    and cn: "finite_call_narrowed D Vp Vh F st g" and mn: "finite_material_narrowed D Vp Vh F st g"
  obtains nd where "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
    "resolution_goal_position g \<noteq> []" "finite_parent_context P Vp Vh st nd (last (resolution_goal_position g))"
proof -
  let ?q = "resolution_goal_position g"
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have declared: "?q \<noteq> [] \<and> (\<exists>nd'. nd' |\<in>| resolution_nodes st \<and> resolution_node_position nd' = butlast ?q \<and>
      finite_premise_only_inputs Vp Vh st nd' (last ?q))"
    if "finite_socket_declared D Vp Vh F st ?q Y g" for Y
    using that unfolding finite_socket_declared_def finite_socket_kept_def finite_socket_free_def by blast
  have narrowed: "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = butlast ?q \<and>
      finite_children_closed Vp Vh st nd (last ?q) \<and> finite_premise_only_unshared nd"
  proof (cases g)
    case (Resolution_Call_Goal q r e p)
    obtain x y where v: "resolution_view_pattern Vp p = Some (x,y)"
      using sc Resolution_Call_Goal by (auto simp: finite_socket_commitment_def split: option.splits)
    show ?thesis using cn Resolution_Call_Goal v unfolding finite_call_narrowed_def by auto
  next
    case (Resolution_Material_Goal q r M)
    show ?thesis using mn Resolution_Material_Goal unfolding finite_material_narrowed_def by auto
  qed
  have decl: "\<exists>Y. finite_socket_declared D Vp Vh F st ?q Y g"
  proof (cases g)
    case (Resolution_Call_Goal q r e p)
    then show ?thesis using sc by (auto simp: finite_socket_commitment_def split: option.splits)
  next
    case (Resolution_Material_Goal q r M)
    then show ?thesis using sc by (auto simp: finite_socket_commitment_def)
  qed
  obtain Y where dY: "finite_socket_declared D Vp Vh F st ?q Y g" using decl by blast
  obtain nd' where qne: "?q \<noteq> []" and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast ?q"
    and poi: "finite_premise_only_inputs Vp Vh st nd' (last ?q)"
    using declared[OF dY] by blast
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast ?q"
    and closed: "finite_children_closed Vp Vh st nd (last ?q)" and unsh: "finite_premise_only_unshared nd"
    using narrowed by blast
  have "nd' = nd" using dist nd'(1) nd(1) nd'(2) nd(2) unfolding resolution_positions_distinct_def by auto
  then have "finite_parent_context P Vp Vh st nd (last ?q)"
    using nd(1) I closed unsh poi
    unfolding finite_parent_context_def resolution_invariant_def resolution_nodes_placed_def by blast
  then show thesis using that nd qne by blast
qed

subsection \<open>The parent context at a frame\<close>

text \<open>
  Correction (10) of DECISIONS.md, task 495's entry (build B2a): the parent context read at a frame C in place of the
  socket's inputs (@{text finite_framed_parent_context}): each premise pending as its instance or closed with a ground
  instance whose variables are outside C (@{const finite_children_framed}), each premise-only variable free or outside C
  with a ground binding (@{const finite_premise_only_framed}), none held by the parent's call. Today's context is its
  instance at the socket's default frame (@{text finite_parent_context_framed}); at a socket commitment of the framed
  test it holds at the frame the test chose (@{text finite_framed_socket_context}). The parent's linked bindings, the
  head read at its view and the free premise-only variables are read by the material discharge and the socket discharges
  alike; their lemmas stood in @{text Factor_Resolution_Socket_Discharges} and are moved here, statements unchanged.
\<close>

lemma resolution_value_agree:
  "resolution_value \<theta> p = resolution_value \<theta>' p \<Longrightarrow> z |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> z = \<theta>' z"
  by (induction p) (auto simp: resolution_value_def)

lemma head_kept_input:
  assumes "head_kept keep Vh S h h'" "resolution_view_pattern Vh (finite_schema_conclusion S) = Some (ci,co)"
  shows "evaluate_pattern h' (decode_finite_pattern ci) = evaluate_pattern h (decode_finite_pattern ci)"
  using assms by (simp add: head_kept_def)

lemma head_kept_variables:
  assumes kept: "head_kept True Vh S h h'" and formed: "view_formed Vh"
    and a: "a |\<in>| finite_pattern_variables (finite_schema_conclusion S)"
  shows "h' a = h a"
proof (cases "resolution_view_pattern Vh (finite_schema_conclusion S)")
  case None
  have "a \<in> head_inputs Vh S" using None a by (simp add: head_inputs_def finite_pattern_variables_correct[symmetric])
  then show ?thesis by (rule head_kept_head_inputs[OF kept])
next
  case (Some v)
  obtain ci co where vv: "v = (ci,co)" by (cases v)
  have vc: "resolution_view_pattern Vh (finite_schema_conclusion S) = Some (ci,co)" using Some vv by simp
  have "a |\<in>| finite_pattern_variables ci |\<union>| finite_pattern_variables co"
    using a resolution_view_pattern_variables[OF formed vc] by simp
  then consider "a |\<in>| finite_pattern_variables ci" | "a |\<in>| finite_pattern_variables co" by auto
  then show ?thesis
  proof cases
    case 1
    then have "a \<in> head_inputs Vh S" using vc by (simp add: head_inputs_def finite_pattern_variables_correct[symmetric])
    then show ?thesis by (rule head_kept_head_inputs[OF kept])
  next
    case 2
    have "evaluate_pattern h' (decode_finite_pattern co) = evaluate_pattern h (decode_finite_pattern co)"
      using kept vc by (simp add: head_kept_def)
    then show ?thesis by (rule evaluate_pattern_agree) (simp add: 2 finite_pattern_variables_correct[symmetric])
  qed
qed

lemma finite_node_binding_linked:
  assumes I: "resolution_invariant P d t st" and np: "np |\<in>| resolution_nodes st"
  shows "resolution_node_bindings np =
      fimage (\<lambda>a. (a,finite_node_binding np a)) (finite_schema_variables (resolution_node_schema np))"
    and "resolution_node_call np =
      finite_pattern_substitute (finite_node_binding np) (finite_schema_conclusion (resolution_node_schema np))"
proof -
  have "resolution_node_linked P st np" using I np unfolding resolution_invariant_def resolution_nodes_placed_def by blast
  then obtain \<beta> where bind: "resolution_node_bindings np = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema np))"
    and call: "resolution_node_call np = finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema np))"
    unfolding resolution_node_linked_def by blast
  have sv: "single_valued (fset (resolution_node_bindings np))" unfolding bind single_valued_def by (auto simp: fimage.rep_eq)
  have agree: "finite_node_binding np a = \<beta> a" if "a |\<in>| finite_schema_variables (resolution_node_schema np)" for a
    by (rule finite_node_binding_row[OF sv]) (use that in \<open>auto simp: bind\<close>)
  show "resolution_node_bindings np =
      fimage (\<lambda>a. (a,finite_node_binding np a)) (finite_schema_variables (resolution_node_schema np))"
    unfolding bind by (rule fimage_cong[OF refl]) (simp add: agree)
  show "resolution_node_call np =
      finite_pattern_substitute (finite_node_binding np) (finite_schema_conclusion (resolution_node_schema np))"
    unfolding call by (rule finite_pattern_substitute_cong) (metis agree finite_schema_variables_members(1))
qed

definition finite_free_premise_only where
  "finite_free_premise_only st np a \<longleftrightarrow>
    finite_node_binding np a = Finite_Variable ((resolution_node_position np,True),a) \<and>
    (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> ((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h \<longrightarrow>
      resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np)"

definition finite_free_premise_variable where
  "finite_free_premise_variable st np z \<longleftrightarrow> fst z = (resolution_node_position np,True) \<and>
    snd z |\<in>| finite_schema_variables (resolution_node_schema np) \<and>
    snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np)) \<and>
    finite_free_premise_only st np (snd z)"

definition finite_framed_parent_context ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'a fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> bool" where
  "finite_framed_parent_context P C st nd s \<longleftrightarrow> nd |\<in>| resolution_nodes st \<and> resolution_node_linked P st nd \<and>
    finite_children_framed C st nd s \<and> finite_premise_only_framed C st nd \<and> finite_premise_only_unshared nd"

lemma finite_parent_context_framed:
  assumes "finite_parent_context P Vp Vh st nd s"
  shows "finite_framed_parent_context P (finite_default_frame Vp Vh (resolution_node_schema nd) s) st nd s"
  using assms finite_children_closed_framed[of Vp Vh st nd s] finite_premise_only_inputs_framed[of Vp Vh st nd s]
  unfolding finite_parent_context_def finite_framed_parent_context_def by blast

text \<open>
  Every node's call is its clause's head under its bindings at every state the invariant holds of
  (@{const finite_nodes_headed}, where B1 states the framed test's containment of today's), and a linked node's clause
  is formed.
\<close>

lemma finite_invariant_headed:
  assumes I: "resolution_invariant P d t st"
  shows "finite_nodes_headed st"
  unfolding finite_nodes_headed_def using finite_node_binding_linked(2)[OF I] by blast

lemma finite_linked_schema_formed:
  assumes I: "resolution_invariant P d t st" and linked: "resolution_node_linked P st nd"
  shows "schema_formed (decode_finite_schema (resolution_node_schema nd))"
proof -
  have cl: "((resolution_node_site nd,resolution_node_clause nd),resolution_node_schema nd) |\<in>| finite_system_clauses P"
    using linked unfolding resolution_node_linked_def by blast
  have "finite_system_formed P" using I by (simp add: resolution_invariant_def)
  then have "finite_schema_formed (resolution_node_schema nd)" using cl unfolding finite_system_formed_def by auto
  then show ?thesis by (simp add: finite_schema_formed_correct)
qed

lemma finite_children_framed_children:
  assumes closed: "finite_children_framed C st np k"
    and h: "h |\<in>| resolution_pending st" "resolution_goal_position h \<noteq> []"
      "butlast (resolution_goal_position h) = resolution_node_position np"
  shows "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
      h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute (finite_node_binding np) p0)) \<or>
    (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
      h = Resolution_Material_Goal (resolution_node_position np @ [s]) r'
        (finite_material_pattern_substitute (finite_node_binding np) N0))"
proof -
  let ?S = "resolution_node_schema np"
  let ?pos = "resolution_node_position np"
  let ?\<beta> = "finite_node_binding np"
  have "fBex (finite_schema_premises ?S) (\<lambda>(s,e,p). h = Resolution_Call_Goal (?pos@[s])
        (Some (resolution_node_site np,resolution_node_clause np,s)) e (finite_pattern_substitute ?\<beta> p)) \<or>
      fBex (finite_schema_materials ?S) (\<lambda>(s,N). h = Resolution_Material_Goal (?pos@[s])
        (resolution_node_site np,resolution_node_clause np,s) (finite_material_pattern_substitute ?\<beta> N))"
    using closed h unfolding finite_children_framed_def by blast
  then show ?thesis
  proof
    assume "fBex (finite_schema_premises ?S) (\<lambda>(s,e,p). h = Resolution_Call_Goal (?pos@[s])
        (Some (resolution_node_site np,resolution_node_clause np,s)) e (finite_pattern_substitute ?\<beta> p))"
    then obtain z where z: "z |\<in>| finite_schema_premises ?S" "case z of (s,e,p) \<Rightarrow> h = Resolution_Call_Goal (?pos@[s])
        (Some (resolution_node_site np,resolution_node_clause np,s)) e (finite_pattern_substitute ?\<beta> p)" by blast
    obtain s e p where zs: "z = (s,e,p)" by (cases z)
    show ?thesis using z unfolding zs by auto
  next
    assume "fBex (finite_schema_materials ?S) (\<lambda>(s,N). h = Resolution_Material_Goal (?pos@[s])
        (resolution_node_site np,resolution_node_clause np,s) (finite_material_pattern_substitute ?\<beta> N))"
    then obtain z where z: "z |\<in>| finite_schema_materials ?S" "case z of (s,N) \<Rightarrow> h = Resolution_Material_Goal (?pos@[s])
        (resolution_node_site np,resolution_node_clause np,s) (finite_material_pattern_substitute ?\<beta> N)" by blast
    obtain s N where zs: "z = (s,N)" by (cases z)
    show ?thesis using z unfolding zs by auto
  qed
qed

lemma finite_framed_premise_only:
  assumes I: "resolution_invariant P d t st" and ctx: "finite_framed_parent_context P C st nd k"
    and a: "a |\<in>| finite_schema_variables (resolution_node_schema nd)"
      "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
  shows "finite_free_premise_only st nd a \<or> (a |\<notin>| C \<and> finite_pattern_variables (finite_node_binding nd a) = {||})"
proof -
  have nd: "nd |\<in>| resolution_nodes st" and pof: "finite_premise_only_framed C st nd"
    using ctx by (simp_all add: finite_framed_parent_context_def)
  have sv: "single_valued (fset (resolution_node_bindings nd))"
    unfolding finite_node_binding_linked(1)[OF I nd] by (auto simp: single_valued_def)
  have "a |\<in>| finite_schema_variables (resolution_node_schema nd) |-|
      finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))" using a by simp
  from fbspec[OF pof[unfolded finite_premise_only_framed_def] this]
  show ?thesis unfolding finite_free_premise_only_def using finite_node_binding_row[OF sv] by blast
qed

text \<open>
  At a socket commitment of the framed test the parent context holds at the frame the test chose, at the socket's views
  and key: the one lemma reading the framed test's conditions on the parent node, as
  @{text finite_declared_socket_context} reads today's.
\<close>

lemma finite_framed_socket_context:
  assumes I: "resolution_invariant P d t st"
    and sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
    and cn: "finite_call_framed D \<Phi> Vp Vh ch F st g" and mn: "finite_material_framed D \<Phi> Vp Vh ch F st g"
  obtains nd C where "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
    "resolution_goal_position g \<noteq> []"
    "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last (resolution_goal_position g)) ch =
      Some C"
    "finite_framed_parent_context P C st nd (last (resolution_goal_position g))"
proof -
  let ?q = "resolution_goal_position g"
  let ?fa = "\<lambda>nd. finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last ?q) ch"
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have declared: "?q \<noteq> [] \<and> (\<exists>nd' C'. nd' |\<in>| resolution_nodes st \<and> resolution_node_position nd' = butlast ?q \<and>
      ?fa nd' = Some C' \<and> finite_premise_only_framed C' st nd')"
    if "finite_socket_declared_framed D \<Phi> Vp Vh ch F st ?q Y g" for Y
    using that unfolding finite_socket_declared_framed_def finite_socket_kept_framed_def finite_socket_free_framed_def
    by (auto split: option.splits)
  have narrowed: "\<exists>nd C. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = butlast ?q \<and> ?fa nd = Some C \<and>
      finite_children_framed C st nd (last ?q) \<and> finite_premise_only_unshared nd"
  proof (cases g)
    case (Resolution_Call_Goal q r e p)
    obtain x y where v: "resolution_view_pattern Vp p = Some (x,y)"
      using sc Resolution_Call_Goal by (auto simp: finite_socket_commitment_framed_def split: option.splits)
    show ?thesis using cn Resolution_Call_Goal v unfolding finite_call_framed_def by (auto split: option.splits)
  next
    case (Resolution_Material_Goal q r M)
    show ?thesis using mn Resolution_Material_Goal unfolding finite_material_framed_def by (auto split: option.splits)
  qed
  have decl: "\<exists>Y. finite_socket_declared_framed D \<Phi> Vp Vh ch F st ?q Y g"
  proof (cases g)
    case (Resolution_Call_Goal q r e p)
    then show ?thesis using sc by (auto simp: finite_socket_commitment_framed_def split: option.splits)
  next
    case (Resolution_Material_Goal q r M)
    then show ?thesis using sc by (auto simp: finite_socket_commitment_framed_def)
  qed
  obtain Y where dY: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st ?q Y g" using decl by blast
  obtain nd' C' where qne: "?q \<noteq> []" and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast ?q"
    and fa': "?fa nd' = Some C'" and pof: "finite_premise_only_framed C' st nd'"
    using declared[OF dY] by blast
  obtain nd C where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast ?q"
    and fa: "?fa nd = Some C" and closed: "finite_children_framed C st nd (last ?q)"
    and unsh: "finite_premise_only_unshared nd"
    using narrowed by blast
  have same: "nd' = nd" using dist nd'(1) nd(1) nd'(2) nd(2) unfolding resolution_positions_distinct_def by auto
  then have "C' = C" using fa fa' by simp
  then have "finite_framed_parent_context P C st nd (last ?q)"
    using nd(1) I closed unsh pof same
    unfolding finite_framed_parent_context_def resolution_invariant_def resolution_nodes_placed_def by blast
  then show thesis using that nd qne fa by blast
qed

subsection \<open>The socket's own variables and the absorbed frame\<close>

lemma finite_socket_own_member:
  "z |\<in>| finite_socket_own Vp S s \<longleftrightarrow>
    (\<exists>d p xi yo. (s,d,p) |\<in>| finite_schema_premises S \<and> resolution_view_pattern Vp p = Some (xi,yo) \<and>
      z |\<in>| finite_pattern_variables yo) \<or>
    (\<exists>N. (s,N) |\<in>| finite_schema_materials S \<and> z |\<in>| finite_material_variables N)"
  by (auto simp: finite_socket_own_def ffUnion.rep_eq fimage.rep_eq ffilter.rep_eq split: option.splits; force)

lemma finite_socket_own_premise:
  assumes formed: "schema_formed (decode_finite_schema S)"
    and p0: "(s,e,p0) |\<in>| finite_schema_premises S" and v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
  shows "finite_socket_own Vp S s |\<subseteq>| finite_pattern_variables yo0"
proof (rule fsubsetI)
  let ?D = "decode_finite_schema S"
  have sv: "single_valued (schema_premises ?D)"
    and dis: "rel_dom (schema_premises ?D) \<inter> rel_dom (schema_material_premises ?D) = {}"
    using formed by (simp_all add: schema_formed_def)
  have prem_dec: "(s',d,decode_finite_pattern p) \<in> schema_premises ?D" if "(s',d,p) |\<in>| finite_schema_premises S" for s' d p
    using that by (force simp: decode_finite_call_pattern_def)
  have mat_dec: "(s',decode_finite_material N) \<in> schema_material_premises ?D" if "(s',N) |\<in>| finite_schema_materials S" for s' N
    using that by auto
  fix z assume "z |\<in>| finite_socket_own Vp S s"
  then consider (prem) d p xi yo where "(s,d,p) |\<in>| finite_schema_premises S" "resolution_view_pattern Vp p = Some (xi,yo)"
      "z |\<in>| finite_pattern_variables yo"
    | (mat) N where "(s,N) |\<in>| finite_schema_materials S"
    unfolding finite_socket_own_member by blast
  then show "z |\<in>| finite_pattern_variables yo0"
  proof cases
    case prem
    have "(d,decode_finite_pattern p) = (e,decode_finite_pattern p0)"
      by (rule single_valued_outputs[OF sv prem_dec[OF prem(1)] prem_dec[OF p0]])
    then have "p = p0" by simp
    then show ?thesis using prem(2,3) v0 by simp
  next
    case mat
    have "s \<in> rel_dom (schema_premises ?D)" using prem_dec[OF p0] by auto
    moreover have "s \<in> rel_dom (schema_material_premises ?D)" using mat_dec[OF mat] by auto
    ultimately show ?thesis using dis by blast
  qed
qed

lemma finite_socket_own_material:
  assumes formed: "schema_formed (decode_finite_schema S)" and N0: "(s,N0) |\<in>| finite_schema_materials S"
  shows "finite_socket_own Vp S s |\<subseteq>| finite_material_variables N0"
proof (rule fsubsetI)
  let ?D = "decode_finite_schema S"
  have svm: "single_valued (schema_material_premises ?D)"
    and dis: "rel_dom (schema_premises ?D) \<inter> rel_dom (schema_material_premises ?D) = {}"
    using formed by (simp_all add: schema_formed_def)
  have prem_dec: "(s',d,decode_finite_pattern p) \<in> schema_premises ?D" if "(s',d,p) |\<in>| finite_schema_premises S" for s' d p
    using that by (force simp: decode_finite_call_pattern_def)
  have mat_dec: "(s',decode_finite_material N) \<in> schema_material_premises ?D" if "(s',N) |\<in>| finite_schema_materials S" for s' N
    using that by auto
  fix z assume "z |\<in>| finite_socket_own Vp S s"
  then consider (prem) d p where "(s,d,p) |\<in>| finite_schema_premises S"
    | (mat) N where "(s,N) |\<in>| finite_schema_materials S" "z |\<in>| finite_material_variables N"
    unfolding finite_socket_own_member by blast
  then show "z |\<in>| finite_material_variables N0"
  proof cases
    case prem
    have "s \<in> rel_dom (schema_premises ?D)" using prem_dec[OF prem] by auto
    moreover have "s \<in> rel_dom (schema_material_premises ?D)" using mat_dec[OF N0] by auto
    ultimately show ?thesis using dis by blast
  next
    case mat
    have "decode_finite_material N = decode_finite_material N0"
      by (rule single_valued_outputs[OF svm mat_dec[OF mat(1)] mat_dec[OF N0]])
    then show ?thesis using mat(2) finite_material_variables_correct[of N] finite_material_variables_correct[of N0] by auto
  qed
qed

lemma finite_parent_absorbed_iff:
  assumes vh: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho)"
  shows "z |\<in>| finite_parent_absorbed Vp Vh C nd s \<longleftrightarrow> (\<exists>b. b |\<in>| finite_pattern_variables ho \<and> b |\<in>| C \<and>
    b |\<notin>| finite_socket_own Vp (resolution_node_schema nd) s \<and> z |\<in>| finite_pattern_variables (finite_node_binding nd b))"
  by (auto simp: finite_parent_absorbed_def vh ffUnion.rep_eq fimage.rep_eq ffilter.rep_eq)

text \<open>
  A variant head output absorbs every frame: each of its variables is bound to a variable of its own, so both conditions
  of (iii) hold whatever the frame, and the variables bound at the first kind lie in the call's output (B1's
  @{text finite_socket_free_framed_default} reads the same argument at the default frame).
\<close>

lemma finite_variant_absorbs:
  assumes vh: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho)"
    and var: "finite_variant ho (finite_pattern_substitute (finite_node_binding nd) ho)"
  shows "finite_parent_absorbs Vp Vh C nd s"
    and "finite_parent_absorbed Vp Vh C nd s |\<subseteq>| finite_pattern_variables (finite_pattern_substitute (finite_node_binding nd) ho)"
proof -
  let ?S = "resolution_node_schema nd"
  let ?\<beta> = "finite_node_binding nd"
  have hv: "\<exists>v. ?\<beta> a = Finite_Variable v \<and>
      (\<forall>b. b |\<in>| finite_pattern_variables ho \<longrightarrow> b \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b))"
    if "a |\<in>| finite_pattern_variables ho" for a
    by (rule finite_variant_substitute_apart[OF var that])
  have i: "a |\<in>| C \<longrightarrow> a |\<notin>| finite_socket_own Vp ?S s \<longrightarrow> (case ?\<beta> a of Finite_Variable v \<Rightarrow>
      fBall (finite_pattern_variables ho) (\<lambda>b. b \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b)) | _ \<Rightarrow> False)"
    if a: "a |\<in>| finite_pattern_variables ho" for a
  proof -
    obtain v where v: "?\<beta> a = Finite_Variable v"
        and dis: "\<forall>b. b |\<in>| finite_pattern_variables ho \<longrightarrow> b \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b)"
      using hv[OF a] by blast
    show ?thesis using dis by (auto simp: v)
  qed
  have ii: "a |\<notin>| C \<longrightarrow> fBall (finite_pattern_variables ho) (\<lambda>b. b |\<in>| C \<longrightarrow>
      finite_pattern_variables (?\<beta> a) |\<inter>| finite_pattern_variables (?\<beta> b) = {||})"
    if a: "a |\<in>| finite_pattern_variables ho" for a
  proof (intro impI fBallI)
    fix b assume aC: "a |\<notin>| C" and b: "b |\<in>| finite_pattern_variables ho" and bC: "b |\<in>| C"
    have ba: "b \<noteq> a" using aC bC by auto
    obtain v where v: "?\<beta> a = Finite_Variable v"
        and dis: "\<forall>c. c |\<in>| finite_pattern_variables ho \<longrightarrow> c \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> c)"
      using hv[OF a] by blast
    have "v |\<notin>| finite_pattern_variables (?\<beta> b)" using dis b ba by blast
    then show "finite_pattern_variables (?\<beta> a) |\<inter>| finite_pattern_variables (?\<beta> b) = {||}"
      by (auto simp: v fset_eq_iff)
  qed
  show "finite_parent_absorbs Vp Vh C nd s"
    unfolding finite_parent_absorbs_def vh option.case prod.case by (intro conjI fBallI) (erule i, erule ii)
  show "finite_parent_absorbed Vp Vh C nd s |\<subseteq>| finite_pattern_variables (finite_pattern_substitute ?\<beta> ho)"
  proof (rule fsubsetI)
    fix w assume "w |\<in>| finite_parent_absorbed Vp Vh C nd s"
    then obtain a where a: "a |\<in>| finite_pattern_variables ho" "w |\<in>| finite_pattern_variables (?\<beta> a)"
      by (auto simp: finite_parent_absorbed_def vh ffUnion.rep_eq)
    show "w |\<in>| finite_pattern_variables (finite_pattern_substitute ?\<beta> ho)"
      by (rule finite_pattern_substitute_variable_holds[where \<beta>="?\<beta>", OF a])
  qed
qed

lemma finite_pattern_substitute_variables_iff:
  "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) \<longleftrightarrow>
    (\<exists>c. c |\<in>| finite_pattern_variables p \<and> z |\<in>| finite_pattern_variables (\<sigma> c))"
  by (induction p) auto

lemma finite_material_substitute_variables:
  "z |\<in>| finite_material_variables (finite_material_pattern_substitute \<sigma> N) \<longleftrightarrow>
    (\<exists>c. c |\<in>| finite_material_variables N \<and> z |\<in>| finite_pattern_variables (\<sigma> c))"
  by (auto simp: finite_material_variables_def finite_pattern_substitute_variables_iff)

subsection \<open>A valuation read from a new instance, one variable at a time\<close>

text \<open>
  A new grounding that takes a new instance @{text h'} of a clause at each clause variable through its binding, given one
  of three kinds for each variable: kept (its binding's variables unchanged, its value the support's), set (bound to a
  changed variable of its own) or the goal's (its binding's variables among the goal's, its value the new answer's).
  The changed variables take the new instance's value of the variable binding them; this is where the parent's variables
  are set one by one at a socket's exchange.
\<close>

lemma finite_kinds_valuation:
  fixes \<beta> :: "'a \<Rightarrow> 'v finite_term_pattern" and \<theta> \<theta>2 :: "'v \<Rightarrow> finite_factor_term" and h' :: "'a \<Rightarrow> factor_term"
  assumes kinds: "\<And>c. c \<in> A \<Longrightarrow>
      (h' c = decode_finite_term (resolution_value \<theta> (\<beta> c)) \<and>
        (\<forall>z. z |\<in>| finite_pattern_variables (\<beta> c) \<longrightarrow> z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z))) \<or>
      (\<exists>z. \<beta> c = Finite_Variable z \<and> z \<in> Z) \<or>
      (h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c)) \<and>
        (\<forall>z. z |\<in>| finite_pattern_variables (\<beta> c) \<longrightarrow> z \<in> Y))"
    and coherent: "\<And>c c' z. c \<in> A \<Longrightarrow> c' \<in> A \<Longrightarrow> \<beta> c = Finite_Variable z \<Longrightarrow> \<beta> c' = Finite_Variable z \<Longrightarrow>
      z \<in> Z \<Longrightarrow> h' c = h' c'"
    and apart: "Y \<inter> Z = {}" and formed: "\<And>c. c \<in> A \<Longrightarrow> term_formed (h' c)"
  obtains \<theta>1 where "\<And>z. z \<in> Y \<Longrightarrow> \<theta>1 z = \<theta>2 z" "\<And>z. z \<notin> Y \<Longrightarrow> z \<notin> Z \<Longrightarrow> \<theta>1 z = \<theta> z"
    "\<And>c. c \<in> A \<Longrightarrow> decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
proof -
  define \<theta>1 where "\<theta>1 = (\<lambda>z. if z \<in> Y then \<theta>2 z
    else if z \<in> Z then finite_term_of (h' (SOME c. c \<in> A \<and> \<beta> c = Finite_Variable z)) else \<theta> z)"
  have K: "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c" if c: "c \<in> A" for c
    using kinds[OF c]
  proof (elim disjE conjE exE)
    assume e: "h' c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
      and vs: "\<forall>z. z |\<in>| finite_pattern_variables (\<beta> c) \<longrightarrow> z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z)"
    have "resolution_value \<theta>1 (\<beta> c) = resolution_value \<theta> (\<beta> c)"
      by (rule resolution_value_cong) (use vs in \<open>auto simp: \<theta>1_def\<close>)
    then show ?thesis using e by simp
  next
    fix z assume bz: "\<beta> c = Finite_Variable z" and zZ: "z \<in> Z"
    have zY: "z \<notin> Y" using zZ apart by blast
    have ex: "\<exists>c'. c' \<in> A \<and> \<beta> c' = Finite_Variable z" using c bz by blast
    have sc: "(SOME c'. c' \<in> A \<and> \<beta> c' = Finite_Variable z) \<in> A \<and>
        \<beta> (SOME c'. c' \<in> A \<and> \<beta> c' = Finite_Variable z) = Finite_Variable z"
      by (rule someI_ex[OF ex])
    have eq: "h' (SOME c'. c' \<in> A \<and> \<beta> c' = Finite_Variable z) = h' c"
      by (rule coherent[OF conjunct1[OF sc] c conjunct2[OF sc] bz zZ])
    have "\<theta>1 z = finite_term_of (h' c)" using zY zZ eq by (simp add: \<theta>1_def)
    then show ?thesis using bz decode_finite_term_of[OF formed[OF c]] by (simp add: resolution_value_def)
  next
    assume e: "h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c))"
      and vs: "\<forall>z. z |\<in>| finite_pattern_variables (\<beta> c) \<longrightarrow> z \<in> Y"
    have "resolution_value \<theta>1 (\<beta> c) = resolution_value \<theta>2 (\<beta> c)"
      by (rule resolution_value_cong) (use vs in \<open>simp add: \<theta>1_def\<close>)
    then show ?thesis using e by simp
  qed
  show thesis
  proof (rule that[of \<theta>1])
    show "\<theta>1 z = \<theta>2 z" if "z \<in> Y" for z using that by (simp add: \<theta>1_def)
    show "\<theta>1 z = \<theta> z" if "z \<notin> Y" "z \<notin> Z" for z using that by (simp add: \<theta>1_def)
    show "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c" if "c \<in> A" for c by (rule K[OF that])
  qed
qed

text \<open>
  At a parent context at a frame C, a new instance @{text h'} of the parent's clause that agrees with the old instance
  @{text h} outside C and keeps the head as the socket says, whose values at the socket's own variables O are the new
  answer's: every clause variable is of one of the three kinds, the parent's variables set one by one. A premise-only
  variable in O is the goal's; one outside O is free (set on its own variable) or outside C with a ground binding
  (kept). At the kept head every head variable is kept. At a free socket a head input is kept; a head output in O is the
  goal's, through the goal's own variables; one in C outside O is set on the fresh variable its binding is, by (iii);
  one outside C is kept, its binding's variables no changed one's, by (iii) and the call's apartness. The changed
  variables are the free premise-only variables and, at a free socket, the absorbed ones: nothing else changes.
\<close>

lemma finite_framed_valuation:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
    and \<theta> \<theta>2 :: "('s,'a) resolution_variable \<Rightarrow> finite_factor_term"
  assumes I: "resolution_invariant P d t st"
    and ctx: "finite_framed_parent_context P C st nd k"
    and Vh: "view_formed Vh"
    and own: "finite_socket_own Vp (resolution_node_schema nd) k |\<subseteq>| Ow"
    and OS: "Ow |\<subseteq>| finite_schema_variables (resolution_node_schema nd)"
    and old_O: "\<And>c. c |\<in>| Ow \<Longrightarrow> h c = decode_finite_term (resolution_value \<theta> (finite_node_binding nd c))"
    and new_O: "\<And>c. c |\<in>| Ow \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (finite_node_binding nd c))"
    and Y: "\<And>z. z \<in> Y \<longleftrightarrow> (\<exists>c. c |\<in>| Ow \<and> z |\<in>| finite_pattern_variables (finite_node_binding nd c))"
    and frame: "\<And>a. a |\<in>| finite_schema_variables (resolution_node_schema nd) \<Longrightarrow> a |\<notin>| C \<Longrightarrow> h' a = h a"
    and head: "(keep \<and> head_kept True Vh (resolution_node_schema nd) h h') \<or>
      (\<not> keep \<and> head_kept False Vh (resolution_node_schema nd) h h' \<and> finite_parent_absorbs Vp Vh C nd k \<and>
        finite_input_output_apart Vh nd)"
    and formed: "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema nd) \<Longrightarrow> term_formed (h' c)"
  obtains \<theta>1 where "\<And>z. z \<in> Y \<Longrightarrow> \<theta>1 z = \<theta>2 z"
    and "\<And>z. z \<notin> Y \<Longrightarrow> \<not> finite_free_premise_variable st nd z \<Longrightarrow>
      keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C nd k \<Longrightarrow> \<theta>1 z = \<theta> z"
    and "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema nd) \<Longrightarrow>
      h c = decode_finite_term (resolution_value \<theta> (finite_node_binding nd c)) \<or>
        (c |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd)) \<and>
          finite_free_premise_only st nd c) \<Longrightarrow>
      decode_finite_term (resolution_value \<theta>1 (finite_node_binding nd c)) = h' c"
proof -
  let ?S = "resolution_node_schema nd"
  let ?\<beta> = "finite_node_binding nd"
  let ?SV = "finite_schema_variables ?S"
  let ?cv = "finite_pattern_variables (finite_schema_conclusion ?S)"
  let ?own = "\<lambda>a. ((resolution_node_position nd,True),a)"
  let ?call = "finite_pattern_variables (resolution_node_call nd)"
  let ?A = "{c. c |\<in>| ?SV \<and> (h c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<or>
    (c |\<notin>| ?cv \<and> finite_free_premise_only st nd c))}"
  have nd: "nd |\<in>| resolution_nodes st" and unshared: "finite_premise_only_unshared nd"
    using ctx by (simp_all add: finite_framed_parent_context_def)
  note linked = finite_node_binding_linked[OF I nd]
  have po: "finite_free_premise_only st nd a \<or> (a |\<notin>| C \<and> finite_pattern_variables (?\<beta> a) = {||})"
    if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    by (rule finite_framed_premise_only[OF I ctx that])
  have own_var: "?\<beta> a = Finite_Variable (?own a)" if "finite_free_premise_only st nd a" for a
    using that unfolding finite_free_premise_only_def by blast
  have own_call: "?own a |\<notin>| ?call" if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    using unshared that unfolding finite_premise_only_unshared_def by auto
  have in_call: "z |\<in>| ?call" if "c |\<in>| ?cv" "z |\<in>| finite_pattern_variables (?\<beta> c)" for c z
    unfolding linked(2) by (rule finite_pattern_substitute_variable_holds[where \<beta>="?\<beta>", OF that])
  have nc: "finite_free_premise_only st nd c \<and> z = ?own c \<and> z |\<notin>| ?call"
    if c: "c |\<in>| ?SV" "c |\<notin>| ?cv" and z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for c z
  proof -
    have f: "finite_free_premise_only st nd c" using po[OF c] z by auto
    have "z = ?own c" using z own_var[OF f] by simp
    then show ?thesis using f own_call[OF c] by simp
  qed
  have OSV: "c |\<in>| ?SV" if "c |\<in>| Ow" for c using OS that by (meson fsubsetD)
  have agree_O: "\<theta>2 z = \<theta> z" if "c' |\<in>| Ow" "h' c' = h c'" "z |\<in>| finite_pattern_variables (?\<beta> c')" for c' z
  proof -
    have "resolution_value \<theta>2 (?\<beta> c') = resolution_value \<theta> (?\<beta> c')"
      using new_O[OF that(1)] old_O[OF that(1)] that(2) by simp
    then show ?thesis by (rule resolution_value_agree) (rule that(3))
  qed
  have Yown: "c |\<in>| Ow" if c: "c |\<in>| ?SV" "c |\<notin>| ?cv" and f: "finite_free_premise_only st nd c" and y: "?own c \<in> Y" for c
  proof -
    obtain c' where c': "c' |\<in>| Ow" "?own c |\<in>| finite_pattern_variables (?\<beta> c')" using Y y by blast
    show ?thesis
    proof (cases "c' |\<in>| ?cv")
      case True
      then show ?thesis using in_call[OF True c'(2)] own_call[OF c] by simp
    next
      case False
      have "?own c = ?own c'" using nc[OF OSV[OF c'(1)] False c'(2)] by blast
      then have "c = c'" by simp
      then show ?thesis using c'(1) by simp
    qed
  qed
  have noncv: "(h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<and>
        (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z))) \<or>
      (\<exists>z. ?\<beta> c = Finite_Variable z \<and> z \<in> Z) \<or>
      (h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c)) \<and>
        (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<in> Y))"
    if cA: "c \<in> ?A" and nO: "c |\<notin>| Ow" and ncv: "c |\<notin>| ?cv"
      and ZI: "\<And>a. a |\<in>| ?SV \<Longrightarrow> a |\<notin>| ?cv \<Longrightarrow> finite_free_premise_only st nd a \<Longrightarrow> ?own a \<notin> Y \<Longrightarrow> ?own a \<in> Z"
    for c Z
  proof -
    have cS: "c |\<in>| ?SV" using cA by simp
    show ?thesis
    proof (cases "finite_free_premise_only st nd c")
      case True
      have nY: "?own c \<notin> Y" using Yown[OF cS ncv True] nO by blast
      then show ?thesis using own_var[OF True] ZI[OF cS ncv True nY] by blast
    next
      case False
      have gr: "c |\<notin>| C \<and> finite_pattern_variables (?\<beta> c) = {||}" using po[OF cS ncv] False by blast
      have hc: "h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using cA False by simp
      show ?thesis using frame[OF cS conjunct1[OF gr]] hc gr by simp
    qed
  qed
  show thesis
  proof (cases keep)
    case True
    have hk: "head_kept True Vh ?S h h'" using head True by blast
    have kept: "h' c = h c" if "c |\<in>| ?cv" for c by (rule head_kept_variables[OF hk Vh that])
    define Z where "Z = {z. \<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> finite_free_premise_only st nd a \<and> z = ?own a} - Y"
    have Zcall: "z |\<notin>| ?call" if "z \<in> Z" for z using that own_call unfolding Z_def by blast
    have ZI: "?own a \<in> Z" if "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "?own a \<notin> Y" for a
      using that unfolding Z_def by blast
    have kinds: "(h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<and>
          (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z))) \<or>
        (\<exists>z. ?\<beta> c = Finite_Variable z \<and> z \<in> Z) \<or>
        (h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c)) \<and>
          (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<in> Y))"
      if cA: "c \<in> ?A" for c
    proof (cases "c |\<in>| Ow")
      case True
      then show ?thesis using new_O[OF True] Y by blast
    next
      case nO: False
      show ?thesis
      proof (cases "c |\<in>| ?cv")
        case cv: True
        have hc: "h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using cA cv by simp
        have vs: "z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z)" if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for z
        proof
          have zc: "z |\<in>| ?call" by (rule in_call[OF cv z])
          show "z \<notin> Z" using zc Zcall by blast
          show "z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z"
          proof
            assume "z \<in> Y"
            then obtain c' where c': "c' |\<in>| Ow" "z |\<in>| finite_pattern_variables (?\<beta> c')" using Y by blast
            show "\<theta>2 z = \<theta> z"
            proof (cases "c' |\<in>| ?cv")
              case True
              show ?thesis by (rule agree_O[OF c'(1) kept[OF True] c'(2)])
            next
              case False
              then show ?thesis using nc[OF OSV[OF c'(1)] False c'(2)] zc by blast
            qed
          qed
        qed
        have "h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using kept[OF cv] hc by simp
        then show ?thesis using vs by blast
      next
        case ncv: False
        show ?thesis by (rule noncv[OF cA nO ncv ZI])
      qed
    qed
    have coh: "h' c = h' c'"
      if cA: "c \<in> ?A" and cA': "c' \<in> ?A" and bc: "?\<beta> c = Finite_Variable z" and bc': "?\<beta> c' = Finite_Variable z"
        and zZ: "z \<in> Z" for c c' z
    proof -
      obtain a where a: "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "z = ?own a"
        using zZ unfolding Z_def by blast
      have same: "b = a" if b: "b |\<in>| ?SV" "?\<beta> b = Finite_Variable z" for b
      proof (cases "b |\<in>| ?cv")
        case True
        have "z |\<in>| ?call" by (rule in_call[OF True]) (simp add: b(2))
        then show ?thesis using own_call[OF a(1,2)] a(4) by simp
      next
        case False
        have "z = ?own b" using nc[OF b(1) False, of z] b(2) by simp
        then show ?thesis using a(4) by simp
      qed
      have "c = a" "c' = a" using same[of c] same[of c'] cA cA' bc bc' by simp_all
      then show ?thesis by simp
    qed
    have disj: "Y \<inter> Z = {}" unfolding Z_def by blast
    have formedA: "term_formed (h' c)" if "c \<in> ?A" for c using formed that by simp
    obtain \<theta>1 where t1: "\<And>z. z \<in> Y \<Longrightarrow> \<theta>1 z = \<theta>2 z" and t2: "\<And>z. z \<notin> Y \<Longrightarrow> z \<notin> Z \<Longrightarrow> \<theta>1 z = \<theta> z"
      and t3: "\<And>c. c \<in> ?A \<Longrightarrow> decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      by (rule finite_kinds_valuation[where A="?A" and h'=h' and \<theta>=\<theta> and \<beta>="?\<beta>" and Z=Z and Y=Y and ?\<theta>2.0=\<theta>2,
        OF kinds coh disj formedA]) (assumption | rule that)+
    show thesis
    proof (rule that[of \<theta>1])
      show "\<theta>1 z = \<theta>2 z" if "z \<in> Y" for z by (rule t1[OF that])
      show "\<theta>1 z = \<theta> z" if "z \<notin> Y" "\<not> finite_free_premise_variable st nd z"
          "keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C nd k" for z
      proof (rule t2[OF that(1)])
        show "z \<notin> Z"
        proof
          assume "z \<in> Z"
          then obtain a where "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "z = ?own a"
            unfolding Z_def by blast
          then have "finite_free_premise_variable st nd z" by (simp add: finite_free_premise_variable_def)
          then show False using that(2) by blast
        qed
      qed
      show "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
        if "c |\<in>| ?SV" "h c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<or>
          (c |\<notin>| ?cv \<and> finite_free_premise_only st nd c)" for c
        by (rule t3) (use that in simp)
    qed
  next
    case nk: False
    have hk: "head_kept False Vh ?S h h'" and abs: "finite_parent_absorbs Vp Vh C nd k"
      and ap: "finite_input_output_apart Vh nd" using head nk by blast+
    obtain hi ho where vh: "resolution_view_pattern Vh (finite_schema_conclusion ?S) = Some (hi,ho)"
      using abs by (auto simp: finite_parent_absorbs_def split: option.splits)
    have cvs: "?cv = finite_pattern_variables hi |\<union>| finite_pattern_variables ho"
      by (rule resolution_view_pattern_variables[OF Vh vh])
    have vk: "resolution_view_pattern Vh (resolution_node_call nd) =
        Some (finite_pattern_substitute ?\<beta> hi,finite_pattern_substitute ?\<beta> ho)"
      unfolding linked(2) by (rule resolution_view_pattern_substitute[OF vh])
    have disj_io: "finite_pattern_variables (finite_pattern_substitute ?\<beta> hi) |\<inter>|
        finite_pattern_variables (finite_pattern_substitute ?\<beta> ho) = {||}"
      using ap vk unfolding finite_input_output_apart_def by simp
    have io: False
      if "c |\<in>| finite_pattern_variables hi" "z |\<in>| finite_pattern_variables (?\<beta> c)"
        "c' |\<in>| finite_pattern_variables ho" "z |\<in>| finite_pattern_variables (?\<beta> c')" for c c' z
    proof -
      have "z |\<in>| finite_pattern_variables (finite_pattern_substitute ?\<beta> hi) |\<inter>|
          finite_pattern_variables (finite_pattern_substitute ?\<beta> ho)"
        using finite_pattern_substitute_variable_holds[where \<beta>="?\<beta>", OF that(1,2)]
          finite_pattern_substitute_variable_holds[where \<beta>="?\<beta>", OF that(3,4)]
        by simp
      then show False using disj_io by simp
    qed
    have input_kept: "h' c = h c" if "c |\<in>| finite_pattern_variables hi" for c
      by (rule evaluate_pattern_agree[OF head_kept_input[OF hk vh]]) (simp add: that finite_pattern_variables_correct[symmetric])
    have ab1: "\<exists>v. ?\<beta> a = Finite_Variable v \<and>
        (\<forall>b. b |\<in>| finite_pattern_variables ho \<longrightarrow> b \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b))"
      if "a |\<in>| finite_pattern_variables ho" "a |\<in>| C" "a |\<notin>| finite_socket_own Vp ?S k" for a
    proof -
      have c: "case ?\<beta> a of Finite_Variable v \<Rightarrow>
          fBall (finite_pattern_variables ho) (\<lambda>b. b \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b)) | _ \<Rightarrow> False"
        using abs that unfolding finite_parent_absorbs_def vh option.case prod.case by blast
      then show ?thesis by (cases "?\<beta> a") auto
    qed
    have ab2: "finite_pattern_variables (?\<beta> a) |\<inter>| finite_pattern_variables (?\<beta> b) = {||}"
      if "a |\<in>| finite_pattern_variables ho" "a |\<notin>| C" "b |\<in>| finite_pattern_variables ho" "b |\<in>| C" for a b
      using abs that unfolding finite_parent_absorbs_def vh option.case prod.case by blast
    have absorbed: "z |\<in>| finite_parent_absorbed Vp Vh C nd k \<longleftrightarrow> (\<exists>b. b |\<in>| finite_pattern_variables ho \<and> b |\<in>| C \<and>
        b |\<notin>| finite_socket_own Vp ?S k \<and> z |\<in>| finite_pattern_variables (?\<beta> b))" for z
      by (rule finite_parent_absorbed_iff[OF vh])
    define Z where "Z = ({z. \<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> finite_free_premise_only st nd a \<and> z = ?own a} \<union>
      fset (finite_parent_absorbed Vp Vh C nd k)) - Y"
    have ZI: "?own a \<in> Z" if "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "?own a \<notin> Y" for a
      using that unfolding Z_def by blast
    have Zcases: "(\<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> finite_free_premise_only st nd a \<and> z = ?own a) \<or>
        (\<exists>b. b |\<in>| finite_pattern_variables ho \<and> b |\<in>| C \<and> b |\<notin>| finite_socket_own Vp ?S k \<and>
          ?\<beta> b = Finite_Variable z)" if "z \<in> Z" for z
    proof -
      have "(\<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> finite_free_premise_only st nd a \<and> z = ?own a) \<or>
          z |\<in>| finite_parent_absorbed Vp Vh C nd k" using that unfolding Z_def by blast
      then show ?thesis
      proof
        assume "z |\<in>| finite_parent_absorbed Vp Vh C nd k"
        then obtain b where b: "b |\<in>| finite_pattern_variables ho" "b |\<in>| C" "b |\<notin>| finite_socket_own Vp ?S k"
            "z |\<in>| finite_pattern_variables (?\<beta> b)" using absorbed by blast
        obtain v where v: "?\<beta> b = Finite_Variable v" using ab1[OF b(1-3)] by blast
        show ?thesis using b v by auto
      qed blast
    qed
    have Y_c: "\<theta>2 z = \<theta> z"
      if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" "z \<in> Y" and cho: "c |\<in>| finite_pattern_variables ho" "c |\<notin>| C"
      for c z
    proof -
      obtain c' where c': "c' |\<in>| Ow" "z |\<in>| finite_pattern_variables (?\<beta> c')" using Y z(2) by blast
      have zc: "z |\<in>| ?call" by (rule in_call[OF _ z(1)]) (use cho(1) cvs in simp)
      show ?thesis
      proof (cases "c' |\<in>| finite_pattern_variables hi")
        case True
        then show ?thesis using io[OF True c'(2) cho(1) z(1)] by blast
      next
        case nhi: False
        show ?thesis
        proof (cases "c' |\<in>| ?cv")
          case True
          have c'ho: "c' |\<in>| finite_pattern_variables ho" using True nhi cvs by simp
          show ?thesis
          proof (cases "c' |\<in>| C")
            case True
            have e: "finite_pattern_variables (?\<beta> c) |\<inter>| finite_pattern_variables (?\<beta> c') = {||}"
              by (rule ab2[OF cho c'ho True])
            have "z |\<in>| finite_pattern_variables (?\<beta> c) |\<inter>| finite_pattern_variables (?\<beta> c')"
              using z(1) c'(2) by simp
            then show ?thesis using e by simp
          next
            case False
            show ?thesis by (rule agree_O[OF c'(1) frame[OF OSV[OF c'(1)] False] c'(2)])
          qed
        next
          case False
          then show ?thesis using nc[OF OSV[OF c'(1)] False c'(2)] zc by blast
        qed
      qed
    qed
    have kinds: "(h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<and>
          (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z))) \<or>
        (\<exists>z. ?\<beta> c = Finite_Variable z \<and> z \<in> Z) \<or>
        (h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c)) \<and>
          (\<forall>z. z |\<in>| finite_pattern_variables (?\<beta> c) \<longrightarrow> z \<in> Y))"
      if cA: "c \<in> ?A" for c
    proof (cases "c |\<in>| Ow")
      case True
      then show ?thesis using new_O[OF True] Y by blast
    next
      case nO: False
      have cS: "c |\<in>| ?SV" using cA by simp
      show ?thesis
      proof (cases "c |\<in>| ?cv")
        case ncv: False
        show ?thesis by (rule noncv[OF cA nO ncv ZI])
      next
        case cv: True
        have hc: "h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using cA cv by simp
        show ?thesis
        proof (cases "c |\<in>| finite_pattern_variables hi")
          case chi: True
          have vs: "z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z)" if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for z
          proof
            have zc: "z |\<in>| ?call" by (rule in_call[OF cv z])
            show "z \<notin> Z"
            proof
              assume "z \<in> Z"
              from Zcases[OF this] show False
              proof (elim disjE exE conjE)
                fix a assume "a |\<in>| ?SV" "a |\<notin>| ?cv" "z = ?own a"
                then show False using own_call zc by blast
              next
                fix b assume b: "b |\<in>| finite_pattern_variables ho" "?\<beta> b = Finite_Variable z"
                show False by (rule io[OF chi z b(1)]) (simp add: b(2))
              qed
            qed
            show "z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z"
            proof
              assume "z \<in> Y"
              then obtain c' where c': "c' |\<in>| Ow" "z |\<in>| finite_pattern_variables (?\<beta> c')" using Y by blast
              show "\<theta>2 z = \<theta> z"
              proof (cases "c' |\<in>| finite_pattern_variables hi")
                case True
                show ?thesis by (rule agree_O[OF c'(1) input_kept[OF True] c'(2)])
              next
                case nhi: False
                show ?thesis
                proof (cases "c' |\<in>| ?cv")
                  case True
                  then have "c' |\<in>| finite_pattern_variables ho" using nhi cvs by simp
                  then show ?thesis using io[OF chi z _ c'(2)] by blast
                next
                  case False
                  then show ?thesis using nc[OF OSV[OF c'(1)] False c'(2)] zc by blast
                qed
              qed
            qed
          qed
          have "h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using input_kept[OF chi] hc by simp
          then show ?thesis using vs by blast
        next
          case nhi: False
          have cho: "c |\<in>| finite_pattern_variables ho" using cv nhi cvs by simp
          show ?thesis
          proof (cases "c |\<in>| C")
            case cC: False
            have vs: "z \<notin> Z \<and> (z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z)" if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for z
            proof
              have zc: "z |\<in>| ?call" by (rule in_call[OF cv z])
              show "z \<notin> Z"
              proof
                assume "z \<in> Z"
                from Zcases[OF this] show False
                proof (elim disjE exE conjE)
                  fix a assume "a |\<in>| ?SV" "a |\<notin>| ?cv" "z = ?own a"
                  then show False using own_call zc by blast
                next
                  fix b assume b: "b |\<in>| finite_pattern_variables ho" "b |\<in>| C" "b |\<notin>| finite_socket_own Vp ?S k"
                    "?\<beta> b = Finite_Variable z"
                  obtain v' where v': "?\<beta> b = Finite_Variable v'"
                    and fr: "\<forall>b'. b' |\<in>| finite_pattern_variables ho \<longrightarrow> b' \<noteq> b \<longrightarrow> v' |\<notin>| finite_pattern_variables (?\<beta> b')"
                    using ab1[OF b(1-3)] by blast
                  have "b \<noteq> c" using b(2) cC by blast
                  then have "v' |\<notin>| finite_pattern_variables (?\<beta> c)" using fr cho by blast
                  then show False using z b(4) v' by simp
                qed
              qed
              show "z \<in> Y \<longrightarrow> \<theta>2 z = \<theta> z" using Y_c[OF z _ cho cC] by blast
            qed
            have "h' c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" using frame[OF cS cC] hc by simp
            then show ?thesis using vs by blast
          next
            case cC: True
            have cown: "c |\<notin>| finite_socket_own Vp ?S k" using nO own by (meson fsubsetD)
            obtain v where v: "?\<beta> c = Finite_Variable v"
              and fr: "\<forall>b. b |\<in>| finite_pattern_variables ho \<longrightarrow> b \<noteq> c \<longrightarrow> v |\<notin>| finite_pattern_variables (?\<beta> b)"
              using ab1[OF cho cC cown] by blast
            have vabs: "v |\<in>| finite_parent_absorbed Vp Vh C nd k" using absorbed cho cC cown v by auto
            have vc: "v |\<in>| ?call" by (rule in_call[OF cv]) (simp add: v)
            have vY: "v \<notin> Y"
            proof
              assume "v \<in> Y"
              then obtain c' where c': "c' |\<in>| Ow" "v |\<in>| finite_pattern_variables (?\<beta> c')" using Y by blast
              show False
              proof (cases "c' |\<in>| finite_pattern_variables hi")
                case True
                show False by (rule io[OF True c'(2) cho]) (simp add: v)
              next
                case nhi': False
                show False
                proof (cases "c' |\<in>| ?cv")
                  case True
                  have c'ho: "c' |\<in>| finite_pattern_variables ho" using True nhi' cvs by simp
                  have "c' \<noteq> c" using c'(1) nO by blast
                  then show False using fr c'ho c'(2) by blast
                next
                  case False
                  then show False using nc[OF OSV[OF c'(1)] False c'(2)] vc by blast
                qed
              qed
            qed
            have "v \<in> Z" unfolding Z_def using vabs vY by simp
            then show ?thesis using v by blast
          qed
        qed
      qed
    qed
    have coh: "h' c = h' c'"
      if cA: "c \<in> ?A" and cA': "c' \<in> ?A" and bc: "?\<beta> c = Finite_Variable z" and bc': "?\<beta> c' = Finite_Variable z"
        and zZ: "z \<in> Z" for c c' z
    proof -
      have det: "\<exists>a. \<forall>b. b |\<in>| ?SV \<longrightarrow> ?\<beta> b = Finite_Variable z \<longrightarrow> b = a"
        using Zcases[OF zZ]
      proof (elim disjE exE conjE)
        fix a assume a: "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "z = ?own a"
        show ?thesis
        proof (rule exI[of _ a], intro allI impI)
          fix b assume b: "b |\<in>| ?SV" "?\<beta> b = Finite_Variable z"
          show "b = a"
          proof (cases "b |\<in>| ?cv")
            case True
            have "z |\<in>| ?call" by (rule in_call[OF True]) (simp add: b(2))
            then show ?thesis using own_call[OF a(1,2)] a(4) by simp
          next
            case False
            have "z = ?own b" using nc[OF b(1) False, of z] b(2) by simp
            then show ?thesis using a(4) by simp
          qed
        qed
      next
        fix b0 assume b0: "b0 |\<in>| finite_pattern_variables ho" "b0 |\<in>| C" "b0 |\<notin>| finite_socket_own Vp ?S k"
          "?\<beta> b0 = Finite_Variable z"
        obtain v' where v': "?\<beta> b0 = Finite_Variable v'"
          and fr: "\<forall>b'. b' |\<in>| finite_pattern_variables ho \<longrightarrow> b' \<noteq> b0 \<longrightarrow> v' |\<notin>| finite_pattern_variables (?\<beta> b')"
          using ab1[OF b0(1-3)] by blast
        have zb0: "z |\<in>| finite_pattern_variables (?\<beta> b0)" using b0(4) by simp
        have zc: "z |\<in>| ?call" by (rule in_call[OF _ zb0]) (use b0(1) cvs in simp)
        show ?thesis
        proof (rule exI[of _ b0], intro allI impI)
          fix b assume b: "b |\<in>| ?SV" "?\<beta> b = Finite_Variable z"
          have zb: "z |\<in>| finite_pattern_variables (?\<beta> b)" using b(2) by simp
          show "b = b0"
          proof (cases "b |\<in>| ?cv")
            case False
            then show ?thesis using nc[OF b(1) False zb] zc by blast
          next
            case True
            show ?thesis
            proof (cases "b |\<in>| finite_pattern_variables hi")
              case True
              then show ?thesis using io[OF True zb b0(1) zb0] by blast
            next
              case False
              have bho: "b |\<in>| finite_pattern_variables ho" using True False cvs by simp
              show ?thesis
              proof (rule ccontr)
                assume "b \<noteq> b0"
                then have "v' |\<notin>| finite_pattern_variables (?\<beta> b)" using fr bho by blast
                then show False using zb v' b0(4) by simp
              qed
            qed
          qed
        qed
      qed
      then obtain a where "\<forall>b. b |\<in>| ?SV \<longrightarrow> ?\<beta> b = Finite_Variable z \<longrightarrow> b = a" by blast
      then have "c = a" "c' = a" using cA cA' bc bc' by auto
      then show ?thesis by simp
    qed
    have disj: "Y \<inter> Z = {}" unfolding Z_def by blast
    have formedA: "term_formed (h' c)" if "c \<in> ?A" for c using formed that by simp
    obtain \<theta>1 where t1: "\<And>z. z \<in> Y \<Longrightarrow> \<theta>1 z = \<theta>2 z" and t2: "\<And>z. z \<notin> Y \<Longrightarrow> z \<notin> Z \<Longrightarrow> \<theta>1 z = \<theta> z"
      and t3: "\<And>c. c \<in> ?A \<Longrightarrow> decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      by (rule finite_kinds_valuation[where A="?A" and h'=h' and \<theta>=\<theta> and \<beta>="?\<beta>" and Z=Z and Y=Y and ?\<theta>2.0=\<theta>2,
        OF kinds coh disj formedA]) (assumption | rule that)+
    show thesis
    proof (rule that[of \<theta>1])
      show "\<theta>1 z = \<theta>2 z" if "z \<in> Y" for z by (rule t1[OF that])
      show "\<theta>1 z = \<theta> z" if "z \<notin> Y" "\<not> finite_free_premise_variable st nd z"
          "keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C nd k" for z
      proof (rule t2[OF that(1)])
        have na: "z |\<notin>| finite_parent_absorbed Vp Vh C nd k" using that(3) nk by blast
        show "z \<notin> Z"
        proof
          assume "z \<in> Z"
          then have "(\<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> finite_free_premise_only st nd a \<and> z = ?own a)"
            using na unfolding Z_def by blast
          then obtain a where "a |\<in>| ?SV" "a |\<notin>| ?cv" "finite_free_premise_only st nd a" "z = ?own a" by blast
          then have "finite_free_premise_variable st nd z" by (simp add: finite_free_premise_variable_def)
          then show False using that(2) by blast
        qed
      qed
      show "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
        if "c |\<in>| ?SV" "h c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<or>
          (c |\<notin>| ?cv \<and> finite_free_premise_only st nd c)" for c
        by (rule t3) (use that in simp)
    qed
  qed
qed

subsection \<open>The socket's obligation re-grounds the pending siblings\<close>

text \<open>
  At a focus holding the parent's children, the parent clause's instance under the support is true: its premises and
  material premises are the pending children, focused and holding. The canonical answer satisfies the socket's material
  premise at the same source, so the obligation gives a true instance agreeing with it on the material variables and
  keeping the head (its input only, at a free socket). The valuation reads that instance at the premise-only variables,
  which the siblings alone hold, and at the output's variables, which only the siblings hold there; it keeps the support
  elsewhere, which no premise-only variable and no output variable reaches in the parent's call.
\<close>

lemma finite_framed_material_valuation:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st"
    and ctx: "finite_framed_parent_context P C st nd k"
    and N0: "(k,N0) |\<in>| finite_schema_materials (resolution_node_schema nd)"
    and g: "Resolution_Material_Goal (resolution_node_position nd@[k]) r M |\<in>| resolution_pending st"
    and M: "M = finite_material_pattern_substitute (finite_node_binding nd) N0"
    and focus: "resolution_focused F (resolution_node_position nd)"
    and holds: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    and socket: "socket_framed (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) k keep Vp Vh (fset C)"
    and Vh: "view_formed Vh"
    and head: "keep \<or> (finite_parent_absorbs Vp Vh C nd k \<and> finite_input_output_apart Vh nd)"
    and outside: "\<And>h z b hi ho. h |\<in>| finite_focus_pending F st \<Longrightarrow>
        \<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position nd) \<Longrightarrow>
        \<not> keep \<Longrightarrow> resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho) \<Longrightarrow>
        b |\<in>| finite_pattern_variables ho \<Longrightarrow> b |\<in>| C \<Longrightarrow> z |\<in>| finite_pattern_variables (finite_node_binding nd b) \<Longrightarrow>
        z |\<notin>| resolution_goal_variables h"
    and free: "finite_free_fields M"
    and source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole R)"
  shows "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R) \<and>
    finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> Resolution_Material_Goal (resolution_node_position nd@[k]) r M \<longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h)"
proof -
  let ?Mn = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema nd"
  let ?pos = "resolution_node_position nd"
  let ?\<beta> = "finite_node_binding nd"
  let ?SV = "finite_schema_variables ?S"
  let ?cv = "finite_pattern_variables (finite_schema_conclusion ?S)"
  let ?g = "Resolution_Material_Goal (?pos@[k]) r M"
  have nd: "nd |\<in>| resolution_nodes st" and linked: "resolution_node_linked P st nd"
    and closed: "finite_children_framed C st nd k"
    using ctx by (simp_all add: finite_framed_parent_context_def)
  have prem_cases: "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
      (finite_pattern_substitute ?\<beta> p) |\<in>| resolution_pending st \<or>
      (resolution_pending_under st (?pos@[s]) = {||} \<and> finite_pattern_variables (finite_pattern_substitute ?\<beta> p) = {||})"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using closed that unfolding finite_children_framed_def by auto
  have mat_cases: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
      (finite_material_pattern_substitute ?\<beta> N) |\<in>| resolution_pending st \<or>
      resolution_pending_under st (?pos@[s]) = {||}"
    if "(s,N) |\<in>| finite_schema_materials ?S" for s N
    using closed that unfolding finite_children_framed_def by auto
  have schema_formed: "schema_formed (decode_finite_schema ?S)" by (rule finite_linked_schema_formed[OF I linked])
  have inst_child: "(\<exists>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<and>
        h = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute ?\<beta> p)) \<or>
      (\<exists>s N. (s,N) |\<in>| finite_schema_materials ?S \<and>
        h = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute ?\<beta> N))"
    if "h |\<in>| resolution_pending st" "resolution_goal_position h \<noteq> []" "butlast (resolution_goal_position h) = ?pos" for h
  proof -
    have "fBex (finite_schema_premises ?S) (\<lambda>(s,e,p). h = Resolution_Call_Goal (?pos@[s])
          (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute ?\<beta> p)) \<or>
        fBex (finite_schema_materials ?S) (\<lambda>(s,N). h = Resolution_Material_Goal (?pos@[s])
          (resolution_node_site nd,resolution_node_clause nd,s) (finite_material_pattern_substitute ?\<beta> N))"
      using closed that unfolding finite_children_framed_def by blast
    then show ?thesis
    proof
      assume "fBex (finite_schema_premises ?S) (\<lambda>(s,e,p). h = Resolution_Call_Goal (?pos@[s])
          (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute ?\<beta> p))"
      then obtain z where z: "z |\<in>| finite_schema_premises ?S" "case z of (s,e,p) \<Rightarrow> h = Resolution_Call_Goal (?pos@[s])
          (Some (resolution_node_site nd,resolution_node_clause nd,s)) e (finite_pattern_substitute ?\<beta> p)" by blast
      obtain s e p where zs: "z = (s,e,p)" by (cases z)
      show ?thesis using z unfolding zs by auto
    next
      assume "fBex (finite_schema_materials ?S) (\<lambda>(s,N). h = Resolution_Material_Goal (?pos@[s])
          (resolution_node_site nd,resolution_node_clause nd,s) (finite_material_pattern_substitute ?\<beta> N))"
      then obtain z where z: "z |\<in>| finite_schema_materials ?S" "case z of (s,N) \<Rightarrow> h = Resolution_Material_Goal (?pos@[s])
          (resolution_node_site nd,resolution_node_clause nd,s) (finite_material_pattern_substitute ?\<beta> N)" by blast
      obtain s N where zs: "z = (s,N)" by (cases z)
      show ?thesis using z unfolding zs by auto
    qed
  qed
  have foc: "h |\<in>| finite_focus_pending F st" if "h |\<in>| resolution_pending st" "resolution_goal_position h = ?pos @ [s]" for h s
    using that by (simp add: finite_focus_pending_focused resolution_focused_child[OF focus])
  define ev where "ev = (\<lambda>a. decode_finite_term (resolution_value \<theta> (?\<beta> a)))"
  define hA where "hA = (\<lambda>a. if term_formed (ev a) then ev a else Payload_Term [])"
  have evsub: "decode_finite_term (resolution_value \<theta>' (finite_pattern_substitute ?\<beta> p)) =
      evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta>' (?\<beta> a))) (decode_finite_pattern p)" for \<theta>' p
    by (simp add: resolution_value_composes decode_resolution_value)
  have matsub: "finite_material_ground_satisfied
      (finite_material_pattern_substitute (resolution_substitution \<theta>') (finite_material_pattern_substitute ?\<beta> N) ::
        ('s,'a) resolution_variable finite_material_pattern) \<longleftrightarrow>
    evaluate_material_satisfaction (\<lambda>a. decode_finite_term (resolution_value \<theta>' (?\<beta> a))) (decode_finite_material N)" for \<theta>' N
    by (simp add: finite_material_ground_value resolution_value_composes finite_material_observation_correct
      decode_resolution_value decode_finite_material_def)
  have evhA: "evaluate_pattern hA p = evaluate_pattern ev p" if "term_formed (evaluate_pattern ev p)" for p
    by (rule evaluate_pattern_cong) (use evaluate_pattern_variables_formed[OF that] in \<open>simp add: hA_def\<close>)
  have call_formed: "term_formed t" if "(e,t) \<in> ?Mn" for e t
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  have mat_vars_formed: "term_formed (f b)"
    if s: "evaluate_material_satisfaction f (decode_finite_material N)" and b: "b |\<in>| finite_material_variables N" for f N b
  proof -
    have fm: "term_formed (evaluate_pattern f (decode_finite_pattern (finite_material_source N)))"
      "term_formed (evaluate_pattern f (decode_finite_pattern (finite_material_atoms N)))"
      "term_formed (evaluate_pattern f (decode_finite_pattern (finite_material_edges N)))"
      "term_formed (evaluate_pattern f (decode_finite_pattern (finite_material_counts N)))"
      "term_formed (evaluate_pattern f (decode_finite_pattern (finite_material_functions N)))"
      using material_observation_formed[OF s] by (simp_all add: decode_finite_material_def)
    from b have "b \<in> pattern_variables (decode_finite_pattern (finite_material_source N)) \<or>
        b \<in> pattern_variables (decode_finite_pattern (finite_material_atoms N)) \<or>
        b \<in> pattern_variables (decode_finite_pattern (finite_material_edges N)) \<or>
        b \<in> pattern_variables (decode_finite_pattern (finite_material_counts N)) \<or>
        b \<in> pattern_variables (decode_finite_pattern (finite_material_functions N))"
      by (auto simp: finite_material_variables_def finite_pattern_variables_correct[symmetric])
    then show ?thesis using evaluate_pattern_variables_formed[OF fm(1)] evaluate_pattern_variables_formed[OF fm(2)]
      evaluate_pattern_variables_formed[OF fm(3)] evaluate_pattern_variables_formed[OF fm(4)]
      evaluate_pattern_variables_formed[OF fm(5)] by blast
  qed
  have mat_hA: "evaluate_material_satisfaction hA (decode_finite_material N)"
    if s: "evaluate_material_satisfaction ev (decode_finite_material N)" for N
  proof -
    have fm: "term_formed (evaluate_pattern ev (decode_finite_pattern (finite_material_source N)))"
      "term_formed (evaluate_pattern ev (decode_finite_pattern (finite_material_atoms N)))"
      "term_formed (evaluate_pattern ev (decode_finite_pattern (finite_material_edges N)))"
      "term_formed (evaluate_pattern ev (decode_finite_pattern (finite_material_counts N)))"
      "term_formed (evaluate_pattern ev (decode_finite_pattern (finite_material_functions N)))"
      using material_observation_formed[OF s] by (simp_all add: decode_finite_material_def)
    show ?thesis using s evhA[OF fm(1)] evhA[OF fm(2)] evhA[OF fm(3)] evhA[OF fm(4)] evhA[OF fm(5)]
      by (simp add: decode_finite_material_def)
  qed
  have clause_hA: "clause_true ?Mn (decode_finite_schema ?S) hA"
    unfolding clause_true_def
  proof (intro conjI allI impI ballI)
    fix a show "term_formed (hA a)" by (simp add: hA_def octets_formed_def)
  next
    fix s d p assume sp: "(s,d,p) \<in> schema_premises (decode_finite_schema ?S)"
    obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises ?S" and pp: "p = decode_finite_pattern p0"
      using sp by (auto simp: decode_finite_call_pattern_def)
    have "(d,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute ?\<beta> p0))) \<in> ?Mn"
    proof (cases "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) d
        (finite_pattern_substitute ?\<beta> p0) |\<in>| resolution_pending st")
      case True
      have "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) d
          (finite_pattern_substitute ?\<beta> p0) |\<in>| finite_focus_pending F st"
        by (rule foc[OF True]) simp
      then show ?thesis using holds by (fastforce simp: finite_goal_holds_def)
    next
      case False
      then have cl: "resolution_pending_under st (?pos@[s]) = {||}"
        "finite_pattern_variables (finite_pattern_substitute ?\<beta> p0) = {||}"
        using prem_cases[OF p0] by blast+
      show ?thesis by (rule finite_closed_premise_true(1)[OF I nd cl(1) p0 cl(2)])
    qed
    then have t: "(d,evaluate_pattern ev (decode_finite_pattern p0)) \<in> ?Mn" unfolding evsub ev_def .
    show "(d,evaluate_pattern hA p) \<in> ?Mn" using t evhA[OF call_formed[OF t]] pp by simp
  next
    fix s N assume sN: "(s,N) \<in> schema_material_premises (decode_finite_schema ?S)"
    obtain N1 where N1: "(s,N1) |\<in>| finite_schema_materials ?S" and NN: "N = decode_finite_material N1"
      using sN by auto
    have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute ?\<beta> N1))"
    proof (cases "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
        (finite_material_pattern_substitute ?\<beta> N1) |\<in>| resolution_pending st")
      case True
      have "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute ?\<beta> N1) |\<in>| finite_focus_pending F st"
        by (rule foc[OF True]) simp
      then show ?thesis using holds by (fastforce simp: finite_goal_holds_def)
    next
      case False
      then have cl: "resolution_pending_under st (?pos@[s]) = {||}" using mat_cases[OF N1] by blast
      show ?thesis by (rule finite_closed_premise_true(2)[OF I nd cl N1])
    qed
    then have "evaluate_material_satisfaction ev (decode_finite_material N1)" unfolding matsub ev_def .
    then show "evaluate_material_satisfaction hA N" unfolding NN by (rule mat_hA)
  qed
  obtain w1 w2 w3 w4 where w: "finite_material_atoms M = Finite_Variable w1" "finite_material_edges M = Finite_Variable w2"
      "finite_material_counts M = Finite_Variable w3" "finite_material_functions M = Finite_Variable w4"
    and wd: "distinct [w1,w2,w3,w4]"
    by (rule finite_free_fields_variables[OF free])
  obtain x1 where x1: "finite_material_atoms N0 = Finite_Variable x1" "?\<beta> x1 = Finite_Variable w1"
    using finite_pattern_substitute_variable_eq[of ?\<beta> "finite_material_atoms N0" w1] w(1) M by auto
  obtain x2 where x2: "finite_material_edges N0 = Finite_Variable x2" "?\<beta> x2 = Finite_Variable w2"
    using finite_pattern_substitute_variable_eq[of ?\<beta> "finite_material_edges N0" w2] w(2) M by auto
  obtain x3 where x3: "finite_material_counts N0 = Finite_Variable x3" "?\<beta> x3 = Finite_Variable w3"
    using finite_pattern_substitute_variable_eq[of ?\<beta> "finite_material_counts N0" w3] w(3) M by auto
  obtain x4 where x4: "finite_material_functions N0 = Finite_Variable x4" "?\<beta> x4 = Finite_Variable w4"
    using finite_pattern_substitute_variable_eq[of ?\<beta> "finite_material_functions N0" w4] w(4) M by auto
  have xd: "distinct [x1,x2,x3,x4]" using wd x1(2) x2(2) x3(2) x4(2) by auto
  have matv: "a |\<in>| ?SV" if "a |\<in>| finite_material_variables N0" for a
    using N0 that by (force simp: finite_schema_variables_def resolution_fset_simps)
  have xmv: "x1 |\<in>| finite_material_variables N0" "x2 |\<in>| finite_material_variables N0"
    "x3 |\<in>| finite_material_variables N0" "x4 |\<in>| finite_material_variables N0"
    using x1(1) x2(1) x3(1) x4(1) by (simp_all add: finite_material_variables_def)
  have src: "finite_pattern_substitute ?\<beta> (finite_material_source N0) = Finite_Pattern_Target (Finite_Whole R)"
    using source M by simp
  have srcx: "a |\<notin>| finite_pattern_variables (finite_material_source N0)" if "?\<beta> a = Finite_Variable wa" for a wa
  proof
    assume "a |\<in>| finite_pattern_variables (finite_material_source N0)"
    from finite_substitute_variables_subset[OF this, of ?\<beta>] show False using that src by simp
  qed
  have gF: "?g |\<in>| finite_focus_pending F st" by (rule foc[OF g]) simp
  have gsat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    using holds[OF gF] by (simp add: finite_goal_holds_def)
  have gev: "evaluate_material_satisfaction ev (decode_finite_material N0)" using gsat unfolding M matsub ev_def .
  have Rf: "finite_exact_formed R" by (rule finite_material_source_formed[OF gsat source])
  obtain A E Bs Fs where rows: "finite_artifact_rows R = (A,E,Bs,Fs)" by (cases "finite_artifact_rows R") auto
  let ?a0 = "finite_enumeration_term (map (finite_atom_term R) A)"
  let ?e0 = "finite_enumeration_term (map (finite_incidence_term R) E)"
  let ?b0 = "finite_enumeration_term (map (finite_attachment_term R) Bs)"
  let ?f0 = "finite_enumeration_term (map (finite_attachment_term R) Fs)"
  have canon: "finite_material_observation (Finite_Target (Finite_Whole R)) ?a0 ?e0 ?b0 ?f0"
    by (rule finite_canonical_observation[OF Rf rows])
  define gm where "gm = hA(x1 := decode_finite_term ?a0, x2 := decode_finite_term ?e0, x3 := decode_finite_term ?b0,
      x4 := decode_finite_term ?f0)"
  have gm_x: "gm x1 = decode_finite_term ?a0" "gm x2 = decode_finite_term ?e0" "gm x3 = decode_finite_term ?b0"
      "gm x4 = decode_finite_term ?f0"
    using xd by (simp_all add: gm_def)
  have gm_src: "evaluate_pattern gm (decode_finite_pattern (finite_material_source N0)) =
      evaluate_pattern hA (decode_finite_pattern (finite_material_source N0))"
    by (rule evaluate_pattern_cong)
      (use srcx[OF x1(2)] srcx[OF x2(2)] srcx[OF x3(2)] srcx[OF x4(2)] in
        \<open>auto simp: gm_def finite_pattern_variables_correct[symmetric]\<close>)
  have ev_src: "evaluate_pattern ev (decode_finite_pattern (finite_material_source N0)) =
      decode_finite_term (Finite_Target (Finite_Whole R))"
    using evsub[of \<theta> "finite_material_source N0"] src by (simp add: ev_def resolution_value_target)
  have src_formed: "term_formed (decode_finite_term (Finite_Target (Finite_Whole R)))"
    using Rf finite_term_formed_correct[of "Finite_Target (Finite_Whole R)"] by simp
  have hA_src: "evaluate_pattern hA (decode_finite_pattern (finite_material_source N0)) =
      decode_finite_term (Finite_Target (Finite_Whole R))"
    using evhA[of "decode_finite_pattern (finite_material_source N0)"] ev_src src_formed by simp
  have gm_sat: "evaluate_material_satisfaction gm (decode_finite_material N0)"
    using canon[unfolded finite_material_observation_correct] gm_src hA_src gm_x x1(1) x2(1) x3(1) x4(1)
    by (simp add: decode_finite_material_def)
  have same_src: "evaluate_pattern gm (material_source (decode_finite_material N0)) =
      evaluate_pattern hA (material_source (decode_finite_material N0))"
    using gm_src by (simp add: decode_finite_material_def)
  have N0d: "(k,decode_finite_material N0) \<in> schema_material_premises (decode_finite_schema ?S)" using N0 by auto
  obtain hN where clN: "clause_true ?Mn (decode_finite_schema ?S) hN"
    and hk: "head_kept keep Vh ?S hA hN"
    and frN: "\<forall>a\<in>schema_variables (decode_finite_schema ?S) - fset C. hN a = hA a"
    and agN: "\<forall>a\<in>material_variables (decode_finite_material N0). hN a = gm a"
    using conjunct2[OF mp[OF spec[OF conjunct2[OF socket[unfolded socket_framed_def]], of hA] clause_hA],
      rule_format, OF N0d gm_sat same_src] by blast
  have hN_x: "hN x1 = decode_finite_term ?a0" "hN x2 = decode_finite_term ?e0" "hN x3 = decode_finite_term ?b0"
      "hN x4 = decode_finite_term ?f0"
    using agN gm_x xmv finite_material_variables_correct[of N0] by auto
  have hN_formed: "term_formed (hN a)" if "a |\<in>| ?SV" for a
    using clN that finite_schema_variables_correct[of ?S] unfolding clause_true_def by auto
  have frameN: "hN a = hA a" if "a |\<in>| ?SV" "a |\<notin>| C" for a
  proof -
    have "a \<in> schema_variables (decode_finite_schema ?S) - fset C"
      using that by (simp add: finite_schema_variables_correct[symmetric])
    then show ?thesis using frN by blast
  qed
  define \<theta>2 where "\<theta>2 = \<theta>(w1 := ?a0, w2 := ?e0, w3 := ?b0, w4 := ?f0)"
  have own: "finite_socket_own Vp ?S k |\<subseteq>| finite_material_variables N0"
    by (rule finite_socket_own_material[OF schema_formed N0])
  have OS: "finite_material_variables N0 |\<subseteq>| ?SV" by (rule fsubsetI) (rule matv)
  have old_O: "hA c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if c: "c |\<in>| finite_material_variables N0" for c
    using mat_vars_formed[OF gev c] by (simp add: hA_def ev_def)
  have new_O: "hN c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))" if c: "c |\<in>| finite_material_variables N0" for c
  proof (cases "c \<in> {x1,x2,x3,x4}")
    case True
    then show ?thesis using hN_x x1(2) x2(2) x3(2) x4(2) wd by (auto simp: \<theta>2_def resolution_value_def)
  next
    case False
    have cs: "c |\<in>| finite_pattern_variables (finite_material_source N0)"
      using c False x1(1) x2(1) x3(1) x4(1) by (auto simp: finite_material_variables_def)
    have gr: "finite_pattern_variables (?\<beta> c) = {||}"
      using finite_substitute_variables_subset[OF cs, of ?\<beta>] src by simp
    have v: "resolution_value \<theta> (?\<beta> c) = resolution_value \<theta>2 (?\<beta> c)"
      by (rule resolution_value_cong) (simp add: gr)
    have "hN c = gm c" using agN c finite_material_variables_correct[of N0] by auto
    moreover have "gm c = hA c" using False by (simp add: gm_def)
    ultimately show ?thesis using old_O[OF c] v by simp
  qed
  have Yiff: "z |\<in>| finite_material_variables M \<longleftrightarrow>
      (\<exists>c. c |\<in>| finite_material_variables N0 \<and> z |\<in>| finite_pattern_variables (?\<beta> c))" for z
    unfolding M by (rule finite_material_substitute_variables)
  have headc: "(keep \<and> head_kept True Vh ?S hA hN) \<or>
      (\<not> keep \<and> head_kept False Vh ?S hA hN \<and> finite_parent_absorbs Vp Vh C nd k \<and> finite_input_output_apart Vh nd)"
    using head hk by (cases keep) auto
  obtain \<theta>1 where t1: "\<And>z. z |\<in>| finite_material_variables M \<Longrightarrow> \<theta>1 z = \<theta>2 z"
    and t2: "\<And>z. z |\<notin>| finite_material_variables M \<Longrightarrow> \<not> finite_free_premise_variable st nd z \<Longrightarrow>
      keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C nd k \<Longrightarrow> \<theta>1 z = \<theta> z"
    and t3: "\<And>c. c |\<in>| ?SV \<Longrightarrow> hA c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<or>
        (c |\<notin>| ?cv \<and> finite_free_premise_only st nd c) \<Longrightarrow>
      decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = hN c"
    by (rule finite_framed_valuation[where h=hA and h'=hN and \<theta>=\<theta> and ?\<theta>2.0=\<theta>2 and
      Y="fset (finite_material_variables M)" and Ow="finite_material_variables N0",
      OF I ctx Vh own OS old_O new_O Yiff frameN headc hN_formed]) (assumption | rule that)+
  have wM: "w1 |\<in>| finite_material_variables M" "w2 |\<in>| finite_material_variables M"
    "w3 |\<in>| finite_material_variables M" "w4 |\<in>| finite_material_variables M"
    using w by (simp_all add: finite_material_variables_def)
  have fv: "resolution_value \<theta>1 (finite_material_atoms M) = ?a0" "resolution_value \<theta>1 (finite_material_edges M) = ?e0"
      "resolution_value \<theta>1 (finite_material_counts M) = ?b0" "resolution_value \<theta>1 (finite_material_functions M) = ?f0"
      "resolution_value \<theta>1 (finite_material_source M) = Finite_Target (Finite_Whole R)"
    using t1[OF wM(1)] t1[OF wM(2)] t1[OF wM(3)] t1[OF wM(4)] w wd source
    by (simp_all add: \<theta>2_def resolution_value_def resolution_value_target)
  have tuple: "(resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R)"
    using fv rows by simp
  have ground1: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M)"
    unfolding finite_material_ground_value using canon fv by simp
  have eq_on: "evaluate_pattern (\<lambda>b. decode_finite_term (resolution_value \<theta>1 (?\<beta> b))) (decode_finite_pattern p) =
      evaluate_pattern hN (decode_finite_pattern p)"
    if pv: "\<And>b. b |\<in>| finite_pattern_variables p \<Longrightarrow> b |\<in>| ?SV \<and> term_formed (ev b)" for p
  proof (rule evaluate_pattern_cong)
    fix b assume "b \<in> pattern_variables (decode_finite_pattern p)"
    then have b: "b |\<in>| finite_pattern_variables p" by (simp add: finite_pattern_variables_correct[symmetric])
    have "hA b = decode_finite_term (resolution_value \<theta> (?\<beta> b))" using pv[OF b] by (simp add: hA_def ev_def)
    then show "decode_finite_term (resolution_value \<theta>1 (?\<beta> b)) = hN b" using t3 pv[OF b] by blast
  qed
  have others: "finite_goal_holds ?Mn \<theta>1 h" if h: "h |\<in>| finite_focus_pending F st" "h \<noteq> ?g" for h
  proof (cases "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos")
    case True
    have hp: "h |\<in>| resolution_pending st" using h(1) by (simp add: finite_focus_pending_focused)
    from inst_child[OF hp conjunct1[OF True] conjunct2[OF True]] show ?thesis
    proof (elim disjE exE conjE)
      fix s e p assume p: "(s,e,p) |\<in>| finite_schema_premises ?S"
        and he: "h = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute ?\<beta> p)"
      have "(e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute ?\<beta> p))) \<in> ?Mn"
        using holds[OF h(1)] he by (simp add: finite_goal_holds_def)
      then have t\<theta>: "(e,evaluate_pattern ev (decode_finite_pattern p)) \<in> ?Mn" unfolding evsub ev_def .
      have pv: "b |\<in>| ?SV \<and> term_formed (ev b)" if "b |\<in>| finite_pattern_variables p" for b
      proof
        show "b |\<in>| ?SV" using p that by (force simp: finite_schema_variables_def resolution_fset_simps)
        show "term_formed (ev b)"
          using evaluate_pattern_variables_formed[OF call_formed[OF t\<theta>]] that
          by (simp add: finite_pattern_variables_correct[symmetric])
      qed
      have tN: "(e,evaluate_pattern hN (decode_finite_pattern p)) \<in> ?Mn"
        using clN p unfolding clause_true_def by (force simp: decode_finite_call_pattern_def)
      show ?thesis using tN he evsub[of \<theta>1 p] eq_on[OF pv] by (simp add: finite_goal_holds_def)
    next
      fix s N1 assume N1: "(s,N1) |\<in>| finite_schema_materials ?S"
        and he: "h = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute ?\<beta> N1)"
      have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
          (finite_material_pattern_substitute ?\<beta> N1))"
        using holds[OF h(1)] he by (simp add: finite_goal_holds_def)
      then have s\<theta>: "evaluate_material_satisfaction ev (decode_finite_material N1)" unfolding matsub ev_def .
      have mv: "b |\<in>| ?SV \<and> term_formed (ev b)" if "b |\<in>| finite_material_variables N1" for b
      proof
        show "b |\<in>| ?SV" using N1 that by (force simp: finite_schema_variables_def resolution_fset_simps)
        show "term_formed (ev b)" by (rule mat_vars_formed[OF s\<theta> that])
      qed
      have sN: "evaluate_material_satisfaction hN (decode_finite_material N1)"
        using clN N1 unfolding clause_true_def by force
      have fields: "evaluate_pattern (\<lambda>b. decode_finite_term (resolution_value \<theta>1 (?\<beta> b))) (decode_finite_pattern f) =
          evaluate_pattern hN (decode_finite_pattern f)"
        if "finite_pattern_variables f |\<subseteq>| finite_material_variables N1" for f
        by (rule eq_on) (use mv that in \<open>meson fsubsetD\<close>)
      have sub: "finite_pattern_variables (finite_material_source N1) |\<subseteq>| finite_material_variables N1"
          "finite_pattern_variables (finite_material_atoms N1) |\<subseteq>| finite_material_variables N1"
          "finite_pattern_variables (finite_material_edges N1) |\<subseteq>| finite_material_variables N1"
          "finite_pattern_variables (finite_material_counts N1) |\<subseteq>| finite_material_variables N1"
          "finite_pattern_variables (finite_material_functions N1) |\<subseteq>| finite_material_variables N1"
        by (rule fsubsetI, simp add: finite_material_variables_def)+
      have "evaluate_material_satisfaction (\<lambda>b. decode_finite_term (resolution_value \<theta>1 (?\<beta> b))) (decode_finite_material N1)"
        using sN fields[OF sub(1)] fields[OF sub(2)] fields[OF sub(3)] fields[OF sub(4)] fields[OF sub(5)]
        by (simp add: decode_finite_material_def)
      then show ?thesis using he matsub[of \<theta>1 N1] by (simp add: finite_goal_holds_def)
    qed
  next
    case nch: False
    have h\<theta>: "finite_goal_holds ?Mn \<theta> h" by (rule holds[OF h(1)])
    have hp: "h |\<in>| resolution_pending st" using h(1) by (simp add: finite_focus_pending_focused)
    have child_of: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos"
      if f: "finite_free_premise_only st nd a" and za: "((?pos,True),a) |\<in>| resolution_goal_variables h" for a
      using f hp za unfolding finite_free_premise_only_def by blast
    have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| resolution_goal_variables h" for z
    proof (cases "z |\<in>| finite_material_variables M")
      case zY: True
      then obtain c where c: "c |\<in>| finite_material_variables N0" "z |\<in>| finite_pattern_variables (?\<beta> c)"
        using Yiff by blast
      have cS: "c |\<in>| ?SV" by (rule matv[OF c(1)])
      have t: "\<theta>1 z = \<theta>2 z" by (rule t1[OF zY])
      have unch: "\<theta>2 z = \<theta> z" if e: "hN c = hA c"
      proof -
        have "resolution_value \<theta>2 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)"
          using new_O[OF c(1)] old_O[OF c(1)] e by simp
        then show ?thesis by (rule resolution_value_agree) (rule c(2))
      qed
      show ?thesis
      proof (cases "c |\<in>| ?cv")
        case cv: True
        show ?thesis
        proof (cases keep)
          case True
          have hkT: "head_kept True Vh ?S hA hN" using hk True by simp
          show ?thesis using t unch[OF head_kept_variables[OF hkT Vh cv]] by simp
        next
          case nk: False
          obtain hi ho where vh: "resolution_view_pattern Vh (finite_schema_conclusion ?S) = Some (hi,ho)"
            using head nk by (auto simp: finite_parent_absorbs_def split: option.splits)
          have cvs: "?cv = finite_pattern_variables hi |\<union>| finite_pattern_variables ho"
            by (rule resolution_view_pattern_variables[OF Vh vh])
          show ?thesis
          proof (cases "c |\<in>| finite_pattern_variables hi")
            case True
            have "hN c = hA c"
              by (rule evaluate_pattern_agree[OF head_kept_input[OF hk vh]])
                (simp add: True finite_pattern_variables_correct[symmetric])
            then show ?thesis using t unch by simp
          next
            case False
            have cho: "c |\<in>| finite_pattern_variables ho" using cv False cvs by simp
            show ?thesis
            proof (cases "c |\<in>| C")
              case True
              have "z |\<notin>| resolution_goal_variables h" by (rule outside[OF h(1) nch nk vh cho True c(2)])
              then show ?thesis using z by simp
            next
              case False
              have "hN c = hA c" by (rule frameN[OF cS False])
              then show ?thesis using t unch by simp
            qed
          qed
        qed
      next
        case ncv: False
        have f: "finite_free_premise_only st nd c"
          using finite_framed_premise_only[OF I ctx cS ncv] c(2) by auto
        have "z = ((?pos,True),c)" using f c(2) unfolding finite_free_premise_only_def by auto
        then have "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos"
          using child_of[OF f] z by simp
        then show ?thesis using nch by blast
      qed
    next
      case zY: False
      show ?thesis
      proof (rule t2[OF zY])
        show "\<not> finite_free_premise_variable st nd z"
        proof
          assume fv: "finite_free_premise_variable st nd z"
          have f: "finite_free_premise_only st nd (snd z)" and z1: "fst z = (?pos,True)"
            using fv by (simp_all add: finite_free_premise_variable_def)
          have zz: "((?pos,True),snd z) |\<in>| resolution_goal_variables h" using z z1 by (metis prod.collapse)
          show False using child_of[OF f zz] nch by blast
        qed
        show "keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C nd k"
        proof (cases keep)
          case nk: False
          obtain hi ho where vh: "resolution_view_pattern Vh (finite_schema_conclusion ?S) = Some (hi,ho)"
            using head nk by (auto simp: finite_parent_absorbs_def split: option.splits)
          have "z |\<notin>| finite_parent_absorbed Vp Vh C nd k"
          proof
            assume "z |\<in>| finite_parent_absorbed Vp Vh C nd k"
            then obtain b where b: "b |\<in>| finite_pattern_variables ho" "b |\<in>| C" "z |\<in>| finite_pattern_variables (?\<beta> b)"
              using finite_parent_absorbed_iff[OF vh] by blast
            have "z |\<notin>| resolution_goal_variables h" by (rule outside[OF h(1) nch nk vh b])
            then show False using z by simp
          qed
          then show ?thesis by blast
        qed simp
      qed
    qed
    show ?thesis using h\<theta> finite_goal_holds_cong[of h \<theta>1 \<theta>] same by blast
  qed
  show ?thesis using tuple ground1 others by blast
qed

text \<open>Today's valuation is the framed one's instance at the socket's default frame, the variant test giving (iii).\<close>

lemma finite_material_socket_valuation:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st"
    and ctx: "finite_parent_context P Vp Vh st nd k"
    and N0: "(k,N0) |\<in>| finite_schema_materials (resolution_node_schema nd)"
    and g: "Resolution_Material_Goal (resolution_node_position nd@[k]) r M |\<in>| resolution_pending st"
    and M: "M = finite_material_pattern_substitute (finite_node_binding nd) N0"
    and focus: "resolution_focused F (resolution_node_position nd)"
    and holds: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    and socket: "socket_discharged (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) k keep Vp Vh"
    and Vh: "view_formed Vh"
    and head: "keep \<or> (\<exists>hi ho x out.
        resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho) \<and>
        resolution_view_pattern Vh (resolution_node_call nd) = Some (x,out) \<and> finite_variant ho out \<and>
        finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||} \<and> OUT = fset (finite_pattern_variables out))"
    and kept_out: "keep \<Longrightarrow> OUT = {}"
    and outside: "\<And>h z. h |\<in>| finite_focus_pending F st \<Longrightarrow>
        \<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position nd) \<Longrightarrow>
        z \<in> OUT \<Longrightarrow> z |\<notin>| resolution_goal_variables h"
    and free: "finite_free_fields M"
    and source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
  shows "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C) \<and>
    finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> Resolution_Material_Goal (resolution_node_position nd@[k]) r M \<longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h)"
proof -
  have nd: "nd |\<in>| resolution_nodes st" and linked: "resolution_node_linked P st nd"
    using ctx by (simp_all add: finite_parent_context_def)
  have formed: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  let ?C = "finite_default_frame Vp Vh (resolution_node_schema nd) k"
  have ctxF: "finite_framed_parent_context P ?C st nd k" by (rule finite_parent_context_framed[OF ctx])
  have sockF: "socket_framed (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) k keep Vp Vh (fset ?C)"
    unfolding finite_default_frame_correct by (rule socket_discharged_framed[OF socket formed])
  have call: "resolution_node_call nd =
      finite_pattern_substitute (finite_node_binding nd) (finite_schema_conclusion (resolution_node_schema nd))"
    by (rule finite_node_binding_linked(2)[OF I nd])
  have headF: "keep \<or> (finite_parent_absorbs Vp Vh ?C nd k \<and> finite_input_output_apart Vh nd)"
  proof (cases keep)
    case False
    then obtain hi ho x out where hd: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) =
        Some (hi,ho)"
      and cl: "resolution_view_pattern Vh (resolution_node_call nd) = Some (x,out)" and var: "finite_variant ho out"
      and ap: "finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||}"
      using head by blast
    have xo: "out = finite_pattern_substitute (finite_node_binding nd) ho"
      using resolution_view_pattern_substitute[OF hd, of "finite_node_binding nd"] cl call by simp
    have "finite_parent_absorbs Vp Vh ?C nd k" by (rule finite_variant_absorbs(1)[OF hd]) (use var xo in simp)
    moreover have "finite_input_output_apart Vh nd" using cl ap by (simp add: finite_input_output_apart_def)
    ultimately show ?thesis by blast
  qed simp
  have outF: "z |\<notin>| resolution_goal_variables h"
    if h: "h |\<in>| finite_focus_pending F st"
      and nc: "\<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position nd)"
      and nk: "\<not> keep" and vh: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho)"
      and b: "b |\<in>| finite_pattern_variables ho" "b |\<in>| ?C"
      and z: "z |\<in>| finite_pattern_variables (finite_node_binding nd b)"
    for h z b hi ho
  proof -
    obtain hi' ho' x out where hd: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) =
        Some (hi',ho')"
      and cl: "resolution_view_pattern Vh (resolution_node_call nd) = Some (x,out)"
      and OUTe: "OUT = fset (finite_pattern_variables out)"
      using head nk by blast
    have hh: "ho' = ho" using hd vh by simp
    have xo: "out = finite_pattern_substitute (finite_node_binding nd) ho'"
      using resolution_view_pattern_substitute[OF hd, of "finite_node_binding nd"] cl call by simp
    have "z |\<in>| finite_pattern_variables out"
      using finite_pattern_substitute_variable_holds[of b ho' z "finite_node_binding nd"] b(1) z hh xo by simp
    then have "z \<in> OUT" using OUTe by simp
    then show ?thesis by (rule outside[OF h nc])
  qed
  show ?thesis by (rule finite_framed_material_valuation[OF I ctxF N0 g M focus holds sockF Vh headF outF free source])
qed

subsection \<open>The exchange at a material socket\<close>

text \<open>
  Where the focus holds the parent's children, the socket's obligation gives the valuation; where it does not, the focus
  holds no child but the committed goal, so no focused goal holds a variable of the socket and the canonical answer
  simply replaces the support there. Either valuation supports a canonical successor with every node barred.
\<close>

lemma finite_framed_material_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Material_Goal q r M |\<in>| finite_focus_pending F st"
    and Ws: "finite_canonical_solutions M = Some Ws" and free: "finite_free_fields M"
    and prem: "finite_material_premise st (Resolution_Material_Goal q r M)"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q" and qne: "q \<noteq> []"
    and ctx: "finite_framed_parent_context P C st nd (last q)"
    and socket: "socket_framed (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) (last q) keep Vp Vh
      (fset C)"
    and Vh: "view_formed Vh"
    and hold: "finite_socket_holders F st q Y (Resolution_Material_Goal q r M)"
    and Ysub: "finite_material_variables M |\<subseteq>| Y"
    and head: "keep \<or> (F = Some (butlast q) \<and> finite_parent_absorbs Vp Vh C nd (last q) \<and>
      finite_input_output_apart Vh nd \<and> finite_parent_absorbed Vp Vh C nd (last q) |\<subseteq>| Y)"
  shows "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
    resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  let ?Mn = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Material_Goal q r M"
  let ?pos = "resolution_node_position nd"
  let ?\<beta> = "finite_node_binding nd"
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have linked: "resolution_node_linked P st nd" using ctx by (simp add: finite_framed_parent_context_def)
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  obtain k where qk: "q = ?pos @ [k]" and k: "k = last q" using nd(2) qne by (metis append_butlast_last_id)
  have ctxk: "finite_framed_parent_context P C st nd k" using ctx k by simp
  obtain N0 where N0: "(k,N0) |\<in>| finite_schema_materials (resolution_node_schema nd)"
  proof -
    obtain np where np: "np |\<in>| resolution_nodes st" "resolution_node_position np = butlast q"
        and m: "fBex (finite_schema_materials (resolution_node_schema np)) (\<lambda>z. fst z = last q)"
      using prem qne unfolding finite_material_premise_def by auto
    have "resolution_node_position np = resolution_node_position nd" using np(2) nd(2) by simp
    then have "np = nd" using dist np(1) nd(1) unfolding resolution_positions_distinct_def by blast
    then obtain z where z: "z |\<in>| finite_schema_materials (resolution_node_schema nd)" "fst z = k" using m k by blast
    show thesis by (rule that[of "snd z"]) (use z in \<open>metis prod.collapse\<close>)
  qed
  have inst_g: "Resolution_Material_Goal (?pos@[k]) (resolution_node_site nd,resolution_node_clause nd,k)
      (finite_material_pattern_substitute ?\<beta> N0) |\<in>| resolution_pending st"
    using ctxk N0 unfolding finite_framed_parent_context_def finite_children_framed_def by auto
  have gq: "Resolution_Material_Goal (?pos@[k]) r M |\<in>| resolution_pending st" using gp by (simp only: qk[symmetric])
  have "resolution_goal_position (Resolution_Material_Goal (?pos@[k]) r M) =
      resolution_goal_position (Resolution_Material_Goal (?pos@[k]) (resolution_node_site nd,resolution_node_clause nd,k)
        (finite_material_pattern_substitute ?\<beta> N0))" by simp
  then have "Resolution_Material_Goal (?pos@[k]) r M = Resolution_Material_Goal (?pos@[k])
      (resolution_node_site nd,resolution_node_clause nd,k) (finite_material_pattern_substitute ?\<beta> N0)"
    using dist gq inst_g unfolding resolution_positions_distinct_def by blast
  then have Meq: "M = finite_material_pattern_substitute ?\<beta> N0" by simp
  obtain R where source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole R)"
    using Ws by (auto simp: finite_canonical_solutions_def
      split: finite_term_pattern.splits finite_exact_target.splits if_splits)
  have placed: "finite_state_placed U st" by (rule resolution_supported_at_placed[OF sup])
  have holds\<theta>: "finite_goal_holds ?Mn \<theta> h" if "h |\<in>| finite_focus_pending F st" for h
    by (rule resolution_supported_at_holds[OF sup that])
  have hold_g: "resolution_goal_variables h |\<inter>| Y = {||} \<or>
      (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos)"
    if "h |\<in>| finite_focus_pending F st" "h \<noteq> ?g" for h
    using hold that nd(2) unfolding finite_socket_holders_def by auto
  have gsat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    using holds\<theta>[OF gF] by (simp add: finite_goal_holds_def)
  have formedS: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  have own_sub: "finite_socket_own Vp (resolution_node_schema nd) k |\<subseteq>| finite_material_variables N0"
    by (rule finite_socket_own_material[OF formedS N0])
  have "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R) \<and>
    finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> ?g \<longrightarrow> finite_goal_holds ?Mn \<theta>1 h)"
  proof (cases "resolution_focused F ?pos")
    case True
    have headv: "keep \<or> (finite_parent_absorbs Vp Vh C nd k \<and> finite_input_output_apart Vh nd)"
      using head[folded k] by blast
    have outside: "z |\<notin>| resolution_goal_variables h"
      if h: "h |\<in>| finite_focus_pending F st"
        and nc: "\<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos)"
        and nk: "\<not> keep"
        and vh: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho)"
        and b: "b |\<in>| finite_pattern_variables ho" "b |\<in>| C" and z: "z |\<in>| finite_pattern_variables (?\<beta> b)"
      for h z b hi ho
    proof -
      have hg: "h \<noteq> ?g" using nc qk by auto
      have dis: "resolution_goal_variables h |\<inter>| Y = {||}" using hold_g[OF h hg] nc by blast
      have zY: "z |\<in>| Y"
      proof (cases "b |\<in>| finite_socket_own Vp (resolution_node_schema nd) k")
        case True
        have "b |\<in>| finite_material_variables N0" using own_sub True by (meson fsubsetD)
        then have "z |\<in>| finite_material_variables M"
          unfolding Meq finite_material_substitute_variables using z by blast
        then show ?thesis using Ysub by (meson fsubsetD)
      next
        case False
        have "z |\<in>| finite_parent_absorbed Vp Vh C nd k" unfolding finite_parent_absorbed_iff[OF vh] using b False z by blast
        moreover have "finite_parent_absorbed Vp Vh C nd k |\<subseteq>| Y" using head[folded k] nk by blast
        ultimately show ?thesis by (meson fsubsetD)
      qed
      show ?thesis
      proof
        assume "z |\<in>| resolution_goal_variables h"
        then have "z |\<in>| resolution_goal_variables h |\<inter>| Y" using zY by simp
        then show False using dis by simp
      qed
    qed
    have "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
        resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
        resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R) \<and>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> Resolution_Material_Goal (?pos@[k]) r M \<longrightarrow>
        finite_goal_holds ?Mn \<theta>1 h)"
      by (rule finite_framed_material_valuation[OF I ctxk N0 gq Meq True holds\<theta> socket[unfolded k[symmetric]] Vh headv
        outside free source])
    then show ?thesis unfolding qk by blast
  next
    case nfoc: False
    obtain f where Ff: "F = Some f" using nfoc by (cases F) (simp_all add: resolution_focused_def)
    obtain w1 w2 w3 w4 where w: "finite_material_atoms M = Finite_Variable w1" "finite_material_edges M = Finite_Variable w2"
        "finite_material_counts M = Finite_Variable w3" "finite_material_functions M = Finite_Variable w4"
      and wd: "distinct [w1,w2,w3,w4]"
      by (rule finite_free_fields_variables[OF free])
    have Rf: "finite_exact_formed R" by (rule finite_material_source_formed[OF gsat source])
    obtain A E Bs Fs where rows: "finite_artifact_rows R = (A,E,Bs,Fs)" by (cases "finite_artifact_rows R") auto
    let ?a0 = "finite_enumeration_term (map (finite_atom_term R) A)"
    let ?e0 = "finite_enumeration_term (map (finite_incidence_term R) E)"
    let ?b0 = "finite_enumeration_term (map (finite_attachment_term R) Bs)"
    let ?f0 = "finite_enumeration_term (map (finite_attachment_term R) Fs)"
    have canon: "finite_material_observation (Finite_Target (Finite_Whole R)) ?a0 ?e0 ?b0 ?f0"
      by (rule finite_canonical_observation[OF Rf rows])
    define \<theta>1 where "\<theta>1 = \<theta>(w1 := ?a0, w2 := ?e0, w3 := ?b0, w4 := ?f0)"
    have fv: "resolution_value \<theta>1 (finite_material_atoms M) = ?a0" "resolution_value \<theta>1 (finite_material_edges M) = ?e0"
        "resolution_value \<theta>1 (finite_material_counts M) = ?b0" "resolution_value \<theta>1 (finite_material_functions M) = ?f0"
        "resolution_value \<theta>1 (finite_material_source M) = Finite_Target (Finite_Whole R)"
      using w wd source by (simp_all add: \<theta>1_def resolution_value_def)
    have tuple: "(resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
        resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
        resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R)"
      using fv rows by simp
    have ground1: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M)"
      unfolding finite_material_ground_value using canon fv by simp
    have others: "finite_goal_holds ?Mn \<theta>1 h" if h: "h |\<in>| finite_focus_pending F st" "h \<noteq> ?g" for h
    proof -
      have not_child: "\<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos)"
      proof
        assume c: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos"
        let ?ph = "resolution_goal_position h"
        have th: "take (length f) ?ph = f" using h(1) Ff by (simp add: finite_focus_pending_focused resolution_focused_def)
        have tq: "take (length f) q = f" using gF Ff by (simp add: finite_focus_pending_focused resolution_focused_def)
        have tp: "take (length f) ?pos \<noteq> f" using nfoc Ff by (simp add: resolution_focused_def)
        have ph: "?ph = ?pos @ [last ?ph]" using c by (metis append_butlast_last_id)
        have gt: "length ?pos < length f"
        proof (rule ccontr)
          assume "\<not> length ?pos < length f"
          then have le: "length f \<le> length ?pos" by simp
          have "take (length f) ?ph = take (length f) ?pos" by (subst ph) (simp add: le)
          then show False using th tp by simp
        qed
        have lph: "length ?ph = Suc (length ?pos)" by (subst ph) simp
        have lq: "length q = Suc (length ?pos)" using qk by simp
        have "?ph = f" using th gt lph by (metis Suc_leI take_all)
        moreover have "q = f" using tq gt lq by (metis Suc_leI take_all)
        ultimately have "resolution_goal_position h = resolution_goal_position ?g" by simp
        moreover have "h |\<in>| resolution_pending st" using h(1) by (simp add: finite_focus_pending_focused)
        ultimately have "h = ?g" using dist gp unfolding resolution_positions_distinct_def by blast
        then show False using h(2) by simp
      qed
      have dis: "resolution_goal_variables h |\<inter>| Y = {||}" using hold_g[OF h] not_child by blast
      have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| resolution_goal_variables h" for z
      proof -
        have "z |\<notin>| finite_material_variables M"
        proof
          assume "z |\<in>| finite_material_variables M"
          then have "z |\<in>| Y" using Ysub by (meson fsubsetD)
          then have "z |\<in>| resolution_goal_variables h |\<inter>| Y" using z by simp
          then show False using dis by simp
        qed
        then have "z \<notin> {w1,w2,w3,w4}" using w by (auto simp: finite_material_variables_def)
        then show ?thesis by (simp add: \<theta>1_def)
      qed
      show ?thesis using holds\<theta>[OF h(1)] finite_goal_holds_cong[of h \<theta>1 \<theta>] same by blast
    qed
    show ?thesis using tuple ground1 others by blast
  qed
  then obtain \<theta>1 where can1: "(resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple R (finite_artifact_rows R)"
    and ground1: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M)"
    and hold1: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> h \<noteq> ?g \<Longrightarrow> finite_goal_holds ?Mn \<theta>1 h"
    by blast
  show ?thesis
    using finite_canonical_successor_supported[OF I gp source Ws ground1 can1 placed hold1] by blast
qed

text \<open>Today's exchange is the framed one's instance at the socket's default frame, the variant test giving (iii).\<close>

lemma finite_material_socket_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Material_Goal q r M |\<in>| finite_focus_pending F st"
    and Ws: "finite_canonical_solutions M = Some Ws" and free: "finite_free_fields M"
    and prem: "finite_material_premise st (Resolution_Material_Goal q r M)"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q" and qne: "q \<noteq> []"
    and ctx: "finite_parent_context P Vp Vh st nd (last q)"
    and socket: "socket_discharged (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) (last q) keep Vp Vh"
    and Vh: "view_formed Vh"
    and hold: "finite_socket_holders F st q Y (Resolution_Material_Goal q r M)"
    and Ysub: "finite_material_variables M |\<subseteq>| Y"
    and head: "keep \<or> (F = Some (butlast q) \<and> (\<exists>hi ho x out.
        resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho) \<and>
        resolution_view_pattern Vh (resolution_node_call nd) = Some (x,out) \<and> finite_variant ho out \<and>
        finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||} \<and> finite_pattern_variables out |\<subseteq>| Y))"
  shows "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
    resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  have linked: "resolution_node_linked P st nd" using ctx by (simp add: finite_parent_context_def)
  have formed: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  let ?C = "finite_default_frame Vp Vh (resolution_node_schema nd) (last q)"
  have ctxF: "finite_framed_parent_context P ?C st nd (last q)" by (rule finite_parent_context_framed[OF ctx])
  have sockF: "socket_framed (positive_meaning (decode_finite_system P)) (resolution_node_schema nd) (last q) keep Vp Vh
      (fset ?C)"
    unfolding finite_default_frame_correct by (rule socket_discharged_framed[OF socket formed])
  have call: "resolution_node_call nd =
      finite_pattern_substitute (finite_node_binding nd) (finite_schema_conclusion (resolution_node_schema nd))"
    by (rule finite_node_binding_linked(2)[OF I nd(1)])
  have headF: "keep \<or> (F = Some (butlast q) \<and> finite_parent_absorbs Vp Vh ?C nd (last q) \<and>
      finite_input_output_apart Vh nd \<and> finite_parent_absorbed Vp Vh ?C nd (last q) |\<subseteq>| Y)"
  proof (cases keep)
    case False
    then obtain hi ho x out where Fq: "F = Some (butlast q)"
        and hd: "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema nd)) = Some (hi,ho)"
        and cl: "resolution_view_pattern Vh (resolution_node_call nd) = Some (x,out)" and var: "finite_variant ho out"
        and ap: "finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||}"
        and oY: "finite_pattern_variables out |\<subseteq>| Y"
      using head by blast
    have xo: "out = finite_pattern_substitute (finite_node_binding nd) ho"
      using resolution_view_pattern_substitute[OF hd, of "finite_node_binding nd"] cl call by simp
    have var': "finite_variant ho (finite_pattern_substitute (finite_node_binding nd) ho)" using var xo by simp
    have abs: "finite_parent_absorbs Vp Vh ?C nd (last q)" by (rule finite_variant_absorbs(1)[OF hd var'])
    have absY: "finite_parent_absorbed Vp Vh ?C nd (last q) |\<subseteq>| Y"
    proof (rule fsubsetI)
      fix w assume w: "w |\<in>| finite_parent_absorbed Vp Vh ?C nd (last q)"
      have "w |\<in>| finite_pattern_variables (finite_pattern_substitute (finite_node_binding nd) ho)"
        using finite_variant_absorbs(2)[OF hd var'] w by (meson fsubsetD)
      then have "w |\<in>| finite_pattern_variables out" using xo by simp
      then show "w |\<in>| Y" using oY by (meson fsubsetD)
    qed
    have apart: "finite_input_output_apart Vh nd" using cl ap by (simp add: finite_input_output_apart_def)
    show ?thesis using Fq abs apart absY by blast
  qed simp
  show ?thesis by (rule finite_framed_material_exchange[OF I sup gF Ws free prem nd qne ctxF sockF Vh hold Ysub headF])
qed

subsection \<open>The discharge of the premise's material part\<close>

text \<open>
  At every state where the test commits a material single solution, some canonical successor is supported with every
  node then present barred: the material part of \<open>finite_commitment_exchanges\<close>, as #621 left it, at the framed
  test, for any finite program, any declarations and frames discharged (\<open>frames_discharged\<close>) at any views and any
  witness construction. The socket is read at its declared views and at the frame the test chose: the parent context
  comes from the test at that frame (\<open>finite_framed_socket_context\<close>), the obligation at the frame from
  \<open>finite_frame_at_framed\<close>.
\<close>

theorem finite_framed_material_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    g |\<in>| finite_focus_pending F st \<Longrightarrow> g = Resolution_Material_Goal q r M \<Longrightarrow>
    finite_canonical_solutions M = Some Ws \<Longrightarrow> commit_material (finite_framed_commitment D \<Phi>) F st g \<Longrightarrow>
    \<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material (finite_framed_commitment D \<Phi>) F st g"
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Material_Goal q r M"
  have gF': "?g |\<in>| finite_focus_pending F st" using gF gq by simp
  have prem: "finite_material_premise st ?g" using cm gq by (simp add: finite_framed_commitment_def)
  obtain Vp Vh ch where sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st ?g"
      and mn: "finite_material_framed D \<Phi> Vp Vh ch F st ?g"
    using cm gq by (auto simp: finite_framed_commitment_def)
  have cn: "finite_call_framed D \<Phi> Vp Vh ch F st ?g" by (simp add: finite_call_framed_def)
  obtain nd C where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q" and qne: "q \<noteq> []"
    and fa: "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch = Some C"
    and ctx: "finite_framed_parent_context P C st nd (last q)"
    using finite_framed_socket_context[OF I sc cn mn] by auto
  have free: "finite_free_fields M"
    and decl: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) ?g"
    using sc by (simp_all add: finite_socket_commitment_framed_def)
  obtain nd0 where nd0: "nd0 |\<in>| resolution_nodes st" "resolution_node_position nd0 = butlast q"
    and ka: "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) ?g \<or>
      finite_input_output_apart Vh nd0"
    using mn unfolding finite_material_framed_def by auto
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have same: "m = nd" if "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast q" for m
  proof -
    have "resolution_node_position m = resolution_node_position nd" using that(2) nd(2) by simp
    then show ?thesis using dist that(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  have linked: "resolution_node_linked P st nd" using ctx by (simp add: finite_framed_parent_context_def)
  have formed: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  have views: "view_formed Vh" if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" for e S s keep
  proof -
    have "declarations_formed D" using discharged by (simp add: declarations_discharged_def)
    then show ?thesis using that unfolding declarations_formed_def by auto
  qed
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
  proof (cases "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) ?g")
    case True
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,True,Vp,Vh) |\<in>| declared_sockets D"
      and hold: "finite_socket_holders F st q (finite_material_variables M) ?g"
      using True unfolding finite_socket_kept_framed_def by auto
    have eq: "nd' = nd" by (rule same[OF nd'(1,2)])
    have decl': "(resolution_node_site nd,resolution_node_schema nd,last q,True,Vp,Vh) |\<in>| declared_sockets D"
      using nd'(3) eq by simp
    have sock: "socket_framed ?M (resolution_node_schema nd) (last q) True Vp Vh (fset C)"
      by (rule finite_frame_at_framed[OF discharged frames decl' fa formed])
    show ?thesis
      by (rule finite_framed_material_exchange[OF I sup gF' Ws free prem nd qne ctx sock views[OF decl'] hold]) simp_all
  next
    case False
    have fr: "finite_socket_free_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) ?g"
      using decl False by (simp add: finite_socket_declared_framed_def)
    have apart: "finite_input_output_apart Vh nd" using ka False same[OF nd0] by simp
    obtain nd' C' where Fq: "F = Some (butlast q)"
      and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,False,Vp,Vh) |\<in>| declared_sockets D"
      and fa': "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd') (resolution_node_schema nd') (last q) ch = Some C'"
      and abs: "finite_parent_absorbs Vp Vh C' nd' (last q)"
      and hold: "finite_socket_holders F st q
        (finite_material_variables M |\<union>| finite_parent_absorbed Vp Vh C' nd' (last q)) ?g"
      using fr unfolding finite_socket_free_framed_def by (auto split: option.splits)
    have eq: "nd' = nd" by (rule same[OF nd'(1,2)])
    have CC: "C' = C" using fa fa' eq by simp
    have decl': "(resolution_node_site nd,resolution_node_schema nd,last q,False,Vp,Vh) |\<in>| declared_sockets D"
      using nd'(3) eq by simp
    have sock: "socket_framed ?M (resolution_node_schema nd) (last q) False Vp Vh (fset C)"
      by (rule finite_frame_at_framed[OF discharged frames decl' fa formed])
    show ?thesis
      by (rule finite_framed_material_exchange[OF I sup gF' Ws free prem nd qne ctx sock views[OF decl'] hold])
        (use Fq abs apart eq CC in auto)
  qed
qed

text \<open>
  Today's material part is the framed one's instance at no frames: every material goal today's test commits the framed
  test commits (B1's containment, at the headed nodes the invariant gives).
\<close>

theorem finite_material_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    g |\<in>| finite_focus_pending F st \<Longrightarrow> g = Resolution_Material_Goal q r M \<Longrightarrow>
    finite_canonical_solutions M = Some Ws \<Longrightarrow> commit_material (finite_declared_commitment D) F st g \<Longrightarrow>
    \<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material (finite_declared_commitment D) F st g"
  have cm': "commit_material (finite_framed_commitment D {||}) F st g"
    by (rule finite_framed_commitment_material[OF cm finite_invariant_headed[OF I]])
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
    by (rule finite_framed_material_commitment_exchanges[OF discharged no_frames_discharged I sup gF gq Ws cm'])
qed

end
