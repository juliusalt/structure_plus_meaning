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
  and it re-grounds the pending siblings, which alone hold the premise-only variables and the socket's variables.

  Three state conditions the test does not check yet are needed (\<open>finite_material_narrowed\<close>, joining
  \<open>finite_children_instances\<close>, \<open>finite_premise_only_unshared\<close> and \<open>finite_input_output_apart\<close>, defined beside the
  test in \<open>Factor_Resolution_Commitments\<close>), each true where the search commits and a counterexample to the premise
  where it fails (DECISIONS.md, task 495's entry, correction (7)).
\<close>

subsection \<open>Values read as evaluations\<close>

lemma finite_material_ground_value:
  "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) N) \<longleftrightarrow>
    finite_material_observation (resolution_value \<theta> (finite_material_source N)) (resolution_value \<theta> (finite_material_atoms N))
      (resolution_value \<theta> (finite_material_edges N)) (resolution_value \<theta> (finite_material_counts N))
      (resolution_value \<theta> (finite_material_functions N))"
  by (simp add: finite_material_ground_satisfied_def resolution_value_exact[symmetric])

subsection \<open>A variant output is a renaming of the head output\<close>

lemma finite_variant_pairs_substitute:
  "finite_variant_pairs p (finite_pattern_substitute \<beta> p) = Some l \<Longrightarrow>
    (\<forall>b. b |\<in>| finite_pattern_variables p \<longrightarrow> (\<exists>w. \<beta> b = Finite_Variable w \<and> (b,w) \<in> set l)) \<and>
    (\<forall>b w. (b,w) \<in> set l \<longrightarrow> \<beta> b = Finite_Variable w)"
proof (induction p arbitrary: l)
  case (Finite_Variable a)
  then show ?case by (cases "\<beta> a") auto
next
  case (Finite_Pattern_Target x)
  then show ?case by simp
next
  case (Finite_Pattern_Payload x)
  then show ?case by simp
next
  case (Finite_Pattern_Pair p1 p2)
  from Finite_Pattern_Pair.prems obtain l1 l2 where l1: "finite_variant_pairs p1 (finite_pattern_substitute \<beta> p1) = Some l1"
    and l2: "finite_variant_pairs p2 (finite_pattern_substitute \<beta> p2) = Some l2" and l: "l = l1 @ l2"
    by (auto split: option.splits)
  show ?case using Finite_Pattern_Pair.IH(1)[OF l1] Finite_Pattern_Pair.IH(2)[OF l2] l by auto
qed

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

subsection \<open>The socket's obligation re-grounds the pending siblings\<close>

text \<open>
  At a focus holding the parent's children, the parent clause's instance under the support is true: its premises and
  material premises are the pending children, focused and holding. The canonical answer satisfies the socket's material
  premise at the same source, so the obligation gives a true instance agreeing with it on the material variables and
  keeping the head (its input only, at a free socket). The valuation reads that instance at the premise-only variables,
  which the siblings alone hold, and at the output's variables, which only the siblings hold there; it keeps the support
  elsewhere, which no premise-only variable and no output variable reaches in the parent's call.
\<close>

lemma finite_material_socket_valuation:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes linked: "resolution_node_linked P st nd"
    and N0: "(k,N0) |\<in>| finite_schema_materials (resolution_node_schema nd)"
    and g: "Resolution_Material_Goal (resolution_node_position nd@[k]) r M |\<in>| resolution_pending st"
    and M: "M = finite_material_pattern_substitute (finite_node_binding nd) N0"
    and inst: "finite_children_instances st nd"
    and po_free: "finite_premise_only_free st nd"
    and unshared: "finite_premise_only_unshared nd"
    and focus: "resolution_focused F (resolution_node_position nd)"
    and holds: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    and socket: "socket_discharged (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema nd)) k keep"
    and head: "keep \<or> (\<exists>hi ho x out. finite_schema_conclusion (resolution_node_schema nd) = Finite_Pattern_Pair hi ho \<and>
        resolution_node_call nd = Finite_Pattern_Pair x out \<and> finite_variant ho out \<and>
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
  let ?Mn = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema nd"
  let ?pos = "resolution_node_position nd"
  let ?\<beta> = "finite_node_binding nd"
  let ?SV = "finite_schema_variables ?S"
  let ?cv = "finite_pattern_variables (finite_schema_conclusion ?S)"
  let ?g = "Resolution_Material_Goal (?pos@[k]) r M"
  obtain \<beta>0 where bind: "resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta>0 a)) ?SV"
    and call0: "resolution_node_call nd = finite_pattern_substitute \<beta>0 (finite_schema_conclusion ?S)"
    using linked unfolding resolution_node_linked_def by blast
  have sv: "single_valued (fset (resolution_node_bindings nd))" unfolding bind by (auto simp: single_valued_def)
  have \<beta>b: "?\<beta> a = p" if "(a,p) |\<in>| resolution_node_bindings nd" for a p
    by (rule finite_node_binding_row[OF sv that])
  have \<beta>0: "?\<beta> a = \<beta>0 a" if "a |\<in>| ?SV" for a by (rule \<beta>b) (use that in \<open>auto simp: bind\<close>)
  have cv_sv: "a |\<in>| ?SV" if "a |\<in>| ?cv" for a using that by (simp add: finite_schema_variables_def)
  have call: "resolution_node_call nd = finite_pattern_substitute ?\<beta> (finite_schema_conclusion ?S)"
    unfolding call0 by (rule finite_pattern_substitute_cong) (simp add: \<beta>0 cv_sv)
  have po_var: "?\<beta> a = Finite_Variable ((?pos,True),a)" if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
  proof -
    have "(a,Finite_Variable ((?pos,True),a)) |\<in>| resolution_node_bindings nd"
      using po_free that unfolding finite_premise_only_free_def by auto
    then show ?thesis by (rule \<beta>b)
  qed
  have po_child: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos"
    if "h |\<in>| resolution_pending st" "a |\<in>| ?SV" "a |\<notin>| ?cv" "((?pos,True),a) |\<in>| resolution_goal_variables h" for h a
    using po_free that unfolding finite_premise_only_free_def by auto
  have po_call: "((?pos,True),a) |\<notin>| finite_pattern_variables (resolution_node_call nd)" if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    using unshared that unfolding finite_premise_only_unshared_def by auto
  have inst_call: "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
      (finite_pattern_substitute ?\<beta> p) |\<in>| resolution_pending st"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using inst that unfolding finite_children_instances_def by auto
  have inst_mat: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
      (finite_material_pattern_substitute ?\<beta> N) |\<in>| resolution_pending st"
    if "(s,N) |\<in>| finite_schema_materials ?S" for s N
    using inst that unfolding finite_children_instances_def by auto
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
      using inst that unfolding finite_children_instances_def by blast
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
    have "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) d
        (finite_pattern_substitute ?\<beta> p0) |\<in>| finite_focus_pending F st"
      by (rule foc[OF inst_call[OF p0]]) simp
    then have "(d,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute ?\<beta> p0))) \<in> ?Mn"
      using holds by (fastforce simp: finite_goal_holds_def)
    then have t: "(d,evaluate_pattern ev (decode_finite_pattern p0)) \<in> ?Mn" unfolding evsub ev_def .
    show "(d,evaluate_pattern hA p) \<in> ?Mn" using t evhA[OF call_formed[OF t]] pp by simp
  next
    fix s N assume sN: "(s,N) \<in> schema_material_premises (decode_finite_schema ?S)"
    obtain N1 where N1: "(s,N1) |\<in>| finite_schema_materials ?S" and NN: "N = decode_finite_material N1"
      using sN by auto
    have "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
        (finite_material_pattern_substitute ?\<beta> N1) |\<in>| finite_focus_pending F st"
      by (rule foc[OF inst_mat[OF N1]]) simp
    then have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute ?\<beta> N1))"
      using holds by (fastforce simp: finite_goal_holds_def)
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
  have src: "finite_pattern_substitute ?\<beta> (finite_material_source N0) = Finite_Pattern_Target (Finite_Whole C)"
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
  have Cf: "finite_exact_formed C" by (rule finite_material_source_formed[OF gsat source])
  obtain A E Bs Fs where rows: "finite_artifact_rows C = (A,E,Bs,Fs)" by (cases "finite_artifact_rows C") auto
  let ?a0 = "finite_enumeration_term (map (finite_atom_term C) A)"
  let ?e0 = "finite_enumeration_term (map (finite_incidence_term C) E)"
  let ?b0 = "finite_enumeration_term (map (finite_attachment_term C) Bs)"
  let ?f0 = "finite_enumeration_term (map (finite_attachment_term C) Fs)"
  have canon: "finite_material_observation (Finite_Target (Finite_Whole C)) ?a0 ?e0 ?b0 ?f0"
    by (rule finite_canonical_observation[OF Cf rows])
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
      decode_finite_term (Finite_Target (Finite_Whole C))"
    using evsub[of \<theta> "finite_material_source N0"] src by (simp add: ev_def resolution_value_target)
  have src_formed: "term_formed (decode_finite_term (Finite_Target (Finite_Whole C)))"
    using Cf finite_term_formed_correct[of "Finite_Target (Finite_Whole C)"] by simp
  have hA_src: "evaluate_pattern hA (decode_finite_pattern (finite_material_source N0)) =
      decode_finite_term (Finite_Target (Finite_Whole C))"
    using evhA[of "decode_finite_pattern (finite_material_source N0)"] ev_src src_formed by simp
  have gm_sat: "evaluate_material_satisfaction gm (decode_finite_material N0)"
    using canon[unfolded finite_material_observation_correct] gm_src hA_src gm_x x1(1) x2(1) x3(1) x4(1)
    by (simp add: decode_finite_material_def)
  have same_src: "evaluate_pattern gm (material_source (decode_finite_material N0)) =
      evaluate_pattern hA (material_source (decode_finite_material N0))"
    using gm_src by (simp add: decode_finite_material_def)
  have N0d: "(k,decode_finite_material N0) \<in> schema_material_premises (decode_finite_schema ?S)" using N0 by auto
  have obligation: "\<forall>N g. (k,N) \<in> schema_material_premises (decode_finite_schema ?S) \<longrightarrow>
      evaluate_material_satisfaction g N \<longrightarrow>
      evaluate_pattern g (material_source N) = evaluate_pattern hA (material_source N) \<longrightarrow>
      (\<exists>h'. clause_true ?Mn (decode_finite_schema ?S) h' \<and> head_kept keep (decode_finite_schema ?S) hA h' \<and>
        (\<forall>a\<in>material_variables N. h' a = g a))"
    using socket clause_hA unfolding socket_discharged_def by blast
  obtain hN where clN: "clause_true ?Mn (decode_finite_schema ?S) hN"
    and hk: "head_kept keep (decode_finite_schema ?S) hA hN"
    and agN: "\<forall>a\<in>material_variables (decode_finite_material N0). hN a = gm a"
    using obligation N0d gm_sat same_src by blast
  have hN_x: "hN x1 = decode_finite_term ?a0" "hN x2 = decode_finite_term ?e0" "hN x3 = decode_finite_term ?b0"
      "hN x4 = decode_finite_term ?f0"
    using agN gm_x xmv finite_material_variables_correct[of N0] by auto
  have hN_formed: "term_formed (hN a)" if "a |\<in>| ?SV" for a
    using clN that finite_schema_variables_correct[of ?S] unfolding clause_true_def by auto
  define inv where "inv = (\<lambda>z. SOME b. b |\<in>| ?cv \<and> ?\<beta> b = Finite_Variable z)"
  define PO where "PO = {z. \<exists>a. a |\<in>| ?SV \<and> a |\<notin>| ?cv \<and> z = ((?pos,True),a)}"
  define \<theta>1 where "\<theta>1 = (\<lambda>z. if z \<in> PO then finite_term_of (hN (snd z))
      else if z \<in> OUT then finite_term_of (hN (inv z)) else \<theta> z)"
  have call_vars: "finite_pattern_variables (?\<beta> b) |\<subseteq>| finite_pattern_variables (resolution_node_call nd)"
    if "b |\<in>| ?cv" for b
    unfolding call by (rule finite_substitute_variables_subset[OF that])
  have notpo: "z \<notin> PO" if "z |\<in>| finite_pattern_variables (resolution_node_call nd)" for z
    unfolding PO_def using po_call that by blast
  have key: "decode_finite_term (resolution_value \<theta>1 (?\<beta> b)) = hN b"
    if b: "b |\<in>| ?SV" and bf: "b |\<notin>| ?cv \<or> term_formed (ev b)" for b
  proof (cases "b |\<in>| ?cv")
    case False
    have "?\<beta> b = Finite_Variable ((?pos,True),b)" by (rule po_var[OF b False])
    moreover have "((?pos,True),b) \<in> PO" unfolding PO_def using b False by blast
    ultimately have "resolution_value \<theta>1 (?\<beta> b) = finite_term_of (hN b)"
      by (simp add: \<theta>1_def resolution_value_def)
    then show ?thesis using decode_finite_term_of[OF hN_formed[OF b]] by simp
  next
    case True
    have evf: "term_formed (ev b)" using bf True by blast
    have agree_\<theta>: "resolution_value \<theta>1 (?\<beta> b) = resolution_value \<theta> (?\<beta> b)"
      if outd: "fset (finite_pattern_variables (?\<beta> b)) \<inter> OUT = {}"
    proof (rule resolution_value_cong)
      fix z assume z: "z |\<in>| finite_pattern_variables (?\<beta> b)"
      have zc: "z |\<in>| finite_pattern_variables (resolution_node_call nd)"
        using call_vars[OF True] z by (meson fsubsetD)
      have "z \<notin> OUT" using outd z by auto
      then show "\<theta>1 z = \<theta> z" using notpo[OF zc] by (simp add: \<theta>1_def)
    qed
    have kept_case: "decode_finite_term (resolution_value \<theta>1 (?\<beta> b)) = hN b"
      if e: "hN b = hA b" and o: "fset (finite_pattern_variables (?\<beta> b)) \<inter> OUT = {}"
    proof -
      have "decode_finite_term (resolution_value \<theta>1 (?\<beta> b)) = ev b" using agree_\<theta>[OF o] by (simp add: ev_def)
      then show ?thesis using e evf by (simp add: hA_def)
    qed
    show ?thesis
    proof (cases keep)
      case True
      have "evaluate_pattern hN (decode_finite_pattern (finite_schema_conclusion ?S)) =
          evaluate_pattern hA (decode_finite_pattern (finite_schema_conclusion ?S))"
        using hk True by (auto simp: head_kept_def split: term_pattern.splits)
      then have "hN b = hA b"
        by (rule evaluate_pattern_agree) (use \<open>b |\<in>| ?cv\<close> in \<open>simp add: finite_pattern_variables_correct[symmetric]\<close>)
      moreover have "OUT = {}" by (rule kept_out[OF True])
      ultimately show ?thesis by (intro kept_case) auto
    next
      case False
      then obtain hi ho x out where hd: "finite_schema_conclusion ?S = Finite_Pattern_Pair hi ho"
        and cl: "resolution_node_call nd = Finite_Pattern_Pair x out" and var: "finite_variant ho out"
        and ap: "finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||}"
        and OUTe: "OUT = fset (finite_pattern_variables out)"
        using head by blast
      have xo: "x = finite_pattern_substitute ?\<beta> hi" "out = finite_pattern_substitute ?\<beta> ho"
        using call cl hd by simp_all
      have hi_kept: "evaluate_pattern hN (decode_finite_pattern hi) = evaluate_pattern hA (decode_finite_pattern hi)"
        using hk hd by (simp add: head_kept_def)
      show ?thesis
      proof (cases "b |\<in>| finite_pattern_variables hi")
        case True
        have e: "hN b = hA b"
          by (rule evaluate_pattern_agree[OF hi_kept]) (use True in \<open>simp add: finite_pattern_variables_correct[symmetric]\<close>)
        have "finite_pattern_variables (?\<beta> b) |\<subseteq>| finite_pattern_variables x"
          unfolding xo by (rule finite_substitute_variables_subset[OF True])
        then have "fset (finite_pattern_variables (?\<beta> b)) \<inter> OUT = {}"
        proof (intro equals0I)
          fix z assume z: "z \<in> fset (finite_pattern_variables (?\<beta> b)) \<inter> OUT"
          assume sub: "finite_pattern_variables (?\<beta> b) |\<subseteq>| finite_pattern_variables x"
          have "z |\<in>| finite_pattern_variables x" using z sub by (meson IntD1 fsubsetD)
          moreover have "z |\<in>| finite_pattern_variables out" using z OUTe by simp
          ultimately have "z |\<in>| finite_pattern_variables x |\<inter>| finite_pattern_variables out" by simp
          then show False using ap by simp
        qed
        then show ?thesis by (rule kept_case[OF e])
      next
        case nhi: False
        have bho: "b |\<in>| finite_pattern_variables ho" using \<open>b |\<in>| ?cv\<close> nhi hd by simp
        have var': "finite_variant ho (finite_pattern_substitute ?\<beta> ho)" using var xo by simp
        obtain w where w: "?\<beta> b = Finite_Variable w" by (rule finite_variant_substitute_variable[OF var' bho])
        have wout: "w |\<in>| finite_pattern_variables out"
          using finite_substitute_variables_subset[OF bho, of ?\<beta>] w xo by simp
        have wcall: "w |\<in>| finite_pattern_variables (resolution_node_call nd)" using wout cl by simp
        have invw: "inv w = b"
        proof -
          have ex: "b |\<in>| ?cv \<and> ?\<beta> b = Finite_Variable w" using \<open>b |\<in>| ?cv\<close> w by simp
          have "inv w |\<in>| ?cv \<and> ?\<beta> (inv w) = Finite_Variable w"
            unfolding inv_def by (rule someI[of _ b]) (rule ex)
          then have iv: "inv w |\<in>| ?cv" "?\<beta> (inv w) = Finite_Variable w" by simp_all
          have iho: "inv w |\<in>| finite_pattern_variables ho"
          proof (rule ccontr)
            assume "inv w |\<notin>| finite_pattern_variables ho"
            then have ihi: "inv w |\<in>| finite_pattern_variables hi" using iv(1) hd by simp
            have "finite_pattern_variables (?\<beta> (inv w)) |\<subseteq>| finite_pattern_variables x"
              unfolding xo by (rule finite_substitute_variables_subset[OF ihi])
            then have "w |\<in>| finite_pattern_variables x" using iv(2) by simp
            then have "w |\<in>| finite_pattern_variables x |\<inter>| finite_pattern_variables out" using wout by simp
            then show False using ap by simp
          qed
          have "?\<beta> (inv w) = ?\<beta> b" using iv(2) w by simp
          then show ?thesis by (rule finite_variant_substitute_injective[OF var' iho bho])
        qed
        have "\<theta>1 w = finite_term_of (hN b)" using notpo[OF wcall] wout OUTe invw by (simp add: \<theta>1_def)
        then show ?thesis using w decode_finite_term_of[OF hN_formed[OF b]] by (simp add: resolution_value_def)
      qed
    qed
  qed
  have evf: "term_formed (ev x1)" "term_formed (ev x2)" "term_formed (ev x3)" "term_formed (ev x4)"
    using mat_vars_formed[OF gev xmv(1)] mat_vars_formed[OF gev xmv(2)] mat_vars_formed[OF gev xmv(3)]
      mat_vars_formed[OF gev xmv(4)] by simp_all
  have field_val: "resolution_value \<theta>1 (Finite_Variable w) = c"
    if "?\<beta> x = Finite_Variable w" "x |\<in>| ?SV" "term_formed (ev x)" "hN x = decode_finite_term c" for w x c
  proof -
    have "decode_finite_term (resolution_value \<theta>1 (Finite_Variable w)) = hN x" using key[OF that(2)] that(1,3) by simp
    then show ?thesis using that(4) by simp
  qed
  have fv: "resolution_value \<theta>1 (finite_material_atoms M) = ?a0" "resolution_value \<theta>1 (finite_material_edges M) = ?e0"
      "resolution_value \<theta>1 (finite_material_counts M) = ?b0" "resolution_value \<theta>1 (finite_material_functions M) = ?f0"
      "resolution_value \<theta>1 (finite_material_source M) = Finite_Target (Finite_Whole C)"
    using field_val[OF x1(2) matv[OF xmv(1)] evf(1) hN_x(1)] field_val[OF x2(2) matv[OF xmv(2)] evf(2) hN_x(2)]
      field_val[OF x3(2) matv[OF xmv(3)] evf(3) hN_x(3)] field_val[OF x4(2) matv[OF xmv(4)] evf(4) hN_x(4)] w source
    by (simp_all add: resolution_value_target)
  have tuple: "(resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C)"
    using fv rows by simp
  have ground1: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M)"
    unfolding finite_material_ground_value using canon fv by simp
  have eq_on: "evaluate_pattern (\<lambda>b. decode_finite_term (resolution_value \<theta>1 (?\<beta> b))) (decode_finite_pattern p) =
      evaluate_pattern hN (decode_finite_pattern p)"
    if "\<And>b. b |\<in>| finite_pattern_variables p \<Longrightarrow> b |\<in>| ?SV \<and> (b |\<notin>| ?cv \<or> term_formed (ev b))" for p
    by (rule evaluate_pattern_cong) (use key that in \<open>auto simp: finite_pattern_variables_correct[symmetric]\<close>)
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
      have pv: "b |\<in>| ?SV \<and> (b |\<notin>| ?cv \<or> term_formed (ev b))" if "b |\<in>| finite_pattern_variables p" for b
      proof
        show "b |\<in>| ?SV" using p that by (force simp: finite_schema_variables_def resolution_fset_simps)
        show "b |\<notin>| ?cv \<or> term_formed (ev b)"
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
      have mv: "b |\<in>| ?SV \<and> (b |\<notin>| ?cv \<or> term_formed (ev b))" if "b |\<in>| finite_material_variables N1" for b
      proof
        show "b |\<in>| ?SV" using N1 that by (force simp: finite_schema_variables_def resolution_fset_simps)
        show "b |\<notin>| ?cv \<or> term_formed (ev b)" using mat_vars_formed[OF s\<theta> that] by blast
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
    case False
    have h\<theta>: "finite_goal_holds ?Mn \<theta> h" by (rule holds[OF h(1)])
    have hp: "h |\<in>| resolution_pending st" using h(1) by (simp add: finite_focus_pending_focused)
    have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| resolution_goal_variables h" for z
    proof -
      have npo: "z \<notin> PO" unfolding PO_def using po_child[OF hp] z False by blast
      have "z \<notin> OUT" using outside[OF h(1) False] z by blast
      then show ?thesis using npo by (simp add: \<theta>1_def)
    qed
    show ?thesis using h\<theta> finite_goal_holds_cong[of h \<theta>1 \<theta>] same by blast
  qed
  show ?thesis using tuple ground1 others by blast
qed

subsection \<open>The exchange at a material socket\<close>

text \<open>
  Where the focus holds the parent's children, the socket's obligation gives the valuation; where it does not, the focus
  holds no child but the committed goal, so no focused goal holds a variable of the socket and the canonical answer
  simply replaces the support there. Either valuation supports a canonical successor with every node barred.
\<close>

lemma finite_material_socket_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Material_Goal q r M |\<in>| finite_focus_pending F st"
    and Ws: "finite_canonical_solutions M = Some Ws" and free: "finite_free_fields M"
    and prem: "finite_material_premise st (Resolution_Material_Goal q r M)"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q" and qne: "q \<noteq> []"
    and inst: "finite_children_instances st nd" and po_free: "finite_premise_only_free st nd"
    and unshared: "finite_premise_only_unshared nd"
    and socket: "socket_discharged (positive_meaning (decode_finite_system P))
      (decode_finite_schema (resolution_node_schema nd)) (last q) keep"
    and hold: "finite_socket_holders F st q Y (Resolution_Material_Goal q r M)"
    and Ysub: "finite_material_variables M |\<subseteq>| Y"
    and head: "keep \<or> (F = Some (butlast q) \<and> (\<exists>hi ho x out.
        finite_schema_conclusion (resolution_node_schema nd) = Finite_Pattern_Pair hi ho \<and>
        resolution_node_call nd = Finite_Pattern_Pair x out \<and> finite_variant ho out \<and>
        finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||} \<and> finite_pattern_variables out |\<subseteq>| Y))"
  shows "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
    resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  let ?Mn = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Material_Goal q r M"
  let ?pos = "resolution_node_position nd"
  let ?\<beta> = "finite_node_binding nd"
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have linked: "resolution_node_linked P st nd"
    using I nd(1) unfolding resolution_invariant_def resolution_nodes_placed_def by blast
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  obtain k where qk: "q = ?pos @ [k]" and k: "k = last q" using nd(2) qne by (metis append_butlast_last_id)
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
    using inst N0 unfolding finite_children_instances_def by auto
  have gq: "Resolution_Material_Goal (?pos@[k]) r M |\<in>| resolution_pending st" using gp by (simp only: qk[symmetric])
  have "resolution_goal_position (Resolution_Material_Goal (?pos@[k]) r M) =
      resolution_goal_position (Resolution_Material_Goal (?pos@[k]) (resolution_node_site nd,resolution_node_clause nd,k)
        (finite_material_pattern_substitute ?\<beta> N0))" by simp
  then have "Resolution_Material_Goal (?pos@[k]) r M = Resolution_Material_Goal (?pos@[k])
      (resolution_node_site nd,resolution_node_clause nd,k) (finite_material_pattern_substitute ?\<beta> N0)"
    using dist gq inst_g unfolding resolution_positions_distinct_def by blast
  then have Meq: "M = finite_material_pattern_substitute ?\<beta> N0" by simp
  obtain C where source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
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
  have "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
      resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C) \<and>
    finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> ?g \<longrightarrow> finite_goal_holds ?Mn \<theta>1 h)"
  proof (cases "resolution_focused F ?pos")
    case True
    show ?thesis
    proof (cases keep)
      case kept: True
      have "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
          resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
          resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C) \<and>
        finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> Resolution_Material_Goal (?pos@[k]) r M \<longrightarrow>
          finite_goal_holds ?Mn \<theta>1 h)"
        by (rule finite_material_socket_valuation[where keep=keep and OUT="{}", OF linked N0 gq Meq inst po_free
          unshared True holds\<theta> socket[unfolded k[symmetric]] _ _ _ free source]) (use kept in auto)
      then show ?thesis unfolding qk by blast
    next
      case nk: False
      then obtain hi ho x out where hd: "finite_schema_conclusion (resolution_node_schema nd) = Finite_Pattern_Pair hi ho"
        "resolution_node_call nd = Finite_Pattern_Pair x out" "finite_variant ho out"
        "finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||}"
        and outY: "finite_pattern_variables out |\<subseteq>| Y"
        using head by blast
      have outside: "z |\<notin>| resolution_goal_variables h"
        if "h |\<in>| finite_focus_pending F st"
          "\<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = ?pos)"
          "z \<in> fset (finite_pattern_variables out)" for h z
      proof -
        have "h \<noteq> ?g" using that(2) qk by auto
        then have dis: "resolution_goal_variables h |\<inter>| Y = {||}" using hold_g[OF that(1)] that(2) by blast
        show ?thesis
        proof
          assume zh: "z |\<in>| resolution_goal_variables h"
          have "z |\<in>| Y" using that(3) outY by (meson fsubsetD)
          then have "z |\<in>| resolution_goal_variables h |\<inter>| Y" using zh by simp
          then show False using dis by simp
        qed
      qed
      have "\<exists>\<theta>1. (resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
          resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
          resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C) \<and>
        finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> h \<noteq> Resolution_Material_Goal (?pos@[k]) r M \<longrightarrow>
          finite_goal_holds ?Mn \<theta>1 h)"
        by (rule finite_material_socket_valuation[where keep=keep and OUT="fset (finite_pattern_variables out)",
          OF linked N0 gq Meq inst po_free unshared True holds\<theta> socket[unfolded k[symmetric]] _ _ outside free source])
          (use nk hd in auto)
      then show ?thesis unfolding qk by blast
    qed
  next
    case nfoc: False
    obtain f where Ff: "F = Some f" using nfoc by (cases F) (simp_all add: resolution_focused_def)
    obtain w1 w2 w3 w4 where w: "finite_material_atoms M = Finite_Variable w1" "finite_material_edges M = Finite_Variable w2"
        "finite_material_counts M = Finite_Variable w3" "finite_material_functions M = Finite_Variable w4"
      and wd: "distinct [w1,w2,w3,w4]"
      by (rule finite_free_fields_variables[OF free])
    have Cf: "finite_exact_formed C" by (rule finite_material_source_formed[OF gsat source])
    obtain A E Bs Fs where rows: "finite_artifact_rows C = (A,E,Bs,Fs)" by (cases "finite_artifact_rows C") auto
    let ?a0 = "finite_enumeration_term (map (finite_atom_term C) A)"
    let ?e0 = "finite_enumeration_term (map (finite_incidence_term C) E)"
    let ?b0 = "finite_enumeration_term (map (finite_attachment_term C) Bs)"
    let ?f0 = "finite_enumeration_term (map (finite_attachment_term C) Fs)"
    have canon: "finite_material_observation (Finite_Target (Finite_Whole C)) ?a0 ?e0 ?b0 ?f0"
      by (rule finite_canonical_observation[OF Cf rows])
    define \<theta>1 where "\<theta>1 = \<theta>(w1 := ?a0, w2 := ?e0, w3 := ?b0, w4 := ?f0)"
    have fv: "resolution_value \<theta>1 (finite_material_atoms M) = ?a0" "resolution_value \<theta>1 (finite_material_edges M) = ?e0"
        "resolution_value \<theta>1 (finite_material_counts M) = ?b0" "resolution_value \<theta>1 (finite_material_functions M) = ?f0"
        "resolution_value \<theta>1 (finite_material_source M) = Finite_Target (Finite_Whole C)"
      using w wd source by (simp_all add: \<theta>1_def resolution_value_def)
    have tuple: "(resolution_value \<theta>1 (finite_material_source M),resolution_value \<theta>1 (finite_material_atoms M),
        resolution_value \<theta>1 (finite_material_edges M),resolution_value \<theta>1 (finite_material_counts M),
        resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C)"
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
      resolution_value \<theta>1 (finite_material_functions M)) = finite_material_tuple C (finite_artifact_rows C)"
    and ground1: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>1) M)"
    and hold1: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> h \<noteq> ?g \<Longrightarrow> finite_goal_holds ?Mn \<theta>1 h"
    by blast
  show ?thesis
    using finite_canonical_successor_supported[OF I gp source Ws ground1 can1 placed hold1] by blast
qed

subsection \<open>The discharge of the premise's material part\<close>

text \<open>
  At every state where the test commits a material single solution and the three state conditions hold, some canonical
  successor is supported with every node then present barred: the material part of \<open>finite_commitment_exchanges\<close>, as
  #621 left it, for any finite program, any declarations and any witness construction.
\<close>

theorem finite_material_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    g |\<in>| finite_focus_pending F st \<Longrightarrow> g = Resolution_Material_Goal q r M \<Longrightarrow>
    finite_canonical_solutions M = Some Ws \<Longrightarrow> commit_material (finite_declared_commitment D) F st g \<Longrightarrow>
    finite_material_narrowed D F st g \<Longrightarrow>
    \<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
proof -
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material (finite_declared_commitment D) F st g"
    and nar: "finite_material_narrowed D F st g"
  let ?g = "Resolution_Material_Goal q r M"
  have gF': "?g |\<in>| finite_focus_pending F st" using gF gq by simp
  have cm': "finite_material_premise st ?g \<and> finite_socket_commitment D F st ?g"
    using cm gq by (simp add: finite_declared_commitment_def)
  have prem: "finite_material_premise st ?g" using cm' by blast
  have free: "finite_free_fields M" and decl: "finite_socket_declared D F st q (finite_material_variables M) ?g"
    using cm' by (simp_all add: finite_socket_commitment_def)
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q"
    and inst: "finite_children_instances st nd" and unsh: "finite_premise_only_unshared nd"
    and ka: "finite_socket_kept D F st q (finite_material_variables M) ?g \<or> finite_input_output_apart nd"
    using nar gq unfolding finite_material_narrowed_def by auto
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have same: "m = nd" if "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast q" for m
  proof -
    have "resolution_node_position m = resolution_node_position nd" using that(2) nd(2) by simp
    then show ?thesis using dist that(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  have sockets: "socket_discharged (positive_meaning (decode_finite_system P)) (decode_finite_schema S) s keep"
    if "(e,S,s,keep) |\<in>| declared_sockets D" for e S s keep
    using discharged that unfolding declarations_discharged_def by blast
  show ?thesis
  proof (cases "finite_socket_kept D F st q (finite_material_variables M) ?g")
    case True
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,True) |\<in>| declared_sockets D"
        "finite_premise_only_free st nd'"
      and qne: "q \<noteq> []" and hold: "finite_socket_holders F st q (finite_material_variables M) ?g"
      using True unfolding finite_socket_kept_def by auto
    have eq: "nd' = nd" by (rule same[OF nd'(1,2)])
    have pof: "finite_premise_only_free st nd" using nd'(4) eq by simp
    have sock: "socket_discharged (positive_meaning (decode_finite_system P))
        (decode_finite_schema (resolution_node_schema nd)) (last q) True"
      using sockets[OF nd'(3)] eq by simp
    show ?thesis by (rule finite_material_socket_exchange[OF I sup gF' Ws free prem nd qne inst pof unsh sock hold]) simp_all
  next
    case False
    have fr: "finite_socket_free D F st q (finite_material_variables M) ?g"
      using decl False by (simp add: finite_socket_declared_def)
    have apart: "finite_input_output_apart nd" using ka False by simp
    obtain nd' out where qne: "q \<noteq> []" and Fq: "F = Some (butlast q)"
      and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,False) |\<in>| declared_sockets D"
        "finite_premise_only_free st nd'"
      and po: "finite_parent_output nd' = Some out"
      and hold: "finite_socket_holders F st q (finite_material_variables M |\<union>| finite_pattern_variables out) ?g"
      using fr unfolding finite_socket_free_def by (auto split: option.splits)
    have eq: "nd' = nd" by (rule same[OF nd'(1,2)])
    have pof: "finite_premise_only_free st nd" using nd'(4) eq by simp
    have sock: "socket_discharged (positive_meaning (decode_finite_system P))
        (decode_finite_schema (resolution_node_schema nd)) (last q) False"
      using sockets[OF nd'(3)] eq by simp
    obtain hi ho x where hd: "finite_schema_conclusion (resolution_node_schema nd) = Finite_Pattern_Pair hi ho"
        "resolution_node_call nd = Finite_Pattern_Pair x out" "finite_variant ho out"
      using po eq by (auto simp: finite_parent_output_def split: prod.splits finite_term_pattern.splits if_splits)
    have ap: "finite_pattern_variables x |\<inter>| finite_pattern_variables out = {||}"
      using apart hd(2) by (simp add: finite_input_output_apart_def)
    show ?thesis
      by (rule finite_material_socket_exchange[OF I sup gF' Ws free prem nd qne inst pof unsh sock hold])
        (use hd ap Fq in auto)
  qed
qed

end
