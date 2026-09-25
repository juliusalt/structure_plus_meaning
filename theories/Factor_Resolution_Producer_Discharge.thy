theory Factor_Resolution_Producer_Discharge
  imports Factor_Resolution_Commitments
begin

section \<open>A committed goal's exchange from its context\<close>

text \<open>
  #565's exchange premise asks, at a committed call goal, that some kept state of its focused sub-search be
  supported with every node then present barred. Barring every node makes the ranks vacuous, so the support is
  the truth of the goals left pending and their placement. The goals left pending at a found state are the goals
  outside the committed position, each the frame's substitution of a goal of the state before
  (@{thm [source] finite_committed_search_frame}); the answer at the position is the call of the node the
  sub-search placed there, accepted in subtree form (@{thm [source] finite_node_proof_subtree_accepted}) and so
  true. What the exchange needs of the context is stated once: every true grounding of the goal's pattern extends
  to a grounding under which every goal outside the position holds (@{text finite_exchange_context}). From it,
  every found state of the sub-search is supported with all its nodes barred, whatever answer it keeps, and so
  every kept one (@{text finite_committed_found_supported}, @{text finite_committed_exchange_context}).

  Two conditions of the state enter beside it. The answer's node is related to the goal through the node at the
  parent position, whose premise the goal is (@{text finite_goal_premise}): the invariant links a node to its
  premises, not a goal to its parent. And the frame lets a construction inside the sub-search bind a registered
  variable of a node already present; such a variable must not be held by a goal outside the position
  (@{text finite_registrations_confined}), which holds at every construction that registers nothing.
\<close>

definition finite_goal_holds ::
    "('d \<times> factor_term) set \<Rightarrow> (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_holds M \<theta> g \<longleftrightarrow> (case g of
      Resolution_Call_Goal q r e p \<Rightarrow> (e,decode_finite_term (resolution_value \<theta> p)) \<in> M
    | Resolution_Material_Goal q r N \<Rightarrow>
        finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) N))"

definition finite_goal_premise :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_premise st g \<longleftrightarrow> resolution_goal_position g \<noteq> [] \<longrightarrow>
    (\<exists>np e0 p0. np |\<in>| resolution_nodes st \<and> resolution_node_position np = butlast (resolution_goal_position g) \<and>
      (last (resolution_goal_position g),e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np))"

definition finite_registrations_confined ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> 's list option \<Rightarrow> 's list \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_registrations_confined \<kappa> F q st \<longleftrightarrow> (\<forall>h z. h |\<in>| finite_focus_pending F st \<longrightarrow>
    \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow> z |\<in>| resolution_goal_variables h \<longrightarrow>
    \<not> finite_registered_at \<kappa> st z)"

definition finite_exchange_context ::
    "('d \<times> factor_term) set \<Rightarrow> 's list option \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 'd \<Rightarrow>
      ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> bool" where
  "finite_exchange_context M F q st e p \<longleftrightarrow> (\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> M \<longrightarrow>
    (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds M \<theta>1 h)))"

lemma finite_registrations_confined_unregistered:
  assumes "\<And>e S. witness_registered \<kappa> e S = {||}"
  shows "finite_registrations_confined \<kappa> F q st"
  using assms by (simp add: finite_registrations_confined_def finite_registered_at_def)

lemma finite_registrations_confined_none: "finite_registrations_confined no_witness_construction F q st"
  by (rule finite_registrations_confined_unregistered) (simp add: no_witness_construction_def)

subsection \<open>Values under a substitution\<close>

lemma resolution_value_composes:
  "resolution_value \<theta> (finite_pattern_substitute \<sigma> p) = resolution_value (\<lambda>z. resolution_value \<theta> (\<sigma> z)) p"
  by (induction p) (simp_all add: resolution_value_def)

lemma resolution_value_residual:
  "resolution_value (\<lambda>z. finite_residual_term (\<sigma> z)) p = finite_residual_term (finite_pattern_substitute \<sigma> p)"
  by (induction p) (simp_all add: resolution_value_def)

lemma resolution_value_blank:
  assumes "\<And>w. w |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> w = Finite_Payload []"
  shows "resolution_value \<theta> p = finite_residual_term p"
  using assms by (induction p) (auto simp: resolution_value_def)

lemma finite_material_substitute_value:
  "finite_material_pattern_substitute (resolution_substitution \<theta>) (finite_material_pattern_substitute \<sigma> N) =
    finite_material_pattern_substitute (resolution_substitution (\<lambda>z. resolution_value \<theta> (\<sigma> z))) N"
  by (simp add: finite_material_pattern_substitute_composes resolution_value_exact)

lemma finite_goal_holds_cong:
  assumes "\<And>z. z |\<in>| resolution_goal_variables g \<Longrightarrow> \<theta> z = \<theta>' z"
  shows "finite_goal_holds M \<theta> g \<longleftrightarrow> finite_goal_holds M \<theta>' g"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  have "resolution_value \<theta> p = resolution_value \<theta>' p"
    by (rule resolution_value_cong) (use assms Resolution_Call_Goal in simp)
  then show ?thesis by (simp add: finite_goal_holds_def Resolution_Call_Goal)
next
  case (Resolution_Material_Goal q r N)
  have "finite_material_pattern_substitute (resolution_substitution \<theta>) N =
      finite_material_pattern_substitute (resolution_substitution \<theta>') N"
    by (rule finite_material_pattern_substitute_cong) (use assms Resolution_Material_Goal in simp)
  then show ?thesis by (simp add: finite_goal_holds_def Resolution_Material_Goal)
qed

lemma finite_goal_holds_substitute:
  "finite_goal_holds M \<theta> (resolution_goal_substitute \<sigma> g) \<longleftrightarrow> finite_goal_holds M (\<lambda>z. resolution_value \<theta> (\<sigma> z)) g"
  by (cases g) (simp_all add: finite_goal_holds_def resolution_value_composes finite_material_substitute_value)


subsection \<open>Support with every node barred, and at the state before\<close>

lemma resolution_supported_at_holds:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and h: "h |\<in>| finite_focus_pending F st"
  shows "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
proof (cases h)
  case (Resolution_Call_Goal q r e p)
  have c: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" "resolution_focused F q"
    using h Resolution_Call_Goal by (simp_all add: finite_focus_pending_focused)
  have "(e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
    using sup c unfolding resolution_supported_at_def by blast
  then show ?thesis by (simp add: Resolution_Call_Goal finite_goal_holds_def)
next
  case (Resolution_Material_Goal q r N)
  have c: "Resolution_Material_Goal q r N |\<in>| resolution_pending st" "resolution_focused F q"
    using h Resolution_Material_Goal by (simp_all add: finite_focus_pending_focused)
  have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) N)"
    using sup c unfolding resolution_supported_at_def by blast
  then show ?thesis by (simp add: Resolution_Material_Goal finite_goal_holds_def)
qed


lemma resolution_supported_at_barred_allI:
  assumes holds: "\<And>h. h |\<in>| resolution_pending s \<Longrightarrow> resolution_focused F (resolution_goal_position h) \<Longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    and placed: "finite_state_placed U s"
  shows "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>"
proof -
  have c: "(e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
    if "Resolution_Call_Goal q r e p |\<in>| resolution_pending s" "resolution_focused F q" for q r e p
    using holds[OF that(1)] that(2) by (simp add: finite_goal_holds_def)
  have m: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) N)"
    if "Resolution_Material_Goal q r N |\<in>| resolution_pending s" "resolution_focused F q" for q r N
    using holds[OF that(1)] that(2) by (simp add: finite_goal_holds_def)
  have b: "resolution_node_position nd |\<in>| fimage resolution_node_position (resolution_nodes s)"
    if "nd |\<in>| resolution_nodes s" for nd
    using that by (auto simp: resolution_fset_simps)
  from c m b placed show ?thesis unfolding resolution_supported_at_def finite_state_placed_def by blast
qed

subsection \<open>The committed goal stands alone under its position\<close>


lemma finite_committed_goal_alone:
  assumes I: "resolution_invariant P d t st" and g: "g |\<in>| resolution_pending st" "resolution_is_call g"
  shows "finite_focus_pending (Some (resolution_goal_position g)) st = {|g|}"
proof -
  let ?q = "resolution_goal_position g"
  have dist: "resolution_positions_distinct st" using I unfolding resolution_invariant_def by blast
  obtain q0 r0 e0 p0 where gc: "g = Resolution_Call_Goal q0 r0 e0 p0" using g(2) by (cases g) auto
  have unique_goal: "h = g" if h: "h |\<in>| resolution_pending st" "take (length ?q) (resolution_goal_position h) = ?q" for h
  proof (cases "resolution_goal_position h = ?q")
    case True
    then show ?thesis using dist h(1) g(1) unfolding resolution_positions_distinct_def by blast
  next
    case False
    let ?x = "resolution_goal_position h"
    have lt: "length ?q < length ?x"
    proof (rule ccontr)
      assume "\<not> length ?q < length ?x"
      then have "take (length ?q) ?x = ?x" by simp
      with h(2) False show False by simp
    qed
    have "resolution_before ?q ?x" using lt h(2) by (simp add: resolution_before_def)
    then obtain m' where m': "m' |\<in>| resolution_nodes st" "resolution_node_position m' = ?q"
      using resolution_goal_ancestor_node[OF I h(1)] by blast
    have "resolution_node_position m' \<noteq> q0"
      by (rule resolution_call_goal_no_node[OF I g(1)[unfolded gc] m'(1)])
    with m'(2) gc show ?thesis by simp
  qed
  have "h |\<in>| finite_focus_pending (Some ?q) st \<longleftrightarrow> h = g" for h
  proof
    assume "h |\<in>| finite_focus_pending (Some ?q) st"
    then have "h |\<in>| resolution_pending st" "take (length ?q) (resolution_goal_position h) = ?q"
      by (simp_all add: finite_focus_pending_def)
    then show "h = g" by (rule unique_goal)
  next
    assume "h = g"
    then show "h |\<in>| finite_focus_pending (Some ?q) st" using g(1) by (simp add: finite_focus_pending_def)
  qed
  then show ?thesis by (auto simp: fset_eq_iff)
qed

subsection \<open>Every found state of the sub-search is supported with its nodes barred\<close>

theorem finite_committed_found_supported:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and parent: "finite_goal_premise st (Resolution_Call_Goal q r e p)"
    and confined: "finite_registrations_confined \<kappa> F q st"
    and ctx: "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e p"
    and found: "s |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st)"
  shows "\<exists>\<theta>'. resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Call_Goal q r e p"
  let ?V = "finite_focus_variables q st"
  have Is: "resolution_invariant P d t s" and closed: "finite_focus_pending (Some q) s = {||}"
    using finite_committed_search_found[OF \<kappa> I found] by blast+
  have placed_st: "finite_state_placed (\<lambda>_. False) st" by (rule resolution_supported_at_placed[OF sup])
  have placed_s: "finite_state_placed (\<lambda>_. False) s" by (rule finite_committed_search_placed[OF \<kappa> I found placed_st])
  have in_s: "\<not> resolution_focused (Some q) (resolution_goal_position h)" if "h |\<in>| resolution_pending s" for h
  proof
    assume "resolution_focused (Some q) (resolution_goal_position h)"
    with that have "h |\<in>| finite_focus_pending (Some q) s" by (simp add: finite_focus_pending_focused)
    with closed show False by simp
  qed
  show ?thesis
  proof (cases "q = []")
    case True
    have none: "resolution_pending s = {||}" using in_s True by (auto simp: fset_eq_iff)
    have "resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>"
      by (rule resolution_supported_at_barred_allI) (simp_all add: none placed_s)
    then show ?thesis by blast
  next
    case False
    obtain np e0 p0 where np: "np |\<in>| resolution_nodes st" "resolution_node_position np = butlast q"
      and prem: "(last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
      using parent False unfolding finite_goal_premise_def by auto
    have posq: "resolution_node_position np @ [last q] = q" using np(2) False by simp
    have dist: "resolution_positions_distinct st" and nplaced: "resolution_nodes_placed P d t st"
      using I unfolding resolution_invariant_def by blast+
    have linked: "resolution_node_linked P st np" using nplaced np(1) unfolding resolution_nodes_placed_def by blast
    obtain \<beta> where bind: "resolution_node_bindings np =
        fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema np))"
      and prem\<beta>: "\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
        Resolution_Call_Goal (resolution_node_position np@[s]) (Some (resolution_node_site np,resolution_node_clause np,s)) e
            (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending st \<or>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=resolution_node_position np@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta> p)"
      using linked unfolding resolution_node_linked_def by blast
    have no_node_q: "resolution_node_position m \<noteq> q" if "m |\<in>| resolution_nodes st" for m
      by (rule resolution_call_goal_no_node[OF I g that])
    from prem\<beta> prem have alt: "Resolution_Call_Goal (resolution_node_position np@[last q])
        (Some (resolution_node_site np,resolution_node_clause np,last q)) e0 (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st \<or>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=resolution_node_position np@[last q] \<and>
        resolution_node_site m=e0 \<and> resolution_node_call m=finite_pattern_substitute \<beta> p0)" by blast
    have gq': "Resolution_Call_Goal q (Some (resolution_node_site np,resolution_node_clause np,last q)) e0
        (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st"
      using alt no_node_q unfolding posq by blast
    have "Resolution_Call_Goal q (Some (resolution_node_site np,resolution_node_clause np,last q)) e0
        (finite_pattern_substitute \<beta> p0) = ?g"
    proof -
      have "resolution_goal_position (Resolution_Call_Goal q (Some (resolution_node_site np,resolution_node_clause np,last q)) e0
          (finite_pattern_substitute \<beta> p0)) = resolution_goal_position ?g" by simp
      with dist gq' g show ?thesis unfolding resolution_positions_distinct_def by blast
    qed
    then have e0: "e0 = e" and p\<beta>: "finite_pattern_substitute \<beta> p0 = p" by simp_all
    obtain \<sigma> where
      fixed: "\<forall>z. resolution_placed st z \<longrightarrow> z \<notin> ?V \<longrightarrow>
        \<sigma> z = Finite_Variable z \<or> (finite_registered_at \<kappa> st z \<and> (\<exists>v. \<sigma> z = finite_exact_term_pattern v))"
      and range: "\<forall>w. fset (finite_pattern_variables (\<sigma> w)) \<subseteq> insert w (?V \<union> {z. \<not> resolution_placed st z})"
      and outg: "finite_outside_pending q s = fimage (resolution_goal_substitute \<sigma>) (finite_outside_pending q st)"
      and outn: "finite_outside_nodes q s = fimage (resolution_node_substitute \<sigma>) (finite_outside_nodes q st)"
      using finite_committed_search_frame[OF \<kappa> I found] unfolding finite_focus_frame_def by blast
    have alone: "finite_focus_pending (Some q) st = {|?g|}"
      using finite_committed_goal_alone[OF I g] by simp
    have V: "?V = fset (finite_pattern_variables p)" by (simp add: finite_focus_variables_def alone)
    have npo: "\<not> resolution_focused (Some q) (resolution_node_position np)"
    proof
      assume "resolution_focused (Some q) (resolution_node_position np)"
      then have "take (length q) (butlast q) = q" using np(2) by simp
      moreover have "take (length q) (butlast q) = butlast q" by simp
      ultimately have "length (butlast q) = length q" by simp
      moreover have "length (butlast q) = length q - 1" by (rule length_butlast)
      moreover have "length q \<noteq> 0" using False by simp
      ultimately show False by arith
    qed
    let ?np = "resolution_node_substitute \<sigma> np"
    have "np |\<in>| finite_outside_nodes q st" using np(1) npo by (simp add: finite_outside_nodes_def)
    then have "?np |\<in>| finite_outside_nodes q s" unfolding outn by (auto simp: resolution_fset_simps)
    then have np's: "?np |\<in>| resolution_nodes s" by (simp add: finite_outside_nodes_def)
    have fpos: "resolution_node_position ?np = resolution_node_position np"
      and fsch: "resolution_node_schema ?np = resolution_node_schema np"
      and fbind: "resolution_node_bindings ?np =
        fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (resolution_node_bindings np)"
      by (cases np; simp)+
    have linked': "resolution_node_linked P s ?np"
      using Is np's unfolding resolution_invariant_def resolution_nodes_placed_def by blast
    obtain \<beta>' where bind': "resolution_node_bindings ?np =
        fimage (\<lambda>a. (a,\<beta>' a)) (finite_schema_variables (resolution_node_schema ?np))"
      and prem\<beta>': "\<forall>k e p. (k,e,p) |\<in>| finite_schema_premises (resolution_node_schema ?np) \<longrightarrow>
        Resolution_Call_Goal (resolution_node_position ?np@[k]) (Some (resolution_node_site ?np,resolution_node_clause ?np,k)) e
            (finite_pattern_substitute \<beta>' p) |\<in>| resolution_pending s \<or>
        (\<exists>m. m |\<in>| resolution_nodes s \<and> resolution_node_position m=resolution_node_position ?np@[k] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta>' p)"
      using linked' unfolding resolution_node_linked_def by blast
    let ?SV = "finite_schema_variables (resolution_node_schema np)"
    have b': "resolution_node_bindings ?np = fimage (\<lambda>a. (a,finite_pattern_substitute \<sigma> (\<beta> a))) ?SV"
    proof -
      have "resolution_node_bindings ?np =
          fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (fimage (\<lambda>a. (a,\<beta> a)) ?SV)"
        using fbind bind by simp
      then show ?thesis by (simp add: fset.map_comp comp_def)
    qed
    have eq: "fimage (\<lambda>a. (a,\<beta>' a)) ?SV = fimage (\<lambda>a. (a,finite_pattern_substitute \<sigma> (\<beta> a))) ?SV"
      using b' bind' fsch by simp
    have agree: "\<beta>' a = finite_pattern_substitute \<sigma> (\<beta> a)" if a: "a |\<in>| ?SV" for a
    proof -
      have "(a,\<beta>' a) |\<in>| fimage (\<lambda>a. (a,\<beta>' a)) ?SV" using a by (auto simp: resolution_fset_simps)
      then have "(a,\<beta>' a) |\<in>| fimage (\<lambda>a. (a,finite_pattern_substitute \<sigma> (\<beta> a))) ?SV" by (simp only: eq)
      then show ?thesis by (auto simp: resolution_fset_simps)
    qed
    have p0v: "a |\<in>| ?SV" if "a |\<in>| finite_pattern_variables p0" for a
      using prem that by (force simp: finite_schema_variables_def resolution_fset_simps)
    have \<beta>'p0: "finite_pattern_substitute \<beta>' p0 = finite_pattern_substitute \<sigma> p"
    proof -
      have "finite_pattern_substitute \<beta>' p0 = finite_pattern_substitute (\<lambda>a. finite_pattern_substitute \<sigma> (\<beta> a)) p0"
        by (rule finite_pattern_substitute_cong) (use agree p0v in blast)
      also have "\<dots> = finite_pattern_substitute \<sigma> (finite_pattern_substitute \<beta> p0)"
        by (simp add: finite_pattern_substitute_composes)
      finally show ?thesis using p\<beta> by simp
    qed
    have prem': "(last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema ?np)" using prem fsch by simp
    have alt': "Resolution_Call_Goal (resolution_node_position ?np@[last q])
        (Some (resolution_node_site ?np,resolution_node_clause ?np,last q)) e0 (finite_pattern_substitute \<beta>' p0) |\<in>| resolution_pending s \<or>
      (\<exists>m. m |\<in>| resolution_nodes s \<and> resolution_node_position m=resolution_node_position ?np@[last q] \<and>
        resolution_node_site m=e0 \<and> resolution_node_call m=finite_pattern_substitute \<beta>' p0)"
      using prem\<beta>' prem' by blast
    have posq': "resolution_node_position ?np@[last q] = q" using fpos posq by simp
    have not_pending: "Resolution_Call_Goal q (Some (resolution_node_site ?np,resolution_node_clause ?np,last q)) e0
        (finite_pattern_substitute \<beta>' p0) |\<notin>| resolution_pending s"
    proof
      assume "Resolution_Call_Goal q (Some (resolution_node_site ?np,resolution_node_clause ?np,last q)) e0
          (finite_pattern_substitute \<beta>' p0) |\<in>| resolution_pending s"
      from in_s[OF this] show False by simp
    qed
    obtain m where m: "m |\<in>| resolution_nodes s" "resolution_node_position m = q" "resolution_node_site m = e"
      "resolution_node_call m = finite_pattern_substitute \<sigma> p"
      using alt' not_pending unfolding posq' e0 \<beta>'p0 by blast
    have Ip: "resolution_pattern_invariant P d (finite_exact_term_pattern t) s"
      using Is by (simp add: resolution_invariant_pattern)
    have under: "resolution_pending_under s (resolution_node_position m) = {||}"
      using closed m(2) by (simp add: finite_focus_pending_def)
    have le: "fcard (resolution_subtree (resolution_nodes s) m) \<le> fcard (resolution_nodes s)"
      by (rule fcard_mono) auto
    have chk: "finite_checks_schema_proof P (finite_node_proof (fcard (resolution_nodes s)) (resolution_nodes s) m) e
        (finite_residual_term (finite_pattern_substitute \<sigma> p))"
      using finite_node_proof_subtree_accepted[OF Ip m(1) under le] unfolding m(3) m(4) .
    have ans: "(e,decode_finite_term (finite_residual_term (finite_pattern_substitute \<sigma> p))) \<in> ?M"
      using schema_proof_sound[OF chk[unfolded finite_checks_schema_proof_exact]] .
    define \<theta>2 where "\<theta>2 = (\<lambda>z. finite_residual_term (\<sigma> z))"
    have ans2: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M"
      using ans unfolding \<theta>2_def resolution_value_residual .
    obtain \<theta>1 where t1: "\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z"
      and hold1: "\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds ?M \<theta>1 h"
      using ctx[unfolded finite_exchange_context_def, rule_format, OF ans2] by blast
    define \<theta>' where "\<theta>' = (\<lambda>z. if z \<in> ?V \<or> \<not> resolution_placed st z then Finite_Payload [] else \<theta>1 z)"
    have key: "resolution_value \<theta>' (\<sigma> z) = \<theta>1 z"
      if pl: "resolution_placed st z" and reg: "z \<notin> ?V \<Longrightarrow> \<not> finite_registered_at \<kappa> st z" for z
    proof (cases "z \<in> ?V")
      case True
      have blank: "\<theta>' w = Finite_Payload []" if "w |\<in>| finite_pattern_variables (\<sigma> z)" for w
        using range[rule_format, of z] that True unfolding \<theta>'_def by auto
      have "resolution_value \<theta>' (\<sigma> z) = finite_residual_term (\<sigma> z)" by (rule resolution_value_blank) (rule blank)
      also have "\<dots> = \<theta>2 z" by (simp add: \<theta>2_def)
      also have "\<dots> = \<theta>1 z"
      proof -
        have "z |\<in>| finite_pattern_variables p" using True V by simp
        then have "\<theta>1 z = \<theta>2 z" using t1 by blast
        then show ?thesis by (rule sym)
      qed
      finally show ?thesis .
    next
      case False
      with pl reg fixed have "\<sigma> z = Finite_Variable z" by blast
      then show ?thesis using False pl by (simp add: \<theta>'_def resolution_value_def)
    qed
    have hs: "finite_goal_holds ?M \<theta>' h"
      if h: "h |\<in>| resolution_pending s" "resolution_focused F (resolution_goal_position h)" for h
    proof -
      have "h |\<in>| finite_outside_pending q s" using h(1) in_s[OF h(1)] by (simp add: finite_outside_pending_def)
      then obtain h0 where h0: "h0 |\<in>| finite_outside_pending q st" and hh: "h = resolution_goal_substitute \<sigma> h0"
        unfolding outg by (auto simp: resolution_fset_simps)
      have pos: "resolution_goal_position h0 = resolution_goal_position h" by (simp add: hh resolution_goal_substitute_fields)
      have h0st: "h0 |\<in>| resolution_pending st" "\<not> resolution_focused (Some q) (resolution_goal_position h0)"
        using h0 by (simp_all add: finite_outside_pending_def)
      have h0F: "h0 |\<in>| finite_focus_pending F st" using h0st(1) h(2) pos by (simp add: finite_focus_pending_focused)
      have held: "finite_goal_holds ?M \<theta>1 h0" using hold1 h0F h0st(2) by blast
      have agree: "resolution_value \<theta>' (\<sigma> z) = \<theta>1 z" if z: "z |\<in>| resolution_goal_variables h0" for z
      proof (rule key)
        show "resolution_placed st z" using placed_st h0st(1) z unfolding finite_state_placed_def by blast
        show "\<not> finite_registered_at \<kappa> st z" if "z \<notin> ?V"
          using confined h0F h0st(2) z unfolding finite_registrations_confined_def by blast
      qed
      have "finite_goal_holds ?M (\<lambda>z. resolution_value \<theta>' (\<sigma> z)) h0"
        using held finite_goal_holds_cong[of h0 "\<lambda>z. resolution_value \<theta>' (\<sigma> z)" \<theta>1 ?M] agree by blast
      then show ?thesis by (simp add: hh finite_goal_holds_substitute)
    qed
    have "resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
      by (rule resolution_supported_at_barred_allI[OF hs placed_s])
    then show ?thesis by blast
  qed
qed

corollary finite_committed_exchange_context:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and parent: "finite_goal_premise st (Resolution_Call_Goal q r e p)"
    and confined: "finite_registrations_confined \<kappa> F q st"
    and ctx: "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e p"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some q) B st)"
  shows "\<exists>s \<theta>'. s |\<in>| finite_kept q (resolution_found (finite_committed_search \<kappa> K P n (Some q) B st)) \<and>
    resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  let ?R = "resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n (Some q) B st)"
  have s0': "s0 |\<in>| ?R" using s0 by (simp add: finite_committed_search_def)
  have s0'': "s0 |\<in>| resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n
      (Some (resolution_goal_position (Resolution_Call_Goal q r e p))) B st)" using s0' by simp
  have call: "resolution_is_call (Resolution_Call_Goal q r e p)" by simp
  have "finite_kept (resolution_goal_position (Resolution_Call_Goal q r e p))
      (resolution_found (finite_committed_search_by (finite_resolution_select \<kappa> P) \<kappa> K P n
        (Some (resolution_goal_position (Resolution_Call_Goal q r e p))) B st)) \<noteq> {||}"
    by (rule finite_committed_kept_nonempty[OF \<kappa> I g call s0''])
  then have "finite_kept q ?R \<noteq> {||}" by simp
  then obtain s where s: "s |\<in>| finite_kept q ?R" by auto
  have found: "s |\<in>| ?R" using finite_kept_subset s by blast
  obtain \<theta>' where "resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
    using finite_committed_found_supported[OF \<kappa> I sup g parent confined ctx found] by blast
  then show ?thesis using s by (auto simp: finite_committed_search_def)
qed

section \<open>The direct producer, over a view\<close>

text \<open>
  A view reads a term as a pair of an input and an output (@{typ "factor_term \<Rightarrow> (factor_term \<times> factor_term) option"}),
  and a pattern as its two parts, whose values under every grounding are the view's of the pattern's value
  (@{text finite_view_parts}). A producer discharged at a view has corresponding outputs at every two answers whose
  views share the input; a consumer discharged at a view holds at two terms whose views share the input and whose
  outputs correspond, or at neither. The context of a committed goal whose view has a ground input, whose producer is
  so discharged and whose every other goal outside the position either holds none of the output's variables or is a
  consumer holding the output pattern itself beside an input sharing none, follows (@{text finite_direct_context}).
  The pair and swap views are R5's producer and its right- and left-side consumers (@{text finite_view_parts_pair},
  @{text finite_view_parts_swap}, @{text producer_discharged_view}, @{text consumer_discharged_pair_view},
  @{text consumer_discharged_swap_view}); R5d's views instantiate the same lemma.
\<close>

definition finite_view_parts ::
    "(factor_term \<Rightarrow> (factor_term \<times> factor_term) option) \<Rightarrow> 'v finite_term_pattern \<Rightarrow> 'v finite_term_pattern \<Rightarrow>
      'v finite_term_pattern \<Rightarrow> bool" where
  "finite_view_parts view p pi po \<longleftrightarrow>
    finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po \<and>
    (\<forall>\<theta>. view (decode_finite_term (resolution_value \<theta> p)) =
      Some (decode_finite_term (resolution_value \<theta> pi),decode_finite_term (resolution_value \<theta> po)))"

definition view_producer_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> (factor_term \<Rightarrow> (factor_term \<times> factor_term) option) \<Rightarrow>
      (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "view_producer_discharged M d view corr \<longleftrightarrow> (\<forall>a b u v v'. (d,a) \<in> M \<longrightarrow> (d,b) \<in> M \<longrightarrow>
    view a = Some (u,v) \<longrightarrow> view b = Some (u,v') \<longrightarrow> corr v v')"

definition view_consumer_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> (factor_term \<Rightarrow> (factor_term \<times> factor_term) option) \<Rightarrow>
      (factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "view_consumer_discharged M e view corr \<longleftrightarrow> (\<forall>a b u v v'. view a = Some (u,v) \<longrightarrow> view b = Some (u,v') \<longrightarrow>
    corr v v' \<longrightarrow> ((e,a) \<in> M \<longleftrightarrow> (e,b) \<in> M))"

theorem finite_direct_context:
  fixes H :: "('a,'s,'d,'c) resolution_goal set"
  assumes parts: "finite_view_parts view p pi po" and ground: "finite_pattern_variables pi = {||}"
    and producer: "view_producer_discharged M e view corr"
    and holds: "(e,decode_finite_term (resolution_value \<theta> p)) \<in> M"
    and others: "\<And>h. h \<in> H \<Longrightarrow> finite_goal_holds M \<theta> h"
    and consumers: "\<And>h. h \<in> H \<Longrightarrow> resolution_goal_variables h |\<inter>| finite_pattern_variables po = {||} \<or>
      (\<exists>q' r' e' p' view' ci. h = Resolution_Call_Goal q' r' e' p' \<and> finite_view_parts view' p' ci po \<and>
        finite_pattern_variables ci |\<inter>| finite_pattern_variables po = {||} \<and> view_consumer_discharged M e' view' corr)"
    and new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> M"
  shows "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and> (\<forall>h. h \<in> H \<longrightarrow> finite_goal_holds M \<theta>1 h)"
proof -
  define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables po then \<theta>2 z else \<theta> z)"
  have pv: "finite_pattern_variables p = finite_pattern_variables po"
    using parts ground unfolding finite_view_parts_def by simp
  have v1: "view (decode_finite_term (resolution_value \<theta> p)) =
      Some (decode_finite_term (resolution_value \<theta> pi),decode_finite_term (resolution_value \<theta> po))"
    and v2: "view (decode_finite_term (resolution_value \<theta>2 p)) =
      Some (decode_finite_term (resolution_value \<theta>2 pi),decode_finite_term (resolution_value \<theta>2 po))"
    using parts unfolding finite_view_parts_def by blast+
  have pi_eq: "resolution_value \<theta>2 pi = resolution_value \<theta> pi" by (rule resolution_value_cong) (simp add: ground)
  have c: "corr (decode_finite_term (resolution_value \<theta> po)) (decode_finite_term (resolution_value \<theta>2 po))"
    using producer[unfolded view_producer_discharged_def, rule_format, OF holds new v1 v2[unfolded pi_eq]] .
  show ?thesis
  proof (intro exI conjI allI impI)
    fix z assume "z |\<in>| finite_pattern_variables p"
    then show "\<theta>1 z = \<theta>2 z" using pv by (simp add: \<theta>1_def)
  next
    fix h assume h: "h \<in> H"
    from consumers[OF h] show "finite_goal_holds M \<theta>1 h"
    proof (elim disjE exE conjE)
      assume dis: "resolution_goal_variables h |\<inter>| finite_pattern_variables po = {||}"
      have "finite_goal_holds M \<theta>1 h \<longleftrightarrow> finite_goal_holds M \<theta> h"
        by (rule finite_goal_holds_cong) (use dis in \<open>auto simp: \<theta>1_def fset_eq_iff\<close>)
      then show ?thesis using others[OF h] by simp
    next
      fix q' r' e' p' view' ci
      assume hq: "h = Resolution_Call_Goal q' r' e' p'" and parts': "finite_view_parts view' p' ci po"
        and dis: "finite_pattern_variables ci |\<inter>| finite_pattern_variables po = {||}"
        and cons: "view_consumer_discharged M e' view' corr"
      have w1: "view' (decode_finite_term (resolution_value \<theta> p')) =
          Some (decode_finite_term (resolution_value \<theta> ci),decode_finite_term (resolution_value \<theta> po))"
        and w2: "view' (decode_finite_term (resolution_value \<theta>1 p')) =
          Some (decode_finite_term (resolution_value \<theta>1 ci),decode_finite_term (resolution_value \<theta>1 po))"
        using parts' unfolding finite_view_parts_def by blast+
      have ci_eq: "resolution_value \<theta>1 ci = resolution_value \<theta> ci"
        by (rule resolution_value_cong) (use dis in \<open>auto simp: \<theta>1_def fset_eq_iff\<close>)
      have po_eq: "resolution_value \<theta>1 po = resolution_value \<theta>2 po" by (rule resolution_value_cong) (simp add: \<theta>1_def)
      have iff: "(e',decode_finite_term (resolution_value \<theta> p')) \<in> M \<longleftrightarrow> (e',decode_finite_term (resolution_value \<theta>1 p')) \<in> M"
        using cons[unfolded view_consumer_discharged_def, rule_format, OF w1 w2[unfolded ci_eq po_eq] c] .
      have "(e',decode_finite_term (resolution_value \<theta> p')) \<in> M" using others[OF h] hq by (simp add: finite_goal_holds_def)
      then show ?thesis using iff hq by (simp add: finite_goal_holds_def)
    qed
  qed
qed

subsection \<open>R5's producer and consumers are the pair and swap views\<close>

definition pair_view :: "factor_term \<Rightarrow> (factor_term \<times> factor_term) option" where
  "pair_view t = (case t of Pair_Term a b \<Rightarrow> Some (a,b) | _ \<Rightarrow> None)"

definition swap_view :: "factor_term \<Rightarrow> (factor_term \<times> factor_term) option" where
  "swap_view t = (case t of Pair_Term a b \<Rightarrow> Some (b,a) | _ \<Rightarrow> None)"

lemma pair_view_some: "pair_view t = Some (u,v) \<longleftrightarrow> t = Pair_Term u v"
  by (cases t) (auto simp: pair_view_def)

lemma swap_view_some: "swap_view t = Some (u,v) \<longleftrightarrow> t = Pair_Term v u"
  by (cases t) (auto simp: swap_view_def)

lemma finite_view_parts_pair: "finite_view_parts pair_view (Finite_Pattern_Pair x y) x y"
  by (simp add: finite_view_parts_def pair_view_def resolution_value_def)

lemma finite_view_parts_swap: "finite_view_parts swap_view (Finite_Pattern_Pair x y) y x"
  by (auto simp: finite_view_parts_def swap_view_def resolution_value_def)

lemma producer_discharged_view:
  assumes "producer_discharged M d corr"
  shows "view_producer_discharged M d pair_view corr"
  unfolding view_producer_discharged_def
proof (intro allI impI)
  fix a b u v v' assume a: "(d,a) \<in> M" and b: "(d,b) \<in> M" and va: "pair_view a = Some (u,v)"
    and vb: "pair_view b = Some (u,v')"
  from va vb have "a = Pair_Term u v" "b = Pair_Term u v'" by (simp_all add: pair_view_some)
  with a b assms show "corr v v'" unfolding producer_discharged_def by blast
qed

lemma consumer_discharged_pair_view:
  assumes "consumer_discharged M e True corr"
  shows "view_consumer_discharged M e pair_view corr"
  unfolding view_consumer_discharged_def
proof (intro allI impI)
  fix a b u v v' assume va: "pair_view a = Some (u,v)" and vb: "pair_view b = Some (u,v')" and c: "corr v v'"
  have k: "(e,consumer_argument True u v) \<in> M \<longleftrightarrow> (e,consumer_argument True u v') \<in> M"
    using assms c unfolding consumer_discharged_def by blast
  from va vb have "a = Pair_Term u v" "b = Pair_Term u v'" by (simp_all add: pair_view_some)
  then show "(e,a) \<in> M \<longleftrightarrow> (e,b) \<in> M" using k by (simp add: consumer_argument_def)
qed

lemma consumer_discharged_swap_view:
  assumes "consumer_discharged M e False corr"
  shows "view_consumer_discharged M e swap_view corr"
  unfolding view_consumer_discharged_def
proof (intro allI impI)
  fix a b u v v' assume va: "swap_view a = Some (u,v)" and vb: "swap_view b = Some (u,v')" and c: "corr v v'"
  have k: "(e,consumer_argument False u v) \<in> M \<longleftrightarrow> (e,consumer_argument False u v') \<in> M"
    using assms c unfolding consumer_discharged_def by blast
  from va vb have "a = Pair_Term v u" "b = Pair_Term v' u" by (simp_all add: swap_view_some)
  then show "(e,a) \<in> M \<longleftrightarrow> (e,b) \<in> M" using k by (simp add: consumer_argument_def)
qed

subsection \<open>R5's direct commitment discharges the exchange\<close>

lemma finite_direct_commitment_context:
  assumes discharged: "declarations_discharged M D corr"
    and direct: "finite_direct_commitment D F st (Resolution_Call_Goal q r e p)"
    and holds: "(e,decode_finite_term (resolution_value \<theta> p)) \<in> M"
    and others: "\<And>h. h |\<in>| finite_focus_pending F st \<Longrightarrow> h \<noteq> Resolution_Call_Goal q r e p \<Longrightarrow> finite_goal_holds M \<theta> h"
    and new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> M"
  shows "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<and> h \<noteq> Resolution_Call_Goal q r e p \<longrightarrow> finite_goal_holds M \<theta>1 h)"
proof -
  let ?g = "Resolution_Call_Goal q r e p"
  obtain x y where p: "p = Finite_Pattern_Pair x y"
    using direct by (cases p) (simp_all add: finite_direct_commitment_def)
  have prod: "e |\<in>| declared_producers D" and ground: "finite_pattern_variables x = {||}"
    and holders: "fBall (finite_focus_pending F st) (\<lambda>h. h = ?g \<or>
      resolution_goal_variables h |\<inter>| finite_pattern_variables y = {||} \<or> finite_output_consumer D e y h)"
    using direct unfolding p by (simp_all add: finite_direct_commitment_def)
  have pd: "producer_discharged M e (corr e)" using discharged prod unfolding declarations_discharged_def by blast
  have cd: "consumer_discharged M e' b (corr e)" if "(e,e',b) |\<in>| declared_consumers D" for e' b
    using discharged that unfolding declarations_discharged_def by blast
  define H where "H = {h. h |\<in>| finite_focus_pending F st \<and> h \<noteq> ?g}"
  have "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and> (\<forall>h. h \<in> H \<longrightarrow> finite_goal_holds M \<theta>1 h)"
  proof (rule finite_direct_context[where view=pair_view and pi=x and po=y and corr="corr e"])
    show "finite_view_parts pair_view p x y" unfolding p by (rule finite_view_parts_pair)
    show "finite_pattern_variables x = {||}" by (rule ground)
    show "view_producer_discharged M e pair_view (corr e)" by (rule producer_discharged_view[OF pd])
    show "(e,decode_finite_term (resolution_value \<theta> p)) \<in> M" by (rule holds)
    show "finite_goal_holds M \<theta> h" if "h \<in> H" for h using others that unfolding H_def by blast
    show "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> M" by (rule new)
    show "resolution_goal_variables h |\<inter>| finite_pattern_variables y = {||} \<or>
      (\<exists>q' r' e' p' view' ci. h = Resolution_Call_Goal q' r' e' p' \<and> finite_view_parts view' p' ci y \<and>
        finite_pattern_variables ci |\<inter>| finite_pattern_variables y = {||} \<and> view_consumer_discharged M e' view' (corr e))"
      if h: "h \<in> H" for h
    proof -
      from h have hF: "h |\<in>| finite_focus_pending F st" and hg: "h \<noteq> ?g" unfolding H_def by simp_all
      have "h = ?g \<or> resolution_goal_variables h |\<inter>| finite_pattern_variables y = {||} \<or> finite_output_consumer D e y h"
        using holders hF by blast
      with hg have "resolution_goal_variables h |\<inter>| finite_pattern_variables y = {||} \<or> finite_output_consumer D e y h"
        by blast
      then show ?thesis
      proof
        assume c: "finite_output_consumer D e y h"
        obtain q' r' e' x' z where hq: "h = Resolution_Call_Goal q' r' e' (Finite_Pattern_Pair x' z)"
          and alt: "((e,e',True) |\<in>| declared_consumers D \<and> z = y \<and>
              finite_pattern_variables x' |\<inter>| finite_pattern_variables y = {||}) \<or>
            ((e,e',False) |\<in>| declared_consumers D \<and> x' = y \<and>
              finite_pattern_variables z |\<inter>| finite_pattern_variables y = {||})"
          using c by (auto simp: finite_output_consumer_def split: resolution_goal.splits finite_term_pattern.splits)
        from alt show ?thesis
        proof
          assume a: "(e,e',True) |\<in>| declared_consumers D \<and> z = y \<and>
            finite_pattern_variables x' |\<inter>| finite_pattern_variables y = {||}"
          have zy: "z = y" using a by blast
          have parts': "finite_view_parts pair_view (Finite_Pattern_Pair x' z) x' y"
            unfolding zy by (rule finite_view_parts_pair)
          have ec: "(e,e',True) |\<in>| declared_consumers D" using a by (elim conjE)
          have cons': "view_consumer_discharged M e' pair_view (corr e)"
            by (rule consumer_discharged_pair_view[OF cd[OF ec]])
          have dis': "finite_pattern_variables x' |\<inter>| finite_pattern_variables y = {||}" using a by blast
          show ?thesis
            by (rule disjI2, rule exI[of _ q'], rule exI[of _ r'], rule exI[of _ e'],
              rule exI[of _ "Finite_Pattern_Pair x' z"], rule exI[of _ pair_view], rule exI[of _ x'])
              (intro conjI hq parts' dis' cons')
        next
          assume a: "(e,e',False) |\<in>| declared_consumers D \<and> x' = y \<and>
            finite_pattern_variables z |\<inter>| finite_pattern_variables y = {||}"
          have xy: "x' = y" using a by blast
          have parts': "finite_view_parts swap_view (Finite_Pattern_Pair x' z) z y"
            unfolding xy by (rule finite_view_parts_swap)
          have ec: "(e,e',False) |\<in>| declared_consumers D" using a by (elim conjE)
          have cons': "view_consumer_discharged M e' swap_view (corr e)"
            by (rule consumer_discharged_swap_view[OF cd[OF ec]])
          have dis': "finite_pattern_variables z |\<inter>| finite_pattern_variables y = {||}" using a by blast
          show ?thesis
            by (rule disjI2, rule exI[of _ q'], rule exI[of _ r'], rule exI[of _ e'],
              rule exI[of _ "Finite_Pattern_Pair x' z"], rule exI[of _ swap_view], rule exI[of _ z])
              (intro conjI hq parts' dis' cons')
        qed
      qed blast
    qed
  qed
  then show ?thesis unfolding H_def by blast
qed

theorem finite_direct_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and direct: "finite_direct_commitment D F st g"
    and parent: "finite_goal_premise st g"
    and confined: "finite_registrations_confined \<kappa> F (resolution_goal_position g) st"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)"
  shows "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g)
      (resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)) \<and>
    resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  obtain q r e p where gq: "g = Resolution_Call_Goal q r e p"
    using direct by (cases g) (simp_all add: finite_direct_commitment_def)
  have gp: "g |\<in>| resolution_pending st" "resolution_focused F q"
    using gF gq by (simp_all add: finite_focus_pending_focused)
  have holds: "(e,decode_finite_term (resolution_value \<theta> p)) \<in> ?M"
    using resolution_supported_at_holds[OF sup gF] gq by (simp add: finite_goal_holds_def)
  have others: "finite_goal_holds ?M \<theta> h" if "h |\<in>| finite_focus_pending F st" "h \<noteq> Resolution_Call_Goal q r e p" for h
    using resolution_supported_at_holds[OF sup that(1)] .
  have ctx: "finite_exchange_context ?M F q st e p"
    unfolding finite_exchange_context_def
  proof (intro allI impI)
    fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M"
    obtain \<theta>1 where t: "\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z"
      and hh: "\<forall>h. h |\<in>| finite_focus_pending F st \<and> h \<noteq> Resolution_Call_Goal q r e p \<longrightarrow> finite_goal_holds ?M \<theta>1 h"
      using finite_direct_commitment_context[OF discharged direct[unfolded gq] holds others new] by blast
    have "finite_goal_holds ?M \<theta>1 h"
      if "h |\<in>| finite_focus_pending F st" "\<not> resolution_focused (Some q) (resolution_goal_position h)" for h
    proof -
      have "h \<noteq> Resolution_Call_Goal q r e p" using that(2) by auto
      then show ?thesis using hh that(1) by blast
    qed
    then show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h)"
      using t by blast
  qed
  have gpos: "resolution_goal_position g = q" by (simp add: gq)
  have g': "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" using gp(1) by (simp only: gq)
  have parent': "finite_goal_premise st (Resolution_Call_Goal q r e p)" using parent by (simp only: gq)
  have confined': "finite_registrations_confined \<kappa> F q st" using confined by (simp only: gpos)
  have s0': "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some q) B st)" using s0 by (simp only: gpos)
  show ?thesis unfolding gpos by (rule finite_committed_exchange_context[OF \<kappa> I sup g' parent' confined' ctx s0'])
qed

end
