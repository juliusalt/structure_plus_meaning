theory Factor_Resolution_Socket_Discharges
  imports Factor_Resolution_Material_Discharge
begin

text \<open>
  The socket kinds' discharges of #565's exchange premise (R5c\<Zprime>\<Zprime>\<Zprime>\<Zprime>a, task 630, of DECISIONS.md "The native evaluator
  constructs the missing witnesses by resolution", its section "Committed choice, for refusals"), stated over the socket's
  views (task 674, its addition "The given's remaining producers: views, carriers and narrowed sockets", (a)): at a socket
  declared with the kept head, at one declared without it, and at an inner commitment, the kept head's or the free
  socket's at a nested focus. The socket's premise is read at the premise's view (@{text finite_socket_premise}), the
  parent's head at the head's view (@{text head_kept_input}, @{text head_kept_variables}, @{text head_kept_whole}) and the
  free socket's variant test at the parent's viewed output (@{text finite_parent_output_parts}). A socket's exchange
  rebuilds its parent clause's instance from the socket's obligation (@{const socket_discharged}): the parent clause's
  instance under the support is true from its pending and closed premises (@{text finite_instance_clause_true},
  @{text finite_parent_instance_true}), the obligation gives a true instance with the new answer keeping the socket's
  inputs (@{text finite_socket_new_instance}), and the goals under the parent are read as that instance's premises
  (@{text finite_parent_exchange_holds}), every other goal keeping its values. What the exchange needs of the state is the
  parent context (@{const finite_parent_context}, correction (9)): each premise pending as its instance or closed with a
  ground instance among the socket's inputs, every pending goal under the parent one of the instances, each premise-only
  variable free or among the inputs with a ground binding, none held by the parent's call; at a free socket the call's
  viewed input sharing no variable with its output. The commitment test checks it where it commits
  (@{text finite_declared_socket_context}), so the exchange premise holds with no hypothesis on the state
  (@{text finite_declared_commitment_exchanges}); the sockets' exchange holds at any discharged declarations, the
  contexts taken at the socket's declared views, and at every socket commitment of the test, including a socket whose
  closed siblings hold only its inputs (correction (9)). At a frame (B2a of correction (10)) the parent context, the
  socket's premise, the parent's instance and the exchanged valuation are read at @{const finite_framed_parent_context},
  and the socket contexts are one context over a class of the socket's output (@{text finite_framed_call_context}), its
  valuation set head output by head output; today's contexts are its instances at the default frame and the class of
  every term, and today's exchange is the framed test's (@{text finite_framed_commitment_exchanges}) at no frames.
\<close>

section \<open>Values of decoded patterns\<close>

lemma resolution_value_substitute_decoded:
  "decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p)) =
    evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta> (\<beta> a))) (decode_finite_pattern p)"
  by (simp add: resolution_value_composes decode_resolution_value)

declare resolution_value_variable [simp]

lemma resolution_value_pair [simp]:
  "resolution_value \<theta> (Finite_Pattern_Pair a b) = Finite_Pair (resolution_value \<theta> a) (resolution_value \<theta> b)"
  by (simp add: resolution_value_def)

lemma finite_pattern_substitute_variable:
  "c |\<in>| finite_pattern_variables p \<Longrightarrow> z |\<in>| finite_pattern_variables (\<sigma> c) \<Longrightarrow>
    z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)"
  by (induction p) auto

lemma finite_material_ground_substitute:
  "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
      (finite_material_pattern_substitute \<beta> N)) \<longleftrightarrow>
    evaluate_material_satisfaction (\<lambda>a. decode_finite_term (resolution_value \<theta> (\<beta> a))) (decode_finite_material N)"
  by (simp add: finite_material_ground_satisfied_def finite_material_pattern_substitute_def resolution_value_substitute
    finite_exact_term_pattern_eq_iff finite_material_observation_correct resolution_value_substitute_decoded
    decode_finite_material_def)

lemma evaluate_material_satisfaction_cong:
  assumes "\<And>a. a \<in> material_variables N \<Longrightarrow> f a = g a"
  shows "evaluate_material_satisfaction f N \<longleftrightarrow> evaluate_material_satisfaction g N"
proof -
  have "evaluate_pattern f p = evaluate_pattern g p" if "p \<in> set (material_fields N)" for p
    by (rule evaluate_pattern_cong) (use assms that in \<open>auto simp: material_variables_def\<close>)
  then show ?thesis by (simp add: material_fields_def)
qed

lemma evaluate_material_variables_formed:
  assumes sat: "evaluate_material_satisfaction h N" and a: "a \<in> material_variables N"
  shows "term_formed (h a)"
proof -
  obtain p where p: "p \<in> set (material_fields N)" "a \<in> pattern_variables p"
    using a by (auto simp: material_variables_def)
  have "term_formed (evaluate_pattern h p)"
    using material_observation_formed[OF sat] p(1) by (auto simp: material_fields_def)
  then show ?thesis using p(2) by (rule evaluate_pattern_variables_formed)
qed

section \<open>A parent clause's instance is true from its pending and closed premises\<close>

text \<open>
  The instance of a clause under bindings @{text \<beta>} and a support @{text \<theta>} reads each clause variable as the value of its
  binding; a variable whose value is not a formed term, which no premise holds, reads as the empty payload. Where every
  premise's instance holds and every material premise's is satisfied, the instance is a true instance of the clause, and
  at each premise variable it is the binding's value.
\<close>

definition finite_instance_valuation ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> 'v finite_term_pattern) \<Rightarrow> 'a \<Rightarrow> factor_term" where
  "finite_instance_valuation \<theta> \<beta> a = (if term_formed (decode_finite_term (resolution_value \<theta> (\<beta> a)))
    then decode_finite_term (resolution_value \<theta> (\<beta> a)) else Payload_Term [])"

lemma finite_instance_valuation_formed: "term_formed (finite_instance_valuation \<theta> \<beta> a)"
  by (simp add: finite_instance_valuation_def octets_formed_def)

theorem finite_instance_clause_true:
  assumes formed: "\<And>e u. (e,u) \<in> M \<Longrightarrow> term_formed u"
    and prem: "\<And>s e p. (s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p))) \<in> M"
    and mat: "\<And>s N. (s,N) |\<in>| finite_schema_materials S \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute \<beta> N))"
  shows "clause_true M (decode_finite_schema S) (finite_instance_valuation \<theta> \<beta>)"
    and "\<And>s e p c. (s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow> c |\<in>| finite_pattern_variables p \<Longrightarrow>
      finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    and "\<And>s N c. (s,N) |\<in>| finite_schema_materials S \<Longrightarrow> c |\<in>| finite_material_variables N \<Longrightarrow>
      finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
proof -
  let ?v = "\<lambda>a. decode_finite_term (resolution_value \<theta> (\<beta> a))"
  have ev: "(e,evaluate_pattern ?v (decode_finite_pattern p)) \<in> M" if "(s,e,p) |\<in>| finite_schema_premises S" for s e p
    using prem[OF that] by (simp add: resolution_value_substitute_decoded)
  have ms: "evaluate_material_satisfaction ?v (decode_finite_material N)"
    if "(s,N) |\<in>| finite_schema_materials S" for s N
    using mat[OF that] by (simp only: finite_material_ground_substitute)
  show pv: "finite_instance_valuation \<theta> \<beta> c = ?v c"
    if "(s,e,p) |\<in>| finite_schema_premises S" "c |\<in>| finite_pattern_variables p" for s e p c
  proof -
    have "term_formed (?v c)"
      by (rule evaluate_pattern_variables_formed[OF formed[OF ev[OF that(1)]]])
        (simp add: that(2) finite_pattern_variables_correct[symmetric])
    then show ?thesis by (simp add: finite_instance_valuation_def)
  qed
  show mv: "finite_instance_valuation \<theta> \<beta> c = ?v c"
    if "(s,N) |\<in>| finite_schema_materials S" "c |\<in>| finite_material_variables N" for s N c
  proof -
    have "term_formed (?v c)"
      by (rule evaluate_material_variables_formed[OF ms[OF that(1)]])
        (simp add: that(2) finite_material_variables_correct[symmetric])
    then show ?thesis by (simp add: finite_instance_valuation_def)
  qed
  show "clause_true M (decode_finite_schema S) (finite_instance_valuation \<theta> \<beta>)"
    unfolding clause_true_def
  proof (intro conjI allI impI ballI)
    fix a assume "a \<in> schema_variables (decode_finite_schema S)"
    show "term_formed (finite_instance_valuation \<theta> \<beta> a)" by (rule finite_instance_valuation_formed)
  next
    fix q d p' assume "(q,d,p') \<in> schema_premises (decode_finite_schema S)"
    then obtain p where p: "(q,d,p) |\<in>| finite_schema_premises S" "p' = decode_finite_pattern p"
      by (auto simp: decode_finite_call_pattern_def)
    have "evaluate_pattern (finite_instance_valuation \<theta> \<beta>) p' = evaluate_pattern ?v p'"
      unfolding p(2) by (rule evaluate_pattern_cong) (simp add: pv[OF p(1)] finite_pattern_variables_correct[symmetric])
    then show "(d,evaluate_pattern (finite_instance_valuation \<theta> \<beta>) p') \<in> M" using ev[OF p(1)] p(2) by simp
  next
    fix q N' assume "(q,N') \<in> schema_material_premises (decode_finite_schema S)"
    then obtain N where N: "(q,N) |\<in>| finite_schema_materials S" "N' = decode_finite_material N" by auto
    have "evaluate_material_satisfaction (finite_instance_valuation \<theta> \<beta>) N' \<longleftrightarrow> evaluate_material_satisfaction ?v N'"
      unfolding N(2) by (rule evaluate_material_satisfaction_cong)
        (simp add: mv[OF N(1)] finite_material_variables_correct[symmetric])
    then show "evaluate_material_satisfaction (finite_instance_valuation \<theta> \<beta>) N'" using ms[OF N(1)] N(2) by simp
  qed
qed

lemma resolution_focused_sibling:
  assumes focus: "resolution_focused F q" and nf: "F \<noteq> Some q" and q: "q \<noteq> []"
  shows "resolution_focused F (butlast q @ [s])"
proof (cases F)
  case (Some f)
  have f: "take (length f) q = f" using focus Some by simp
  have lt: "length f < length q"
  proof (rule ccontr)
    assume "\<not> length f < length q"
    then have "take (length f) q = q" by simp
    with f Some nf show False by simp
  qed
  have "take (length f) (butlast q @ [s]) = take (length f) (butlast q)"
    using lt q by (simp add: take_append)
  also have "\<dots> = take (length f) q"
  proof -
    have "length f \<le> length q - 1" using lt by arith
    then show ?thesis by (simp add: butlast_conv_take min_absorb1)
  qed
  finally show ?thesis using f Some by simp
qed simp

text \<open>
  At a state, the parent node's premises in its context are pending in the focus of the committed goal, which is one of
  them, or closed with a ground instance: the support makes each pending one true, the subtree acceptance or the parent's
  linkage each closed one (@{text finite_closed_premise_true}), and the instance of the parent clause under the parent's
  bindings is true.
\<close>

lemma finite_framed_instance_true:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and nf: "F \<noteq> Some (resolution_goal_position g)"
    and q: "resolution_goal_position g \<noteq> []" and np: "resolution_node_position np = butlast (resolution_goal_position g)"
    and ctx: "finite_framed_parent_context P C st np k"
  shows "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (finite_instance_valuation \<theta> (finite_node_binding np))"
    and "\<And>s e p c. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_pattern_variables p \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
    and "\<And>s N c. (s,N) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_material_variables N \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?q = "resolution_goal_position g"
  let ?S = "resolution_node_schema np"
  let ?pos = "resolution_node_position np"
  let ?\<beta> = "finite_node_binding np"
  have nd: "np |\<in>| resolution_nodes st" and closed: "finite_children_framed C st np k"
    using ctx by (simp_all add: finite_framed_parent_context_def)
  have focused: "resolution_focused F ?q" using gF by (simp add: finite_focus_pending_focused)
  have inF: "h |\<in>| finite_focus_pending F st"
    if "h |\<in>| resolution_pending st" "resolution_goal_position h = ?pos @ [s]" for h s
    using that resolution_focused_sibling[OF focused nf q, of s] np by (simp add: finite_focus_pending_focused)
  have formed: "\<And>e u. (e,u) \<in> ?M \<Longrightarrow> term_formed u"
  proof -
    fix e u assume "(e,u) \<in> ?M"
    from schema_call_formed_target[OF positive_meaning_formed[OF this]] show "term_formed u" by blast
  qed
  have prem_cases: "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site np,resolution_node_clause np,s)) e
      (finite_pattern_substitute ?\<beta> p) |\<in>| resolution_pending st \<or>
      (resolution_pending_under st (?pos@[s]) = {||} \<and> finite_pattern_variables (finite_pattern_substitute ?\<beta> p) = {||})"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using closed that unfolding finite_children_framed_def by auto
  have mat_cases: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site np,resolution_node_clause np,s)
      (finite_material_pattern_substitute ?\<beta> N) |\<in>| resolution_pending st \<or>
      resolution_pending_under st (?pos@[s]) = {||}"
    if "(s,N) |\<in>| finite_schema_materials ?S" for s N
    using closed that unfolding finite_children_framed_def by auto
  have prem: "(e0,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute ?\<beta> p0))) \<in> ?M"
    if m: "(s,e0,p0) |\<in>| finite_schema_premises ?S" for s e0 p0
    using prem_cases[OF m]
  proof
    assume h: "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site np,resolution_node_clause np,s)) e0
        (finite_pattern_substitute ?\<beta> p0) |\<in>| resolution_pending st"
    have "finite_goal_holds ?M \<theta> (Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site np,resolution_node_clause np,s)) e0
        (finite_pattern_substitute ?\<beta> p0))"
      by (rule resolution_supported_at_holds[OF sup inF[OF h]]) simp
    then show ?thesis by (simp add: finite_goal_holds_def)
  next
    assume c: "resolution_pending_under st (?pos@[s]) = {||} \<and>
      finite_pattern_variables (finite_pattern_substitute ?\<beta> p0) = {||}"
    show ?thesis by (rule finite_closed_premise_true(1)[OF I nd c[THEN conjunct1] m c[THEN conjunct2]])
  qed
  have mat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
      (finite_material_pattern_substitute ?\<beta> N0))"
    if m: "(s,N0) |\<in>| finite_schema_materials ?S" for s N0
    using mat_cases[OF m]
  proof
    assume h: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site np,resolution_node_clause np,s)
        (finite_material_pattern_substitute ?\<beta> N0) |\<in>| resolution_pending st"
    have "finite_goal_holds ?M \<theta> (Resolution_Material_Goal (?pos@[s]) (resolution_node_site np,resolution_node_clause np,s)
        (finite_material_pattern_substitute ?\<beta> N0))"
      by (rule resolution_supported_at_holds[OF sup inF[OF h]]) simp
    then show ?thesis by (simp add: finite_goal_holds_def)
  next
    assume c: "resolution_pending_under st (?pos@[s]) = {||}"
    show ?thesis by (rule finite_closed_premise_true(2)[OF I nd c m])
  qed
  show "clause_true ?M (decode_finite_schema ?S) (finite_instance_valuation \<theta> ?\<beta>)"
    by (rule finite_instance_clause_true(1); (erule formed | erule prem | erule mat))
  show "finite_instance_valuation \<theta> ?\<beta> c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p" for s e p c
    by (rule finite_instance_clause_true(2)[OF _ _ _ that]; (erule formed | erule prem | erule mat))
  show "finite_instance_valuation \<theta> ?\<beta> c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_instance_clause_true(3)[OF _ _ _ that]; (erule formed | erule prem | erule mat))
qed

lemma finite_parent_instance_true:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and nf: "F \<noteq> Some (resolution_goal_position g)"
    and q: "resolution_goal_position g \<noteq> []" and np: "resolution_node_position np = butlast (resolution_goal_position g)"
    and ctx: "finite_parent_context P Vp Vh st np k"
  shows "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (finite_instance_valuation \<theta> (finite_node_binding np))"
    and "\<And>s e p c. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_pattern_variables p \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
    and "\<And>s N c. (s,N) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_material_variables N \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
proof -
  note framed = finite_framed_instance_true[OF I sup gF nf q np finite_parent_context_framed[OF ctx]]
  show "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (finite_instance_valuation \<theta> (finite_node_binding np))" by (rule framed(1))
  show "finite_instance_valuation \<theta> (finite_node_binding np) c =
      decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
    if "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np)" "c |\<in>| finite_pattern_variables p" for s e p c
    by (rule framed(2)[OF that])
  show "finite_instance_valuation \<theta> (finite_node_binding np) c =
      decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
    if "(s,N) |\<in>| finite_schema_materials (resolution_node_schema np)" "c |\<in>| finite_material_variables N" for s N c
    by (rule framed(3)[OF that])
qed

section \<open>The goals under a parent read at a new instance\<close>

text \<open>
  Once a true instance @{text h'} of the parent clause is given and a grounding @{text \<theta>1} whose bindings' values are
  @{text h'} at every premise variable and equal to the support's at every variable of a goal elsewhere in the focus,
  every goal of the focus holds at @{text \<theta>1}: the goals under the parent are its premises' instances, true by the
  clause, and every other goal keeps its values.
\<close>

lemma finite_parent_exchange_holds:
  assumes sup: "resolution_supported_at U F B P st \<theta>"
    and children: "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) = resolution_node_position np \<Longrightarrow>
      (\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        h = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
    and true': "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    and agree: "\<And>s e p c. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      c |\<in>| finite_pattern_variables p \<Longrightarrow> decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
    and agree_m: "\<And>s N c. (s,N) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      c |\<in>| finite_material_variables N \<Longrightarrow> decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
    and unchanged: "\<And>h z. h |\<in>| finite_focus_pending F st \<Longrightarrow>
      \<not> (resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np) \<Longrightarrow>
      z |\<in>| resolution_goal_variables h \<Longrightarrow> \<theta>1 z = \<theta> z"
    and h: "h |\<in>| finite_focus_pending F st"
  shows "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h"
proof (cases "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np")
  case True
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  have hp: "h |\<in>| resolution_pending st" using h by (simp add: finite_focus_pending_focused)
  from children[OF hp True[THEN conjunct1] True[THEN conjunct2]] show ?thesis
  proof (elim disjE exE conjE)
    fix s e0 p0 r' assume m: "(s,e0,p0) |\<in>| finite_schema_premises ?S"
      and hh: "h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)"
    have "(s,e0,decode_finite_pattern p0) \<in> schema_premises (decode_finite_schema ?S)"
      using m by (force simp: decode_finite_call_pattern_def)
    then have "(e0,evaluate_pattern h' (decode_finite_pattern p0)) \<in> ?M" using true' unfolding clause_true_def by blast
    moreover have "evaluate_pattern h' (decode_finite_pattern p0) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta>1 (\<beta> a))) (decode_finite_pattern p0)"
      by (rule evaluate_pattern_cong) (simp add: agree[OF m] finite_pattern_variables_correct[symmetric])
    ultimately show ?thesis by (simp add: hh finite_goal_holds_def resolution_value_substitute_decoded)
  next
    fix s N0 r' assume m: "(s,N0) |\<in>| finite_schema_materials ?S"
      and hh: "h = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)"
    have "(s,decode_finite_material N0) \<in> schema_material_premises (decode_finite_schema ?S)" using m by force
    then have "evaluate_material_satisfaction h' (decode_finite_material N0)" using true' unfolding clause_true_def by blast
    moreover have "evaluate_material_satisfaction h' (decode_finite_material N0) \<longleftrightarrow>
        evaluate_material_satisfaction (\<lambda>a. decode_finite_term (resolution_value \<theta>1 (\<beta> a))) (decode_finite_material N0)"
      by (rule evaluate_material_satisfaction_cong) (simp add: agree_m[OF m] finite_material_variables_correct[symmetric])
    ultimately show ?thesis by (simp add: hh finite_goal_holds_def finite_material_ground_substitute)
  qed
next
  case False
  have "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h" by (rule resolution_supported_at_holds[OF sup h])
  moreover have "finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h \<longleftrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta> h"
    by (rule finite_goal_holds_cong) (rule unchanged[OF h False])
  ultimately show ?thesis by simp
qed

section \<open>The socket's premise, the parent's head and its output read at their views\<close>

text \<open>
  The head at its view: its viewed input is kept at either flag, and at the kept head its viewed output too, so every head
  variable keeps its value, the view's parts holding exactly the head's variables.
\<close>

lemma head_kept_whole:
  assumes kept: "head_kept True Vh S h h'" and formed: "view_formed Vh"
  shows "evaluate_pattern h' (decode_finite_pattern (finite_schema_conclusion S)) =
    evaluate_pattern h (decode_finite_pattern (finite_schema_conclusion S))"
  by (rule evaluate_pattern_cong, rule head_kept_variables[OF kept formed])
    (simp add: finite_pattern_variables_correct[symmetric])

text \<open>
  The committed goal is its parent's premise at the socket, under the parent's bindings; the premise is of its view's
  form (the obligation's first conjunct), and its viewed parts give the goal's viewed input and output.
\<close>

lemma finite_socket_premise:
  assumes gi: "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        Resolution_Call_Goal q r e p =
          Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        Resolution_Call_Goal q r e p =
          Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
    and vp: "resolution_view_pattern Vp p = Some (x,y)"
    and viewed: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p0 \<noteq> None"
  obtains p0 xi0 yo0 where "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    "p = finite_pattern_substitute \<beta> p0" "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0"
proof -
  obtain s0 e0 p1 r0 where m0: "(s0,e0,p1) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and g0: "Resolution_Call_Goal q r e p =
      Resolution_Call_Goal (resolution_node_position np @ [s0]) r0 e0 (finite_pattern_substitute \<beta> p1)"
    using gi by blast
  have qs: "q = resolution_node_position np @ [s0]" and ee: "e = e0"
    and pp: "p = finite_pattern_substitute \<beta> p1" using g0 by simp_all
  have s0: "s0 = last q" using qs by simp
  have nn: "resolution_view_pattern Vp p1 \<noteq> None" using viewed m0 s0 by blast
  obtain v where v: "resolution_view_pattern Vp p1 = Some v" using nn by (cases "resolution_view_pattern Vp p1") auto
  obtain xi0 yo0 where vv: "v = (xi0,yo0)" by (cases v)
  have v0: "resolution_view_pattern Vp p1 = Some (xi0,yo0)" using v vv by simp
  have "resolution_view_pattern Vp p = Some (finite_pattern_substitute \<beta> xi0,finite_pattern_substitute \<beta> yo0)"
    unfolding pp by (rule resolution_view_pattern_substitute[OF v0])
  then have xy: "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0" using vp by simp_all
  show thesis by (rule that[of p1 xi0 yo0]) (use m0 s0 ee pp v0 xy in simp_all)
qed

text \<open>
  The free socket's variant test at the parent's viewed output: the head and the parent's call are read at the head's
  view, the call's viewed parts the head's under the parent's bindings, and the output a variant of the head's.
\<close>

lemma finite_parent_output_parts:
  assumes po: "finite_parent_output Vh np = Some out"
    and call: "resolution_node_call np = finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema np))"
  obtains hi ho where "resolution_view_pattern Vh (finite_schema_conclusion (resolution_node_schema np)) = Some (hi,ho)"
    "resolution_view_pattern Vh (resolution_node_call np) = Some (finite_pattern_substitute \<beta> hi,out)"
    "out = finite_pattern_substitute \<beta> ho" "finite_variant ho out"
proof -
  let ?c = "finite_schema_conclusion (resolution_node_schema np)"
  obtain v where v: "resolution_view_pattern Vh ?c = Some v"
    using po by (cases "resolution_view_pattern Vh ?c") (auto simp: finite_parent_output_def)
  obtain hi ho where vv: "v = (hi,ho)" by (cases v)
  have vc: "resolution_view_pattern Vh ?c = Some (hi,ho)" using v vv by simp
  have vk: "resolution_view_pattern Vh (resolution_node_call np) =
      Some (finite_pattern_substitute \<beta> hi,finite_pattern_substitute \<beta> ho)"
    unfolding call by (rule resolution_view_pattern_substitute[OF vc])
  have oo: "out = finite_pattern_substitute \<beta> ho" and var: "finite_variant ho out"
    using po vc vk by (auto simp: finite_parent_output_def split: if_splits)
  show thesis by (rule that[OF vc _ oo var]) (simp add: vk oo)
qed

text \<open>
  The parent's own bindings, read by the test (@{const finite_node_binding}), are the linked ones on its clause's
  variables. Every pending goal under the parent in its context is one of its instances, and each premise-only variable is
  free — bound to its own variable, which only the parent's children hold — or among the socket's inputs with a ground
  binding.
\<close>

lemma finite_children_closed_children:
  assumes closed: "finite_children_closed Vp Vh st np k"
    and h: "h |\<in>| resolution_pending st" "resolution_goal_position h \<noteq> []"
      "butlast (resolution_goal_position h) = resolution_node_position np"
  shows "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
      h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute (finite_node_binding np) p0)) \<or>
    (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
      h = Resolution_Material_Goal (resolution_node_position np @ [s]) r'
        (finite_material_pattern_substitute (finite_node_binding np) N0))"
  by (rule finite_children_framed_children[OF finite_children_closed_framed[OF closed] h])

lemma finite_premise_only_bound:
  assumes poi: "finite_premise_only_inputs Vp Vh st np k"
    and sv: "single_valued (fset (resolution_node_bindings np))"
    and a: "a |\<in>| finite_schema_variables (resolution_node_schema np)"
      "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np))"
  shows "(finite_node_binding np a = Finite_Variable ((resolution_node_position np,True),a) \<and>
      (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> ((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h \<longrightarrow>
        resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np)) \<or>
    (a |\<in>| finite_socket_inputs Vp Vh (resolution_node_schema np) k \<and>
      finite_pattern_variables (finite_node_binding np a) = {||})"
proof -
  have "a |\<in>| finite_schema_variables (resolution_node_schema np) |-|
      finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np))" using a by simp
  from fbspec[OF poi[unfolded finite_premise_only_inputs_def] this]
  have c: "((a,Finite_Variable ((resolution_node_position np,True),a)) |\<in>| resolution_node_bindings np \<and>
      (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow> ((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h \<longrightarrow>
        resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np)) \<or>
    (a |\<in>| finite_socket_inputs Vp Vh (resolution_node_schema np) k \<and>
      finite_pattern_variables (finite_node_binding np a) = {||})" by auto
  then show ?thesis using finite_node_binding_row[OF sv] by blast
qed

section \<open>The parent context read at the socket\<close>

text \<open>
  What both socket contexts read of the parent context, stated once. A premise-only variable is free
  (@{text finite_free_premise_only}) when the node binds it to its own renamed-apart variable and only the parent's
  goals hold that variable; its renamed variable (@{text finite_free_premise_variable}) is not held by the parent's call.
  The parts (@{text finite_socket_parent_parts}): the socket's premise read at its view, its output's variables among the
  clause's with their values the support's, and every premise-only variable free or a ground input of the socket. The
  exchange (@{text finite_socket_exchange_valuation}): a new valuation that agrees with the new answer on the goal's
  viewed output, gives the new instance at the clause's variables, and keeps the support's values outside a set the
  holders test covers and outside the free premise-only variables, holds every goal outside the socket's focus.
\<close>

lemma finite_free_premise_variable_call:
  assumes ctx: "finite_parent_context P Vp Vh st np k" and Z: "finite_free_premise_variable st np z"
  shows "z |\<notin>| finite_pattern_variables (resolution_node_call np)"
proof -
  have unsh: "finite_premise_only_unshared np" using ctx by (simp add: finite_parent_context_def)
  have z: "z = ((resolution_node_position np,True),snd z)"
    and s: "snd z |\<in>| finite_schema_variables (resolution_node_schema np)"
    and c: "snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np))"
    using Z by (auto simp: finite_free_premise_variable_def prod_eq_iff)
  have "((resolution_node_position np,True),snd z) |\<notin>| finite_pattern_variables (resolution_node_call np)"
    using unsh s c unfolding finite_premise_only_unshared_def by auto
  then show ?thesis using z by metis
qed

lemma finite_framed_parent_premise:
  assumes gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and viewed: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p0 \<noteq> None"
  obtains p0 xi0 yo0 where "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and "p = finite_pattern_substitute (finite_node_binding np) p0"
    and "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and "x = finite_pattern_substitute (finite_node_binding np) xi0"
    and "y = finite_pattern_substitute (finite_node_binding np) yo0"
proof -
  let ?g = "Resolution_Call_Goal q r e p"
  have closed: "finite_children_framed C st np (last q)" using ctx by (simp add: finite_framed_parent_context_def)
  note children = finite_children_framed_children[OF closed]
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  obtain p0 xi0 yo0 where "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and "p = finite_pattern_substitute (finite_node_binding np) p0"
    and "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and "x = finite_pattern_substitute (finite_node_binding np) xi0"
    and "y = finite_pattern_substitute (finite_node_binding np) yo0"
    by (rule finite_socket_premise[OF children[OF gp gchild] vp viewed])
  then show thesis by (rule that)
qed

lemma finite_socket_parent_premise:
  assumes gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)"
    and ctx: "finite_parent_context P Vp Vh st np (last q)"
    and obl: "socket_discharged M (resolution_node_schema np) (last q) keep Vp Vh"
  obtains p0 xi0 yo0 where "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and "p = finite_pattern_substitute (finite_node_binding np) p0"
    and "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and "x = finite_pattern_substitute (finite_node_binding np) xi0"
    and "y = finite_pattern_substitute (finite_node_binding np) yo0"
proof -
  have viewed: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p0 \<noteq> None"
    using obl unfolding socket_discharged_def by blast
  obtain p0 xi0 yo0 where "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and "p = finite_pattern_substitute (finite_node_binding np) p0"
    and "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and "x = finite_pattern_substitute (finite_node_binding np) xi0"
    and "y = finite_pattern_substitute (finite_node_binding np) yo0"
    by (rule finite_framed_parent_premise[OF gF q np vp finite_parent_context_framed[OF ctx] viewed])
  then show thesis by (rule that)
qed

lemma finite_socket_parent_parts:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and ctx: "finite_parent_context P Vp Vh st np (last q)" and Vp: "view_formed Vp"
    and prem0: "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
  shows "c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> c |\<in>| finite_schema_variables (resolution_node_schema np)"
    and "c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> finite_instance_valuation \<theta> (finite_node_binding np) c =
      decode_finite_term (resolution_value \<theta> (finite_node_binding np c))"
    and "c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      c |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np)) \<Longrightarrow>
      finite_free_premise_only st np c \<or> (c |\<in>| finite_socket_inputs Vp Vh (resolution_node_schema np) (last q) \<and>
        finite_pattern_variables (finite_node_binding np c) = {||})"
    and "c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      c |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np)) \<Longrightarrow>
      ((resolution_node_position np,True),c) |\<notin>| finite_pattern_variables (resolution_node_call np)"
proof -
  let ?g = "Resolution_Call_Goal q r e p"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  have nd: "np |\<in>| resolution_nodes st" and poi: "finite_premise_only_inputs Vp Vh st np (last q)"
    and unsh: "finite_premise_only_unshared np"
    using ctx by (simp_all add: finite_parent_context_def)
  note linked = finite_node_binding_linked[OF I nd]
  have sv: "single_valued (fset (resolution_node_bindings np))" unfolding linked(1) by (auto simp: single_valued_def)
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  show "c |\<in>| finite_schema_variables ?S" if "c |\<in>| finite_pattern_variables yo0"
    by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: pvars that)
  show "finite_instance_valuation \<theta> ?\<beta> c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "c |\<in>| finite_pattern_variables yo0"
    by (rule finite_parent_instance_true(2)[OF I sup gF nf' q' np' ctx prem0]) (simp add: pvars that)
  show "finite_free_premise_only st np c \<or>
      (c |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> c) = {||})"
    if "c |\<in>| finite_schema_variables ?S" "c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    unfolding finite_free_premise_only_def by (rule finite_premise_only_bound[OF poi sv that])
  show "((resolution_node_position np,True),c) |\<notin>| finite_pattern_variables (resolution_node_call np)"
    if "c |\<in>| finite_schema_variables ?S" "c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    using unsh that unfolding finite_premise_only_unshared_def by auto
qed

lemma finite_framed_exchange_valuation:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and Vp: "view_formed Vp"
    and tr': "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    and K: "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c)) \<Longrightarrow>
      decode_finite_term (resolution_value \<theta>1 (finite_node_binding np c)) = h' c"
    and holders: "finite_socket_holders F st q Y (Resolution_Call_Goal q r e p)"
    and new: "\<And>z. z |\<in>| finite_pattern_variables y \<Longrightarrow> \<theta>1 z = \<theta>2 z"
    and old: "\<And>z. z |\<notin>| Y \<Longrightarrow> \<not> finite_free_premise_variable st np z \<Longrightarrow> \<theta>1 z = \<theta> z"
  shows "(\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Call_Goal q r e p"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  have closed: "finite_children_framed C st np (last q)" using ctx by (simp add: finite_framed_parent_context_def)
  note children = finite_children_framed_children[OF closed]
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent2: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,e',p') |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p'" for s e' p' c
    by (rule finite_framed_instance_true(2)[OF I sup gF nf' q' np' ctx that])
  have parent3: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_framed_instance_true(3)[OF I sup gF nf' q' np' ctx that])
  have unchanged: "\<And>h0 z. h0 |\<in>| finite_focus_pending F st \<Longrightarrow>
      \<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np) \<Longrightarrow>
      z |\<in>| resolution_goal_variables h0 \<Longrightarrow> \<theta>1 z = \<theta> z"
  proof -
    fix h0 z assume h0: "h0 |\<in>| finite_focus_pending F st"
      and nc: "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
      and z: "z |\<in>| resolution_goal_variables h0"
    have ny: "z |\<notin>| Y"
    proof
      assume zy: "z |\<in>| Y"
      have "h0 = ?g \<or> resolution_goal_variables h0 |\<inter>| Y = {||} \<or>
          (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q)"
        using holders h0 unfolding finite_socket_holders_def by auto
      then show False
      proof (elim disjE)
        assume "h0 = ?g" then show False using nc gchild by simp
      next
        assume d: "resolution_goal_variables h0 |\<inter>| Y = {||}"
        have "z |\<in>| resolution_goal_variables h0 |\<inter>| Y" using z zy by simp
        then show False using d by simp
      next
        assume "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q"
        then show False using nc np by simp
      qed
    qed
    have nZ: "\<not> finite_free_premise_variable st np z"
    proof
      assume Z: "finite_free_premise_variable st np z"
      have h0p: "h0 |\<in>| resolution_pending st" using h0 by (simp add: finite_focus_pending_focused)
      have z1: "fst z = (resolution_node_position np,True)" and f: "finite_free_premise_only st np (snd z)"
        using Z by (simp_all add: finite_free_premise_variable_def)
      have zz: "((resolution_node_position np,True),snd z) |\<in>| resolution_goal_variables h0"
        using z z1 by (metis prod.collapse)
      have "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np"
        using f h0p zz unfolding finite_free_premise_only_def by blast
      with nc show False by blast
    qed
    show "\<theta>1 z = \<theta> z" by (rule old[OF ny nZ])
  qed
  have holds: "finite_goal_holds ?M \<theta>1 h" if "h |\<in>| finite_focus_pending F st" for h
  proof (rule finite_parent_exchange_holds[OF sup children tr' _ _ _ that])
    fix s e' p' c assume m: "(s,e',p') |\<in>| finite_schema_premises ?S" and c: "c |\<in>| finite_pattern_variables p'"
    show "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      by (rule K) (use m c parent2[OF m c] in \<open>auto intro: finite_schema_variables_members(2)\<close>)
  next
    fix s N c assume m: "(s,N) |\<in>| finite_schema_materials ?S" and c: "c |\<in>| finite_material_variables N"
    show "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      by (rule K) (use m c parent3[OF m c] in \<open>auto intro: finite_schema_variables_members(3)\<close>)
  next
    fix h0 z assume "h0 |\<in>| finite_focus_pending F st"
      "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
      "z |\<in>| resolution_goal_variables h0"
    then show "\<theta>1 z = \<theta> z" by (rule unchanged)
  qed
  have pv: "finite_pattern_variables p = finite_pattern_variables x |\<union>| finite_pattern_variables y"
    by (rule resolution_view_pattern_variables[OF Vp vp])
  show ?thesis
  proof (intro conjI allI impI)
    fix z assume z: "z |\<in>| finite_pattern_variables p"
    have "z |\<in>| finite_pattern_variables y" using z pv ground by simp
    then show "\<theta>1 z = \<theta>2 z" by (rule new)
  next
    fix h assume h: "h |\<in>| finite_focus_pending F st"
      and "\<not> resolution_focused (Some q) (resolution_goal_position h)"
    show "finite_goal_holds ?M \<theta>1 h" by (rule holds[OF h])
  qed
qed

lemma finite_socket_exchange_valuation:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and ctx: "finite_parent_context P Vp Vh st np (last q)"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and Vp: "view_formed Vp"
    and tr': "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    and K: "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      finite_instance_valuation \<theta> (finite_node_binding np) c =
        decode_finite_term (resolution_value \<theta> (finite_node_binding np c)) \<Longrightarrow>
      decode_finite_term (resolution_value \<theta>1 (finite_node_binding np c)) = h' c"
    and holders: "finite_socket_holders F st q Y (Resolution_Call_Goal q r e p)"
    and new: "\<And>z. z |\<in>| finite_pattern_variables y \<Longrightarrow> \<theta>1 z = \<theta>2 z"
    and old: "\<And>z. z |\<notin>| Y \<Longrightarrow> \<not> finite_free_premise_variable st np z \<Longrightarrow> \<theta>1 z = \<theta> z"
  shows "(\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
    (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
      finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h)"
  by (rule finite_framed_exchange_valuation[OF I sup gF nf q np finite_parent_context_framed[OF ctx] vp ground Vp tr' K
    holders new old])

section \<open>The socket at a frame, over a class of the socket's output\<close>

text \<open>
  B2a of correction (10). The socket's obligation at a frame @{text C} and over a class @{text N} of the socket's output
  is the calls conjunct of @{text narrowed_socket_framed}, stated inline, and holds of @{const socket_framed} at every
  class (@{text socket_framed_calls}): for a true instance and an answer at the socket's viewed input whose output is in
  @{text N}, a true instance agreeing with the old outside @{text C}, keeping the head as the declaration says and taking
  the answer at the socket's output (@{text finite_framed_new_instance}). One call context
  (@{text finite_framed_call_context}) sets the exchanged valuation head output by head output
  (@{text finite_framed_valuation}) and reads the goals outside the socket's focus through
  @{text finite_framed_exchange_valuation}, for every new answer whose output is in @{text N} (#599's (ii) at the kept
  answer). The kept and the free contexts at a frame are its instances (@{text finite_framed_kept_context},
  @{text finite_framed_free_context}), and today's contexts are theirs at the default frame and the class of every term.
\<close>

lemma finite_framed_new_instance:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and obl: "\<forall>h. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h \<longrightarrow>
      (\<forall>e1 p1 xi yo u y'. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
        resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow> (e1,u) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
        resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h' \<and>
          head_kept keep Vh (resolution_node_schema np) h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema (resolution_node_schema np)) - fset C. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y'))"
    and Vp: "view_formed Vp"
    and prem0: "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and pp: "p = finite_pattern_substitute (finite_node_binding np) p0"
    and ground: "finite_pattern_variables (finite_pattern_substitute (finite_node_binding np) xi0) = {||}"
    and new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> positive_meaning (decode_finite_system P)"
    and inN: "N (decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute (finite_node_binding np) yo0)))"
  obtains h' where "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    "head_kept keep Vh (resolution_node_schema np) (finite_instance_valuation \<theta> (finite_node_binding np)) h'"
    "\<forall>a\<in>schema_variables (decode_finite_schema (resolution_node_schema np)) - fset C.
      h' a = finite_instance_valuation \<theta> (finite_node_binding np) a"
    "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (finite_node_binding np c))"
    "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow> term_formed (h' c)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  let ?g = "Resolution_Call_Goal q r e p"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent1: "clause_true ?M (decode_finite_schema ?S) ?h"
    by (rule finite_framed_instance_true(1)[OF I sup gF nf' q' np' ctx])
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  have hxi: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if "c |\<in>| finite_pattern_variables xi0" for c
    by (rule finite_framed_instance_true(2)[OF I sup gF nf' q' np' ctx prem0]) (simp add: pvars that)
  have vp: "resolution_view_pattern Vp p = Some (finite_pattern_substitute ?\<beta> xi0,finite_pattern_substitute ?\<beta> yo0)"
    unfolding pp by (rule resolution_view_pattern_substitute[OF vp0])
  have ex: "decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> xi0)) =
      evaluate_pattern ?h (decode_finite_pattern xi0)"
  proof -
    have "resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> xi0) = resolution_value \<theta> (finite_pattern_substitute ?\<beta> xi0)"
      by (rule resolution_value_cong) (simp add: ground)
    then have "decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> xi0)) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta> (?\<beta> a))) (decode_finite_pattern xi0)"
      by (simp add: resolution_value_substitute_decoded)
    also have "\<dots> = evaluate_pattern ?h (decode_finite_pattern xi0)"
      by (rule evaluate_pattern_cong) (simp add: hxi finite_pattern_variables_correct[symmetric])
    finally show ?thesis .
  qed
  have vt: "resolution_view_term Vp (decode_finite_term (resolution_value \<theta>2 p)) =
      Some (evaluate_pattern ?h (decode_finite_pattern xi0),
        decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> yo0)))"
    using resolution_view_pattern_value[OF Vp vp, of \<theta>2] ex by simp
  have "\<exists>h'. clause_true ?M (decode_finite_schema ?S) h' \<and> head_kept keep Vh ?S ?h h' \<and>
      (\<forall>a\<in>schema_variables (decode_finite_schema ?S) - fset C. h' a = ?h a) \<and>
      evaluate_pattern h' (decode_finite_pattern xi0) = evaluate_pattern ?h (decode_finite_pattern xi0) \<and>
      evaluate_pattern h' (decode_finite_pattern yo0) =
        decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> yo0))"
    by (rule obl[rule_format, OF parent1 prem0 vp0 new vt inN])
  then obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'" and hk: "head_kept keep Vh ?S ?h h'"
    and fr: "\<forall>a\<in>schema_variables (decode_finite_schema ?S) - fset C. h' a = ?h a"
    and hy: "evaluate_pattern h' (decode_finite_pattern yo0) =
      decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> yo0))"
    by blast
  have formed': "term_formed (h' c)" if "c |\<in>| finite_schema_variables ?S" for c
    using tr' that unfolding clause_true_def by (simp add: finite_schema_variables_correct[symmetric])
  have hy_agree: "h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
  proof -
    have "evaluate_pattern h' (decode_finite_pattern yo0) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta>2 (?\<beta> a))) (decode_finite_pattern yo0)"
      using hy by (simp add: resolution_value_substitute_decoded)
    then show ?thesis by (rule evaluate_pattern_agree) (simp add: that finite_pattern_variables_correct[symmetric])
  qed
  show thesis by (rule that[OF tr' hk fr]) (erule hy_agree, erule formed')
qed

text \<open>
  The obligation at a frame read off a framed socket, at every class of the socket's output.
\<close>

lemma socket_framed_viewed:
  assumes framed: "socket_framed M S s keep Vp Vh C"
  shows "\<forall>e1 p1. (s,e1,p1) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p1 \<noteq> None"
  using framed unfolding socket_framed_def by blast

lemma socket_framed_calls:
  assumes framed: "socket_framed M S s keep Vp Vh C"
  shows "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
    (\<forall>e1 p1 xi yo u y'. (s,e1,p1) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow>
      (e1,u) \<in> M \<longrightarrow> resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
      (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'))"
  using framed unfolding socket_framed_def by blast

text \<open>
  Today's new instance, keeping the socket's inputs, is the framed one's at the default frame and the class of every
  term: the inputs within the schema's variables lie outside the default frame, and the others among the head's viewed
  input, which the kept head keeps at either flag.
\<close>

lemma finite_socket_new_instance:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and ctx: "finite_parent_context P Vp Vh st np (last q)"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (resolution_node_schema np) (last q) keep Vp Vh"
    and Vp: "view_formed Vp"
    and prem0: "(last q,e,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and pp: "p = finite_pattern_substitute (finite_node_binding np) p0"
    and ground: "finite_pattern_variables (finite_pattern_substitute (finite_node_binding np) xi0) = {||}"
    and new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> positive_meaning (decode_finite_system P)"
  obtains h' where "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    "head_kept keep Vh (resolution_node_schema np) (finite_instance_valuation \<theta> (finite_node_binding np)) h'"
    "\<forall>a\<in>socket_inputs Vp Vh (resolution_node_schema np) (last q). h' a = finite_instance_valuation \<theta> (finite_node_binding np) a"
    "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (finite_node_binding np c))"
    "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow> term_formed (h' c)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  let ?h = "finite_instance_valuation \<theta> (finite_node_binding np)"
  let ?C = "finite_default_frame Vp Vh ?S (last q)"
  have linked: "resolution_node_linked P st np" using ctx by (simp add: finite_parent_context_def)
  have formedS: "schema_formed (decode_finite_schema ?S)" by (rule finite_linked_schema_formed[OF I linked])
  have framed: "socket_framed ?M ?S (last q) keep Vp Vh (fset ?C)"
    unfolding finite_default_frame_correct by (rule socket_discharged_framed[OF obl formedS])
  obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'" and hk: "head_kept keep Vh ?S ?h h'"
    and fr: "\<forall>a\<in>schema_variables (decode_finite_schema ?S) - fset ?C. h' a = ?h a"
    and hy: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow>
      h' c = decode_finite_term (resolution_value \<theta>2 (finite_node_binding np c))"
    and fm: "\<And>c. c |\<in>| finite_schema_variables ?S \<Longrightarrow> term_formed (h' c)"
    by (rule finite_framed_new_instance[OF I sup gF nf q np finite_parent_context_framed[OF ctx]
      socket_framed_calls[OF framed, where N="\<lambda>_. True"] Vp prem0 vp0 pp ground new TrueI]) blast
  have ins: "\<forall>a\<in>socket_inputs Vp Vh ?S (last q). h' a = ?h a"
  proof
    fix a assume a: "a \<in> socket_inputs Vp Vh ?S (last q)"
    show "h' a = ?h a"
    proof (cases "a \<in> schema_variables (decode_finite_schema ?S)")
      case True
      have "a \<in> schema_variables (decode_finite_schema ?S) - fset ?C"
        using True a by (simp add: finite_default_frame_correct socket_default_frame_def)
      then show ?thesis using fr by blast
    next
      case False
      have prem_in: "a \<in> schema_variables (decode_finite_schema ?S)"
        if "(last q,d',p') |\<in>| finite_schema_premises ?S" "resolution_view_pattern Vp p' = Some (xi,yo)"
          "a \<in> pattern_variables (decode_finite_pattern xi)" for d' p' xi yo
      proof -
        have "a |\<in>| finite_pattern_variables xi" using that(3) by (simp add: finite_pattern_variables_correct[symmetric])
        then have "a |\<in>| finite_pattern_variables p'" using resolution_view_pattern_variables[OF Vp that(2)] by simp
        then have "a |\<in>| finite_schema_variables ?S" by (rule finite_schema_variables_members(2)[OF that(1)])
        then show ?thesis by (simp add: finite_schema_variables_correct[symmetric])
      qed
      have mat_in: "a \<in> schema_variables (decode_finite_schema ?S)"
        if "(last q,N) |\<in>| finite_schema_materials ?S"
          "a \<in> pattern_variables (decode_finite_pattern (finite_material_source N))" for N
      proof -
        have "a |\<in>| finite_material_variables N"
          using that(2) by (simp add: finite_material_variables_def finite_pattern_variables_correct[symmetric])
        then have "a |\<in>| finite_schema_variables ?S" by (rule finite_schema_variables_members(3)[OF that(1)])
        then show ?thesis by (simp add: finite_schema_variables_correct[symmetric])
      qed
      have head: "a \<in> head_inputs Vh ?S" using a False prem_in mat_in unfolding socket_inputs_def by blast
      show ?thesis
      proof (cases "resolution_view_pattern Vh (finite_schema_conclusion ?S)")
        case None
        have "evaluate_pattern h' (decode_finite_pattern (finite_schema_conclusion ?S)) =
            evaluate_pattern ?h (decode_finite_pattern (finite_schema_conclusion ?S))"
          using hk None by (simp add: head_kept_def)
        moreover have "a \<in> pattern_variables (decode_finite_pattern (finite_schema_conclusion ?S))"
          using head None by (simp add: head_inputs_def)
        ultimately show ?thesis by (rule evaluate_pattern_agree)
      next
        case (Some v)
        obtain ci co where v: "v = (ci,co)" by (cases v)
        have "evaluate_pattern h' (decode_finite_pattern ci) = evaluate_pattern ?h (decode_finite_pattern ci)"
          using hk Some v by (simp add: head_kept_def)
        moreover have "a \<in> pattern_variables (decode_finite_pattern ci)" using head Some v by (simp add: head_inputs_def)
        ultimately show ?thesis by (rule evaluate_pattern_agree)
      qed
    qed
  qed
  show thesis by (rule that[OF tr' hk ins]) (erule hy, erule fm)
qed

text \<open>
  The one call context: at a framed parent context and the obligation over @{text N}, with the kept head or, at a free
  socket, the absorbing frame and the call's input apart from its output, and holders covering the goal's viewed output
  and, at a free socket, the absorbed variables.
\<close>

lemma finite_framed_call_context:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and viewed: "\<forall>e1 p1. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p1 \<noteq> None"
    and obl: "\<forall>h. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h \<longrightarrow>
      (\<forall>e1 p1 xi yo u y'. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
        resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow> (e1,u) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
        resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h' \<and>
          head_kept keep Vh (resolution_node_schema np) h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema (resolution_node_schema np)) - fset C. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y'))"
    and Vp: "view_formed Vp" and Vh: "view_formed Vh"
    and head: "keep \<or> (finite_parent_absorbs Vp Vh C np (last q) \<and> finite_input_output_apart Vh np)"
    and holders: "finite_socket_holders F st q Y (Resolution_Call_Goal q r e p)"
    and Ysub: "finite_pattern_variables y |\<subseteq>| Y"
    and Yabs: "\<not> keep \<Longrightarrow> finite_parent_absorbed Vp Vh C np (last q) |\<subseteq>| Y"
  shows "\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
      N (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
    (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h))"
proof (intro allI impI)
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Call_Goal q r e p"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  let ?SV = "finite_schema_variables ?S"
  fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M"
    and inN: "N (decode_finite_term (resolution_value \<theta>2 y))"
  obtain p0 xi0 yo0 where prem0: "(last q,e,p0) |\<in>| finite_schema_premises ?S"
    and pp: "p = finite_pattern_substitute ?\<beta> p0" and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and xy: "x = finite_pattern_substitute ?\<beta> xi0" "y = finite_pattern_substitute ?\<beta> yo0"
    by (rule finite_framed_parent_premise[OF gF q np vp ctx viewed])
  have groundxi: "finite_pattern_variables (finite_pattern_substitute ?\<beta> xi0) = {||}" using ground xy(1) by simp
  have inN0: "N (decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> yo0)))" using inN xy(2) by simp
  obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
    and hk: "head_kept keep Vh ?S ?h h'"
    and fr: "\<forall>a\<in>schema_variables (decode_finite_schema ?S) - fset C. h' a = ?h a"
    and hy_agree: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))"
    and formed': "\<And>c. c |\<in>| ?SV \<Longrightarrow> term_formed (h' c)"
    by (rule finite_framed_new_instance[OF I sup gF nf q np ctx obl Vp prem0 vp0 pp groundxi new inN0]) blast
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have linked: "resolution_node_linked P st np" using ctx by (simp add: finite_framed_parent_context_def)
  have formedS: "schema_formed (decode_finite_schema ?S)" by (rule finite_linked_schema_formed[OF I linked])
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  have own: "finite_socket_own Vp ?S (last q) |\<subseteq>| finite_pattern_variables yo0"
    by (rule finite_socket_own_premise[OF formedS prem0 vp0])
  have OS: "finite_pattern_variables yo0 |\<subseteq>| ?SV"
  proof (rule fsubsetI)
    fix c assume c: "c |\<in>| finite_pattern_variables yo0"
    show "c |\<in>| ?SV" by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: pvars c)
  qed
  have old_O: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
    by (rule finite_framed_instance_true(2)[OF I sup gF nf' q' np' ctx prem0]) (simp add: pvars that)
  have Yiff: "z \<in> fset (finite_pattern_variables y) \<longleftrightarrow>
      (\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and> z |\<in>| finite_pattern_variables (?\<beta> c))" for z
    unfolding xy(2) by (blast intro: finite_pattern_substitute_variable dest: finite_pattern_substitute_origin)
  have frame: "h' a = ?h a" if "a |\<in>| ?SV" "a |\<notin>| C" for a
  proof -
    have "a \<in> schema_variables (decode_finite_schema ?S) - fset C"
      using that by (simp add: finite_schema_variables_correct[symmetric])
    then show ?thesis using fr by blast
  qed
  have headc: "(keep \<and> head_kept True Vh ?S ?h h') \<or>
      (\<not> keep \<and> head_kept False Vh ?S ?h h' \<and> finite_parent_absorbs Vp Vh C np (last q) \<and>
        finite_input_output_apart Vh np)"
    using head hk by (cases keep) auto
  obtain \<theta>1 where t1: "\<And>z. z \<in> fset (finite_pattern_variables y) \<Longrightarrow> \<theta>1 z = \<theta>2 z"
    and t2: "\<And>z. z \<notin> fset (finite_pattern_variables y) \<Longrightarrow> \<not> finite_free_premise_variable st np z \<Longrightarrow>
      keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C np (last q) \<Longrightarrow> \<theta>1 z = \<theta> z"
    and t3: "\<And>c. c |\<in>| ?SV \<Longrightarrow> ?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c)) \<or>
        (c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S) \<and> finite_free_premise_only st np c) \<Longrightarrow>
      decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
    by (rule finite_framed_valuation[where h="finite_instance_valuation \<theta> (finite_node_binding np)" and h'=h' and
      \<theta>=\<theta> and ?\<theta>2.0=\<theta>2 and Y="fset (finite_pattern_variables y)" and Ow="finite_pattern_variables yo0",
      OF I ctx Vh own OS old_O hy_agree Yiff frame headc formed']) (assumption | rule that)+
  have K: "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
    if "c |\<in>| ?SV" "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" for c
    using t3 that by blast
  have new1: "\<theta>1 z = \<theta>2 z" if "z |\<in>| finite_pattern_variables y" for z using t1 that by blast
  have old1: "\<theta>1 z = \<theta> z" if z: "z |\<notin>| Y" "\<not> finite_free_premise_variable st np z" for z
  proof (rule t2)
    show "z |\<notin>| finite_pattern_variables y" using z(1) Ysub by (meson fsubsetD)
    show "\<not> finite_free_premise_variable st np z" by (rule z(2))
    show "keep \<or> z |\<notin>| finite_parent_absorbed Vp Vh C np (last q)" using z(1) Yabs by (meson fsubsetD)
  qed
  show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds ?M \<theta>1 h)"
    by (rule exI[of _ \<theta>1], rule finite_framed_exchange_valuation[OF I sup gF nf q np ctx vp ground Vp tr' K holders new1 old1])
qed

theorem finite_framed_kept_context:
  fixes Vp Vh :: "nat resolution_view"
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and viewed: "\<forall>e1 p1. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p1 \<noteq> None"
    and obl: "\<forall>h. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h \<longrightarrow>
      (\<forall>e1 p1 xi yo u y'. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
        resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow> (e1,u) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
        resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h' \<and>
          head_kept True Vh (resolution_node_schema np) h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema (resolution_node_schema np)) - fset C. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y'))"
    and Vp: "view_formed Vp" and Vh: "view_formed Vh"
    and holders: "finite_socket_holders F st q Y (Resolution_Call_Goal q r e p)"
    and Ysub: "finite_pattern_variables y |\<subseteq>| Y"
  shows "\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
      N (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
    (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h))"
  by (rule finite_framed_call_context[OF I sup gF nf q np vp ground ctx viewed obl Vp Vh _ holders Ysub]) simp_all

theorem finite_framed_free_context:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and root: "F = Some (butlast q)" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and ctx: "finite_framed_parent_context P C st np (last q)"
    and viewed: "\<forall>e1 p1. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      resolution_view_pattern Vp p1 \<noteq> None"
    and obl: "\<forall>h. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h \<longrightarrow>
      (\<forall>e1 p1 xi yo u y'. (last q,e1,p1) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
        resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow> (e1,u) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
        resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h' \<and>
          head_kept False Vh (resolution_node_schema np) h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema (resolution_node_schema np)) - fset C. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y'))"
    and Vp: "view_formed Vp" and Vh: "view_formed Vh"
    and absorbs: "finite_parent_absorbs Vp Vh C np (last q)" and apart: "finite_input_output_apart Vh np"
    and holders: "finite_socket_holders F st q Y (Resolution_Call_Goal q r e p)"
    and Ysub: "finite_pattern_variables y |\<union>| finite_parent_absorbed Vp Vh C np (last q) |\<subseteq>| Y"
  shows "\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> positive_meaning (decode_finite_system P) \<longrightarrow>
      N (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
    (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
        finite_goal_holds (positive_meaning (decode_finite_system P)) \<theta>1 h))"
proof -
  have "length (butlast q) \<noteq> length q" using q by (cases q) simp_all
  then have "butlast q \<noteq> q" by metis
  then have nf: "F \<noteq> Some q" using root by simp
  show ?thesis
    by (rule finite_framed_call_context[OF I sup gF nf q np vp ground ctx viewed obl Vp Vh _ holders])
      (use absorbs apart Ysub in \<open>auto simp: le_sup_iff\<close>)
qed

section \<open>The socket declared with the kept head\<close>

text \<open>
  At a socket declared with the kept head, the context of #565's exchange is the kept context at a frame
  (@{text finite_framed_kept_context}) at the socket's default frame, the framed parent context today's parent context
  gives (@{text finite_parent_context_framed}), and the class of every term: the obligation at the default frame is the
  declaration's (@{text socket_discharged_framed}).
\<close>

theorem finite_socket_kept_context:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and ctx: "finite_parent_context P Vp Vh st np (last q)"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (resolution_node_schema np) (last q) True Vp Vh"
    and Vp: "view_formed Vp" and Vh: "view_formed Vh"
    and holders: "finite_socket_holders F st q (finite_pattern_variables y) (Resolution_Call_Goal q r e p)"
  shows "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e p"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  let ?C = "finite_default_frame Vp Vh ?S (last q)"
  have linked: "resolution_node_linked P st np" using ctx by (simp add: finite_parent_context_def)
  have formedS: "schema_formed (decode_finite_schema ?S)" by (rule finite_linked_schema_formed[OF I linked])
  have framed: "socket_framed ?M ?S (last q) True Vp Vh (fset ?C)"
    unfolding finite_default_frame_correct by (rule socket_discharged_framed[OF obl formedS])
  show ?thesis unfolding finite_exchange_context_def
    using finite_framed_kept_context[OF I sup gF nf q np vp ground finite_parent_context_framed[OF ctx]
      socket_framed_viewed[OF framed] socket_framed_calls[OF framed, where N="\<lambda>_. True"] Vp Vh holders order_refl]
    by simp
qed

section \<open>The socket declared without the kept head\<close>

text \<open>
  At a socket declared without the kept head, the parent is the focus root and its call's viewed output is a variant of
  its clause's viewed head output: the default frame absorbs (@{text finite_variant_absorbs}), its absorbed variables
  lie in the call's output, and the context is the free context at a frame (@{text finite_framed_free_context}) at the
  default frame and the class of every term.
\<close>

theorem finite_socket_free_context:
  assumes I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e p |\<in>| finite_focus_pending F st"
    and root: "F = Some (butlast q)" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and ctx: "finite_parent_context P Vp Vh st np (last q)"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (resolution_node_schema np) (last q) False Vp Vh"
    and Vp: "view_formed Vp" and Vh: "view_formed Vh"
    and po: "finite_parent_output Vh np = Some out" and apart: "finite_input_output_apart Vh np"
    and holders: "finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out)
      (Resolution_Call_Goal q r e p)"
  shows "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e p"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  let ?C = "finite_default_frame Vp Vh ?S (last q)"
  let ?\<beta> = "finite_node_binding np"
  have nd: "np |\<in>| resolution_nodes st" and linked: "resolution_node_linked P st np"
    using ctx by (simp_all add: finite_parent_context_def)
  have formedS: "schema_formed (decode_finite_schema ?S)" by (rule finite_linked_schema_formed[OF I linked])
  have framed: "socket_framed ?M ?S (last q) False Vp Vh (fset ?C)"
    unfolding finite_default_frame_correct by (rule socket_discharged_framed[OF obl formedS])
  obtain hi ho where vc: "resolution_view_pattern Vh (finite_schema_conclusion ?S) = Some (hi,ho)"
    and vk: "resolution_view_pattern Vh (resolution_node_call np) = Some (finite_pattern_substitute ?\<beta> hi,out)"
    and xo: "out = finite_pattern_substitute ?\<beta> ho" and variant: "finite_variant ho out"
    by (rule finite_parent_output_parts[OF po finite_node_binding_linked(2)[OF I nd]])
  have variant': "finite_variant ho (finite_pattern_substitute ?\<beta> ho)" using variant xo by simp
  have absorbs: "finite_parent_absorbs Vp Vh ?C np (last q)" by (rule finite_variant_absorbs(1)[OF vc variant'])
  have absub: "finite_parent_absorbed Vp Vh ?C np (last q) |\<subseteq>| finite_pattern_variables (finite_pattern_substitute ?\<beta> ho)"
    by (rule finite_variant_absorbs(2)[OF vc variant'])
  have Ysub: "finite_pattern_variables y |\<union>| finite_parent_absorbed Vp Vh ?C np (last q) |\<subseteq>|
      finite_pattern_variables y |\<union>| finite_pattern_variables out"
    by (rule sup_mono[OF order_refl]) (simp add: absub xo)
  show ?thesis unfolding finite_exchange_context_def
    using finite_framed_free_context[OF I sup gF root q np vp ground finite_parent_context_framed[OF ctx]
      socket_framed_viewed[OF framed] socket_framed_calls[OF framed, where N="\<lambda>_. True"] Vp Vh absorbs apart holders
      Ysub]
    by simp
qed

section \<open>At every state where the test commits\<close>

text \<open>
  At a socket commitment of the framed test the parent context holds at the frame the test chose
  (@{text finite_framed_socket_context}), at the socket's declared views and key, so the framed contexts' hypotheses are
  the test's conditions; the obligation at that frame comes from the declarations' and the frames' discharge
  (@{text finite_frame_at_framed}), the views' formation from the declarations'. This holds at every focus and for the
  found states of any committed search.
\<close>

theorem finite_framed_socket_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>" and gF: "g |\<in>| finite_focus_pending F st"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and cc: "commit_call (finite_framed_commitment D \<Phi>) F st g" and nf0: "F \<noteq> Some (resolution_goal_position g)"
    and socket: "\<not> finite_direct_commitment D F st g"
    and only: "finite_registrations_premise_only \<kappa> P" and H: "resolution_registrations_held \<kappa> st"
    and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)"
  shows "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        K P n (Some (resolution_goal_position g)) B st)) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  have parent: "finite_goal_premise st g" by (rule finite_framed_commitment_premise[OF cc])
  obtain Vp Vh ch where call: "resolution_is_call g" and sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
    and cn: "finite_call_framed D \<Phi> Vp Vh ch F st g"
    using cc socket by (auto simp: finite_framed_commitment_def)
  obtain q r e p where gq: "g = Resolution_Call_Goal q r e p" using call by (cases g) simp_all
  let ?g = "Resolution_Call_Goal q r e p"
  have mn: "finite_material_framed D \<Phi> Vp Vh ch F st g" using gq by (simp add: finite_material_framed_def)
  obtain nd C where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
    and qne: "resolution_goal_position g \<noteq> []"
    and fa0: "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd)
      (last (resolution_goal_position g)) ch = Some C"
    and ctx0: "finite_framed_parent_context P C st nd (last (resolution_goal_position g))"
    by (rule finite_framed_socket_context[OF I sc cn mn])
  have q: "q \<noteq> []" and np: "resolution_node_position nd = butlast q"
    and fa: "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch = Some C"
    and ctx: "finite_framed_parent_context P C st nd (last q)" using qne nd(2) fa0 ctx0 gq by simp_all
  obtain x y where vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and decl: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) ?g"
    using sc gq by (auto simp: finite_socket_commitment_framed_def split: option.splits prod.splits)
  have gF': "?g |\<in>| finite_focus_pending F st" using gF gq by simp
  have nf: "F \<noteq> Some q" using nf0 gq by simp
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have same: "m = nd" if "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast q" for m
  proof -
    have "resolution_node_position m = resolution_node_position nd" using that(2) np by simp
    then show ?thesis using dist that(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  have linked: "resolution_node_linked P st nd" using ctx by (simp add: finite_framed_parent_context_def)
  have formed: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  have views: "view_formed Vp \<and> view_formed Vh" if "(e',S,s,keep,Vp,Vh) |\<in>| declared_sockets D" for e' S s keep
  proof -
    have "declarations_formed D" using discharged by (simp add: declarations_discharged_def)
    then show ?thesis using that unfolding declarations_formed_def by auto
  qed
  have ctxE: "finite_exchange_context ?M F q st e p"
  proof (cases "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) ?g")
    case True
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,True,Vp,Vh) |\<in>| declared_sockets D"
      and holders: "finite_socket_holders F st q (finite_pattern_variables y) ?g"
      using True unfolding finite_socket_kept_framed_def by auto
    have decl': "(resolution_node_site nd,resolution_node_schema nd,last q,True,Vp,Vh) |\<in>| declared_sockets D"
      using nd'(3) same[OF nd'(1,2)] by simp
    have framed: "socket_framed ?M (resolution_node_schema nd) (last q) True Vp Vh (fset C)"
      by (rule finite_frame_at_framed[OF discharged frames decl' fa formed])
    have vf: "view_formed Vp" "view_formed Vh" using views[OF decl'] by simp_all
    show ?thesis unfolding finite_exchange_context_def
      using finite_framed_kept_context[OF I sup gF' nf q np vp ground ctx socket_framed_viewed[OF framed]
        socket_framed_calls[OF framed, where N="\<lambda>_. True"] vf holders order_refl] by simp
  next
    case False
    have free: "finite_socket_free_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) ?g"
      using decl False by (simp add: finite_socket_declared_framed_def)
    obtain nd0 where nd0: "nd0 |\<in>| resolution_nodes st" "resolution_node_position nd0 = butlast q"
      and ka: "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) ?g \<or>
        finite_input_output_apart Vh nd0"
      using cn gq vp unfolding finite_call_framed_def by auto
    have apart: "finite_input_output_apart Vh nd" using ka False same[OF nd0] by blast
    obtain nd' C' where root: "F = Some (butlast q)"
      and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,False,Vp,Vh) |\<in>| declared_sockets D"
      and fa': "finite_frame_at \<Phi> Vp Vh (resolution_node_site nd') (resolution_node_schema nd') (last q) ch = Some C'"
      and absorbs': "finite_parent_absorbs Vp Vh C' nd' (last q)"
      and holders': "finite_socket_holders F st q
        (finite_pattern_variables y |\<union>| finite_parent_absorbed Vp Vh C' nd' (last q)) ?g"
      using free unfolding finite_socket_free_framed_def by (auto split: option.splits)
    have ndd: "nd' = nd" by (rule same[OF nd'(1,2)])
    have CC: "C' = C" using fa fa' ndd by simp
    have decl': "(resolution_node_site nd,resolution_node_schema nd,last q,False,Vp,Vh) |\<in>| declared_sockets D"
      using nd'(3) ndd by simp
    have absorbs: "finite_parent_absorbs Vp Vh C nd (last q)" using absorbs' ndd CC by simp
    have holders: "finite_socket_holders F st q
        (finite_pattern_variables y |\<union>| finite_parent_absorbed Vp Vh C nd (last q)) ?g"
      using holders' ndd CC by simp
    have framed: "socket_framed ?M (resolution_node_schema nd) (last q) False Vp Vh (fset C)"
      by (rule finite_frame_at_framed[OF discharged frames decl' fa formed])
    have vf: "view_formed Vp" "view_formed Vh" using views[OF decl'] by simp_all
    show ?thesis unfolding finite_exchange_context_def
      using finite_framed_free_context[OF I sup gF' root q np vp ground ctx socket_framed_viewed[OF framed]
        socket_framed_calls[OF framed, where N="\<lambda>_. True"] vf absorbs apart holders order_refl] by simp
  qed
  have g': "?g |\<in>| resolution_pending st" using gF' by (simp add: finite_focus_pending_focused)
  have parent': "finite_goal_premise st ?g" using parent gq by simp
  have unheld': "\<not> finite_held \<kappa> st ?g" using unheld gq by simp
  have gpos: "resolution_goal_position g = q" using gq by simp
  have s0': "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some q) B st)"
    using s0 by (simp only: gpos)
  show ?thesis unfolding gpos
    by (rule finite_committed_exchange_context[OF \<kappa> I sup g' parent' only H unheld' ctxE s0'])
qed

text \<open>
  Today's socket exchange is the framed one's instance at no frames: every call today's test commits the framed test
  commits (B1's containment, at the headed nodes the invariant gives).
\<close>

theorem finite_socket_commitment_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>" and gF: "g |\<in>| finite_focus_pending F st"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and committed: "finite_goal_committed (finite_declared_commitment D) F st g"
    and socket: "\<not> finite_direct_commitment D F st g"
    and only: "finite_registrations_premise_only \<kappa> P" and H: "resolution_registrations_held \<kappa> st"
    and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_declared_commitment D) P n
      (Some (resolution_goal_position g)) B st)"
  shows "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        (finite_declared_commitment D) P n (Some (resolution_goal_position g)) B st)) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  have cc: "commit_call (finite_declared_commitment D) F st g" and nf0: "F \<noteq> Some (resolution_goal_position g)"
    using committed by (simp_all add: finite_goal_committed_def)
  have cc': "commit_call (finite_framed_commitment D {||}) F st g"
    by (rule finite_framed_commitment_call[OF cc finite_invariant_headed[OF I]])
  show ?thesis
    by (rule finite_framed_socket_exchange[OF \<kappa> I sup gF discharged no_frames_discharged cc' nf0 socket only H unheld s0])
qed

text \<open>
  #565's exchange premise, its dispatch stated once: at any commitment with no production whose call and material
  commitments the framed test makes at every invariant state, the direct producer's discharge
  (@{text finite_direct_exchange}) and the sockets' (@{text finite_framed_socket_exchange}), both stated for the found
  states of any committed search, and the material single solution's
  (@{text finite_framed_material_commitment_exchanges}) after the containment, from the declarations' and the frames'
  discharge, a formed construction and premise-only registrations. The framed test is its instance, and today's
  declared test at no frames (B1's containment at the headed nodes the invariant gives).
\<close>

theorem finite_framed_contained_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and none: "\<And>F st g. commit_production K F st g = None"
    and calls: "\<And>d t st F g. resolution_invariant P d t st \<Longrightarrow> commit_call K F st g \<Longrightarrow>
      commit_call (finite_framed_commitment D \<Phi>) F st g"
    and materials: "\<And>d t st F g. resolution_invariant P d t st \<Longrightarrow> commit_material K F st g \<Longrightarrow>
      commit_material (finite_framed_commitment D \<Phi>) F st g"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> K P"
  unfolding finite_commitment_exchanges_unproduced[OF none]
proof (intro allI impI conjI)
  fix n F B st \<theta> g d t s0 B0 \<theta>0
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and committed: "finite_goal_committed K F st g"
    and H: "resolution_registrations_held \<kappa> st" and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g)) B st)"
    and "resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
  have cc0: "commit_call K F st g" and nf0: "F \<noteq> Some (resolution_goal_position g)"
    using committed by (simp_all add: finite_goal_committed_def)
  have cc: "commit_call (finite_framed_commitment D \<Phi>) F st g" by (rule calls[OF I cc0])
  show "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        K P n (Some (resolution_goal_position g)) B st)) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
  proof (cases "finite_direct_commitment D F st g")
    case True
    have parent: "finite_goal_premise st g" by (rule finite_framed_commitment_premise[OF cc])
    show ?thesis by (rule finite_direct_exchange[OF \<kappa> I sup gF discharged True parent only H unheld s0])
  next
    case False
    show ?thesis by (rule finite_framed_socket_exchange[OF \<kappa> I sup gF discharged frames cc nf0 False only H unheld s0])
  qed
next
  fix n F B st \<theta> g d t q r M Ws
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material K F st g"
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at (\<lambda>_. False) F (finite_committed_barring B st) P st' \<theta>'"
    by (rule finite_framed_material_commitment_exchanges[OF discharged frames I sup gF gq Ws materials[OF I cm]])
qed

text \<open>
  #565's exchange premise at the declared commitment, with no hypothesis on the state: the dispatch's instance at no
  frames, every call and material premise today's test commits the framed test committing at the headed nodes the
  invariant gives.
\<close>

theorem finite_declared_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment D) P"
proof (rule finite_framed_contained_exchanges[OF \<kappa> discharged no_frames_discharged only
    finite_declared_commitment_production])
  fix d t st F g
  assume I: "resolution_invariant P d t st" and c: "commit_call (finite_declared_commitment D) F st g"
  show "commit_call (finite_framed_commitment D {||}) F st g"
    by (rule finite_framed_commitment_call[OF c finite_invariant_headed[OF I]])
next
  fix d t st F g
  assume I: "resolution_invariant P d t st" and c: "commit_material (finite_declared_commitment D) F st g"
  show "commit_material (finite_framed_commitment D {||}) F st g"
    by (rule finite_framed_commitment_material[OF c finite_invariant_headed[OF I]])
qed

text \<open>
  #565's exchange premise at the framed test, with no hypothesis on the state (B2a of correction (10)): the dispatch's
  (@{text finite_framed_contained_exchanges}) instance at the framed test itself. What remains is the declarations' and
  the frames' discharge, a formed construction and a program whose registrations are premise-only.
\<close>

theorem finite_framed_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_framed_commitment D \<Phi>) P"
  by (rule finite_framed_contained_exchanges[OF \<kappa> discharged frames only finite_framed_commitment_production]) simp_all

end