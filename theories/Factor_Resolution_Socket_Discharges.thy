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
  closed siblings hold only its inputs (correction (9)).
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

lemma resolution_value_agree:
  "resolution_value \<theta> p = resolution_value \<theta>' p \<Longrightarrow> z |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> z = \<theta>' z"
  by (induction p) (auto simp: resolution_value_def)

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
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?q = "resolution_goal_position g"
  let ?S = "resolution_node_schema np"
  let ?pos = "resolution_node_position np"
  let ?\<beta> = "finite_node_binding np"
  have nd: "np |\<in>| resolution_nodes st" and closed: "finite_children_closed Vp Vh st np k"
    using ctx by (simp_all add: finite_parent_context_def)
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
    using closed that unfolding finite_children_closed_def by auto
  have mat_cases: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site np,resolution_node_clause np,s)
      (finite_material_pattern_substitute ?\<beta> N) |\<in>| resolution_pending st \<or>
      resolution_pending_under st (?pos@[s]) = {||}"
    if "(s,N) |\<in>| finite_schema_materials ?S" for s N
    using closed that unfolding finite_children_closed_def by auto
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

lemma finite_children_closed_children:
  assumes closed: "finite_children_closed Vp Vh st np k"
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
    using closed h unfolding finite_children_closed_def by blast
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

section \<open>What a socket's obligation gives at a new answer\<close>

text \<open>
  At a new answer of the committed goal, the obligation gives a true instance of the parent clause with that answer at the
  socket's viewed output, keeping the socket's inputs (@{text socket_inputs_kept}) and relating its head to the support's
  instance as the declaration's kept head says.
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
  let ?\<beta> = "finite_node_binding np"
  let ?g = "Resolution_Call_Goal q r e p"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent1: "clause_true ?M (decode_finite_schema ?S) ?h"
    by (rule finite_parent_instance_true(1)[OF I sup gF nf' q' np' ctx])
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  have hxi: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if "c |\<in>| finite_pattern_variables xi0" for c
    by (rule finite_parent_instance_true(2)[OF I sup gF nf' q' np' ctx prem0]) (simp add: pvars that)
  have formed_S: "schema_formed (decode_finite_schema ?S)"
  proof -
    have linked: "resolution_node_linked P st np" using ctx by (simp add: finite_parent_context_def)
    have cl: "((resolution_node_site np,resolution_node_clause np),?S) |\<in>| finite_system_clauses P"
      using linked unfolding resolution_node_linked_def by blast
    have "finite_system_formed P" using I by (simp add: resolution_invariant_def)
    then have "finite_schema_formed ?S" using cl unfolding finite_system_formed_def by auto
    then show ?thesis by (simp add: finite_schema_formed_correct)
  qed
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
  obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'" and hk: "head_kept keep Vh ?S ?h h'"
    and ins: "\<forall>a\<in>socket_inputs Vp Vh ?S (last q). h' a = ?h a"
    and hy: "evaluate_pattern h' (decode_finite_pattern yo0) =
      decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute ?\<beta> yo0))"
    using socket_inputs_kept(1)[OF obl formed_S parent1 prem0 vp0 new vt] by blast
  have formed': "term_formed (h' c)" if "c |\<in>| finite_schema_variables ?S" for c
    using tr' that unfolding clause_true_def by (simp add: finite_schema_variables_correct[symmetric])
  have hy_agree: "h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
  proof -
    have "evaluate_pattern h' (decode_finite_pattern yo0) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta>2 (?\<beta> a))) (decode_finite_pattern yo0)"
      using hy by (simp add: resolution_value_substitute_decoded)
    then show ?thesis by (rule evaluate_pattern_agree) (simp add: that finite_pattern_variables_correct[symmetric])
  qed
  show thesis by (rule that[OF tr' hk ins]) (erule hy_agree, erule formed')
qed

section \<open>The socket declared with the kept head\<close>

text \<open>
  At a socket declared with the kept head, the context of #565's exchange follows from the socket's obligation over the
  parent context. The support and the closed premises make the parent clause's instance true; the obligation gives, for
  the new answer, a true instance keeping the head, which fixes every head variable, and the socket's inputs, which fixes
  every premise-only variable among them. The new grounding takes the new answer at the goal's viewed output, the new
  instance's values at the free premise-only variables, which no call of the parent holds, and the support's elsewhere;
  the holders test and the free premise-only variables' holders keep every goal outside the parent at its values.
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
  let ?g = "Resolution_Call_Goal q r e p"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  let ?z = "\<lambda>a. ((resolution_node_position np,True),a)"
  let ?SV = "finite_schema_variables ?S"
  let ?cv = "finite_pattern_variables (finite_schema_conclusion ?S)"
  have nd: "np |\<in>| resolution_nodes st" and closed: "finite_children_closed Vp Vh st np (last q)"
    and poi: "finite_premise_only_inputs Vp Vh st np (last q)" and unsh: "finite_premise_only_unshared np"
    using ctx by (simp_all add: finite_parent_context_def)
  note linked = finite_node_binding_linked[OF I nd]
  have sv: "single_valued (fset (resolution_node_bindings np))" unfolding linked(1) by (auto simp: single_valued_def)
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  note children = finite_children_closed_children[OF closed]
  have viewed: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises ?S \<longrightarrow> resolution_view_pattern Vp p0 \<noteq> None"
    using obl unfolding socket_discharged_def by blast
  obtain p0 xi0 yo0 where prem0: "(last q,e,p0) |\<in>| finite_schema_premises ?S"
    and pp: "p = finite_pattern_substitute ?\<beta> p0" and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and xy: "x = finite_pattern_substitute ?\<beta> xi0" "y = finite_pattern_substitute ?\<beta> yo0"
    by (rule finite_socket_premise[OF children[OF gp gchild] vp viewed])
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent2: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,e',p') |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p'" for s e' p' c
    by (rule finite_parent_instance_true(2)[OF I sup gF nf' q' np' ctx that])
  have parent3: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_parent_instance_true(3)[OF I sup gF nf' q' np' ctx that])
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  have yo_S: "c |\<in>| ?SV" if "c |\<in>| finite_pattern_variables yo0" for c
    by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: pvars that)
  have hyo: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
    by (rule parent2[OF prem0]) (simp add: pvars that)
  define fpo where "fpo = (\<lambda>a. ?\<beta> a = Finite_Variable (?z a) \<and> (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow>
      ?z a |\<in>| resolution_goal_variables h \<longrightarrow>
      resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np))"
  have po_cases: "fpo a \<or> (a |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> a) = {||})"
    if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    unfolding fpo_def by (rule finite_premise_only_bound[OF poi sv that])
  have po_call: "?z a |\<notin>| finite_pattern_variables (resolution_node_call np)" if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    using unsh that unfolding finite_premise_only_unshared_def by auto
  define Zs where "Zs = (\<lambda>z. fst z = (resolution_node_position np,True) \<and> snd z |\<in>| ?SV \<and> snd z |\<notin>| ?cv \<and> fpo (snd z))"
  have Zs_z: "z = ?z (snd z)" "snd z |\<in>| ?SV" "snd z |\<notin>| ?cv" "fpo (snd z)" if "Zs z" for z
    using that by (auto simp: Zs_def prod_eq_iff)
  have Zs_call: "z |\<notin>| finite_pattern_variables (resolution_node_call np)" if "Zs z" for z
    using po_call[OF Zs_z(2)[OF that] Zs_z(3)[OF that]] Zs_z(1)[OF that] by metis
  have pv: "finite_pattern_variables p = finite_pattern_variables x |\<union>| finite_pattern_variables y"
    by (rule resolution_view_pattern_variables[OF Vp vp])
  have groundxi: "finite_pattern_variables (finite_pattern_substitute ?\<beta> xi0) = {||}" using ground xy(1) by simp
  show ?thesis unfolding finite_exchange_context_def
  proof (intro allI impI)
    fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M"
    obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
      and hk: "head_kept True Vh ?S ?h h'"
      and ins: "\<forall>a\<in>socket_inputs Vp Vh ?S (last q). h' a = ?h a"
      and hy_agree: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))"
      and formed': "\<And>c. c |\<in>| ?SV \<Longrightarrow> term_formed (h' c)"
      by (rule finite_socket_new_instance[OF I sup gF nf q np ctx obl Vp prem0 vp0 pp groundxi new]) blast
    have kept_h: "h' c = ?h c" if "c |\<in>| ?cv" for c by (rule head_kept_variables[OF hk Vh that])
    have ycases: "(\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and> c |\<notin>| ?cv \<and> fpo c \<and> z = ?z c) \<or>
        (z |\<in>| finite_pattern_variables (resolution_node_call np) \<and> \<theta>2 z = \<theta> z)"
      if zy: "z |\<in>| finite_pattern_variables y" for z
    proof -
      obtain c where c: "c |\<in>| finite_pattern_variables yo0" "z |\<in>| finite_pattern_variables (?\<beta> c)"
        using finite_pattern_substitute_origin[OF zy[unfolded xy(2)]] by blast
      show ?thesis
      proof (cases "c |\<in>| ?cv")
        case True
        have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)"
          unfolding linked(2) by (rule finite_pattern_substitute_variable[where \<sigma>="finite_node_binding np", OF True c(2)])
        have "decode_finite_term (resolution_value \<theta>2 (?\<beta> c)) = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
          using hy_agree[OF c(1)] kept_h[OF True] hyo[OF c(1)] by simp
        then have "resolution_value \<theta>2 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by simp
        then have "\<theta>2 z = \<theta> z" by (rule resolution_value_agree) (rule c(2))
        then show ?thesis using zc by blast
      next
        case False
        from po_cases[OF yo_S[OF c(1)] False] show ?thesis
        proof
          assume f: "fpo c"
          have "z = ?z c" using c(2) f unfolding fpo_def by simp
          then show ?thesis using c(1) False f by blast
        next
          assume "c |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> c) = {||}"
          then show ?thesis using c(2) by simp
        qed
      qed
    qed
    define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables y then \<theta>2 z
      else if Zs z then finite_term_of (h' (snd z)) else \<theta> z)"
    have K: "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      if cS: "c |\<in>| ?SV" and hc: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" for c
    proof (cases "c |\<in>| ?cv")
      case concl: True
      have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for z
      proof -
        have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)"
          unfolding linked(2) by (rule finite_pattern_substitute_variable[where \<sigma>="finite_node_binding np", OF concl z])
        show ?thesis
        proof (cases "z |\<in>| finite_pattern_variables y")
          case zy: True
          from ycases[OF zy] show ?thesis
          proof (elim disjE exE conjE)
            fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<notin>| ?cv" "fpo c'" "z = ?z c'"
            have "z |\<notin>| finite_pattern_variables (resolution_node_call np)"
              using po_call[OF yo_S[OF c'(1)] c'(2)] c'(4) by simp
            with zc show ?thesis by simp
          next
            assume "z |\<in>| finite_pattern_variables (resolution_node_call np)" "\<theta>2 z = \<theta> z"
            then show ?thesis using zy by (simp add: \<theta>1_def)
          qed
        next
          case ny: False
          have "\<not> Zs z" using Zs_call zc by blast
          then show ?thesis using ny by (simp add: \<theta>1_def)
        qed
      qed
      have "resolution_value \<theta>1 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by (rule resolution_value_cong) (rule same)
      then show ?thesis using kept_h[OF concl] hc by simp
    next
      case nconcl: False
      from po_cases[OF cS nconcl] show ?thesis
      proof
        assume f: "fpo c"
        have bc: "?\<beta> c = Finite_Variable (?z c)" using f unfolding fpo_def by blast
        show ?thesis
        proof (cases "?z c |\<in>| finite_pattern_variables y")
          case zy: True
          from ycases[OF zy] show ?thesis
          proof (elim disjE exE conjE)
            fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<notin>| ?cv" "fpo c'" "?z c = ?z c'"
            then have cc: "c' = c" by simp
            show ?thesis using hy_agree[OF c'(1)] zy bc cc by (simp add: \<theta>1_def)
          next
            assume "?z c |\<in>| finite_pattern_variables (resolution_node_call np)" "\<theta>2 (?z c) = \<theta> (?z c)"
            with po_call[OF cS nconcl] show ?thesis by simp
          qed
        next
          case ny: False
          have "Zs (?z c)" using cS nconcl f by (simp add: Zs_def)
          then show ?thesis using ny bc decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
        qed
      next
        assume gr: "c |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> c) = {||}"
        have "resolution_value \<theta>1 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by (rule resolution_value_cong) (use gr in simp)
        moreover have "c \<in> socket_inputs Vp Vh ?S (last q)" using gr by (simp add: finite_socket_inputs_correct[symmetric])
        then have "h' c = ?h c" using ins by blast
        ultimately show ?thesis using hc by simp
      qed
    qed
    have unchanged: "\<And>h0 z. h0 |\<in>| finite_focus_pending F st \<Longrightarrow>
        \<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np) \<Longrightarrow>
        z |\<in>| resolution_goal_variables h0 \<Longrightarrow> \<theta>1 z = \<theta> z"
    proof -
      fix h0 z assume h0: "h0 |\<in>| finite_focus_pending F st"
        and nc: "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
        and z: "z |\<in>| resolution_goal_variables h0"
      have ny: "z |\<notin>| finite_pattern_variables y"
      proof
        assume zy: "z |\<in>| finite_pattern_variables y"
        have "h0 = ?g \<or> resolution_goal_variables h0 |\<inter>| finite_pattern_variables y = {||} \<or>
            (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q)"
          using holders h0 unfolding finite_socket_holders_def by auto
        then show False
        proof (elim disjE)
          assume "h0 = ?g" then show False using nc gchild by simp
        next
          assume d: "resolution_goal_variables h0 |\<inter>| finite_pattern_variables y = {||}"
          have "z |\<in>| resolution_goal_variables h0 |\<inter>| finite_pattern_variables y" using z zy by simp
          then show False using d by simp
        next
          assume "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q"
          then show False using nc np by simp
        qed
      qed
      have nZ: "\<not> Zs z"
      proof
        assume Z: "Zs z"
        have h0p: "h0 |\<in>| resolution_pending st" using h0 by (simp add: finite_focus_pending_focused)
        have zz: "?z (snd z) |\<in>| resolution_goal_variables h0" using z Zs_z(1)[OF Z] by metis
        have "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np"
          using Zs_z(4)[OF Z] h0p zz unfolding fpo_def by blast
        with nc show False by blast
      qed
      show "\<theta>1 z = \<theta> z" using ny nZ by (simp add: \<theta>1_def)
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
    show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h)"
      using holds ground pv by (intro exI[of _ \<theta>1]) (auto simp: \<theta>1_def)
  qed
qed

section \<open>The socket declared without the kept head\<close>

text \<open>
  At a socket declared without the kept head, the parent is the focus root and its call's viewed output is a variant of
  its clause's viewed head output, which the obligation's new instance may change: each variable of the call's output
  takes the new instance's value of the head variable it binds, the head's viewed input is kept, and the call's viewed
  input, sharing no variable with its output, keeps its values. The holders test covers the variables of the call's
  output beside the goal's.
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
  let ?g = "Resolution_Call_Goal q r e p"
  let ?S = "resolution_node_schema np"
  let ?\<beta> = "finite_node_binding np"
  let ?h = "finite_instance_valuation \<theta> ?\<beta>"
  let ?z = "\<lambda>a. ((resolution_node_position np,True),a)"
  let ?SV = "finite_schema_variables ?S"
  let ?cv = "finite_pattern_variables (finite_schema_conclusion ?S)"
  have "length (butlast q) \<noteq> length q" using q by (cases q) simp_all
  then have "butlast q \<noteq> q" by metis
  then have nf: "F \<noteq> Some q" using root by simp
  have nd: "np |\<in>| resolution_nodes st" and closed: "finite_children_closed Vp Vh st np (last q)"
    and poi: "finite_premise_only_inputs Vp Vh st np (last q)" and unsh: "finite_premise_only_unshared np"
    using ctx by (simp_all add: finite_parent_context_def)
  note linked = finite_node_binding_linked[OF I nd]
  have sv: "single_valued (fset (resolution_node_bindings np))" unfolding linked(1) by (auto simp: single_valued_def)
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  note children = finite_children_closed_children[OF closed]
  have viewed: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises ?S \<longrightarrow> resolution_view_pattern Vp p0 \<noteq> None"
    using obl unfolding socket_discharged_def by blast
  obtain p0 xi0 yo0 where prem0: "(last q,e,p0) |\<in>| finite_schema_premises ?S"
    and pp: "p = finite_pattern_substitute ?\<beta> p0" and vp0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    and xy: "x = finite_pattern_substitute ?\<beta> xi0" "y = finite_pattern_substitute ?\<beta> yo0"
    by (rule finite_socket_premise[OF children[OF gp gchild] vp viewed])
  obtain hi ho where vc: "resolution_view_pattern Vh (finite_schema_conclusion ?S) = Some (hi,ho)"
    and vk: "resolution_view_pattern Vh (resolution_node_call np) = Some (finite_pattern_substitute ?\<beta> hi,out)"
    and xo: "out = finite_pattern_substitute ?\<beta> ho" and variant: "finite_variant ho out"
    by (rule finite_parent_output_parts[OF po linked(2)])
  let ?xc = "finite_pattern_substitute ?\<beta> hi"
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent2: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,e',p') |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p'" for s e' p' c
    by (rule finite_parent_instance_true(2)[OF I sup gF nf' q' np' ctx that])
  have parent3: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_parent_instance_true(3)[OF I sup gF nf' q' np' ctx that])
  have pvars: "finite_pattern_variables p0 = finite_pattern_variables xi0 |\<union>| finite_pattern_variables yo0"
    by (rule resolution_view_pattern_variables[OF Vp vp0])
  have yo_S: "c |\<in>| ?SV" if "c |\<in>| finite_pattern_variables yo0" for c
    by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: pvars that)
  have hyo: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
    by (rule parent2[OF prem0]) (simp add: pvars that)
  define fpo where "fpo = (\<lambda>a. ?\<beta> a = Finite_Variable (?z a) \<and> (\<forall>h. h |\<in>| resolution_pending st \<longrightarrow>
      ?z a |\<in>| resolution_goal_variables h \<longrightarrow>
      resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np))"
  have po_cases: "fpo a \<or> (a |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> a) = {||})"
    if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    unfolding fpo_def by (rule finite_premise_only_bound[OF poi sv that])
  have po_call: "?z a |\<notin>| finite_pattern_variables (resolution_node_call np)" if "a |\<in>| ?SV" "a |\<notin>| ?cv" for a
    using unsh that unfolding finite_premise_only_unshared_def by auto
  have cvs: "?cv = finite_pattern_variables hi |\<union>| finite_pattern_variables ho"
    by (rule resolution_view_pattern_variables[OF Vh vc])
  have callv: "finite_pattern_variables (resolution_node_call np) =
      finite_pattern_variables ?xc |\<union>| finite_pattern_variables out"
    by (rule resolution_view_pattern_variables[OF Vh vk])
  have disj: "finite_pattern_variables ?xc |\<inter>| finite_pattern_variables out = {||}"
    using apart vk unfolding finite_input_output_apart_def by simp
  have xcv: "z |\<in>| finite_pattern_variables ?xc"
    if "c |\<in>| finite_pattern_variables hi" "z |\<in>| finite_pattern_variables (?\<beta> c)" for c z
    by (rule finite_pattern_substitute_variable[where \<sigma>="finite_node_binding np", OF that])
  have outv: "z |\<in>| finite_pattern_variables out"
    if "c |\<in>| finite_pattern_variables ho" "z |\<in>| finite_pattern_variables (?\<beta> c)" for c z
    unfolding xo by (rule finite_pattern_substitute_variable[where \<sigma>="finite_node_binding np", OF that])
  have variant': "finite_variant ho (finite_pattern_substitute ?\<beta> ho)" using variant xo by simp
  define Zs where "Zs = (\<lambda>z. fst z = (resolution_node_position np,True) \<and> snd z |\<in>| ?SV \<and> snd z |\<notin>| ?cv \<and> fpo (snd z))"
  have Zs_z: "z = ?z (snd z)" "snd z |\<in>| ?SV" "snd z |\<notin>| ?cv" "fpo (snd z)" if "Zs z" for z
    using that by (auto simp: Zs_def prod_eq_iff)
  have Zs_call: "z |\<notin>| finite_pattern_variables (resolution_node_call np)" if "Zs z" for z
    using po_call[OF Zs_z(2)[OF that] Zs_z(3)[OF that]] Zs_z(1)[OF that] by metis
  have pv: "finite_pattern_variables p = finite_pattern_variables x |\<union>| finite_pattern_variables y"
    by (rule resolution_view_pattern_variables[OF Vp vp])
  have groundxi: "finite_pattern_variables (finite_pattern_substitute ?\<beta> xi0) = {||}" using ground xy(1) by simp
  show ?thesis unfolding finite_exchange_context_def
  proof (intro allI impI)
    fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M"
    obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
      and hk: "head_kept False Vh ?S ?h h'"
      and ins: "\<forall>a\<in>socket_inputs Vp Vh ?S (last q). h' a = ?h a"
      and hy_agree: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (?\<beta> c))"
      and formed': "\<And>c. c |\<in>| ?SV \<Longrightarrow> term_formed (h' c)"
      by (rule finite_socket_new_instance[OF I sup gF nf q np ctx obl Vp prem0 vp0 pp groundxi new]) blast
    have input_h: "h' c = ?h c" if "c |\<in>| finite_pattern_variables hi" for c
      by (rule evaluate_pattern_agree[OF head_kept_input[OF hk vc]]) (simp add: that finite_pattern_variables_correct[symmetric])
    have ycases: "(\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and> c |\<notin>| ?cv \<and> fpo c \<and> z = ?z c) \<or>
        (\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and> c |\<in>| finite_pattern_variables ho \<and> z |\<in>| finite_pattern_variables (?\<beta> c)) \<or>
        (z |\<in>| finite_pattern_variables ?xc \<and> \<theta>2 z = \<theta> z)"
      if zy: "z |\<in>| finite_pattern_variables y" for z
    proof -
      obtain c where c: "c |\<in>| finite_pattern_variables yo0" "z |\<in>| finite_pattern_variables (?\<beta> c)"
        using finite_pattern_substitute_origin[OF zy[unfolded xy(2)]] by blast
      show ?thesis
      proof (cases "c |\<in>| finite_pattern_variables ho")
        case True
        then show ?thesis using c by blast
      next
        case notho: False
        show ?thesis
        proof (cases "c |\<in>| finite_pattern_variables hi")
          case True
          have "decode_finite_term (resolution_value \<theta>2 (?\<beta> c)) = decode_finite_term (resolution_value \<theta> (?\<beta> c))"
            using hy_agree[OF c(1)] input_h[OF True] hyo[OF c(1)] by simp
          then have "resolution_value \<theta>2 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by simp
          then have "\<theta>2 z = \<theta> z" by (rule resolution_value_agree) (rule c(2))
          then show ?thesis using xcv[OF True c(2)] by blast
        next
          case False
          have nc: "c |\<notin>| ?cv" using False notho cvs by simp
          from po_cases[OF yo_S[OF c(1)] nc] show ?thesis
          proof
            assume f: "fpo c"
            have "z = ?z c" using c(2) f unfolding fpo_def by simp
            then show ?thesis using c(1) nc f by blast
          next
            assume "c |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> c) = {||}"
            then show ?thesis using c(2) by simp
          qed
        qed
      qed
    qed
    define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables y then \<theta>2 z
      else if Zs z then finite_term_of (h' (snd z))
      else if z |\<in>| finite_pattern_variables out
        then finite_term_of (h' (SOME b. b |\<in>| finite_pattern_variables ho \<and> ?\<beta> b = Finite_Variable z))
      else \<theta> z)"
    have K: "decode_finite_term (resolution_value \<theta>1 (?\<beta> c)) = h' c"
      if cS: "c |\<in>| ?SV" and hc: "?h c = decode_finite_term (resolution_value \<theta> (?\<beta> c))" for c
    proof (cases "c |\<in>| finite_pattern_variables ho")
      case inho: True
      obtain w where bw: "?\<beta> c = Finite_Variable w" by (rule finite_variant_substitute_variable[OF variant' inho])
      have wu: "b = c" if "b |\<in>| finite_pattern_variables ho" "?\<beta> b = Finite_Variable w" for b
        using finite_variant_substitute_injective[OF variant' that(1) inho] that(2) bw by simp
      have wout: "w |\<in>| finite_pattern_variables out" using outv[OF inho] bw by simp
      have wcall: "w |\<in>| finite_pattern_variables (resolution_node_call np)" using wout callv by simp
      show ?thesis
      proof (cases "w |\<in>| finite_pattern_variables y")
        case wy: True
        from ycases[OF wy] show ?thesis
        proof (elim disjE exE conjE)
          fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<notin>| ?cv" "fpo c'" "w = ?z c'"
          have "w |\<notin>| finite_pattern_variables (resolution_node_call np)"
            using po_call[OF yo_S[OF c'(1)] c'(2)] c'(4) by simp
          with wcall show ?thesis by simp
        next
          fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
            "w |\<in>| finite_pattern_variables (?\<beta> c')"
          obtain w' where bw': "?\<beta> c' = Finite_Variable w'"
            by (rule finite_variant_substitute_variable[OF variant' c'(2)])
          have "?\<beta> c' = Finite_Variable w" using c'(3) bw' by simp
          then have cc: "c' = c" by (rule wu[OF c'(2)])
          show ?thesis using hy_agree[OF c'(1)] cc bw wy by (simp add: \<theta>1_def)
        next
          assume a1: "w |\<in>| finite_pattern_variables ?xc" "\<theta>2 w = \<theta> w"
          have "w |\<in>| finite_pattern_variables ?xc |\<inter>| finite_pattern_variables out" using a1(1) wout by simp
          then show ?thesis using disj by simp
        qed
      next
        case wny: False
        have "\<not> Zs w" using Zs_call wcall by blast
        moreover have "(SOME b. b |\<in>| finite_pattern_variables ho \<and> ?\<beta> b = Finite_Variable w) = c"
          by (rule some_equality) (use inho bw wu in blast)+
        ultimately show ?thesis using wny wout bw decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
      qed
    next
      case notho: False
      show ?thesis
      proof (cases "c |\<in>| finite_pattern_variables hi")
        case inhi: True
        have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| finite_pattern_variables (?\<beta> c)" for z
        proof -
          have zx: "z |\<in>| finite_pattern_variables ?xc" by (rule xcv[OF inhi z])
          have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)" using zx callv by simp
          have nout: "z |\<notin>| finite_pattern_variables out"
          proof
            assume "z |\<in>| finite_pattern_variables out"
            then have "z |\<in>| finite_pattern_variables ?xc |\<inter>| finite_pattern_variables out" using zx by simp
            then show False using disj by simp
          qed
          show ?thesis
          proof (cases "z |\<in>| finite_pattern_variables y")
            case zy: True
            from ycases[OF zy] show ?thesis
            proof (elim disjE exE conjE)
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<notin>| ?cv" "fpo c'" "z = ?z c'"
              have "z |\<notin>| finite_pattern_variables (resolution_node_call np)"
                using po_call[OF yo_S[OF c'(1)] c'(2)] c'(4) by simp
              with zc show ?thesis by simp
            next
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
                "z |\<in>| finite_pattern_variables (?\<beta> c')"
              have "z |\<in>| finite_pattern_variables out" by (rule outv[OF c'(2,3)])
              with nout show ?thesis by simp
            next
              assume "z |\<in>| finite_pattern_variables ?xc" "\<theta>2 z = \<theta> z"
              then show ?thesis using zy by (simp add: \<theta>1_def)
            qed
          next
            case ny: False
            have "\<not> Zs z" using Zs_call zc by blast
            then show ?thesis using ny nout by (simp add: \<theta>1_def)
          qed
        qed
        have "resolution_value \<theta>1 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by (rule resolution_value_cong) (rule same)
        then show ?thesis using input_h[OF inhi] hc by simp
      next
        case notin: False
        have nconcl: "c |\<notin>| ?cv" using notin notho cvs by simp
        from po_cases[OF cS nconcl] show ?thesis
        proof
          assume f: "fpo c"
          have bc: "?\<beta> c = Finite_Variable (?z c)" using f unfolding fpo_def by blast
          have zcall: "?z c |\<notin>| finite_pattern_variables (resolution_node_call np)" by (rule po_call[OF cS nconcl])
          show ?thesis
          proof (cases "?z c |\<in>| finite_pattern_variables y")
            case zy: True
            from ycases[OF zy] show ?thesis
            proof (elim disjE exE conjE)
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<notin>| ?cv" "fpo c'" "?z c = ?z c'"
              then have cc: "c' = c" by simp
              show ?thesis using hy_agree[OF c'(1)] zy bc cc by (simp add: \<theta>1_def)
            next
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
                "?z c |\<in>| finite_pattern_variables (?\<beta> c')"
              have "?z c |\<in>| finite_pattern_variables out" by (rule outv[OF c'(2,3)])
              with zcall callv show ?thesis by simp
            next
              assume "?z c |\<in>| finite_pattern_variables ?xc" "\<theta>2 (?z c) = \<theta> (?z c)"
              with zcall callv show ?thesis by simp
            qed
          next
            case ny: False
            have "Zs (?z c)" using cS nconcl f by (simp add: Zs_def)
            then show ?thesis using ny bc decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
          qed
        next
          assume gr: "c |\<in>| finite_socket_inputs Vp Vh ?S (last q) \<and> finite_pattern_variables (?\<beta> c) = {||}"
          have "resolution_value \<theta>1 (?\<beta> c) = resolution_value \<theta> (?\<beta> c)" by (rule resolution_value_cong) (use gr in simp)
          moreover have "c \<in> socket_inputs Vp Vh ?S (last q)" using gr by (simp add: finite_socket_inputs_correct[symmetric])
          then have "h' c = ?h c" using ins by blast
          ultimately show ?thesis using hc by simp
        qed
      qed
    qed
    have unchanged: "\<And>h0 z. h0 |\<in>| finite_focus_pending F st \<Longrightarrow>
        \<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np) \<Longrightarrow>
        z |\<in>| resolution_goal_variables h0 \<Longrightarrow> \<theta>1 z = \<theta> z"
    proof -
      fix h0 z assume h0: "h0 |\<in>| finite_focus_pending F st"
        and nc: "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
        and z: "z |\<in>| resolution_goal_variables h0"
      have nyo: "z |\<notin>| finite_pattern_variables y |\<union>| finite_pattern_variables out"
      proof
        assume zy: "z |\<in>| finite_pattern_variables y |\<union>| finite_pattern_variables out"
        have "h0 = ?g \<or> resolution_goal_variables h0 |\<inter>| (finite_pattern_variables y |\<union>| finite_pattern_variables out) = {||} \<or>
            (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q)"
          using holders h0 unfolding finite_socket_holders_def by auto
        then show False
        proof (elim disjE)
          assume "h0 = ?g" then show False using nc gchild by simp
        next
          assume d: "resolution_goal_variables h0 |\<inter>| (finite_pattern_variables y |\<union>| finite_pattern_variables out) = {||}"
          have "z |\<in>| resolution_goal_variables h0 |\<inter>| (finite_pattern_variables y |\<union>| finite_pattern_variables out)"
            using z zy by simp
          then show False using d by simp
        next
          assume "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = butlast q"
          then show False using nc np by simp
        qed
      qed
      have nZ: "\<not> Zs z"
      proof
        assume Z: "Zs z"
        have h0p: "h0 |\<in>| resolution_pending st" using h0 by (simp add: finite_focus_pending_focused)
        have zz: "?z (snd z) |\<in>| resolution_goal_variables h0" using z Zs_z(1)[OF Z] by metis
        have "resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np"
          using Zs_z(4)[OF Z] h0p zz unfolding fpo_def by blast
        with nc show False by blast
      qed
      show "\<theta>1 z = \<theta> z" using nyo nZ by (simp add: \<theta>1_def)
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
    show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h)"
      using holds ground pv by (intro exI[of _ \<theta>1]) (auto simp: \<theta>1_def)
  qed
qed

section \<open>At every state where the test commits\<close>

text \<open>
  At a socket commitment of the test the parent context holds (@{text finite_declared_socket_context}), at the socket's
  declared views and key, so the contexts' hypotheses are the test's conditions; the obligation and the views' formation
  come from the declarations' discharge. This holds at any discharged declarations and at every focus.
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
  let ?M = "positive_meaning (decode_finite_system P)"
  have cc: "commit_call (finite_declared_commitment D) F st g" and nf0: "F \<noteq> Some (resolution_goal_position g)"
    and call: "resolution_is_call g" using committed by (simp_all add: finite_goal_committed_def)
  have parent: "finite_goal_premise st g" by (rule finite_declared_commitment_premise[OF cc])
  obtain Vp Vh where sc: "finite_socket_commitment D Vp Vh F st g" and nar: "finite_call_narrowed D Vp Vh F st g"
    using cc socket call by (auto simp: finite_declared_commitment_def)
  obtain q r e p where gq: "g = Resolution_Call_Goal q r e p" using call by (cases g) simp_all
  let ?g = "Resolution_Call_Goal q r e p"
  have mn: "finite_material_narrowed D Vp Vh F st g" using gq by (simp add: finite_material_narrowed_def)
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
    and qne: "resolution_goal_position g \<noteq> []"
    and ctx0: "finite_parent_context P Vp Vh st nd (last (resolution_goal_position g))"
    by (rule finite_declared_socket_context[OF I sc nar mn])
  have q: "q \<noteq> []" and np: "resolution_node_position nd = butlast q"
    and ctx: "finite_parent_context P Vp Vh st nd (last q)" using qne nd(2) ctx0 gq by simp_all
  obtain x y where vp: "resolution_view_pattern Vp p = Some (x,y)" and ground: "finite_pattern_variables x = {||}"
    and decl: "finite_socket_declared D Vp Vh F st q (finite_pattern_variables y) ?g"
    using sc gq by (auto simp: finite_socket_commitment_def split: option.splits prod.splits)
  have gF': "?g |\<in>| finite_focus_pending F st" using gF gq by simp
  have nf: "F \<noteq> Some q" using nf0 gq by simp
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have same: "m = nd" if "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast q" for m
  proof -
    have "resolution_node_position m = resolution_node_position nd" using that(2) np by simp
    then show ?thesis using dist that(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  have sockets: "socket_discharged ?M S s keep Vp Vh \<and> view_formed Vp \<and> view_formed Vh"
    if "(e',S,s,keep,Vp,Vh) |\<in>| declared_sockets D" for e' S s keep
  proof -
    have "socket_discharged ?M S s keep Vp Vh" using discharged that unfolding declarations_discharged_def by blast
    moreover have "declarations_formed D" using discharged by (simp add: declarations_discharged_def)
    ultimately show ?thesis using that unfolding declarations_formed_def by auto
  qed
  have ctxE: "finite_exchange_context ?M F q st e p"
  proof (cases "finite_socket_kept D Vp Vh F st q (finite_pattern_variables y) ?g")
    case True
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,True,Vp,Vh) |\<in>| declared_sockets D"
      and holders: "finite_socket_holders F st q (finite_pattern_variables y) ?g"
      using True unfolding finite_socket_kept_def by auto
    have ndd: "nd' = nd" by (rule same[OF nd'(1,2)])
    have obl: "socket_discharged ?M (resolution_node_schema nd) (last q) True Vp Vh"
      and vf: "view_formed Vp" "view_formed Vh" using sockets[OF nd'(3)] ndd by simp_all
    show ?thesis
      by (rule finite_socket_kept_context[OF I sup gF' nf q np vp ground ctx obl vf holders])
  next
    case False
    then have free: "finite_socket_free D Vp Vh F st q (finite_pattern_variables y) ?g"
      using decl unfolding finite_socket_declared_def by blast
    obtain nd'' where nd'': "nd'' |\<in>| resolution_nodes st" "resolution_node_position nd'' = butlast q"
      and ka: "finite_socket_kept D Vp Vh F st q (finite_pattern_variables y) ?g \<or> finite_input_output_apart Vh nd''"
      using nar gq vp unfolding finite_call_narrowed_def by auto
    have apart: "finite_input_output_apart Vh nd" using ka False same[OF nd''] by blast
    obtain nd' out where root: "F = Some (butlast q)"
      and nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
        "(resolution_node_site nd',resolution_node_schema nd',last q,False,Vp,Vh) |\<in>| declared_sockets D"
      and po: "finite_parent_output Vh nd' = Some out"
      and holders: "finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out) ?g"
      using free unfolding finite_socket_free_def by (auto split: option.splits)
    have ndd: "nd' = nd" by (rule same[OF nd'(1,2)])
    have obl: "socket_discharged ?M (resolution_node_schema nd) (last q) False Vp Vh"
      and vf: "view_formed Vp" "view_formed Vh" using sockets[OF nd'(3)] ndd by simp_all
    show ?thesis
      by (rule finite_socket_free_context[OF I sup gF' root q np vp ground ctx obl vf po[unfolded ndd] apart holders])
  qed
  have g': "?g |\<in>| resolution_pending st" using gF' by (simp add: finite_focus_pending_focused)
  have parent': "finite_goal_premise st ?g" using parent gq by simp
  have unheld': "\<not> finite_held \<kappa> st ?g" using unheld gq by simp
  have gpos: "resolution_goal_position g = q" using gq by simp
  have s0': "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_declared_commitment D) P n (Some q) B st)"
    using s0 by (simp only: gpos)
  show ?thesis unfolding gpos
    by (rule finite_committed_exchange_context[OF \<kappa> I sup g' parent' only H unheld' ctxE s0'])
qed

text \<open>
  #565's exchange premise at the declared commitment, with no hypothesis on the state: the direct producer's discharge
  (@{text finite_direct_exchange}), the sockets' (@{text finite_socket_commitment_exchange}, at every focus, so at an inner
  commitment too) and the material single solution's (@{text finite_material_commitment_exchanges}), each from the state
  conditions the test checks where it commits. What remains is the declarations' discharge, a formed construction and a
  program whose registrations are premise-only.
\<close>

theorem finite_declared_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and pairs: "pair_declarations D"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment D) P"
  unfolding finite_commitment_exchanges_def
proof (intro allI impI conjI)
  fix n F B st \<theta> g d t s0 B0 \<theta>0
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and committed: "finite_goal_committed (finite_declared_commitment D) F st g"
    and H: "resolution_registrations_held \<kappa> st" and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_declared_commitment D) P n
      (Some (resolution_goal_position g)) B st)"
    and "resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
  show "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        (finite_declared_commitment D) P n (Some (resolution_goal_position g)) B st)) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
  proof (cases "finite_direct_commitment D F st g")
    case True
    have "commit_call (finite_declared_commitment D) F st g" using committed by (simp add: finite_goal_committed_def)
    then have parent: "finite_goal_premise st g" by (rule finite_declared_commitment_premise)
    show ?thesis by (rule finite_direct_exchange[OF \<kappa> I sup gF discharged True parent only H unheld s0])
  next
    case False
    show ?thesis by (rule finite_socket_commitment_exchange[OF \<kappa> I sup gF discharged committed False only H unheld s0])
  qed
next
  fix n F B st \<theta> g d t q r M Ws
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material (finite_declared_commitment D) F st g"
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at (\<lambda>_. False) F (finite_committed_barring B st) P st' \<theta>'"
    by (rule finite_material_commitment_exchanges[OF discharged I sup gF gq Ws cm])
qed

end
