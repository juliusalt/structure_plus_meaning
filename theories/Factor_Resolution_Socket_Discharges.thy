theory Factor_Resolution_Socket_Discharges
  imports Factor_Resolution_Material_Discharge
begin

text \<open>
  The socket kinds' discharges of #565's exchange premise (R5c\<Zprime>\<Zprime>\<Zprime>\<Zprime>a, task 630, of DECISIONS.md "The native evaluator
  constructs the missing witnesses by resolution", its section "Committed choice, for refusals"): at a socket declared
  with the kept head, at one declared without it, and at an inner commitment, the kept head's or the free socket's at a
  nested focus. A socket's exchange rebuilds its parent clause's instance from the socket's obligation
  (@{const socket_discharged}): the parent clause's instance under the support is true from its pending premises
  (@{text finite_instance_clause_true}, @{text finite_parent_instance_true}), the obligation gives a true instance with the
  new answer, and the goals under the parent are read as that instance's premises (@{text finite_parent_exchange_holds}),
  every other goal keeping its values. What the exchange needs of the state is stated as the hypotheses of the context
  lemmas: the parent's premises pending as its linked instances and every pending goal under it one of them, no premise-only
  variable of the parent held by its call, the socket's premise of the obligation's pair form, and at a free socket the
  call's input sharing no variable with its output. The commitment test checks them where it commits
  (@{const finite_call_narrowed}, @{const finite_material_narrowed}), so the exchange premise holds with no hypothesis on
  the state (@{text finite_declared_commitment_exchanges}).
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

section \<open>A parent clause's instance is true from its pending premises\<close>

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
  At a state, the parent node's premises are its linked instances, pending in the focus of the committed goal, which is one
  of them: the support makes each true and the instance of the parent clause true.
\<close>

lemma finite_parent_instance_true:
  assumes sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and nf: "F \<noteq> Some (resolution_goal_position g)"
    and q: "resolution_goal_position g \<noteq> []" and np: "resolution_node_position np = butlast (resolution_goal_position g)"
    and pend: "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st"
    and materials: "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)
        |\<in>| resolution_pending st"
  shows "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (finite_instance_valuation \<theta> \<beta>)"
    and "\<And>s e p c. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_pattern_variables p \<Longrightarrow>
      finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    and "\<And>s N c. (s,N) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow> c |\<in>| finite_material_variables N \<Longrightarrow>
      finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?q = "resolution_goal_position g"
  have focused: "resolution_focused F ?q" using gF by (simp add: finite_focus_pending_focused)
  have inF: "h |\<in>| finite_focus_pending F st"
    if "h |\<in>| resolution_pending st" "resolution_goal_position h = resolution_node_position np @ [s]" for h s
    using that resolution_focused_sibling[OF focused nf q, of s] np by (simp add: finite_focus_pending_focused)
  have formed: "\<And>e u. (e,u) \<in> ?M \<Longrightarrow> term_formed u"
  proof -
    fix e u assume "(e,u) \<in> ?M"
    from schema_call_formed_target[OF positive_meaning_formed[OF this]] show "term_formed u" by blast
  qed
  have prem: "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      (e0,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p0))) \<in> ?M"
  proof -
    fix s e0 p0 assume m: "(s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    obtain r' where h: "Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)
        |\<in>| resolution_pending st" using pend[OF m] by blast
    have "finite_goal_holds ?M \<theta> (Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0))"
      by (rule resolution_supported_at_holds[OF sup inF[OF h]]) simp
    then show "(e0,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p0))) \<in> ?M"
      by (simp add: finite_goal_holds_def)
  qed
  have mat: "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute \<beta> N0))"
  proof -
    fix s N0 assume m: "(s,N0) |\<in>| finite_schema_materials (resolution_node_schema np)"
    obtain r' where h: "Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)
        |\<in>| resolution_pending st" using materials[OF m] by blast
    have "finite_goal_holds ?M \<theta> (Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
      by (rule resolution_supported_at_holds[OF sup inF[OF h]]) simp
    then show "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
        (finite_material_pattern_substitute \<beta> N0))" by (simp add: finite_goal_holds_def)
  qed
  show "clause_true ?M (decode_finite_schema (resolution_node_schema np)) (finite_instance_valuation \<theta> \<beta>)"
    by (rule finite_instance_clause_true(1); (erule formed | erule prem | erule mat))
  show "finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema np)" "c |\<in>| finite_pattern_variables p" for s e p c
    by (rule finite_instance_clause_true(2)[OF _ _ _ that]; (erule formed | erule prem | erule mat))
  show "finite_instance_valuation \<theta> \<beta> c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials (resolution_node_schema np)" "c |\<in>| finite_material_variables N" for s N c
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

section \<open>What a socket's obligation gives at a new answer\<close>

lemma head_kept_whole:
  assumes "head_kept True S h h'"
  shows "evaluate_pattern h' (schema_conclusion S) = evaluate_pattern h (schema_conclusion S)"
  using assms by (cases "schema_conclusion S") (simp_all add: head_kept_def)

lemma head_kept_variables:
  assumes "head_kept True S h h'" "a \<in> pattern_variables (schema_conclusion S)"
  shows "h' a = h a"
  using evaluate_pattern_agree[OF head_kept_whole[OF assms(1)] assms(2)] .

lemma head_kept_input:
  assumes "head_kept keep S h h'" "schema_conclusion S = Pattern_Pair ci co"
  shows "evaluate_pattern h' ci = evaluate_pattern h ci"
  using assms by (simp add: head_kept_def)

text \<open>
  The committed goal is its parent's premise at the socket, under the parent's bindings; the obligation speaks of a pair
  premise, whose parts give the goal's input and output.
\<close>

lemma finite_socket_premise:
  assumes q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and gi: "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) =
          Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) =
          Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
    and pair: "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<longrightarrow>
      (\<exists>xi yo. p0 = Finite_Pattern_Pair xi yo)"
  obtains xi0 yo0 where "(last q,e,Finite_Pattern_Pair xi0 yo0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0"
proof -
  obtain s0 e0 p0 r0 where m0: "(s0,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and g0: "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) =
      Resolution_Call_Goal (resolution_node_position np @ [s0]) r0 e0 (finite_pattern_substitute \<beta> p0)"
    using gi by blast
  have qs: "q = resolution_node_position np @ [s0]" and ee: "e = e0"
    and pp: "Finite_Pattern_Pair x y = finite_pattern_substitute \<beta> p0" using g0 by simp_all
  have s0: "s0 = last q" using qs by simp
  obtain xi0 yo0 where p0: "p0 = Finite_Pattern_Pair xi0 yo0" using pair m0[unfolded s0] by blast
  show thesis by (rule that) (use m0 s0 ee p0 pp in simp_all)
qed

text \<open>A premise-only variable of the parent is bound to its own variable, which only the parent's children hold.\<close>

lemma finite_premise_only_bound:
  assumes only: "finite_premise_only_free st np"
    and bind: "resolution_node_bindings np = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema np))"
    and a: "a |\<in>| finite_schema_variables (resolution_node_schema np)"
      "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np))"
  shows "\<beta> a = Finite_Variable ((resolution_node_position np,True),a)"
    and "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> ((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h \<Longrightarrow>
      resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np"
proof -
  have "a |\<in>| finite_schema_variables (resolution_node_schema np) |-|
      finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np))" using a by simp
  from fbspec[OF only[unfolded finite_premise_only_free_def] this]
  have c: "(a,Finite_Variable ((resolution_node_position np,True),a)) |\<in>| resolution_node_bindings np"
    "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> ((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h \<Longrightarrow>
      resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np"
    by auto
  show "\<beta> a = Finite_Variable ((resolution_node_position np,True),a)" using c(1) bind by (auto simp: fimage.rep_eq)
  show "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np"
    if "h |\<in>| resolution_pending st" "((resolution_node_position np,True),a) |\<in>| resolution_goal_variables h" for h
    using c(2)[OF that] .
qed

text \<open>
  At a new answer of the committed goal, the obligation gives a true instance of the parent clause with that answer at the
  socket's output, relating its head to the support's instance as the declaration's kept head says.
\<close>

lemma finite_socket_new_instance:
  assumes sup: "resolution_supported_at U F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and pend: "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st"
    and materials: "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)
        |\<in>| resolution_pending st"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (last q) keep"
    and prem0: "(last q,e,Finite_Pattern_Pair xi0 yo0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    and xy: "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0"
    and ground: "finite_pattern_variables x = {||}"
    and new: "(e,decode_finite_term (resolution_value \<theta>2 (Finite_Pattern_Pair x y))) \<in> positive_meaning (decode_finite_system P)"
  obtains h' where "clause_true (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np)) h'"
    "head_kept keep (decode_finite_schema (resolution_node_schema np)) (finite_instance_valuation \<theta> \<beta>) h'"
    "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c))"
    "\<And>c. c |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow> term_formed (h' c)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?S = "resolution_node_schema np"
  let ?g = "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y)"
  let ?h = "finite_instance_valuation \<theta> \<beta>"
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent1: "clause_true ?M (decode_finite_schema ?S) ?h"
    by (rule finite_parent_instance_true(1)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np'];
      (erule pend | erule materials))
  have hxi: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))" if "c |\<in>| finite_pattern_variables xi0" for c
    by (rule finite_parent_instance_true(2)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np' _ _ prem0];
      (erule pend | erule materials)?) (use that in simp)
  have obl': "\<forall>d xi yo y'. (last q,d,Pattern_Pair xi yo) \<in> schema_premises (decode_finite_schema ?S) \<longrightarrow>
      (d,Pair_Term (evaluate_pattern ?h xi) y') \<in> ?M \<longrightarrow>
      (\<exists>h'. clause_true ?M (decode_finite_schema ?S) h' \<and> head_kept keep (decode_finite_schema ?S) ?h h' \<and>
        evaluate_pattern h' xi = evaluate_pattern ?h xi \<and> evaluate_pattern h' yo = y')"
    using obl parent1 unfolding socket_discharged_def by blast
  have dprem: "(last q,e,Pattern_Pair (decode_finite_pattern xi0) (decode_finite_pattern yo0)) \<in>
      schema_premises (decode_finite_schema ?S)"
    using prem0 by (force simp: decode_finite_call_pattern_def)
  have ex: "decode_finite_term (resolution_value \<theta> x) = evaluate_pattern ?h (decode_finite_pattern xi0)"
  proof -
    have "decode_finite_term (resolution_value \<theta> x) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta> (\<beta> a))) (decode_finite_pattern xi0)"
      unfolding xy(1) by (rule resolution_value_substitute_decoded)
    also have "\<dots> = evaluate_pattern ?h (decode_finite_pattern xi0)"
      by (rule evaluate_pattern_cong) (simp add: hxi finite_pattern_variables_correct[symmetric])
    finally show ?thesis .
  qed
  have vx: "resolution_value \<theta>2 x = resolution_value \<theta> x" by (rule resolution_value_cong) (simp add: ground)
  have newp: "(e,Pair_Term (evaluate_pattern ?h (decode_finite_pattern xi0)) (decode_finite_term (resolution_value \<theta>2 y)))
      \<in> ?M"
    using new by (simp add: vx ex)
  obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
    and hk: "head_kept keep (decode_finite_schema ?S) ?h h'"
    and hy: "evaluate_pattern h' (decode_finite_pattern yo0) = decode_finite_term (resolution_value \<theta>2 y)"
    using obl'[rule_format, OF dprem newp] by blast
  have formed': "term_formed (h' c)" if "c |\<in>| finite_schema_variables ?S" for c
    using tr' that unfolding clause_true_def by (simp add: finite_schema_variables_correct[symmetric])
  have hy_agree: "h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
  proof -
    have "evaluate_pattern h' (decode_finite_pattern yo0) =
        evaluate_pattern (\<lambda>a. decode_finite_term (resolution_value \<theta>2 (\<beta> a))) (decode_finite_pattern yo0)"
      using hy unfolding xy(2) by (simp add: resolution_value_substitute_decoded)
    then show ?thesis by (rule evaluate_pattern_agree) (simp add: that finite_pattern_variables_correct[symmetric])
  qed
  show thesis by (rule that[OF tr' hk]) (erule hy_agree, erule formed')
qed

section \<open>The socket declared with the kept head\<close>

text \<open>
  At a socket declared with the kept head, the context of #565's exchange follows from the socket's obligation. The
  support makes the parent clause's instance true; the obligation gives, for the new answer, a true instance keeping the
  head, which fixes every head variable, so an output variable a head variable's binding holds takes no new value (the
  kept head's gap, closed by the obligation wherever the socket's premise is a pair). The new grounding takes the new
  answer at the goal's output, the new instance's values at the premise-only variables, which no call of the parent holds,
  and the support's elsewhere; the holders test and the premise-only variables' holders keep every goal outside the
  parent at its values.
\<close>

theorem finite_socket_kept_context:
  assumes sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) |\<in>| finite_focus_pending F st"
    and nf: "F \<noteq> Some q" and ground: "finite_pattern_variables x = {||}"
    and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and bind: "resolution_node_bindings np = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema np))"
    and call: "resolution_node_call np = finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema np))"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (last q) True"
    and pend: "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st"
    and materials: "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)
        |\<in>| resolution_pending st"
    and children: "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) = resolution_node_position np \<Longrightarrow>
      (\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        h = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
    and only: "finite_premise_only_free st np"
    and image: "\<And>a. a |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np)) \<Longrightarrow>
      ((resolution_node_position np,True),a) |\<notin>| finite_pattern_variables (resolution_node_call np)"
    and pair: "\<And>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>xi yo. p0 = Finite_Pattern_Pair xi yo"
    and holders: "finite_socket_holders F st q (finite_pattern_variables y) (Resolution_Call_Goal q r e (Finite_Pattern_Pair x y))"
  shows "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e (Finite_Pattern_Pair x y)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y)"
  let ?S = "resolution_node_schema np"
  let ?h = "finite_instance_valuation \<theta> \<beta>"
  let ?z = "\<lambda>a. ((resolution_node_position np,True),a)"
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  obtain xi0 yo0 where prem0: "(last q,e,Finite_Pattern_Pair xi0 yo0) |\<in>| finite_schema_premises ?S"
    and xy: "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0"
  proof (rule finite_socket_premise[OF q np])
    show "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises ?S \<and>
        ?g = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials ?S \<and>
        ?g = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
      by (rule children[OF gp gchild])
    show "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises ?S \<longrightarrow> (\<exists>xi yo. p0 = Finite_Pattern_Pair xi yo)"
      using pair by blast
  qed
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent2: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,e',p') |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p'" for s e' p' c
    by (rule finite_parent_instance_true(2)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np' _ _ that];
      (erule pend | erule materials))
  have parent3: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_parent_instance_true(3)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np' _ _ that];
      (erule pend | erule materials))
  have hyo: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
    using parent2[OF prem0] that by simp
  have only_b: "\<beta> a = Finite_Variable (?z a)"
    if "a |\<in>| finite_schema_variables ?S" "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" for a
    by (rule finite_premise_only_bound(1)[OF only bind that])
  have only_h: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np"
    if "a |\<in>| finite_schema_variables ?S" "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
      "h |\<in>| resolution_pending st" "?z a |\<in>| resolution_goal_variables h" for a h
    by (rule finite_premise_only_bound(2)[OF only bind that(1,2) that(3,4)])
  define Zs where "Zs = (\<lambda>z. fst z = (resolution_node_position np,True) \<and> snd z |\<in>| finite_schema_variables ?S \<and>
    snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S))"
  have Zs_z: "z = ?z (snd z)" "snd z |\<in>| finite_schema_variables ?S"
      "snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" if "Zs z" for z
    using that by (auto simp: Zs_def prod_eq_iff)
  have Zs_call: "z |\<notin>| finite_pattern_variables (resolution_node_call np)" if "Zs z" for z
    using image[OF Zs_z(2)[OF that] Zs_z(3)[OF that]] Zs_z(1)[OF that] by metis
  show ?thesis unfolding finite_exchange_context_def
  proof (intro allI impI)
    fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 (Finite_Pattern_Pair x y))) \<in> ?M"
    obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
      and hk: "head_kept True (decode_finite_schema ?S) ?h h'"
      and hy_agree: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c))"
      and formed': "\<And>c. c |\<in>| finite_schema_variables ?S \<Longrightarrow> term_formed (h' c)"
      by (rule finite_socket_new_instance[OF sup gF nf q np _ _ obl prem0 xy ground new])
        (erule pend, erule materials, blast)
    have kept_h: "h' c = ?h c" if "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S)" for c
      by (rule head_kept_variables[OF hk]) (simp add: that finite_pattern_variables_correct[symmetric])
    have ycases: "(\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and>
          c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S) \<and> z = ?z c) \<or>
        (z |\<in>| finite_pattern_variables (resolution_node_call np) \<and> \<theta>2 z = \<theta> z)"
      if zy: "z |\<in>| finite_pattern_variables y" for z
    proof -
      obtain c where c: "c |\<in>| finite_pattern_variables yo0" "z |\<in>| finite_pattern_variables (\<beta> c)"
        using finite_pattern_substitute_origin[OF zy[unfolded xy(2)]] by blast
      have cS: "c |\<in>| finite_schema_variables ?S"
        by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: c(1))
      show ?thesis
      proof (cases "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S)")
        case True
        have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)"
          unfolding call by (rule finite_pattern_substitute_variable[where \<sigma>=\<beta>, OF True c(2)])
        have "decode_finite_term (resolution_value \<theta>2 (\<beta> c)) = decode_finite_term (resolution_value \<theta> (\<beta> c))"
          using hy_agree[OF c(1)] kept_h[OF True] hyo[OF c(1)] by simp
        then have "resolution_value \<theta>2 (\<beta> c) = resolution_value \<theta> (\<beta> c)" by simp
        then have "\<theta>2 z = \<theta> z" by (rule resolution_value_agree) (rule c(2))
        then show ?thesis using zc by blast
      next
        case False
        have "z = ?z c" using c(2) only_b[OF cS False] by simp
        then show ?thesis using c(1) False by blast
      qed
    qed
    define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables y then \<theta>2 z
      else if Zs z then finite_term_of (h' (snd z)) else \<theta> z)"
    have K: "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
      if cS: "c |\<in>| finite_schema_variables ?S"
        and hc: "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S) \<Longrightarrow>
          ?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))" for c
    proof (cases "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S)")
      case concl: True
      have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| finite_pattern_variables (\<beta> c)" for z
      proof -
        have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)"
          unfolding call by (rule finite_pattern_substitute_variable[where \<sigma>=\<beta>, OF concl z])
        show ?thesis
        proof (cases "z |\<in>| finite_pattern_variables y")
          case zy: True
          from ycases[OF zy] show ?thesis
          proof (elim disjE exE conjE)
            fix c' assume c': "c' |\<in>| finite_pattern_variables yo0"
              "c' |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" "z = ?z c'"
            have "c' |\<in>| finite_schema_variables ?S"
              by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: c'(1))
            then have "z |\<notin>| finite_pattern_variables (resolution_node_call np)" using image c'(2,3) by simp
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
      have "resolution_value \<theta>1 (\<beta> c) = resolution_value \<theta> (\<beta> c)" by (rule resolution_value_cong) (rule same)
      then show ?thesis using kept_h[OF concl] hc[OF concl] by simp
    next
      case nconcl: False
      have bc: "\<beta> c = Finite_Variable (?z c)" by (rule only_b[OF cS nconcl])
      show ?thesis
      proof (cases "?z c |\<in>| finite_pattern_variables y")
        case zy: True
        from ycases[OF zy] show ?thesis
        proof (elim disjE exE conjE)
          fix c' assume c': "c' |\<in>| finite_pattern_variables yo0"
            "c' |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" "?z c = ?z c'"
          then have cc: "c' = c" by simp
          show ?thesis using hy_agree[OF c'(1)] zy bc cc by (simp add: \<theta>1_def)
        next
          assume "?z c |\<in>| finite_pattern_variables (resolution_node_call np)" "\<theta>2 (?z c) = \<theta> (?z c)"
          with image[OF cS nconcl] show ?thesis by simp
        qed
      next
        case ny: False
        have "Zs (?z c)" using cS nconcl by (simp add: Zs_def)
        then show ?thesis using ny bc decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
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
          by (rule only_h[OF Zs_z(2)[OF Z] Zs_z(3)[OF Z] h0p zz])
        with nc show False by blast
      qed
      show "\<theta>1 z = \<theta> z" using ny nZ by (simp add: \<theta>1_def)
    qed
    have holds: "finite_goal_holds ?M \<theta>1 h" if "h |\<in>| finite_focus_pending F st" for h
    proof (rule finite_parent_exchange_holds[OF sup children tr' _ _ _ that])
      fix s e' p' c assume m: "(s,e',p') |\<in>| finite_schema_premises ?S" and c: "c |\<in>| finite_pattern_variables p'"
      show "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
        by (rule K) (use m c parent2[OF m c] in \<open>auto intro: finite_schema_variables_members(2)\<close>)
    next
      fix s N c assume m: "(s,N) |\<in>| finite_schema_materials ?S" and c: "c |\<in>| finite_material_variables N"
      show "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
        by (rule K) (use m c parent3[OF m c] in \<open>auto intro: finite_schema_variables_members(3)\<close>)
    next
      fix h0 z assume "h0 |\<in>| finite_focus_pending F st"
        "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
        "z |\<in>| resolution_goal_variables h0"
      then show "\<theta>1 z = \<theta> z" by (rule unchanged)
    qed
    show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables (Finite_Pattern_Pair x y) \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h)"
      using holds ground by (intro exI[of _ \<theta>1]) (auto simp: \<theta>1_def)
  qed
qed

section \<open>The socket declared without the kept head\<close>

text \<open>
  At a socket declared without the kept head, the parent is the focus root and its call's output is a variant of its
  clause's head output, which the obligation's new instance may change: each variable of the call's output takes the new
  instance's value of the head variable it binds, the head input is kept, and the call's input, sharing no variable with
  its output, keeps its values. The holders test covers the variables of the call's output beside the goal's.
\<close>

theorem finite_socket_free_context:
  assumes sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y) |\<in>| finite_focus_pending F st"
    and root: "F = Some (butlast q)" and ground: "finite_pattern_variables x = {||}"
    and q: "q \<noteq> []" and np: "resolution_node_position np = butlast q"
    and bind: "resolution_node_bindings np = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema np))"
    and call: "resolution_node_call np = finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema np))"
    and obl: "socket_discharged (positive_meaning (decode_finite_system P)) (decode_finite_schema (resolution_node_schema np))
      (last q) False"
    and pend: "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0) |\<in>| resolution_pending st"
    and materials: "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0)
        |\<in>| resolution_pending st"
    and children: "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) = resolution_node_position np \<Longrightarrow>
      (\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        h = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
    and only: "finite_premise_only_free st np"
    and image: "\<And>a. a |\<in>| finite_schema_variables (resolution_node_schema np) \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema np)) \<Longrightarrow>
      ((resolution_node_position np,True),a) |\<notin>| finite_pattern_variables (resolution_node_call np)"
    and pair: "\<And>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>xi yo. p0 = Finite_Pattern_Pair xi yo"
    and concl: "finite_schema_conclusion (resolution_node_schema np) = Finite_Pattern_Pair hi ho"
    and callout: "resolution_node_call np = Finite_Pattern_Pair xc out" and variant: "finite_variant ho out"
    and apart: "finite_pattern_variables xc |\<inter>| finite_pattern_variables out = {||}"
    and holders: "finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out)
      (Resolution_Call_Goal q r e (Finite_Pattern_Pair x y))"
  shows "finite_exchange_context (positive_meaning (decode_finite_system P)) F q st e (Finite_Pattern_Pair x y)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?g = "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y)"
  let ?S = "resolution_node_schema np"
  let ?h = "finite_instance_valuation \<theta> \<beta>"
  let ?z = "\<lambda>a. ((resolution_node_position np,True),a)"
  have "length (butlast q) \<noteq> length q" using q by (cases q) simp_all
  then have "butlast q \<noteq> q" by metis
  then have nf: "F \<noteq> Some q" using root by simp
  have gp: "?g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have gchild: "resolution_goal_position ?g \<noteq> []" "butlast (resolution_goal_position ?g) = resolution_node_position np"
    using q np by simp_all
  obtain xi0 yo0 where prem0: "(last q,e,Finite_Pattern_Pair xi0 yo0) |\<in>| finite_schema_premises ?S"
    and xy: "x = finite_pattern_substitute \<beta> xi0" "y = finite_pattern_substitute \<beta> yo0"
  proof (rule finite_socket_premise[OF q np])
    show "(\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises ?S \<and>
        ?g = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute \<beta> p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials ?S \<and>
        ?g = Resolution_Material_Goal (resolution_node_position np @ [s]) r' (finite_material_pattern_substitute \<beta> N0))"
      by (rule children[OF gp gchild])
    show "\<forall>e0 p0. (last q,e0,p0) |\<in>| finite_schema_premises ?S \<longrightarrow> (\<exists>xi yo. p0 = Finite_Pattern_Pair xi yo)"
      using pair by blast
  qed
  have nf': "F \<noteq> Some (resolution_goal_position ?g)" and q': "resolution_goal_position ?g \<noteq> []"
    and np': "resolution_node_position np = butlast (resolution_goal_position ?g)" using nf q np by simp_all
  have parent2: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,e',p') |\<in>| finite_schema_premises ?S" "c |\<in>| finite_pattern_variables p'" for s e' p' c
    by (rule finite_parent_instance_true(2)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np' _ _ that];
      (erule pend | erule materials))
  have parent3: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))"
    if "(s,N) |\<in>| finite_schema_materials ?S" "c |\<in>| finite_material_variables N" for s N c
    by (rule finite_parent_instance_true(3)[where g="?g" and np=np and \<beta>=\<beta>, OF sup gF nf' q' np' _ _ that];
      (erule pend | erule materials))
  have hyo: "?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))" if "c |\<in>| finite_pattern_variables yo0" for c
    using parent2[OF prem0] that by simp
  have only_b: "\<beta> a = Finite_Variable (?z a)"
    if "a |\<in>| finite_schema_variables ?S" "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" for a
    by (rule finite_premise_only_bound(1)[OF only bind that])
  have only_h: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = resolution_node_position np"
    if "a |\<in>| finite_schema_variables ?S" "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
      "h |\<in>| resolution_pending st" "?z a |\<in>| resolution_goal_variables h" for a h
    by (rule finite_premise_only_bound(2)[OF only bind that(1,2) that(3,4)])
  have xo: "xc = finite_pattern_substitute \<beta> hi" "out = finite_pattern_substitute \<beta> ho"
    using call callout concl by simp_all
  have cv: "fset (finite_pattern_variables (finite_schema_conclusion ?S)) =
      fset (finite_pattern_variables hi) \<union> fset (finite_pattern_variables ho)" by (simp add: concl)
  have callv: "fset (finite_pattern_variables (resolution_node_call np)) =
      fset (finite_pattern_variables xc) \<union> fset (finite_pattern_variables out)" by (simp add: callout)
  have xcv: "z |\<in>| finite_pattern_variables xc" if "c |\<in>| finite_pattern_variables hi" "z |\<in>| finite_pattern_variables (\<beta> c)" for c z
    unfolding xo(1) by (rule finite_pattern_substitute_variable[where \<sigma>=\<beta>, OF that])
  have outv: "z |\<in>| finite_pattern_variables out" if "c |\<in>| finite_pattern_variables ho" "z |\<in>| finite_pattern_variables (\<beta> c)" for c z
    unfolding xo(2) by (rule finite_pattern_substitute_variable[where \<sigma>=\<beta>, OF that])
  have variant': "finite_variant ho (finite_pattern_substitute \<beta> ho)" using variant xo(2) by simp
  define Zs where "Zs = (\<lambda>z. fst z = (resolution_node_position np,True) \<and> snd z |\<in>| finite_schema_variables ?S \<and>
    snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S))"
  have Zs_z: "z = ?z (snd z)" "snd z |\<in>| finite_schema_variables ?S"
      "snd z |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" if "Zs z" for z
    using that by (auto simp: Zs_def prod_eq_iff)
  have Zs_call: "z |\<notin>| finite_pattern_variables (resolution_node_call np)" if "Zs z" for z
    using image[OF Zs_z(2)[OF that] Zs_z(3)[OF that]] Zs_z(1)[OF that] by metis
  have dconcl: "schema_conclusion (decode_finite_schema ?S) = Pattern_Pair (decode_finite_pattern hi) (decode_finite_pattern ho)"
    by (simp add: concl)
  show ?thesis unfolding finite_exchange_context_def
  proof (intro allI impI)
    fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 (Finite_Pattern_Pair x y))) \<in> ?M"
    obtain h' where tr': "clause_true ?M (decode_finite_schema ?S) h'"
      and hk: "head_kept False (decode_finite_schema ?S) ?h h'"
      and hy_agree: "\<And>c. c |\<in>| finite_pattern_variables yo0 \<Longrightarrow> h' c = decode_finite_term (resolution_value \<theta>2 (\<beta> c))"
      and formed': "\<And>c. c |\<in>| finite_schema_variables ?S \<Longrightarrow> term_formed (h' c)"
      by (rule finite_socket_new_instance[OF sup gF nf q np _ _ obl prem0 xy ground new])
        (erule pend, erule materials, blast)
    have input_h: "h' c = ?h c" if "c |\<in>| finite_pattern_variables hi" for c
      by (rule evaluate_pattern_agree[OF head_kept_input[OF hk dconcl]]) (simp add: that finite_pattern_variables_correct[symmetric])
    have ycases: "(\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and>
          c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S) \<and> z = ?z c) \<or>
        (\<exists>c. c |\<in>| finite_pattern_variables yo0 \<and> c |\<in>| finite_pattern_variables ho \<and> z |\<in>| finite_pattern_variables (\<beta> c)) \<or>
        (z |\<in>| finite_pattern_variables xc \<and> \<theta>2 z = \<theta> z)"
      if zy: "z |\<in>| finite_pattern_variables y" for z
    proof -
      obtain c where c: "c |\<in>| finite_pattern_variables yo0" "z |\<in>| finite_pattern_variables (\<beta> c)"
        using finite_pattern_substitute_origin[OF zy[unfolded xy(2)]] by blast
      have cS: "c |\<in>| finite_schema_variables ?S"
        by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: c(1))
      show ?thesis
      proof (cases "c |\<in>| finite_pattern_variables ho")
        case True
        then show ?thesis using c by blast
      next
        case notho: False
        show ?thesis
        proof (cases "c |\<in>| finite_pattern_variables hi")
          case True
          have "decode_finite_term (resolution_value \<theta>2 (\<beta> c)) = decode_finite_term (resolution_value \<theta> (\<beta> c))"
            using hy_agree[OF c(1)] input_h[OF True] hyo[OF c(1)] by simp
          then have "resolution_value \<theta>2 (\<beta> c) = resolution_value \<theta> (\<beta> c)" by simp
          then have "\<theta>2 z = \<theta> z" by (rule resolution_value_agree) (rule c(2))
          then show ?thesis using xcv[OF True c(2)] by blast
        next
        case False
          have nc: "c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" using False notho concl by simp
          have "z = ?z c" using c(2) only_b[OF cS nc] by simp
          then show ?thesis using c(1) nc by blast
        qed
      qed
    qed
    define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables y then \<theta>2 z
      else if Zs z then finite_term_of (h' (snd z))
      else if z |\<in>| finite_pattern_variables out
        then finite_term_of (h' (SOME b. b |\<in>| finite_pattern_variables ho \<and> \<beta> b = Finite_Variable z))
      else \<theta> z)"
    have K: "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
      if cS: "c |\<in>| finite_schema_variables ?S"
        and hc: "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S) \<Longrightarrow>
          ?h c = decode_finite_term (resolution_value \<theta> (\<beta> c))" for c
    proof (cases "c |\<in>| finite_pattern_variables ho")
      case inho: True
      obtain w where bw: "\<beta> c = Finite_Variable w" by (rule finite_variant_substitute_variable[OF variant' inho])
      have wu: "b = c" if "b |\<in>| finite_pattern_variables ho" "\<beta> b = Finite_Variable w" for b
        using finite_variant_substitute_injective[OF variant' that(1) inho] that(2) bw by simp
      have wout: "w |\<in>| finite_pattern_variables out" using outv[OF inho] bw by simp
      have wcall: "w |\<in>| finite_pattern_variables (resolution_node_call np)" using wout callv by auto
      show ?thesis
      proof (cases "w |\<in>| finite_pattern_variables y")
        case wy: True
        from ycases[OF wy] show ?thesis
        proof (elim disjE exE conjE)
          fix c' assume c': "c' |\<in>| finite_pattern_variables yo0"
            "c' |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" "w = ?z c'"
          have "c' |\<in>| finite_schema_variables ?S"
            by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: c'(1))
          then have "w |\<notin>| finite_pattern_variables (resolution_node_call np)" using image c'(2,3) by simp
          with wcall show ?thesis by simp
        next
          fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
            "w |\<in>| finite_pattern_variables (\<beta> c')"
          obtain w' where bw': "\<beta> c' = Finite_Variable w'"
            by (rule finite_variant_substitute_variable[OF variant' c'(2)])
          have "\<beta> c' = Finite_Variable w" using c'(3) bw' by simp
          then have cc: "c' = c" by (rule wu[OF c'(2)])
          show ?thesis using hy_agree[OF c'(1)] cc bw wy by (simp add: \<theta>1_def)
        next
          assume a1: "w |\<in>| finite_pattern_variables xc" "\<theta>2 w = \<theta> w"
          have "w |\<in>| finite_pattern_variables xc |\<inter>| finite_pattern_variables out" using a1(1) wout by simp
          then show ?thesis using apart by simp
        qed
      next
        case wny: False
        have "\<not> Zs w" using Zs_call wcall by blast
        moreover have "(SOME b. b |\<in>| finite_pattern_variables ho \<and> \<beta> b = Finite_Variable w) = c"
          by (rule some_equality) (use inho bw wu in blast)+
        ultimately show ?thesis using wny wout bw decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
      qed
    next
      case notho: False
      show ?thesis
      proof (cases "c |\<in>| finite_pattern_variables hi")
        case inhi: True
        have concl_c: "c |\<in>| finite_pattern_variables (finite_schema_conclusion ?S)" using inhi concl by simp
        have same: "\<theta>1 z = \<theta> z" if z: "z |\<in>| finite_pattern_variables (\<beta> c)" for z
        proof -
          have zx: "z |\<in>| finite_pattern_variables xc" by (rule xcv[OF inhi z])
          have zc: "z |\<in>| finite_pattern_variables (resolution_node_call np)" using zx callv by auto
          have nout: "z |\<notin>| finite_pattern_variables out"
          proof
            assume "z |\<in>| finite_pattern_variables out"
            then have "z |\<in>| finite_pattern_variables xc |\<inter>| finite_pattern_variables out" using zx by simp
            then show False using apart by simp
          qed
          show ?thesis
          proof (cases "z |\<in>| finite_pattern_variables y")
            case zy: True
            from ycases[OF zy] show ?thesis
            proof (elim disjE exE conjE)
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0"
                "c' |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" "z = ?z c'"
              have "c' |\<in>| finite_schema_variables ?S"
                by (rule finite_schema_variables_members(2)[OF prem0]) (simp add: c'(1))
              then have "z |\<notin>| finite_pattern_variables (resolution_node_call np)" using image c'(2,3) by simp
              with zc show ?thesis by simp
            next
              fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
                "z |\<in>| finite_pattern_variables (\<beta> c')"
              have "z |\<in>| finite_pattern_variables out" by (rule outv[OF c'(2,3)])
              with nout show ?thesis by simp
            next
              assume "z |\<in>| finite_pattern_variables xc" "\<theta>2 z = \<theta> z"
              then show ?thesis using zy by (simp add: \<theta>1_def)
            qed
          next
            case ny: False
            have "\<not> Zs z" using Zs_call zc by blast
            then show ?thesis using ny nout by (simp add: \<theta>1_def)
          qed
        qed
        have "resolution_value \<theta>1 (\<beta> c) = resolution_value \<theta> (\<beta> c)" by (rule resolution_value_cong) (rule same)
        then show ?thesis using input_h[OF inhi] hc[OF concl_c] by simp
      next
        case notin: False
        have nconcl: "c |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" using notin notho concl by simp
        have bc: "\<beta> c = Finite_Variable (?z c)" by (rule only_b[OF cS nconcl])
        have zcall: "?z c |\<notin>| finite_pattern_variables (resolution_node_call np)" by (rule image[OF cS nconcl])
        show ?thesis
        proof (cases "?z c |\<in>| finite_pattern_variables y")
          case zy: True
          from ycases[OF zy] show ?thesis
          proof (elim disjE exE conjE)
            fix c' assume c': "c' |\<in>| finite_pattern_variables yo0"
              "c' |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)" "?z c = ?z c'"
            then have cc: "c' = c" by simp
            show ?thesis using hy_agree[OF c'(1)] zy bc cc by (simp add: \<theta>1_def)
          next
            fix c' assume c': "c' |\<in>| finite_pattern_variables yo0" "c' |\<in>| finite_pattern_variables ho"
              "?z c |\<in>| finite_pattern_variables (\<beta> c')"
            have "?z c |\<in>| finite_pattern_variables out" by (rule outv[OF c'(2,3)])
            with zcall callv show ?thesis by auto
          next
            assume "?z c |\<in>| finite_pattern_variables xc" "\<theta>2 (?z c) = \<theta> (?z c)"
            with zcall callv show ?thesis by auto
          qed
        next
          case ny: False
          have "Zs (?z c)" using cS nconcl by (simp add: Zs_def)
          then show ?thesis using ny bc decode_finite_term_of[OF formed'[OF cS]] by (simp add: \<theta>1_def)
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
          by (rule only_h[OF Zs_z(2)[OF Z] Zs_z(3)[OF Z] h0p zz])
        with nc show False by blast
      qed
      show "\<theta>1 z = \<theta> z" using nyo nZ by (simp add: \<theta>1_def)
    qed
    have holds: "finite_goal_holds ?M \<theta>1 h" if "h |\<in>| finite_focus_pending F st" for h
    proof (rule finite_parent_exchange_holds[OF sup children tr' _ _ _ that])
      fix s e' p' c assume m: "(s,e',p') |\<in>| finite_schema_premises ?S" and c: "c |\<in>| finite_pattern_variables p'"
      show "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
        by (rule K) (use m c parent2[OF m c] in \<open>auto intro: finite_schema_variables_members(2)\<close>)
    next
      fix s N c assume m: "(s,N) |\<in>| finite_schema_materials ?S" and c: "c |\<in>| finite_material_variables N"
      show "decode_finite_term (resolution_value \<theta>1 (\<beta> c)) = h' c"
        by (rule K) (use m c parent3[OF m c] in \<open>auto intro: finite_schema_variables_members(3)\<close>)
    next
      fix h0 z assume "h0 |\<in>| finite_focus_pending F st"
        "\<not> (resolution_goal_position h0 \<noteq> [] \<and> butlast (resolution_goal_position h0) = resolution_node_position np)"
        "z |\<in>| resolution_goal_variables h0"
      then show "\<theta>1 z = \<theta> z" by (rule unchanged)
    qed
    show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables (Finite_Pattern_Pair x y) \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h)"
      using holds ground by (intro exI[of _ \<theta>1]) (auto simp: \<theta>1_def)
  qed
qed

section \<open>At every state where the test commits\<close>

text \<open>
  The parent's own bindings, read by the test (@{const finite_node_binding}), are the linked ones on its clause's variables,
  so the narrowed test's conditions give the contexts' hypotheses.
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

lemma finite_children_instances_parts:
  assumes "finite_children_instances st np"
  shows "\<And>s e0 p0. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0
        (finite_pattern_substitute (finite_node_binding np) p0) |\<in>| resolution_pending st"
    and "\<And>s N0. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<Longrightarrow>
      \<exists>r'. Resolution_Material_Goal (resolution_node_position np @ [s]) r'
        (finite_material_pattern_substitute (finite_node_binding np) N0) |\<in>| resolution_pending st"
    and "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) = resolution_node_position np \<Longrightarrow>
      (\<exists>s e0 p0 r'. (s,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np) \<and>
        h = Resolution_Call_Goal (resolution_node_position np @ [s]) r' e0 (finite_pattern_substitute (finite_node_binding np) p0)) \<or>
      (\<exists>s N0 r'. (s,N0) |\<in>| finite_schema_materials (resolution_node_schema np) \<and>
        h = Resolution_Material_Goal (resolution_node_position np @ [s]) r'
          (finite_material_pattern_substitute (finite_node_binding np) N0))"
  using assms unfolding finite_children_instances_def by fastforce+

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
  have sc: "finite_socket_commitment D F st g" and nar: "finite_call_narrowed D F st g"
    using cc socket call by (simp_all add: finite_declared_commitment_def)
  obtain q r e p where gq: "g = Resolution_Call_Goal q r e p" using call by (cases g) simp_all
  obtain x y where p: "p = Finite_Pattern_Pair x y"
    using sc gq by (cases p) (simp_all add: finite_socket_commitment_def)
  let ?g = "Resolution_Call_Goal q r e (Finite_Pattern_Pair x y)"
  have ground: "finite_pattern_variables x = {||}" and decl: "finite_socket_declared D F st q (finite_pattern_variables y) ?g"
    using sc gq p by (simp_all add: finite_socket_commitment_def)
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q"
    and inst: "finite_children_instances st nd" and unsh: "finite_premise_only_unshared nd"
    and pair0: "finite_socket_pair q (resolution_node_schema nd)"
    and ka: "finite_socket_kept D F st q (finite_pattern_variables y) ?g \<or> finite_input_output_apart nd"
    using nar gq p unfolding finite_call_narrowed_def by auto
  have gF': "?g |\<in>| finite_focus_pending F st" using gF gq p by simp
  have nf: "F \<noteq> Some q" using nf0 gq by simp
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have same: "m = nd" if "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast q" for m
  proof -
    have "resolution_node_position m = resolution_node_position nd" using that(2) nd(2) by simp
    then show ?thesis using dist that(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  note linked = finite_node_binding_linked[OF I nd(1)]
  note parts = finite_children_instances_parts[OF inst]
  have image: "((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (resolution_node_call nd)"
    if "a |\<in>| finite_schema_variables (resolution_node_schema nd)"
      "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))" for a
    using unsh that unfolding finite_premise_only_unshared_def by auto
  have pair: "\<exists>xi yo. p0 = Finite_Pattern_Pair xi yo"
    if "(last q,e0,p0) |\<in>| finite_schema_premises (resolution_node_schema nd)" for e0 p0
    using pair0 that unfolding finite_socket_pair_def by (fastforce split: finite_term_pattern.splits)
  have ctx: "finite_exchange_context ?M F q st e (Finite_Pattern_Pair x y)"
  proof (cases "finite_socket_kept D F st q (finite_pattern_variables y) ?g")
    case True
    have q: "q \<noteq> []" and holders: "finite_socket_holders F st q (finite_pattern_variables y) ?g" and
      ex: "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        (resolution_node_site nd,resolution_node_schema nd,last q,True) |\<in>| declared_sockets D \<and>
        finite_siblings_pending st q (resolution_node_schema nd) \<and> finite_premise_only_free st nd)"
      using True unfolding finite_socket_kept_def by blast+
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
      and decl': "(resolution_node_site nd',resolution_node_schema nd',last q,True) |\<in>| declared_sockets D"
      and only': "finite_premise_only_free st nd'" using ex by blast
    have ndd: "nd' = nd" by (rule same[OF nd'])
    have obl: "socket_discharged ?M (decode_finite_schema (resolution_node_schema nd)) (last q) True"
      using discharged decl' ndd unfolding declarations_discharged_def by blast
    show ?thesis
      by (rule finite_socket_kept_context[where np=nd and \<beta>="finite_node_binding nd", OF sup gF' nf ground q nd(2)
        linked obl parts(1) parts(2) parts(3) only'[unfolded ndd] image pair holders])
  next
    case False
    then have free: "finite_socket_free D F st q (finite_pattern_variables y) ?g"
      using decl unfolding finite_socket_declared_def by blast
    have apart: "finite_input_output_apart nd" using ka False by blast
    have q: "q \<noteq> []" and root: "F = Some (butlast q)" and
      ex: "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        (resolution_node_site nd,resolution_node_schema nd,last q,False) |\<in>| declared_sockets D \<and>
        finite_siblings_pending st q (resolution_node_schema nd) \<and> finite_premise_only_free st nd \<and>
        (case finite_parent_output nd of None \<Rightarrow> False
          | Some out \<Rightarrow> finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out) ?g))"
      using free unfolding finite_socket_free_def by blast+
    obtain nd' where nd': "nd' |\<in>| resolution_nodes st" "resolution_node_position nd' = butlast q"
      and decl': "(resolution_node_site nd',resolution_node_schema nd',last q,False) |\<in>| declared_sockets D"
      and only': "finite_premise_only_free st nd'"
      and po': "case finite_parent_output nd' of None \<Rightarrow> False
          | Some out \<Rightarrow> finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out) ?g"
      using ex by blast
    have ndd: "nd' = nd" by (rule same[OF nd'])
    obtain out where po: "finite_parent_output nd = Some out"
      and holders: "finite_socket_holders F st q (finite_pattern_variables y |\<union>| finite_pattern_variables out) ?g"
      using po' ndd by (cases "finite_parent_output nd") simp_all
    obtain hi ho xc where concl: "finite_schema_conclusion (resolution_node_schema nd) = Finite_Pattern_Pair hi ho"
      and callout: "resolution_node_call nd = Finite_Pattern_Pair xc out" and variant: "finite_variant ho out"
      using po unfolding finite_parent_output_def
      by (auto split: finite_term_pattern.splits prod.splits if_splits)
    have disj: "finite_pattern_variables xc |\<inter>| finite_pattern_variables out = {||}"
      using apart callout by (simp add: finite_input_output_apart_def)
    have obl: "socket_discharged ?M (decode_finite_schema (resolution_node_schema nd)) (last q) False"
      using discharged decl' ndd unfolding declarations_discharged_def by blast
    show ?thesis
      by (rule finite_socket_free_context[where np=nd and \<beta>="finite_node_binding nd", OF sup gF' root ground q nd(2)
        linked obl parts(1) parts(2) parts(3) only'[unfolded ndd] image pair concl callout variant disj holders])
  qed
  have g': "?g |\<in>| resolution_pending st" using gF' by (simp add: finite_focus_pending_focused)
  have parent': "finite_goal_premise st ?g" using parent gq p by simp
  have unheld': "\<not> finite_held \<kappa> st ?g" using unheld gq p by simp
  have gpos: "resolution_goal_position g = q" using gq by simp
  have s0': "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_declared_commitment D) P n (Some q) B st)"
    using s0 by (simp only: gpos)
  show ?thesis unfolding gpos
    by (rule finite_committed_exchange_context[OF \<kappa> I sup g' parent' only H unheld' ctx s0'])
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
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
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
  have nar: "finite_material_narrowed D F st g" using cm by (simp add: finite_declared_commitment_def)
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at (\<lambda>_. False) F (finite_committed_barring B st) P st' \<theta>'"
    by (rule finite_material_commitment_exchanges[OF discharged I sup gF gq Ws cm nar])
qed

end
