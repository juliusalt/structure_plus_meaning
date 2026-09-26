theory Factor_Construction_Holders
  imports Factor_Resolution_Completeness
begin

text \<open>
  Where a registered variable stands in a search's state (task 526, the correction of task 496's entry that a
  construction step bars the nodes present). A witness construction registers premise-only variables of clauses. When
  a clause is renamed apart at a node, its registered variable x stands only in the node's own binding of it and in
  the goals raised by the node's premises that hold it: no unification reaches x, since a goal holding x is held back
  from selection while x is free, and every other pattern a step unifies is renamed at another position. The
  construction step replaces x by its value everywhere. This is an invariant of the search from a call
  (@{text resolution_registrations_held}), kept by every step; a construction step reads from it that the goals
  holding x are exactly the node's premises holding the registered variable.
\<close>

section \<open>The variables of a state\<close>

definition resolution_state_variables :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('s,'a) resolution_variable set" where
  "resolution_state_variables st =
    (\<Union>g\<in>fset (resolution_pending st). fset (resolution_goal_variables g)) \<union>
    (\<Union>nd\<in>fset (resolution_nodes st). fset (finite_pattern_variables (resolution_node_call nd)) \<union>
      (\<Union>z\<in>fset (resolution_node_bindings nd). fset (finite_pattern_variables (snd z))))"

lemma resolution_state_variables_state [simp]:
  "resolution_state_variables (Resolution_State (resolution_pending st) (resolution_nodes st) W) =
    resolution_state_variables st"
  by (simp add: resolution_state_variables_def)

lemma resolution_state_variables_goal:
  "g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> z \<in> resolution_state_variables st"
  unfolding resolution_state_variables_def by blast

lemma resolution_state_variables_call:
  "nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
    z \<in> resolution_state_variables st"
  unfolding resolution_state_variables_def by blast

lemma resolution_state_variables_binding:
  assumes "nd |\<in>| resolution_nodes st" "(b,y) |\<in>| resolution_node_bindings nd" "z |\<in>| finite_pattern_variables y"
  shows "z \<in> resolution_state_variables st"
proof -
  have "z \<in> (\<Union>z\<in>fset (resolution_node_bindings nd). fset (finite_pattern_variables (snd z)))"
    using assms(2,3) by (intro UN_I[of "(b,y)"]) simp_all
  with assms(1) show ?thesis unfolding resolution_state_variables_def by blast
qed

lemma resolution_state_variables_cases:
  assumes "z \<in> resolution_state_variables st"
  obtains g where "g |\<in>| resolution_pending st" "z |\<in>| resolution_goal_variables g"
  | nd where "nd |\<in>| resolution_nodes st" "z |\<in>| finite_pattern_variables (resolution_node_call nd)"
  | nd b y where "nd |\<in>| resolution_nodes st" "(b,y) |\<in>| resolution_node_bindings nd"
    "z |\<in>| finite_pattern_variables y"
proof -
  from assms[unfolded resolution_state_variables_def] show thesis
  proof (elim UnE UN_E)
    fix g assume "g \<in> fset (resolution_pending st)" "z \<in> fset (resolution_goal_variables g)"
    then show thesis using that(1) by blast
  next
    fix nd assume "nd \<in> fset (resolution_nodes st)" "z \<in> fset (finite_pattern_variables (resolution_node_call nd))"
    then show thesis using that(2) by blast
  next
    fix nd y' assume "nd \<in> fset (resolution_nodes st)" "y' \<in> fset (resolution_node_bindings nd)"
      "z \<in> fset (finite_pattern_variables (snd y'))"
    then show thesis using that(3)[of nd "fst y'" "snd y'"] by simp
  qed
qed

lemma resolution_state_variables_substitute:
  assumes z: "z \<in> resolution_state_variables (resolution_state_substitute \<sigma> st)"
  shows "\<exists>y\<in>resolution_state_variables st. z |\<in>| finite_pattern_variables (\<sigma> y)"
  using z
proof (cases rule: resolution_state_variables_cases)
  case (1 g')
  obtain g where g: "g |\<in>| resolution_pending st" "g' = resolution_goal_substitute \<sigma> g" using 1(1) by auto
  obtain y where "y |\<in>| resolution_goal_variables g" "z |\<in>| finite_pattern_variables (\<sigma> y)"
    using resolution_goal_substitute_variable_origin[of z \<sigma> g] 1(2) g(2) by blast
  then show ?thesis using resolution_state_variables_goal[OF g(1)] by blast
next
  case (2 nd')
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "nd' = resolution_node_substitute \<sigma> nd" using 2(1) by auto
  have "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> (resolution_node_call nd))"
    using 2(2) nd(2) by simp
  from finite_substitute_variable_origin[OF this]
  obtain y where "y |\<in>| finite_pattern_variables (resolution_node_call nd)" "z |\<in>| finite_pattern_variables (\<sigma> y)"
    by blast
  then show ?thesis using resolution_state_variables_call[OF nd(1)] by blast
next
  case (3 nd' b y')
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "nd' = resolution_node_substitute \<sigma> nd" using 3(1) by auto
  have "(b,y') |\<in>| fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (resolution_node_bindings nd)"
    using 3(2) nd(2) by simp
  then obtain y where yb: "(b,y) |\<in>| resolution_node_bindings nd" "y' = finite_pattern_substitute \<sigma> y" by auto
  obtain w where "w |\<in>| finite_pattern_variables y" "z |\<in>| finite_pattern_variables (\<sigma> w)"
    using finite_substitute_variable_origin[of z \<sigma> y] 3(3) yb(2) by blast
  then show ?thesis using resolution_state_variables_binding[OF nd(1) yb(1)] by blast
qed

section \<open>A registered variable held at its node\<close>

text \<open>
  The premises of a clause holding its variable a at a socket s. A registered variable is held at a node when the
  node binds it to itself (it is free), no node's call holds it, among the node's bindings only its own holds it, and
  every pending goal holding it stands at a socket of the node whose premise holds a.
\<close>

definition resolution_registered_premise :: "('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool" where
  "resolution_registered_premise S s a \<longleftrightarrow>
    (\<exists>e p. (s,e,p) |\<in>| finite_schema_premises S \<and> a |\<in>| finite_pattern_variables p) \<or>
    (\<exists>M. (s,M) |\<in>| finite_schema_materials S \<and> a |\<in>| finite_material_variables M)"

definition resolution_variable_held ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> bool" where
  "resolution_variable_held st nd a \<longleftrightarrow>
    (a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd \<and>
    (\<forall>m. m |\<in>| resolution_nodes st \<longrightarrow>
      ((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (resolution_node_call m)) \<and>
    (\<forall>b y. (b,y) |\<in>| resolution_node_bindings nd \<longrightarrow>
      ((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables y \<longrightarrow> b = a) \<and>
    (\<forall>g. g |\<in>| resolution_pending st \<longrightarrow> ((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g \<longrightarrow>
      (\<exists>s. resolution_goal_position g = resolution_node_position nd @ [s] \<and>
        resolution_registered_premise (resolution_node_schema nd) s a))"

lemma resolution_variable_heldD:
  assumes "resolution_variable_held st nd a"
  shows "(a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd"
    and "m |\<in>| resolution_nodes st \<Longrightarrow>
      ((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (resolution_node_call m)"
    and "(b,y) |\<in>| resolution_node_bindings nd \<Longrightarrow>
      ((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables y \<Longrightarrow> b = a"
    and "g |\<in>| resolution_pending st \<Longrightarrow> ((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g \<Longrightarrow>
      \<exists>s. resolution_goal_position g = resolution_node_position nd @ [s] \<and>
        resolution_registered_premise (resolution_node_schema nd) s a"
  using assms unfolding resolution_variable_held_def by blast+

lemma resolution_variable_heldI:
  assumes "(a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd"
    and "\<And>m. m |\<in>| resolution_nodes st \<Longrightarrow>
      ((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (resolution_node_call m)"
    and "\<And>b y. (b,y) |\<in>| resolution_node_bindings nd \<Longrightarrow>
      ((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables y \<Longrightarrow> b = a"
    and "\<And>g. g |\<in>| resolution_pending st \<Longrightarrow> ((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g \<Longrightarrow>
      \<exists>s. resolution_goal_position g = resolution_node_position nd @ [s] \<and>
        resolution_registered_premise (resolution_node_schema nd) s a"
  shows "resolution_variable_held st nd a"
  using assms unfolding resolution_variable_held_def by blast

lemma resolution_variable_held_state [simp]:
  "resolution_variable_held (Resolution_State (resolution_pending st) (resolution_nodes st) W) nd a \<longleftrightarrow>
    resolution_variable_held st nd a"
  by (simp add: resolution_variable_held_def)

text \<open>A substitution fixing x and introducing it nowhere keeps it held.\<close>

lemma finite_substitute_keeps_variable:
  assumes apart: "\<And>y. y \<noteq> x \<Longrightarrow> x |\<notin>| finite_pattern_variables (\<sigma> y)"
    and x: "x |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)"
  shows "x |\<in>| finite_pattern_variables p"
proof -
  obtain y where y: "y |\<in>| finite_pattern_variables p" "x |\<in>| finite_pattern_variables (\<sigma> y)"
    using finite_substitute_variable_origin[OF x] by blast
  have "y = x" using apart[of y] y(2) by (cases "y = x") simp_all
  then show ?thesis using y(1) by simp
qed

lemma resolution_goal_keeps_variable:
  assumes apart: "\<And>y. y \<noteq> x \<Longrightarrow> x |\<notin>| finite_pattern_variables (\<sigma> y)"
    and x: "x |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g)"
  shows "x |\<in>| resolution_goal_variables g"
proof -
  obtain y where y: "y |\<in>| resolution_goal_variables g" "x |\<in>| finite_pattern_variables (\<sigma> y)"
    using resolution_goal_substitute_variable_origin[OF x] by blast
  have "y = x" using apart[of y] y(2) by (cases "y = x") simp_all
  then show ?thesis using y(1) by simp
qed

lemma resolution_variable_held_substitute:
  assumes held: "resolution_variable_held st nd a"
    and fixed: "\<sigma> ((resolution_node_position nd,True),a) = Finite_Variable ((resolution_node_position nd,True),a)"
    and apart: "\<And>y. y \<noteq> ((resolution_node_position nd,True),a) \<Longrightarrow>
      ((resolution_node_position nd,True),a) |\<notin>| finite_pattern_variables (\<sigma> y)"
  shows "resolution_variable_held (resolution_state_substitute \<sigma> st) (resolution_node_substitute \<sigma> nd) a"
proof -
  let ?x = "((resolution_node_position nd,True),a)"
  have keep: "\<And>p. ?x |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) \<Longrightarrow> ?x |\<in>| finite_pattern_variables p"
    by (rule finite_substitute_keeps_variable[OF apart])
  have gkeep: "\<And>g. ?x |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g) \<Longrightarrow>
      ?x |\<in>| resolution_goal_variables g"
    by (rule resolution_goal_keeps_variable[OF apart])
  show ?thesis
  proof (rule resolution_variable_heldI)
  have "(\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (a,Finite_Variable ?x) |\<in>|
      fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (resolution_node_bindings nd)"
    by (rule fimageI[OF resolution_variable_heldD(1)[OF held]])
  then show "(a,Finite_Variable ((resolution_node_position (resolution_node_substitute \<sigma> nd),True),a)) |\<in>|
      resolution_node_bindings (resolution_node_substitute \<sigma> nd)"
    using fixed by simp
next
  fix m assume "m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
  then obtain m0 where m0: "m0 |\<in>| resolution_nodes st" "m = resolution_node_substitute \<sigma> m0" by auto
  show "((resolution_node_position (resolution_node_substitute \<sigma> nd),True),a) |\<notin>|
      finite_pattern_variables (resolution_node_call m)"
  proof
    assume "((resolution_node_position (resolution_node_substitute \<sigma> nd),True),a) |\<in>|
        finite_pattern_variables (resolution_node_call m)"
    then have "((resolution_node_position nd,True),a) |\<in>|
        finite_pattern_variables (finite_pattern_substitute \<sigma> (resolution_node_call m0))" using m0(2) by simp
    then have "((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables (resolution_node_call m0)"
      by (rule keep)
    then show False using resolution_variable_heldD(2)[OF held m0(1)] by simp
  qed
next
  fix b y assume "(b,y) |\<in>| resolution_node_bindings (resolution_node_substitute \<sigma> nd)"
    and x: "((resolution_node_position (resolution_node_substitute \<sigma> nd),True),a) |\<in>| finite_pattern_variables y"
  then obtain y0 where y0: "(b,y0) |\<in>| resolution_node_bindings nd" "y = finite_pattern_substitute \<sigma> y0" by auto
  have "((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> y0)"
    using x y0(2) by simp
  then have "((resolution_node_position nd,True),a) |\<in>| finite_pattern_variables y0"
    by (rule keep)
  then show "b = a" by (rule resolution_variable_heldD(3)[OF held y0(1)])
next
  fix g assume "g |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
    and x: "((resolution_node_position (resolution_node_substitute \<sigma> nd),True),a) |\<in>| resolution_goal_variables g"
  then obtain g0 where g0: "g0 |\<in>| resolution_pending st" "g = resolution_goal_substitute \<sigma> g0" by auto
  have "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g0)"
    using x g0(2) by simp
  then have "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g0"
    by (rule gkeep)
  then have "\<exists>s. resolution_goal_position g0 = resolution_node_position nd @ [s] \<and>
      resolution_registered_premise (resolution_node_schema nd) s a"
    by (rule resolution_variable_heldD(4)[OF held g0(1)])
  then show "\<exists>s. resolution_goal_position g = resolution_node_position (resolution_node_substitute \<sigma> nd) @ [s] \<and>
      resolution_registered_premise (resolution_node_schema (resolution_node_substitute \<sigma> nd)) s a"
    using g0(2) by simp
  qed
qed

section \<open>The invariant\<close>

definition resolution_registrations_held ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_registrations_held \<kappa> st \<longleftrightarrow>
    (\<forall>z\<in>resolution_state_variables st. resolution_placed st z) \<and>
    (\<forall>nd a. nd |\<in>| resolution_nodes st \<longrightarrow>
      a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd) \<longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd)) \<longrightarrow>
      ((resolution_node_position nd,True),a) \<notin> resolution_state_variables st \<or> resolution_variable_held st nd a)"

lemma resolution_registrations_heldD:
  assumes "resolution_registrations_held \<kappa> st"
  shows "z \<in> resolution_state_variables st \<Longrightarrow> resolution_placed st z"
    and "nd |\<in>| resolution_nodes st \<Longrightarrow>
      a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd) \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd)) \<Longrightarrow>
      ((resolution_node_position nd,True),a) \<notin> resolution_state_variables st \<or> resolution_variable_held st nd a"
  using assms unfolding resolution_registrations_held_def by blast+

lemma resolution_registrations_heldI:
  assumes "\<And>z. z \<in> resolution_state_variables st \<Longrightarrow> resolution_placed st z"
    and "\<And>nd a. nd |\<in>| resolution_nodes st \<Longrightarrow>
      a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd) \<Longrightarrow>
      a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd)) \<Longrightarrow>
      ((resolution_node_position nd,True),a) \<notin> resolution_state_variables st \<or> resolution_variable_held st nd a"
  shows "resolution_registrations_held \<kappa> st"
  using assms unfolding resolution_registrations_held_def by blast

lemma resolution_registrations_held_state [simp]:
  "resolution_registrations_held \<kappa> (Resolution_State (resolution_pending st) (resolution_nodes st) W) \<longleftrightarrow>
    resolution_registrations_held \<kappa> st"
  by (simp add: resolution_registrations_held_def resolution_placed_def)

lemma resolution_registrations_initial: "resolution_registrations_held \<kappa> (finite_initial_state d t)"
  by (simp add: resolution_registrations_held_def finite_initial_state_def resolution_state_variables_def)

text \<open>A goal the search can select holds no registered premise-only variable of any node.\<close>

lemma resolution_registrations_unheld:
  assumes H: "resolution_registrations_held \<kappa> st" and g: "g |\<in>| resolution_pending st"
    and unheld: "\<not> finite_held \<kappa> st g" and nd: "nd |\<in>| resolution_nodes st"
    and reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
    and only: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
  shows "((resolution_node_position nd,True),a) |\<notin>| resolution_goal_variables g"
proof
  assume x: "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g"
  have "((resolution_node_position nd,True),a) \<in> resolution_state_variables st"
    by (rule resolution_state_variables_goal[OF g x])
  then have held: "resolution_variable_held st nd a" using resolution_registrations_heldD(2)[OF H nd reg only] by blast
  have "a |\<in>| finite_free_registered \<kappa> nd"
    using reg resolution_variable_heldD(1)[OF held] unfolding finite_free_registered_def by simp
  then show False using unheld nd x unfolding finite_held_def by blast
qed

section \<open>The construction step keeps the invariant\<close>

lemma finite_construction_substitution_variables:
  assumes "z' |\<in>| finite_pattern_variables (finite_construction_substitution \<kappa> P G nd z)"
  shows "z' = z \<and> finite_construction_substitution \<kappa> P G nd z = Finite_Variable z"
  using assms by (auto simp: finite_construction_substitution_def split: prod.splits option.splits if_splits)

lemma resolution_registrations_construction_step:
  assumes H: "resolution_registrations_held \<kappa> st"
  shows "resolution_registrations_held \<kappa> (finite_construction_step \<kappa> P st nd0)"
proof -
  let ?\<sigma> = "finite_construction_substitution \<kappa> P (resolution_pending st) nd0"
  define W where "W = resolution_witnesses st |\<union>|
      ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd0 a of
          Some v \<Rightarrow> {|(((resolution_node_position nd0,True),a),v)|} | None \<Rightarrow> {||})
        (finite_constructed \<kappa> P (resolution_pending st) nd0))"
  define st0 where "st0 = Resolution_State (resolution_pending st) (resolution_nodes st) W"
  have step: "finite_construction_step \<kappa> P st nd0 = resolution_state_substitute ?\<sigma> st0"
    by (simp add: finite_construction_step_def W_def st0_def Let_def)
  have H0: "resolution_registrations_held \<kappa> st0" using H by (simp add: st0_def)
  have origin: "\<And>z. z \<in> resolution_state_variables (resolution_state_substitute ?\<sigma> st0) \<Longrightarrow>
      z \<in> resolution_state_variables st0"
  proof -
    fix z assume "z \<in> resolution_state_variables (resolution_state_substitute ?\<sigma> st0)"
    then obtain y where y: "y \<in> resolution_state_variables st0" "z |\<in>| finite_pattern_variables (?\<sigma> y)"
      using resolution_state_variables_substitute by blast
    have "z = y" using finite_construction_substitution_variables[OF y(2)] by simp
    then show "z \<in> resolution_state_variables st0" using y(1) by simp
  qed
  show ?thesis unfolding step
  proof (rule resolution_registrations_heldI)
    fix z assume "z \<in> resolution_state_variables (resolution_state_substitute ?\<sigma> st0)"
    then have "resolution_placed st0 z" using origin resolution_registrations_heldD(1)[OF H0] by blast
    then show "resolution_placed (resolution_state_substitute ?\<sigma> st0) z" by (simp add: resolution_placed_substitute)
  next
    fix nd a assume nd: "nd |\<in>| resolution_nodes (resolution_state_substitute ?\<sigma> st0)"
      and reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
      and only: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
    obtain m where m: "m |\<in>| resolution_nodes st0" "nd = resolution_node_substitute ?\<sigma> m" using nd by auto
    let ?x = "((resolution_node_position m,True),a)"
    have regm: "a |\<in>| witness_registered \<kappa> (resolution_node_site m) (resolution_node_schema m)"
      and onlym: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema m))"
      using reg only m(2) by simp_all
    have xs: "?x \<in> resolution_state_variables (resolution_state_substitute ?\<sigma> st0) \<Longrightarrow>
        ?\<sigma> ?x = Finite_Variable ?x"
    proof -
      assume "?x \<in> resolution_state_variables (resolution_state_substitute ?\<sigma> st0)"
      then obtain y where "?x |\<in>| finite_pattern_variables (?\<sigma> y)"
        using resolution_state_variables_substitute by blast
      then have "?x = y \<and> ?\<sigma> y = Finite_Variable y" by (rule finite_construction_substitution_variables)
      then show "?\<sigma> ?x = Finite_Variable ?x" by simp
    qed
    have "?x \<notin> resolution_state_variables st0 \<or> resolution_variable_held st0 m a"
      by (rule resolution_registrations_heldD(2)[OF H0 m(1) regm onlym])
    then show "((resolution_node_position nd,True),a) \<notin> resolution_state_variables (resolution_state_substitute ?\<sigma> st0) \<or>
        resolution_variable_held (resolution_state_substitute ?\<sigma> st0) nd a"
    proof
      assume "?x \<notin> resolution_state_variables st0"
      then show ?thesis using origin m(2) by auto
    next
      assume held: "resolution_variable_held st0 m a"
      show ?thesis
      proof (cases "?\<sigma> ?x = Finite_Variable ?x")
        case True
        have apart: "\<And>y. y \<noteq> ?x \<Longrightarrow> ?x |\<notin>| finite_pattern_variables (?\<sigma> y)"
        proof
          fix y assume "y \<noteq> ?x" and "?x |\<in>| finite_pattern_variables (?\<sigma> y)"
          then show False using finite_construction_substitution_variables[of ?x \<kappa> P "resolution_pending st" nd0 y]
            by simp
        qed
        have "resolution_variable_held (resolution_state_substitute ?\<sigma> st0) (resolution_node_substitute ?\<sigma> m) a"
          by (rule resolution_variable_held_substitute[where \<sigma>="?\<sigma>", OF held True apart])
        then show ?thesis using m(2) by simp
      next
        case False
        then show ?thesis using xs m(2) by auto
      qed
    qed
  qed
qed

section \<open>A resolution step keeps the invariant\<close>

lemma finite_clause_goals_cases:
  assumes "g0 |\<in>| finite_clause_goals q e c S"
  obtains s e' p where "(s,e',p) |\<in>| finite_schema_premises S"
    "g0 = Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_rename_apart (q,True) p)"
  | s M where "(s,M) |\<in>| finite_schema_materials S"
    "g0 = Resolution_Material_Goal (q@[s]) (e,c,s) (finite_rename_material (Pair (q,True)) M)"
  using assms by (auto simp: finite_clause_goals_def resolution_fset_simps)

lemma finite_rename_material_variables:
  "finite_material_variables (finite_rename_material f M) = f |`| finite_material_variables M"
  by (simp add: finite_rename_material_def finite_material_variables_def finite_pattern_variables_map fimage_funion)

lemma finite_schema_variables_members:
  "a |\<in>| finite_pattern_variables (finite_schema_conclusion S) \<Longrightarrow> a |\<in>| finite_schema_variables S"
  "(s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow> a |\<in>| finite_pattern_variables p \<Longrightarrow> a |\<in>| finite_schema_variables S"
  "(s,M) |\<in>| finite_schema_materials S \<Longrightarrow> a |\<in>| finite_material_variables M \<Longrightarrow> a |\<in>| finite_schema_variables S"
  by (force simp: finite_schema_variables_def resolution_fset_simps)+

text \<open>The variables a resolution by a clause at q adds are those of the clause renamed at q, flagged True.\<close>

lemma finite_clause_goal_variables:
  assumes g0: "g0 |\<in>| finite_clause_goals q e c S" and z: "z |\<in>| resolution_goal_variables g0"
  obtains b s where "z = ((q,True),b)" "resolution_goal_position g0 = q @ [s]" "resolution_registered_premise S s b"
    "b |\<in>| finite_schema_variables S"
  using g0
proof (cases rule: finite_clause_goals_cases)
  case (1 s e' p)
  obtain b where b: "b |\<in>| finite_pattern_variables p" "z = ((q,True),b)"
    using 1(2) z by (auto simp: finite_rename_apart_variables)
  have "resolution_registered_premise S s b" unfolding resolution_registered_premise_def using 1(1) b(1) by blast
  then show thesis using that[of b s] b(2) 1(2) finite_schema_variables_members(2)[OF 1(1) b(1)] by simp
next
  case (2 s M)
  obtain b where b: "b |\<in>| finite_material_variables M" "z = ((q,True),b)"
    using 2(2) z by (auto simp: finite_rename_material_variables)
  have "resolution_registered_premise S s b" unfolding resolution_registered_premise_def using 2(1) b(1) by blast
  then show thesis using that[of b s] b(2) 2(2) finite_schema_variables_members(3)[OF 2(1) b(1)] by simp
qed

lemma finite_clause_node_variables:
  assumes "z |\<in>| finite_pattern_variables (resolution_node_call (finite_clause_node q e c S)) \<or>
    (\<exists>b y. (b,y) |\<in>| resolution_node_bindings (finite_clause_node q e c S) \<and> z |\<in>| finite_pattern_variables y)"
  shows "\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S"
  using assms finite_schema_variables_members(1)
  by (auto simp: finite_clause_node_def finite_rename_apart_variables resolution_fset_simps)

lemma finite_clause_node_call_variables:
  "z |\<in>| finite_pattern_variables (resolution_node_call (finite_clause_node q e c S)) \<Longrightarrow>
    \<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_pattern_variables (finite_schema_conclusion S)"
  by (auto simp: finite_clause_node_def finite_rename_apart_variables)

lemma finite_clause_state_variables:
  assumes "z \<in> resolution_state_variables (Resolution_State (finite_clause_goals q e c S |\<union>| G)
      (finsert (finite_clause_node q e c S) N) W)"
  shows "z \<in> resolution_state_variables (Resolution_State G N W) \<or>
    (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S)"
  using assms
proof (cases rule: resolution_state_variables_cases)
  case (1 g)
  show ?thesis
  proof (cases "g |\<in>| finite_clause_goals q e c S")
    case True
    obtain b s where "z = ((q,True),b)" "resolution_goal_position g = q @ [s]"
      "resolution_registered_premise S s b" "b |\<in>| finite_schema_variables S"
      by (rule finite_clause_goal_variables[OF True 1(2)])
    then show ?thesis by blast
  next
    case False
    then have "g |\<in>| G" using 1(1) by simp
    then show ?thesis using resolution_state_variables_goal[of g "Resolution_State G N W"] 1(2) by simp
  qed
next
  case (2 nd)
  show ?thesis
  proof (cases "nd = finite_clause_node q e c S")
    case True
    have "\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S"
      by (rule finite_clause_node_variables[of z q e c S]) (use 2(2) True in simp)
    then show ?thesis by blast
  next
    case False
    then have "nd |\<in>| N" using 2(1) by simp
    then show ?thesis using resolution_state_variables_call[of nd "Resolution_State G N W"] 2(2) by simp
  qed
next
  case (3 nd b y)
  show ?thesis
  proof (cases "nd = finite_clause_node q e c S")
    case True
    have "\<exists>b'. z = ((q,True),b') \<and> b' |\<in>| finite_schema_variables S"
      by (rule finite_clause_node_variables[of z q e c S]) (use 3(2,3) True in blast)
    then show ?thesis by blast
  next
    case False
    then have "nd |\<in>| N" using 3(1) by simp
    then show ?thesis using resolution_state_variables_binding[of nd "Resolution_State G N W"] 3(2,3) by simp
  qed
qed

lemma finite_call_pairs_variables:
  assumes "z \<in> finite_pairs_variables [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)]"
  shows "fst (fst z) = q \<and> (snd (fst z) \<longrightarrow> snd z |\<in>| finite_pattern_variables (finite_schema_conclusion S)) \<or>
    z |\<in>| finite_pattern_variables p"
  using assms by (auto simp: finite_rename_apart_variables)

lemma resolution_registrations_call_step:
  assumes distinct: "resolution_positions_distinct st" and H: "resolution_registrations_held \<kappa> st"
    and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and unheld: "\<not> finite_held \<kappa> st (Resolution_Call_Goal q r e p)"
    and st': "st' |\<in>| finite_call_successors P st q r e p"
  shows "resolution_registrations_held \<kappa> st'"
proof -
  obtain i c S u where
    u: "finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
    and st'_eq: "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}))
        (finsert (finite_clause_node q e c S) (resolution_nodes st)) (resolution_witnesses st))"
    by (rule finite_call_successors_member[OF st'])
  define E where "E = [(finite_rename_apart (q,False) i,p),(finite_rename_apart (q,True) (finite_schema_conclusion S),p)]"
  define G0 where "G0 = resolution_pending st |-| {|Resolution_Call_Goal q r e p|}"
  define new where "new = finite_clause_node q e c S"
  define st0 where "st0 = Resolution_State (finite_clause_goals q e c S |\<union>| G0) (finsert new (resolution_nodes st))
    (resolution_witnesses st)"
  let ?u = "finite_binding_substitution u"
  have u': "finite_unify_pairs E = Some u" using u by (simp add: E_def)
  have st'_def: "st' = resolution_state_substitute ?u st0" using st'_eq by (simp add: st0_def G0_def new_def)
  have q_free: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd \<noteq> q"
  proof -
    fix nd assume nd: "nd |\<in>| resolution_nodes st"
    have all: "\<forall>g. g |\<in>| resolution_pending st \<longrightarrow> (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow>
        resolution_is_call g \<longrightarrow> resolution_goal_position g \<noteq> resolution_node_position nd)"
      using distinct unfolding resolution_positions_distinct_def by blast
    have c: "resolution_is_call (Resolution_Call_Goal q r e p)" by simp
    have "resolution_goal_position (Resolution_Call_Goal q r e p) \<noteq> resolution_node_position nd"
      using all g nd c by blast
    then show "resolution_node_position nd \<noteq> q" by simp
  qed
  have not_q: "\<And>z. z \<in> resolution_state_variables st \<Longrightarrow> fst (fst z) \<noteq> q"
  proof -
    fix z assume "z \<in> resolution_state_variables st"
    then have "resolution_placed st z" by (rule resolution_registrations_heldD(1)[OF H])
    then obtain nd where "nd |\<in>| resolution_nodes st" "resolution_node_position nd = fst (fst z)"
      unfolding resolution_placed_def by blast
    then show "fst (fst z) \<noteq> q" using q_free by metis
  qed
  have p_vars: "\<And>z. z |\<in>| finite_pattern_variables p \<Longrightarrow> z \<in> resolution_state_variables st"
  proof -
    fix z assume "z |\<in>| finite_pattern_variables p"
    then have "z |\<in>| resolution_goal_variables (Resolution_Call_Goal q r e p)" by simp
    then show "z \<in> resolution_state_variables st" by (rule resolution_state_variables_goal[OF g])
  qed
  have st0_vars: "\<And>z. z \<in> resolution_state_variables st0 \<Longrightarrow> z \<in> resolution_state_variables st \<or>
      (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S)"
  proof -
    fix z assume "z \<in> resolution_state_variables st0"
    then have "z \<in> resolution_state_variables (Resolution_State G0 (resolution_nodes st) (resolution_witnesses st)) \<or>
        (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S)"
      unfolding st0_def new_def by (rule finite_clause_state_variables)
    then show "z \<in> resolution_state_variables st \<or> (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S)"
    proof
      assume "z \<in> resolution_state_variables (Resolution_State G0 (resolution_nodes st) (resolution_witnesses st))"
      then have "z \<in> resolution_state_variables st"
      proof (cases rule: resolution_state_variables_cases)
        case (1 g') then show ?thesis using resolution_state_variables_goal[of g' st] by (simp add: G0_def)
      next
        case (2 nd) then show ?thesis using resolution_state_variables_call[of nd st] by simp
      next
        case (3 nd b y) then show ?thesis using resolution_state_variables_binding[of nd st b y] by simp
      qed
      then show ?thesis by blast
    qed blast
  qed
  have st'_vars: "\<And>z. z \<in> resolution_state_variables st' \<Longrightarrow>
      z \<in> resolution_state_variables st \<or> (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S) \<or>
      z \<in> finite_pairs_variables E"
  proof -
    fix z assume "z \<in> resolution_state_variables st'"
    then obtain y where y: "y \<in> resolution_state_variables st0" "z |\<in>| finite_pattern_variables (?u y)"
      using resolution_state_variables_substitute unfolding st'_def by blast
    have "z = y \<or> z \<in> finite_pairs_variables E" by (rule finite_unifier_variable[OF u' y(2)])
    then show "z \<in> resolution_state_variables st \<or> (\<exists>b. z = ((q,True),b) \<and> b |\<in>| finite_schema_variables S) \<or>
        z \<in> finite_pairs_variables E" using st0_vars[OF y(1)] by blast
  qed
  have nodes': "resolution_nodes st' = fimage (resolution_node_substitute ?u) (finsert new (resolution_nodes st))"
    by (simp add: st'_def st0_def)
  have new_pos: "resolution_node_position new = q" by (simp add: new_def finite_clause_node_def)
  have placed_node: "\<And>m z. m |\<in>| finsert new (resolution_nodes st) \<Longrightarrow> resolution_node_position m = fst (fst z) \<Longrightarrow>
      resolution_placed st' z"
  proof -
    fix m and z :: "('b list \<times> bool) \<times> 'a"
    assume m: "m |\<in>| finsert new (resolution_nodes st)" "resolution_node_position m = fst (fst z)"
    have "resolution_node_substitute ?u m |\<in>| resolution_nodes st'" unfolding nodes' by (rule fimageI[OF m(1)])
    moreover have "resolution_node_position (resolution_node_substitute ?u m) = fst (fst z)" using m(2) by simp
    ultimately show "resolution_placed st' z" unfolding resolution_placed_def by blast
  qed
  have placed_old: "\<And>z. z \<in> resolution_state_variables st \<Longrightarrow> resolution_placed st' z"
  proof -
    fix z assume "z \<in> resolution_state_variables st"
    then have "resolution_placed st z" by (rule resolution_registrations_heldD(1)[OF H])
    then obtain m where "m |\<in>| resolution_nodes st" "resolution_node_position m = fst (fst z)"
      unfolding resolution_placed_def by blast
    then show "resolution_placed st' z" using placed_node[of m z] by simp
  qed
  have placed_q: "\<And>z. z \<in> resolution_state_variables st' \<Longrightarrow> fst (fst z) = q \<Longrightarrow> resolution_placed st' z"
    using placed_node[of new] new_pos by simp
  have apart: "\<And>x y. x \<notin> finite_pairs_variables E \<Longrightarrow> y \<noteq> x \<Longrightarrow> x |\<notin>| finite_pattern_variables (?u y)"
    using finite_unifier_variable[OF u'] by blast
  have fixed: "\<And>x. x \<notin> finite_pairs_variables E \<Longrightarrow> ?u x = Finite_Variable x"
    by (rule finite_unify_pairs_outside[OF u'])
  show ?thesis
  proof (rule resolution_registrations_heldI)
    fix z assume zs: "z \<in> resolution_state_variables st'"
    from st'_vars[OF zs] show "resolution_placed st' z"
    proof (elim disjE exE conjE)
      assume "z \<in> resolution_state_variables st" then show ?thesis by (rule placed_old)
    next
      fix b assume "z = ((q,True),b)" then show ?thesis using placed_q[OF zs] by simp
    next
      assume "z \<in> finite_pairs_variables E"
      then have "fst (fst z) = q \<or> z |\<in>| finite_pattern_variables p"
        using finite_call_pairs_variables[of z q i p S, folded E_def] by blast
      then show ?thesis using placed_q[OF zs] placed_old p_vars by blast
    qed
  next
    fix nd a assume nd: "nd |\<in>| resolution_nodes st'"
      and reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
      and only: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
    obtain m where m: "m |\<in>| finsert new (resolution_nodes st)" "nd = resolution_node_substitute ?u m"
      using nd nodes' by auto
    let ?x = "((resolution_node_position m,True),a)"
    have regm: "a |\<in>| witness_registered \<kappa> (resolution_node_site m) (resolution_node_schema m)"
      and onlym: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema m))"
      using reg only m(2) by simp_all
    show "((resolution_node_position nd,True),a) \<notin> resolution_state_variables st' \<or> resolution_variable_held st' nd a"
    proof (cases "m = new")
      case True
      have xq: "?x = ((q,True),a)" using True new_pos by simp
      have schema: "resolution_node_schema m = S" using True by (simp add: new_def finite_clause_node_def)
      have x_pairs: "?x \<notin> finite_pairs_variables E"
      proof
        assume "?x \<in> finite_pairs_variables E"
        then have "fst (fst ?x) = q \<and> (snd (fst ?x) \<longrightarrow> snd ?x |\<in>| finite_pattern_variables (finite_schema_conclusion S)) \<or>
            ?x |\<in>| finite_pattern_variables p"
          using finite_call_pairs_variables[of ?x q i p S, folded E_def] by blast
        then show False using onlym schema xq p_vars not_q by fastforce
      qed
      have x_old: "((q,True),a) \<notin> resolution_state_variables st" using not_q by fastforce
      show ?thesis
      proof (cases "a |\<in>| finite_schema_variables S")
        case False
        have "?x \<notin> resolution_state_variables st'"
        proof
          assume "?x \<in> resolution_state_variables st'"
          from st'_vars[OF this] show False using x_pairs x_old xq False by auto
        qed
        then show ?thesis using m(2) by simp
      next
        case True
        have held0: "resolution_variable_held st0 new a"
        proof (rule resolution_variable_heldI)
          show "(a,Finite_Variable ((resolution_node_position new,True),a)) |\<in>| resolution_node_bindings new"
            using True by (simp add: new_def finite_clause_node_def)
        next
          fix m' assume m': "m' |\<in>| resolution_nodes st0"
          show "((resolution_node_position new,True),a) |\<notin>| finite_pattern_variables (resolution_node_call m')"
          proof (cases "m' = new")
            case True
            then show ?thesis using onlym schema \<open>m = new\<close> finite_clause_node_call_variables[of _ q e c S]
              unfolding new_def by auto
          next
            case False
            then have "m' |\<in>| resolution_nodes st" using m' by (simp add: st0_def)
            then show ?thesis using x_old new_pos resolution_state_variables_call[of m' st] by auto
          qed
        next
          fix b y assume "(b,y) |\<in>| resolution_node_bindings new"
            and "((resolution_node_position new,True),a) |\<in>| finite_pattern_variables y"
          then show "b = a" using new_pos by (auto simp: new_def finite_clause_node_def resolution_fset_simps)
        next
          fix g' assume g': "g' |\<in>| resolution_pending st0"
            and xg: "((resolution_node_position new,True),a) |\<in>| resolution_goal_variables g'"
          show "\<exists>s. resolution_goal_position g' = resolution_node_position new @ [s] \<and>
              resolution_registered_premise (resolution_node_schema new) s a"
          proof (cases "g' |\<in>| finite_clause_goals q e c S")
            case True
            have xg': "((q,True),a) |\<in>| resolution_goal_variables g'" using xg new_pos by simp
            obtain b s where "((q,True),a) = ((q,True),b)" "resolution_goal_position g' = q @ [s]"
              "resolution_registered_premise S s b" "b |\<in>| finite_schema_variables S"
              by (rule finite_clause_goal_variables[OF True xg'])
            then show ?thesis using new_pos by (simp add: new_def finite_clause_node_def)
          next
            case False
            then have "g' |\<in>| resolution_pending st" using g' by (simp add: st0_def G0_def)
            then show ?thesis using x_old new_pos resolution_state_variables_goal[of g' st] xg by auto
          qed
        qed
        have fx: "?u ((resolution_node_position new,True),a) = Finite_Variable ((resolution_node_position new,True),a)"
          using fixed[OF x_pairs] xq new_pos by simp
        have ax: "\<And>y. y \<noteq> ((resolution_node_position new,True),a) \<Longrightarrow>
            ((resolution_node_position new,True),a) |\<notin>| finite_pattern_variables (?u y)"
          using apart[OF x_pairs] xq new_pos by simp
        have "resolution_variable_held st' (resolution_node_substitute ?u new) a"
          unfolding st'_def by (rule resolution_variable_held_substitute[where \<sigma>="?u", OF held0 fx ax])
        then show ?thesis using m(2) \<open>m = new\<close> by simp
      qed
    next
      case False
      then have mold: "m |\<in>| resolution_nodes st" using m(1) by simp
      have mq: "resolution_node_position m \<noteq> q" by (rule q_free[OF mold])
      have x_p: "?x |\<notin>| finite_pattern_variables p"
        using resolution_registrations_unheld[OF H g unheld mold regm onlym] by simp
      have x_pairs: "?x \<notin> finite_pairs_variables E"
      proof
        assume "?x \<in> finite_pairs_variables E"
        then have "fst (fst ?x) = q \<and> (snd (fst ?x) \<longrightarrow> snd ?x |\<in>| finite_pattern_variables (finite_schema_conclusion S)) \<or>
            ?x |\<in>| finite_pattern_variables p"
          using finite_call_pairs_variables[of ?x q i p S, folded E_def] by blast
        then show False using x_p mq by simp
      qed
      have "?x \<notin> resolution_state_variables st \<or> resolution_variable_held st m a"
        by (rule resolution_registrations_heldD(2)[OF H mold regm onlym])
      then show ?thesis
      proof
        assume x_old: "?x \<notin> resolution_state_variables st"
        have "?x \<notin> resolution_state_variables st'"
        proof
          assume "?x \<in> resolution_state_variables st'"
          from st'_vars[OF this] show False using x_old x_pairs mq by auto
        qed
        then show ?thesis using m(2) by simp
      next
        assume held: "resolution_variable_held st m a"
        have held0: "resolution_variable_held st0 m a"
        proof (rule resolution_variable_heldI)
          show "(a,Finite_Variable ?x) |\<in>| resolution_node_bindings m" by (rule resolution_variable_heldD(1)[OF held])
        next
          fix m' assume m': "m' |\<in>| resolution_nodes st0"
          show "?x |\<notin>| finite_pattern_variables (resolution_node_call m')"
          proof (cases "m' = new")
            case True
            then show ?thesis using mq finite_clause_node_call_variables[of ?x q e c S] unfolding new_def by auto
          next
            case False
            then have "m' |\<in>| resolution_nodes st" using m' by (simp add: st0_def)
            then show ?thesis by (rule resolution_variable_heldD(2)[OF held])
          qed
        next
          fix b y assume "(b,y) |\<in>| resolution_node_bindings m" and "?x |\<in>| finite_pattern_variables y"
          then show "b = a" by (rule resolution_variable_heldD(3)[OF held])
        next
          fix g' assume g': "g' |\<in>| resolution_pending st0" and xg: "?x |\<in>| resolution_goal_variables g'"
          show "\<exists>s. resolution_goal_position g' = resolution_node_position m @ [s] \<and>
              resolution_registered_premise (resolution_node_schema m) s a"
          proof (cases "g' |\<in>| finite_clause_goals q e c S")
            case True
            obtain b s where "?x = ((q,True),b)" "resolution_goal_position g' = q @ [s]"
              "resolution_registered_premise S s b" "b |\<in>| finite_schema_variables S"
              by (rule finite_clause_goal_variables[OF True xg])
            then show ?thesis using mq by simp
          next
            case False
            then have "g' |\<in>| resolution_pending st" using g' by (simp add: st0_def G0_def)
            then show ?thesis by (rule resolution_variable_heldD(4)[OF held _ xg])
          qed
        qed
        have "resolution_variable_held st' (resolution_node_substitute ?u m) a"
          unfolding st'_def
          by (rule resolution_variable_held_substitute[where \<sigma>="?u", OF held0 fixed[OF x_pairs] apart[OF x_pairs]])
        then show ?thesis using m(2) by simp
      qed
    qed
  qed
qed

lemma finite_material_pairs_variables:
  assumes "E |\<in>| finite_material_instance_pairs W M" and "z \<in> finite_pairs_variables E"
  shows "z |\<in>| finite_material_variables M"
  using finite_material_instance_pairs_member[OF assms(1)] assms(2)
  by (auto simp: finite_material_variables_def)

lemma resolution_registrations_material_step:
  assumes H: "resolution_registrations_held \<kappa> st"
    and g: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and unheld: "\<not> finite_held \<kappa> st (Resolution_Material_Goal q r M)"
    and st': "st' |\<in>| finite_material_successors st q r M"
  shows "resolution_registrations_held \<kappa> st'"
proof -
  obtain Ws W E u where E: "E |\<in>| finite_material_instance_pairs W M" and u: "finite_unify_pairs E = Some u"
    and st'_eq: "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
    by (rule finite_material_successors_member[OF st'])
  define st0 where "st0 = Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|})
      (resolution_nodes st) (resolution_witnesses st)"
  let ?u = "finite_binding_substitution u"
  have st'_def: "st' = resolution_state_substitute ?u st0" using st'_eq by (simp add: st0_def)
  have M_vars: "\<And>z. z \<in> finite_pairs_variables E \<Longrightarrow> z \<in> resolution_state_variables st"
  proof -
    fix z assume "z \<in> finite_pairs_variables E"
    then have "z |\<in>| resolution_goal_variables (Resolution_Material_Goal q r M)"
      using finite_material_pairs_variables[OF E] by simp
    then show "z \<in> resolution_state_variables st" by (rule resolution_state_variables_goal[OF g])
  qed
  have st0_vars: "\<And>z. z \<in> resolution_state_variables st0 \<Longrightarrow> z \<in> resolution_state_variables st"
  proof -
    fix z assume "z \<in> resolution_state_variables st0"
    then show "z \<in> resolution_state_variables st"
    proof (cases rule: resolution_state_variables_cases)
      case (1 g') then show ?thesis using resolution_state_variables_goal[of g' st] by (simp add: st0_def)
    next
      case (2 nd) then show ?thesis using resolution_state_variables_call[of nd st] by (simp add: st0_def)
    next
      case (3 nd b y) then show ?thesis using resolution_state_variables_binding[of nd st b y] by (simp add: st0_def)
    qed
  qed
  have st'_vars: "\<And>z. z \<in> resolution_state_variables st' \<Longrightarrow> z \<in> resolution_state_variables st"
  proof -
    fix z assume "z \<in> resolution_state_variables st'"
    then obtain y where y: "y \<in> resolution_state_variables st0" "z |\<in>| finite_pattern_variables (?u y)"
      using resolution_state_variables_substitute unfolding st'_def by blast
    have "z = y \<or> z \<in> finite_pairs_variables E" by (rule finite_unifier_variable[OF u y(2)])
    then show "z \<in> resolution_state_variables st" using st0_vars[OF y(1)] M_vars by blast
  qed
  have nodes': "resolution_nodes st' = fimage (resolution_node_substitute ?u) (resolution_nodes st)"
    by (simp add: st'_def st0_def)
  show ?thesis
  proof (rule resolution_registrations_heldI)
    fix z assume "z \<in> resolution_state_variables st'"
    then have "resolution_placed st z" using st'_vars resolution_registrations_heldD(1)[OF H] by blast
    then obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = fst (fst z)"
      unfolding resolution_placed_def by blast
    have "resolution_node_substitute ?u m |\<in>| resolution_nodes st'" unfolding nodes' by (rule fimageI[OF m(1)])
    moreover have "resolution_node_position (resolution_node_substitute ?u m) = fst (fst z)" using m(2) by simp
    ultimately show "resolution_placed st' z" unfolding resolution_placed_def by blast
  next
    fix nd a assume nd: "nd |\<in>| resolution_nodes st'"
      and reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
      and only: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
    obtain m where m: "m |\<in>| resolution_nodes st" "nd = resolution_node_substitute ?u m" using nd nodes' by auto
    let ?x = "((resolution_node_position m,True),a)"
    have regm: "a |\<in>| witness_registered \<kappa> (resolution_node_site m) (resolution_node_schema m)"
      and onlym: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema m))"
      using reg only m(2) by simp_all
    have x_M: "?x |\<notin>| finite_material_variables M"
      using resolution_registrations_unheld[OF H g unheld m(1) regm onlym] by simp
    have x_pairs: "?x \<notin> finite_pairs_variables E" using finite_material_pairs_variables[OF E] x_M by blast
    have "?x \<notin> resolution_state_variables st \<or> resolution_variable_held st m a"
      by (rule resolution_registrations_heldD(2)[OF H m(1) regm onlym])
    then show "((resolution_node_position nd,True),a) \<notin> resolution_state_variables st' \<or> resolution_variable_held st' nd a"
    proof
      assume "?x \<notin> resolution_state_variables st"
      then show ?thesis using st'_vars m(2) by auto
    next
      assume held: "resolution_variable_held st m a"
      have held0: "resolution_variable_held st0 m a"
      proof (rule resolution_variable_heldI)
        show "(a,Finite_Variable ?x) |\<in>| resolution_node_bindings m" by (rule resolution_variable_heldD(1)[OF held])
      next
        fix m' assume "m' |\<in>| resolution_nodes st0"
        then show "?x |\<notin>| finite_pattern_variables (resolution_node_call m')"
          using resolution_variable_heldD(2)[OF held] by (simp add: st0_def)
      next
        fix b y assume "(b,y) |\<in>| resolution_node_bindings m" and "?x |\<in>| finite_pattern_variables y"
        then show "b = a" by (rule resolution_variable_heldD(3)[OF held])
      next
        fix g' assume "g' |\<in>| resolution_pending st0" and xg: "?x |\<in>| resolution_goal_variables g'"
        then have "g' |\<in>| resolution_pending st" by (simp add: st0_def)
        then show "\<exists>s. resolution_goal_position g' = resolution_node_position m @ [s] \<and>
            resolution_registered_premise (resolution_node_schema m) s a"
          by (rule resolution_variable_heldD(4)[OF held _ xg])
      qed
      have "resolution_variable_held st' (resolution_node_substitute ?u m) a"
        unfolding st'_def
        by (rule resolution_variable_held_substitute[where \<sigma>="?u", OF held0 finite_unify_pairs_outside[OF u x_pairs]])
          (use finite_unifier_variable[OF u] x_pairs in blast)
      then show ?thesis using m(2) by simp
    qed
  qed
qed

section \<open>Where a registered variable is held, and what stands under a pending call\<close>

text \<open>
  Under the invariant a registered premise-only variable of a node is held only at the node's premises, so a goal
  holding it stands in every focus the node stands in (task 526, q113 (iii)). And under R4's invariant nothing stands
  under a pending call but the call itself: no node, since a node's ancestors are nodes and no node stands at a pending
  call's position, and no other pending goal (q113 (ii)).
\<close>

lemma resolution_focused_child:
  assumes "resolution_focused F q"
  shows "resolution_focused F (q @ [s])"
proof (cases F)
  case (Some f)
  then have t: "take (length f) q = f" using assms by (simp add: resolution_focused_def)
  have "length f \<le> length q" using arg_cong[OF t, of length] by (simp add: min_def split: if_splits)
  then show ?thesis using Some t by (simp add: resolution_focused_def)
qed (simp add: resolution_focused_def)

lemma resolution_registrations_held_focused:
  assumes H: "resolution_registrations_held \<kappa> st" and nd: "nd |\<in>| resolution_nodes st"
    and focus: "resolution_focused F (resolution_node_position nd)"
    and reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
    and only: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion (resolution_node_schema nd))"
    and h: "h |\<in>| resolution_pending st" and x: "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables h"
  shows "resolution_focused F (resolution_goal_position h)"
proof -
  have held: "resolution_variable_held st nd a"
    using resolution_registrations_heldD(2)[OF H nd reg] only resolution_state_variables_goal[OF h x] by blast
  obtain s where "resolution_goal_position h = resolution_node_position nd @ [s]"
    using resolution_variable_heldD(4)[OF held h x] by blast
  then show ?thesis using resolution_focused_child[OF focus] by simp
qed


lemma finite_call_goal_no_node_under:
  assumes I: "resolution_invariant P d t st" and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and nd: "nd |\<in>| resolution_nodes st"
  shows "\<not> resolution_focused (Some q) (resolution_node_position nd)"
proof
  assume "resolution_focused (Some q) (resolution_node_position nd)"
  then have t: "take (length q) (resolution_node_position nd) = q" by (simp add: resolution_focused_def)
  have len: "length q \<le> length (resolution_node_position nd)"
    using arg_cong[OF t, of length] by (simp add: min_def split: if_splits)
  obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = q"
    using resolution_node_prefix[OF I, of "length (resolution_node_position nd)"] nd len t by blast
  show False using resolution_call_goal_no_node[OF I g m(1)] m(2) by simp
qed

lemma finite_call_goal_alone_under:
  assumes I: "resolution_invariant P d t st" and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and h: "h |\<in>| resolution_pending st" and focus: "resolution_focused (Some q) (resolution_goal_position h)"
  shows "h = Resolution_Call_Goal q r e p"
proof (cases "resolution_goal_position h = q")
  case True
  then show ?thesis using I g h unfolding resolution_invariant_def resolution_positions_distinct_def by force
next
  case False
  have t: "take (length q) (resolution_goal_position h) = q" using focus by (simp add: resolution_focused_def)
  have "resolution_before q (resolution_goal_position h)"
    unfolding resolution_before_def using t False by (metis linorder_not_less take_all)
  then obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = q"
    using resolution_goal_ancestor_node[OF I h] by blast
  show ?thesis using resolution_call_goal_no_node[OF I g m(1)] m(2) by simp
qed

theorem resolution_registrations_goal_step:
  assumes distinct: "resolution_positions_distinct st" and H: "resolution_registrations_held \<kappa> st"
    and g: "g |\<in>| resolution_pending st" and unheld: "\<not> finite_held \<kappa> st g"
    and st': "st' |\<in>| finite_goal_successors P st g"
  shows "resolution_registrations_held \<kappa> st'"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  have s: "st' |\<in>| finite_call_successors P st q r e p" using st' Resolution_Call_Goal by simp
  show ?thesis
    by (rule resolution_registrations_call_step[OF distinct H g[unfolded Resolution_Call_Goal]
      unheld[unfolded Resolution_Call_Goal] s])
next
  case (Resolution_Material_Goal q r M)
  have s: "st' |\<in>| finite_material_successors st q r M" using st' Resolution_Material_Goal by simp
  show ?thesis
    by (rule resolution_registrations_material_step[OF H g[unfolded Resolution_Material_Goal]
      unheld[unfolded Resolution_Material_Goal] s])
qed

end
