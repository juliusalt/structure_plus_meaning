theory Factor_Least_Witness_Registrations
  imports Factor_Resolution_Commitments Factor_Least_Collections Factor_Finite_Mapped_Extensions
    Factor_Construction_Holders
begin

text \<open>
  The generic contract of task 496's registrations (W4 of DECISIONS.md "A checker does not produce", its first part):
  completeness of a registered variable at a program, for any finite program and witness construction; distinctness
  of W2's registrations, a formation condition under which the construction's value at a registered variable is that
  one registration's; the construction from complete registrations complete; and relocation of a
  construction and its completeness by an injective placement of definitions. A construction is production: the
  checked program is read by the search and the finite proof checker as it stands, and no clause is refined,
  restated or added. Completeness is what a refusal at a construction rests on.
\<close>

section \<open>The premises that hold a registered variable\<close>

text \<open>
  A registered variable of a clause is read through the clause's premises that hold it: each call premise holding it
  is true at the valuation, each material premise holding it is satisfied there. The premises holding it are bound by
  a set of other variables when each has no further variable: at the search's call of the construction, the goals
  holding the variable have no other free variable, so the ground bindings the construction receives cover them.
\<close>

definition finite_variable_premises_hold ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> bool" where
  "finite_variable_premises_hold P S a \<theta> \<longleftrightarrow>
    (\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises S \<longrightarrow> a |\<in>| finite_pattern_variables p \<longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)) \<and>
    (\<forall>s M. (s,M) |\<in>| finite_schema_materials S \<longrightarrow> a |\<in>| finite_material_variables M \<longrightarrow>
      finite_material_ground_satisfied
        (finite_material_pattern_substitute (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'a finite_term_pattern) M))"

definition finite_variable_premises_bound :: "('a,'s,'d) finite_factor_schema \<Rightarrow> 'a \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "finite_variable_premises_bound S a X \<longleftrightarrow>
    (\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises S \<longrightarrow> a |\<in>| finite_pattern_variables p \<longrightarrow>
      finite_pattern_variables p |\<subseteq>| finsert a X) \<and>
    (\<forall>s M. (s,M) |\<in>| finite_schema_materials S \<longrightarrow> a |\<in>| finite_material_variables M \<longrightarrow>
      finite_material_variables M |\<subseteq>| finsert a X)"

lemma finite_variable_premises_bound_premise:
  assumes scope: "finite_variable_premises_bound S a X" and premise: "(s,e,p) |\<in>| finite_schema_premises S"
    and held: "a |\<in>| finite_pattern_variables p" and other: "x |\<in>| finite_pattern_variables p" "x\<noteq>a"
  shows "x |\<in>| X"
proof -
  have "finite_pattern_variables p |\<subseteq>| finsert a X"
    using scope premise held unfolding finite_variable_premises_bound_def by blast
  then have "x |\<in>| finsert a X" using other(1) by (rule fsubsetD)
  then show ?thesis using other(2) by simp
qed

section \<open>Completeness of a registered variable\<close>

text \<open>
  A value function V, from the ground bindings of a clause's other variables to a value of the variable a or nothing,
  is complete at the clause when, for every formed functional binding B not binding a and covering the premises that
  hold a at which V returns v, those premises hold at some formed value of a exactly when they hold at v. A witnessed
  failure at v then refutes the premises at every value. A construction is complete at a program when every
  variable it registers at a clause of the program is complete with the construction's values; a W2 registration is
  complete when its collection value is (@{const finite_registration_value}), W2's construction returning a value
  only where its queries were complete.
\<close>

definition finite_value_complete ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a \<Rightarrow>
      (('a\<times>finite_factor_term) fset \<Rightarrow> finite_factor_term option) \<Rightarrow> bool" where
  "finite_value_complete P S a V \<longleftrightarrow> (\<forall>B v. finite_relation_functional B \<longrightarrow>
      fBall B (\<lambda>(b,t). finite_term_formed t) \<longrightarrow> a |\<notin>| fimage fst B \<longrightarrow>
      finite_variable_premises_bound S a (fimage fst B) \<longrightarrow> V B = Some v \<longrightarrow>
      ((\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P S a ((finite_binding_valuation B)(a:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P S a ((finite_binding_valuation B)(a:=v))))"

definition finite_construction_complete ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_construction_complete \<kappa> P \<longleftrightarrow> (\<forall>d c S a. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
      a |\<in>| witness_registered \<kappa> d S \<longrightarrow> a |\<notin>| finite_pattern_variables (finite_schema_conclusion S) \<and>
      finite_value_complete P S a (\<lambda>B. witness_value \<kappa> P d S B a))"

definition finite_registration_complete ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow> bool" where
  "finite_registration_complete P n R \<longleftrightarrow>
    registration_variable R |\<notin>| finite_pattern_variables (finite_schema_conclusion (registration_schema R)) \<and>
    finite_value_complete P (registration_schema R) (registration_variable R) (finite_registration_value P n R)"

text \<open>The empty construction registers nothing and is complete at every program.\<close>

lemma no_witness_construction_complete: "finite_construction_complete no_witness_construction P"
  by (simp add: finite_construction_complete_def no_witness_construction_def)

section \<open>Distinct registrations\<close>

text \<open>
  W2's construction reads the first registration naming the clause's site, schema and variable. Registrations are
  distinct when no two name the same: then the construction's value at a registered variable is its one
  registration's collection value. A construction from complete registrations is complete whether or not they are
  distinct: the registration it reads is a member of the list (task 615, review 527's follow-up 4).
\<close>

definition finite_registration_key ::
    "('a,'s,'d,'v) collection_registration \<Rightarrow> 'd \<times> ('a,'s,'d) finite_factor_schema \<times> 'a" where
  "finite_registration_key R = (registration_site R,registration_schema R,registration_variable R)"

definition finite_registrations_distinct :: "('a,'s,'d,'v) collection_registration list \<Rightarrow> bool" where
  "finite_registrations_distinct Rs \<longleftrightarrow> distinct (map finite_registration_key Rs)"

lemma finite_registrations_distinct_find:
  assumes distinct: "finite_registrations_distinct Rs" and R: "R \<in> set Rs"
  shows "find (\<lambda>R'. finite_registration_matches (registration_site R) (registration_schema R) R' \<and>
      registration_variable R' = registration_variable R) Rs = Some R"
proof -
  let ?P = "\<lambda>R'. finite_registration_matches (registration_site R) (registration_schema R) R' \<and>
      registration_variable R' = registration_variable R"
  have key: "\<And>R'. ?P R' \<longleftrightarrow> finite_registration_key R' = finite_registration_key R"
    by (auto simp: finite_registration_matches_def finite_registration_key_def)
  have "find ?P Rs \<noteq> None" using R key by (auto simp: find_None_iff)
  then obtain R' where f: "find ?P Rs = Some R'" by auto
  then have R': "R' \<in> set Rs" "?P R'" by (auto simp: find_Some_iff)
  have inj: "inj_on finite_registration_key (set Rs)"
    using distinct by (simp add: finite_registrations_distinct_def distinct_map)
  have "R' = R" using inj_onD[OF inj _ R'(1) R] R'(2) key by blast
  then show ?thesis using f by simp
qed

theorem finite_collection_construction_value_at:
  assumes "finite_registrations_distinct Rs" and "R \<in> set Rs"
  shows "witness_value (finite_collection_construction Rs n) P (registration_site R) (registration_schema R) B
      (registration_variable R) = finite_registration_value P n R B"
proof -
  have f: "find (\<lambda>R'. finite_registration_matches (registration_site R) (registration_schema R) R' \<and>
      registration_variable R' = registration_variable R) Rs = Some R"
    by (rule finite_registrations_distinct_find[OF assms])
  show ?thesis unfolding finite_collection_construction_def finite_witness_construction.select_convs f
    by (simp only: option.case)
qed

text \<open>
  The construction reads a registration only at a clause of the program: it is complete when every registration
  naming a clause of the program is complete there, whatever the others (task 528: the given's readers hold no clause
  at 525 or 561, the request's program none at 392 or 525).
\<close>

theorem finite_collection_construction_complete_at:
  assumes complete: "\<And>R c. R \<in> set Rs \<Longrightarrow>
      ((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses P \<Longrightarrow>
      finite_registration_complete P n R"
  shows "finite_construction_complete (finite_collection_construction Rs n) P"
  unfolding finite_construction_complete_def
proof (intro allI impI)
  fix d c S a
  assume clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and "a |\<in>| witness_registered (finite_collection_construction Rs n) d S"
  then have "\<exists>R\<in>set Rs. finite_registration_matches d S R \<and> registration_variable R = a"
    by (simp only: finite_collection_construction_registered)
  then have "find (\<lambda>R. finite_registration_matches d S R \<and> registration_variable R = a) Rs \<noteq> None"
    by (auto simp: find_None_iff)
  then obtain R where f: "find (\<lambda>R. finite_registration_matches d S R \<and> registration_variable R = a) Rs = Some R"
    by auto
  have R: "R \<in> set Rs" "finite_registration_matches d S R" "registration_variable R = a"
    using f by (auto simp: find_Some_iff)
  have S: "registration_schema R = S" and site: "registration_site R = d"
    using R(2) by (simp_all add: finite_registration_matches_def)
  have "\<And>B. witness_value (finite_collection_construction Rs n) P d S B a = finite_registration_value P n R B"
  proof -
    fix B show "witness_value (finite_collection_construction Rs n) P d S B a = finite_registration_value P n R B"
      unfolding finite_collection_construction_def finite_witness_construction.select_convs f by (simp only: option.case)
  qed
  then have eq: "(\<lambda>B. witness_value (finite_collection_construction Rs n) P d S B a) = finite_registration_value P n R"
    by (rule ext)
  have "finite_registration_complete P n R" using complete[OF R(1)] clause S site by simp
  then show "a |\<notin>| finite_pattern_variables (finite_schema_conclusion S) \<and>
      finite_value_complete P S a (\<lambda>B. witness_value (finite_collection_construction Rs n) P d S B a)"
    using S R(3) unfolding eq by (simp add: finite_registration_complete_def)
qed

theorem finite_collection_construction_complete:
  assumes complete: "\<And>R. R \<in> set Rs \<Longrightarrow> finite_registration_complete P n R"
  shows "finite_construction_complete (finite_collection_construction Rs n) P"
  by (rule finite_collection_construction_complete_at) (rule complete)

section \<open>An unconstructed registration\<close>

text \<open>
  The diagnosis @{const Resolution_Unconstructed} names exactly each registration of a node whose variable is free and
  ready for its construction, at which the construction returns nothing, with the goals held at it.
\<close>

lemma finite_unconstructed_member:
  "D |\<in>| finite_unconstructed \<kappa> P st \<longleftrightarrow> (\<exists>nd a. nd |\<in>| resolution_nodes st \<and> a |\<in>| finite_free_registered \<kappa> nd \<and>
    finite_registration_ready (resolution_pending st) nd a \<and> finite_registered_value \<kappa> P nd a = None \<and>
    D = Resolution_Unconstructed (resolution_node_site nd) (resolution_node_schema nd) a
      (finite_goal_holders (resolution_pending st) ((resolution_node_position nd,True),a)))"
  by (auto simp: finite_unconstructed_def Let_def resolution_fset_simps)

section \<open>A construction step at complete registrations keeps a support\<close>

text \<open>
  A construction step replaces each constructed registered variable x of a node by its value v. The goals holding x
  are exactly the node's premises holding the registered variable (@{text resolution_registrations_held}), and at the
  node's ground bindings the construction's completeness carries their truth at the support's value of x to their
  truth at v. The ranks that justify pruning do not carry across the step, so every node then present is barred: the
  successor is supported at the larger barred set, which asks truth, satisfaction and placement alone of it.
\<close>

declare resolution_value_variable [simp]

lemma finite_material_substitute_variables_subset:
  "b |\<in>| finite_material_variables M \<Longrightarrow>
    finite_pattern_variables (\<sigma> b) |\<subseteq>| finite_material_variables (finite_material_pattern_substitute \<sigma> M)"
  unfolding finite_material_variables_def using finite_substitute_variables_subset[of b _ \<sigma>]
  by (auto simp: finite_material_pattern_substitute_def)

lemma resolution_value_ground_residual:
  "finite_pattern_variables p = {||} \<Longrightarrow> resolution_value \<theta> p = finite_residual_term p"
  by (simp add: resolution_value_def finite_pattern_substitute_ground)


lemma finite_material_ground_satisfied_values:
  "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M) \<longleftrightarrow>
    finite_material_observation (resolution_value \<theta> (finite_material_source M)) (resolution_value \<theta> (finite_material_atoms M))
      (resolution_value \<theta> (finite_material_edges M)) (resolution_value \<theta> (finite_material_counts M))
      (resolution_value \<theta> (finite_material_functions M))"
  by (simp add: finite_material_ground_satisfied_def resolution_value_substitute finite_exact_term_pattern_eq_iff)

lemma finite_material_observation_formed:
  assumes "finite_material_observation s a e b f"
  shows "finite_term_formed s \<and> finite_term_formed a \<and> finite_term_formed e \<and> finite_term_formed b \<and> finite_term_formed f"
  using material_observation_formed[OF assms[unfolded finite_material_observation_correct]]
  by (simp add: finite_term_formed_correct)

lemma finite_material_satisfied_variable_formed:
  assumes sat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and x: "x |\<in>| finite_material_variables M"
  shows "finite_term_formed (\<theta> x)"
proof -
  have obs: "finite_material_observation (resolution_value \<theta> (finite_material_source M)) (resolution_value \<theta> (finite_material_atoms M))
      (resolution_value \<theta> (finite_material_edges M)) (resolution_value \<theta> (finite_material_counts M))
      (resolution_value \<theta> (finite_material_functions M))"
    using sat by (simp only: finite_material_ground_satisfied_values)
  show ?thesis
    using finite_material_observation_formed[OF obs] x resolution_value_variable_formed
    unfolding finite_material_variables_def by auto
qed


theorem finite_complete_construction_supported:
  assumes I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and sup: "resolution_supported_at U F B P st \<theta>"
    and focus: "resolution_focused F (resolution_node_position nd)"
    and complete: "finite_construction_complete \<kappa> P" and nd: "nd |\<in>| resolution_nodes st"
  shows "\<exists>\<theta>'. resolution_supported_at U F (finite_committed_barring B st) P
      (finite_construction_step \<kappa> P st nd) \<theta>'"
proof -
  let ?G = "resolution_pending st"
  let ?C = "finite_constructed \<kappa> P ?G nd"
  let ?\<sigma> = "finite_construction_substitution \<kappa> P ?G nd"
  let ?pos = "resolution_node_position nd"
  let ?S = "resolution_node_schema nd"
  let ?B = "finite_node_ground_bindings nd"
  let ?x = "\<lambda>a. ((?pos,True),a)"
  define \<theta>' where "\<theta>' = (\<lambda>z. if fst z = (?pos,True) \<and> snd z |\<in>| ?C
      then the (finite_registered_value \<kappa> P nd (snd z)) else \<theta> z)"
  define W where "W = resolution_witnesses st |\<union>|
      ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
          Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||}) ?C)"
  define st0 where "st0 = Resolution_State ?G (resolution_nodes st) W"
  have step: "finite_construction_step \<kappa> P st nd = resolution_state_substitute ?\<sigma> st0"
    by (simp add: finite_construction_step_def W_def st0_def Let_def)
  have placed_nodes: "resolution_nodes_placed P d t st" and distinct: "resolution_positions_distinct st"
    using I unfolding resolution_invariant_def by blast+
  have linked: "resolution_node_linked P st nd"
    using placed_nodes nd unfolding resolution_nodes_placed_def by blast
  have bformed: "\<And>a x. (a,x) |\<in>| resolution_node_bindings nd \<Longrightarrow> finite_pattern_formed x"
    using placed_nodes nd unfolding resolution_nodes_placed_def by blast
  obtain \<beta> where bind: "resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables ?S)"
    and prem: "\<And>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<Longrightarrow>
        Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G \<or>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = ?pos@[s] \<and>
          resolution_node_site m = e \<and> resolution_node_call m = finite_pattern_substitute \<beta> p)"
    and mat: "\<And>s M. (s,M) |\<in>| finite_schema_materials ?S \<Longrightarrow>
        Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G \<or> resolution_material_done \<beta> M"
    using linked unfolding resolution_node_linked_def by blast
  have clause: "((resolution_node_site nd,resolution_node_clause nd),?S) |\<in>| finite_system_clauses P"
    using linked unfolding resolution_node_linked_def by blast
  have bind_mem: "\<And>b y. (b,y) |\<in>| resolution_node_bindings nd \<longleftrightarrow> b |\<in>| finite_schema_variables ?S \<and> y = \<beta> b"
    unfolding bind by auto
  have B_mem: "\<And>b v. (b,v) |\<in>| ?B \<longleftrightarrow> b |\<in>| finite_schema_variables ?S \<and>
      finite_pattern_variables (\<beta> b) = {||} \<and> v = finite_residual_term (\<beta> b)"
    unfolding finite_node_ground_bindings_def bind by (auto simp: resolution_fset_simps)
  have B_fun: "finite_relation_functional ?B"
    unfolding finite_relation_functional_correct single_valued_def by (auto simp: B_mem)
  have B_val: "\<And>b. b |\<in>| finite_schema_variables ?S \<Longrightarrow> finite_pattern_variables (\<beta> b) = {||} \<Longrightarrow>
      finite_binding_valuation ?B b = finite_residual_term (\<beta> b)"
    using finite_binding_valuation_member[OF B_fun] B_mem by blast
  have B_formed: "fBall ?B (\<lambda>(b,t). finite_term_formed t)"
  proof
    fix z assume "z |\<in>| ?B"
    then obtain b v where z: "z = (b,v)" "(b,v) |\<in>| ?B" by (cases z) auto
    then have "b |\<in>| finite_schema_variables ?S" "v = finite_residual_term (\<beta> b)" using B_mem by blast+
    then have "finite_pattern_formed (\<beta> b)" using bformed bind_mem by blast
    then show "case z of (b,t) \<Rightarrow> finite_term_formed t" using z \<open>v = finite_residual_term (\<beta> b)\<close> by simp
  qed
  text \<open>The step's substitution evaluates at @{term \<theta>'} to @{term \<theta>'} itself.\<close>
  have \<sigma>_val: "\<And>z. resolution_value \<theta>' (?\<sigma> z) = \<theta>' z"
  proof -
    fix z :: "('b list \<times> bool) \<times> 'a"
    obtain q b a where z: "z = ((q,b),a)" by (cases z) auto
    show "resolution_value \<theta>' (?\<sigma> z) = \<theta>' z"
    proof (cases "b \<and> q = ?pos \<and> a |\<in>| ?C")
      case True
      then obtain v where v: "finite_registered_value \<kappa> P nd a = Some v"
        unfolding finite_constructed_def by auto
      then show ?thesis using True z
        by (simp add: finite_construction_substitution_def \<theta>'_def resolution_value_ground)
    next
      case False
      then show ?thesis using z by (auto simp: finite_construction_substitution_def \<theta>'_def)
    qed
  qed
  have val_step: "\<And>p. resolution_value \<theta>' (finite_pattern_substitute ?\<sigma> p) = resolution_value \<theta>' p"
    by (simp add: resolution_value_instance \<sigma>_val)
  have mat_step: "\<And>M. finite_material_pattern_substitute (resolution_substitution \<theta>') (finite_material_pattern_substitute ?\<sigma> M) =
      finite_material_pattern_substitute (resolution_substitution \<theta>') M"
    by (simp add: finite_material_pattern_substitute_composes resolution_value_substitute \<sigma>_val)
  text \<open>At a constructed variable, the premises holding it are its goals, and completeness carries their truth.\<close>
  have constructed: "\<And>a. a |\<in>| ?C \<Longrightarrow>
      (\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow> a |\<in>| finite_pattern_variables p \<longrightarrow>
        Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G \<and>
        (e,decode_finite_term (resolution_value \<theta>' (finite_pattern_substitute \<beta> p))) \<in>
          positive_meaning (decode_finite_system P)) \<and>
      (\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow> a |\<in>| finite_material_variables M \<longrightarrow>
        Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G \<and>
        finite_material_ground_satisfied
          (finite_material_pattern_substitute (resolution_substitution \<theta>') (finite_material_pattern_substitute \<beta> M)))"
  proof -
    fix a assume aC: "a |\<in>| ?C"
    have free: "a |\<in>| finite_free_registered \<kappa> nd" and ready: "finite_registration_ready ?G nd a"
      and some: "finite_registered_value \<kappa> P nd a \<noteq> None"
      using aC unfolding finite_constructed_def by auto
    obtain v where v: "finite_registered_value \<kappa> P nd a = Some v" using some by auto
    have reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) ?S"
      and xbind: "(a,Finite_Variable (?x a)) |\<in>| resolution_node_bindings nd"
      using free unfolding finite_free_registered_def by auto
    have \<beta>a: "\<beta> a = Finite_Variable (?x a)" and aS: "a |\<in>| finite_schema_variables ?S"
      using xbind by (simp_all add: bind_mem)
    have cS: "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S) \<and>
        finite_value_complete P ?S a (\<lambda>B. witness_value \<kappa> P (resolution_node_site nd) ?S B a)"
      using complete clause reg unfolding finite_construction_complete_def by blast
    have xstate: "?x a \<in> resolution_state_variables st"
      using resolution_state_variables_binding[OF nd xbind] by simp
    have held: "resolution_variable_held st nd a"
      using resolution_registrations_heldD(2)[OF H nd reg] cS xstate by blast
    have \<theta>'x: "\<theta>' (?x a) = v" using aC v by (simp add: \<theta>'_def)
    have ready_vars: "\<And>g. g |\<in>| ?G \<Longrightarrow> ?x a |\<in>| resolution_goal_variables g \<Longrightarrow>
        resolution_goal_variables g |\<subseteq>| {|?x a|}"
      using ready unfolding finite_registration_ready_def Let_def finite_goal_holders_def by auto
    have holders: "\<exists>g. g |\<in>| ?G \<and> ?x a |\<in>| resolution_goal_variables g"
      using ready unfolding finite_registration_ready_def Let_def finite_goal_holders_def by auto
    text \<open>Each premise holding a is a pending goal, and its other variables are ground.\<close>
    have call_pending: "\<And>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<Longrightarrow> a |\<in>| finite_pattern_variables p \<Longrightarrow>
        Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G"
    proof -
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      have xp: "?x a |\<in>| finite_pattern_variables (finite_pattern_substitute \<beta> p)"
        using finite_substitute_variables_subset[OF ap, of \<beta>] \<beta>a by auto
      have "\<not> (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m = ?pos@[s] \<and>
          resolution_node_site m = e \<and> resolution_node_call m = finite_pattern_substitute \<beta> p)"
        using resolution_variable_heldD(2)[OF held] xp by metis
      then show "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G" using prem[OF sp] by blast
    qed
    have mat_pending: "\<And>s M. (s,M) |\<in>| finite_schema_materials ?S \<Longrightarrow> a |\<in>| finite_material_variables M \<Longrightarrow>
        Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G"
    proof -
      fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      have "\<not> resolution_material_done \<beta> M"
        using aM \<beta>a unfolding resolution_material_done_def by auto
      then show "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G" using mat[OF sM] by blast
    qed
    have ground: "\<And>b q. q |\<in>| ?G \<Longrightarrow> ?x a |\<in>| resolution_goal_variables q \<Longrightarrow>
        (\<forall>w. w |\<in>| resolution_goal_variables q \<longrightarrow> w = ?x a)" using ready_vars by blast
    have call_ground: "\<And>s e p b. (s,e,p) |\<in>| finite_schema_premises ?S \<Longrightarrow> a |\<in>| finite_pattern_variables p \<Longrightarrow>
        b |\<in>| finite_pattern_variables p \<Longrightarrow> b \<noteq> a \<Longrightarrow> finite_pattern_variables (\<beta> b) = {||}"
    proof -
      fix s e p b assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
        and bp: "b |\<in>| finite_pattern_variables p" and ba: "b \<noteq> a"
      let ?g = "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p)"
      have gG: "?g |\<in>| ?G" by (rule call_pending[OF sp ap])
      have xg: "?x a |\<in>| resolution_goal_variables ?g"
        using finite_substitute_variables_subset[OF ap, of \<beta>] \<beta>a by auto
      have sub: "finite_pattern_variables (\<beta> b) |\<subseteq>| {|?x a|}"
        using ready_vars[OF gG xg] finite_substitute_variables_subset[OF bp, of \<beta>] by auto
      have "?x a |\<notin>| finite_pattern_variables (\<beta> b)"
        using resolution_variable_heldD(3)[OF held, of b "\<beta> b"] bind_mem ba finite_schema_variables_members(2)[OF sp bp]
        by blast
      then show "finite_pattern_variables (\<beta> b) = {||}" using sub by blast
    qed
    have mat_ground: "\<And>s M b. (s,M) |\<in>| finite_schema_materials ?S \<Longrightarrow> a |\<in>| finite_material_variables M \<Longrightarrow>
        b |\<in>| finite_material_variables M \<Longrightarrow> b \<noteq> a \<Longrightarrow> finite_pattern_variables (\<beta> b) = {||}"
    proof -
      fix s M b assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
        and bM: "b |\<in>| finite_material_variables M" and ba: "b \<noteq> a"
      let ?g = "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M)"
      have gG: "?g |\<in>| ?G" by (rule mat_pending[OF sM aM])
      have xg: "?x a |\<in>| resolution_goal_variables ?g"
        using finite_material_substitute_variables_subset[OF aM, of \<beta>] \<beta>a by auto
      have sub: "finite_pattern_variables (\<beta> b) |\<subseteq>| {|?x a|}"
        using ready_vars[OF gG xg] finite_material_substitute_variables_subset[OF bM, of \<beta>] by auto
      have "?x a |\<notin>| finite_pattern_variables (\<beta> b)"
        using resolution_variable_heldD(3)[OF held, of b "\<beta> b"] bind_mem ba finite_schema_variables_members(3)[OF sM bM]
        by blast
      then show "finite_pattern_variables (\<beta> b) = {||}" using sub by blast
    qed
    text \<open>Values at the node's ground bindings.\<close>
    have conv: "\<And>\<theta>'' s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<Longrightarrow> a |\<in>| finite_pattern_variables p \<Longrightarrow>
        resolution_value \<theta>'' (finite_pattern_substitute \<beta> p) =
        resolution_value ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) p"
    proof -
      fix \<theta>'' s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      show "resolution_value \<theta>'' (finite_pattern_substitute \<beta> p) =
          resolution_value ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) p"
        unfolding resolution_value_instance
      proof (rule resolution_value_cong)
        fix b assume bp: "b |\<in>| finite_pattern_variables p"
        show "resolution_value \<theta>'' (\<beta> b) = ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) b"
        proof (cases "b = a")
          case True then show ?thesis using \<beta>a by simp
        next
          case False
          have g: "finite_pattern_variables (\<beta> b) = {||}" by (rule call_ground[OF sp ap bp False])
          then show ?thesis using False B_val[OF finite_schema_variables_members(2)[OF sp bp] g]
            by (simp add: resolution_value_ground_residual)
        qed
      qed
    qed
    have fconv: "\<And>\<theta>'' s M f. (s,M) |\<in>| finite_schema_materials ?S \<Longrightarrow> a |\<in>| finite_material_variables M \<Longrightarrow>
        finite_pattern_variables f |\<subseteq>| finite_material_variables M \<Longrightarrow>
        resolution_value \<theta>'' (finite_pattern_substitute \<beta> f) =
        resolution_value ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) f"
    proof -
      fix \<theta>'' s M f assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
        and fM: "finite_pattern_variables f |\<subseteq>| finite_material_variables M"
      show "resolution_value \<theta>'' (finite_pattern_substitute \<beta> f) =
          resolution_value ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) f"
        unfolding resolution_value_instance
      proof (rule resolution_value_cong)
        fix b assume "b |\<in>| finite_pattern_variables f"
        then have bM: "b |\<in>| finite_material_variables M" using fM by blast
        show "resolution_value \<theta>'' (\<beta> b) = ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) b"
        proof (cases "b = a")
          case True then show ?thesis using \<beta>a by simp
        next
          case False
          have g: "finite_pattern_variables (\<beta> b) = {||}" by (rule mat_ground[OF sM aM bM False])
          then show ?thesis using False B_val[OF finite_schema_variables_members(3)[OF sM bM] g]
            by (simp add: resolution_value_ground_residual)
        qed
      qed
    qed
    have mconv: "\<And>\<theta>'' s M. (s,M) |\<in>| finite_schema_materials ?S \<Longrightarrow> a |\<in>| finite_material_variables M \<Longrightarrow>
        finite_material_ground_satisfied
          (finite_material_pattern_substitute (resolution_substitution \<theta>'') (finite_material_pattern_substitute \<beta> M)) \<longleftrightarrow>
        finite_material_ground_satisfied (finite_material_pattern_substitute
          (resolution_substitution ((finite_binding_valuation ?B)(a := \<theta>'' (?x a)))) M)"
    proof -
      fix \<theta>'' s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      have f: "\<And>f. finite_pattern_variables f |\<subseteq>| finite_material_variables M \<Longrightarrow>
          resolution_value \<theta>'' (finite_pattern_substitute \<beta> f) =
          resolution_value ((finite_binding_valuation ?B)(a := \<theta>'' (?x a))) f"
        by (rule fconv[OF sM aM])
      have fields: "finite_pattern_variables (finite_material_source M) |\<subseteq>| finite_material_variables M"
        "finite_pattern_variables (finite_material_atoms M) |\<subseteq>| finite_material_variables M"
        "finite_pattern_variables (finite_material_edges M) |\<subseteq>| finite_material_variables M"
        "finite_pattern_variables (finite_material_counts M) |\<subseteq>| finite_material_variables M"
        "finite_pattern_variables (finite_material_functions M) |\<subseteq>| finite_material_variables M"
        by (auto simp: finite_material_variables_def)
      show "finite_material_ground_satisfied
          (finite_material_pattern_substitute (resolution_substitution \<theta>'') (finite_material_pattern_substitute \<beta> M)) \<longleftrightarrow>
        finite_material_ground_satisfied (finite_material_pattern_substitute
          (resolution_substitution ((finite_binding_valuation ?B)(a := \<theta>'' (?x a)))) M)"
        by (simp only: finite_material_ground_satisfied_values finite_material_pattern_substitute_fields
          f[OF fields(1)] f[OF fields(2)] f[OF fields(3)] f[OF fields(4)] f[OF fields(5)])
    qed
    text \<open>The support's value of x is formed, and the premises hold at it.\<close>
    have sup_call: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| ?G \<Longrightarrow> resolution_focused F q \<Longrightarrow>
        (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
      using sup unfolding resolution_supported_at_def by blast
    have sup_mat: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| ?G \<Longrightarrow> resolution_focused F q \<Longrightarrow>
        finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
      using sup unfolding resolution_supported_at_def by blast
    have fchild: "\<And>s. resolution_focused F (?pos@[s])" by (rule resolution_focused_child[OF focus])
    have at_theta: "finite_variable_premises_hold P ?S a ((finite_binding_valuation ?B)(a := \<theta> (?x a)))"
      unfolding finite_variable_premises_hold_def
    proof (intro conjI allI impI)
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      have "(e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p))) \<in>
          positive_meaning (decode_finite_system P)" by (rule sup_call[OF call_pending[OF sp ap] fchild])
      then show "(e,decode_finite_term (resolution_value ((finite_binding_valuation ?B)(a := \<theta> (?x a))) p)) \<in>
          positive_meaning (decode_finite_system P)" using conv[OF sp ap, of \<theta>] by simp
    next
      fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
          (finite_material_pattern_substitute \<beta> M))" by (rule sup_mat[OF mat_pending[OF sM aM] fchild])
      then show "finite_material_ground_satisfied (finite_material_pattern_substitute
          (resolution_substitution ((finite_binding_valuation ?B)(a := \<theta> (?x a)))) M)"
        using mconv[OF sM aM, of \<theta>] by simp
    qed
    have w_formed: "finite_term_formed (\<theta> (?x a))"
    proof -
      obtain g where g: "g |\<in>| ?G" "?x a |\<in>| resolution_goal_variables g" using holders by blast
      obtain s where "resolution_registered_premise ?S s a"
        using resolution_variable_heldD(4)[OF held g] by blast
      then show ?thesis unfolding resolution_registered_premise_def
      proof (elim disjE exE conjE)
        fix e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
        have tr: "(e,decode_finite_term (resolution_value \<theta> (finite_pattern_substitute \<beta> p))) \<in>
            positive_meaning (decode_finite_system P)" by (rule sup_call[OF call_pending[OF sp ap] fchild])
        have "finite_term_formed (resolution_value \<theta> (finite_pattern_substitute \<beta> p))"
          using positive_meaning_formed[OF tr]
          by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
        moreover have "?x a |\<in>| finite_pattern_variables (finite_pattern_substitute \<beta> p)"
          using finite_substitute_variables_subset[OF ap, of \<beta>] \<beta>a by auto
        ultimately show ?thesis by (rule resolution_value_variable_formed)
      next
        fix M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
        have sat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>)
            (finite_material_pattern_substitute \<beta> M))" by (rule sup_mat[OF mat_pending[OF sM aM] fchild])
        moreover have "?x a |\<in>| finite_material_variables (finite_material_pattern_substitute \<beta> M)"
          using finite_material_substitute_variables_subset[OF aM, of \<beta>] \<beta>a by auto
        ultimately show ?thesis by (rule finite_material_satisfied_variable_formed)
      qed
    qed
    text \<open>Completeness carries the premises to the constructed value.\<close>
    have B_free: "a |\<notin>| fimage fst ?B"
    proof
      assume "a |\<in>| fimage fst ?B"
      then obtain t where "(a,t) |\<in>| ?B" by auto
      then show False using B_mem \<beta>a by simp
    qed
    have B_bound: "finite_variable_premises_bound ?S a (fimage fst ?B)"
      unfolding finite_variable_premises_bound_def
    proof (intro conjI allI impI)
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      show "finite_pattern_variables p |\<subseteq>| finsert a (fimage fst ?B)"
      proof
        fix b assume bp: "b |\<in>| finite_pattern_variables p"
        show "b |\<in>| finsert a (fimage fst ?B)"
        proof (cases "b = a")
          case False
          have "(b,finite_residual_term (\<beta> b)) |\<in>| ?B"
            using B_mem finite_schema_variables_members(2)[OF sp bp] call_ground[OF sp ap bp False] by blast
          then show ?thesis by (auto intro: fimageI[where f=fst, of "(b,finite_residual_term (\<beta> b))", simplified])
        qed simp
      qed
    next
      fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      show "finite_material_variables M |\<subseteq>| finsert a (fimage fst ?B)"
      proof
        fix b assume bM: "b |\<in>| finite_material_variables M"
        show "b |\<in>| finsert a (fimage fst ?B)"
        proof (cases "b = a")
          case False
          have "(b,finite_residual_term (\<beta> b)) |\<in>| ?B"
            using B_mem finite_schema_variables_members(3)[OF sM bM] mat_ground[OF sM aM bM False] by blast
          then show ?thesis by (auto intro: fimageI[where f=fst, of "(b,finite_residual_term (\<beta> b))", simplified])
        qed simp
      qed
    qed
    have wv: "witness_value \<kappa> P (resolution_node_site nd) ?S ?B a = Some v"
      using v unfolding finite_registered_value_def .
    have at_v: "finite_variable_premises_hold P ?S a ((finite_binding_valuation ?B)(a := v))"
      using cS B_fun B_formed B_free B_bound wv at_theta w_formed unfolding finite_value_complete_def by blast
    show "(\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow> a |\<in>| finite_pattern_variables p \<longrightarrow>
        Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G \<and>
        (e,decode_finite_term (resolution_value \<theta>' (finite_pattern_substitute \<beta> p))) \<in>
          positive_meaning (decode_finite_system P)) \<and>
      (\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow> a |\<in>| finite_material_variables M \<longrightarrow>
        Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G \<and>
        finite_material_ground_satisfied
          (finite_material_pattern_substitute (resolution_substitution \<theta>') (finite_material_pattern_substitute \<beta> M)))"
    proof (intro conjI allI impI)
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      show "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G" by (rule call_pending[OF sp ap])
      have "(e,decode_finite_term (resolution_value ((finite_binding_valuation ?B)(a := v)) p)) \<in>
          positive_meaning (decode_finite_system P)"
        using at_v sp ap unfolding finite_variable_premises_hold_def by blast
      then show "(e,decode_finite_term (resolution_value \<theta>' (finite_pattern_substitute \<beta> p))) \<in>
          positive_meaning (decode_finite_system P)" using conv[OF sp ap, of \<theta>'] \<theta>'x by simp
    next
      fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      show "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G" by (rule mat_pending[OF sM aM])
      have "finite_material_ground_satisfied (finite_material_pattern_substitute
          (resolution_substitution ((finite_binding_valuation ?B)(a := v))) M)"
        using at_v sM aM unfolding finite_variable_premises_hold_def by blast
      then show "finite_material_ground_satisfied
          (finite_material_pattern_substitute (resolution_substitution \<theta>') (finite_material_pattern_substitute \<beta> M))"
        using mconv[OF sM aM, of \<theta>'] \<theta>'x by simp
    qed
  qed
  text \<open>The successor: every goal holding a constructed variable is a premise goal the step made true.\<close>
  have held_C: "\<And>a. a |\<in>| ?C \<Longrightarrow> resolution_variable_held st nd a"
  proof -
    fix a assume aC: "a |\<in>| ?C"
    have free: "a |\<in>| finite_free_registered \<kappa> nd" using aC unfolding finite_constructed_def by auto
    have reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) ?S"
      and xbind: "(a,Finite_Variable (?x a)) |\<in>| resolution_node_bindings nd"
      using free unfolding finite_free_registered_def by auto
    have "a |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
      using complete clause reg unfolding finite_construction_complete_def by blast
    moreover have "?x a \<in> resolution_state_variables st"
      using resolution_state_variables_binding[OF nd xbind] by simp
    ultimately show "resolution_variable_held st nd a"
      using resolution_registrations_heldD(2)[OF H nd reg] by blast
  qed
  have dist_goals: "\<And>g h. g |\<in>| ?G \<Longrightarrow> h |\<in>| ?G \<Longrightarrow> resolution_goal_position g = resolution_goal_position h \<Longrightarrow> g = h"
    using distinct unfolding resolution_positions_distinct_def by blast
  have holder: "\<And>a g0. a |\<in>| ?C \<Longrightarrow> g0 |\<in>| ?G \<Longrightarrow> ?x a |\<in>| resolution_goal_variables g0 \<Longrightarrow>
      (\<exists>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<and> a |\<in>| finite_pattern_variables p \<and>
        g0 = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p)) \<or>
      (\<exists>s M. (s,M) |\<in>| finite_schema_materials ?S \<and> a |\<in>| finite_material_variables M \<and>
        g0 = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M))"
  proof -
    fix a g0 assume aC: "a |\<in>| ?C" and g0G: "g0 |\<in>| ?G" and xg: "?x a |\<in>| resolution_goal_variables g0"
    obtain s where pos: "resolution_goal_position g0 = ?pos@[s]" and rp: "resolution_registered_premise ?S s a"
      using resolution_variable_heldD(4)[OF held_C[OF aC] g0G xg] by blast
    from rp show "?thesis a g0" unfolding resolution_registered_premise_def
    proof (elim disjE exE conjE)
      fix e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p"
      have gG: "Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p) |\<in>| ?G" using constructed[OF aC] sp ap by blast
      have "g0 = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
          (finite_pattern_substitute \<beta> p)" using dist_goals[OF g0G gG] pos by simp
      then show ?thesis using sp ap by blast
    next
      fix M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
      have gG: "Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M) |\<in>| ?G" using constructed[OF aC] sM aM by blast
      have "g0 = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
          (finite_material_pattern_substitute \<beta> M)" using dist_goals[OF g0G gG] pos by simp
      then show ?thesis using sM aM by blast
    qed
  qed
  have agree: "\<And>p. (\<And>a. a |\<in>| ?C \<Longrightarrow> ?x a |\<notin>| finite_pattern_variables p) \<Longrightarrow>
      resolution_value \<theta>' p = resolution_value \<theta> p"
  proof -
    fix p assume no: "\<And>a. a |\<in>| ?C \<Longrightarrow> ?x a |\<notin>| finite_pattern_variables p"
    show "resolution_value \<theta>' p = resolution_value \<theta> p"
    proof (rule resolution_value_cong)
      fix z assume zp: "z |\<in>| finite_pattern_variables p"
      obtain w a where z: "z = (w,a)" by (cases z)
      show "\<theta>' z = \<theta> z"
      proof (cases "w = (?pos,True) \<and> a |\<in>| ?C")
        case True then show ?thesis using no zp z by auto
      next
        case False then show ?thesis using z by (auto simp: \<theta>'_def)
      qed
    qed
  qed
  have magree: "\<And>M. (\<And>a. a |\<in>| ?C \<Longrightarrow> ?x a |\<notin>| finite_material_variables M) \<Longrightarrow>
      finite_material_pattern_substitute (resolution_substitution \<theta>') M =
      finite_material_pattern_substitute (resolution_substitution \<theta>) M"
  proof -
    fix M assume no: "\<And>a. a |\<in>| ?C \<Longrightarrow> ?x a |\<notin>| finite_material_variables M"
    show "finite_material_pattern_substitute (resolution_substitution \<theta>') M =
        finite_material_pattern_substitute (resolution_substitution \<theta>) M"
    proof (rule finite_material_pattern_substitute_cong)
      fix z assume zM: "z |\<in>| finite_material_variables M"
      obtain w a where z: "z = (w,a)" by (cases z)
      have "\<theta>' z = \<theta> z"
      proof (cases "w = (?pos,True) \<and> a |\<in>| ?C")
        case True then show ?thesis using no zM z by auto
      next
        case False then show ?thesis using z by (auto simp: \<theta>'_def)
      qed
      then show "resolution_substitution \<theta>' z = resolution_substitution \<theta> z" by simp
    qed
  qed
  have sup_call: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| ?G \<Longrightarrow> resolution_focused F q \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
    using sup unfolding resolution_supported_at_def by blast
  have sup_mat: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| ?G \<Longrightarrow> resolution_focused F q \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    using sup unfolding resolution_supported_at_def by blast
  have sup_goal_placed: "\<And>g z. g |\<in>| ?G \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> U z"
    using sup unfolding resolution_supported_at_def by blast
  have sup_node_placed: "\<And>n z. n |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call n) \<Longrightarrow>
      resolution_placed st z \<or> U z"
    using sup unfolding resolution_supported_at_def by blast
  have placed_step: "\<And>z. resolution_placed (resolution_state_substitute ?\<sigma> st0) z \<longleftrightarrow> resolution_placed st z"
    by (auto simp: resolution_placed_substitute st0_def resolution_placed_def)
  have pending_step: "\<And>g'. g' |\<in>| resolution_pending (resolution_state_substitute ?\<sigma> st0) \<Longrightarrow>
      \<exists>g0. g0 |\<in>| ?G \<and> g' = resolution_goal_substitute ?\<sigma> g0"
    by (auto simp: st0_def)
  have barred: "\<And>n. n |\<in>| resolution_nodes (resolution_state_substitute ?\<sigma> st0) \<Longrightarrow>
      resolution_node_position n |\<in>| B |\<union>| fimage resolution_node_position (resolution_nodes st)"
  proof -
    fix n assume "n |\<in>| resolution_nodes (resolution_state_substitute ?\<sigma> st0)"
    then obtain n0 where "n0 |\<in>| resolution_nodes st" "n = resolution_node_substitute ?\<sigma> n0" by (auto simp: st0_def)
    then show "resolution_node_position n |\<in>| B |\<union>| fimage resolution_node_position (resolution_nodes st)" by auto
  qed
  have "resolution_supported_at U F (B |\<union>| fimage resolution_node_position (resolution_nodes st)) P
      (resolution_state_substitute ?\<sigma> st0) \<theta>'"
  proof (rule resolution_supported_atI)
    fix q r e p' assume g': "Resolution_Call_Goal q r e p' |\<in>| resolution_pending (resolution_state_substitute ?\<sigma> st0)"
      and fq: "resolution_focused F q"
    obtain g0 where g0: "g0 |\<in>| ?G" "Resolution_Call_Goal q r e p' = resolution_goal_substitute ?\<sigma> g0"
      using pending_step[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal q r e p0" and p': "p' = finite_pattern_substitute ?\<sigma> p0"
      using g0(2)[symmetric] unfolding resolution_goal_substitute_call by blast
    have tru: "(e,decode_finite_term (resolution_value \<theta>' p0)) \<in> positive_meaning (decode_finite_system P)"
    proof (cases "\<exists>a. a |\<in>| ?C \<and> ?x a |\<in>| finite_pattern_variables p0")
      case True
      then obtain a where aC: "a |\<in>| ?C" and xp: "?x a |\<in>| finite_pattern_variables p0" by blast
      have xg: "?x a |\<in>| resolution_goal_variables g0" using xp g0c by simp
      from holder[OF aC g0(1) xg] show ?thesis
      proof (elim disjE exE conjE)
        fix s e1 p1 assume sp: "(s,e1,p1) |\<in>| finite_schema_premises ?S" and ap: "a |\<in>| finite_pattern_variables p1"
          and eq: "g0 = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e1
            (finite_pattern_substitute \<beta> p1)"
        have e: "e = e1" and p0: "p0 = finite_pattern_substitute \<beta> p1" using eq g0c by simp_all
        show ?thesis using constructed[OF aC] sp ap e p0 by blast
      next
        fix s M assume "g0 = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
            (finite_material_pattern_substitute \<beta> M)"
        then show ?thesis using g0c by simp
      qed
    next
      case False
      then have "resolution_value \<theta>' p0 = resolution_value \<theta> p0" using agree by blast
      moreover have "(e,decode_finite_term (resolution_value \<theta> p0)) \<in> positive_meaning (decode_finite_system P)"
        using sup_call[OF g0(1)[unfolded g0c] fq] .
      ultimately show ?thesis by simp
    qed
    show "(e,decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd'. nd' |\<in>| resolution_nodes (resolution_state_substitute ?\<sigma> st0) \<longrightarrow>
        resolution_node_position nd' |\<notin>| B |\<union>| fimage resolution_node_position (resolution_nodes st) \<longrightarrow>
        resolution_before (resolution_node_position nd') q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta>' p')) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd',decode_finite_term (resolution_value \<theta>' (resolution_node_call nd'))))"
      using tru p' val_step barred by simp
  next
    fix q r M' assume g': "Resolution_Material_Goal q r M' |\<in>| resolution_pending (resolution_state_substitute ?\<sigma> st0)"
      and fq: "resolution_focused F q"
    obtain g0 where g0: "g0 |\<in>| ?G" "Resolution_Material_Goal q r M' = resolution_goal_substitute ?\<sigma> g0"
      using pending_step[OF g'] by blast
    obtain M0 where g0c: "g0 = Resolution_Material_Goal q r M0" and M': "M' = finite_material_pattern_substitute ?\<sigma> M0"
      using g0(2)[symmetric] unfolding resolution_goal_substitute_material by blast
    have sat: "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>') M0)"
    proof (cases "\<exists>a. a |\<in>| ?C \<and> ?x a |\<in>| finite_material_variables M0")
      case True
      then obtain a where aC: "a |\<in>| ?C" and xM: "?x a |\<in>| finite_material_variables M0" by blast
      have xg: "?x a |\<in>| resolution_goal_variables g0" using xM g0c by simp
      from holder[OF aC g0(1) xg] show ?thesis
      proof (elim disjE exE conjE)
        fix s e1 p1 assume "g0 = Resolution_Call_Goal (?pos@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e1
            (finite_pattern_substitute \<beta> p1)"
        then show ?thesis using g0c by simp
      next
        fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S" and aM: "a |\<in>| finite_material_variables M"
          and eq: "g0 = Resolution_Material_Goal (?pos@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
            (finite_material_pattern_substitute \<beta> M)"
        have "M0 = finite_material_pattern_substitute \<beta> M" using eq g0c by simp
        then show ?thesis using constructed[OF aC] sM aM by blast
      qed
    next
      case False
      then have "finite_material_pattern_substitute (resolution_substitution \<theta>') M0 =
          finite_material_pattern_substitute (resolution_substitution \<theta>) M0" using magree by blast
      moreover have "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M0)"
        using sup_mat[OF g0(1)[unfolded g0c] fq] .
      ultimately show ?thesis by simp
    qed
    have "finite_material_pattern_substitute (resolution_substitution \<theta>') M' =
        finite_material_pattern_substitute (resolution_substitution \<theta>') M0"
      unfolding M' by (rule mat_step)
    then show "finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>') M')"
      using sat by simp
  next
    fix g' z assume g': "g' |\<in>| resolution_pending (resolution_state_substitute ?\<sigma> st0)"
      and z: "z |\<in>| resolution_goal_variables g'"
    obtain g0 where g0: "g0 |\<in>| ?G" "g' = resolution_goal_substitute ?\<sigma> g0" using pending_step[OF g'] by blast
    obtain y where y: "y |\<in>| resolution_goal_variables g0" "z |\<in>| finite_pattern_variables (?\<sigma> y)"
      using resolution_goal_substitute_variable_origin[of z ?\<sigma> g0] z g0(2) by blast
    have "z = y" using finite_construction_substitution_variables[OF y(2)] by simp
    then show "resolution_placed (resolution_state_substitute ?\<sigma> st0) z \<or> U z"
      using sup_goal_placed[OF g0(1)] y(1) placed_step by blast
  next
    fix n z assume n: "n |\<in>| resolution_nodes (resolution_state_substitute ?\<sigma> st0)"
      and z: "z |\<in>| finite_pattern_variables (resolution_node_call n)"
    obtain n0 where n0: "n0 |\<in>| resolution_nodes st" "n = resolution_node_substitute ?\<sigma> n0" using n by (auto simp: st0_def)
    have "z |\<in>| finite_pattern_variables (finite_pattern_substitute ?\<sigma> (resolution_node_call n0))" using z n0(2) by simp
    from finite_substitute_variable_origin[OF this]
    obtain y where y: "y |\<in>| finite_pattern_variables (resolution_node_call n0)" "z |\<in>| finite_pattern_variables (?\<sigma> y)"
      by blast
    have "z = y" using finite_construction_substitution_variables[OF y(2)] by simp
    then show "resolution_placed (resolution_state_substitute ?\<sigma> st0) z \<or> U z"
      using sup_node_placed[OF n0(1)] y(1) placed_step by blast
  qed
  then show ?thesis unfolding step finite_committed_barring_def by blast
qed

section \<open>Relocation by a placement of definitions\<close>

text \<open>
  A construction over a program P is relocated by a map g of its definitions: at the relocated program it registers,
  at the site g d and the schema with its callees relocated, the variables it registers at the clause of P they come
  from, and its value there is its value at that clause of P. The value is produced over P, on the producing side;
  the relocated program's clauses check it. Its completeness is carried by the relocation of the positive meaning
  (@{thm [source] renamed_system_positive_meaning}), g injective on P's definitions.
\<close>

definition finite_relocated_construction ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'e,'c) finite_witness_construction" where
  "finite_relocated_construction g P \<kappa> = \<lparr>
    witness_registered = (\<lambda>e T. ffUnion (fimage (\<lambda>((d,c),S). if g d = e \<and> finite_rename_schema id id g S = T
      then witness_registered \<kappa> d S else {||}) (finite_system_clauses P))),
    witness_value = (\<lambda>Q e T B a. let Vs = fimage (\<lambda>((d,c),S). witness_value \<kappa> P d S B a)
        (ffilter (\<lambda>((d,c),S). g d = e \<and> finite_rename_schema id id g S = T \<and> a |\<in>| witness_registered \<kappa> d S)
          (finite_system_clauses P)) in
      if Vs = {|fthe_elem Vs|} then fthe_elem Vs else None)\<rparr>"

lemma finite_relocated_construction_registered:
  "a |\<in>| witness_registered (finite_relocated_construction g P \<kappa>) e T \<longleftrightarrow>
    (\<exists>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<and> g d = e \<and> finite_rename_schema id id g S = T \<and>
      a |\<in>| witness_registered \<kappa> d S)"
proof
  assume "a |\<in>| witness_registered (finite_relocated_construction g P \<kappa>) e T"
  then show "\<exists>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<and> g d = e \<and> finite_rename_schema id id g S = T \<and>
      a |\<in>| witness_registered \<kappa> d S"
    by (auto simp: finite_relocated_construction_def resolution_fset_simps split: if_splits) blast
next
  assume "\<exists>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<and> g d = e \<and> finite_rename_schema id id g S = T \<and>
      a |\<in>| witness_registered \<kappa> d S"
  then obtain d c S where S: "((d,c),S) |\<in>| finite_system_clauses P" "g d = e" "finite_rename_schema id id g S = T"
    "a |\<in>| witness_registered \<kappa> d S" by blast
  show "a |\<in>| witness_registered (finite_relocated_construction g P \<kappa>) e T"
    using S by (force simp: finite_relocated_construction_def resolution_fset_simps)
qed

lemma finite_relocated_construction_value:
  assumes "witness_value (finite_relocated_construction g P \<kappa>) Q e T B a = Some v"
  shows "\<exists>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<and> g d = e \<and> finite_rename_schema id id g S = T \<and>
    a |\<in>| witness_registered \<kappa> d S \<and> witness_value \<kappa> P d S B a = Some v"
proof -
  define Vs where "Vs = fimage (\<lambda>((d,c),S). witness_value \<kappa> P d S B a)
      (ffilter (\<lambda>((d,c),S). g d = e \<and> finite_rename_schema id id g S = T \<and> a |\<in>| witness_registered \<kappa> d S)
        (finite_system_clauses P))"
  have single: "Vs = {|fthe_elem Vs|}" and elem: "fthe_elem Vs = Some v"
    using assms by (simp_all add: finite_relocated_construction_def Vs_def[symmetric] Let_def split: if_splits)
  have "Some v |\<in>| Vs" using single elem by (metis finsertI1)
  then show ?thesis unfolding Vs_def by (auto simp: resolution_fset_simps) blast
qed

lemma finite_relocated_construction_formed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_witness_construction_formed (finite_relocated_construction g P \<kappa>)"
  unfolding finite_witness_construction_formed_def
proof (intro allI impI)
  fix Q e T B a v assume "witness_value (finite_relocated_construction g P \<kappa>) Q e T B a = Some v"
  from finite_relocated_construction_value[OF this] obtain d S where "witness_value \<kappa> P d S B a = Some v" by blast
  then show "finite_term_formed v" using \<kappa> unfolding finite_witness_construction_formed_def by blast
qed

text \<open>A premise's callee is a definition of a formed program; relocation keeps the meaning there.\<close>

lemma finite_clause_callee_definition:
  assumes formed: "finite_system_formed P" and clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and premise: "(s,e,p) |\<in>| finite_schema_premises S"
  shows "e \<in> system_definitions (decode_finite_system P)"
proof -
  from formed have "fBall (finite_system_clauses P) (\<lambda>((d,c),S). d |\<in>| finite_system_definitions P \<and>
      finite_schema_formed S \<and> finite_schema_dependencies S |\<subseteq>| finite_system_definitions P)"
    by (simp add: finite_system_formed_def)
  from fbspec[OF this clause] have dep: "finite_schema_dependencies S |\<subseteq>| finite_system_definitions P" by simp
  have "e |\<in>| finite_system_definitions P"
    using premise dep by (force simp: finite_schema_dependencies_def less_eq_fset.rep_eq resolution_fset_simps)
  then show ?thesis by (simp add: finite_system_definitions_correct[symmetric])
qed

lemma renamed_meaning_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "e \<in> system_definitions P"
  shows "(g e,x) \<in> positive_meaning (rename_system g P) \<longleftrightarrow> (e,x) \<in> positive_meaning P"
proof -
  have PM: "positive_meaning (rename_system g P) = map_prod g id ` positive_meaning P"
    by (rule renamed_system_positive_meaning[OF formed injective])
  have "(g e,x) \<in> map_prod g id ` positive_meaning P \<longleftrightarrow> (e,x) \<in> positive_meaning P"
  proof
    assume "(g e,x) \<in> map_prod g id ` positive_meaning P"
    then obtain e0 where e0: "(e0,x) \<in> positive_meaning P" "g e0 = g e" by auto
    have "e0 \<in> system_definitions P"
      using positive_meaning_formed[OF e0(1)] by (auto simp: schema_call_formed_def system_definitions_def rel_dom_def)
    then have "e0 = e" using inj_onD[OF injective e0(2)] member by simp
    then show "(e,x) \<in> positive_meaning P" using e0(1) by simp
  qed force
  then show ?thesis unfolding PM .
qed

lemma finite_rename_material_id: "finite_rename_material id M = M"
  by (cases M) (simp add: finite_rename_material_def finite_term_pattern.map_id)

lemma finite_rename_schema_premise:
  "(s,e',p) |\<in>| finite_schema_premises (finite_rename_schema id id g S) \<longleftrightarrow>
    (\<exists>e. (s,e,p) |\<in>| finite_schema_premises S \<and> e' = g e)"
  by (force simp: finite_rename_schema_def finite_term_pattern.map_id resolution_fset_simps)

lemma finite_rename_schema_materials:
  "finite_schema_materials (finite_rename_schema id id g S) = finite_schema_materials S"
  by (simp add: finite_rename_schema_def finite_rename_material_id case_prod_unfold)

lemma finite_relocated_premises:
  assumes formed: "finite_system_formed P" and injective: "inj_on g (system_definitions (decode_finite_system P))"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "finite_variable_premises_hold (finite_rename_system g P) (finite_rename_schema id id g S) a \<theta> \<longleftrightarrow>
      finite_variable_premises_hold P S a \<theta>"
    and "finite_variable_premises_bound (finite_rename_schema id id g S) a X \<longleftrightarrow> finite_variable_premises_bound S a X"
proof -
  have Pf: "schema_system_formed (decode_finite_system P)" using formed by (simp add: finite_system_formed_correct)
  have at: "\<And>s e p x. (s,e,p) |\<in>| finite_schema_premises S \<Longrightarrow>
      (g e,x) \<in> positive_meaning (decode_finite_system (finite_rename_system g P)) \<longleftrightarrow>
      (e,x) \<in> positive_meaning (decode_finite_system P)"
    using renamed_meaning_at[OF Pf injective finite_clause_callee_definition[OF formed clause]] by simp
  show "finite_variable_premises_hold (finite_rename_system g P) (finite_rename_schema id id g S) a \<theta> \<longleftrightarrow>
      finite_variable_premises_hold P S a \<theta>"
  proof
    assume H: "finite_variable_premises_hold (finite_rename_system g P) (finite_rename_schema id id g S) a \<theta>"
    show "finite_variable_premises_hold P S a \<theta>"
      unfolding finite_variable_premises_hold_def
    proof (intro conjI allI impI)
      fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises S" and ap: "a |\<in>| finite_pattern_variables p"
      have "(s,g e,p) |\<in>| finite_schema_premises (finite_rename_schema id id g S)"
        using sp by (auto simp: finite_rename_schema_premise)
      then have "(g e,decode_finite_term (resolution_value \<theta> p)) \<in>
          positive_meaning (decode_finite_system (finite_rename_system g P))"
        using H ap unfolding finite_variable_premises_hold_def by blast
      then show "(e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
        using at[OF sp] by simp
    next
      fix s M assume "(s,M) |\<in>| finite_schema_materials S" and "a |\<in>| finite_material_variables M"
      then show "finite_material_ground_satisfied
          (finite_material_pattern_substitute (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'a finite_term_pattern) M)"
        using H unfolding finite_variable_premises_hold_def finite_rename_schema_materials by blast
    qed
  next
    assume H: "finite_variable_premises_hold P S a \<theta>"
    show "finite_variable_premises_hold (finite_rename_system g P) (finite_rename_schema id id g S) a \<theta>"
      unfolding finite_variable_premises_hold_def
    proof (intro conjI allI impI)
      fix s e' p assume sp: "(s,e',p) |\<in>| finite_schema_premises (finite_rename_schema id id g S)"
        and ap: "a |\<in>| finite_pattern_variables p"
      then obtain e where e: "(s,e,p) |\<in>| finite_schema_premises S" "e' = g e"
        by (auto simp: finite_rename_schema_premise)
      have "(e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P)"
        using H ap e(1) unfolding finite_variable_premises_hold_def by blast
      then show "(e',decode_finite_term (resolution_value \<theta> p)) \<in>
          positive_meaning (decode_finite_system (finite_rename_system g P))"
        using at[OF e(1)] e(2) by simp
    next
      fix s M assume "(s,M) |\<in>| finite_schema_materials (finite_rename_schema id id g S)"
        and "a |\<in>| finite_material_variables M"
      then show "finite_material_ground_satisfied
          (finite_material_pattern_substitute (\<lambda>z. finite_exact_term_pattern (\<theta> z) :: 'a finite_term_pattern) M)"
        using H unfolding finite_variable_premises_hold_def finite_rename_schema_materials by blast
    qed
  qed
  show "finite_variable_premises_bound (finite_rename_schema id id g S) a X \<longleftrightarrow> finite_variable_premises_bound S a X"
    unfolding finite_variable_premises_bound_def finite_rename_schema_materials
    by (auto simp: finite_rename_schema_premise)
qed

theorem finite_relocated_construction_complete:
  assumes formed: "finite_system_formed P" and injective: "inj_on g (system_definitions (decode_finite_system P))"
    and complete: "finite_construction_complete \<kappa> P"
  shows "finite_construction_complete (finite_relocated_construction g P \<kappa>) (finite_rename_system g P)"
  unfolding finite_construction_complete_def
proof (intro allI impI conjI)
  fix e c T a
  assume reg0: "a |\<in>| witness_registered (finite_relocated_construction g P \<kappa>) e T"
  obtain d0 c1 S0 where S0: "((d0,c1),S0) |\<in>| finite_system_clauses P" "g d0 = e" "finite_rename_schema id id g S0 = T"
      "a |\<in>| witness_registered \<kappa> d0 S0"
    using reg0 by (auto simp: finite_relocated_construction_registered)
  have "a |\<notin>| finite_pattern_variables (finite_schema_conclusion S0)"
    using complete S0(1,4) unfolding finite_construction_complete_def by blast
  then show "a |\<notin>| finite_pattern_variables (finite_schema_conclusion T)"
    using S0(3) by (auto simp: finite_rename_schema_def finite_term_pattern.map_id)
next
  fix e c T a
  show "finite_value_complete (finite_rename_system g P) T a
      (\<lambda>B. witness_value (finite_relocated_construction g P \<kappa>) (finite_rename_system g P) e T B a)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
  fix B v
  assume fn: "finite_relation_functional B" and bf: "fBall B (\<lambda>(b,t). finite_term_formed t)"
    and free: "a |\<notin>| fimage fst B"
    and bound: "finite_variable_premises_bound T a (fimage fst B)"
    and val: "witness_value (finite_relocated_construction g P \<kappa>) (finite_rename_system g P) e T B a = Some v"
  obtain d c0 S where S: "((d,c0),S) |\<in>| finite_system_clauses P" "g d = e" "finite_rename_schema id id g S = T"
    "a |\<in>| witness_registered \<kappa> d S" "witness_value \<kappa> P d S B a = Some v"
    using finite_relocated_construction_value[OF val] by blast
  have cS: "finite_value_complete P S a (\<lambda>B. witness_value \<kappa> P d S B a)"
    using complete S(1,4) unfolding finite_construction_complete_def by blast
  have boundS: "finite_variable_premises_bound S a (fimage fst B)"
    using bound finite_relocated_premises(2)[OF formed injective S(1)] S(3) by simp
  have iff: "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P S a ((finite_binding_valuation B)(a:=w))) \<longleftrightarrow>
      finite_variable_premises_hold P S a ((finite_binding_valuation B)(a:=v))"
    using cS fn bf free boundS S(5) unfolding finite_value_complete_def by blast
  show "(\<exists>w. finite_term_formed w \<and>
        finite_variable_premises_hold (finite_rename_system g P) T a ((finite_binding_valuation B)(a:=w))) \<longleftrightarrow>
      finite_variable_premises_hold (finite_rename_system g P) T a ((finite_binding_valuation B)(a:=v))"
    using iff finite_relocated_premises(1)[OF formed injective S(1)] S(3) by simp
  qed
qed

text \<open>
  In a finite mapped extension, a construction over the numbered target program Q is relocated by the installation's
  placement: every variable it registers names a clause of the placed program, the program the installation compiles
  into the installed package (whose meaning is the placed program's, by the installation's @{text correct}), and it is
  complete there wherever it is complete at Q.
\<close>

context finite_mapped_native_extension
begin

lemma relocated_registered_clause:
  assumes "a |\<in>| witness_registered (finite_relocated_construction placement Q \<kappa>) e T"
  shows "\<exists>c. ((e,c),T) |\<in>| finite_system_clauses goal"
proof -
  obtain d c S where S: "((d,c),S) |\<in>| finite_system_clauses Q" "placement d = e"
    "finite_rename_schema id id placement S = T"
    using assms by (auto simp: finite_relocated_construction_registered)
  have "map_prod (map_prod placement id) (finite_rename_schema id id placement) ((d,c),S) |\<in>|
      fimage (map_prod (map_prod placement id) (finite_rename_schema id id placement)) (finite_system_clauses Q)"
    by (rule fimageI[OF S(1)])
  then have "((e,c),T) |\<in>| finite_system_clauses goal"
    unfolding S(2)[symmetric] S(3)[symmetric] by (simp add: finite_rename_system_def)
  then show ?thesis by blast
qed

theorem relocated_construction_complete:
  assumes "finite_construction_complete \<kappa> Q"
  shows "finite_construction_complete (finite_relocated_construction placement Q \<kappa>) goal"
  by (rule finite_relocated_construction_complete[OF target maps.injective assms])

end

section \<open>Complete registrations lift every construction step, and the committed forms are exact\<close>

text \<open>
  A complete construction lifts every construction step of R5's committed search (@{const finite_construction_lifts}):
  at a selected node in the focus, @{text finite_complete_construction_supported} gives the successor supported with
  every node present barred. So the per-call, demand and native forms are exact over a complete construction as
  R5's committed forms at no commitment (task 526, q110 course A): resolved, the call holds; refuted, it does not.
  R3's @{const finite_program_resolution} stays sound with a registered construction, and is not claimed exact:
  its search keeps pruning across a construction step, which the committed search bars.
\<close>

theorem finite_construction_complete_lifts:
  assumes complete: "finite_construction_complete \<kappa> P"
  shows "finite_construction_lifts U \<kappa> P"
  unfolding finite_construction_lifts_def
proof (intro allI impI)
  fix F B st \<theta> d t N nd
  assume I: "resolution_invariant P d t st" and H: "resolution_registrations_held \<kappa> st"
    and sup: "resolution_supported_at U F B P st \<theta>"
    and sel: "finite_resolution_select \<kappa> P (finite_focused F st) = Select_Construction N"
    and nd: "nd |\<in>| N" and focus: "resolution_focused F (resolution_node_position nd)"
  have ndst: "nd |\<in>| resolution_nodes st"
    using finite_resolution_select_construction[OF sel] nd by (auto simp: finite_focused_def)
  show "\<exists>\<theta>'. resolution_supported_at U F (finite_committed_barring B st) P (finite_construction_step \<kappa> P st nd) \<theta>'"
    by (rule finite_complete_construction_supported[OF I H sup focus complete ndst])
qed

text \<open>The exact forms at a complete construction, each R5's at no commitment.\<close>

lemmas finite_complete_resolution_refutation_exact =
  finite_committed_resolution_refutation_exact[OF _ finite_commitment_exchanges_none finite_construction_complete_lifts]

lemmas finite_complete_verdict_exact =
  finite_committed_verdict_exact[OF _ finite_commitment_exchanges_none finite_construction_complete_lifts]

lemmas finite_complete_demand_exact =
  finite_committed_demand_exact[OF _ finite_commitment_exchanges_none finite_construction_complete_lifts]

lemmas native_complete_resolution_exact =
  native_committed_resolution_exact[OF _ finite_commitment_exchanges_none finite_construction_complete_lifts]

text \<open>
  At the construction of a list of registrations, each complete, the forms are exact
  (@{text finite_collection_construction_complete}).
\<close>

lemmas finite_registered_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF _ finite_collection_construction_complete]

lemmas finite_registered_verdict_exact =
  finite_complete_verdict_exact[OF _ finite_collection_construction_complete]

lemmas finite_registered_demand_exact =
  finite_complete_demand_exact[OF _ finite_collection_construction_complete]

lemmas native_registered_resolution_exact =
  native_complete_resolution_exact[OF _ finite_collection_construction_complete]

end
