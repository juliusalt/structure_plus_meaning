theory Factor_Resolution_Completeness
  imports Factor_Resolution_Acceptance Factor_Finite_Program_Evaluation Factor_Executable_Packages
    Candidate_Generators Inference_Rounds "HOL-Library.List_Lexorder"
begin

text \<open>
  Completeness and exactness of the resolving evaluator (R4 of DECISIONS.md "The native evaluator constructs the
  missing witnesses by resolution", items 5 and 6). A refuted call has no derivation: every true call of a
  formed program is the root of a branch the search keeps, down to the bound, so a search that neither
  succeeded nor was cut or stuck proves the call false. The argument is the lifting of derivations, made on a
  state through a support: a ground value for every variable under which every pending call holds and every
  pending material premise is satisfied. A true call is resolved by the clause and bindings of one of its
  least-round derivations, so its premises hold at smaller rounds than it, and a ground goal equal to the call
  of an ancestor, which pruning removes, would hold at no smaller round than itself: pruning keeps one branch.
  The search keeps every alternative of every goal it selects, so no goal is resolved once. The empty witness
  construction is the one the statements take; soundness holds for every construction (R3).
\<close>

section \<open>A true call is established at a finite round\<close>

text \<open>
  The rounds of a program are the inference rounds of its rules from nothing (@{text Inference_Rounds}); their
  union is its positive meaning (@{thm [source] inference_closure_rounds} with
  @{thm [source] schema_inference_closure}).
\<close>

abbreviation schema_rounds :: "('a,'s,'d,'c) schema_system \<Rightarrow> nat \<Rightarrow> ('d\<times>factor_term) set" where
  "schema_rounds P k \<equiv> inference_rounds (schema_inference_rules P) {} k"

text \<open>
  The rank of a true call is the least round that establishes it. A call of rank k+1 is the conclusion of an
  admitted instance whose premises hold at round k: each premise holds and has a smaller rank.
\<close>

definition resolution_rank :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd\<times>factor_term \<Rightarrow> nat" where
  "resolution_rank P q = (LEAST k. q \<in> schema_rounds P k)"

lemma resolution_rank_rounds:
  assumes "q \<in> positive_meaning P"
  shows "q \<in> schema_rounds P (resolution_rank P q)"
proof -
  have "q \<in> inference_closure (schema_inference_rules P) {}" using assms by (simp only: schema_inference_closure)
  then have "q \<in> (\<Union>k. schema_rounds P k)" by (simp only: inference_closure_rounds)
  then obtain k where "q \<in> schema_rounds P k" by blast
  then show ?thesis unfolding resolution_rank_def by (rule LeastI)
qed

lemma resolution_rank_le: "q \<in> schema_rounds P k \<Longrightarrow> resolution_rank P q \<le> k"
  unfolding resolution_rank_def by (rule Least_le)

lemma resolution_rank_step:
  assumes holds: "(d,t) \<in> positive_meaning P"
  obtains c V Q where "admitted_schema_instance P d c V t Q"
    "\<And>s e x. (s,e,x) \<in> Q \<Longrightarrow> (e,x) \<in> positive_meaning P \<and> resolution_rank P (e,x) < resolution_rank P (d,t)"
proof -
  have in_k: "(d,t) \<in> schema_rounds P (resolution_rank P (d,t))" by (rule resolution_rank_rounds[OF holds])
  then obtain k where k: "resolution_rank P (d,t) = Suc k"
    by (cases "resolution_rank P (d,t)") auto
  with in_k have "(d,t) \<in> inference_consequences (schema_inference_rules P) (schema_rounds P k)" by simp
  then obtain c V Q where inst: "admitted_schema_instance P d c V t Q" and sup: "rel_ran Q \<subseteq> schema_rounds P k"
    by (auto simp: inference_consequences_def schema_inference_rules_def)
  have prems_k: "\<And>s e x. (s,e,x) \<in> Q \<Longrightarrow> (e,x) \<in> schema_rounds P k" using sup by (auto simp: rel_ran_def)
  have meaning: "schema_rounds P k \<subseteq> positive_meaning P"
    using inference_rounds_inside_closure[of "schema_inference_rules P" "{}" k] by (simp only: schema_inference_closure)
  show ?thesis
  proof (rule that[OF inst])
    fix s e x assume "(s,e,x) \<in> Q"
    with prems_k have "(e,x) \<in> schema_rounds P k" by blast
    then show "(e,x) \<in> positive_meaning P \<and> resolution_rank P (e,x) < resolution_rank P (d,t)"
      using meaning resolution_rank_le[of "(e,x)" P k] k by fastforce
  qed
qed

section \<open>An admitted instance of the decoded program has a finite presentation\<close>

lemma finite_bindings_representation:
  assumes formed: "term_bindings_formed B V"
  obtains W where "decode_finite_term_bindings W = V"
proof -
  have fin: "finite V" and vals: "\<And>a x. (a,x) \<in> V \<Longrightarrow> term_formed x"
    using formed by (auto simp: term_bindings_formed_def)
  let ?W = "Abs_fset (map_relation_values finite_term_of V)"
  have fs: "fset ?W = map_relation_values finite_term_of V" using fin by (simp add: Abs_fset_inverse)
  have "map_relation_values decode_finite_term (map_relation_values finite_term_of V) = V"
    by (rule map_relation_values_inverse) (use vals decode_finite_term_of in blast)
  then show thesis by (intro that[of ?W]) (simp add: decode_finite_term_bindings_def fs)
qed

lemma finite_admitted_from_decoded:
  assumes inst: "admitted_schema_instance (decode_finite_system P) d c V (decode_finite_term t) Q"
  obtains W H where "finite_admitted_schema_instance P d c W t H" "decode_finite_premises H = Q"
proof -
  from inst obtain S where "schema_instance S V (decode_finite_term t) Q"
    by (auto simp: admitted_schema_instance_def)
  then have "term_bindings_formed (schema_variables S) V" by (auto simp: schema_instance_def)
  then obtain W where W: "decode_finite_term_bindings W = V" by (rule finite_bindings_representation)
  have instW: "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings W)
      (decode_finite_term t) Q"
    using inst by (simp only: W)
  obtain H where H: "H |\<in>| finite_admitted_premise_readings P d c W t" and HQ: "decode_finite_premises H = Q"
    using iffD1[OF finite_admitted_premise_readings_correct[of P d c W t Q] instW] by blast
  have "finite_admitted_schema_instance P d c W t H"
    using iffD1[OF finite_admitted_premise_reading_exact[of H P d c W t] H] .
  then show thesis by (rule that[OF _ HQ])
qed

section \<open>The ground value of a pattern under a support\<close>

abbreviation resolution_substitution :: "('v \<Rightarrow> finite_factor_term) \<Rightarrow> 'v \<Rightarrow> 'v finite_term_pattern" where
  "resolution_substitution \<theta> x \<equiv> finite_exact_term_pattern (\<theta> x)"

definition resolution_value :: "('v \<Rightarrow> finite_factor_term) \<Rightarrow> 'v finite_term_pattern \<Rightarrow> finite_factor_term" where
  "resolution_value \<theta> p =
    finite_residual_term (finite_pattern_substitute (resolution_substitution \<theta>) p)"

lemma resolution_value_exact:
  "finite_exact_term_pattern (resolution_value \<theta> p) = finite_pattern_substitute (resolution_substitution \<theta>) p"
  by (simp add: resolution_value_def finite_exact_residual_substitute)

lemma resolution_value_eq:
  "resolution_value \<theta> p = t \<longleftrightarrow>
    finite_pattern_substitute (resolution_substitution \<theta>) p = finite_exact_term_pattern t"
  using resolution_value_exact[of \<theta> p] finite_exact_term_pattern_eq_iff by metis

lemma resolution_value_cong:
  assumes agree: "\<And>x. x |\<in>| finite_pattern_variables p \<Longrightarrow> \<theta> x = \<theta>' x"
  shows "resolution_value \<theta> p = resolution_value \<theta>' p"
proof -
  have "finite_pattern_substitute (resolution_substitution \<theta>) p =
      finite_pattern_substitute (resolution_substitution \<theta>') p"
    by (rule finite_pattern_substitute_cong) (simp add: agree)
  then show ?thesis by (simp add: resolution_value_def)
qed

lemma resolution_value_unifier:
  assumes "\<And>b. finite_pattern_substitute (resolution_substitution \<theta>) (\<sigma> b) = finite_exact_term_pattern (\<theta> b)"
  shows "resolution_value \<theta> (finite_pattern_substitute \<sigma> p) = resolution_value \<theta> p"
  by (simp add: resolution_value_def finite_pattern_substitute_composes assms)

lemma resolution_value_ground:
  "resolution_value \<theta> (finite_exact_term_pattern t) = t"
  by (simp add: resolution_value_def finite_pattern_substitute_ground)

text \<open>The value does not depend on the variable type the exact patterns are read at.\<close>

lemma finite_residual_substitute_value:
  "finite_residual_term (finite_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<theta> a)) p) = resolution_value \<theta> p"
  unfolding resolution_value_def by (induction p) simp_all

lemma resolution_value_substitute:
  "(finite_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<theta> a)) p :: 'w finite_term_pattern) =
    finite_exact_term_pattern (resolution_value \<theta> p)"
proof -
  have "finite_exact_term_pattern (finite_residual_term (finite_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<theta> a)) p)) =
      (finite_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<theta> a)) p :: 'w finite_term_pattern)"
    by (simp add: finite_exact_residual_substitute)
  then show ?thesis by (simp add: finite_residual_substitute_value)
qed

abbreviation resolution_binding_value :: "('a\<times>finite_factor_term) fset \<Rightarrow> 'a \<Rightarrow> finite_factor_term" where
  "resolution_binding_value V \<equiv> rel_value (fset V)"

lemma resolution_binding_graph:
  assumes formed: "finite_term_bindings_formed B V"
  shows "V = finite_ground_bindings (resolution_binding_value V) B"
proof (rule fset_eqI)
  fix z :: "'a \<times> finite_factor_term"
  obtain a x where z: "z = (a,x)" by (cases z)
  have functional: "finite_relation_functional V" and B: "B = fimage fst V"
    using formed by (auto simp: finite_term_bindings_formed_def)
  have sv: "single_valued (fset V)" using functional by (simp only: finite_relation_functional_correct)
  show "z |\<in>| V \<longleftrightarrow> z |\<in>| finite_ground_bindings (resolution_binding_value V) B"
    unfolding z finite_ground_bindings_member B
    using rel_value_eq[OF sv] by (force simp: fimage_iff)
qed

lemma resolution_binding_instance:
  assumes formed: "finite_term_bindings_formed B V"
    and scope: "finite_pattern_variables p |\<subseteq>| B"
    and inst: "finite_pattern_instance V p x"
  shows "resolution_value (resolution_binding_value V) p = x"
proof -
  have "finite_pattern_instance (finite_ground_bindings (resolution_binding_value V) B) p x"
    using inst by (simp only: resolution_binding_graph[OF formed, symmetric])
  moreover have "fset (finite_pattern_variables p) \<subseteq> fset B" using scope by (simp add: less_eq_fset.rep_eq)
  ultimately have "finite_exact_term_pattern x =
      (finite_pattern_substitute (finite_exact_term_pattern \<circ> resolution_binding_value V) p :: 'a finite_term_pattern)"
    using finite_ground_substitution_instance[of p B] by blast
  then show ?thesis by (simp add: resolution_value_eq o_def)
qed

lemma resolution_ground_instance:
  fixes \<theta> :: "'v \<Rightarrow> finite_factor_term" and p :: "'v finite_term_pattern"
  assumes pf: "finite_pattern_formed p" and scope: "finite_pattern_variables p |\<subseteq>| B"
    and eq: "finite_pattern_substitute (resolution_substitution \<theta>) p = finite_exact_term_pattern y"
  shows "finite_pattern_instance (finite_ground_bindings \<theta> B) p y"
proof -
  have sub: "fset (finite_pattern_variables p) \<subseteq> fset B" using scope by (simp add: less_eq_fset.rep_eq)
  have eq': "finite_exact_term_pattern y =
      (finite_pattern_substitute (finite_exact_term_pattern \<circ> \<theta>) p :: 'v finite_term_pattern)"
    using eq by (simp add: o_def)
  show ?thesis using finite_ground_substitution_instance[OF sub] pf eq' by blast
qed

lemma resolution_binding_material:
  assumes formed: "finite_term_bindings_formed B V"
    and scope: "finite_material_variables M |\<subseteq>| B"
    and sat: "finite_material_satisfied V M"
  shows "finite_material_ground_satisfied
    (finite_material_pattern_substitute (\<lambda>a. finite_exact_term_pattern (resolution_binding_value V a)) M)"
proof -
  have field: "\<And>p y. finite_pattern_instance V p y \<Longrightarrow> finite_pattern_variables p |\<subseteq>| B \<Longrightarrow>
      finite_pattern_substitute (\<lambda>a. finite_exact_term_pattern (resolution_binding_value V a)) p = finite_exact_term_pattern y"
    using resolution_binding_instance[OF formed] resolution_value_substitute by metis
  have sc: "finite_pattern_variables (finite_material_source M) |\<subseteq>| B"
    "finite_pattern_variables (finite_material_atoms M) |\<subseteq>| B"
    "finite_pattern_variables (finite_material_edges M) |\<subseteq>| B"
    "finite_pattern_variables (finite_material_counts M) |\<subseteq>| B"
    "finite_pattern_variables (finite_material_functions M) |\<subseteq>| B"
    using scope by (auto simp: finite_material_variables_def)
  from sat obtain s a e b f where
      i_s: "finite_pattern_instance V (finite_material_source M) s"
      and ia: "finite_pattern_instance V (finite_material_atoms M) a"
      and ie: "finite_pattern_instance V (finite_material_edges M) e"
      and ib: "finite_pattern_instance V (finite_material_counts M) b"
      and iF: "finite_pattern_instance V (finite_material_functions M) f"
      and obs: "finite_material_observation s a e b f"
    by (auto simp: finite_material_satisfied_def finite_pattern_instances_member)
  show ?thesis unfolding finite_material_ground_satisfied_def finite_material_pattern_substitute_fields
    using field[OF i_s sc(1)] field[OF ia sc(2)] field[OF ie sc(3)] field[OF ib sc(4)] field[OF iF sc(5)] obs
    by blast
qed

section \<open>Variables under substitution\<close>

lemma finite_substitute_variable_origin:
  "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) \<Longrightarrow>
    \<exists>y. y |\<in>| finite_pattern_variables p \<and> z |\<in>| finite_pattern_variables (\<sigma> y)"
  by (induction p) auto

lemma finite_material_substitute_variable_origin:
  "z |\<in>| finite_material_variables (finite_material_pattern_substitute \<sigma> M) \<Longrightarrow>
    \<exists>y. y |\<in>| finite_material_variables M \<and> z |\<in>| finite_pattern_variables (\<sigma> y)"
  by (auto simp: finite_material_variables_def dest!: finite_substitute_variable_origin)

lemma resolution_goal_substitute_variable_origin:
  assumes z: "z |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g)"
  shows "\<exists>y. y |\<in>| resolution_goal_variables g \<and> z |\<in>| finite_pattern_variables (\<sigma> y)"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  with z show ?thesis using finite_substitute_variable_origin[of z \<sigma> p] by simp
next
  case (Resolution_Material_Goal q r M)
  with z show ?thesis using finite_material_substitute_variable_origin[of z \<sigma> M] by simp
qed

lemma finite_unifier_variable:
  assumes u: "finite_unify_pairs E = Some u"
    and z: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
  shows "z = y \<or> z \<in> finite_pairs_variables E"
proof (cases "map_of u y")
  case None
  with z show ?thesis by (simp add: finite_binding_substitution_def)
next
  case (Some q)
  then have "(y,q) \<in> set u" by (rule map_of_SomeD)
  then have "fset (finite_pattern_variables q) \<subseteq> finite_pairs_variables E"
    using finite_unify_pairs_variables[OF u] by fastforce
  with Some z show ?thesis by (auto simp: finite_binding_substitution_def)
qed

lemma finite_material_pattern_substitute_cong:
  assumes "\<And>z. z |\<in>| finite_material_variables M \<Longrightarrow> \<sigma> z = \<sigma>' z"
  shows "finite_material_pattern_substitute \<sigma> M = finite_material_pattern_substitute \<sigma>' M"
  unfolding finite_material_pattern_substitute_def
  using assms by (auto simp: finite_material_variables_def intro!: finite_pattern_substitute_cong)

lemma resolution_goal_substitute_call:
  "resolution_goal_substitute \<sigma> g = Resolution_Call_Goal q r e p \<longleftrightarrow>
    (\<exists>p0. g = Resolution_Call_Goal q r e p0 \<and> p = finite_pattern_substitute \<sigma> p0)"
  by (cases g) auto

lemma resolution_goal_substitute_material:
  "resolution_goal_substitute \<sigma> g = Resolution_Material_Goal q r M \<longleftrightarrow>
    (\<exists>M0. g = Resolution_Material_Goal q r M0 \<and> M = finite_material_pattern_substitute \<sigma> M0)"
  by (cases g) auto

section \<open>Positions\<close>

definition resolution_before :: "'s list \<Rightarrow> 's list \<Rightarrow> bool" where
  "resolution_before x y \<longleftrightarrow> length x < length y \<and> take (length x) y = x"

lemma resolution_before_child:
  "resolution_before x (q@[s]) \<Longrightarrow> x = q \<or> resolution_before x q"
  unfolding resolution_before_def by (cases "length x = length q") (auto simp: take_append)

lemma resolution_before_irrefl: "\<not> resolution_before x x"
  by (simp add: resolution_before_def)

lemma resolution_pattern_node_prefix:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
  shows "\<forall>m a. m |\<in>| resolution_nodes st \<longrightarrow> length (resolution_node_position m) = n \<longrightarrow>
    length a \<le> n \<longrightarrow> take (length a) (resolution_node_position m) = a \<longrightarrow>
    (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = a)"
proof (induction n)
  case 0
  show ?case by force
next
  case (Suc n)
  show ?case
  proof (intro allI impI)
    fix m a assume m: "m |\<in>| resolution_nodes st" and len: "length (resolution_node_position m) = Suc n"
      and la: "length a \<le> Suc n" and tk: "take (length a) (resolution_node_position m) = a"
    show "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = a"
    proof (cases "length a = Suc n")
      case True
      then have "resolution_node_position m = a" using len tk by (metis take_all order_refl)
      with m show ?thesis by blast
    next
      case False
      have ne: "resolution_node_position m \<noteq> []" using len by auto
      obtain m' where m': "m' |\<in>| resolution_nodes st" "resolution_node_position m' = butlast (resolution_node_position m)"
        using I m ne by (auto simp: resolution_pattern_invariant_def resolution_pattern_nodes_placed_def)
      have "length (resolution_node_position m') = n" using len m'(2) by simp
      moreover have "length a \<le> n" using la False by simp
      moreover have "take (length a) (resolution_node_position m') = a"
        using m'(2) tk len False la by (simp add: take_butlast)
      ultimately show ?thesis using Suc.IH m'(1) by blast
    qed
  qed
qed

lemma resolution_node_prefix:
  assumes I: "resolution_invariant P d t st"
  shows "\<forall>m a. m |\<in>| resolution_nodes st \<longrightarrow> length (resolution_node_position m) = n \<longrightarrow>
    length a \<le> n \<longrightarrow> take (length a) (resolution_node_position m) = a \<longrightarrow>
    (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = a)"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_node_prefix)

lemma resolution_pattern_goal_ancestor_node:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and h: "h |\<in>| resolution_pending st"
    and before: "resolution_before a (resolution_goal_position h)"
  shows "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = a"
proof -
  have ne: "resolution_goal_position h \<noteq> []" using before by (auto simp: resolution_before_def)
  obtain m where m: "m |\<in>| resolution_nodes st" "resolution_node_position m = butlast (resolution_goal_position h)"
    using I h ne by (auto simp: resolution_pattern_invariant_def resolution_pattern_goals_placed_def)
  have "length a \<le> length (resolution_node_position m)" "take (length a) (resolution_node_position m) = a"
    using m(2) before by (auto simp: resolution_before_def take_butlast)
  then show ?thesis using resolution_pattern_node_prefix[OF I] m(1) by blast
qed

lemma resolution_goal_ancestor_node:
  assumes I: "resolution_invariant P d t st" and h: "h |\<in>| resolution_pending st"
    and before: "resolution_before a (resolution_goal_position h)"
  shows "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = a"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_goal_ancestor_node)

lemma resolution_pattern_call_goal_no_node:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and nd: "nd |\<in>| resolution_nodes st"
  shows "resolution_node_position nd \<noteq> q"
  using I g nd by (fastforce simp: resolution_pattern_invariant_def resolution_positions_distinct_def)

lemma resolution_call_goal_no_node:
  assumes I: "resolution_invariant P d t st" and g: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and nd: "nd |\<in>| resolution_nodes st"
  shows "resolution_node_position nd \<noteq> q"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_call_goal_no_node)

section \<open>A support of a state\<close>

text \<open>
  A support of a state gives every variable a ground value: every pending call holds at its value and has a
  smaller rank than the call of each node above it, every pending material premise is satisfied at its value,
  and every variable of a pending goal or of a node's call belongs to a node's position.
\<close>

definition resolution_placed :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> bool" where
  "resolution_placed st z \<longleftrightarrow> (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = fst (fst z))"

definition resolution_supported ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow> bool" where
  "resolution_supported P st \<theta> \<longleftrightarrow>
    (\<forall>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))) \<and>
    (\<forall>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)) \<and>
    (\<forall>g z. g |\<in>| resolution_pending st \<longrightarrow> z |\<in>| resolution_goal_variables g \<longrightarrow> resolution_placed st z) \<and>
    (\<forall>nd z. nd |\<in>| resolution_nodes st \<longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow>
      resolution_placed st z)"

text \<open>
  A support may leave unplaced the variables a predicate F allows. A search started at a pattern goal holds the
  pattern's variables before any node stands at their positions; F keeps them apart from the variables the
  program's clauses and interfaces are renamed to, a variable F allows being no program variable
  (@{text finite_program_variables}). The support of a ground root allows none (@{text resolution_supported_none}).
  The root value of a state under a support is the value its pending root goal and its root node take.
\<close>

definition finite_program_variables :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'a fset" where
  "finite_program_variables P =
    ffUnion (fimage (\<lambda>(e,i). finite_pattern_variables i) (finite_system_interfaces P)) |\<union>|
    ffUnion (fimage (\<lambda>(dc,S). finite_schema_variables S) (finite_system_clauses P))"

lemma finite_program_variables_clause:
  "((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> a |\<in>| finite_schema_variables S \<Longrightarrow>
    a |\<in>| finite_program_variables P"
  unfolding finite_program_variables_def by (force simp: resolution_fset_simps)

lemma finite_program_variables_interface:
  "(e,i) |\<in>| finite_system_interfaces P \<Longrightarrow> a |\<in>| finite_pattern_variables i \<Longrightarrow>
    a |\<in>| finite_program_variables P"
  unfolding finite_program_variables_def by (force simp: resolution_fset_simps)

definition resolution_supported_by ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow> bool" where
  "resolution_supported_by F P st \<theta> \<longleftrightarrow>
    (\<forall>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))) \<and>
    (\<forall>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)) \<and>
    (\<forall>g z. g |\<in>| resolution_pending st \<longrightarrow> z |\<in>| resolution_goal_variables g \<longrightarrow> resolution_placed st z \<or> F z) \<and>
    (\<forall>nd z. nd |\<in>| resolution_nodes st \<longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow>
      resolution_placed st z \<or> F z)"


lemma resolution_supported_none:
  "resolution_supported P st \<theta> \<longleftrightarrow> resolution_supported_by (\<lambda>_. False) P st \<theta>"
  by (simp add: resolution_supported_def resolution_supported_by_def)

lemma resolution_no_foreign: "(\<lambda>_. False) z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
  by simp

definition resolution_root_value ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow>
      finite_factor_term \<Rightarrow> bool" where
  "resolution_root_value st \<theta> v \<longleftrightarrow>
    (\<forall>r e p. Resolution_Call_Goal [] r e p |\<in>| resolution_pending st \<longrightarrow> resolution_value \<theta> p = v) \<and>
    (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd = [] \<longrightarrow>
      resolution_value \<theta> (resolution_node_call nd) = v)"

lemma resolution_supportedI:
  assumes "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    and "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z"
    and "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z"
  shows "resolution_supported P st \<theta>"
  using assms unfolding resolution_supported_def by blast

lemma resolution_supported_byI:
  assumes "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    and "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
  shows "resolution_supported_by F P st \<theta>"
  using assms unfolding resolution_supported_by_def by blast

lemma resolution_supported_by_unpruned:
  assumes sup: "resolution_supported_by F P st \<theta>" and g: "g |\<in>| resolution_pending st"
  shows "\<not> finite_pruned st g"
proof
  assume pruned: "finite_pruned st g"
  then obtain q r e p where gq: "g = Resolution_Call_Goal q r e p"
    by (auto simp: finite_pruned_def split: resolution_goal.splits)
  with pruned obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_before (resolution_node_position nd) q"
    "resolution_node_site nd = e" "resolution_node_call nd = p"
    by (auto simp: finite_pruned_def resolution_before_def)
  have "resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
      resolution_rank (decode_finite_system P)
        (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
    using sup g nd(1,2) unfolding gq resolution_supported_by_def by blast
  with nd(3,4) show False by simp
qed

lemma resolution_supported_unpruned:
  assumes sup: "resolution_supported P st \<theta>" and g: "g |\<in>| resolution_pending st"
  shows "\<not> finite_pruned st g"
  using assms unfolding resolution_supported_none by (rule resolution_supported_by_unpruned)

section \<open>The successors a step constructs\<close>

lemma finite_call_successors_intro:
  assumes iface: "(e,i) |\<in>| finite_system_interfaces P" and clause: "((e,c),S) |\<in>| finite_system_clauses P"
    and unified: "finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
  shows "resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}))
        (finsert (finite_clause_node q e c S) (resolution_nodes st)) (resolution_witnesses st))
    |\<in>| finite_call_successors P st q r e p"
  using iface clause unified unfolding finite_call_successors_def
  by (force simp: resolution_fset_simps)

lemma finite_material_instance_pairs_intro:
  assumes "finite_pattern_instance W (finite_material_source M) s" "finite_pattern_instance W (finite_material_atoms M) a"
    "finite_pattern_instance W (finite_material_edges M) e" "finite_pattern_instance W (finite_material_counts M) b"
    "finite_pattern_instance W (finite_material_functions M) f"
  shows "[(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)] |\<in>| finite_material_instance_pairs W M"
  using assms unfolding finite_material_instance_pairs_def
  apply (simp add: resolution_fset_simps finite_pattern_instances_member)
  apply (rule bexI[of _ s], rule bexI[of _ a], rule bexI[of _ e], rule bexI[of _ b], rule rev_image_eqI[of f])
  by (simp_all add: finite_pattern_instances_member)

lemma finite_material_successors_intro:
  assumes Ws: "finite_material_resolution M = Material_Solutions Ws" and W: "W |\<in>| Ws"
    and E: "E |\<in>| finite_material_instance_pairs W M" and u: "finite_unify_pairs E = Some u"
  shows "resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st)) |\<in>| finite_material_successors st q r M"
  using W E u unfolding finite_material_successors_def Ws by (force simp: resolution_fset_simps)

lemma resolution_placed_substitute:
  "resolution_placed (resolution_state_substitute \<sigma> st) z \<longleftrightarrow> resolution_placed st z"
proof
  assume "resolution_placed (resolution_state_substitute \<sigma> st) z"
  then obtain nd where nd: "nd \<in> resolution_node_substitute \<sigma> ` fset (resolution_nodes st)"
    and pos: "resolution_node_position nd = fst (fst z)"
    unfolding resolution_placed_def resolution_state_substitute_fields fimage.rep_eq by blast
  from nd obtain m where m: "m |\<in>| resolution_nodes st" and ndm: "nd = resolution_node_substitute \<sigma> m"
    by blast
  have "resolution_node_position m = fst (fst z)" using pos ndm by simp
  with m show "resolution_placed st z" unfolding resolution_placed_def by blast
next
  assume "resolution_placed st z"
  then obtain m where m: "m |\<in>| resolution_nodes st" and pos: "resolution_node_position m = fst (fst z)"
    unfolding resolution_placed_def by blast
  have "resolution_node_substitute \<sigma> m \<in> resolution_node_substitute \<sigma> ` fset (resolution_nodes st)"
    using m by blast
  moreover have "resolution_node_position (resolution_node_substitute \<sigma> m) = fst (fst z)" using pos by simp
  ultimately show "resolution_placed (resolution_state_substitute \<sigma> st) z"
    unfolding resolution_placed_def resolution_state_substitute_fields fimage.rep_eq by blast
qed

lemma resolution_placed_state:
  "resolution_placed (Resolution_State G N W) z \<longleftrightarrow> (\<exists>nd. nd |\<in>| N \<and> resolution_node_position nd = fst (fst z))"
  by (simp add: resolution_placed_def)

lemma resolution_state_substitute_members:
  "nd |\<in>| resolution_nodes (resolution_state_substitute \<sigma> (Resolution_State G N W)) \<Longrightarrow>
    \<exists>m. m |\<in>| N \<and> nd = resolution_node_substitute \<sigma> m"
  "g |\<in>| resolution_pending (resolution_state_substitute \<sigma> (Resolution_State G N W)) \<Longrightarrow>
    \<exists>g0. g0 |\<in>| G \<and> g = resolution_goal_substitute \<sigma> g0"
  unfolding resolution_state_substitute_fields resolution_state.sel fimage.rep_eq by blast+

section \<open>A supported goal has a supported successor\<close>

lemma resolution_call_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
  obtains st' \<theta>' where "st' |\<in>| finite_call_successors P st q r e p" "resolution_supported_by F P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof -
  let ?P = "decode_finite_system P"
  define x where "x = resolution_value \<theta> p"
  have holds: "(e,decode_finite_term x) \<in> positive_meaning ?P"
    and ancestors: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_before (resolution_node_position nd) q \<Longrightarrow>
      resolution_rank ?P (e,decode_finite_term x) < resolution_rank ?P (resolution_node_site nd,
        decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
    using sup goal unfolding x_def resolution_supported_by_def by blast+
  have goal_placed: "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and node_placed: "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
    and old_material: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and old_calls: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank ?P (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    using sup unfolding resolution_supported_by_def by blast+
  obtain c V Q where admitted: "admitted_schema_instance ?P e c V (decode_finite_term x) Q"
    and smaller: "\<And>s e' y. (s,e',y) \<in> Q \<Longrightarrow> (e',y) \<in> positive_meaning ?P \<and>
      resolution_rank ?P (e',y) < resolution_rank ?P (e,decode_finite_term x)"
    using resolution_rank_step[OF holds] by blast
  obtain W H where fadm: "finite_admitted_schema_instance P e c W x H" and HQ: "decode_finite_premises H = Q"
    by (rule finite_admitted_from_decoded[OF admitted])
  from fadm obtain i S where iface: "(e,i) |\<in>| finite_system_interfaces P" "finite_pattern_accepts i x"
    and clause: "((e,c),S) |\<in>| finite_system_clauses P" and sinst: "finite_schema_instance S W x H"
    and smat: "finite_schema_material_satisfied S W"
    by (auto simp: finite_admitted_schema_instance_def finite_schema_call_formed_def)
  from sinst have Wf: "finite_term_bindings_formed (finite_schema_variables S) W"
    and hinst: "finite_pattern_instance W (finite_schema_conclusion S) x"
    and pinst: "finite_schema_premise_instance S W H"
    by (auto simp: finite_schema_instance_def)
  from iface(2) have Mf: "finite_term_bindings_formed (finite_pattern_variables i) (finite_matching_bindings i x)"
    and minst: "finite_pattern_instance (finite_matching_bindings i x) i x"
    by (auto simp: finite_pattern_accepts_def)
  define \<tau> where "\<tau> = resolution_binding_value W"
  define \<iota> where "\<iota> = resolution_binding_value (finite_matching_bindings i x)"
  define owned where "owned = (\<lambda>z. fst (fst z) = q \<and>
    (if snd (fst z) then snd z |\<in>| finite_schema_variables S else snd z |\<in>| finite_pattern_variables i))"
  define \<theta>' where "\<theta>' = (\<lambda>z. if owned z then (if snd (fst z) then \<tau> (snd z) else \<iota> (snd z)) else \<theta> z)"
  let ?\<sigma> = "resolution_substitution \<theta>'"
  have prem_scope: "\<And>s e' p'. (s,e',p') |\<in>| finite_schema_premises S \<Longrightarrow>
      finite_pattern_variables p' |\<subseteq>| finite_schema_variables S"
    by (force simp: finite_schema_variables_def resolution_fset_simps less_eq_fset.rep_eq)
  have mat_scope: "\<And>s N. (s,N) |\<in>| finite_schema_materials S \<Longrightarrow>
      finite_material_variables N |\<subseteq>| finite_schema_variables S"
    by (force simp: finite_schema_variables_def resolution_fset_simps less_eq_fset.rep_eq)
  have concl_scope: "\<And>a. a |\<in>| finite_pattern_variables (finite_schema_conclusion S) \<Longrightarrow>
      a |\<in>| finite_schema_variables S"
    by (auto simp: finite_schema_variables_def resolution_fset_simps)
  have prem_vars: "\<And>s e' p' a. (s,e',p') |\<in>| finite_schema_premises S \<Longrightarrow> a |\<in>| finite_pattern_variables p' \<Longrightarrow>
      a |\<in>| finite_schema_variables S"
    by (meson fsubsetD prem_scope)
  have head: "resolution_value \<tau> (finite_schema_conclusion S) = x"
    unfolding \<tau>_def by (rule resolution_binding_instance[OF Wf _ hinst])
      (auto simp: finite_schema_variables_def resolution_fset_simps less_eq_fset.rep_eq)
  have iface_value: "resolution_value \<iota> i = x"
    unfolding \<iota>_def by (rule resolution_binding_instance[OF Mf _ minst]) simp
  have no_node_q: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd \<noteq> q"
    by (rule resolution_pattern_call_goal_no_node[OF I goal])
  have owned_vars: "\<And>z. owned z \<Longrightarrow> snd z |\<in>| finite_program_variables P"
    using finite_program_variables_clause[OF clause] finite_program_variables_interface[OF iface(1)]
    by (auto simp: owned_def split: if_splits)
  have agree: "\<And>z. resolution_placed st z \<or> F z \<Longrightarrow> \<theta>' z = \<theta> z"
  proof -
    fix z assume old: "resolution_placed st z \<or> F z"
    have "\<not> owned z"
    proof
      assume own: "owned z"
      from old show False
      proof
        assume "resolution_placed st z"
        then show False using own no_node_q by (auto simp: resolution_placed_def owned_def)
      next
        assume "F z"
        then show False using foreign own owned_vars by blast
      qed
    qed
    then show "\<theta>' z = \<theta> z" by (simp add: \<theta>'_def)
  qed
  have value_old: "\<And>y. (\<And>z. z |\<in>| finite_pattern_variables y \<Longrightarrow> resolution_placed st z \<or> F z) \<Longrightarrow>
      resolution_value \<theta>' y = resolution_value \<theta> y"
    by (rule resolution_value_cong) (simp add: agree)
  have value_p: "resolution_value \<theta>' p = x"
    unfolding x_def by (rule value_old) (use goal_placed[OF goal] in simp)
  have value_new: "\<And>p2. (\<And>a. a |\<in>| finite_pattern_variables p2 \<Longrightarrow> a |\<in>| finite_schema_variables S) \<Longrightarrow>
      resolution_value \<theta>' (finite_rename_apart (q,True) p2) = resolution_value \<tau> p2"
  proof -
    fix p2 assume scope: "\<And>a. a |\<in>| finite_pattern_variables p2 \<Longrightarrow> a |\<in>| finite_schema_variables S"
    have "resolution_value \<theta>' (finite_rename_apart (q,True) p2) = resolution_value (\<lambda>a. \<theta>' ((q,True),a)) p2"
      unfolding resolution_value_def[of \<theta>'] by (simp add: finite_rename_apart_substitute finite_residual_substitute_value)
    also have "\<dots> = resolution_value \<tau> p2"
      by (rule resolution_value_cong) (simp add: \<theta>'_def owned_def scope)
    finally show "resolution_value \<theta>' (finite_rename_apart (q,True) p2) = resolution_value \<tau> p2" .
  qed
  have iface_new: "resolution_value \<theta>' (finite_rename_apart (q,False) i) = x"
  proof -
    have "resolution_value \<theta>' (finite_rename_apart (q,False) i) = resolution_value (\<lambda>a. \<theta>' ((q,False),a)) i"
      unfolding resolution_value_def[of \<theta>'] by (simp add: finite_rename_apart_substitute finite_residual_substitute_value)
    also have "\<dots> = resolution_value \<iota> i"
      by (rule resolution_value_cong) (simp add: \<theta>'_def owned_def)
    finally show ?thesis using iface_value by simp
  qed
  define E where "E = [(finite_rename_apart (q,False) i,p),(finite_rename_apart (q,True) (finite_schema_conclusion S),p)]"
  have unifies: "finite_unifies ?\<sigma> E"
  proof -
    have "finite_pattern_substitute ?\<sigma> p = finite_exact_term_pattern x"
      using value_p by (simp add: resolution_value_eq)
    moreover have "finite_pattern_substitute ?\<sigma> (finite_rename_apart (q,False) i) = finite_exact_term_pattern x"
      using iface_new by (simp add: resolution_value_eq)
    moreover have "finite_pattern_substitute ?\<sigma> (finite_rename_apart (q,True) (finite_schema_conclusion S)) =
        finite_exact_term_pattern x"
      using value_new[OF concl_scope] head by (simp add: resolution_value_eq)
    ultimately show ?thesis by (simp add: E_def)
  qed
  obtain u where u: "finite_unify_pairs E = Some u"
    using unifies finite_unify_pairs_none_iff[of E] by (cases "finite_unify_pairs E") auto
  have mgu: "\<And>b. finite_pattern_substitute ?\<sigma> (finite_binding_substitution u b) = ?\<sigma> b"
    by (rule finite_unify_pairs_most_general[OF u unifies])
  have keep: "\<And>y. resolution_value \<theta>' (finite_pattern_substitute (finite_binding_substitution u) y) = resolution_value \<theta>' y"
    by (rule resolution_value_unifier) (rule mgu)
  have keep_material: "\<And>N. finite_material_pattern_substitute ?\<sigma>
      (finite_material_pattern_substitute (finite_binding_substitution u) N) = finite_material_pattern_substitute ?\<sigma> N"
    by (simp add: finite_material_pattern_substitute_composes mgu)
  have E_vars: "\<And>z. z \<in> finite_pairs_variables E \<Longrightarrow> resolution_placed st z \<or> F z \<or> fst (fst z) = q"
    using goal_placed[OF goal] by (auto simp: E_def finite_rename_apart_variables)
  have unified_var: "\<And>y z. z |\<in>| finite_pattern_variables (finite_binding_substitution u y) \<Longrightarrow>
      z = y \<or> resolution_placed st z \<or> F z \<or> fst (fst z) = q"
    using finite_unifier_variable[OF u] E_vars by blast
  define st' where "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}))
        (finsert (finite_clause_node q e c S) (resolution_nodes st)) (resolution_witnesses st))"
  have u': "finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
    using u by (simp only: E_def)
  have member: "st' |\<in>| finite_call_successors P st q r e p"
    unfolding st'_def by (rule finite_call_successors_intro[where st=st and r=r, OF iface(1) clause u'])
  have placed': "\<And>z. resolution_placed st' z \<longleftrightarrow> resolution_placed st z \<or> fst (fst z) = q"
    unfolding st'_def resolution_placed_substitute resolution_placed_state resolution_placed_def
    by (auto simp: finite_clause_node_def)
  have new_goals: "\<And>g0. g0 |\<in>| finite_clause_goals q e c S \<Longrightarrow>
      (\<exists>s e' p2. (s,e',p2) |\<in>| finite_schema_premises S \<and>
        g0 = Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_rename_apart (q,True) p2)) \<or>
      (\<exists>s N. (s,N) |\<in>| finite_schema_materials S \<and>
        g0 = Resolution_Material_Goal (q@[s]) (e,c,s) (finite_rename_material (Pair (q,True)) N))"
    by (auto simp: finite_clause_goals_def)
  have new_vars: "\<And>g0 z. g0 |\<in>| finite_clause_goals q e c S \<Longrightarrow> z |\<in>| resolution_goal_variables g0 \<Longrightarrow>
      fst (fst z) = q"
  proof -
    fix g0 z assume g0: "g0 |\<in>| finite_clause_goals q e c S" and z: "z |\<in>| resolution_goal_variables g0"
    from new_goals[OF g0] show "fst (fst z) = q"
    proof (elim disjE exE conjE)
      fix s e' p2 assume "g0 = Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_rename_apart (q,True) p2)"
      with z have "z |\<in>| Pair (q,True) |`| finite_pattern_variables p2"
        by (simp add: finite_rename_apart_variables)
      then show "fst (fst z) = q" by auto
    next
      fix s N assume "g0 = Resolution_Material_Goal (q@[s]) (e,c,s) (finite_rename_material (Pair (q,True)) N)"
      with z have "z |\<in>| finite_material_variables
          (finite_material_pattern_substitute (\<lambda>a. Finite_Variable ((q,True),a)) N)"
        by (simp add: finite_rename_material_as_substitute)
      then obtain y where "z |\<in>| finite_pattern_variables ((\<lambda>a. Finite_Variable ((q,True),a)) y)"
        using finite_material_substitute_variable_origin[of z "\<lambda>a. Finite_Variable ((q,True),a)" N] by blast
      then show "fst (fst z) = q" by simp
    qed
  qed
  have st'_nodes: "\<And>nd. nd |\<in>| resolution_nodes st' \<Longrightarrow>
      \<exists>m. m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st) \<and>
        nd = resolution_node_substitute (finite_binding_substitution u) m"
    unfolding st'_def by (rule resolution_state_substitute_members(1))
  have st'_goals: "\<And>g'. g' |\<in>| resolution_pending st' \<Longrightarrow>
      \<exists>g0. g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}) \<and>
        g' = resolution_goal_substitute (finite_binding_substitution u) g0"
    unfolding st'_def by (rule resolution_state_substitute_members(2))
  have clause_node_value: "resolution_value \<theta>' (resolution_node_call (resolution_node_substitute
      (finite_binding_substitution u) (finite_clause_node q e c S))) = x"
    using keep value_new[OF concl_scope] head by (simp add: finite_clause_node_def)
  have old_node_value: "\<And>m. m |\<in>| resolution_nodes st \<Longrightarrow>
      resolution_value \<theta>' (resolution_node_call (resolution_node_substitute (finite_binding_substitution u) m)) =
      resolution_value \<theta> (resolution_node_call m)"
    using keep value_old node_placed by simp
  have support: "resolution_supported_by F P st' \<theta>'"
  proof (rule resolution_supported_byI)
    fix q' r' e' p' assume g': "Resolution_Call_Goal q' r' e' p' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})"
      and eq: "Resolution_Call_Goal q' r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal q' r' e' p0" and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    show "(e',decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow> resolution_before (resolution_node_position nd) q' \<longrightarrow>
        resolution_rank ?P (e',decode_finite_term (resolution_value \<theta>' p')) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta>' (resolution_node_call nd))))"
    proof (cases "g0 |\<in>| finite_clause_goals q e c S")
      case True
      then obtain s p2 where prem: "(s,e',p2) |\<in>| finite_schema_premises S" and q': "q' = q@[s]"
        and p0: "p0 = finite_rename_apart (q,True) p2"
        using new_goals g0c by fastforce
      from pinst prem obtain x2 where x2: "(s,e',x2) |\<in>| H" and i2: "finite_pattern_instance W p2 x2"
        by (fastforce simp: finite_schema_premise_instance_def)
      have v2: "resolution_value \<theta>' p' = x2"
        using keep[of p0] value_new[OF prem_vars[OF prem]] resolution_binding_instance[OF Wf prem_scope[OF prem] i2] p' p0
        by (simp add: \<tau>_def)
      have "(s,e',decode_finite_term x2) \<in> Q" using x2 unfolding HQ[symmetric] by simp
      then have small: "(e',decode_finite_term x2) \<in> positive_meaning ?P \<and>
          resolution_rank ?P (e',decode_finite_term x2) < resolution_rank ?P (e,decode_finite_term x)"
        by (rule smaller)
      show ?thesis
      proof (intro conjI allI impI)
        show "(e',decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning ?P" using small v2 by simp
        fix nd assume nd: "nd |\<in>| resolution_nodes st'" and before: "resolution_before (resolution_node_position nd) q'"
        obtain m where m: "m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st)"
          and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
          using st'_nodes[OF nd] by blast
        have "resolution_node_position m = q \<or> resolution_before (resolution_node_position m) q"
          using before ndm q' resolution_before_child by simp
        then show "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta>' p')) <
            resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta>' (resolution_node_call nd)))"
        proof
          assume "resolution_node_position m = q"
          then have "m = finite_clause_node q e c S" using m no_node_q by auto
          then show ?thesis using small v2 clause_node_value ndm by (simp add: finite_clause_node_def)
        next
          assume mb: "resolution_before (resolution_node_position m) q"
          have "m \<noteq> finite_clause_node q e c S"
            using mb resolution_before_irrefl[of q] by (auto simp: finite_clause_node_def)
          then have mold: "m |\<in>| resolution_nodes st" using m by simp
          show ?thesis using ancestors[OF mold mb] small v2 old_node_value[OF mold] ndm by simp
        qed
      qed
    next
      case False
      with g0 have old: "g0 |\<in>| resolution_pending st" by simp
      have v0: "resolution_value \<theta>' p' = resolution_value \<theta> p0"
        using keep value_old goal_placed[OF old] p' g0c by simp
      have hold0: "(e',decode_finite_term (resolution_value \<theta> p0)) \<in> positive_meaning ?P \<and>
        (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q' \<longrightarrow>
          resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
          resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
        using old_calls old g0c by blast
      show ?thesis
      proof (intro conjI allI impI)
        show "(e',decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning ?P" using hold0 v0 by simp
        fix nd assume nd: "nd |\<in>| resolution_nodes st'" and before: "resolution_before (resolution_node_position nd) q'"
        obtain m where m: "m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st)"
          and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
          using st'_nodes[OF nd] by blast
        have mb: "resolution_before (resolution_node_position m) q'" using before ndm by simp
        have mold: "m |\<in>| resolution_nodes st"
        proof (rule ccontr)
          assume "m |\<notin>| resolution_nodes st"
          with m have "resolution_node_position m = q" by (simp add: finite_clause_node_def)
          then obtain n where "n |\<in>| resolution_nodes st" "resolution_node_position n = q"
            using resolution_pattern_goal_ancestor_node[OF I old] mb g0c by auto
          with no_node_q show False by blast
        qed
        show "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta>' p')) <
            resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta>' (resolution_node_call nd)))"
          using hold0 mold mb v0 old_node_value[OF mold] ndm by simp
      qed
    qed
  next
    fix q' r' M' assume g': "Resolution_Material_Goal q' r' M' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})"
      and eq: "Resolution_Material_Goal q' r' M' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain M0 where g0m: "g0 = Resolution_Material_Goal q' r' M0"
      and M': "M' = finite_material_pattern_substitute (finite_binding_substitution u) M0"
      using eq[symmetric] unfolding resolution_goal_substitute_material by blast
    have "finite_material_pattern_substitute ?\<sigma> M' = finite_material_pattern_substitute ?\<sigma> M0"
      unfolding M' by (rule keep_material)
    moreover have "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M0)"
    proof (cases "g0 |\<in>| finite_clause_goals q e c S")
      case True
      then obtain s N where mat: "(s,N) |\<in>| finite_schema_materials S"
        and M0: "M0 = finite_rename_material (Pair (q,True)) N"
        using new_goals g0m by fastforce
      have sat: "finite_material_satisfied W N" using smat mat by (auto simp: finite_schema_material_satisfied_def)
      have mat_vars: "\<And>a. a |\<in>| finite_material_variables N \<Longrightarrow> a |\<in>| finite_schema_variables S"
        by (meson fsubsetD mat_scope[OF mat])
      have "finite_material_pattern_substitute ?\<sigma> M0 = finite_material_pattern_substitute (\<lambda>a. ?\<sigma> ((q,True),a)) N"
        by (simp add: M0 finite_rename_material_as_substitute finite_material_pattern_substitute_composes)
      also have "\<dots> = finite_material_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<tau> a)) N"
        by (rule finite_material_pattern_substitute_cong) (simp add: \<theta>'_def owned_def mat_vars)
      finally have "finite_material_pattern_substitute ?\<sigma> M0 =
          finite_material_pattern_substitute (\<lambda>a. finite_exact_term_pattern (\<tau> a)) N" .
      then show ?thesis using resolution_binding_material[OF Wf mat_scope[OF mat] sat] by (simp add: \<tau>_def)
    next
      case False
      with g0 have old: "g0 |\<in>| resolution_pending st" by simp
      have "finite_material_pattern_substitute ?\<sigma> M0 =
          finite_material_pattern_substitute (resolution_substitution \<theta>) M0"
        by (rule finite_material_pattern_substitute_cong) (use goal_placed[OF old] agree g0m in simp)
      then show ?thesis using old_material old g0m by simp
    qed
    ultimately show "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M')" by simp
  next
    fix g' z assume g': "g' |\<in>| resolution_pending st'" and z: "z |\<in>| resolution_goal_variables g'"
    obtain g0 where g0: "g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})"
      and eq: "g' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain y where y: "y |\<in>| resolution_goal_variables g0" and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using resolution_goal_substitute_variable_origin z eq by blast
    have "resolution_placed st y \<or> F y \<or> fst (fst y) = q"
    proof (cases "g0 |\<in>| finite_clause_goals q e c S")
      case True
      then show ?thesis using new_vars[OF True y] by blast
    next
      case False
      then have "g0 |\<in>| resolution_pending st" using g0 by simp
      then show ?thesis using goal_placed y by blast
    qed
    with unified_var[OF zy] show "resolution_placed st' z \<or> F z" unfolding placed' by blast
  next
    fix nd z assume nd: "nd |\<in>| resolution_nodes st'" and z: "z |\<in>| finite_pattern_variables (resolution_node_call nd)"
    obtain m where m: "m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st)"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    obtain y where y: "y |\<in>| finite_pattern_variables (resolution_node_call m)"
      and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using finite_substitute_variable_origin z ndm by force
    have "resolution_placed st y \<or> F y \<or> fst (fst y) = q"
    proof (cases "m = finite_clause_node q e c S")
      case True
      with y have "y |\<in>| Pair (q,True) |`| finite_pattern_variables (finite_schema_conclusion S)"
        by (simp add: finite_clause_node_def finite_rename_apart_variables)
      then show ?thesis by auto
    next
      case False
      with m have "m |\<in>| resolution_nodes st" by simp
      then show ?thesis using node_placed y by blast
    qed
    with unified_var[OF zy] show "resolution_placed st' z \<or> F z" unfolding placed' by blast
  qed
  have root_value: "resolution_root_value st' \<theta>' v" if rv: "resolution_root_value st \<theta> v" for v
    unfolding resolution_root_value_def
  proof (intro conjI allI impI)
    fix r' e' p' assume g': "Resolution_Call_Goal [] r' e' p' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})"
      and eq: "Resolution_Call_Goal [] r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal [] r' e' p0"
      and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    have "g0 |\<notin>| finite_clause_goals q e c S" using new_goals g0c by fastforce
    with g0 have old: "g0 |\<in>| resolution_pending st" by simp
    have "resolution_value \<theta>' p' = resolution_value \<theta> p0"
      using keep value_old goal_placed[OF old] p' g0c by simp
    moreover have "resolution_value \<theta> p0 = v" using rv old g0c unfolding resolution_root_value_def by blast
    ultimately show "resolution_value \<theta>' p' = v" by simp
  next
    fix nd assume nd: "nd |\<in>| resolution_nodes st'" and pos: "resolution_node_position nd = []"
    obtain m where m: "m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st)"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    show "resolution_value \<theta>' (resolution_node_call nd) = v"
    proof (cases "m = finite_clause_node q e c S")
      case True
      then have "q = []" using pos ndm by (simp add: finite_clause_node_def)
      then have "resolution_value \<theta> p = v" using rv goal unfolding resolution_root_value_def by auto
      then show ?thesis using clause_node_value ndm True unfolding x_def by simp
    next
      case False
      then have mold: "m |\<in>| resolution_nodes st" using m by simp
      have "resolution_value \<theta> (resolution_node_call m) = v"
        using rv mold pos ndm unfolding resolution_root_value_def by auto
      then show ?thesis using old_node_value[OF mold] ndm by simp
    qed
  qed
  show thesis by (rule that[OF member support root_value])
qed

lemma resolution_call_lifted:
  assumes I: "resolution_invariant P d0 t0 st" and sup: "resolution_supported P st \<theta>"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
  obtains st' \<theta>' where "st' |\<in>| finite_call_successors P st q r e p" "resolution_supported P st' \<theta>'"
proof -
  show thesis
  proof (rule resolution_call_lifted_by[OF I[unfolded resolution_invariant_pattern]
      sup[unfolded resolution_supported_none] resolution_no_foreign goal])
    fix st' \<theta>' assume s: "st' |\<in>| finite_call_successors P st q r e p"
      and u: "resolution_supported_by (\<lambda>_. False) P st' \<theta>'"
    show thesis by (rule that[OF s]) (use u in \<open>simp only: resolution_supported_none\<close>)
  qed
qed

lemma resolution_material_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and solvable: "finite_material_resolution M \<noteq> Material_Waits"
  obtains st' where "st' |\<in>| finite_material_successors st q r M" "resolution_supported_by F P st' \<theta>"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
proof -
  let ?P = "decode_finite_system P"
  let ?\<sigma> = "resolution_substitution \<theta>"
  have ground: "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M)"
    and goal_placed: "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and node_placed: "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
    and old_material: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M)"
    and old_calls: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank ?P (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    using sup goal unfolding resolution_supported_by_def by blast+
  have "resolution_goal_formed (Resolution_Material_Goal q r M)"
    using I goal unfolding resolution_pattern_invariant_def resolution_pattern_goals_placed_def by blast
  then have Mf: "finite_material_formed M" by simp
  obtain Ws where Ws: "finite_material_resolution M = Material_Solutions Ws"
    using solvable by (cases "finite_material_resolution M") auto
  from ground obtain s a e b f where
      fs: "finite_pattern_substitute ?\<sigma> (finite_material_source M) = finite_exact_term_pattern s"
      and fa: "finite_pattern_substitute ?\<sigma> (finite_material_atoms M) = finite_exact_term_pattern a"
      and fe: "finite_pattern_substitute ?\<sigma> (finite_material_edges M) = finite_exact_term_pattern e"
      and fb: "finite_pattern_substitute ?\<sigma> (finite_material_counts M) = finite_exact_term_pattern b"
      and ff: "finite_pattern_substitute ?\<sigma> (finite_material_functions M) = finite_exact_term_pattern f"
      and obs: "finite_material_observation s a e b f"
    by (auto simp: finite_material_ground_satisfied_def)
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
  have "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V = V"
    unfolding V_def by (rule fset_eqI) auto
  then have W_in: "V |\<in>| Ws" using finite_material_resolution_complete[OF Ws Vf sat] by simp
  have "[(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)] |\<in>| finite_material_instance_pairs V M"
    by (rule finite_material_instance_pairs_intro[OF i_s ia ie ib iF])
  then obtain E where E_in: "E |\<in>| finite_material_instance_pairs V M"
    and E_def: "E = [(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)]"
    by blast
  have unifies: "finite_unifies ?\<sigma> E"
    using fs fa fe fb ff by (simp add: E_def finite_pattern_substitute_ground)
  obtain u where u: "finite_unify_pairs E = Some u"
    using unifies finite_unify_pairs_none_iff[of E] by (cases "finite_unify_pairs E") auto
  have mgu: "\<And>y. finite_pattern_substitute ?\<sigma> (finite_binding_substitution u y) = ?\<sigma> y"
    by (rule finite_unify_pairs_most_general[OF u unifies])
  have keep: "\<And>y. resolution_value \<theta> (finite_pattern_substitute (finite_binding_substitution u) y) = resolution_value \<theta> y"
    by (rule resolution_value_unifier) (rule mgu)
  have keep_material: "\<And>N. finite_material_pattern_substitute ?\<sigma>
      (finite_material_pattern_substitute (finite_binding_substitution u) N) = finite_material_pattern_substitute ?\<sigma> N"
    by (simp add: finite_material_pattern_substitute_composes mgu)
  have E_vars: "\<And>z. z \<in> finite_pairs_variables E \<Longrightarrow> resolution_placed st z \<or> F z"
    using goal_placed[OF goal] by (auto simp: E_def finite_material_variables_def)
  have unified_var: "\<And>y z. z |\<in>| finite_pattern_variables (finite_binding_substitution u y) \<Longrightarrow>
      z = y \<or> resolution_placed st z \<or> F z"
    using finite_unifier_variable[OF u] E_vars by blast
  define st' where "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
  have member: "st' |\<in>| finite_material_successors st q r M"
    unfolding st'_def by (rule finite_material_successors_intro[where st=st and q=q and r=r, OF Ws W_in E_in u])
  have placed': "\<And>z. resolution_placed st' z \<longleftrightarrow> resolution_placed st z"
    unfolding st'_def resolution_placed_substitute by (simp add: resolution_placed_def)
  have st'_nodes: "\<And>nd. nd |\<in>| resolution_nodes st' \<Longrightarrow>
      \<exists>m. m |\<in>| resolution_nodes st \<and> nd = resolution_node_substitute (finite_binding_substitution u) m"
    unfolding st'_def by (rule resolution_state_substitute_members(1))
  have st'_goals: "\<And>g'. g' |\<in>| resolution_pending st' \<Longrightarrow>
      \<exists>g0. g0 |\<in>| resolution_pending st \<and> g' = resolution_goal_substitute (finite_binding_substitution u) g0"
  proof -
    fix g' assume "g' |\<in>| resolution_pending st'"
    then obtain g0 where "g0 |\<in>| resolution_pending st |-| {|Resolution_Material_Goal q r M|}"
      "g' = resolution_goal_substitute (finite_binding_substitution u) g0"
      unfolding st'_def using resolution_state_substitute_members(2) by blast
    then show "\<exists>g0. g0 |\<in>| resolution_pending st \<and> g' = resolution_goal_substitute (finite_binding_substitution u) g0"
      by auto
  qed
  have support: "resolution_supported_by F P st' \<theta>"
  proof (rule resolution_supported_byI)
    fix q' r' e' p' assume g': "Resolution_Call_Goal q' r' e' p' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "Resolution_Call_Goal q' r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal q' r' e' p0"
      and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    have hold0: "(e',decode_finite_term (resolution_value \<theta> p0)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_before (resolution_node_position nd) q' \<longrightarrow>
        resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
      using old_calls g0 g0c by blast
    show "(e',decode_finite_term (resolution_value \<theta> p')) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow> resolution_before (resolution_node_position nd) q' \<longrightarrow>
        resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p')) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    proof (intro conjI allI impI)
      show "(e',decode_finite_term (resolution_value \<theta> p')) \<in> positive_meaning ?P" using hold0 keep p' by simp
      fix nd assume nd: "nd |\<in>| resolution_nodes st'" and before: "resolution_before (resolution_node_position nd) q'"
      obtain m where m: "m |\<in>| resolution_nodes st" and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
        using st'_nodes[OF nd] by blast
      have mb: "resolution_before (resolution_node_position m) q'" using before ndm by simp
      have "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
          resolution_rank ?P (resolution_node_site m,decode_finite_term (resolution_value \<theta> (resolution_node_call m)))"
        using hold0 m mb by blast
      then show "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p')) <
          resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
        using ndm keep p' by simp
    qed
  next
    fix q' r' M' assume g': "Resolution_Material_Goal q' r' M' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "Resolution_Material_Goal q' r' M' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain M0 where g0m: "g0 = Resolution_Material_Goal q' r' M0"
      and M': "M' = finite_material_pattern_substitute (finite_binding_substitution u) M0"
      using eq[symmetric] unfolding resolution_goal_substitute_material by blast
    show "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M')"
      using old_material g0 g0m keep_material M' by simp
  next
    fix g' z assume g': "g' |\<in>| resolution_pending st'" and z: "z |\<in>| resolution_goal_variables g'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "g' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain y where y: "y |\<in>| resolution_goal_variables g0" and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using resolution_goal_substitute_variable_origin z eq by blast
    show "resolution_placed st' z \<or> F z" using unified_var[OF zy] goal_placed[OF g0 y] placed' by blast
  next
    fix nd z assume nd: "nd |\<in>| resolution_nodes st'" and z: "z |\<in>| finite_pattern_variables (resolution_node_call nd)"
    obtain m where m: "m |\<in>| resolution_nodes st"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    obtain y where y: "y |\<in>| finite_pattern_variables (resolution_node_call m)"
      and zy: "z |\<in>| finite_pattern_variables (finite_binding_substitution u y)"
      using finite_substitute_variable_origin z ndm by force
    show "resolution_placed st' z \<or> F z" using unified_var[OF zy] node_placed[OF m y] placed' by blast
  qed
  have root_value: "resolution_root_value st' \<theta> v" if rv: "resolution_root_value st \<theta> v" for v
    unfolding resolution_root_value_def
  proof (intro conjI allI impI)
    fix r' e' p' assume g': "Resolution_Call_Goal [] r' e' p' |\<in>| resolution_pending st'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "Resolution_Call_Goal [] r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal [] r' e' p0"
      and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    have "resolution_value \<theta> p0 = v" using rv g0 g0c unfolding resolution_root_value_def by blast
    then show "resolution_value \<theta> p' = v" using keep p' by simp
  next
    fix nd assume nd: "nd |\<in>| resolution_nodes st'" and pos: "resolution_node_position nd = []"
    obtain m where m: "m |\<in>| resolution_nodes st"
      and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
      using st'_nodes[OF nd] by blast
    have "resolution_value \<theta> (resolution_node_call m) = v"
      using rv m pos ndm unfolding resolution_root_value_def by auto
    then show "resolution_value \<theta> (resolution_node_call nd) = v" using keep ndm by simp
  qed
  show thesis by (rule that[OF member support root_value])
qed

lemma resolution_material_lifted:
  assumes I: "resolution_invariant P d0 t0 st" and sup: "resolution_supported P st \<theta>"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and solvable: "finite_material_resolution M \<noteq> Material_Waits"
  obtains st' where "st' |\<in>| finite_material_successors st q r M" "resolution_supported P st' \<theta>"
proof -
  show thesis
  proof (rule resolution_material_lifted_by[OF I[unfolded resolution_invariant_pattern]
      sup[unfolded resolution_supported_none] goal solvable])
    fix st' assume s: "st' |\<in>| finite_material_successors st q r M"
      and u: "resolution_supported_by (\<lambda>_. False) P st' \<theta>"
    show thesis by (rule that[OF s]) (use u in \<open>simp only: resolution_supported_none\<close>)
  qed
qed

lemma resolution_goal_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and g: "g |\<in>| resolution_pending st" and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
  obtains st' \<theta>' where "st' |\<in>| finite_goal_successors P st g" "resolution_supported_by F P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  have goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" using g Resolution_Call_Goal by simp
  show thesis
  proof (rule resolution_call_lifted_by[OF I sup foreign goal])
    fix st' \<theta>' assume s: "st' |\<in>| finite_call_successors P st q r e p" and u: "resolution_supported_by F P st' \<theta>'"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
    have s': "st' |\<in>| finite_goal_successors P st g" using s Resolution_Call_Goal by simp
    show thesis by (rule that[OF s' u w])
  qed
next
  case (Resolution_Material_Goal q r M)
  with kind have solvable: "finite_material_resolution M \<noteq> Material_Waits" by simp
  have goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st" using g Resolution_Material_Goal by simp
  show thesis
  proof (rule resolution_material_lifted_by[OF I sup goal solvable])
    fix st' assume s: "st' |\<in>| finite_material_successors st q r M" and u: "resolution_supported_by F P st' \<theta>"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
    have s': "st' |\<in>| finite_goal_successors P st g" using s Resolution_Material_Goal by simp
    show thesis by (rule that[OF s' u w])
  qed
qed

lemma resolution_goal_lifted:
  assumes I: "resolution_invariant P d0 t0 st" and sup: "resolution_supported P st \<theta>"
    and g: "g |\<in>| resolution_pending st" and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
  obtains st' \<theta>' where "st' |\<in>| finite_goal_successors P st g" "resolution_supported P st' \<theta>'"
proof -
  show thesis
  proof (rule resolution_goal_lifted_by[OF I[unfolded resolution_invariant_pattern]
      sup[unfolded resolution_supported_none] resolution_no_foreign g kind])
    fix st' \<theta>' assume s: "st' |\<in>| finite_goal_successors P st g"
      and u: "resolution_supported_by (\<lambda>_. False) P st' \<theta>'"
    show thesis by (rule that[OF s]) (use u in \<open>simp only: resolution_supported_none\<close>)
  qed
qed

section \<open>The lifting of derivations\<close>

lemma resolution_union_member: "x |\<in>| A \<Longrightarrow> y |\<in>| f x \<Longrightarrow> y |\<in>| ffUnion (fimage f A)"
  by (auto simp: ffUnion.rep_eq fimage.rep_eq)

lemma resolution_union_nonempty: "x |\<in>| A \<Longrightarrow> f x \<noteq> {||} \<Longrightarrow> ffUnion (fimage f A) \<noteq> {||}"
  by (metis all_not_fin_conv resolution_union_member)

text \<open>
  For any selection that never selects a construction and selects a nonempty set of pending goals none of which
  is a waiting material premise, the search from a supported state keeps a branch down to the bound: it
  returns a successful state or a diagnosis. The bound counts the search's steps.
\<close>

text \<open>
  The lifting is stated for a support that may leave the variables F allows unplaced, and keeps the root value:
  the successful state it reaches is supported, and every value the root takes under the start's support it takes
  there under the found one. The ground lifting below is its instance at a support allowing no unplaced variable.
\<close>

theorem finite_resolution_lifting_by:
  assumes selection: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
    and plain: "\<And>st N. sel st \<noteq> Select_Construction N"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
  shows "resolution_pattern_invariant P d \<pi> st \<Longrightarrow> resolution_supported_by F P st \<theta> \<Longrightarrow>
    (\<exists>st' \<theta>'. st' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<and>
      resolution_supported_by F P st' \<theta>' \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
proof (induction n arbitrary: st \<theta>)
  case 0
  show ?case
  proof (cases "resolution_pending st = {||}")
    case True
    then show ?thesis using "0.prems"(2) by auto
  next
    case False
    then show ?thesis by simp
  qed
next
  case (Suc n)
  show ?case
  proof (cases "resolution_pending st = {||}")
    case True
    then show ?thesis using Suc.prems(2) by auto
  next
    case False
    show ?thesis
    proof (cases "sel st")
      case (Select_Construction N)
      with plain show ?thesis by blast
    next
      case Select_None
      with False show ?thesis by simp
    next
      case (Select_Goals G)
      from selection[OF Select_Goals] obtain g where g: "g |\<in>| G" and gp: "g |\<in>| resolution_pending st"
        and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
        by (metis all_not_fin_conv)
      show ?thesis
      proof (rule resolution_goal_lifted_by[OF Suc.prems foreign gp kind])
      fix st' \<theta>' assume succ: "st' |\<in>| finite_goal_successors P st g" and sup': "resolution_supported_by F P st' \<theta>'"
        and rv': "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
      have I': "resolution_pattern_invariant P d \<pi> st'" by (rule resolution_pattern_goal_step[OF Suc.prems(1) gp succ])
      have rec: "(\<exists>st'' \<theta>''. st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st') \<and>
          resolution_supported_by F P st'' \<theta>'' \<and> (\<forall>v. resolution_root_value st' \<theta>' v \<longrightarrow> resolution_root_value st'' \<theta>'' v)) \<or>
        resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st') \<noteq> {||}"
        by (rule Suc.IH[OF I' sup'])
      have unpruned: "\<not> finite_pruned st g" by (rule resolution_supported_by_unpruned[OF Suc.prems(2) gp])
      have ne: "finite_goal_successors P st g \<noteq> {||}" using succ by auto
      define Og where "Og = finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st g"
      have Oeq: "Og = finite_outcome_union (fimage (finite_resolution_search_by sel \<kappa> P n) (finite_goal_successors P st g))"
        unfolding Og_def finite_goal_outcome_def using unpruned ne by (simp add: Let_def)
      have mem: "finite_resolution_search_by sel \<kappa> P n st' |\<in>|
          fimage (finite_resolution_search_by sel \<kappa> P n) (finite_goal_successors P st g)"
        by (rule fimageI[OF succ])
      have memg: "Og |\<in>| fimage (finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st) G"
        unfolding Og_def by (rule fimageI[OF g])
      have eqS: "finite_resolution_search_by sel \<kappa> P (Suc n) st =
          finite_outcome_union (fimage (finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st) G)"
        using False Select_Goals by simp
      from rec show ?thesis
      proof (elim disjE exE conjE)
        fix st'' \<theta>'' assume f: "st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st')"
          and s'': "resolution_supported_by F P st'' \<theta>''"
          and r'': "\<forall>v. resolution_root_value st' \<theta>' v \<longrightarrow> resolution_root_value st'' \<theta>'' v"
        have "st'' |\<in>| resolution_found Og"
          unfolding Oeq finite_outcome_union_fields by (rule resolution_union_member[OF mem]) (rule f)
        then have "st'' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P (Suc n) st)"
          unfolding eqS finite_outcome_union_fields by (rule resolution_union_member[OF memg])
        moreover have "\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st'' \<theta>'' v" using r'' rv' by blast
        ultimately show ?thesis using s'' by blast
      next
        assume "resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st') \<noteq> {||}"
        then have "resolution_diagnoses Og \<noteq> {||}"
          using resolution_union_nonempty[OF mem, of resolution_diagnoses] unfolding Oeq finite_outcome_union_fields by blast
        then show ?thesis unfolding eqS finite_outcome_union_fields
          using resolution_union_nonempty[OF memg, of resolution_diagnoses] by blast
      qed
      qed
    qed
  qed
qed

theorem finite_resolution_lifting:
  assumes selection: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
    and plain: "\<And>st N. sel st \<noteq> Select_Construction N"
  shows "resolution_invariant P d t st \<Longrightarrow> resolution_supported P st \<theta> \<Longrightarrow>
    resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||} \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
proof -
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported P st \<theta>"
  have "(\<exists>st' \<theta>'. st' |\<in>| resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<and>
      resolution_supported_by (\<lambda>_. False) P st' \<theta>' \<and>
      (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}"
    by (rule finite_resolution_lifting_by[OF selection plain resolution_no_foreign
      I[unfolded resolution_invariant_pattern] sup[unfolded resolution_supported_none]])
  then show "resolution_found (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||} \<or>
      resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st) \<noteq> {||}" by auto
qed

section \<open>The plain selection meets the lifting's conditions\<close>

lemma finite_goal_selection_member:
  "g |\<in>| finite_goal_selection G A \<Longrightarrow> g |\<in>| A \<and> (resolution_is_call g \<or> finite_solvable_material_goal g)"
  unfolding finite_goal_selection_def Let_def finite_first_goals_def
  by (cases g) (auto simp: finite_independent_goal_def split: if_splits)

lemma finite_plain_selection_goals:
  "finite_plain_selection G = Select_Goals S \<Longrightarrow> S \<noteq> {||} \<and>
    (\<forall>g. g |\<in>| S \<longrightarrow> g |\<in>| G \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
  unfolding finite_plain_selection_def Let_def using finite_goal_selection_member by (auto split: if_splits)

lemma finite_plain_selection_construction: "finite_plain_selection G \<noteq> Select_Construction N"
  by (simp add: finite_plain_selection_def Let_def)

section \<open>Exactness of the per-call result\<close>

theorem finite_program_resolution_refutation_exact:
  assumes refuted: "finite_program_resolution no_witness_construction P d t n = Finite_Refuted"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
proof
  assume holds: "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  have Pf: "finite_system_formed P"
    using positive_meaning_has_formed_system[OF holds] by (simp add: finite_system_formed_correct)
  have tf: "finite_term_formed t"
    using positive_meaning_formed[OF holds]
    by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
  let ?sel = "\<lambda>st. finite_plain_selection (resolution_pending st)"
  let ?R = "finite_resolution_search no_witness_construction P n (finite_initial_state d t)"
  have R: "?R = finite_resolution_search_by ?sel no_witness_construction P n (finite_initial_state d t)"
    by (simp add: no_witness_search)
  have I0: "resolution_invariant P d t (finite_initial_state d t)" by (rule resolution_initial_invariant[OF Pf tf])
  have S0: "resolution_supported P (finite_initial_state d t) (\<lambda>_. Finite_Payload [])"
    using holds by (simp add: resolution_supported_def finite_initial_state_def resolution_value_ground)
  have "resolution_found ?R \<noteq> {||} \<or> resolution_diagnoses ?R \<noteq> {||}"
    unfolding R by (rule finite_resolution_lifting[OF finite_plain_selection_goals finite_plain_selection_construction I0 S0])
  moreover have diag: "resolution_diagnoses ?R = {||}"
    and C: "ffUnion (fimage finite_state_proofs (resolution_found ?R)) = {||}"
    using refuted finite_program_resolution_certificates[OF Pf tf no_witness_construction_formed, of d n]
    by (auto simp: Let_def split: if_splits)
  ultimately obtain st' where st': "st' |\<in>| resolution_found ?R" by (metis all_not_fin_conv)
  have "resolution_invariant P d t st' \<and> resolution_pending st' = {||}"
    using finite_resolution_search_found[OF no_witness_construction_formed I0] st'
    by (simp add: finite_resolution_search_def)
  then obtain nd where nd: "nd |\<in>| resolution_nodes st'" "resolution_node_position nd = []"
    by (auto simp: resolution_invariant_def resolution_root_held_def)
  then have "finite_node_proof (fcard (resolution_nodes st')) (resolution_nodes st') nd |\<in>| finite_state_proofs st'"
    by (auto simp: finite_state_proofs_def)
  then have "finite_state_proofs st' \<noteq> {||}" by auto
  with st' C show False using resolution_union_nonempty[of st' "resolution_found ?R" finite_state_proofs] by blast
qed

text \<open>
  The contract the route consumes: a resolved call holds, for every witness construction (R3), and a call
  refuted at the empty construction does not.
\<close>

lemmas finite_program_resolution_exact =
  finite_program_resolution_sound(2) finite_program_resolution_refutation_exact

text \<open>The verdict of a result: resolved is true, refuted false, and unresolved no verdict.\<close>

definition finite_resolution_verdict :: "('a,'s,'d,'c) finite_resolution_result \<Rightarrow> bool option" where
  "finite_resolution_verdict r = (case r of Finite_Resolved C \<Rightarrow> Some True | Finite_Refuted \<Rightarrow> Some False
    | Finite_Unresolved D \<Rightarrow> None)"

lemma finite_resolution_verdict_exact:
  assumes "finite_resolution_verdict (finite_program_resolution no_witness_construction P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof (cases "finite_program_resolution no_witness_construction P d t n")
  case (Finite_Resolved C)
  with assms show ?thesis using finite_program_resolution_sound(2)[OF Finite_Resolved]
    by (simp add: finite_resolution_verdict_def)
next
  case Finite_Refuted
  with assms show ?thesis using finite_program_resolution_refutation_exact[OF Finite_Refuted]
    by (simp add: finite_resolution_verdict_def)
next
  case (Finite_Unresolved D)
  with assms show ?thesis by (simp add: finite_resolution_verdict_def)
qed

text \<open>
  Where it answers, the resolver's answer is the program's meaning, so two programs of one meaning, as two
  presentations differing in their clause keys, variable names or sockets are, receive the same answers
  wherever both answer.
\<close>

corollary finite_program_resolution_meaning_determined:
  assumes "positive_meaning (decode_finite_system P) = positive_meaning (decode_finite_system P')"
    and "finite_resolution_verdict (finite_program_resolution no_witness_construction P d t n) = Some b"
    and "finite_resolution_verdict (finite_program_resolution no_witness_construction P' d t m) = Some b'"
  shows "b = b'"
  using finite_resolution_verdict_exact[OF assms(2)] finite_resolution_verdict_exact[OF assms(3)] assms(1) by blast

text \<open>
  A generator of the accepted candidates (@{text Candidate_Generators}): over a finite set of calls, the calls
  the resolver does not refute generate the true ones. It is sound, every generated call a candidate, and
  complete, no true call refuted; it is not tight, an unresolved call being generated true or false.
\<close>

lemma finite_program_resolution_generator:
  "candidate_generator D (\<lambda>q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P))
    (ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D)"
proof (unfold_locales)
  fix q assume "q |\<in>| ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D"
  then show "q |\<in>| D" by simp
next
  fix q assume q: "q |\<in>| D" and holds: "decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  have "finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted"
    using finite_program_resolution_refutation_exact[of P "fst q" "snd q" n] holds
    by (auto simp: decode_finite_call_term_fields)
  with q show "q |\<in>| ffilter (\<lambda>q. finite_program_resolution no_witness_construction P (fst q) (snd q) n \<noteq> Finite_Refuted) D"
    by simp
qed

section \<open>A pattern goal\<close>

text \<open>
  A search started at a pattern goal (@{const finite_pattern_state}) keeps the lifting of every true instance of
  the pattern, when the pattern's variables are no program variables: it returns a diagnosis, or a found state
  whose root call has, under some support, the instance's value. Every formed instance of a found root call is
  certified: the found state substituted by the instance's values keeps the branch invariant, so the certificate of
  its root node is accepted at the instance. The instances of the found root calls therefore generate the true
  instances of the pattern (@{text Candidate_Generators}): tight by that acceptance, complete where the search
  reports no diagnosis.
\<close>

lemma resolution_value_instance:
  "resolution_value \<theta> (finite_pattern_substitute \<rho> p) = resolution_value (\<lambda>z. resolution_value \<theta> (\<rho> z)) p"
proof -
  have unfolded: "resolution_value \<theta> (finite_pattern_substitute \<rho> p) =
      finite_residual_term (finite_pattern_substitute (resolution_substitution \<theta>) (finite_pattern_substitute \<rho> p))"
    by (rule resolution_value_def)
  have composed: "finite_pattern_substitute (resolution_substitution \<theta>) (finite_pattern_substitute \<rho> p) =
      finite_pattern_substitute (\<lambda>z. finite_exact_term_pattern (resolution_value \<theta> (\<rho> z))) p"
    by (simp add: finite_pattern_substitute_composes resolution_value_exact)
  show ?thesis unfolding unfolded composed by (rule finite_residual_substitute_value)
qed

theorem finite_resolution_pattern_lifting:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and foreign: "\<And>z. z |\<in>| finite_pattern_variables \<pi> \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and holds: "(d,decode_finite_term (resolution_value \<theta> \<pi>)) \<in> positive_meaning (decode_finite_system P)"
  shows "resolution_diagnoses (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) \<noteq> {||} \<or>
    (\<exists>st nd \<theta>' \<rho>. st |\<in>| resolution_found (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) \<and>
      nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = [] \<and> resolution_node_site nd = d \<and>
      resolution_node_call nd = finite_pattern_substitute \<rho> \<pi> \<and>
      resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>)"
proof -
  let ?sel = "\<lambda>st. finite_plain_selection (resolution_pending st)"
  let ?st0 = "finite_pattern_state d \<pi> :: ('a,'b,'c,'d) resolution_state"
  let ?R = "finite_resolution_search no_witness_construction P n ?st0"
  have R: "?R = finite_resolution_search_by ?sel no_witness_construction P n ?st0" by (simp add: no_witness_search)
  have I0: "resolution_pattern_invariant P d \<pi> ?st0" by (rule resolution_pattern_initial_invariant[OF Pf \<pi>f])
  have S0: "resolution_supported_by (\<lambda>z. snd z |\<notin>| finite_program_variables P) P ?st0 \<theta>"
    unfolding resolution_supported_by_def using holds foreign by (auto simp: finite_pattern_state_def)
  have V0: "resolution_root_value ?st0 \<theta> (resolution_value \<theta> \<pi>)"
    by (auto simp: resolution_root_value_def finite_pattern_state_def)
  have lifted: "(\<exists>st' \<theta>'. st' |\<in>| resolution_found ?R \<and>
      resolution_supported_by (\<lambda>z. snd z |\<notin>| finite_program_variables P) P st' \<theta>' \<and>
      (\<forall>v. resolution_root_value ?st0 \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)) \<or>
    resolution_diagnoses ?R \<noteq> {||}"
  proof -
    have F0: "\<And>z. snd z |\<notin>| finite_program_variables P \<Longrightarrow> snd z |\<notin>| finite_program_variables P" by simp
    note L = finite_resolution_lifting_by[where sel="\<lambda>st. finite_plain_selection (resolution_pending st)",
      OF finite_plain_selection_goals finite_plain_selection_construction F0 I0 S0]
    show ?thesis unfolding R by (rule L) simp_all
  qed
  from lifted show ?thesis
  proof (elim disjE exE conjE)
    fix st' \<theta>' assume found: "st' |\<in>| resolution_found ?R"
      and rv: "\<forall>v. resolution_root_value ?st0 \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v"
    have "resolution_pattern_invariant P d \<pi> st' \<and> resolution_pending st' = {||}"
      using finite_resolution_pattern_search_found[OF no_witness_construction_formed I0] found
      by (simp add: finite_resolution_search_def)
    then have I: "resolution_pattern_invariant P d \<pi> st'" and closed: "resolution_pending st' = {||}" by blast+
    obtain nd where nd: "nd |\<in>| resolution_nodes st'" "resolution_node_position nd = []"
      using I closed by (auto simp: resolution_pattern_invariant_def resolution_pattern_root_held_def)
    obtain \<rho> where site: "resolution_node_site nd = d" and call: "resolution_node_call nd = finite_pattern_substitute \<rho> \<pi>"
      using I nd unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast
    have "resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>"
      using rv V0 nd unfolding resolution_root_value_def by blast
    then show ?thesis using found nd site call by blast
  next
    assume "resolution_diagnoses ?R \<noteq> {||}"
    then show ?thesis by blast
  qed
qed

definition finite_pattern_answer ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow>
      ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_pattern_answer \<kappa> P d \<pi> n x \<longleftrightarrow> finite_term_formed x \<and>
    (\<exists>st nd \<theta>. st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d \<pi>)) \<and>
      nd |\<in>| resolution_nodes st \<and> resolution_node_position nd = [] \<and> resolution_value \<theta> (resolution_node_call nd) = x)"

theorem finite_pattern_answer_true:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and \<kappa>: "finite_witness_construction_formed \<kappa>" and answer: "finite_pattern_answer \<kappa> P d \<pi> n x"
  shows "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
proof -
  obtain st nd \<theta> where found: "st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d \<pi>))"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = []"
    and x: "resolution_value \<theta> (resolution_node_call nd) = x" and xf: "finite_term_formed x"
    using answer unfolding finite_pattern_answer_def by blast
  have "resolution_pattern_invariant P d \<pi> st \<and> resolution_pending st = {||}"
    using finite_resolution_pattern_search_found[OF \<kappa> resolution_pattern_initial_invariant[OF Pf \<pi>f]] found
    by (simp add: finite_resolution_search_def)
  then have I: "resolution_pattern_invariant P d \<pi> st" and closed: "resolution_pending st = {||}" by blast+
  obtain \<rho> where site: "resolution_node_site nd = d" and call: "resolution_node_call nd = finite_pattern_substitute \<rho> \<pi>"
    using I nd unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast
  have eq: "finite_pattern_substitute (resolution_substitution \<theta>) (resolution_node_call nd) = finite_exact_term_pattern x"
    using resolution_value_exact[of \<theta> "resolution_node_call nd"] x by simp
  have vars_formed: "finite_term_formed (\<theta> z)" if z: "z |\<in>| finite_pattern_variables (resolution_node_call nd)" for z
    using finite_pattern_substitute_formed_variable[of "resolution_substitution \<theta>" "resolution_node_call nd" z] eq xf z
    by (simp add: finite_exact_pattern_formed)
  define \<sigma> where "\<sigma> = resolution_substitution (\<lambda>z. if finite_term_formed (\<theta> z) then \<theta> z else Finite_Payload [])"
  have \<sigma>f: "\<And>z. finite_pattern_formed (\<sigma> z)" by (simp add: \<sigma>_def octets_formed_def finite_exact_pattern_formed)
  have \<sigma>call: "finite_pattern_substitute \<sigma> (resolution_node_call nd) = finite_exact_term_pattern x"
  proof -
    have "finite_pattern_substitute \<sigma> (resolution_node_call nd) =
        finite_pattern_substitute (resolution_substitution \<theta>) (resolution_node_call nd)"
      by (rule finite_pattern_substitute_cong) (simp add: \<sigma>_def vars_formed)
    then show ?thesis using eq by simp
  qed
  let ?st = "resolution_state_substitute \<sigma> st"
  have I': "resolution_pattern_invariant P d \<pi> ?st" by (rule resolution_pattern_invariant_substitute[OF I \<sigma>f])
  have closed': "resolution_pending ?st = {||}" using closed by simp
  have nd': "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes ?st"
    unfolding resolution_state_substitute_fields by (rule fimageI[OF nd(1)])
  have "fcard (resolution_subtree (resolution_nodes ?st) (resolution_node_substitute \<sigma> nd)) \<le> fcard (resolution_nodes ?st)"
    by (rule fcard_mono) auto
  from finite_node_proof_pattern_accepted[OF I' closed' nd' this]
  have "finite_checks_schema_proof P (finite_node_proof (fcard (resolution_nodes ?st)) (resolution_nodes ?st)
      (resolution_node_substitute \<sigma> nd)) d x"
    by (simp add: site \<sigma>call)
  then have "checks_schema_proof (decode_finite_system P) (decode_finite_proof (finite_node_proof
      (fcard (resolution_nodes ?st)) (resolution_nodes ?st) (resolution_node_substitute \<sigma> nd))) d (decode_finite_term x)"
    by (simp only: finite_checks_schema_proof_exact)
  then have holds: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P)" by (rule schema_proof_sound)
  have "resolution_value (\<lambda>z. resolution_value \<theta> (\<rho> z)) \<pi> = x" using x call by (simp add: resolution_value_instance)
  then show ?thesis using holds by blast
qed

text \<open>
  The goal-level generator of item 5: over any finite space of candidate terms, the formed instances of the found
  root calls generate the true instances of the pattern. It is tight, every generated candidate true, by the
  acceptance of the substituted certificates (@{text finite_pattern_answer_true}); its soundness in the locale's
  sense is membership of the space, which the filter gives; it is complete where the search reports no diagnosis, by
  the answer-preserving lifting (@{text finite_resolution_pattern_lifting}).
\<close>

theorem finite_pattern_resolution_generator:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and foreign: "\<And>z. z |\<in>| finite_pattern_variables \<pi> \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and complete: "resolution_diagnoses (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>)) = {||}"
  shows "tight_candidate_generator D
    (\<lambda>x. (d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x))
    (ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D)"
proof (unfold_locales)
  fix x assume "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D"
  then show "x |\<in>| D" by simp
next
  fix x assume member: "x |\<in>| D"
    and accepted: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
  then obtain \<theta> where holds: "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P)"
    and x: "resolution_value \<theta> \<pi> = x" by blast
  have xf: "finite_term_formed x"
    using positive_meaning_formed[OF holds]
    by (auto simp: schema_call_formed_def pattern_accepts_def finite_term_formed_correct)
  have holds': "(d,decode_finite_term (resolution_value \<theta> \<pi>)) \<in> positive_meaning (decode_finite_system P)"
    using holds x by simp
  obtain st nd \<theta>' where "st |\<in>| resolution_found (finite_resolution_search no_witness_construction P n (finite_pattern_state d \<pi>))"
    "nd |\<in>| resolution_nodes st" "resolution_node_position nd = []"
    "resolution_value \<theta>' (resolution_node_call nd) = resolution_value \<theta> \<pi>"
    using finite_resolution_pattern_lifting[OF Pf \<pi>f foreign holds', of n] complete by blast
  then have "finite_pattern_answer no_witness_construction P d \<pi> n x"
    unfolding finite_pattern_answer_def using xf x by blast
  with member show "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D" by simp
next
  fix x assume "x |\<in>| ffilter (finite_pattern_answer no_witness_construction P d \<pi> n) D"
  then have "finite_pattern_answer no_witness_construction P d \<pi> n x" by simp
  then show "(d,decode_finite_term x) \<in> positive_meaning (decode_finite_system P) \<and> (\<exists>\<theta>. resolution_value \<theta> \<pi> = x)"
    by (rule finite_pattern_answer_true[OF Pf \<pi>f no_witness_construction_formed])
qed

section \<open>The demand-level form\<close>

lemma fimage_fst_filter_graph:
  "fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)) = ffilter (\<lambda>q. R (f q)) D"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)) \<longleftrightarrow>
      x |\<in>| ffilter (\<lambda>q. R (f q)) D"
  proof
    assume "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))"
    then show "x |\<in>| ffilter (\<lambda>q. R (f q)) D" by (auto simp: fimage.rep_eq ffilter.rep_eq)
  next
    assume "x |\<in>| ffilter (\<lambda>q. R (f q)) D"
    then have "(x,f x) |\<in>| ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D)" by (auto intro: fimageI)
    then have "fst (x,f x) |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))" by (rule fimageI)
    then show "x |\<in>| fimage fst (ffilter (\<lambda>(q,v). R v) (fimage (\<lambda>q. (q,f q)) D))" by simp
  qed
qed

text \<open>
  A demand is resolved when the program is formed and every call of it is resolved or refuted; the result is
  then the set of resolved calls, in the shape of @{const finite_program_evaluation}, and nothing otherwise.
\<close>

definition finite_demand_resolution ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> nat \<Rightarrow>
      ('d\<times>finite_factor_term) fset option" where
  "finite_demand_resolution P D n = (let V = fimage (\<lambda>q. (q,finite_resolution_verdict
      (finite_program_resolution no_witness_construction P (fst q) (snd q) n))) D in
    if finite_system_formed P \<and> fBall V (\<lambda>(q,v). v \<noteq> None)
    then Some (fimage fst (ffilter (\<lambda>(q,v). v = Some True) V)) else None)"

theorem finite_demand_resolution_exact:
  assumes result: "finite_demand_resolution P D n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  let ?v = "\<lambda>q. finite_resolution_verdict (finite_program_resolution no_witness_construction P (fst q) (snd q) n)"
  from result have Pf: "finite_system_formed P" and answered: "\<And>q. q |\<in>| D \<Longrightarrow> ?v q \<noteq> None"
    and A: "A = fimage fst (ffilter (\<lambda>(q,v). v = Some True) (fimage (\<lambda>q. (q,?v q)) D))"
    by (auto simp: finite_demand_resolution_def Let_def split: if_splits)
  show "schema_system_formed (decode_finite_system P)" using Pf by (simp add: finite_system_formed_correct)
  have key: "\<And>q. q |\<in>| D \<Longrightarrow>
      ?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    fix q assume q: "q |\<in>| D"
    obtain b where b: "?v q = Some b" using answered[OF q] by auto
    have "b \<longleftrightarrow> (fst q,decode_finite_term (snd q)) \<in> positive_meaning (decode_finite_system P)"
      by (rule finite_resolution_verdict_exact[OF b])
    then show "?v q = Some True \<longleftrightarrow> decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
      using b by (simp add: decode_finite_call_term_fields)
  qed
  show "fset A = {q\<in>fset D. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    unfolding A fimage_fst_filter_graph ffilter.rep_eq Set.filter_eq
    by (rule Collect_cong) (simp add: key cong: conj_cong)
qed

text \<open>
  Where both answer, the resolver and @{const finite_program_evaluation} agree: an equation of results, both
  being exact at the demand.
\<close>

theorem finite_demand_resolution_evaluation:
  assumes "finite_demand_resolution P D n = Some A" and "finite_program_evaluation P D = Some B"
  shows "A = B"
proof -
  have "fset A = fset B"
    using finite_demand_resolution_exact(2)[OF assms(1)] finite_program_evaluation_exact(2)[OF assms(2)] by simp
  then show ?thesis by (simp only: fset_inject)
qed

section \<open>The native form\<close>

text \<open>
  The native form reads a program and its requested calls, as @{text native_call_evaluation} does, with the
  bound: each requested call with its result (its certificates or its diagnosis) and the demand-level answer.
  Native sockets are ordered lexicographically (@{text List_Lexorder}), which orders which goal is worked
  first and never which alternative is kept.
\<close>

type_synonym native_resolution_result =
  "(local_address,local_address,local_address option definition_site,local_address) finite_resolution_result"

definition native_call_resolution ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      nat \<Rightarrow> ((local_address option definition_site\<times>finite_factor_term)\<times>native_resolution_result) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_call_resolution P R n =
    (fimage (\<lambda>q. (q,finite_program_resolution no_witness_construction P (fst q) (snd q) n)) R,
     finite_demand_resolution P R n)"

theorem native_call_resolution_exact:
  assumes result: "native_call_resolution P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,Finite_Refuted) |\<in>| T \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
proof -
  have T: "T = fimage (\<lambda>q. (q,finite_program_resolution no_witness_construction P (fst q) (snd q) n)) R"
    and A: "A = finite_demand_resolution P R n"
    using result by (simp_all add: native_call_resolution_def)
  show "fimage fst T = R" unfolding T fset.map_comp by (simp add: comp_def)
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,Finite_Resolved C) |\<in>| T"
    then have res: "finite_program_resolution no_witness_construction P (fst q) (snd q) n = Finite_Resolved C"
      unfolding T by auto
    show "C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
        decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
      using finite_program_resolution_sound[OF res] finite_program_resolution_accepted[OF res]
      by (simp add: decode_finite_call_term_fields)
  qed
  show "(q,Finite_Refuted) |\<in>| T \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,Finite_Refuted) |\<in>| T"
    then have res: "finite_program_resolution no_witness_construction P (fst q) (snd q) n = Finite_Refuted"
      unfolding T by auto
    show "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
      using finite_program_resolution_refutation_exact[OF res] by (simp add: decode_finite_call_term_fields)
  qed
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  proof -
    assume "A = Some B"
    then have res: "finite_demand_resolution P R n = Some B" using A by simp
    show "schema_system_formed (decode_finite_system P) \<and>
        fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
      using finite_demand_resolution_exact[OF res] by simp
  qed
qed

end
