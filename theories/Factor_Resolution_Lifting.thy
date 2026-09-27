theory Factor_Resolution_Lifting
  imports Factor_Resolution_Acceptance Factor_Finite_Program_Evaluation Factor_Executable_Packages
    Candidate_Generators Inference_Rounds Ordered_Finite_Terms Finite_Pattern_Tuples Finite_Functional_Enumeration
    "HOL-Library.List_Lexorder"
begin

text \<open>
  The lifting of a supported state (R4 of DECISIONS.md "The native evaluator constructs the missing witnesses by
  resolution", items 5 and 6): the round of a true call, the ground value of a pattern under a support, positions,
  the support of a state, the successors a step constructs and the supported successor of a supported goal. With
  them stand the views (R5's producers' outputs), the committed search (R5, "Committed choice, for refusals") and its
  lifting at a focused barred support over the selection parameter, which read nothing above them: the completeness
  of the resolving evaluator reads R4's search as the committed search at no commitment
  (@{text finite_committed_search_by_plain}).
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


text \<open>
  A support at a focus and a barred set asks truth, ranks and satisfaction of the pending goals inside the focus
  only, and ranks only against the ancestors whose positions are not barred; placement is asked of every goal and
  node. The committed search solves the goals of a focus, and bars the nodes present at a commitment
  (@{text Factor_Resolution_Commitments}). The support of the whole state is its instance at no focus and no
  barred position (@{text resolution_supported_by_at}).
\<close>

definition resolution_focused :: "'s list option \<Rightarrow> 's list \<Rightarrow> bool" where
  "resolution_focused Fo q \<longleftrightarrow> (case Fo of None \<Rightarrow> True | Some f \<Rightarrow> take (length f) q = f)"

lemma resolution_focused_some [simp]: "resolution_focused (Some f) q \<longleftrightarrow> take (length f) q = f"
  by (simp add: resolution_focused_def)

lemma resolution_focused_within:
  assumes focus: "resolution_focused F q" and within: "take (length q) q' = q"
  shows "resolution_focused F q'"
proof (cases F)
  case None
  then show ?thesis by (simp add: resolution_focused_def)
next
  case (Some f)
  with focus have f: "take (length f) q = f" by simp
  then have le: "length f \<le> length q" by (metis length_take min.cobounded1)
  have "take (length f) q' = take (length f) (take (length q) q')" using le by (simp add: min.absorb1)
  also have "\<dots> = f" using within f by simp
  finally show ?thesis using Some by simp
qed

lemma resolution_focused_none [simp]: "resolution_focused None q"
  by (simp add: resolution_focused_def)

definition resolution_supported_at ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow> bool" where
  "resolution_supported_at F Fo B P st \<theta> \<longleftrightarrow>
    (\<forall>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<longrightarrow> resolution_focused Fo q \<longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))) \<and>
    (\<forall>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<longrightarrow> resolution_focused Fo q \<longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)) \<and>
    (\<forall>g z. g |\<in>| resolution_pending st \<longrightarrow> z |\<in>| resolution_goal_variables g \<longrightarrow> resolution_placed st z \<or> F z) \<and>
    (\<forall>nd z. nd |\<in>| resolution_nodes st \<longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<longrightarrow>
      resolution_placed st z \<or> F z)"

lemma resolution_supported_by_at:
  "resolution_supported_by F P st \<theta> \<longleftrightarrow> resolution_supported_at F None {||} P st \<theta>"
  by (simp add: resolution_supported_by_def resolution_supported_at_def)

lemma resolution_supported_atI:
  assumes "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning (decode_finite_system P) \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank (decode_finite_system P)
          (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    and "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
  shows "resolution_supported_at F Fo B P st \<theta>"
  using assms unfolding resolution_supported_at_def by blast

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

lemma resolution_call_lifted_at:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_at F Fo B P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" and focus: "resolution_focused Fo q"
  obtains st' \<theta>' where "st' |\<in>| finite_call_successors P st q r e p" "resolution_supported_at F Fo B P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof -
  let ?P = "decode_finite_system P"
  define x where "x = resolution_value \<theta> p"
  have holds: "(e,decode_finite_term x) \<in> positive_meaning ?P"
    and ancestors: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd |\<notin>| B \<Longrightarrow>
      resolution_before (resolution_node_position nd) q \<Longrightarrow>
      resolution_rank ?P (e,decode_finite_term x) < resolution_rank ?P (resolution_node_site nd,
        decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
    using sup goal focus unfolding x_def resolution_supported_at_def by blast+
  have goal_placed: "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and node_placed: "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
    and old_material: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute (resolution_substitution \<theta>) M)"
    and old_calls: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank ?P (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    using sup unfolding resolution_supported_at_def by blast+
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
  proof -
    fix z
    have pos: "resolution_node_position (finite_clause_node q e c S) = q" by (simp add: finite_clause_node_def)
    have "resolution_placed st' z \<longleftrightarrow>
        (\<exists>nd. nd |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st) \<and>
          resolution_node_position nd = fst (fst z))"
      unfolding st'_def resolution_placed_substitute resolution_placed_state by (rule refl)
    also have "\<dots> \<longleftrightarrow> resolution_placed st z \<or> fst (fst z) = q"
      unfolding resolution_placed_def using pos by auto
    finally show "resolution_placed st' z \<longleftrightarrow> resolution_placed st z \<or> fst (fst z) = q" .
  qed
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
  have support: "resolution_supported_at F Fo B P st' \<theta>'"
  proof (rule resolution_supported_atI)
    fix q' r' e' p' assume g': "Resolution_Call_Goal q' r' e' p' |\<in>| resolution_pending st'"
      and f': "resolution_focused Fo q'"
    obtain g0 where g0: "g0 |\<in>| finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})"
      and eq: "Resolution_Call_Goal q' r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal q' r' e' p0" and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    show "(e',decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q' \<longrightarrow>
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
        fix nd assume nd: "nd |\<in>| resolution_nodes st'" and nb: "resolution_node_position nd |\<notin>| B"
          and before: "resolution_before (resolution_node_position nd) q'"
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
          have mB: "resolution_node_position m |\<notin>| B" using nb ndm by simp
          show ?thesis using ancestors[OF mold mB mb] small v2 old_node_value[OF mold] ndm by simp
        qed
      qed
    next
      case False
      with g0 have old: "g0 |\<in>| resolution_pending st" by simp
      have v0: "resolution_value \<theta>' p' = resolution_value \<theta> p0"
        using keep value_old goal_placed[OF old] p' g0c by simp
      have hold0: "(e',decode_finite_term (resolution_value \<theta> p0)) \<in> positive_meaning ?P \<and>
        (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
          resolution_before (resolution_node_position nd) q' \<longrightarrow>
          resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
          resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
        using old_calls old g0c f' by blast
      show ?thesis
      proof (intro conjI allI impI)
        show "(e',decode_finite_term (resolution_value \<theta>' p')) \<in> positive_meaning ?P" using hold0 v0 by simp
        fix nd assume nd: "nd |\<in>| resolution_nodes st'" and nb: "resolution_node_position nd |\<notin>| B"
          and before: "resolution_before (resolution_node_position nd) q'"
        obtain m where m: "m |\<in>| finsert (finite_clause_node q e c S) (resolution_nodes st)"
          and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
          using st'_nodes[OF nd] by blast
        have mB: "resolution_node_position m |\<notin>| B" using nb ndm by simp
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
          using hold0 mold mB mb v0 old_node_value[OF mold] ndm by simp
      qed
    qed
  next
    fix q' r' M' assume g': "Resolution_Material_Goal q' r' M' |\<in>| resolution_pending st'"
      and f': "resolution_focused Fo q'"
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
      then show ?thesis using old_material old g0m f' by simp
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

lemma resolution_call_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
  obtains st' \<theta>' where "st' |\<in>| finite_call_successors P st q r e p" "resolution_supported_by F P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof -
  show thesis
  proof (rule resolution_call_lifted_at[OF I sup[unfolded resolution_supported_by_at] foreign goal
      resolution_focused_none])
    fix st' \<theta>' assume s: "st' |\<in>| finite_call_successors P st q r e p"
      and u: "resolution_supported_at F None {||} P st' \<theta>'"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
    show thesis by (rule that[OF s _ w]) (use u in \<open>simp only: resolution_supported_by_at\<close>)
  qed
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

lemma resolution_material_lifted_at:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_at F Fo B P st \<theta>"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st" and focus: "resolution_focused Fo q"
    and solvable: "finite_material_resolution M \<noteq> Material_Waits"
  obtains st' where "st' |\<in>| finite_material_successors st q r M" "resolution_supported_at F Fo B P st' \<theta>"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
proof -
  let ?P = "decode_finite_system P"
  let ?\<sigma> = "resolution_substitution \<theta>"
  have ground: "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M)"
    and goal_placed: "\<And>g z. g |\<in>| resolution_pending st \<Longrightarrow> z |\<in>| resolution_goal_variables g \<Longrightarrow> resolution_placed st z \<or> F z"
    and node_placed: "\<And>nd z. nd |\<in>| resolution_nodes st \<Longrightarrow> z |\<in>| finite_pattern_variables (resolution_node_call nd) \<Longrightarrow>
      resolution_placed st z \<or> F z"
    and old_material: "\<And>q r M. Resolution_Material_Goal q r M |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M)"
    and old_calls: "\<And>q r e p. Resolution_Call_Goal q r e p |\<in>| resolution_pending st \<Longrightarrow> resolution_focused Fo q \<Longrightarrow>
      (e,decode_finite_term (resolution_value \<theta> p)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q \<longrightarrow>
        resolution_rank ?P (e,decode_finite_term (resolution_value \<theta> p)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    using sup goal focus unfolding resolution_supported_at_def by blast+
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
  have support: "resolution_supported_at F Fo B P st' \<theta>"
  proof (rule resolution_supported_atI)
    fix q' r' e' p' assume g': "Resolution_Call_Goal q' r' e' p' |\<in>| resolution_pending st'"
      and f': "resolution_focused Fo q'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "Resolution_Call_Goal q' r' e' p' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain p0 where g0c: "g0 = Resolution_Call_Goal q' r' e' p0"
      and p': "p' = finite_pattern_substitute (finite_binding_substitution u) p0"
      using eq[symmetric] unfolding resolution_goal_substitute_call by blast
    have hold0: "(e',decode_finite_term (resolution_value \<theta> p0)) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q' \<longrightarrow>
        resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
      using old_calls g0 g0c f' by blast
    show "(e',decode_finite_term (resolution_value \<theta> p')) \<in> positive_meaning ?P \<and>
      (\<forall>nd. nd |\<in>| resolution_nodes st' \<longrightarrow> resolution_node_position nd |\<notin>| B \<longrightarrow>
        resolution_before (resolution_node_position nd) q' \<longrightarrow>
        resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p')) <
        resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd))))"
    proof (intro conjI allI impI)
      show "(e',decode_finite_term (resolution_value \<theta> p')) \<in> positive_meaning ?P" using hold0 keep p' by simp
      fix nd assume nd: "nd |\<in>| resolution_nodes st'" and nb: "resolution_node_position nd |\<notin>| B"
        and before: "resolution_before (resolution_node_position nd) q'"
      obtain m where m: "m |\<in>| resolution_nodes st" and ndm: "nd = resolution_node_substitute (finite_binding_substitution u) m"
        using st'_nodes[OF nd] by blast
      have mb: "resolution_before (resolution_node_position m) q'" using before ndm by simp
      have "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p0)) <
          resolution_rank ?P (resolution_node_site m,decode_finite_term (resolution_value \<theta> (resolution_node_call m)))"
        using hold0 m mb nb ndm by auto
      then show "resolution_rank ?P (e',decode_finite_term (resolution_value \<theta> p')) <
          resolution_rank ?P (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
        using ndm keep p' by simp
    qed
  next
    fix q' r' M' assume g': "Resolution_Material_Goal q' r' M' |\<in>| resolution_pending st'"
      and f': "resolution_focused Fo q'"
    obtain g0 where g0: "g0 |\<in>| resolution_pending st"
      and eq: "Resolution_Material_Goal q' r' M' = resolution_goal_substitute (finite_binding_substitution u) g0"
      using st'_goals[OF g'] by blast
    obtain M0 where g0m: "g0 = Resolution_Material_Goal q' r' M0"
      and M': "M' = finite_material_pattern_substitute (finite_binding_substitution u) M0"
      using eq[symmetric] unfolding resolution_goal_substitute_material by blast
    show "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M')"
      using old_material g0 g0m keep_material M' f' by simp
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

lemma resolution_material_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and solvable: "finite_material_resolution M \<noteq> Material_Waits"
  obtains st' where "st' |\<in>| finite_material_successors st q r M" "resolution_supported_by F P st' \<theta>"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
proof -
  show thesis
  proof (rule resolution_material_lifted_at[OF I sup[unfolded resolution_supported_by_at] goal
      resolution_focused_none solvable])
    fix st' assume s: "st' |\<in>| finite_material_successors st q r M"
      and u: "resolution_supported_at F None {||} P st' \<theta>"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
    show thesis by (rule that[OF s _ w]) (use u in \<open>simp only: resolution_supported_by_at\<close>)
  qed
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

text \<open>
  A support constrains each pending goal and node alone, so a state with fewer pending goals and the same nodes keeps
  it, at any focus and barred set, and keeps the root value: the case of a ground call closed by reuse (F3).
\<close>

lemma resolution_supported_at_fewer:
  assumes sup: "resolution_supported_at F Fo B P st \<theta>"
    and pend: "resolution_pending st' |\<subseteq>| resolution_pending st" and nodes: "resolution_nodes st' = resolution_nodes st"
  shows "resolution_supported_at F Fo B P st' \<theta>"
proof -
  have sub: "\<And>h. h |\<in>| resolution_pending st' \<Longrightarrow> h |\<in>| resolution_pending st"
    by (rule fsubsetD[OF pend])
  show ?thesis using sup sub nodes unfolding resolution_supported_at_def resolution_placed_def by blast
qed

lemma resolution_root_value_fewer:
  assumes "resolution_root_value st \<theta> v"
    and "resolution_pending st' |\<subseteq>| resolution_pending st" and "resolution_nodes st' = resolution_nodes st"
  shows "resolution_root_value st' \<theta> v"
  using assms unfolding resolution_root_value_def by (auto simp: less_eq_fset.rep_eq)

lemma resolution_goal_lifted_at:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_at F Fo B P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and g: "g |\<in>| resolution_pending st" and focus: "resolution_focused Fo (resolution_goal_position g)"
    and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
  obtains st' \<theta>' where "st' |\<in>| finite_goal_successors P st g" "resolution_supported_at F Fo B P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  have goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" using g Resolution_Call_Goal by simp
  have fq: "resolution_focused Fo q" using focus Resolution_Call_Goal by simp
  show thesis
  proof (cases "finite_reusable st g")
    case True
    have s': "finite_goal_closed st g |\<in>| finite_goal_successors P st g" by (simp add: finite_reusable_successors[OF True])
    have fewer: "resolution_pending (finite_goal_closed st g) |\<subseteq>| resolution_pending st"
      "resolution_nodes (finite_goal_closed st g) = resolution_nodes st"
      by (auto simp: finite_goal_closed_def less_eq_fset.rep_eq resolution_fset_simps)
    show thesis
      by (rule that[OF s' resolution_supported_at_fewer[OF sup fewer]]) (rule resolution_root_value_fewer[OF _ fewer])
  next
    case False
    show thesis
    proof (rule resolution_call_lifted_at[OF I sup foreign goal fq])
      fix st' \<theta>' assume s: "st' |\<in>| finite_call_successors P st q r e p" and u: "resolution_supported_at F Fo B P st' \<theta>'"
        and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
      have s': "st' |\<in>| finite_goal_successors P st g" using s Resolution_Call_Goal False by simp
      show thesis by (rule that[OF s' u w])
    qed
  qed
next
  case (Resolution_Material_Goal q r M)
  with kind have solvable: "finite_material_resolution M \<noteq> Material_Waits" by simp
  have goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st" using g Resolution_Material_Goal by simp
  have fq: "resolution_focused Fo q" using focus Resolution_Material_Goal by simp
  show thesis
  proof (rule resolution_material_lifted_at[OF I sup goal fq solvable])
    fix st' assume s: "st' |\<in>| finite_material_successors st q r M" and u: "resolution_supported_at F Fo B P st' \<theta>"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta> v"
    have s': "st' |\<in>| finite_goal_successors P st g" using s Resolution_Material_Goal by simp
    show thesis by (rule that[OF s' u w])
  qed
qed

lemma resolution_goal_lifted_by:
  assumes I: "resolution_pattern_invariant P d0 \<pi>0 st" and sup: "resolution_supported_by F P st \<theta>"
    and foreign: "\<And>z. F z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
    and g: "g |\<in>| resolution_pending st" and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
  obtains st' \<theta>' where "st' |\<in>| finite_goal_successors P st g" "resolution_supported_by F P st' \<theta>'"
    "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
proof -
  show thesis
  proof (rule resolution_goal_lifted_at[OF I sup[unfolded resolution_supported_by_at] foreign g
      resolution_focused_none kind])
    fix st' \<theta>' assume s: "st' |\<in>| finite_goal_successors P st g"
      and u: "resolution_supported_at F None {||} P st' \<theta>'"
      and w: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
    show thesis by (rule that[OF s _ w]) (use u in \<open>simp only: resolution_supported_by_at\<close>)
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

lemma resolution_union_member: "x |\<in>| A \<Longrightarrow> y |\<in>| f x \<Longrightarrow> y |\<in>| ffUnion (fimage f A)"
  by (auto simp: ffUnion.rep_eq fimage.rep_eq)

lemma resolution_union_nonempty: "x |\<in>| A \<Longrightarrow> f x \<noteq> {||} \<Longrightarrow> ffUnion (fimage f A) \<noteq> {||}"
  by (metis all_not_fin_conv resolution_union_member)

text \<open>A variable's substitute stands inside the substituted pattern.\<close>

lemma finite_substitute_variables_subset:
  "b |\<in>| finite_pattern_variables p \<Longrightarrow>
    finite_pattern_variables (\<sigma> b) |\<subseteq>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)"
  by (induction p) auto

section \<open>Views: a producer's output anywhere in its argument\<close>

text \<open>
  A view reads a term as a pair of an input and an output (@{typ "factor_term \<Rightarrow> (factor_term \<times> factor_term) option"}),
  and a pattern as its two parts, whose values under every grounding are the view's of the pattern's value
  (@{text finite_view_parts}). As data (DECISIONS.md, task 495's entry, its addition "The given's remaining producers:
  views, carriers and narrowed sockets", (a)) a view is a linear pattern p of the site's argument and a pair
  Pair pi po over exactly p's variables (@{text view_formed}); its term function matches p and evaluates pi and po at
  the match (@{text resolution_view_term}). It has p's parts at every grounding (@{text resolution_view_parts}) and is
  injective on the terms p matches (@{text resolution_view_injective}). The identity view is R5's pair and the swap its
  left side (@{text identity_view_term}, @{text swapped_view_term}); a view whose po is a tuple of patterns names them its
  holes (@{text view_holes}). A view reads a term's shape and where its variables occur, never a value; a declaration
  reads it, and nothing installs it.
\<close>

lemma decode_resolution_value:
  "decode_finite_term (resolution_value \<theta> p) = evaluate_pattern (\<lambda>z. decode_finite_term (\<theta> z)) (decode_finite_pattern p)"
  by (induction p) (simp_all add: resolution_value_def)

lemma resolution_value_composes:
  "resolution_value \<theta> (finite_pattern_substitute \<sigma> p) = resolution_value (\<lambda>z. resolution_value \<theta> (\<sigma> z)) p"
  by (induction p) (simp_all add: resolution_value_def)

definition finite_view_parts ::
    "(factor_term \<Rightarrow> (factor_term \<times> factor_term) option) \<Rightarrow> 'v finite_term_pattern \<Rightarrow> 'v finite_term_pattern \<Rightarrow>
      'v finite_term_pattern \<Rightarrow> bool" where
  "finite_view_parts view p pi po \<longleftrightarrow>
    finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po \<and>
    (\<forall>\<theta>. view (decode_finite_term (resolution_value \<theta> p)) =
      Some (decode_finite_term (resolution_value \<theta> pi),decode_finite_term (resolution_value \<theta> po)))"

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

subsection \<open>A view as data\<close>

type_synonym 'v resolution_view = "'v finite_term_pattern \<times> 'v finite_term_pattern \<times> 'v finite_term_pattern"

fun finite_pattern_occurrences :: "'v finite_term_pattern \<Rightarrow> 'v list" where
  "finite_pattern_occurrences (Finite_Variable v) = [v]"
| "finite_pattern_occurrences (Finite_Pattern_Target t) = []"
| "finite_pattern_occurrences (Finite_Pattern_Payload b) = []"
| "finite_pattern_occurrences (Finite_Pattern_Pair p q) = finite_pattern_occurrences p @ finite_pattern_occurrences q"

lemma finite_pattern_occurrences_set: "set (finite_pattern_occurrences p) = fset (finite_pattern_variables p)"
  by (induction p) auto

definition view_formed :: "'v resolution_view \<Rightarrow> bool" where
  "view_formed V \<longleftrightarrow> (case V of (p,pi,po) \<Rightarrow> distinct (finite_pattern_occurrences p) \<and>
    finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po)"

text \<open>
  A match lists the value of each of p's variable occurrences, in order; a variable is read from the list by one lookup
  with a default, the same for a term's match and a pattern's.
\<close>

definition view_lookup :: "'b \<Rightarrow> ('v \<times> 'b) list \<Rightarrow> 'v \<Rightarrow> 'b" where
  "view_lookup z l v = (case map_of l v of Some x \<Rightarrow> x | None \<Rightarrow> z)"

lemma view_lookup_append_left: "map_of l1 v \<noteq> None \<Longrightarrow> view_lookup z (l1 @ l2) v = view_lookup z l1 v"
  by (auto simp: view_lookup_def map_of_append map_add_def split: option.splits)

lemma view_lookup_append_right: "map_of l1 v = None \<Longrightarrow> view_lookup z (l1 @ l2) v = view_lookup z l2 v"
  by (auto simp: view_lookup_def map_of_append map_add_def split: option.splits)

lemma view_lookup_bound:
  assumes "map fst l = finite_pattern_occurrences p"
  shows "map_of l v \<noteq> None \<longleftrightarrow> v |\<in>| finite_pattern_variables p"
proof -
  have "set (map fst l) = fset (finite_pattern_variables p)" using assms finite_pattern_occurrences_set by metis
  then show ?thesis by (auto simp: map_of_eq_None_iff)
qed

lemma view_lookup_split:
  assumes l1: "map fst l1 = finite_pattern_occurrences p"
    and dis: "set (finite_pattern_occurrences p) \<inter> set (finite_pattern_occurrences q) = {}"
  shows "v |\<in>| finite_pattern_variables p \<Longrightarrow> view_lookup z (l1 @ l2) v = view_lookup z l1 v"
    and "v |\<in>| finite_pattern_variables q \<Longrightarrow> view_lookup z (l1 @ l2) v = view_lookup z l2 v"
proof -
  show "v |\<in>| finite_pattern_variables p \<Longrightarrow> view_lookup z (l1 @ l2) v = view_lookup z l1 v"
    using view_lookup_bound[OF l1] by (auto intro: view_lookup_append_left)
  assume vq: "v |\<in>| finite_pattern_variables q"
  have "v |\<notin>| finite_pattern_variables p"
    using vq dis finite_pattern_occurrences_set[of p] finite_pattern_occurrences_set[of q] by auto
  then have "map_of l1 v = None" using view_lookup_bound[OF l1] by blast
  then show "view_lookup z (l1 @ l2) v = view_lookup z l2 v" by (rule view_lookup_append_right)
qed

fun view_match :: "'v finite_term_pattern \<Rightarrow> factor_term \<Rightarrow> ('v \<times> factor_term) list option" where
  "view_match (Finite_Variable v) t = Some [(v,t)]"
| "view_match (Finite_Pattern_Target a) t = (if t = Target_Term (decode_finite_target a) then Some [] else None)"
| "view_match (Finite_Pattern_Payload b) t = (if t = Payload_Term b then Some [] else None)"
| "view_match (Finite_Pattern_Pair p q) (Pair_Term t u) =
    (case (view_match p t,view_match q u) of (Some l,Some m) \<Rightarrow> Some (l @ m) | _ \<Rightarrow> None)"
| "view_match (Finite_Pattern_Pair p q) t = None"

abbreviation view_valuation :: "('v \<times> factor_term) list \<Rightarrow> 'v \<Rightarrow> factor_term" where
  "view_valuation \<equiv> view_lookup (Payload_Term [])"

definition resolution_view_term :: "'v resolution_view \<Rightarrow> factor_term \<Rightarrow> (factor_term \<times> factor_term) option" where
  "resolution_view_term V t = (case V of (p,pi,po) \<Rightarrow> (case view_match p t of None \<Rightarrow> None
    | Some l \<Rightarrow> Some (evaluate_pattern (view_valuation l) (decode_finite_pattern pi),
        evaluate_pattern (view_valuation l) (decode_finite_pattern po))))"

lemma view_match_domain: "view_match p t = Some l \<Longrightarrow> map fst l = finite_pattern_occurrences p"
proof (induction p arbitrary: t l)
  case (Finite_Pattern_Pair p q)
  then show ?case by (cases t) (auto split: option.splits)
qed (auto split: if_splits)

lemma view_match_sound:
  "distinct (finite_pattern_occurrences p) \<Longrightarrow> view_match p t = Some l \<Longrightarrow>
    evaluate_pattern (view_valuation l) (decode_finite_pattern p) = t"
proof (induction p arbitrary: t l)
  case (Finite_Variable v)
  then show ?case by (auto simp: view_lookup_def)
next
  case (Finite_Pattern_Target a)
  then show ?case by (simp split: if_splits)
next
  case (Finite_Pattern_Payload b)
  then show ?case by (simp split: if_splits)
next
  case (Finite_Pattern_Pair p q)
  obtain t1 t2 where t: "t = Pair_Term t1 t2" using Finite_Pattern_Pair.prems(2) by (cases t) simp_all
  from Finite_Pattern_Pair.prems(2) obtain l1 l2 where m1: "view_match p t1 = Some l1"
      and m2: "view_match q t2 = Some l2" and l: "l = l1 @ l2"
    unfolding t by (auto split: option.splits)
  have dp: "distinct (finite_pattern_occurrences p)" and dq: "distinct (finite_pattern_occurrences q)"
    and dis: "set (finite_pattern_occurrences p) \<inter> set (finite_pattern_occurrences q) = {}"
    using Finite_Pattern_Pair.prems(1) by simp_all
  note split = view_lookup_split[OF view_match_domain[OF m1] dis]
  have a1: "evaluate_pattern (view_valuation l) (decode_finite_pattern p) =
      evaluate_pattern (view_valuation l1) (decode_finite_pattern p)"
    by (rule evaluate_pattern_cong) (simp add: l split(1) finite_pattern_variables_correct[symmetric])
  have a2: "evaluate_pattern (view_valuation l) (decode_finite_pattern q) =
      evaluate_pattern (view_valuation l2) (decode_finite_pattern q)"
    by (rule evaluate_pattern_cong) (simp add: l split(2) finite_pattern_variables_correct[symmetric])
  show ?case using a1 a2 Finite_Pattern_Pair.IH(1)[OF dp m1] Finite_Pattern_Pair.IH(2)[OF dq m2] t by simp
qed

lemma view_match_complete:
  "distinct (finite_pattern_occurrences p) \<Longrightarrow>
    \<exists>l. view_match p (evaluate_pattern h (decode_finite_pattern p)) = Some l \<and>
      (\<forall>v. v |\<in>| finite_pattern_variables p \<longrightarrow> view_valuation l v = h v)"
proof (induction p)
  case (Finite_Variable v)
  then show ?case by (simp add: view_lookup_def)
next
  case (Finite_Pattern_Pair p q)
  have dp: "distinct (finite_pattern_occurrences p)" and dq: "distinct (finite_pattern_occurrences q)"
    and dis: "set (finite_pattern_occurrences p) \<inter> set (finite_pattern_occurrences q) = {}"
    using Finite_Pattern_Pair.prems by simp_all
  obtain l1 where m1: "view_match p (evaluate_pattern h (decode_finite_pattern p)) = Some l1"
      and a1: "\<forall>v. v |\<in>| finite_pattern_variables p \<longrightarrow> view_valuation l1 v = h v"
    using Finite_Pattern_Pair.IH(1)[OF dp] by blast
  obtain l2 where m2: "view_match q (evaluate_pattern h (decode_finite_pattern q)) = Some l2"
      and a2: "\<forall>v. v |\<in>| finite_pattern_variables q \<longrightarrow> view_valuation l2 v = h v"
    using Finite_Pattern_Pair.IH(2)[OF dq] by blast
  note split = view_lookup_split[OF view_match_domain[OF m1] dis]
  have val: "view_valuation (l1 @ l2) v = h v" if "v |\<in>| finite_pattern_variables (Finite_Pattern_Pair p q)" for v
    using that a1 a2 split by auto
  show ?case using m1 m2 val by (intro exI[of _ "l1 @ l2"]) simp
qed simp_all

lemma resolution_view_evaluate:
  assumes formed: "view_formed (p,pi,po)"
  shows "resolution_view_term (p,pi,po) (evaluate_pattern h (decode_finite_pattern p)) =
    Some (evaluate_pattern h (decode_finite_pattern pi),evaluate_pattern h (decode_finite_pattern po))"
proof -
  have lin: "distinct (finite_pattern_occurrences p)"
    and vs: "finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po"
    using formed by (simp_all add: view_formed_def)
  obtain l where m: "view_match p (evaluate_pattern h (decode_finite_pattern p)) = Some l"
    and a: "\<forall>v. v |\<in>| finite_pattern_variables p \<longrightarrow> view_valuation l v = h v"
    using view_match_complete[OF lin, of h] by blast
  have ai: "evaluate_pattern (view_valuation l) (decode_finite_pattern pi) = evaluate_pattern h (decode_finite_pattern pi)"
    by (rule evaluate_pattern_cong) (simp add: a vs finite_pattern_variables_correct[symmetric])
  have ao: "evaluate_pattern (view_valuation l) (decode_finite_pattern po) = evaluate_pattern h (decode_finite_pattern po)"
    by (rule evaluate_pattern_cong) (simp add: a vs finite_pattern_variables_correct[symmetric])
  show ?thesis by (simp add: resolution_view_term_def m ai ao)
qed

theorem resolution_view_parts:
  assumes formed: "view_formed (p,pi,po)"
  shows "finite_view_parts (resolution_view_term (p,pi,po)) p pi po"
proof -
  have vs: "finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po"
    using formed by (simp add: view_formed_def)
  show ?thesis using vs by (simp add: finite_view_parts_def decode_resolution_value resolution_view_evaluate[OF formed])
qed

subsection \<open>The view of a pattern\<close>

text \<open>
  A view reads a call's pattern as it reads a term: p is matched against the pattern, and pi and po are the same
  substitution's (@{text resolution_view_pattern}). The viewed parts are the parts of the term view at the call
  (@{text resolution_view_pattern_parts}); at p itself they are pi and po (@{text resolution_view_parts}).
\<close>

fun view_pattern_match :: "'v finite_term_pattern \<Rightarrow> 'w finite_term_pattern \<Rightarrow> ('v \<times> 'w finite_term_pattern) list option" where
  "view_pattern_match (Finite_Variable v) c = Some [(v,c)]"
| "view_pattern_match (Finite_Pattern_Target a) c = (if c = Finite_Pattern_Target a then Some [] else None)"
| "view_pattern_match (Finite_Pattern_Payload b) c = (if c = Finite_Pattern_Payload b then Some [] else None)"
| "view_pattern_match (Finite_Pattern_Pair p q) (Finite_Pattern_Pair c e) =
    (case (view_pattern_match p c,view_pattern_match q e) of (Some l,Some m) \<Rightarrow> Some (l @ m) | _ \<Rightarrow> None)"
| "view_pattern_match (Finite_Pattern_Pair p q) c = None"

abbreviation view_substitution :: "('v \<times> 'w finite_term_pattern) list \<Rightarrow> 'v \<Rightarrow> 'w finite_term_pattern" where
  "view_substitution \<equiv> view_lookup (Finite_Pattern_Payload [])"

definition resolution_view_pattern ::
    "'v resolution_view \<Rightarrow> 'w finite_term_pattern \<Rightarrow> ('w finite_term_pattern \<times> 'w finite_term_pattern) option" where
  "resolution_view_pattern V c = (case V of (p,pi,po) \<Rightarrow> (case view_pattern_match p c of None \<Rightarrow> None
    | Some l \<Rightarrow> Some (finite_pattern_substitute (view_substitution l) pi,finite_pattern_substitute (view_substitution l) po)))"

lemma view_pattern_match_domain: "view_pattern_match p c = Some l \<Longrightarrow> map fst l = finite_pattern_occurrences p"
proof (induction p arbitrary: c l)
  case (Finite_Pattern_Pair p q)
  then show ?case by (cases c) (auto split: option.splits)
qed (auto split: if_splits)

lemma view_pattern_match_sound:
  "distinct (finite_pattern_occurrences p) \<Longrightarrow> view_pattern_match p c = Some l \<Longrightarrow>
    finite_pattern_substitute (view_substitution l) p = c"
proof (induction p arbitrary: c l)
  case (Finite_Variable v)
  then show ?case by (auto simp: view_lookup_def)
next
  case (Finite_Pattern_Target a)
  then show ?case by (simp split: if_splits)
next
  case (Finite_Pattern_Payload b)
  then show ?case by (simp split: if_splits)
next
  case (Finite_Pattern_Pair p q)
  obtain c1 c2 where c: "c = Finite_Pattern_Pair c1 c2" using Finite_Pattern_Pair.prems(2) by (cases c) simp_all
  from Finite_Pattern_Pair.prems(2) obtain l1 l2 where m1: "view_pattern_match p c1 = Some l1"
      and m2: "view_pattern_match q c2 = Some l2" and l: "l = l1 @ l2"
    unfolding c by (auto split: option.splits)
  have dp: "distinct (finite_pattern_occurrences p)" and dq: "distinct (finite_pattern_occurrences q)"
    and dis: "set (finite_pattern_occurrences p) \<inter> set (finite_pattern_occurrences q) = {}"
    using Finite_Pattern_Pair.prems(1) by simp_all
  note split = view_lookup_split[OF view_pattern_match_domain[OF m1] dis]
  have a1: "finite_pattern_substitute (view_substitution l) p = finite_pattern_substitute (view_substitution l1) p"
    by (rule finite_pattern_substitute_cong) (simp add: l split(1))
  have a2: "finite_pattern_substitute (view_substitution l) q = finite_pattern_substitute (view_substitution l2) q"
    by (rule finite_pattern_substitute_cong) (simp add: l split(2))
  show ?case using a1 a2 Finite_Pattern_Pair.IH(1)[OF dp m1] Finite_Pattern_Pair.IH(2)[OF dq m2] c by simp
qed

theorem resolution_view_pattern_parts:
  assumes formed: "view_formed (p,pi,po)" and viewed: "resolution_view_pattern (p,pi,po) c = Some (ci,co)"
  shows "finite_view_parts (resolution_view_term (p,pi,po)) c ci co"
proof -
  have lin: "distinct (finite_pattern_occurrences p)"
    and vs: "finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po"
    using formed by (simp_all add: view_formed_def)
  obtain l where m: "view_pattern_match p c = Some l"
      and ci: "ci = finite_pattern_substitute (view_substitution l) pi"
      and co: "co = finite_pattern_substitute (view_substitution l) po"
    using viewed by (auto simp: resolution_view_pattern_def split: option.splits)
  let ?s = "view_substitution l"
  have c: "finite_pattern_substitute ?s p = c" by (rule view_pattern_match_sound[OF lin m])
  have vc: "finite_pattern_variables c = finite_pattern_variables ci |\<union>| finite_pattern_variables co"
    unfolding c[symmetric] ci co
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s p) \<longleftrightarrow>
        x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s pi) |\<union>| finite_pattern_variables (finite_pattern_substitute ?s po)"
    proof
      assume x: "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s p)"
      obtain v where v: "v |\<in>| finite_pattern_variables p" "x |\<in>| finite_pattern_variables (?s v)"
        using finite_substitute_variable_origin[OF x] by blast
      have "v |\<in>| finite_pattern_variables pi \<or> v |\<in>| finite_pattern_variables po" using v(1) vs by simp
      then show "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s pi) |\<union>|
          finite_pattern_variables (finite_pattern_substitute ?s po)"
        using v(2) finite_substitute_variables_subset[of v pi ?s] finite_substitute_variables_subset[of v po ?s] by auto
    next
      assume "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s pi) |\<union>|
          finite_pattern_variables (finite_pattern_substitute ?s po)"
      then obtain w where w: "w = pi \<or> w = po" and x: "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s w)"
        by auto
      obtain v where v: "v |\<in>| finite_pattern_variables w" "x |\<in>| finite_pattern_variables (?s v)"
        using finite_substitute_variable_origin[OF x] by blast
      have "v |\<in>| finite_pattern_variables p" using v(1) w vs by auto
      then show "x |\<in>| finite_pattern_variables (finite_pattern_substitute ?s p)"
        using v(2) finite_substitute_variables_subset[of v p ?s] by auto
    qed
  qed
  have "resolution_view_term (p,pi,po) (decode_finite_term (resolution_value \<theta> c)) =
      Some (decode_finite_term (resolution_value \<theta> ci),decode_finite_term (resolution_value \<theta> co))" for \<theta>
    unfolding c[symmetric] ci co resolution_value_composes decode_resolution_value
    by (rule resolution_view_evaluate[OF formed])
  then show ?thesis using vc by (simp add: finite_view_parts_def)
qed

theorem resolution_view_injective:
  assumes formed: "view_formed (p,pi,po)"
    and a: "resolution_view_term (p,pi,po) t = Some z" and b: "resolution_view_term (p,pi,po) t' = Some z"
  shows "t = t'"
proof -
  have lin: "distinct (finite_pattern_occurrences p)"
    and vs: "finite_pattern_variables p = finite_pattern_variables pi |\<union>| finite_pattern_variables po"
    using formed by (simp_all add: view_formed_def)
  obtain l where m: "view_match p t = Some l"
      and zl: "z = (evaluate_pattern (view_valuation l) (decode_finite_pattern pi),
        evaluate_pattern (view_valuation l) (decode_finite_pattern po))"
    using a by (auto simp: resolution_view_term_def split: option.splits)
  obtain l' where m': "view_match p t' = Some l'"
      and zl': "z = (evaluate_pattern (view_valuation l') (decode_finite_pattern pi),
        evaluate_pattern (view_valuation l') (decode_finite_pattern po))"
    using b by (auto simp: resolution_view_term_def split: option.splits)
  have ei: "evaluate_pattern (view_valuation l) (decode_finite_pattern pi) =
      evaluate_pattern (view_valuation l') (decode_finite_pattern pi)" using zl zl' by simp
  have eo: "evaluate_pattern (view_valuation l) (decode_finite_pattern po) =
      evaluate_pattern (view_valuation l') (decode_finite_pattern po)" using zl zl' by simp
  have ag: "view_valuation l v = view_valuation l' v" if "v |\<in>| finite_pattern_variables p" for v
  proof -
    have "v |\<in>| finite_pattern_variables pi \<or> v |\<in>| finite_pattern_variables po" using that vs by simp
    then show ?thesis using evaluate_pattern_agree[OF ei] evaluate_pattern_agree[OF eo]
      by (auto simp: finite_pattern_variables_correct[symmetric])
  qed
  have "evaluate_pattern (view_valuation l) (decode_finite_pattern p) =
      evaluate_pattern (view_valuation l') (decode_finite_pattern p)"
    by (rule evaluate_pattern_cong) (simp add: ag finite_pattern_variables_correct[symmetric])
  then show ?thesis using view_match_sound[OF lin m] view_match_sound[OF lin m'] by simp
qed

text \<open>
  A view reads a pattern's substitution instance as the substitution of its reading (#585's (a): a view commutes with
  substitution), and a formed view's parts hold exactly the pattern's variables.
\<close>

lemma view_pattern_match_substitute:
  "view_pattern_match p c = Some l \<Longrightarrow>
    view_pattern_match p (finite_pattern_substitute \<sigma> c) = Some (map (\<lambda>(v,c). (v,finite_pattern_substitute \<sigma> c)) l)"
proof (induction p arbitrary: c l)
  case (Finite_Pattern_Pair p q)
  obtain c1 c2 where c: "c = Finite_Pattern_Pair c1 c2" using Finite_Pattern_Pair.prems by (cases c) simp_all
  from Finite_Pattern_Pair.prems obtain l1 l2 where m1: "view_pattern_match p c1 = Some l1"
      and m2: "view_pattern_match q c2 = Some l2" and l: "l = l1 @ l2"
    unfolding c by (auto split: option.splits)
  show ?case using Finite_Pattern_Pair.IH(1)[OF m1] Finite_Pattern_Pair.IH(2)[OF m2] c l by simp
qed (auto split: if_splits)

lemma resolution_view_pattern_substitute:
  assumes viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_pattern V (finite_pattern_substitute \<sigma> c) =
    Some (finite_pattern_substitute \<sigma> ci,finite_pattern_substitute \<sigma> co)"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V)
  obtain l where m: "view_pattern_match p c = Some l"
      and ci: "ci = finite_pattern_substitute (view_substitution l) pi"
      and co: "co = finite_pattern_substitute (view_substitution l) po"
    using viewed V by (auto simp: resolution_view_pattern_def split: option.splits)
  let ?l = "map (\<lambda>(v,c). (v,finite_pattern_substitute \<sigma> c)) l"
  have sub: "view_substitution ?l = (\<lambda>v. finite_pattern_substitute \<sigma> (view_substitution l v))"
    by (rule ext) (auto simp: view_lookup_def map_of_map split: option.splits)
  have m': "view_pattern_match p (finite_pattern_substitute \<sigma> c) = Some ?l" by (rule view_pattern_match_substitute[OF m])
  show ?thesis using m' V ci co sub by (simp add: resolution_view_pattern_def finite_pattern_substitute_composes)
qed

lemma resolution_view_pattern_variables:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "finite_pattern_variables c = finite_pattern_variables ci |\<union>| finite_pattern_variables co"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V)
  show ?thesis using resolution_view_pattern_parts[of p pi po c ci co] formed viewed V by (simp add: finite_view_parts_def)
qed

text \<open>A view reads a pattern renamed by a binder map as the renaming of its reading.\<close>

lemma resolution_view_pattern_map:
  assumes "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_pattern V (map_finite_term_pattern f c) =
    Some (map_finite_term_pattern f ci,map_finite_term_pattern f co)"
  using resolution_view_pattern_substitute[OF assms, of "\<lambda>a. Finite_Variable (f a)"]
  by (simp only: finite_pattern_substitute_variable_map)

lemma resolution_view_parts_variables:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "fset (finite_pattern_variables ci) \<subseteq> fset (finite_pattern_variables c)"
    and "fset (finite_pattern_variables co) \<subseteq> fset (finite_pattern_variables c)"
  using resolution_view_pattern_variables[OF formed viewed] by auto

text \<open>A view reads the value of a pattern it matches as the values of the pattern's viewed parts.\<close>

lemma resolution_view_pattern_value:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_term V (decode_finite_term (resolution_value \<theta> c)) =
    Some (decode_finite_term (resolution_value \<theta> ci),decode_finite_term (resolution_value \<theta> co))"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  show ?thesis using resolution_view_pattern_parts[of p pi po c ci co] formed viewed V by (simp add: finite_view_parts_def)
qed

text \<open>
  A view read at a call pattern gives the parts of the pattern's value under every valuation.
\<close>

lemma resolution_view_pattern_evaluate:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_term V (evaluate_pattern g (decode_finite_pattern c)) =
    Some (evaluate_pattern g (decode_finite_pattern ci),evaluate_pattern g (decode_finite_pattern co))"
proof -
  obtain p pi po where V: "V = (p,pi,po)" by (cases V rule: prod_cases3)
  have lin: "distinct (finite_pattern_occurrences p)" using formed V by (simp add: view_formed_def)
  obtain l where m: "view_pattern_match p c = Some l"
      and ci: "ci = finite_pattern_substitute (view_substitution l) pi"
      and co: "co = finite_pattern_substitute (view_substitution l) po"
    using viewed V by (auto simp: resolution_view_pattern_def split: option.splits)
  define h where "h = (\<lambda>v. evaluate_pattern g (decode_finite_pattern (view_substitution l v)))"
  have sub: "evaluate_pattern g (decode_finite_pattern (finite_pattern_substitute (view_substitution l) q)) =
      evaluate_pattern h (decode_finite_pattern q)" for q
    by (simp add: decode_finite_pattern_substitute h_def comp_def)
  have c: "c = finite_pattern_substitute (view_substitution l) p" using view_pattern_match_sound[OF lin m] by simp
  show ?thesis using resolution_view_evaluate[OF formed[unfolded V], of h] unfolding V c ci co sub .
qed

subsection \<open>R5's pair and its swap are views\<close>

definition identity_view :: "'v \<Rightarrow> 'v \<Rightarrow> 'v resolution_view" where
  "identity_view a b = (Finite_Pattern_Pair (Finite_Variable a) (Finite_Variable b),Finite_Variable a,Finite_Variable b)"

definition swapped_view :: "'v \<Rightarrow> 'v \<Rightarrow> 'v resolution_view" where
  "swapped_view a b = (Finite_Pattern_Pair (Finite_Variable a) (Finite_Variable b),Finite_Variable b,Finite_Variable a)"

lemma identity_view_formed: "a \<noteq> b \<Longrightarrow> view_formed (identity_view a b)"
  by (simp add: view_formed_def identity_view_def finsert_commute)

lemma swapped_view_formed: "a \<noteq> b \<Longrightarrow> view_formed (swapped_view a b)"
  by (simp add: view_formed_def swapped_view_def finsert_commute)

lemma identity_view_term:
  assumes "a \<noteq> b"
  shows "resolution_view_term (identity_view a b) = pair_view"
proof
  fix t show "resolution_view_term (identity_view a b) t = pair_view t"
    using assms by (cases t) (simp_all add: resolution_view_term_def identity_view_def view_lookup_def pair_view_def)
qed

lemma swapped_view_term:
  assumes "a \<noteq> b"
  shows "resolution_view_term (swapped_view a b) = swap_view"
proof
  fix t show "resolution_view_term (swapped_view a b) t = swap_view t"
    using assms by (cases t) (simp_all add: resolution_view_term_def swapped_view_def view_lookup_def swap_view_def)
qed

subsection \<open>A view's holes\<close>

text \<open>
  A view whose output is a tuple of patterns (@{const finite_pattern_tuple}) names them its holes: a consumer holds one
  hole, and the view's correspondence is a product, one factor per hole.
\<close>

definition view_holes :: "'v resolution_view \<Rightarrow> 'v finite_term_pattern list \<Rightarrow> bool" where
  "view_holes V hs \<longleftrightarrow> snd (snd V) = finite_pattern_tuple hs"

section \<open>The committed search\<close>

text \<open>
  A commitment decides, at a state and a focus, whether a call goal is committed and whether a material goal
  takes its single solution. The search is R3's, with a focus: a committed goal at a position is solved first
  in the subtree under it (the search with that position as its focus, which is done when no goal under it is
  pending); of the states so reached, those whose answer at the position is the least by the term key order of
  @{text Ordered_Finite_Terms} are kept, a function of the set of answers alone; the search goes on from them
  with the focus it had. At a commitment every node then present is barred: a ground goal equal to the call of
  an unbarred ancestor is pruned as in R3, and one equal to the call of a barred ancestor ends its branch with a
  diagnosis, never a refutation, since the ranks that justify pruning do not decrease across a commitment. A
  committed material goal whose source is a ground whole artifact takes the solution of the artifact's
  canonical rows, a member of R1's solutions.

  A commitment also gives, at a focus, a state and a call goal, an optional production: a view and a ground value
  for the goal's output read at it (R5f1, task 725's correction closing the addition "The given's remaining
  producers" to task 495's entry). A committed call goal whose commitment produces is solved in its subtree from the
  produced state, its output bound to the value; every other committed goal as before.
\<close>

record ('a,'s,'d,'c) resolution_commitment =
  commit_call :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
  commit_material :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool"
  commit_production :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
    (nat resolution_view \<times> finite_factor_term) option"

definition no_commitment :: "('a,'s,'d,'c) resolution_commitment" where
  "no_commitment = \<lparr>commit_call=(\<lambda>F st g. False), commit_material=(\<lambda>F st g. False),
    commit_production=(\<lambda>F st g. None)\<rparr>"

text \<open>
  The committed search selects at the commitment's own tests (F1 of the addition "The resolver at the given's size" to
  task 495's entry): a goal the call or material test accepts on the state the selection reads, at no focus or with
  the goal's parent position as the focus, is taken before a goal with one alternative. Among the goals the tests
  accept at one state only the least position is taken, so one commitment can end another's committability, and a
  one-alternative sibling expanded before a socket becomes committable can still foreclose it (F1.5 of the addition).
  At no commitment the priority is empty and the selection is R3's.
\<close>

definition finite_commitment_priority ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_commitment_priority K st g = (let F = Some (butlast (resolution_goal_position g)) in
    case g of Resolution_Call_Goal q r d p \<Rightarrow> commit_call K None st g \<or> commit_call K F st g
    | Resolution_Material_Goal q r M \<Rightarrow> commit_material K None st g \<or> commit_material K F st g)"

lemma finite_commitment_priority_none [simp]: "finite_commitment_priority no_commitment = (\<lambda>st g. False)"
proof (rule ext, rule ext)
  fix st g
  show "finite_commitment_priority no_commitment st g = False"
    by (cases g) (simp_all add: finite_commitment_priority_def no_commitment_def)
qed

abbreviation finite_committed_select ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_committed_select \<kappa> K P \<equiv> finite_resolution_select_at (finite_commitment_priority K) \<kappa> P"

definition finite_focus_pending ::
    "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_focus_pending F st = (case F of None \<Rightarrow> resolution_pending st
    | Some q \<Rightarrow> ffilter (\<lambda>g. take (length q) (resolution_goal_position g) = q) (resolution_pending st))"

definition finite_focused :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_focused F st = Resolution_State (finite_focus_pending F st) (resolution_nodes st) (resolution_witnesses st)"

definition finite_unbarred :: "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_unbarred B st = Resolution_State (resolution_pending st)
    (ffilter (\<lambda>nd. resolution_node_position nd |\<notin>| B) (resolution_nodes st)) (resolution_witnesses st)"

definition finite_barred :: "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_barred B st = Resolution_State (resolution_pending st)
    (ffilter (\<lambda>nd. resolution_node_position nd |\<in>| B) (resolution_nodes st)) (resolution_witnesses st)"

lemma finite_focus_pending_subset: "finite_focus_pending F st |\<subseteq>| resolution_pending st"
  by (auto simp: finite_focus_pending_def split: option.splits)

lemma finite_focus_none [simp]:
  "finite_focus_pending None st = resolution_pending st" "finite_focused None st = st"
  by (simp_all add: finite_focus_pending_def finite_focused_def)

lemma finite_unbarred_empty [simp]: "finite_unbarred {||} st = st"
  by (cases st) (simp add: finite_unbarred_def fset_eq_iff)

lemma finite_barred_empty [simp]: "\<not> finite_pruned (finite_barred {||} st) g"
  by (auto simp: finite_pruned_def finite_barred_def split: resolution_goal.splits)

text \<open>The answers of a state at a position, and the states keeping the least answer.\<close>

definition finite_committed_answers :: "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ordered_factor_term fset" where
  "finite_committed_answers q st = fimage (\<lambda>nd. Ordered_Factor_Term (finite_residual_term (resolution_node_call nd)))
    (ffilter (\<lambda>nd. resolution_node_position nd = q) (resolution_nodes st))"

definition finite_kept :: "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state fset \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_kept q S = (let A = ffUnion (fimage (finite_committed_answers q) S) in
    ffilter (\<lambda>st. fBex (finite_committed_answers q st) (\<lambda>a. fBall A (\<lambda>b. a \<le> b))) S)"

lemma finite_kept_subset: "finite_kept q S |\<subseteq>| S"
  by (auto simp: finite_kept_def Let_def)

text \<open>The material successors of a family of solutions; R1's are those of all its solutions.\<close>

definition finite_solution_successors ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> 'd \<times> 'c \<times> 's \<Rightarrow>
      ('s,'a) resolution_variable finite_material_pattern \<Rightarrow> (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state fset" where
  "finite_solution_successors st q r M Ws = ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E.
      case finite_unify_pairs E of
        None \<Rightarrow> {||}
      | Some u \<Rightarrow> {|resolution_state_substitute (finite_binding_substitution u)
          (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|})
            (resolution_nodes st) (resolution_witnesses st))|})
    (finite_material_instance_pairs W M))) Ws)"

lemma finite_material_successors_solutions:
  "finite_material_successors st q r M = (case finite_material_resolution M of Material_Waits \<Rightarrow> {||}
    | Material_Solutions Ws \<Rightarrow> finite_solution_successors st q r M Ws)"
  by (simp add: finite_material_successors_def finite_solution_successors_def split: finite_material_outcome.split)

lemma finite_solution_successors_mono:
  "Ws' |\<subseteq>| Ws \<Longrightarrow> finite_solution_successors st q r M Ws' |\<subseteq>| finite_solution_successors st q r M Ws"
  unfolding finite_solution_successors_def by (auto simp: resolution_fset_simps less_eq_fset.rep_eq)

lemma finite_artifact_rows_enumerated: "finite_artifact_rows C \<in> set (finite_artifact_enumerations C)"
proof -
  obtain A E B F where r: "finite_artifact_rows C = (A,E,B,F)" by (cases "finite_artifact_rows C") auto
  have "A \<in> set (rearrangements A)" "E \<in> set (rearrangements E)" "B \<in> set (rearrangements B)"
    "F \<in> set (rearrangements F)" by (simp_all add: rearrangements_member)
  then show ?thesis by (force simp: finite_artifact_enumerations_def r)
qed

text \<open>
  The single solution of a material goal whose skeleton is open and whose source is a ground whole artifact:
  the candidate of the artifact's canonical rows (@{const finite_artifact_rows}), one of R1's solutions.
\<close>

definition finite_canonical_solutions ::
    "'v finite_material_pattern \<Rightarrow> ('v \<times> finite_factor_term) fset fset option" where
  "finite_canonical_solutions M = (case finite_material_source M of
      Finite_Pattern_Target x \<Rightarrow> (case x of
          Finite_Whole C \<Rightarrow> if finite_material_skeleton M = Open_Reading
            then Some (finite_material_candidates M [finite_material_tuple C (finite_artifact_rows C)]) else None
        | Finite_Anchor C a \<Rightarrow> None)
    | _ \<Rightarrow> None)"

text \<open>
  A material premise whose skeleton is not an open reading, as where an unreadable field stands beside an open one, has
  no canonical solutions, at a ground whole source too (review 809).
\<close>

lemma finite_canonical_solutions_unread:
  assumes "finite_material_skeleton M \<noteq> Open_Reading"
  shows "finite_canonical_solutions M = None"
  using assms by (auto simp: finite_canonical_solutions_def split: finite_term_pattern.splits finite_exact_target.splits)

lemma finite_canonical_solutions_member:
  assumes canonical: "finite_canonical_solutions M = Some Ws'"
  obtains Ws where "finite_material_resolution M = Material_Solutions Ws" "Ws' |\<subseteq>| Ws"
proof -
  from canonical obtain C where source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
    and skeleton: "finite_material_skeleton M = Open_Reading"
    and Ws': "Ws' = finite_material_candidates M [finite_material_tuple C (finite_artifact_rows C)]"
    by (auto simp: finite_canonical_solutions_def split: finite_term_pattern.splits finite_exact_target.splits if_splits)
  have "finite_material_tuple C (finite_artifact_rows C) \<in> set (map (finite_material_tuple C) (finite_artifact_enumerations C))"
    using finite_artifact_rows_enumerated by simp
  have mono: "set ts \<subseteq> set ts' \<Longrightarrow> finite_material_candidates M ts |\<subseteq>| finite_material_candidates M ts'" for ts ts'
    unfolding finite_material_candidates_def by (auto simp: less_eq_fset.rep_eq ffilter.rep_eq fset_of_list.rep_eq)
  then have "Ws' |\<subseteq>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))"
    unfolding Ws' using \<open>finite_material_tuple C (finite_artifact_rows C) \<in> _\<close> by simp
  with finite_material_resolution_source(1)[OF skeleton source] show ?thesis using that by blast
qed

text \<open>
  At the focus of a committed sub-search a call takes its call's successors and never the reuse step (F3 of the
  addition "The resolver at the given's size" to task 495's entry, course (b) of q129): the focus is solved in its own
  subtree as before F3, so a committed call's answer is the node its resolution leaves at the focus, and no committed
  goal is cut for being reusable. Every other goal of the sub-search is closed by reuse as anywhere else.
\<close>

definition finite_committed_successors ::
    "('a,'s::linorder,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_committed_successors K P F st g = (case g of
      Resolution_Material_Goal q r M \<Rightarrow> (case finite_canonical_solutions M of
          Some Ws \<Rightarrow> if commit_material K F st g then finite_solution_successors st q r M Ws
            else finite_goal_successors P st g
        | None \<Rightarrow> finite_goal_successors P st g)
    | Resolution_Call_Goal q r d p \<Rightarrow> if F = Some q then finite_call_successors P st q r d p
        else finite_goal_successors P st g)"

text \<open>A committed successor is a goal's successor or, at the focus, a call's.\<close>

lemma finite_committed_successors_cases:
  assumes s: "s |\<in>| finite_committed_successors K P F st g"
  obtains (goal) "s |\<in>| finite_goal_successors P st g"
    | (focus) q r e p where "g = Resolution_Call_Goal q r e p" "F = Some q"
      "s |\<in>| finite_call_successors P st q r e p"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  show thesis
  proof (cases "F = Some q")
    case True
    show thesis
      by (rule focus[OF Resolution_Call_Goal True]) (use s in \<open>simp add: Resolution_Call_Goal True finite_committed_successors_def\<close>)
  next
    case False
    show thesis
      by (rule goal) (use s in \<open>simp add: Resolution_Call_Goal False finite_committed_successors_def\<close>)
  qed
next
  case (Resolution_Material_Goal q r M)
  have sub: "finite_committed_successors K P F st g |\<subseteq>| finite_goal_successors P st g"
  proof (cases "finite_canonical_solutions M")
    case (Some Ws')
    then obtain Ws where Ws: "finite_material_resolution M = Material_Solutions Ws" "Ws' |\<subseteq>| Ws"
      by (rule finite_canonical_solutions_member)
    show ?thesis using Some Ws finite_solution_successors_mono[OF Ws(2), of st q r M]
      by (simp add: Resolution_Material_Goal finite_committed_successors_def finite_material_successors_solutions)
  qed (simp add: Resolution_Material_Goal finite_committed_successors_def)
  show thesis by (rule goal, rule fsubsetD[OF sub s])
qed

lemma finite_committed_successor_invariant:
  assumes I: "resolution_invariant P d t st" and pending: "g |\<in>| resolution_pending st"
    and s: "s |\<in>| finite_committed_successors K P F st g"
  shows "resolution_invariant P d t s"
  using s
proof (cases rule: finite_committed_successors_cases)
  case goal
  then show ?thesis by (rule resolution_goal_step[OF I pending])
next
  case (focus q r e p)
  show ?thesis by (rule resolution_call_step[OF I pending[unfolded focus(1)] focus(3)])
qed

lemma no_commitment_successors [simp]:
  "finite_committed_successors no_commitment P None st g = finite_goal_successors P st g"
  by (simp add: finite_committed_successors_def no_commitment_def split: resolution_goal.split option.split)

text \<open>
  A call goal the commitment's call test accepts outside its own focus is committing. It is committed when the
  commitment produces nothing for it, and producing when it produces: the two part the committing goals.
\<close>

definition finite_goal_committing ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_committing K F st g \<longleftrightarrow>
    resolution_is_call g \<and> F \<noteq> Some (resolution_goal_position g) \<and> commit_call K F st g"

definition finite_goal_committed ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_committed K F st g \<longleftrightarrow>
    resolution_is_call g \<and> F \<noteq> Some (resolution_goal_position g) \<and> commit_call K F st g \<and>
    commit_production K F st g = None"

definition finite_goal_producing ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_producing K F st g \<longleftrightarrow>
    resolution_is_call g \<and> F \<noteq> Some (resolution_goal_position g) \<and> commit_call K F st g \<and>
    commit_production K F st g \<noteq> None"

lemma finite_goal_committing_parts:
  "finite_goal_committing K F st g \<longleftrightarrow> finite_goal_committed K F st g \<or> finite_goal_producing K F st g"
  unfolding finite_goal_committing_def finite_goal_committed_def finite_goal_producing_def by blast

lemma finite_goal_committed_unproduced:
  assumes "commit_production K F st g = None"
  shows "finite_goal_committed K F st g \<longleftrightarrow>
    resolution_is_call g \<and> F \<noteq> Some (resolution_goal_position g) \<and> commit_call K F st g"
  using assms by (simp add: finite_goal_committed_def)

lemma finite_goal_committing_unproduced:
  assumes "commit_production K F st g = None"
  shows "finite_goal_committing K F st g \<longleftrightarrow> finite_goal_committed K F st g"
  using assms by (simp add: finite_goal_committing_def finite_goal_committed_def)

lemma no_commitment_committed [simp]: "\<not> finite_goal_committed no_commitment F st g"
  by (simp add: finite_goal_committed_def no_commitment_def)

lemma no_commitment_committing [simp]: "\<not> finite_goal_committing no_commitment F st g"
  by (simp add: finite_goal_committing_def no_commitment_def)

lemma no_commitment_producing [simp]: "\<not> finite_goal_producing no_commitment F st g"
  by (simp add: finite_goal_producing_def no_commitment_def)

text \<open>
  The produced state (R5f1). The goal's output read at the production's view (@{const resolution_view_pattern}) is
  matched against the value (@{const finite_matching_bindings}): each variable of the output takes the ground pattern
  of the term it meets (@{text finite_output_substitution}). The substitution is the production's where the value is
  formed, the output's variables are the pattern's and the output under it is the value
  (@{text finite_production_substitution}); the produced state is the state under it, and the state as it is where the
  commitment produces nothing or its value does not match (@{text finite_produced_state}). It binds only variables of
  the committed goal's pattern, each to a formed ground term (@{text finite_produced_state_cases}).
\<close>

definition finite_output_substitution ::
    "'v finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> 'v \<Rightarrow> 'v finite_term_pattern" where
  "finite_output_substitution y v z = (if z |\<in>| finite_pattern_variables y then
      (case finite_relation_option (finite_matching_bindings y v) z of
        Some w \<Rightarrow> finite_exact_term_pattern w | None \<Rightarrow> Finite_Variable z)
    else Finite_Variable z)"

definition finite_production_substitution ::
    "nat resolution_view \<Rightarrow> 'v finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> ('v \<Rightarrow> 'v finite_term_pattern) option" where
  "finite_production_substitution V p v = (case resolution_view_pattern V p of None \<Rightarrow> None
    | Some xy \<Rightarrow> if finite_pattern_variables (snd xy) |\<subseteq>| finite_pattern_variables p \<and> finite_term_formed v \<and>
        finite_pattern_substitute (finite_output_substitution (snd xy) v) (snd xy) = finite_exact_term_pattern v
      then Some (finite_output_substitution (snd xy) v) else None)"

definition finite_produced_state ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_produced_state K F st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> (case commit_production K F st g of
          Some (V,v) \<Rightarrow> (case finite_production_substitution V p v of
              Some \<sigma> \<Rightarrow> resolution_state_substitute \<sigma> st
            | None \<Rightarrow> st)
        | None \<Rightarrow> st)
    | Resolution_Material_Goal q r M \<Rightarrow> st)"

lemma finite_produced_state_unproduced [simp]:
  "commit_production K F st g = None \<Longrightarrow> finite_produced_state K F st g = st"
  by (cases g) (simp_all add: finite_produced_state_def)

lemma finite_matching_bindings_subterm_formed:
  "(z,w) |\<in>| finite_matching_bindings y v \<Longrightarrow> finite_term_formed v \<Longrightarrow> finite_term_formed w"
  by (induction y arbitrary: v) (auto split: finite_factor_term.splits)

lemma finite_output_substitution_ground:
  assumes formed: "finite_term_formed v"
  shows "finite_output_substitution y v z = Finite_Variable z \<or> (z |\<in>| finite_pattern_variables y \<and>
    (\<exists>w. finite_term_formed w \<and> finite_output_substitution y v z = finite_exact_term_pattern w))"
proof (cases "z |\<in>| finite_pattern_variables y")
  case inside: True
  show ?thesis
  proof (cases "finite_relation_option (finite_matching_bindings y v) z")
    case none: None
    show ?thesis by (rule disjI1) (simp add: finite_output_substitution_def inside none)
  next
    case some: (Some w)
    have "(z,w) |\<in>| finite_matching_bindings y v" by (rule finite_relation_option_member[OF some])
    then have wf: "finite_term_formed w" using formed by (rule finite_matching_bindings_subterm_formed)
    have eq: "finite_output_substitution y v z = finite_exact_term_pattern w"
      by (simp add: finite_output_substitution_def inside some)
    show ?thesis by (rule disjI2, rule conjI[OF inside], rule exI[of _ w]) (simp add: wf eq)
  qed
next
  case outside: False
  show ?thesis by (rule disjI1) (simp add: finite_output_substitution_def outside)
qed

lemma finite_production_substitution_ground:
  assumes s: "finite_production_substitution V p v = Some \<sigma>"
  shows "\<sigma> z = Finite_Variable z \<or> (z |\<in>| finite_pattern_variables p \<and>
    (\<exists>w. finite_term_formed w \<and> \<sigma> z = finite_exact_term_pattern w))"
proof (cases "resolution_view_pattern V p")
  case none: None
  then show ?thesis using s by (simp add: finite_production_substitution_def)
next
  case some: (Some xy)
  have c: "finite_pattern_variables (snd xy) |\<subseteq>| finite_pattern_variables p" "finite_term_formed v"
    and \<sigma>: "\<sigma> = finite_output_substitution (snd xy) v"
    using s some by (simp_all add: finite_production_substitution_def split: if_splits)
  show ?thesis using finite_output_substitution_ground[OF c(2), of "snd xy" z] c(1) unfolding \<sigma>
    by (auto dest: fsubsetD)
qed

lemma finite_produced_state_cases:
  obtains (unchanged) "finite_produced_state K F st g = st"
  | (produced) \<sigma> where "finite_produced_state K F st g = resolution_state_substitute \<sigma> st"
      "\<And>z. \<sigma> z = Finite_Variable z \<or> (z |\<in>| resolution_goal_variables g \<and>
        (\<exists>w. finite_term_formed w \<and> \<sigma> z = finite_exact_term_pattern w))"
proof (cases g)
  case m: (Resolution_Material_Goal q r M)
  show thesis by (rule unchanged) (simp add: finite_produced_state_def m)
next
  case c: (Resolution_Call_Goal q r e p)
  show thesis
  proof (cases "commit_production K F st g")
    case n: None
    show thesis by (rule unchanged) (rule finite_produced_state_unproduced[OF n])
  next
    case s: (Some Vv)
    obtain V v where Vv: "Vv = (V,v)" by (cases Vv)
    have pr: "commit_production K F st (Resolution_Call_Goal q r e p) = Some (V,v)" using s Vv c by simp
    show thesis
    proof (cases "finite_production_substitution V p v")
      case n: None
      show thesis by (rule unchanged) (simp add: finite_produced_state_def c pr n)
    next
      case s': (Some \<sigma>)
      have ground: "\<And>z. \<sigma> z = Finite_Variable z \<or> (z |\<in>| resolution_goal_variables g \<and>
          (\<exists>w. finite_term_formed w \<and> \<sigma> z = finite_exact_term_pattern w))"
        using finite_production_substitution_ground[OF s'] by (simp add: c)
      show thesis
        by (rule produced[of \<sigma>, OF _ ground]) (simp add: finite_produced_state_def c pr s')
    qed
  qed
qed

lemma finite_produced_state_invariant:
  assumes I: "resolution_invariant P d t st"
  shows "resolution_invariant P d t (finite_produced_state K F st g)"
proof (cases rule: finite_produced_state_cases[of K F st g])
  case unchanged
  then show ?thesis using I by simp
next
  case (produced \<sigma>)
  have "finite_pattern_formed (\<sigma> x)" for x using produced(2)[of x] by auto
  then show ?thesis unfolding produced(1) by (rule resolution_invariant_substitute[OF I])
qed

text \<open>
  One barring rule for every committed step (task 621, q112): a committed goal, a committed material premise and a
  construction step each bar, for the rest of the search, the nodes present where the search goes on after it, beside
  those already barred (@{text finite_committed_barring}). The ranks that justify pruning do not carry across any of
  them: a commitment abandons the derivation a pruning's rank rests on, and a construction's value bound is its own.
  A committed material premise is one whose goal takes the canonical solution (@{text finite_material_committed});
  the barred set after a goal's step is the rule's where the goal is a committed material premise, and the one
  before otherwise (@{text finite_goal_barring}).
\<close>

definition finite_committed_barring ::
    "'s list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list fset" where
  "finite_committed_barring B st = B |\<union>| fimage resolution_node_position (resolution_nodes st)"

definition finite_material_committed ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_material_committed K F st g \<longleftrightarrow> (case g of
      Resolution_Material_Goal q r M \<Rightarrow> finite_canonical_solutions M \<noteq> None \<and> commit_material K F st g
    | Resolution_Call_Goal q r d p \<Rightarrow> False)"

definition finite_goal_barring ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> 's list fset" where
  "finite_goal_barring K F B st g = (if finite_material_committed K F st g then finite_committed_barring B st else B)"

lemma finite_committed_barring_subset: "B |\<subseteq>| finite_committed_barring B st"
  by (auto simp: finite_committed_barring_def)

lemma no_commitment_barring [simp]: "finite_goal_barring no_commitment F B st g = B"
  by (simp add: finite_goal_barring_def finite_material_committed_def no_commitment_def split: resolution_goal.split)

text \<open>
  The barring of a committing goal's sub-search (task 767, q134's (G2)). A producing goal's sub-search starts at the
  produced state with every node present there barred, by the one barring rule of every committed step: the ranks
  that justify pruning do not carry across the production, which changes the goal's output. A goal committed without
  a production keeps the parent's barring.
\<close>

definition finite_goal_sub_barring ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> 's list fset" where
  "finite_goal_sub_barring K F B st g = (if commit_production K F st g = None then B
    else finite_committed_barring B (finite_produced_state K F st g))"

lemma finite_goal_sub_barring_unproduced [simp]:
  "commit_production K F st g = None \<Longrightarrow> finite_goal_sub_barring K F B st g = B"
  by (simp add: finite_goal_sub_barring_def)

lemma finite_goal_sub_barring_produced:
  assumes "commit_production K F st g \<noteq> None"
  shows "finite_goal_sub_barring K F B st g = finite_committed_barring B (finite_produced_state K F st g)"
  unfolding finite_goal_sub_barring_def by (rule if_not_P[OF assms])

section \<open>The first join below a ground focus\<close>

text \<open>
  Correction (14) of task 495's entry (task 794, build K1). At a state whose focus is a position q and whose call at q
  (the pending goal at q, or the node at q) holds no variable, every found state below answers that one call, and one
  found state decides it. There a join keeps the first block, in the order of a key, whose outcome finds, joining every
  block's diagnoses where none finds; equal keys form one block, joined as a union. At no focus and at a focus whose
  call holds a variable a join is the union. The key read at a goal's successors is structural, determinate first: the
  number of the successor's goals under the goal's position, not at it, that hold a variable. It reads no clause key,
  name or position beyond the prefix order of positions, as the focus does.
\<close>

definition finite_focus_ground :: "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_focus_ground F st = (case F of None \<Rightarrow> False | Some q \<Rightarrow>
    fBall (resolution_pending st) (\<lambda>g. resolution_goal_position g = q \<longrightarrow> resolution_goal_variables g = {||}) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = q \<longrightarrow>
      finite_pattern_variables (resolution_node_call nd) = {||}))"

lemma finite_focus_ground_none [simp]: "\<not> finite_focus_ground None st"
  by (simp add: finite_focus_ground_def)

definition finite_determinate_key :: "'s list \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> nat" where
  "finite_determinate_key q s = fcard (ffilter (\<lambda>h. take (length q) (resolution_goal_position h) = q \<and>
    resolution_goal_position h \<noteq> q \<and> resolution_goal_variables h \<noteq> {||}) (resolution_pending s))"

fun finite_first_outcome ::
    "('x \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow> 'x fset list \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_first_outcome f [] = Resolution_Outcome {||} {||}"
| "finite_first_outcome f (X # Xs) = (let R = finite_outcome_union (fimage f X) in
    if resolution_found R \<noteq> {||} then R
    else let R' = finite_first_outcome f Xs in
      Resolution_Outcome (resolution_found R') (resolution_diagnoses R |\<union>| resolution_diagnoses R'))"

definition finite_key_blocks :: "('x \<Rightarrow> nat) \<Rightarrow> 'x fset \<Rightarrow> 'x fset list" where
  "finite_key_blocks key X = map (\<lambda>k. ffilter (\<lambda>x. key x = k) X) (sorted_list_of_fset (fimage key X))"

definition finite_search_join ::
    "'s list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow>
      ('x \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow> 'x fset \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_search_join F st key f X = (if finite_focus_ground F st
    then finite_first_outcome f (finite_key_blocks key X) else finite_outcome_union (fimage f X))"

text \<open>The join laws: a found state of a join is one of a part's; off a ground focus the join is the union, and a join
  of one block is too; where a join finds nothing every part was evaluated and gave its diagnoses.\<close>

lemma finite_outcome_union_part:
  assumes "Oc |\<in>| Os"
  shows "resolution_found Oc |\<subseteq>| resolution_found (finite_outcome_union Os)"
    and "resolution_diagnoses Oc |\<subseteq>| resolution_diagnoses (finite_outcome_union Os)"
  unfolding finite_outcome_union_def by (auto intro!: fsubsetI resolution_union_member[OF assms])

lemma finite_outcome_union_nested:
  "finite_outcome_union {|A, finite_outcome_union Os|} = finite_outcome_union (finsert A Os)"
  unfolding finite_outcome_union_def by (auto intro!: fset_eqI simp: resolution_fset_simps)

lemma finite_key_blocks_subset: "Y \<in> set (finite_key_blocks key X) \<Longrightarrow> x |\<in>| Y \<Longrightarrow> x |\<in>| X"
  unfolding finite_key_blocks_def by auto

lemma finite_key_blocks_cover:
  assumes x: "x |\<in>| X"
  shows "\<exists>Y. Y \<in> set (finite_key_blocks key X) \<and> x |\<in>| Y"
proof -
  have "ffilter (\<lambda>y. key y = key x) X \<in> set (finite_key_blocks key X)"
    using x unfolding finite_key_blocks_def by (auto intro!: image_eqI[where x="key x"])
  moreover have "x |\<in>| ffilter (\<lambda>y. key y = key x) X" using x by simp
  ultimately show ?thesis by blast
qed

lemma finite_first_outcome_found:
  "s |\<in>| resolution_found (finite_first_outcome f Xs) \<Longrightarrow>
    \<exists>Y x. Y \<in> set Xs \<and> x |\<in>| Y \<and> s |\<in>| resolution_found (f x)"
proof (induction Xs)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  show ?case
  proof (cases "resolution_found (finite_outcome_union (fimage f X)) = {||}")
    case True
    then have "s |\<in>| resolution_found (finite_first_outcome f Xs)" using Cons.prems by (simp add: Let_def)
    then show ?thesis using Cons.IH by auto
  next
    case False
    then have "s |\<in>| resolution_found (finite_outcome_union (fimage f X))" using Cons.prems by (simp add: Let_def)
    then show ?thesis by (auto simp: finite_outcome_union_def resolution_fset_simps)
  qed
qed

lemma finite_first_outcome_unfound:
  assumes "resolution_found (finite_first_outcome f Xs) = {||}" and "Y \<in> set Xs" and "x |\<in>| Y"
  shows "s |\<notin>| resolution_found (f x) \<and>
    (D |\<in>| resolution_diagnoses (f x) \<longrightarrow> D |\<in>| resolution_diagnoses (finite_first_outcome f Xs))"
  using assms
proof (induction Xs)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  let ?R = "finite_outcome_union (fimage f X)"
  have none: "resolution_found ?R = {||}"
  proof (rule ccontr)
    assume ne: "resolution_found ?R \<noteq> {||}"
    then have "finite_first_outcome f (X # Xs) = ?R" by (simp add: Let_def)
    then show False using Cons.prems(1) ne by simp
  qed
  have eq: "finite_first_outcome f (X # Xs) = Resolution_Outcome (resolution_found (finite_first_outcome f Xs))
      (resolution_diagnoses ?R |\<union>| resolution_diagnoses (finite_first_outcome f Xs))"
    using none by (simp add: Let_def)
  have rest: "resolution_found (finite_first_outcome f Xs) = {||}" using Cons.prems(1) unfolding eq by simp
  show ?case
  proof (cases "Y = X")
    case True
    then have x: "x |\<in>| X" using Cons.prems(3) by simp
    have mem: "f x |\<in>| fimage f X" using x by simp
    note part = finite_outcome_union_part[OF mem]
    show ?thesis unfolding eq using part none by (auto dest: fsubsetD)
  next
    case False
    then have "Y \<in> set Xs" using Cons.prems(2) by simp
    then show ?thesis unfolding eq using Cons.IH[OF rest _ Cons.prems(3)] by auto
  qed
qed

lemma finite_search_join_found:
  assumes s: "s |\<in>| resolution_found (finite_search_join F st key f X)"
  shows "\<exists>x. x |\<in>| X \<and> s |\<in>| resolution_found (f x)"
proof (cases "finite_focus_ground F st")
  case True
  then have "s |\<in>| resolution_found (finite_first_outcome f (finite_key_blocks key X))"
    using s by (simp add: finite_search_join_def)
  then have "\<exists>Y x. Y \<in> set (finite_key_blocks key X) \<and> x |\<in>| Y \<and> s |\<in>| resolution_found (f x)"
    by (rule finite_first_outcome_found)
  then show ?thesis using finite_key_blocks_subset by metis
next
  case False
  then show ?thesis using s by (auto simp: finite_search_join_def finite_outcome_union_def resolution_fset_simps)
qed

lemma finite_search_join_union:
  "\<not> finite_focus_ground F st \<Longrightarrow> finite_search_join F st key f X = finite_outcome_union (fimage f X)"
  by (simp add: finite_search_join_def)

lemma finite_first_outcome_repeated:
  assumes "\<forall>Y\<in>set Ys. Y = X" and "Ys \<noteq> []"
  shows "finite_first_outcome f Ys = finite_outcome_union (fimage f X)"
  using assms
proof (induction Ys)
  case Nil
  then show ?case by simp
next
  case (Cons Y Ys)
  obtain A D where R: "finite_outcome_union (fimage f X) = Resolution_Outcome A D"
    by (cases "finite_outcome_union (fimage f X)")
  have Y: "Y = X" using Cons.prems(1) by simp
  show ?case
  proof (cases "Ys = []")
    case True
    then show ?thesis using Y R by (auto simp: Let_def)
  next
    case False
    then have "finite_first_outcome f Ys = Resolution_Outcome A D" using Cons.IH Cons.prems(1) R by simp
    then show ?thesis using Y R by (auto simp: Let_def)
  qed
qed

lemma finite_search_join_block:
  "finite_search_join F st (\<lambda>_. k) f X = finite_outcome_union (fimage f X)"
proof (cases "finite_focus_ground F st \<and> X \<noteq> {||}")
  case True
  obtain x0 where x0: "x0 |\<in>| X" using True by (metis all_not_fin_conv)
  have ne: "sorted_list_of_fset (fimage (\<lambda>_. k) X) \<noteq> []"
  proof
    assume "sorted_list_of_fset (fimage (\<lambda>_. k) X) = []"
    then have "set (sorted_list_of_fset (fimage (\<lambda>_. k) X)) = {}" by simp
    then show False using x0 by (simp add: fimage.rep_eq)
  qed
  have same: "\<forall>Y\<in>set (finite_key_blocks (\<lambda>_. k) X). Y = X"
    by (auto simp: finite_key_blocks_def fimage.rep_eq)
  have "finite_key_blocks (\<lambda>_. k) X \<noteq> []" using ne by (simp add: finite_key_blocks_def)
  then show ?thesis using True finite_first_outcome_repeated[OF same] by (simp add: finite_search_join_def)
next
  case False
  show ?thesis
  proof (cases "finite_focus_ground F st")
    case True
    then have X: "X = {||}" using False by simp
    have "set (sorted_list_of_fset (fimage (\<lambda>_. k) X)) = {}" using X by simp
    then have "sorted_list_of_fset (fimage (\<lambda>_. k) X) = []" by (rule iffD1[OF set_empty])
    then show ?thesis using True X by (simp add: finite_search_join_def finite_key_blocks_def finite_outcome_union_def)
  next
    case False
    then show ?thesis by (simp add: finite_search_join_def)
  qed
qed

lemma finite_search_join_unfound:
  assumes none: "resolution_found (finite_search_join F st key f X) = {||}" and x: "x |\<in>| X"
  shows "s |\<notin>| resolution_found (f x) \<and>
    (D |\<in>| resolution_diagnoses (f x) \<longrightarrow> D |\<in>| resolution_diagnoses (finite_search_join F st key f X))"
proof (cases "finite_focus_ground F st")
  case True
  obtain Y where Y: "Y \<in> set (finite_key_blocks key X)" "x |\<in>| Y" using finite_key_blocks_cover[OF x] by blast
  have "resolution_found (finite_first_outcome f (finite_key_blocks key X)) = {||}"
    using none True by (simp add: finite_search_join_def)
  then have "s |\<notin>| resolution_found (f x) \<and>
      (D |\<in>| resolution_diagnoses (f x) \<longrightarrow> D |\<in>| resolution_diagnoses (finite_first_outcome f (finite_key_blocks key X)))"
    by (rule finite_first_outcome_unfound[OF _ Y])
  then show ?thesis using True by (simp add: finite_search_join_def)
next
  case False
  have mem: "f x |\<in>| fimage f X" using x by simp
  note part = finite_outcome_union_part[OF mem]
  show ?thesis using part none False by (auto simp: finite_search_join_def dest: fsubsetD)
qed

definition finite_committed_goal_outcome ::
    "('s::linorder list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      ('a,'s,'d,'c) resolution_commitment \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list option \<Rightarrow>
      's list fset \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_goal_outcome rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
     else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
     else if finite_goal_committing K F st g then
       (let q = resolution_goal_position g;
          sub = rec (Some q) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g) in
        finite_outcome_union {|Resolution_Outcome {||} (resolution_diagnoses sub),
          finite_search_join F st (\<lambda>_. 0) (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found sub))|})
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
         (rec F (finite_goal_barring K F B st g)) S)"

text \<open>The kept continuations of a committed goal form one block, so their join is the union; only a goal's
  successors are joined by the key.\<close>

lemma finite_committed_goal_outcome_eq:
  "finite_committed_goal_outcome rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
     else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
     else if finite_goal_committing K F st g then
       (let q = resolution_goal_position g;
          sub = rec (Some q) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g) in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found sub)))))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
         (rec F (finite_goal_barring K F B st g)) S)"
  by (simp only: finite_committed_goal_outcome_def Let_def finite_search_join_block finite_outcome_union_nested)

text \<open>A found state of the committed step at a goal is a found state of a kept continuation of its sub-search, or of
  the search from one of its committed successors: the join case of every lemma that follows the search.\<close>

lemma finite_committed_goal_outcome_found:
  assumes found: "s |\<in>| resolution_found (finite_committed_goal_outcome rec K P F B st g)"
  shows "(finite_goal_committing K F st g \<longrightarrow> (\<exists>s0. s0 |\<in>| finite_kept (resolution_goal_position g)
      (resolution_found (rec (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g)
        (finite_produced_state K F st g))) \<and>
      s0 |\<in>| resolution_found (rec (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g)
        (finite_produced_state K F st g)) \<and>
      s |\<in>| resolution_found (rec F (finite_committed_barring B s0) s0))) \<and>
    (\<not> finite_goal_committing K F st g \<longrightarrow> (\<exists>s1. s1 |\<in>| finite_committed_successors K P F st g \<and>
      s |\<in>| resolution_found (rec F (finite_goal_barring K F B st g) s1)))"
proof (cases "finite_goal_committing K F st g")
  case True
  obtain s0 where k: "s0 |\<in>| finite_kept (resolution_goal_position g)
      (resolution_found (rec (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g)
        (finite_produced_state K F st g)))"
    and s: "s |\<in>| resolution_found (rec F (finite_committed_barring B s0) s0)"
    using found True
    by (auto simp: finite_committed_goal_outcome_eq Let_def finite_outcome_union_def resolution_fset_simps split: if_splits)
  then show ?thesis using True fsubsetD[OF finite_kept_subset] by blast
next
  case False
  have "s |\<in>| resolution_found (finite_search_join F st (finite_determinate_key (resolution_goal_position g))
      (rec F (finite_goal_barring K F B st g)) (finite_committed_successors K P F st g))"
    using found False by (auto simp: finite_committed_goal_outcome_eq Let_def split: if_splits)
  then show ?thesis using False by (auto dest!: finite_search_join_found)
qed

text \<open>At a goal whose commitment produces nothing the committed step is the step before the production.\<close>

lemma finite_committed_goal_outcome_unproduced:
  assumes none: "commit_production K F st g = None"
  shows "finite_committed_goal_outcome rec K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
     else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
     else if finite_goal_committed K F st g then
       (let q = resolution_goal_position g; sub = rec (Some q) B st in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. rec F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found sub)))))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
         (rec F (finite_goal_barring K F B st g)) S)"
  using none by (simp add: finite_committed_goal_outcome_eq finite_goal_committing_unproduced[OF none])

text \<open>
  A construction step is committed as a goal is: every node present at it is barred in the rest of the search, for
  the ranks that justify pruning do not carry across a construction (task 526, q110), and it constructs at the
  selected nodes in the focus alone. Selection reads the focus and the step the whole state; at a node in the
  focus, under the holders invariant of @{text Factor_Construction_Holders}, every goal holding a registered variable
  of the node stands at one of its premises and so in the focus, and the two read the same holders. A selected node
  outside the focus is not constructed inside the sub-search: the branch stops as stuck, unresolved.
\<close>

primrec finite_committed_search_by ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search_by sel \<kappa> K P 0 F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else Resolution_Outcome {||} {|Resolution_Cut (finite_focus_pending F st)|})"
| "finite_committed_search_by sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}
        else finite_outcome_union (fimage (finite_committed_search_by sel \<kappa> K P n F
            (finite_committed_barring B st)) (fimage (finite_construction_step \<kappa> P st) M)))
    | Select_Goals G \<Rightarrow> finite_outcome_union
        (fimage (finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F B st) G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))))"

definition finite_committed_search ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search \<kappa> K P = finite_committed_search_by (finite_committed_select \<kappa> K P) \<kappa> K P"

text \<open>
  The search at a priority @{text pr} of F1's selection (task 802): every statement below that reads the selection
  only through F1's facts at a priority is stated at any priority, and the committed search is its instance at the
  commitment's own priority (@{thm [source] finite_committed_search_def}).
\<close>

abbreviation finite_committed_search_at ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_committed_search_at pr \<kappa> K P \<equiv> finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P"

text \<open>
  At a commitment that produces nothing the committed search is the search before the production: its step at a
  committed goal starts the goal's sub-search from the state the goal stands at.
\<close>

lemma finite_committed_search_by_unproduced:
  assumes none: "\<And>F st g. commit_production K F st g = None"
  shows "finite_committed_search_by sel \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else (case sel (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}
        else finite_outcome_union (fimage (finite_committed_search_by sel \<kappa> K P n F
            (finite_committed_barring B st)) (fimage (finite_construction_step \<kappa> P st) M)))
    | Select_Goals G \<Rightarrow> finite_outcome_union (fimage (\<lambda>g.
        if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
        else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
        else if finite_goal_committed K F st g then
          (let q = resolution_goal_position g; sub = finite_committed_search_by sel \<kappa> K P n (Some q) B st in
           finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
             (fimage (\<lambda>s. finite_committed_search_by sel \<kappa> K P n F (finite_committed_barring B s) s)
               (finite_kept q (resolution_found sub)))))
        else let S = finite_committed_successors K P F st g in
          if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
            else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
          else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
            (finite_committed_search_by sel \<kappa> K P n F (finite_goal_barring K F B st g)) S)
        G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))))"
proof -
  have "finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F B st g =
    (if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
     else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
     else if finite_goal_committed K F st g then
       (let q = resolution_goal_position g; sub = finite_committed_search_by sel \<kappa> K P n (Some q) B st in
        finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
          (fimage (\<lambda>s. finite_committed_search_by sel \<kappa> K P n F (finite_committed_barring B s) s)
            (finite_kept q (resolution_found sub)))))
     else let S = finite_committed_successors K P F st g in
       if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
         else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
       else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
            (finite_committed_search_by sel \<kappa> K P n F (finite_goal_barring K F B st g)) S)"
    for g by (rule finite_committed_goal_outcome_unproduced[OF none])
  then have "finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> K P n) K P F B st = (\<lambda>g.
    if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
    else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
    else if finite_goal_committed K F st g then
      (let q = resolution_goal_position g; sub = finite_committed_search_by sel \<kappa> K P n (Some q) B st in
       finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
         (fimage (\<lambda>s. finite_committed_search_by sel \<kappa> K P n F (finite_committed_barring B s) s)
           (finite_kept q (resolution_found sub)))))
    else let S = finite_committed_successors K P F st g in
      if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
        else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
      else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
            (finite_committed_search_by sel \<kappa> K P n F (finite_goal_barring K F B st g)) S)"
    by (rule ext)
  then show ?thesis by (simp only: finite_committed_search_by.simps(2))
qed

lemma finite_committed_search_unproduced:
  assumes none: "\<And>F st g. commit_production K F st g = None"
  shows "finite_committed_search \<kappa> K P (Suc n) F B st = (if finite_focus_pending F st={||}
    then Resolution_Outcome {|st|} {||} else (case finite_committed_select \<kappa> K P (finite_focused F st) of
      Select_Construction N \<Rightarrow> (let M = ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N in
        if M = {||} then Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}
        else finite_outcome_union (fimage (finite_committed_search \<kappa> K P n F
            (finite_committed_barring B st)) (fimage (finite_construction_step \<kappa> P st) M)))
    | Select_Goals G \<Rightarrow> finite_outcome_union (fimage (\<lambda>g.
        if finite_pruned (finite_unbarred B st) g then Resolution_Outcome {||} {||}
        else if finite_pruned (finite_barred B st) g then Resolution_Outcome {||} {|Resolution_Cut {|g|}|}
        else if finite_goal_committed K F st g then
          (let q = resolution_goal_position g; sub = finite_committed_search \<kappa> K P n (Some q) B st in
           finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses sub))
             (fimage (\<lambda>s. finite_committed_search \<kappa> K P n F (finite_committed_barring B s) s)
               (finite_kept q (resolution_found sub)))))
        else let S = finite_committed_successors K P F st g in
          if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
            else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
          else finite_search_join F st (finite_determinate_key (resolution_goal_position g))
            (finite_committed_search \<kappa> K P n F (finite_goal_barring K F B st g)) S)
        G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))))"
  unfolding finite_committed_search_def by (rule finite_committed_search_by_unproduced[OF none])

section \<open>At no commitment and no construction the search is R3's\<close>

text \<open>
  At no commitment the search differs from R3's only at a construction step, which it bars; a search whose selection
  never constructs is R3's (task 526: with a registered construction R3's search is sound and not exact).
\<close>

theorem finite_committed_search_by_plain:
  assumes free: "\<And>st N. sel st \<noteq> Select_Construction N"
  shows "finite_committed_search_by sel \<kappa> no_commitment P n None {||} = finite_resolution_search_by sel \<kappa> P n"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  have out: "finite_committed_goal_outcome (finite_committed_search_by sel \<kappa> no_commitment P n) no_commitment P None {||} st =
      finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st" for st
    by (rule ext) (simp add: finite_committed_goal_outcome_def finite_search_join_def finite_goal_outcome_def Suc.IH Let_def)
  show ?case by (rule ext) (simp add: out Suc.IH free split: resolution_selection.split)
qed

corollary finite_committed_search_plain:
  assumes free: "\<And>st N. finite_resolution_select \<kappa> P st \<noteq> Select_Construction N"
  shows "finite_committed_search \<kappa> no_commitment P n None {||} = finite_resolution_search \<kappa> P n"
  by (simp add: finite_committed_search_def finite_resolution_search_def finite_committed_search_by_plain[OF free])

section \<open>The lifting at a focused barred support\<close>

text \<open>
  The committed search solves the goals of its focus, prunes a ground goal equal to an unbarred ancestor's call and
  ends a branch reaching a barred ancestor's call with a diagnosis. Its lifting is stated at a support of the focus
  whose ranks cover the unbarred ancestors only (@{const resolution_supported_at}): from such a support the search
  returns a found state supported at its focus, or a diagnosis that is not a witnessed failure. It rests on two
  premises, each a property of the commitment and the construction and not of the search: the exchange
  (@{text finite_commitment_exchanges}), that at a committed call some kept state of the committed goal's sub-search
  is supported with every node then present barred, and at a committed material premise some canonical successor is
  supported; and that a selected construction keeps a support (@{text finite_construction_lifts}). Both hold at no
  commitment and at the empty construction. The steps are R4's, at the focused barred support.
\<close>

definition finite_witnessed_diagnosis :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> bool" where
  "finite_witnessed_diagnosis D \<longleftrightarrow> (case D of Resolution_Witnessed W g \<Rightarrow> True | _ \<Rightarrow> False)"

definition finite_lifted_outcome ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome \<Rightarrow> bool" where
  "finite_lifted_outcome U F P R \<longleftrightarrow>
    (\<exists>st' B' \<theta>'. st' |\<in>| resolution_found R \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
    (\<exists>D. D |\<in>| resolution_diagnoses R \<and> \<not> finite_witnessed_diagnosis D)"

lemma finite_lifted_outcome_union:
  assumes mem: "Oc |\<in>| Os" and lifted: "finite_lifted_outcome U F P Oc"
  shows "finite_lifted_outcome U F P (finite_outcome_union Os)"
  using lifted unfolding finite_lifted_outcome_def
proof (elim disjE exE conjE)
  fix st' B' \<theta>' assume f: "st' |\<in>| resolution_found Oc" and s: "resolution_supported_at U F B' P st' \<theta>'"
  have "st' |\<in>| resolution_found (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_found, OF mem f] by simp
  then show "(\<exists>st' B' \<theta>'. st' |\<in>| resolution_found (finite_outcome_union Os) \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
      (\<exists>D. D |\<in>| resolution_diagnoses (finite_outcome_union Os) \<and> \<not> finite_witnessed_diagnosis D)"
    using s by blast
next
  fix D assume d: "D |\<in>| resolution_diagnoses Oc" and w: "\<not> finite_witnessed_diagnosis D"
  have "D |\<in>| resolution_diagnoses (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_diagnoses, OF mem d] by simp
  then show "(\<exists>st' B' \<theta>'. st' |\<in>| resolution_found (finite_outcome_union Os) \<and> resolution_supported_at U F B' P st' \<theta>') \<or>
      (\<exists>D. D |\<in>| resolution_diagnoses (finite_outcome_union Os) \<and> \<not> finite_witnessed_diagnosis D)"
    using w by blast
qed

lemma finite_lifted_diagnosis:
  "D |\<in>| resolution_diagnoses R \<Longrightarrow> \<not> finite_witnessed_diagnosis D \<Longrightarrow> finite_lifted_outcome U F P R"
  unfolding finite_lifted_outcome_def by blast

lemma finite_focus_pending_focused:
  "g |\<in>| finite_focus_pending F st \<longleftrightarrow> g |\<in>| resolution_pending st \<and> resolution_focused F (resolution_goal_position g)"
  by (cases F) (auto simp: finite_focus_pending_def resolution_fset_simps)

lemma resolution_supported_at_narrow:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and focus: "resolution_focused F q"
  shows "resolution_supported_at U (Some q) B P st \<theta>"
proof -
  have w: "\<And>q'. resolution_focused (Some q) q' \<Longrightarrow> resolution_focused F q'"
    using resolution_focused_within[OF focus] by simp
  show ?thesis using sup w unfolding resolution_supported_at_def by blast
qed

lemma resolution_supported_at_unbarred:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and g: "g |\<in>| resolution_pending st"
    and focus: "resolution_focused F (resolution_goal_position g)"
  shows "\<not> finite_pruned (finite_unbarred B st) g"
proof
  assume pruned: "finite_pruned (finite_unbarred B st) g"
  then obtain q r e p where gq: "g = Resolution_Call_Goal q r e p"
    by (auto simp: finite_pruned_def split: resolution_goal.splits)
  with pruned obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd |\<notin>| B"
    "resolution_before (resolution_node_position nd) q" "resolution_node_site nd = e" "resolution_node_call nd = p"
    by (auto simp: finite_pruned_def finite_unbarred_def resolution_before_def resolution_fset_simps)
  have fq: "resolution_focused F q" using focus gq by simp
  have "resolution_rank (decode_finite_system P) (e,decode_finite_term (resolution_value \<theta> p)) <
      resolution_rank (decode_finite_system P)
        (resolution_node_site nd,decode_finite_term (resolution_value \<theta> (resolution_node_call nd)))"
    using sup g fq nd(1,2,3) unfolding gq resolution_supported_at_def by blast
  with nd(4,5) show False by simp
qed

lemma resolution_supported_at_barred_mono:
  assumes sup: "resolution_supported_at U F B P st \<theta>" and sub: "B |\<subseteq>| B'"
  shows "resolution_supported_at U F B' P st \<theta>"
proof -
  have out: "x |\<notin>| B" if "x |\<notin>| B'" for x using sub that by (auto dest: fsubsetD)
  show ?thesis using sup out unfolding resolution_supported_at_def by blast
qed

text \<open>
  The lifting at a selection parameter. The committed search takes its selection as a parameter
  (@{const finite_committed_search_by}), and its lifting is stated once, at any selection and any invariant J of the
  states searched: a selection meeting R4's conditions (a nonempty set of pending goals, none a waiting material premise,
  as @{text finite_resolution_select_lifts} of @{text Factor_Resolution_Completeness} states of every selection at a priority), an invariant that is a
  pattern-root invariant (@{const resolution_pattern_invariant}) and is kept by every committed successor of a selected
  goal, and an exchange and a construction premise read at that selection and invariant
  (@{text finite_lifting_premises}). From a state keeping J and a focused barred support the search returns a found
  state supported at its focus, or a diagnosis that is not a witnessed failure; where the search commits nothing and
  never constructs (@{text finite_commits_nothing}), every step is R4's call, material or goal step, so the found state
  is supported at the barring the search started with and the root takes there every value it took
  (@{const resolution_root_value}). The committed lifting is its instance at the committed search's own selection, J the
  ground call's invariant with the holders invariant of @{text Factor_Construction_Holders}
  (@{text finite_committed_lifting_premises}); at no commitment and a selection that never constructs it states R4's
  lifting (@{text finite_resolution_lifting_by} of @{text Factor_Resolution_Completeness}), from a pattern-root invariant, the root's value kept, so the
  holders invariant, which holds at no pattern root, is not among the lifting's premises.
\<close>

definition finite_commits_nothing ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      bool" where
  "finite_commits_nothing K sel \<longleftrightarrow> (\<forall>F st g. \<not> finite_goal_committing K F st g \<and> \<not> commit_material K F st g) \<and>
    (\<forall>st N. sel st \<noteq> Select_Construction N)"

lemma finite_commits_nothing_none:
  assumes free: "\<And>st N. sel st \<noteq> Select_Construction N"
  shows "finite_commits_nothing no_commitment sel"
proof -
  have committing: "\<not> finite_goal_committing no_commitment F st g" for F st g by (rule no_commitment_committing)
  have material: "\<not> commit_material no_commitment F st g" for F st g by (simp add: no_commitment_def)
  show ?thesis using committing material free unfolding finite_commits_nothing_def by blast
qed

definition finite_keeping_outcome ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> 's list option \<Rightarrow> 's list fset \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> (('s,'a) resolution_variable \<Rightarrow> finite_factor_term) \<Rightarrow> bool \<Rightarrow>
      ('a,'s,'d,'c) resolution_outcome \<Rightarrow> bool" where
  "finite_keeping_outcome U F B P st \<theta> c R \<longleftrightarrow>
    (\<exists>st' B' \<theta>'. st' |\<in>| resolution_found R \<and> resolution_supported_at U F B' P st' \<theta>' \<and>
      (c \<longrightarrow> B' = B \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v))) \<or>
    (\<exists>D. D |\<in>| resolution_diagnoses R \<and> \<not> finite_witnessed_diagnosis D)"

lemma finite_keeping_outcome_lifted:
  "finite_keeping_outcome U F B P st \<theta> c R \<Longrightarrow> finite_lifted_outcome U F P R"
  unfolding finite_keeping_outcome_def finite_lifted_outcome_def by blast

lemma finite_keeping_outcome_found:
  "st |\<in>| resolution_found R \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow> finite_keeping_outcome U F B P st \<theta> c R"
  unfolding finite_keeping_outcome_def by blast

lemma finite_keeping_outcome_diagnosis:
  "D |\<in>| resolution_diagnoses R \<Longrightarrow> \<not> finite_witnessed_diagnosis D \<Longrightarrow> finite_keeping_outcome U F B P st \<theta> c R"
  unfolding finite_keeping_outcome_def by blast

lemma finite_keeping_outcome_step:
  assumes kept: "finite_keeping_outcome U F B' P st' \<theta>' c R"
    and step: "c \<Longrightarrow> B' = B \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)"
  shows "finite_keeping_outcome U F B P st \<theta> c R"
  using kept step unfolding finite_keeping_outcome_def by blast

lemma finite_keeping_outcome_union:
  assumes mem: "Oc |\<in>| Os" and kept: "finite_keeping_outcome U F B P st \<theta> c Oc"
  shows "finite_keeping_outcome U F B P st \<theta> c (finite_outcome_union Os)"
proof -
  have found: "\<And>s. s |\<in>| resolution_found Oc \<Longrightarrow> s |\<in>| resolution_found (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_found, OF mem] by simp
  have diag: "\<And>D. D |\<in>| resolution_diagnoses Oc \<Longrightarrow> D |\<in>| resolution_diagnoses (finite_outcome_union Os)"
    unfolding finite_outcome_union_def using resolution_union_member[where f=resolution_diagnoses, OF mem] by simp
  show ?thesis using kept found diag unfolding finite_keeping_outcome_def by blast
qed

text \<open>
  The exchange and the construction premise at a selection and an invariant J: those of @{text finite_commitment_exchanges}
  and @{text finite_construction_lifts}, read at the goals and constructions the selection selects, the committed
  sub-search at the same selection, and J kept at the produced state, at the kept state and at a construction step.
\<close>

text \<open>
  A part's keeping outcome is carried to the join. Off a ground focus the join is the union. At a ground focus, where
  the join finds nothing every part was evaluated and gave its diagnoses; where it finds, its found states are
  supported by the hypothesis: a found state at the focus holds no pending goal there, so the conditions on focused
  goals are vacuous and its placement and root values are what the hypothesis supplies.
\<close>

lemma finite_search_join_lifted:
  assumes x0: "x0 |\<in>| X" and kept: "finite_keeping_outcome U F B P st \<theta> c (f x0)"
    and found: "\<And>s. s |\<in>| resolution_found (finite_search_join F' st' key f X) \<Longrightarrow> finite_focus_ground F' st' \<Longrightarrow>
      \<exists>B' \<theta>'. resolution_supported_at U F B' P s \<theta>' \<and>
        (c \<longrightarrow> B' = B \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value s \<theta>' v))"
  shows "finite_keeping_outcome U F B P st \<theta> c (finite_search_join F' st' key f X)"
proof (cases "finite_focus_ground F' st'")
  case False
  have mem: "f x0 |\<in>| fimage f X" using x0 by simp
  show ?thesis unfolding finite_search_join_union[OF False] by (rule finite_keeping_outcome_union[OF mem kept])
next
  case ground: True
  show ?thesis
  proof (cases "resolution_found (finite_search_join F' st' key f X) = {||}")
    case True
    have "\<exists>D. D |\<in>| resolution_diagnoses (f x0) \<and> \<not> finite_witnessed_diagnosis D"
      using kept finite_search_join_unfound[OF True x0] unfolding finite_keeping_outcome_def by blast
    then obtain D where D: "D |\<in>| resolution_diagnoses (f x0)" "\<not> finite_witnessed_diagnosis D" by blast
    have "D |\<in>| resolution_diagnoses (finite_search_join F' st' key f X)"
      using finite_search_join_unfound[OF True x0] D(1) by blast
    then show ?thesis using D(2) by (rule finite_keeping_outcome_diagnosis)
  next
    case False
    then obtain s where s: "s |\<in>| resolution_found (finite_search_join F' st' key f X)" by (metis all_not_fin_conv)
    show ?thesis using found[OF s ground] s unfolding finite_keeping_outcome_def by blast
  qed
qed

definition finite_exchanges_by ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_exchanges_by U J sel \<kappa> K P \<longleftrightarrow>
    (\<forall>n F B st \<theta> G g. J st \<longrightarrow> resolution_supported_at U F B P st \<theta> \<longrightarrow>
      sel (finite_focused F st) = Select_Goals G \<longrightarrow> g |\<in>| G \<longrightarrow>
      (finite_goal_committing K F st g \<longrightarrow> J (finite_produced_state K F st g) \<and>
        (\<exists>\<theta>1. resolution_supported_at U (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) P
          (finite_produced_state K F st g) \<theta>1) \<and>
        (\<forall>s0 B0 \<theta>0. s0 |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P n (Some (resolution_goal_position g))
            (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g)) \<longrightarrow>
          resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0 \<longrightarrow>
          (\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search_by sel \<kappa> K P n
              (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g))) \<and>
            J s \<and> resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'))) \<and>
      (\<forall>q r M Ws. g = Resolution_Material_Goal q r M \<longrightarrow> finite_canonical_solutions M = Some Ws \<longrightarrow>
        commit_material K F st g \<longrightarrow>
        (\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
          resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>')))"

lemma finite_exchanges_byI:
  assumes produced: "\<And>F B st \<theta> G g. J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
      sel (finite_focused F st) = Select_Goals G \<Longrightarrow> g |\<in>| G \<Longrightarrow> finite_goal_committing K F st g \<Longrightarrow>
      J (finite_produced_state K F st g)"
    and support: "\<And>F B st \<theta> G g. J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
      sel (finite_focused F st) = Select_Goals G \<Longrightarrow> g |\<in>| G \<Longrightarrow> finite_goal_committing K F st g \<Longrightarrow>
      \<exists>\<theta>1. resolution_supported_at U (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) P
        (finite_produced_state K F st g) \<theta>1"
    and kept: "\<And>n F B st \<theta> G g s0 B0 \<theta>0. J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
      sel (finite_focused F st) = Select_Goals G \<Longrightarrow> g |\<in>| G \<Longrightarrow> finite_goal_committing K F st g \<Longrightarrow>
      s0 |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P n (Some (resolution_goal_position g))
        (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g)) \<Longrightarrow>
      resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0 \<Longrightarrow>
      \<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search_by sel \<kappa> K P n
          (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g))) \<and>
        J s \<and> resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
    and material: "\<And>F B st \<theta> G g q r M Ws. J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
      sel (finite_focused F st) = Select_Goals G \<Longrightarrow> g |\<in>| G \<Longrightarrow> g = Resolution_Material_Goal q r M \<Longrightarrow>
      finite_canonical_solutions M = Some Ws \<Longrightarrow> commit_material K F st g \<Longrightarrow>
      \<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
        resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
  shows "finite_exchanges_by U J sel \<kappa> K P"
  unfolding finite_exchanges_by_def
proof (intro allI impI conjI)
  fix n F B st \<theta> G g
  assume J: "J st" and sup: "resolution_supported_at U F B P st \<theta>"
    and sel: "sel (finite_focused F st) = Select_Goals G" and g: "g |\<in>| G"
  { assume c: "finite_goal_committing K F st g"
    show "J (finite_produced_state K F st g)" by (rule produced[OF J sup sel g c])
    show "\<exists>\<theta>1. resolution_supported_at U (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) P
        (finite_produced_state K F st g) \<theta>1" by (rule support[OF J sup sel g c])
    fix s0 B0 \<theta>0
    assume s0: "s0 |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P n (Some (resolution_goal_position g))
        (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g))"
      and s0sup: "resolution_supported_at U (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
    show "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search_by sel \<kappa> K P n
          (Some (resolution_goal_position g)) (finite_goal_sub_barring K F B st g) (finite_produced_state K F st g))) \<and>
        J s \<and> resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
      by (rule kept[OF J sup sel g c s0 s0sup]) }
  fix q r M Ws
  assume gm: "g = Resolution_Material_Goal q r M" and Ws: "finite_canonical_solutions M = Some Ws"
    and cm: "commit_material K F st g"
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
    by (rule material[OF J sup sel g gm Ws cm])
qed

definition finite_constructions_by ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_constructions_by U J sel \<kappa> P \<longleftrightarrow>
    (\<forall>F B st \<theta> N nd. J st \<longrightarrow> resolution_supported_at U F B P st \<theta> \<longrightarrow>
      sel (finite_focused F st) = Select_Construction N \<longrightarrow> nd |\<in>| N \<longrightarrow> resolution_focused F (resolution_node_position nd) \<longrightarrow>
      J (finite_construction_step \<kappa> P st nd) \<and>
      (\<exists>\<theta>'. resolution_supported_at U F (finite_committed_barring B st) P (finite_construction_step \<kappa> P st nd) \<theta>'))"

text \<open>
  The first join below a ground focus returns the found states of its first finding block, which need not be those of
  the part the lifting follows: every found state of a search from a supported state at a ground focus is supported
  there, and keeps the root values where the search commits nothing. The committed search's own premises discharge it
  (@{text finite_committed_ground_founds_at}).
\<close>

definition finite_ground_founds_by ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_ground_founds_by U J sel \<kappa> K P \<longleftrightarrow>
    (\<forall>n q B st \<theta> s. J st \<longrightarrow> resolution_supported_at U (Some q) B P st \<theta> \<longrightarrow>
      finite_focus_ground (Some q) st \<longrightarrow>
      s |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P n (Some q) B st) \<longrightarrow>
      (\<exists>B' \<theta>'. resolution_supported_at U (Some q) B' P s \<theta>' \<and>
        (finite_commits_nothing K sel \<longrightarrow> B' = B \<and>
          (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value s \<theta>' v))))"

definition finite_lifting_premises ::
    "(('s,'a) resolution_variable \<Rightarrow> bool) \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_commitment \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_lifting_premises U J sel \<kappa> K P \<longleftrightarrow>
    (\<forall>st G. sel st = Select_Goals G \<longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))) \<and>
    (\<forall>st. J st \<longrightarrow> (\<exists>d \<pi>. resolution_pattern_invariant P d \<pi> st)) \<and>
    (\<forall>F st G g s. J st \<longrightarrow> sel (finite_focused F st) = Select_Goals G \<longrightarrow> g |\<in>| G \<longrightarrow>
      s |\<in>| finite_committed_successors K P F st g \<longrightarrow> J s) \<and>
    finite_exchanges_by U J sel \<kappa> K P \<and> finite_constructions_by U J sel \<kappa> P \<and>
    finite_ground_founds_by U J sel \<kappa> K P"

lemma finite_lifting_premises_goals:
  assumes given: "finite_lifting_premises U J sel \<kappa> K P" and sel: "sel st = Select_Goals G"
  shows "G |\<subseteq>| resolution_pending st"
  using given sel unfolding finite_lifting_premises_def by (blast intro: fsubsetI)

theorem finite_committed_lifting_by:
  assumes given: "finite_lifting_premises U J sel \<kappa> K P"
    and foreign: "\<And>z. U z \<Longrightarrow> snd z |\<notin>| finite_program_variables P"
  shows "J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    finite_keeping_outcome U F B P st \<theta> (finite_commits_nothing K sel) (finite_committed_search_by sel \<kappa> K P n F B st)"
proof -
  have selection: "\<And>st G. sel st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> (resolution_is_call g \<or> finite_solvable_material_goal g))"
    and pattern: "\<And>st. J st \<Longrightarrow> \<exists>d \<pi>. resolution_pattern_invariant P d \<pi> st"
    and successors: "\<And>F st G g s. J st \<Longrightarrow> sel (finite_focused F st) = Select_Goals G \<Longrightarrow> g |\<in>| G \<Longrightarrow>
      s |\<in>| finite_committed_successors K P F st g \<Longrightarrow> J s"
    and exchanges: "finite_exchanges_by U J sel \<kappa> K P" and constructions: "finite_constructions_by U J sel \<kappa> P"
    and grounds: "finite_ground_founds_by U J sel \<kappa> K P"
    using given unfolding finite_lifting_premises_def by blast+
  show "J st \<Longrightarrow> resolution_supported_at U F B P st \<theta> \<Longrightarrow>
    finite_keeping_outcome U F B P st \<theta> (finite_commits_nothing K sel) (finite_committed_search_by sel \<kappa> K P n F B st)"
  proof (induction n arbitrary: F B st \<theta>)
    case 0
    show ?case
    proof (cases "finite_focus_pending F st = {||}")
      case True
      then have "st |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P 0 F B st)" by simp
      then show ?thesis by (rule finite_keeping_outcome_found[OF _ "0.prems"(2)])
    next
      case False
      then show ?thesis
        by (intro finite_keeping_outcome_diagnosis[where D="Resolution_Cut (finite_focus_pending F st)"])
          (simp_all add: finite_witnessed_diagnosis_def)
    qed
  next
    case (Suc n)
    let ?rec = "finite_committed_search_by sel \<kappa> K P n"
    let ?c = "finite_commits_nothing K sel"
    have J: "J st" and sup: "resolution_supported_at U F B P st \<theta>" by (rule Suc.prems)+
    obtain d0 \<pi>0 where Ip: "resolution_pattern_invariant P d0 \<pi>0 st" using pattern[OF J] by blast
    show ?case
    proof (cases "finite_focus_pending F st = {||}")
      case True
      then have "st |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P (Suc n) F B st)" by simp
      then show ?thesis by (rule finite_keeping_outcome_found[OF _ sup])
    next
      case False
      show ?thesis
      proof (cases "sel (finite_focused F st)")
        case (Select_Construction N)
        have unplain: "\<not> ?c" using Select_Construction unfolding finite_commits_nothing_def by blast
        let ?B' = "finite_committed_barring B st"
        let ?M = "ffilter (\<lambda>nd. resolution_focused F (resolution_node_position nd)) N"
        show ?thesis
        proof (cases "?M = {||}")
          case True
          have eq: "finite_committed_search_by sel \<kappa> K P (Suc n) F B st =
              Resolution_Outcome {||} {|Resolution_Stuck (finite_focus_pending F st)|}"
            using False Select_Construction True by (simp add: Let_def)
          show ?thesis unfolding eq
            by (rule finite_keeping_outcome_diagnosis[where D="Resolution_Stuck (finite_focus_pending F st)"])
              (simp_all add: finite_witnessed_diagnosis_def)
        next
          case nonempty: False
          then obtain nd where ndM: "nd |\<in>| ?M" by (metis all_not_fin_conv)
          then have nd: "nd |\<in>| N" and focus: "resolution_focused F (resolution_node_position nd)"
            by (auto simp: resolution_fset_simps)
          note step = constructions[unfolded finite_constructions_by_def, rule_format, OF J sup Select_Construction nd focus]
          obtain \<theta>' where J': "J (finite_construction_step \<kappa> P st nd)"
            and sup': "resolution_supported_at U F ?B' P (finite_construction_step \<kappa> P st nd) \<theta>'"
            using step by blast
          have kept: "finite_keeping_outcome U F ?B' P (finite_construction_step \<kappa> P st nd) \<theta>' ?c
              (?rec F ?B' (finite_construction_step \<kappa> P st nd))"
            by (rule Suc.IH[OF J' sup'])
          have mem: "?rec F ?B' (finite_construction_step \<kappa> P st nd) |\<in>|
              fimage (?rec F ?B') (fimage (finite_construction_step \<kappa> P st) ?M)"
            by (rule fimageI, rule fimageI[OF ndM])
          have eq: "finite_committed_search_by sel \<kappa> K P (Suc n) F B st =
              finite_outcome_union (fimage (?rec F ?B') (fimage (finite_construction_step \<kappa> P st) ?M))"
            using False Select_Construction nonempty by (simp add: Let_def)
          show ?thesis unfolding eq
            by (rule finite_keeping_outcome_union[OF mem finite_keeping_outcome_step[OF kept]]) (use unplain in blast)
        qed
      next
        case Select_None
        have eq: "finite_committed_search_by sel \<kappa> K P (Suc n) F B st = Resolution_Outcome {||}
            (finsert (Resolution_Stuck (finite_focus_pending F st)) (finite_unconstructed \<kappa> P st))"
          using False Select_None by simp
        show ?thesis unfolding eq
          by (rule finite_keeping_outcome_diagnosis[where D="Resolution_Stuck (finite_focus_pending F st)"])
            (simp_all add: finite_witnessed_diagnosis_def)
      next
        case (Select_Goals G)
        have focused_pending: "resolution_pending (finite_focused F st) = finite_focus_pending F st"
          by (simp add: finite_focused_def)
        obtain g where g: "g |\<in>| G" and gp: "g |\<in>| finite_focus_pending F st"
          and kind: "resolution_is_call g \<or> finite_solvable_material_goal g"
          using selection[OF Select_Goals] focused_pending by (metis all_not_fin_conv)
        have pending: "g |\<in>| resolution_pending st" and focus: "resolution_focused F (resolution_goal_position g)"
          using gp by (simp_all add: finite_focus_pending_focused)
        define Og where "Og = finite_committed_goal_outcome ?rec K P F B st g"
        have eq: "finite_committed_search_by sel \<kappa> K P (Suc n) F B st =
            finite_outcome_union (fimage (finite_committed_goal_outcome ?rec K P F B st) G)"
          using False Select_Goals by simp
        have memg: "Og |\<in>| fimage (finite_committed_goal_outcome ?rec K P F B st) G"
          unfolding Og_def by (rule fimageI[OF g])
        have unpruned: "\<not> finite_pruned (finite_unbarred B st) g"
          by (rule resolution_supported_at_unbarred[OF sup pending focus])
        note exg = exchanges[unfolded finite_exchanges_by_def, rule_format,
          where n=n and F=F and B=B and st=st and \<theta>=\<theta> and G=G and g=g, OF J sup Select_Goals g]
        have "finite_keeping_outcome U F B P st \<theta> ?c Og"
        proof (cases "finite_pruned (finite_barred B st) g")
          case True
          have "Og = Resolution_Outcome {||} {|Resolution_Cut {|g|}|}"
            unfolding Og_def finite_committed_goal_outcome_def using unpruned True by simp
          then show ?thesis
            by (simp only:) (rule finite_keeping_outcome_diagnosis[where D="Resolution_Cut {|g|}"],
              simp_all add: finite_witnessed_diagnosis_def)
        next
          case barred: False
          show ?thesis
          proof (cases "finite_goal_committing K F st g")
            case True
            have unplain: "\<not> ?c" using True unfolding finite_commits_nothing_def by blast
            let ?q = "resolution_goal_position g"
            let ?st0 = "finite_produced_state K F st g"
            let ?B1 = "finite_goal_sub_barring K F B st g"
            let ?sub = "?rec (Some ?q) ?B1 ?st0"
            have Og: "Og = finite_outcome_union (finsert (Resolution_Outcome {||} (resolution_diagnoses ?sub))
                (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                  (finite_kept ?q (resolution_found ?sub))))"
              unfolding Og_def finite_committed_goal_outcome_eq using unpruned barred True
              by (simp add: Let_def)
            note X = exg[THEN conjunct1, rule_format, OF True]
            have J0: "J ?st0" using X by blast
            obtain \<theta>q where supq: "resolution_supported_at U (Some ?q) ?B1 P ?st0 \<theta>q" using X by blast
            have "finite_keeping_outcome U (Some ?q) ?B1 P ?st0 \<theta>q ?c ?sub" by (rule Suc.IH[OF J0 supq])
            then consider (found) s0 B0 \<theta>0 where "s0 |\<in>| resolution_found ?sub"
                "resolution_supported_at U (Some ?q) B0 P s0 \<theta>0"
              | (diag) D where "D |\<in>| resolution_diagnoses ?sub" "\<not> finite_witnessed_diagnosis D"
              unfolding finite_keeping_outcome_def by blast
            then show ?thesis
            proof cases
              case diag
              have mem: "Resolution_Outcome {||} (resolution_diagnoses ?sub) |\<in>|
                  finsert (Resolution_Outcome {||} (resolution_diagnoses ?sub))
                    (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                      (finite_kept ?q (resolution_found ?sub)))" by simp
              have "finite_keeping_outcome U F B P st \<theta> ?c (Resolution_Outcome {||} (resolution_diagnoses ?sub))"
                by (rule finite_keeping_outcome_diagnosis[where D=D]) (simp_all add: diag)
              then show ?thesis unfolding Og by (rule finite_keeping_outcome_union[OF mem])
            next
              case found
              obtain s \<theta>' where s: "s |\<in>| finite_kept ?q (resolution_found ?sub)" and Js: "J s"
                and sups: "resolution_supported_at U F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
                using X found by blast
              have sups': "resolution_supported_at U F (finite_committed_barring B s) P s \<theta>'"
                by (rule resolution_supported_at_barred_mono[OF sups]) (auto simp: finite_committed_barring_def)
              have kept: "finite_keeping_outcome U F (finite_committed_barring B s) P s \<theta>' ?c
                  (?rec F (finite_committed_barring B s) s)"
                by (rule Suc.IH[OF Js sups'])
              have mem: "?rec F (finite_committed_barring B s) s |\<in>|
                  finsert (Resolution_Outcome {||} (resolution_diagnoses ?sub))
                    (fimage (\<lambda>s. ?rec F (finite_committed_barring B s) s)
                      (finite_kept ?q (resolution_found ?sub)))"
                by (rule finsertI2, rule fimageI[OF s])
              show ?thesis unfolding Og
                by (rule finite_keeping_outcome_union[OF mem finite_keeping_outcome_step[OF kept]]) (use unplain in blast)
            qed
          next
            case uncommitted: False
            obtain st' \<theta>' where st': "st' |\<in>| finite_committed_successors K P F st g"
              and sup': "resolution_supported_at U F (finite_goal_barring K F B st g) P st' \<theta>'"
              and keep: "?c \<Longrightarrow> finite_goal_barring K F B st g = B \<and>
                (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value st' \<theta>' v)"
            proof (cases "\<exists>q r M Ws. g = Resolution_Material_Goal q r M \<and> finite_canonical_solutions M = Some Ws \<and>
                commit_material K F st g")
              case True
              then obtain q r M Ws where gm: "g = Resolution_Material_Goal q r M"
                and Ws: "finite_canonical_solutions M = Some Ws" and cm: "commit_material K F st g" by blast
              have unplain: "\<not> ?c" using cm unfolding finite_commits_nothing_def by blast
              obtain st' \<theta>' where s: "st' |\<in>| finite_solution_successors st q r M Ws"
                and u: "resolution_supported_at U F (finite_committed_barring B st) P st' \<theta>'"
                using exg[THEN conjunct2, rule_format, OF gm Ws cm] by blast
              have eqS: "finite_committed_successors K P F st g = finite_solution_successors st q r M Ws"
                using gm Ws cm by (simp add: finite_committed_successors_def)
              have eqB: "finite_goal_barring K F B st g = finite_committed_barring B st"
                using gm Ws cm by (simp add: finite_goal_barring_def finite_material_committed_def)
              show thesis by (rule that[of st' \<theta>']) (use s u eqS eqB unplain in auto)
            next
              case False
              have eqB: "finite_goal_barring K F B st g = B"
                using False by (auto simp: finite_goal_barring_def finite_material_committed_def split: resolution_goal.splits)
              show thesis
              proof (cases "\<exists>q r e p. g = Resolution_Call_Goal q r e p \<and> F = Some q")
                case True
                then obtain q r e p where gc: "g = Resolution_Call_Goal q r e p" and Fq: "F = Some q" by blast
                have eqS: "finite_committed_successors K P F st g = finite_call_successors P st q r e p"
                  using gc Fq by (simp add: finite_committed_successors_def)
                have goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st" using pending gc by simp
                have fq: "resolution_focused F q" using focus gc by simp
                show thesis
                proof (rule resolution_call_lifted_at[OF Ip sup foreign goal fq])
                  fix st' \<theta>' assume s: "st' |\<in>| finite_call_successors P st q r e p"
                    and u: "resolution_supported_at U F B P st' \<theta>'"
                    and rv: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
                  show thesis by (rule that[of st' \<theta>']) (use s u rv eqS eqB in auto)
                qed
              next
                case unfocused: False
                have eqS: "finite_committed_successors K P F st g = finite_goal_successors P st g"
                  using False unfocused
                  by (auto simp: finite_committed_successors_def split: resolution_goal.splits option.splits)
                show thesis
                proof (rule resolution_goal_lifted_at[OF Ip sup foreign pending focus kind])
                  fix st' \<theta>' assume s: "st' |\<in>| finite_goal_successors P st g"
                    and u: "resolution_supported_at U F B P st' \<theta>'"
                    and rv: "\<And>v. resolution_root_value st \<theta> v \<Longrightarrow> resolution_root_value st' \<theta>' v"
                  show thesis by (rule that[of st' \<theta>']) (use s u rv eqS eqB in auto)
                qed
              qed
            qed
            have J': "J st'" by (rule successors[OF J Select_Goals g st'])
            have kept: "finite_keeping_outcome U F (finite_goal_barring K F B st g) P st' \<theta>' ?c
                (?rec F (finite_goal_barring K F B st g) st')"
              by (rule Suc.IH[OF J' sup'])
            have ne: "finite_committed_successors K P F st g \<noteq> {||}" using st' by auto
            have Og: "Og = finite_search_join F st (finite_determinate_key (resolution_goal_position g))
                (?rec F (finite_goal_barring K F B st g)) (finite_committed_successors K P F st g)"
              unfolding Og_def finite_committed_goal_outcome_eq using unpruned barred uncommitted ne
              by (simp add: Let_def)
            have kept': "finite_keeping_outcome U F B P st \<theta> ?c (?rec F (finite_goal_barring K F B st g) st')"
              by (rule finite_keeping_outcome_step[OF kept keep])
            show ?thesis unfolding Og
            proof (rule finite_search_join_lifted[where f="?rec F (finite_goal_barring K F B st g)", OF st' kept'])
              fix s
              assume s: "s |\<in>| resolution_found (finite_search_join F st (finite_determinate_key (resolution_goal_position g))
                  (?rec F (finite_goal_barring K F B st g)) (finite_committed_successors K P F st g))"
                and ground: "finite_focus_ground F st"
              obtain q where Fq: "F = Some q" using ground by (cases F) simp_all
              have sO: "s |\<in>| resolution_found Og" using s Og by simp
              have "s |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P (Suc n) F B st)"
                unfolding eq by (rule fsubsetD[OF finite_outcome_union_part(1)[OF memg] sO])
              then have sF: "s |\<in>| resolution_found (finite_committed_search_by sel \<kappa> K P (Suc n) (Some q) B st)"
                by (simp only: Fq)
              have "\<exists>B' \<theta>'. resolution_supported_at U (Some q) B' P s \<theta>' \<and>
                  (?c \<longrightarrow> B' = B \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value s \<theta>' v))"
                by (rule grounds[unfolded finite_ground_founds_by_def, rule_format,
                  OF J sup[unfolded Fq] ground[unfolded Fq] sF])
              then show "\<exists>B' \<theta>'. resolution_supported_at U F B' P s \<theta>' \<and>
                  (?c \<longrightarrow> B' = B \<and> (\<forall>v. resolution_root_value st \<theta> v \<longrightarrow> resolution_root_value s \<theta>' v))"
                using Fq by simp
            qed
          qed
        qed
        then show ?thesis unfolding eq by (rule finite_keeping_outcome_union[OF memg])
      qed
    qed
  qed
qed

end
