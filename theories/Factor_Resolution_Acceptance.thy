theory Factor_Resolution_Acceptance
  imports Factor_Program_Resolution
begin

section \<open>Patterns under substitution and residual instantiation\<close>

lemma finite_pattern_substitute_formed:
  assumes "finite_pattern_formed p" and "\<And>x. finite_pattern_formed (\<sigma> x)"
  shows "finite_pattern_formed (finite_pattern_substitute \<sigma> p)"
  using assms by (induction p) simp_all

lemma finite_pattern_substitute_formed_variable:
  "finite_pattern_formed (finite_pattern_substitute \<sigma> p) \<Longrightarrow> x |\<in>| finite_pattern_variables p \<Longrightarrow>
    finite_pattern_formed (\<sigma> x)"
  by (induction p) auto

lemma finite_pattern_substitute_ground_variable:
  "finite_pattern_variables (finite_pattern_substitute \<sigma> p) = {||} \<Longrightarrow> x |\<in>| finite_pattern_variables p \<Longrightarrow>
    finite_pattern_variables (\<sigma> x) = {||}"
  by (induction p) (auto simp: sup_eq_bot_iff)

lemma finite_pattern_substitute_ground:
  "finite_pattern_variables p = {||} \<Longrightarrow> finite_pattern_substitute \<sigma> p = p"
  by (induction p) (auto simp: sup_eq_bot_iff)

lemma finite_rename_pattern_formed [simp]:
  "finite_pattern_formed (map_finite_term_pattern f p) = finite_pattern_formed p"
  by (induction p) simp_all

lemma finite_exact_pattern_formed [simp]:
  "finite_pattern_formed (finite_exact_term_pattern t) = finite_term_formed t"
  by (induction t) simp_all

lemma finite_residual_term_formed [simp]:
  "finite_term_formed (finite_residual_term p) = finite_pattern_formed p"
  by (induction p) (simp_all add: octets_formed_def)

lemma finite_residual_exact [simp]: "finite_residual_term (finite_exact_term_pattern t) = t"
  by (induction t) simp_all

lemma finite_exact_residual_substitute:
  "finite_exact_term_pattern (finite_residual_term (finite_pattern_substitute \<sigma> p)) =
    finite_pattern_substitute (\<lambda>x. finite_exact_term_pattern (finite_residual_term (\<sigma> x))) p"
  by (induction p) simp_all

lemma finite_rename_as_substitute:
  "map_finite_term_pattern f p = finite_pattern_substitute (\<lambda>a. Finite_Variable (f a)) p"
  by (induction p) simp_all

lemma finite_binding_substitution_formed:
  assumes "\<forall>y\<in>set s. finite_pattern_formed (snd y)"
  shows "finite_pattern_formed (finite_binding_substitution s a)"
  using assms by (auto simp: finite_binding_substitution_def split: option.split dest!: map_of_SomeD)

lemma finite_unify_pairs_formed:
  assumes "finite_unify_pairs E = Some s"
    and "\<forall>x\<in>set E. finite_pattern_formed (fst x) \<and> finite_pattern_formed (snd x)"
  shows "\<forall>y\<in>set s. finite_pattern_formed (snd y)"
  using assms
proof (induction E arbitrary: s rule: finite_unify_pairs.induct)
  case (2 a q E s)
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1) "2.prems" show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False "2.prems" show ?thesis by simp
    next
      case fresh: False
      from "2.prems"(1) False fresh obtain s' where
        rec: "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = Some s'" and
        s: "s = (a, finite_pattern_substitute (finite_binding_substitution s') q) # s'"
        by auto
      have qf: "finite_pattern_formed q" using "2.prems"(2) by simp
      have ef: "\<And>x. finite_pattern_formed (finite_eliminator a q x)" using qf by simp
      have "\<forall>x\<in>set (finite_pairs_substitute (finite_eliminator a q) E).
          finite_pattern_formed (fst x) \<and> finite_pattern_formed (snd x)"
        using "2.prems"(2) by (auto simp: finite_pairs_substitute_def intro: finite_pattern_substitute_formed[OF _ ef])
      then have sf: "\<forall>y\<in>set s'. finite_pattern_formed (snd y)" by (rule "2.IH"(2)[OF False fresh rec])
      have "finite_pattern_formed (finite_pattern_substitute (finite_binding_substitution s') q)"
        by (rule finite_pattern_substitute_formed[OF qf finite_binding_substitution_formed[OF sf]])
      then show ?thesis using sf by (simp add: s)
    qed
  qed
qed (auto split: if_splits)

lemma finite_unifier_formed:
  assumes "finite_unify_pairs E = Some s"
    and "\<forall>x\<in>set E. finite_pattern_formed (fst x) \<and> finite_pattern_formed (snd x)"
  shows "finite_pattern_formed (finite_binding_substitution s a)"
  by (rule finite_binding_substitution_formed[OF finite_unify_pairs_formed[OF assms]])

lemma finite_ground_instance_residual:
  assumes "finite_pattern_formed p" and "finite_pattern_variables p |\<subseteq>| X"
  shows "finite_pattern_instance (finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) X) p
    (finite_residual_term (finite_pattern_substitute \<beta> p))"
proof -
  have sub: "fset (finite_pattern_variables p) \<subseteq> fset X" using assms(2) by (simp add: less_eq_fset.rep_eq)
  show ?thesis
  proof (rule iffD2[OF finite_ground_substitution_instance[OF sub]])
    show "finite_pattern_formed p \<and> finite_exact_term_pattern (finite_residual_term (finite_pattern_substitute \<beta> p)) =
        finite_pattern_substitute (finite_exact_term_pattern \<circ> (\<lambda>a. finite_residual_term (\<beta> a))) p"
      by (simp add: assms(1) finite_exact_residual_substitute comp_def)
  qed
qed

lemma finite_pattern_accepts_intro:
  assumes "finite_term_formed t" and "finite_term_bindings_formed (finite_pattern_variables p) V"
    and "finite_pattern_instance V p t"
  shows "finite_pattern_accepts p t"
proof -
  have f: "term_formed (decode_finite_term t)" using assms(1) by (simp add: finite_term_formed_correct)
  have b: "term_bindings_formed (pattern_variables (decode_finite_pattern p)) (decode_finite_term_bindings V)"
    using assms(2) by (simp add: finite_term_bindings_formed_correct finite_pattern_variables_correct)
  have i: "pattern_instance (decode_finite_term_bindings V) (decode_finite_pattern p) (decode_finite_term t)"
    using assms(3) by (simp add: finite_pattern_instance_correct)
  have "pattern_accepts (decode_finite_pattern p) (decode_finite_term t)"
    using f b i unfolding pattern_accepts_def by blast
  then show ?thesis by (simp add: finite_pattern_accepts_correct)
qed

lemma finite_pattern_accepts_substitute:
  assumes formed: "finite_pattern_formed p" and call: "finite_pattern_formed (finite_pattern_substitute \<iota> p)"
  shows "finite_pattern_accepts p (finite_residual_term (finite_pattern_substitute \<iota> p))"
proof (rule finite_pattern_accepts_intro)
  show "finite_term_formed (finite_residual_term (finite_pattern_substitute \<iota> p))" using call by simp
  show "finite_term_bindings_formed (finite_pattern_variables p)
      (finite_ground_bindings (\<lambda>a. finite_residual_term (\<iota> a)) (finite_pattern_variables p))"
    by (rule finite_ground_bindings_formed)
      (simp add: finite_pattern_substitute_formed_variable[OF call])
  show "finite_pattern_instance (finite_ground_bindings (\<lambda>a. finite_residual_term (\<iota> a)) (finite_pattern_variables p)) p
      (finite_residual_term (finite_pattern_substitute \<iota> p))"
    by (rule finite_ground_instance_residual[OF formed]) simp
qed

section \<open>Material patterns under substitution\<close>

lemma finite_material_pattern_substitute_fields [simp]:
  "finite_material_source (finite_material_pattern_substitute \<sigma> M) = finite_pattern_substitute \<sigma> (finite_material_source M)"
  "finite_material_atoms (finite_material_pattern_substitute \<sigma> M) = finite_pattern_substitute \<sigma> (finite_material_atoms M)"
  "finite_material_edges (finite_material_pattern_substitute \<sigma> M) = finite_pattern_substitute \<sigma> (finite_material_edges M)"
  "finite_material_counts (finite_material_pattern_substitute \<sigma> M) = finite_pattern_substitute \<sigma> (finite_material_counts M)"
  "finite_material_functions (finite_material_pattern_substitute \<sigma> M) =
    finite_pattern_substitute \<sigma> (finite_material_functions M)"
  by (simp_all add: finite_material_pattern_substitute_def)

lemma finite_material_pattern_substitute_composes:
  "finite_material_pattern_substitute \<tau> (finite_material_pattern_substitute \<sigma> M) =
    finite_material_pattern_substitute (\<lambda>a. finite_pattern_substitute \<tau> (\<sigma> a)) M"
  by (simp add: finite_material_pattern_substitute_def finite_pattern_substitute_composes)

lemma finite_rename_material_as_substitute:
  "finite_rename_material f M = finite_material_pattern_substitute (\<lambda>a. Finite_Variable (f a)) M"
  by (simp add: finite_rename_material_def finite_material_pattern_substitute_def finite_rename_as_substitute)

lemma finite_material_pattern_substitute_formed:
  assumes "finite_material_formed M" and "\<And>x. finite_pattern_formed (\<sigma> x)"
  shows "finite_material_formed (finite_material_pattern_substitute \<sigma> M)"
  using assms by (simp add: finite_material_formed_def finite_pattern_substitute_formed)

text \<open>
  A material premise is done at an instance of its clause's variables when every variable of it is
  ground and the ground values satisfy it; a later substitution leaves such an instance unchanged. A
  material goal whose fields are the exact patterns of satisfying operands gives a done instance.
\<close>

definition resolution_material_done :: "('a \<Rightarrow> 'v finite_term_pattern) \<Rightarrow> 'a finite_material_pattern \<Rightarrow> bool" where
  "resolution_material_done \<beta> M \<longleftrightarrow>
    (\<forall>a. a |\<in>| finite_material_variables M \<longrightarrow> finite_pattern_variables (\<beta> a) = {||}) \<and>
    finite_material_satisfied (finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) (finite_material_variables M)) M"

definition finite_material_ground_satisfied :: "'v finite_material_pattern \<Rightarrow> bool" where
  "finite_material_ground_satisfied M \<longleftrightarrow> (\<exists>s a e b f.
    finite_material_source M = finite_exact_term_pattern s \<and> finite_material_atoms M = finite_exact_term_pattern a \<and>
    finite_material_edges M = finite_exact_term_pattern e \<and> finite_material_counts M = finite_exact_term_pattern b \<and>
    finite_material_functions M = finite_exact_term_pattern f \<and> finite_material_observation s a e b f)"

lemma resolution_material_done_substitute:
  fixes \<beta> :: "'a \<Rightarrow> 'v finite_term_pattern" and \<sigma> :: "'v \<Rightarrow> 'v finite_term_pattern"
  assumes "resolution_material_done \<beta> M"
  shows "resolution_material_done (\<lambda>a. finite_pattern_substitute \<sigma> (\<beta> a)) M"
proof -
  have same: "\<And>a. a |\<in>| finite_material_variables M \<Longrightarrow> finite_pattern_substitute \<sigma> (\<beta> a) = \<beta> a"
    using assms by (simp add: resolution_material_done_def finite_pattern_substitute_ground)
  have "finite_ground_bindings (\<lambda>a. finite_residual_term (finite_pattern_substitute \<sigma> (\<beta> a))) (finite_material_variables M) =
      finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) (finite_material_variables M)"
    using same by (auto simp: fset_eq_iff)
  then show ?thesis using assms same by (simp add: resolution_material_done_def)
qed

lemma resolution_material_done_ground:
  assumes formed: "finite_material_formed M"
    and ground: "finite_material_ground_satisfied (finite_material_pattern_substitute \<beta> M)"
  shows "resolution_material_done \<beta> M"
proof -
  obtain s a e b f where fields: "finite_pattern_substitute \<beta> (finite_material_source M) = finite_exact_term_pattern s"
      "finite_pattern_substitute \<beta> (finite_material_atoms M) = finite_exact_term_pattern a"
      "finite_pattern_substitute \<beta> (finite_material_edges M) = finite_exact_term_pattern e"
      "finite_pattern_substitute \<beta> (finite_material_counts M) = finite_exact_term_pattern b"
      "finite_pattern_substitute \<beta> (finite_material_functions M) = finite_exact_term_pattern f"
    and obs: "finite_material_observation s a e b f"
    using ground by (auto simp: finite_material_ground_satisfied_def)
  let ?V = "finite_ground_bindings (\<lambda>x. finite_residual_term (\<beta> x)) (finite_material_variables M)"
  have inst: "\<And>p t. finite_pattern_formed p \<Longrightarrow> finite_pattern_variables p |\<subseteq>| finite_material_variables M \<Longrightarrow>
      finite_pattern_substitute \<beta> p = finite_exact_term_pattern t \<Longrightarrow> t |\<in>| finite_pattern_instances ?V p"
    by (metis finite_pattern_instances_member finite_ground_instance_residual finite_residual_exact)
  have fm: "finite_pattern_formed (finite_material_source M)" "finite_pattern_formed (finite_material_atoms M)"
      "finite_pattern_formed (finite_material_edges M)" "finite_pattern_formed (finite_material_counts M)"
      "finite_pattern_formed (finite_material_functions M)"
    using formed by (simp_all add: finite_material_formed_def)
  have vm: "finite_pattern_variables (finite_material_source M) |\<subseteq>| finite_material_variables M"
      "finite_pattern_variables (finite_material_atoms M) |\<subseteq>| finite_material_variables M"
      "finite_pattern_variables (finite_material_edges M) |\<subseteq>| finite_material_variables M"
      "finite_pattern_variables (finite_material_counts M) |\<subseteq>| finite_material_variables M"
      "finite_pattern_variables (finite_material_functions M) |\<subseteq>| finite_material_variables M"
    by (auto simp: finite_material_variables_def)
  have sat: "finite_material_satisfied ?V M"
    unfolding finite_material_satisfied_def
    using inst[OF fm(1) vm(1) fields(1)] inst[OF fm(2) vm(2) fields(2)] inst[OF fm(3) vm(3) fields(3)]
      inst[OF fm(4) vm(4) fields(4)] inst[OF fm(5) vm(5) fields(5)] obs
    by blast
  have gv: "finite_pattern_variables (\<beta> x) = {||}"
    if "finite_pattern_substitute \<beta> F = finite_exact_term_pattern u" "x |\<in>| finite_pattern_variables F" for F u x
    using finite_pattern_substitute_ground_variable[of \<beta> F x] that by simp
  have "\<And>x. x |\<in>| finite_material_variables M \<Longrightarrow> finite_pattern_variables (\<beta> x) = {||}"
    using gv[OF fields(1)] gv[OF fields(2)] gv[OF fields(3)] gv[OF fields(4)] gv[OF fields(5)]
    by (auto simp: finite_material_variables_def)
  then show ?thesis using sat by (simp add: resolution_material_done_def)
qed

lemma finite_material_instance_pairs_member:
  "E |\<in>| finite_material_instance_pairs W M \<Longrightarrow> \<exists>s a e b f.
    finite_pattern_instance W (finite_material_source M) s \<and> finite_pattern_instance W (finite_material_atoms M) a \<and>
    finite_pattern_instance W (finite_material_edges M) e \<and> finite_pattern_instance W (finite_material_counts M) b \<and>
    finite_pattern_instance W (finite_material_functions M) f \<and>
    E = [(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)]"
  by (auto simp: finite_material_instance_pairs_def ffUnion.rep_eq fimage.rep_eq finite_pattern_instances_member)

lemma finite_material_step_ground:
  assumes solution: "finite_material_solution M W" and pairs: "E |\<in>| finite_material_instance_pairs W M"
    and unified: "finite_unify_pairs E = Some u"
  shows "finite_material_ground_satisfied (finite_material_pattern_substitute (finite_binding_substitution u) M)"
proof -
  obtain s a e b f where i: "finite_pattern_instance W (finite_material_source M) s"
      "finite_pattern_instance W (finite_material_atoms M) a" "finite_pattern_instance W (finite_material_edges M) e"
      "finite_pattern_instance W (finite_material_counts M) b" "finite_pattern_instance W (finite_material_functions M) f"
    and E: "E = [(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
      (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
      (finite_material_functions M,finite_exact_term_pattern f)]"
    using finite_material_instance_pairs_member[OF pairs] by blast
  have functional: "finite_relation_functional W" and sat: "finite_material_satisfied W M"
    using solution by (simp_all add: finite_material_solution_def finite_term_bindings_formed_def)
  obtain s' a' e' b' f' where i': "finite_pattern_instance W (finite_material_source M) s'"
      "finite_pattern_instance W (finite_material_atoms M) a'" "finite_pattern_instance W (finite_material_edges M) e'"
      "finite_pattern_instance W (finite_material_counts M) b'" "finite_pattern_instance W (finite_material_functions M) f'"
    and obs: "finite_material_observation s' a' e' b' f'"
    using sat by (auto simp: finite_material_satisfied_def finite_pattern_instances_member)
  have same: "s=s'" "a=a'" "e=e'" "b=b'" "f=f'"
    using finite_pattern_instance_unique[OF functional] i i' by blast+
  have "finite_unifies (finite_binding_substitution u) E" by (rule finite_unify_pairs_sound[OF unified])
  then show ?thesis using obs same
    by (auto simp: E finite_material_ground_satisfied_def finite_pattern_substitute_ground)
qed

lemma finite_pattern_instance_term_formed:
  "fBall V (\<lambda>(a,t). finite_term_formed t) \<Longrightarrow> finite_pattern_instance V p t \<Longrightarrow> finite_term_formed t"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemmas resolution_fset_simps = fimage.rep_eq ffUnion.rep_eq ffilter.rep_eq sup_fset.rep_eq minus_fset.rep_eq
  finsert.rep_eq

section \<open>The invariant of a branch\<close>

text \<open>
  The invariant of a branch from the call of a site d at a term t, at a formed program and a formed
  term: every node is linked to its clause and interface, its bindings are the instance of the clause's
  variables its call and each premise read, and each premise is either a pending goal at its socket's
  position or a node there, each material premise either a pending goal or done; positions identify
  nodes and goals, a pending call goal stands where no node does, and every position but the root's has
  its parent node. Every pattern in a state is formed.
\<close>

definition resolution_root_goal :: "'d \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_goal" where
  "resolution_root_goal d t = Resolution_Call_Goal [] None d (finite_exact_term_pattern t)"

fun resolution_goal_formed :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "resolution_goal_formed (Resolution_Call_Goal q r d p) = finite_pattern_formed p"
| "resolution_goal_formed (Resolution_Material_Goal q r M) = finite_material_formed M"

fun resolution_is_call :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "resolution_is_call (Resolution_Call_Goal q r d p) = True"
| "resolution_is_call (Resolution_Material_Goal q r M) = False"

definition resolution_node_linked ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "resolution_node_linked P st nd \<longleftrightarrow>
    (\<exists>i \<iota>. (resolution_node_site nd,i) |\<in>| finite_system_interfaces P \<and>
      resolution_node_call nd = finite_pattern_substitute \<iota> i) \<and>
    ((resolution_node_site nd,resolution_node_clause nd),resolution_node_schema nd) |\<in>| finite_system_clauses P \<and>
    (\<exists>\<beta>. resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema nd)) \<and>
      resolution_node_call nd = finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema nd)) \<and>
      (\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd) \<longrightarrow>
        Resolution_Call_Goal (resolution_node_position nd@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e
            (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending st \<or>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=resolution_node_position nd@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta> p)) \<and>
      (\<forall>s M. (s,M) |\<in>| finite_schema_materials (resolution_node_schema nd) \<longrightarrow>
        Resolution_Material_Goal (resolution_node_position nd@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
            (finite_material_pattern_substitute \<beta> M) |\<in>| resolution_pending st \<or>
        resolution_material_done \<beta> M))"

definition resolution_root_held :: "'d \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_root_held d t st \<longleftrightarrow> resolution_root_goal d t |\<in>| resolution_pending st \<or>
    (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[])"

definition resolution_goals_placed :: "'d \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_goals_placed d t st \<longleftrightarrow> (\<forall>g. g |\<in>| resolution_pending st \<longrightarrow> resolution_goal_formed g \<and>
    (resolution_goal_position g=[] \<longrightarrow> g=resolution_root_goal d t) \<and>
    (resolution_goal_position g\<noteq>[] \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_goal_position g))))"

definition resolution_nodes_placed ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_nodes_placed P d t st \<longleftrightarrow> (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow>
    finite_pattern_formed (resolution_node_call nd) \<and>
    (\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd \<longrightarrow> finite_pattern_formed x) \<and>
    resolution_node_linked P st nd \<and>
    (resolution_node_position nd=[] \<longrightarrow> resolution_node_site nd=d \<and> resolution_node_call nd=finite_exact_term_pattern t) \<and>
    (resolution_node_position nd\<noteq>[] \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_node_position nd))))"

definition resolution_positions_distinct :: "('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_positions_distinct st \<longleftrightarrow>
    (\<forall>nd m. nd |\<in>| resolution_nodes st \<longrightarrow> m |\<in>| resolution_nodes st \<longrightarrow>
      resolution_node_position nd=resolution_node_position m \<longrightarrow> nd=m) \<and>
    (\<forall>g h. g |\<in>| resolution_pending st \<longrightarrow> h |\<in>| resolution_pending st \<longrightarrow>
      resolution_goal_position g=resolution_goal_position h \<longrightarrow> g=h) \<and>
    (\<forall>g nd. g |\<in>| resolution_pending st \<longrightarrow> nd |\<in>| resolution_nodes st \<longrightarrow> resolution_is_call g \<longrightarrow>
      resolution_goal_position g\<noteq>resolution_node_position nd)"

definition resolution_invariant ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_invariant P d t st \<longleftrightarrow> finite_system_formed P \<and> finite_term_formed t \<and>
    resolution_root_held d t st \<and> resolution_goals_placed d t st \<and> resolution_nodes_placed P d t st \<and>
    resolution_positions_distinct st"

lemma resolution_node_substitute_fields [simp]:
  "resolution_node_position (resolution_node_substitute \<sigma> nd) = resolution_node_position nd"
  "resolution_node_site (resolution_node_substitute \<sigma> nd) = resolution_node_site nd"
  "resolution_node_clause (resolution_node_substitute \<sigma> nd) = resolution_node_clause nd"
  "resolution_node_schema (resolution_node_substitute \<sigma> nd) = resolution_node_schema nd"
  "resolution_node_call (resolution_node_substitute \<sigma> nd) = finite_pattern_substitute \<sigma> (resolution_node_call nd)"
  "resolution_node_bindings (resolution_node_substitute \<sigma> nd) =
    fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (resolution_node_bindings nd)"
  by (cases nd; simp)+

lemma resolution_goal_substitute_fields [simp]:
  "resolution_goal_position (resolution_goal_substitute \<sigma> g) = resolution_goal_position g"
  "resolution_is_call (resolution_goal_substitute \<sigma> g) = resolution_is_call g"
  by (cases g; simp)+

lemma resolution_goal_substitute_formed:
  "resolution_goal_formed g \<Longrightarrow> (\<And>x. finite_pattern_formed (\<sigma> x)) \<Longrightarrow>
    resolution_goal_formed (resolution_goal_substitute \<sigma> g)"
  by (cases g) (simp_all add: finite_pattern_substitute_formed finite_material_pattern_substitute_formed)

lemma resolution_state_substitute_fields [simp]:
  "resolution_pending (resolution_state_substitute \<sigma> st) = fimage (resolution_goal_substitute \<sigma>) (resolution_pending st)"
  "resolution_nodes (resolution_state_substitute \<sigma> st) = fimage (resolution_node_substitute \<sigma>) (resolution_nodes st)"
  by (simp_all add: resolution_state_substitute_def)

lemma resolution_invariant_state_fields:
  "resolution_invariant P d t (Resolution_State (resolution_pending st) (resolution_nodes st) W) =
    resolution_invariant P d t st"
  by (simp add: resolution_invariant_def resolution_root_held_def resolution_goals_placed_def
    resolution_nodes_placed_def resolution_positions_distinct_def resolution_node_linked_def)

lemma resolution_root_goal_substitute [simp]:
  "resolution_goal_substitute \<sigma> (resolution_root_goal d t) = resolution_root_goal d t"
  by (simp add: resolution_root_goal_def finite_pattern_substitute_ground)

lemma resolution_initial_invariant:
  assumes "finite_system_formed P" and "finite_term_formed t"
  shows "resolution_invariant P d t (finite_initial_state d t)"
  using assms by (simp add: resolution_invariant_def resolution_root_held_def resolution_goals_placed_def
    resolution_nodes_placed_def resolution_positions_distinct_def finite_initial_state_def resolution_root_goal_def)

section \<open>The invariant of a branch from a pattern goal\<close>

text \<open>
  A search may start at a pattern goal of a site d, a call pattern whose variables its answers bind
  (@{text finite_pattern_state}). The invariant of its branches is the ground invariant with the root read as an
  instance of the pattern: the root goal, while it is pending, and the root node are instances of it under the
  substitution the branch has applied. Every other condition is the ground invariant's, and the ground invariant is
  its instance at the exact pattern of a term (@{text resolution_invariant_pattern}). Every step keeps it, and every
  node certificate of a closed branch is accepted, below; the ground statements are their instances.
\<close>

definition finite_pattern_state ::
    "'d \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_pattern_state d \<pi> = Resolution_State {|Resolution_Call_Goal [] None d \<pi>|} {||} {||}"

definition resolution_pattern_root_held ::
    "'d \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_pattern_root_held d \<pi> st \<longleftrightarrow>
    (\<exists>\<rho>. Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>) |\<in>| resolution_pending st) \<or>
    (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[])"

definition resolution_pattern_goals_placed ::
    "'d \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_pattern_goals_placed d \<pi> st \<longleftrightarrow> (\<forall>g. g |\<in>| resolution_pending st \<longrightarrow> resolution_goal_formed g \<and>
    (resolution_goal_position g=[] \<longrightarrow> (\<exists>\<rho>. g=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>))) \<and>
    (resolution_goal_position g\<noteq>[] \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_goal_position g))))"

definition resolution_pattern_nodes_placed ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_pattern_nodes_placed P d \<pi> st \<longleftrightarrow> (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow>
    finite_pattern_formed (resolution_node_call nd) \<and>
    (\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd \<longrightarrow> finite_pattern_formed x) \<and>
    resolution_node_linked P st nd \<and>
    (resolution_node_position nd=[] \<longrightarrow> resolution_node_site nd=d \<and>
      (\<exists>\<rho>. resolution_node_call nd=finite_pattern_substitute \<rho> \<pi>)) \<and>
    (resolution_node_position nd\<noteq>[] \<longrightarrow>
      (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_node_position nd))))"

definition resolution_pattern_invariant ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "resolution_pattern_invariant P d \<pi> st \<longleftrightarrow> finite_system_formed P \<and> finite_pattern_formed \<pi> \<and>
    resolution_pattern_root_held d \<pi> st \<and> resolution_pattern_goals_placed d \<pi> st \<and>
    resolution_pattern_nodes_placed P d \<pi> st \<and> resolution_positions_distinct st"

lemma finite_exact_term_pattern_substitute:
  "finite_pattern_substitute \<rho> (finite_exact_term_pattern t) = finite_exact_term_pattern t"
  by (induction t) simp_all

lemma finite_initial_pattern_state:
  "finite_initial_state d t = finite_pattern_state d (finite_exact_term_pattern t)"
  by (simp add: finite_initial_state_def finite_pattern_state_def)

lemma resolution_invariant_pattern:
  "resolution_invariant P d t st \<longleftrightarrow> resolution_pattern_invariant P d (finite_exact_term_pattern t) st"
  by (simp add: resolution_invariant_def resolution_pattern_invariant_def resolution_root_held_def
    resolution_pattern_root_held_def resolution_goals_placed_def resolution_pattern_goals_placed_def
    resolution_nodes_placed_def resolution_pattern_nodes_placed_def resolution_root_goal_def
    finite_exact_term_pattern_substitute)

lemma resolution_pattern_invariant_state_fields:
  "resolution_pattern_invariant P d \<pi> (Resolution_State (resolution_pending st) (resolution_nodes st) W) =
    resolution_pattern_invariant P d \<pi> st"
  by (simp add: resolution_pattern_invariant_def resolution_pattern_root_held_def resolution_pattern_goals_placed_def
    resolution_pattern_nodes_placed_def resolution_positions_distinct_def resolution_node_linked_def)

lemma resolution_pattern_initial_invariant:
  assumes "finite_system_formed P" and "finite_pattern_formed \<pi>"
  shows "resolution_pattern_invariant P d \<pi> (finite_pattern_state d \<pi>)"
  using assms by (auto simp: resolution_pattern_invariant_def resolution_pattern_root_held_def
    resolution_pattern_goals_placed_def resolution_pattern_nodes_placed_def resolution_positions_distinct_def
    finite_pattern_state_def intro: exI[where x=Finite_Variable])

section \<open>Every step keeps the invariant\<close>

lemma resolution_linked_substitute:
  assumes linked: "resolution_node_linked P st nd"
  shows "resolution_node_linked P (resolution_state_substitute \<sigma> st) (resolution_node_substitute \<sigma> nd)"
proof -
  let ?S = "resolution_node_schema nd" and ?q = "resolution_node_position nd"
    and ?d = "resolution_node_site nd" and ?c = "resolution_node_clause nd"
  obtain i \<iota> where interface: "(?d,i) |\<in>| finite_system_interfaces P"
      and iface: "resolution_node_call nd = finite_pattern_substitute \<iota> i"
    using linked unfolding resolution_node_linked_def by blast
  have clause: "((?d,?c),?S) |\<in>| finite_system_clauses P"
    using linked unfolding resolution_node_linked_def by blast
  obtain \<beta> where B: "resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables ?S)"
      and head: "resolution_node_call nd = finite_pattern_substitute \<beta> (finite_schema_conclusion ?S)"
      and prem: "\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow>
        Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending st \<or>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=?q@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta> p)"
      and mat: "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
        Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta> M) |\<in>| resolution_pending st \<or>
        resolution_material_done \<beta> M"
    using linked unfolding resolution_node_linked_def by blast
  define \<beta>' where "\<beta>' = (\<lambda>a. finite_pattern_substitute \<sigma> (\<beta> a))"
  have prem': "\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow>
      Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta>' p) |\<in>|
        resolution_pending (resolution_state_substitute \<sigma> st) \<or>
      (\<exists>m. m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st) \<and> resolution_node_position m=?q@[s] \<and>
        resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta>' p)"
  proof (intro allI impI)
    fix s e p assume sp: "(s,e,p) |\<in>| finite_schema_premises ?S"
    have eq: "finite_pattern_substitute \<beta>' p = finite_pattern_substitute \<sigma> (finite_pattern_substitute \<beta> p)"
      by (simp add: \<beta>'_def finite_pattern_substitute_composes)
    from prem sp consider
        (goal) "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending st"
      | (node) m where "m |\<in>| resolution_nodes st" "resolution_node_position m=?q@[s]" "resolution_node_site m=e"
          "resolution_node_call m=finite_pattern_substitute \<beta> p"
      by blast
    then show "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta>' p) |\<in>|
        resolution_pending (resolution_state_substitute \<sigma> st) \<or>
      (\<exists>m. m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st) \<and> resolution_node_position m=?q@[s] \<and>
        resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta>' p)"
    proof cases
      case goal
      have "resolution_goal_substitute \<sigma> (Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e
          (finite_pattern_substitute \<beta> p)) |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
        using fimageI[OF goal, of "resolution_goal_substitute \<sigma>"] by (simp only: resolution_state_substitute_fields)
      then show ?thesis by (simp add: eq)
    next
      case node
      have "resolution_node_substitute \<sigma> m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
        using fimageI[OF node(1), of "resolution_node_substitute \<sigma>"] by (simp only: resolution_state_substitute_fields)
      then show ?thesis using node eq by auto
    qed
  qed
  have mat': "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
      Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M) |\<in>|
        resolution_pending (resolution_state_substitute \<sigma> st) \<or> resolution_material_done \<beta>' M"
  proof (intro allI impI)
    fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S"
    have eq: "finite_material_pattern_substitute \<beta>' M =
        finite_material_pattern_substitute \<sigma> (finite_material_pattern_substitute \<beta> M)"
      by (simp add: \<beta>'_def finite_material_pattern_substitute_composes)
    from mat sM consider
        (goal) "Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta> M) |\<in>| resolution_pending st"
      | (finished) "resolution_material_done \<beta> M"
      by blast
    then show "Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M) |\<in>|
        resolution_pending (resolution_state_substitute \<sigma> st) \<or> resolution_material_done \<beta>' M"
    proof cases
      case goal
      have "resolution_goal_substitute \<sigma> (Resolution_Material_Goal (?q@[s]) (?d,?c,s)
          (finite_material_pattern_substitute \<beta> M)) |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
        using fimageI[OF goal, of "resolution_goal_substitute \<sigma>"] by (simp only: resolution_state_substitute_fields)
      then show ?thesis by (simp add: eq)
    next
      case finished
      then show ?thesis unfolding \<beta>'_def by (rule disjI2[OF resolution_material_done_substitute])
    qed
  qed
  have B': "resolution_node_bindings (resolution_node_substitute \<sigma> nd) = fimage (\<lambda>a. (a,\<beta>' a)) (finite_schema_variables ?S)"
    by (simp add: B \<beta>'_def fset.map_comp comp_def)
  have head': "resolution_node_call (resolution_node_substitute \<sigma> nd) = finite_pattern_substitute \<beta>' (finite_schema_conclusion ?S)"
    by (simp add: head \<beta>'_def finite_pattern_substitute_composes)
  have iface': "resolution_node_call (resolution_node_substitute \<sigma> nd) =
      finite_pattern_substitute (\<lambda>x. finite_pattern_substitute \<sigma> (\<iota> x)) i"
    by (simp add: iface finite_pattern_substitute_composes)
  have c1: "\<exists>i \<iota>. (resolution_node_site (resolution_node_substitute \<sigma> nd),i) |\<in>| finite_system_interfaces P \<and>
      resolution_node_call (resolution_node_substitute \<sigma> nd) = finite_pattern_substitute \<iota> i"
    using interface iface' by (intro exI[of _ i] exI[of _ "\<lambda>x. finite_pattern_substitute \<sigma> (\<iota> x)"]) simp
  have c3: "\<exists>\<beta>. resolution_node_bindings (resolution_node_substitute \<sigma> nd) =
        fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables (resolution_node_schema (resolution_node_substitute \<sigma> nd))) \<and>
      resolution_node_call (resolution_node_substitute \<sigma> nd) =
        finite_pattern_substitute \<beta> (finite_schema_conclusion (resolution_node_schema (resolution_node_substitute \<sigma> nd))) \<and>
      (\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema (resolution_node_substitute \<sigma> nd)) \<longrightarrow>
        Resolution_Call_Goal (resolution_node_position (resolution_node_substitute \<sigma> nd)@[s])
            (Some (resolution_node_site (resolution_node_substitute \<sigma> nd),resolution_node_clause (resolution_node_substitute \<sigma> nd),s)) e
            (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending (resolution_state_substitute \<sigma> st) \<or>
        (\<exists>m. m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st) \<and>
          resolution_node_position m=resolution_node_position (resolution_node_substitute \<sigma> nd)@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta> p)) \<and>
      (\<forall>s M. (s,M) |\<in>| finite_schema_materials (resolution_node_schema (resolution_node_substitute \<sigma> nd)) \<longrightarrow>
        Resolution_Material_Goal (resolution_node_position (resolution_node_substitute \<sigma> nd)@[s])
            (resolution_node_site (resolution_node_substitute \<sigma> nd),resolution_node_clause (resolution_node_substitute \<sigma> nd),s)
            (finite_material_pattern_substitute \<beta> M) |\<in>| resolution_pending (resolution_state_substitute \<sigma> st) \<or>
        resolution_material_done \<beta> M)"
    apply (rule exI[of _ \<beta>'])
    using B' head' prem' mat' by (simp only: resolution_node_substitute_fields)
  show ?thesis unfolding resolution_node_linked_def using c1 clause c3 by (simp only: resolution_node_substitute_fields)
qed

lemma resolution_pattern_invariant_substitute:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and \<sigma>: "\<And>x. finite_pattern_formed (\<sigma> x)"
  shows "resolution_pattern_invariant P d \<pi> (resolution_state_substitute \<sigma> st)"
proof -
  let ?st = "resolution_state_substitute \<sigma> st"
  have composed: "\<And>\<rho>. finite_pattern_substitute \<sigma> (finite_pattern_substitute \<rho> \<pi>) =
      finite_pattern_substitute (\<lambda>a. finite_pattern_substitute \<sigma> (\<rho> a)) \<pi>"
    by (rule finite_pattern_substitute_composes)
  have root: "resolution_pattern_root_held d \<pi> ?st"
  proof -
    have "(\<exists>\<rho>. Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>) |\<in>| resolution_pending st) \<or>
        (\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[])"
      using I unfolding resolution_pattern_invariant_def resolution_pattern_root_held_def by blast
    then show ?thesis
    proof
      assume "\<exists>\<rho>. Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>) |\<in>| resolution_pending st"
      then obtain \<rho> where g: "Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>) |\<in>| resolution_pending st"
        by blast
      have "resolution_goal_substitute \<sigma> (Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>)) |\<in>|
          resolution_pending ?st"
        unfolding resolution_state_substitute_fields by (rule fimageI[OF g])
      then have "Resolution_Call_Goal [] None d (finite_pattern_substitute (\<lambda>a. finite_pattern_substitute \<sigma> (\<rho> a)) \<pi>)
          |\<in>| resolution_pending ?st"
        by (simp only: resolution_goal_substitute.simps composed)
      then show ?thesis unfolding resolution_pattern_root_held_def by blast
    next
      assume "\<exists>nd. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[]"
      then obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd=[]" by blast
      have "resolution_node_substitute \<sigma> nd |\<in>| resolution_nodes ?st"
        unfolding resolution_state_substitute_fields by (rule fimageI[OF nd(1)])
      moreover have "resolution_node_position (resolution_node_substitute \<sigma> nd)=[]" using nd(2) by simp
      ultimately show ?thesis unfolding resolution_pattern_root_held_def by blast
    qed
  qed
  have goals: "resolution_pattern_goals_placed d \<pi> ?st"
    unfolding resolution_pattern_goals_placed_def
  proof (intro allI impI)
    fix g' assume "g' |\<in>| resolution_pending ?st"
    then obtain g where g: "g |\<in>| resolution_pending st" and g': "g'=resolution_goal_substitute \<sigma> g"
      by (auto simp: fimage.rep_eq)
    have placed: "resolution_goal_formed g"
        "resolution_goal_position g=[] \<longrightarrow> (\<exists>\<rho>. g=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>))"
        "resolution_goal_position g\<noteq>[] \<longrightarrow>
          (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_goal_position g))"
      using I g unfolding resolution_pattern_invariant_def resolution_pattern_goals_placed_def by blast+
    show "resolution_goal_formed g' \<and>
        (resolution_goal_position g'=[] \<longrightarrow> (\<exists>\<rho>. g'=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>))) \<and>
        (resolution_goal_position g'\<noteq>[] \<longrightarrow>
          (\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=butlast (resolution_goal_position g')))"
    proof (intro conjI impI)
      show "resolution_goal_formed g'" using placed(1) \<sigma> by (simp add: g' resolution_goal_substitute_formed)
      show "\<exists>\<rho>. g'=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>)"
        if pos: "resolution_goal_position g'=[]"
      proof -
        obtain \<rho> where "g=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>)"
          using placed(2) pos g' by auto
        then have "g'=Resolution_Call_Goal [] None d (finite_pattern_substitute (\<lambda>a. finite_pattern_substitute \<sigma> (\<rho> a)) \<pi>)"
          by (simp add: g' composed)
        then show ?thesis by blast
      qed
      show "\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=butlast (resolution_goal_position g')"
        if "resolution_goal_position g'\<noteq>[]"
        using placed(3) that by (auto simp: g' fimage.rep_eq)
    qed
  qed
  have nodes: "resolution_pattern_nodes_placed P d \<pi> ?st"
    unfolding resolution_pattern_nodes_placed_def
  proof (intro allI impI)
    fix nd' assume "nd' |\<in>| resolution_nodes ?st"
    then obtain nd where nd: "nd |\<in>| resolution_nodes st" and nd': "nd'=resolution_node_substitute \<sigma> nd"
      by (auto simp: fimage.rep_eq)
    have placed: "finite_pattern_formed (resolution_node_call nd)"
        "\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd \<longrightarrow> finite_pattern_formed x"
        "resolution_node_linked P st nd"
        "resolution_node_position nd=[] \<longrightarrow> resolution_node_site nd=d \<and>
          (\<exists>\<rho>. resolution_node_call nd=finite_pattern_substitute \<rho> \<pi>)"
        "resolution_node_position nd\<noteq>[] \<longrightarrow>
          (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_node_position nd))"
      using I nd unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast+
    have linked: "resolution_node_linked P ?st nd'" using resolution_linked_substitute[OF placed(3)] by (simp add: nd')
    have root: "resolution_node_site nd'=d \<and> (\<exists>\<rho>. resolution_node_call nd'=finite_pattern_substitute \<rho> \<pi>)"
      if pos: "resolution_node_position nd'=[]"
    proof -
      obtain \<rho> where "resolution_node_site nd=d" "resolution_node_call nd=finite_pattern_substitute \<rho> \<pi>"
        using placed(4) pos nd' by auto
      then have "resolution_node_site nd'=d \<and>
          resolution_node_call nd'=finite_pattern_substitute (\<lambda>a. finite_pattern_substitute \<sigma> (\<rho> a)) \<pi>"
        by (simp add: nd' composed)
      then show ?thesis by blast
    qed
    show "finite_pattern_formed (resolution_node_call nd') \<and>
        (\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd' \<longrightarrow> finite_pattern_formed x) \<and>
        resolution_node_linked P ?st nd' \<and>
        (resolution_node_position nd'=[] \<longrightarrow> resolution_node_site nd'=d \<and>
          (\<exists>\<rho>. resolution_node_call nd'=finite_pattern_substitute \<rho> \<pi>)) \<and>
        (resolution_node_position nd'\<noteq>[] \<longrightarrow>
          (\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=butlast (resolution_node_position nd')))"
    proof (intro conjI impI)
      show "finite_pattern_formed (resolution_node_call nd')"
        using placed(1) \<sigma> by (simp add: nd' finite_pattern_substitute_formed)
      show "\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd' \<longrightarrow> finite_pattern_formed x"
        using placed(2) \<sigma> by (auto simp: nd' fimage.rep_eq intro: finite_pattern_substitute_formed)
      show "resolution_node_linked P ?st nd'" by (rule linked)
      show "resolution_node_site nd'=d" if "resolution_node_position nd'=[]" using root[OF that] by blast
      show "\<exists>\<rho>. resolution_node_call nd'=finite_pattern_substitute \<rho> \<pi>" if "resolution_node_position nd'=[]"
        using root[OF that] by blast
      show "\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=butlast (resolution_node_position nd')"
        if "resolution_node_position nd'\<noteq>[]" using placed(5) that by (auto simp: nd' fimage.rep_eq)
    qed
  qed
  have distinct: "resolution_positions_distinct ?st"
    using I unfolding resolution_pattern_invariant_def resolution_positions_distinct_def by (auto simp: fimage.rep_eq)
  show ?thesis using I root goals nodes distinct unfolding resolution_pattern_invariant_def by blast
qed

lemma resolution_invariant_substitute:
  assumes I: "resolution_invariant P d t st" and \<sigma>: "\<And>x. finite_pattern_formed (\<sigma> x)"
  shows "resolution_invariant P d t (resolution_state_substitute \<sigma> st)"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_invariant_substitute)

lemma resolution_goal_minus_image:
  assumes distinct: "resolution_positions_distinct st" and goal: "g |\<in>| resolution_pending st"
  shows "fimage (resolution_goal_substitute \<sigma>) (resolution_pending st |-| {|g|}) =
    fimage (resolution_goal_substitute \<sigma>) (resolution_pending st) |-| {|resolution_goal_substitute \<sigma> g|}"
proof -
  have same: "h=g" if h: "h |\<in>| resolution_pending st"
    and eq: "resolution_goal_substitute \<sigma> h=resolution_goal_substitute \<sigma> g" for h
  proof -
    have "resolution_goal_position h=resolution_goal_position g"
      using arg_cong[OF eq, of resolution_goal_position] by simp
    then show "h=g" using distinct h goal unfolding resolution_positions_distinct_def by blast
  qed
  show ?thesis unfolding fset_eq_iff using same by (auto simp: resolution_fset_simps)
qed

lemma finite_clause_goals_substitute:
  "fimage (resolution_goal_substitute \<sigma>) (finite_clause_goals q e c S) =
    fimage (\<lambda>(s,e',p'). Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e'
        (finite_pattern_substitute (\<lambda>a. \<sigma> ((q,True),a)) p')) (finite_schema_premises S) |\<union>|
    fimage (\<lambda>(s,M). Resolution_Material_Goal (q@[s]) (e,c,s)
        (finite_material_pattern_substitute (\<lambda>a. \<sigma> ((q,True),a)) M)) (finite_schema_materials S)"
  unfolding finite_clause_goals_def fimage_funion fset.map_comp
  by (intro arg_cong2[where f=sup] fset.map_cong0)
    (auto simp: finite_rename_apart_def finite_rename_as_substitute finite_rename_material_as_substitute
      finite_pattern_substitute_composes finite_material_pattern_substitute_composes split: prod.splits)

lemma finite_clause_node_substitute:
  "resolution_node_substitute \<sigma> (finite_clause_node q e c S) =
    Resolution_Node q e c S (finite_pattern_substitute \<sigma> (finite_rename_apart (q,True) (finite_schema_conclusion S)))
      (fimage (\<lambda>a. (a,\<sigma> ((q,True),a))) (finite_schema_variables S))"
  by (simp add: finite_clause_node_def fset.map_comp comp_def)

lemma finite_system_formed_parts:
  assumes "finite_system_formed P"
  shows "(e,i) |\<in>| finite_system_interfaces P \<Longrightarrow> finite_pattern_formed i"
    and "((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> finite_schema_formed S"
  using assms unfolding finite_system_formed_def by fastforce+

lemma resolution_pattern_invariant_add:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and clause: "((e,c),S) |\<in>| finite_system_clauses P" and interface: "(e,i) |\<in>| finite_system_interfaces P"
    and iface: "p = finite_pattern_substitute \<iota> i"
    and head: "p = finite_pattern_substitute \<beta> (finite_schema_conclusion S)"
    and \<beta>f: "\<And>a. finite_pattern_formed (\<beta> a)"
    and G: "G = fimage (\<lambda>(s,e',p'). Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p'))
        (finite_schema_premises S) |\<union>|
      fimage (\<lambda>(s,M). Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M))
        (finite_schema_materials S)"
    and nd: "nd = Resolution_Node q e c S p (fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables S))"
  shows "resolution_pattern_invariant P d \<pi>
    (Resolution_State (G |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})) (finsert nd (resolution_nodes st)) W)"
proof -
  let ?g = "Resolution_Call_Goal q r e p"
  let ?st = "Resolution_State (G |\<union>| (resolution_pending st |-| {|?g|})) (finsert nd (resolution_nodes st)) W"
  have Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and root: "resolution_pattern_root_held d \<pi> st" and goals: "resolution_pattern_goals_placed d \<pi> st"
    and nodes: "resolution_pattern_nodes_placed P d \<pi> st" and dist: "resolution_positions_distinct st"
    using I unfolding resolution_pattern_invariant_def by blast+
  have Sf: "finite_schema_formed S" by (rule finite_system_formed_parts(2)[OF Pf clause])
  have "resolution_goal_formed (Resolution_Call_Goal q r e p)"
    using goals goal unfolding resolution_pattern_goals_placed_def by blast
  then have gf: "finite_pattern_formed p" by simp
  have no_node: "resolution_node_position m\<noteq>q" if "m |\<in>| resolution_nodes st" for m
    using dist goal that unfolding resolution_positions_distinct_def by fastforce
  have no_child: "resolution_node_position m\<noteq>q@[s]" if m: "m |\<in>| resolution_nodes st" for m s
  proof
    assume at: "resolution_node_position m=q@[s]"
    then obtain m' where "m' |\<in>| resolution_nodes st" "resolution_node_position m'=q"
      using nodes m unfolding resolution_pattern_nodes_placed_def by fastforce
    then show False using no_node by blast
  qed
  have no_child_goal: "resolution_goal_position h\<noteq>q@[s]" if h: "h |\<in>| resolution_pending st" for h s
  proof
    assume at: "resolution_goal_position h=q@[s]"
    then obtain m' where "m' |\<in>| resolution_nodes st" "resolution_node_position m'=q"
      using goals h unfolding resolution_pattern_goals_placed_def by fastforce
    then show False using no_node by blast
  qed
  have gp: "resolution_goal_formed h \<and>
      (resolution_goal_position h=[] \<longrightarrow> (\<exists>\<rho>. h=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>))) \<and>
      (resolution_goal_position h\<noteq>[] \<longrightarrow>
        (\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast (resolution_goal_position h)))"
    if "h |\<in>| resolution_pending st" for h
    using goals that unfolding resolution_pattern_goals_placed_def by blast
  have root_goal: "e=d \<and> (\<exists>\<rho>. p=finite_pattern_substitute \<rho> \<pi>)" if "q=[]"
    using gp[OF goal] that by auto
  have parent: "\<exists>m. m |\<in>| resolution_nodes st \<and> resolution_node_position m=butlast q" if "q\<noteq>[]"
    using gp[OF goal] that by simp
  have prem_fun: "finite_relation_functional (finite_schema_premises S)"
    and mat_fun: "finite_relation_functional (finite_schema_materials S)"
    and sockets: "fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||}"
    and prem_formed: "fBall (finite_schema_premises S) (\<lambda>(s,d,p). finite_pattern_formed p)"
    and mat_formed: "fBall (finite_schema_materials S) (\<lambda>(s,M). finite_material_formed M)"
    using Sf unfolding finite_schema_formed_def by blast+
  have Gmem: "x |\<in>| G \<longleftrightarrow>
      (\<exists>s e' p'. (s,e',p') |\<in>| finite_schema_premises S \<and>
        x=Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p')) \<or>
      (\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and>
        x=Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M))" for x
    unfolding G fimage.rep_eq sup_fset.rep_eq Un_iff image_iff by fastforce
  have Gpos: "\<exists>s. resolution_goal_position x=q@[s]" if "x |\<in>| G" for x
    using that Gmem by fastforce
  have Gformed: "resolution_goal_formed x" if "x |\<in>| G" for x
    using that Gmem prem_formed mat_formed \<beta>f
    by (fastforce intro: finite_pattern_substitute_formed finite_material_pattern_substitute_formed)
  have prem_same: "e1=e2 \<and> p1=p2" if "(s,e1,p1) |\<in>| finite_schema_premises S" "(s,e2,p2) |\<in>| finite_schema_premises S"
    for s e1 e2 p1 p2
    using prem_fun that unfolding finite_relation_functional_def by fastforce
  have mat_same: "M1=M2" if "(s,M1) |\<in>| finite_schema_materials S" "(s,M2) |\<in>| finite_schema_materials S" for s M1 M2
    using mat_fun that unfolding finite_relation_functional_def by fastforce
  have apart: False if "(s,e1,p1) |\<in>| finite_schema_premises S" "(s,M1) |\<in>| finite_schema_materials S" for s e1 p1 M1
  proof -
    have "s |\<in>| fimage fst (finite_schema_premises S)" using that(1) by (force simp: fimage.rep_eq)
    moreover have "s |\<in>| fimage fst (finite_schema_materials S)" using that(2) by (force simp: fimage.rep_eq)
    ultimately have "s |\<in>| fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S)" by simp
    then show False using sockets by simp
  qed
  have Gdistinct: "x=y" if "x |\<in>| G" "y |\<in>| G" "resolution_goal_position x=resolution_goal_position y" for x y
  proof -
    note pos = that(3)
    from that(2) Gmem consider (py) s2 e2 p2 where "(s2,e2,p2) |\<in>| finite_schema_premises S"
        "y=Resolution_Call_Goal (q@[s2]) (Some (e,c,s2)) e2 (finite_pattern_substitute \<beta> p2)"
      | (my) s2 M2 where "(s2,M2) |\<in>| finite_schema_materials S"
        "y=Resolution_Material_Goal (q@[s2]) (e,c,s2) (finite_material_pattern_substitute \<beta> M2)" by blast
    note ycases = this
    from that(1) Gmem consider (px) s e' p' where "(s,e',p') |\<in>| finite_schema_premises S"
        "x=Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p')"
      | (mx) s M where "(s,M) |\<in>| finite_schema_materials S"
        "x=Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M)" by blast
    then show "x=y"
    proof cases
      case px
      show ?thesis using ycases
      proof cases
        case py
        have "s=s2" using pos px(2) py(2) by simp
        then have "e'=e2 \<and> p'=p2" using prem_same px(1) py(1) by blast
        then show ?thesis using px(2) py(2) \<open>s=s2\<close> by simp
      next
        case my
        have "s=s2" using pos px(2) my(2) by simp
        then show ?thesis using apart px(1) my(1) by blast
      qed
    next
      case mx
      show ?thesis using ycases
      proof cases
        case py
        have "s=s2" using pos mx(2) py(2) by simp
        then show ?thesis using apart py(1) mx(1) by blast
      next
        case my
        have "s=s2" using pos mx(2) my(2) by simp
        then have "M=M2" using mat_same mx(1) my(1) by blast
        then show ?thesis using mx(2) my(2) \<open>s=s2\<close> by simp
      qed
    qed
  qed
  have Gcall: "Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p') |\<in>| G"
    if "(s,e',p') |\<in>| finite_schema_premises S" for s e' p'
    using that unfolding G by (force simp: fimage.rep_eq)
  have Gmat: "Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M) |\<in>| G"
    if "(s,M) |\<in>| finite_schema_materials S" for s M
    using that unfolding G by (force simp: fimage.rep_eq)
  have linked_nd: "resolution_node_linked P ?st nd"
    unfolding resolution_node_linked_def
  proof (intro conjI)
    show "\<exists>i \<iota>. (resolution_node_site nd,i) |\<in>| finite_system_interfaces P \<and>
        resolution_node_call nd = finite_pattern_substitute \<iota> i"
      using interface iface by (intro exI[of _ i] exI[of _ \<iota>]) (simp add: nd)
    show "((resolution_node_site nd,resolution_node_clause nd),resolution_node_schema nd) |\<in>| finite_system_clauses P"
      using clause by (simp add: nd)
    show "\<exists>\<beta>'. resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta>' a)) (finite_schema_variables (resolution_node_schema nd)) \<and>
      resolution_node_call nd = finite_pattern_substitute \<beta>' (finite_schema_conclusion (resolution_node_schema nd)) \<and>
      (\<forall>s e' p'. (s,e',p') |\<in>| finite_schema_premises (resolution_node_schema nd) \<longrightarrow>
        Resolution_Call_Goal (resolution_node_position nd@[s]) (Some (resolution_node_site nd,resolution_node_clause nd,s)) e'
            (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending ?st \<or>
        (\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=resolution_node_position nd@[s] \<and>
          resolution_node_site m=e' \<and> resolution_node_call m=finite_pattern_substitute \<beta>' p')) \<and>
      (\<forall>s M. (s,M) |\<in>| finite_schema_materials (resolution_node_schema nd) \<longrightarrow>
        Resolution_Material_Goal (resolution_node_position nd@[s]) (resolution_node_site nd,resolution_node_clause nd,s)
            (finite_material_pattern_substitute \<beta>' M) |\<in>| resolution_pending ?st \<or>
        resolution_material_done \<beta>' M)"
      apply (rule exI[of _ \<beta>], intro conjI allI impI)
         apply (simp add: nd)
        apply (simp add: nd head)
       apply (simp add: nd Gcall)
      apply (simp add: nd Gmat)
      done
  qed
  have linked_old: "resolution_node_linked P ?st m" if m: "m |\<in>| resolution_nodes st" for m
  proof -
    let ?S = "resolution_node_schema m" and ?q = "resolution_node_position m"
      and ?d = "resolution_node_site m" and ?c = "resolution_node_clause m"
    have linked: "resolution_node_linked P st m" using nodes m unfolding resolution_pattern_nodes_placed_def by blast
    obtain i' \<iota>' where if12: "(?d,i') |\<in>| finite_system_interfaces P" "resolution_node_call m = finite_pattern_substitute \<iota>' i'"
      using linked unfolding resolution_node_linked_def by blast
    have clause_m: "((?d,?c),?S) |\<in>| finite_system_clauses P" using linked unfolding resolution_node_linked_def by blast
    obtain \<beta>' where B: "resolution_node_bindings m = fimage (\<lambda>a. (a,\<beta>' a)) (finite_schema_variables ?S)"
        and hd: "resolution_node_call m = finite_pattern_substitute \<beta>' (finite_schema_conclusion ?S)"
        and prem: "\<forall>s e' p'. (s,e',p') |\<in>| finite_schema_premises ?S \<longrightarrow>
          Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending st \<or>
          (\<exists>m'. m' |\<in>| resolution_nodes st \<and> resolution_node_position m'=?q@[s] \<and>
            resolution_node_site m'=e' \<and> resolution_node_call m'=finite_pattern_substitute \<beta>' p')"
        and mat: "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
          Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M) |\<in>| resolution_pending st \<or>
          resolution_material_done \<beta>' M"
      using linked unfolding resolution_node_linked_def by blast
    have prem': "\<forall>s e' p'. (s,e',p') |\<in>| finite_schema_premises ?S \<longrightarrow>
        Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending ?st \<or>
        (\<exists>m'. m' |\<in>| resolution_nodes ?st \<and> resolution_node_position m'=?q@[s] \<and>
          resolution_node_site m'=e' \<and> resolution_node_call m'=finite_pattern_substitute \<beta>' p')"
    proof (intro allI impI)
      fix s e' p' assume sp: "(s,e',p') |\<in>| finite_schema_premises ?S"
      from prem sp consider
          (goal) "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending st"
        | (node) m' where "m' |\<in>| resolution_nodes st" "resolution_node_position m'=?q@[s]"
            "resolution_node_site m'=e'" "resolution_node_call m'=finite_pattern_substitute \<beta>' p'"
        by blast
      then show "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending ?st \<or>
          (\<exists>m'. m' |\<in>| resolution_nodes ?st \<and> resolution_node_position m'=?q@[s] \<and>
            resolution_node_site m'=e' \<and> resolution_node_call m'=finite_pattern_substitute \<beta>' p')"
      proof cases
        case goal
        show ?thesis
        proof (cases "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') = ?g")
          case True
          then have "resolution_node_position nd=?q@[s] \<and> resolution_node_site nd=e' \<and>
              resolution_node_call nd=finite_pattern_substitute \<beta>' p'" by (simp add: nd)
          then show ?thesis by (auto simp: resolution_fset_simps)
        next
          case False
          then show ?thesis using goal by (simp add: resolution_fset_simps)
        qed
      next
        case node
        then show ?thesis by (auto simp: resolution_fset_simps)
      qed
    qed
    have mat': "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
        Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M) |\<in>| resolution_pending ?st \<or>
        resolution_material_done \<beta>' M"
      using mat by (auto simp: resolution_fset_simps)
    show ?thesis unfolding resolution_node_linked_def
      apply (intro conjI)
        apply (use if12 in blast)
       apply (rule clause_m)
      apply (rule exI[of _ \<beta>'], intro conjI)
         apply (rule B)
        apply (rule hd)
       apply (rule prem')
      apply (rule mat')
      done
  qed
  have root': "resolution_pattern_root_held d \<pi> ?st"
    using root no_node by (cases "q=[]") (auto simp: resolution_pattern_root_held_def nd resolution_fset_simps)
  have goals': "resolution_pattern_goals_placed d \<pi> ?st"
    unfolding resolution_pattern_goals_placed_def
  proof (intro allI impI)
    fix x assume x: "x |\<in>| resolution_pending ?st"
    show "resolution_goal_formed x \<and>
        (resolution_goal_position x=[] \<longrightarrow> (\<exists>\<rho>. x=Resolution_Call_Goal [] None d (finite_pattern_substitute \<rho> \<pi>))) \<and>
        (resolution_goal_position x\<noteq>[] \<longrightarrow>
          (\<exists>m. m |\<in>| resolution_nodes ?st \<and> resolution_node_position m=butlast (resolution_goal_position x)))"
    proof (cases "x |\<in>| G")
      case True
      then obtain s where "resolution_goal_position x=q@[s]" using Gpos by blast
      then show ?thesis using Gformed[OF True] by (auto simp: nd resolution_fset_simps)
    next
      case False
      then have old: "x |\<in>| resolution_pending st" using x by (simp add: resolution_fset_simps)
      then show ?thesis using goals unfolding resolution_pattern_goals_placed_def by (fastforce simp: resolution_fset_simps)
    qed
  qed
  have nodes': "resolution_pattern_nodes_placed P d \<pi> ?st"
    unfolding resolution_pattern_nodes_placed_def
  proof (intro allI impI)
    fix m assume m: "m |\<in>| resolution_nodes ?st"
    show "finite_pattern_formed (resolution_node_call m) \<and>
        (\<forall>a x. (a,x) |\<in>| resolution_node_bindings m \<longrightarrow> finite_pattern_formed x) \<and>
        resolution_node_linked P ?st m \<and>
        (resolution_node_position m=[] \<longrightarrow> resolution_node_site m=d \<and>
          (\<exists>\<rho>. resolution_node_call m=finite_pattern_substitute \<rho> \<pi>)) \<and>
        (resolution_node_position m\<noteq>[] \<longrightarrow>
          (\<exists>m'. m' |\<in>| resolution_nodes ?st \<and> resolution_node_position m'=butlast (resolution_node_position m)))"
    proof (cases "m=nd")
      case True
      show ?thesis using gf \<beta>f linked_nd root_goal parent by (auto simp: True nd resolution_fset_simps)
    next
      case False
      then have old: "m |\<in>| resolution_nodes st" using m by (simp add: resolution_fset_simps)
      then show ?thesis using nodes linked_old[OF old] unfolding resolution_pattern_nodes_placed_def
        by (fastforce simp: resolution_fset_simps)
    qed
  qed
  have dist': "resolution_positions_distinct ?st"
    unfolding resolution_positions_distinct_def
  proof (intro conjI allI impI)
    fix m m' assume m: "m |\<in>| resolution_nodes ?st" and m': "m' |\<in>| resolution_nodes ?st"
      and pos: "resolution_node_position m=resolution_node_position m'"
    have old: "x |\<in>| resolution_nodes st" if "x |\<in>| resolution_nodes ?st" "x\<noteq>nd" for x
      using that by (simp add: resolution_fset_simps)
    have posnd: "resolution_node_position nd=q" by (simp add: nd)
    show "m=m'"
    proof (cases "m=nd")
      case True
      show ?thesis
      proof (rule ccontr)
        assume "m\<noteq>m'"
        then have "m' |\<in>| resolution_nodes st" using old m' True by blast
        moreover have "resolution_node_position m'=q" using pos True posnd by simp
        ultimately show False using no_node by blast
      qed
    next
      case mnd: False
      show ?thesis
      proof (cases "m'=nd")
        case True
        have "m |\<in>| resolution_nodes st" using old m mnd by blast
        moreover have "resolution_node_position m=q" using pos True posnd by simp
        ultimately show ?thesis using no_node by blast
      next
        case False
        have "m |\<in>| resolution_nodes st" "m' |\<in>| resolution_nodes st" using old m m' mnd False by blast+
        then show ?thesis using dist pos unfolding resolution_positions_distinct_def by blast
      qed
    qed
  next
    fix x y assume x: "x |\<in>| resolution_pending ?st" and y: "y |\<in>| resolution_pending ?st"
      and pos: "resolution_goal_position x=resolution_goal_position y"
    show "x=y"
    proof (cases "x |\<in>| G")
      case xG: True
      show ?thesis
      proof (cases "y |\<in>| G")
        case True then show ?thesis using Gdistinct xG pos by blast
      next
        case False
        then have yo: "y |\<in>| resolution_pending st" using y by (simp add: resolution_fset_simps)
        obtain s where "resolution_goal_position x=q@[s]" using Gpos[OF xG] by blast
        then have False using no_child_goal[OF yo, of s] pos by simp
        then show ?thesis by blast
      qed
    next
      case xG: False
      then have xo: "x |\<in>| resolution_pending st" using x by (simp add: resolution_fset_simps)
      show ?thesis
      proof (cases "y |\<in>| G")
        case True
        obtain s where "resolution_goal_position y=q@[s]" using Gpos[OF True] by blast
        then have False using no_child_goal[OF xo, of s] pos by simp
        then show ?thesis by blast
      next
        case False
        then have "y |\<in>| resolution_pending st" using y by (simp add: resolution_fset_simps)
        then show ?thesis using xo pos dist unfolding resolution_positions_distinct_def by blast
      qed
    qed
  next
    fix x m assume x: "x |\<in>| resolution_pending ?st" and m: "m |\<in>| resolution_nodes ?st" and call: "resolution_is_call x"
    show "resolution_goal_position x\<noteq>resolution_node_position m"
    proof (cases "x |\<in>| G")
      case True
      then obtain s where xs: "resolution_goal_position x=q@[s]" using Gpos by blast
      show ?thesis
      proof
        assume eq: "resolution_goal_position x=resolution_node_position m"
        show False
        proof (cases "m=nd")
          case True then show False using xs eq by (simp add: nd)
        next
          case False
          then have "m |\<in>| resolution_nodes st" using m by (simp add: resolution_fset_simps)
          then show False using no_child[of m s] xs eq by simp
        qed
      qed
    next
      case False
      then have xo: "x |\<in>| resolution_pending st" and xg: "x\<noteq>?g" using x by (simp_all add: resolution_fset_simps)
      have "resolution_goal_position x\<noteq>q"
      proof
        assume "resolution_goal_position x=q"
        then have "x=?g" using dist xo goal unfolding resolution_positions_distinct_def by fastforce
        then show False using xg by blast
      qed
      note notq = this
      show ?thesis
      proof (cases "m=nd")
        case True then show ?thesis using notq by (simp add: nd)
      next
        case False
        then have "m |\<in>| resolution_nodes st" using m by (simp add: resolution_fset_simps)
        then show ?thesis using xo call dist unfolding resolution_positions_distinct_def by blast
      qed
    qed
  qed
  show ?thesis using Pf \<pi>f root' goals' nodes' dist' unfolding resolution_pattern_invariant_def by blast
qed

lemma resolution_invariant_add:
  assumes I: "resolution_invariant P d t st"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and clause: "((e,c),S) |\<in>| finite_system_clauses P" and interface: "(e,i) |\<in>| finite_system_interfaces P"
    and iface: "p = finite_pattern_substitute \<iota> i"
    and head: "p = finite_pattern_substitute \<beta> (finite_schema_conclusion S)"
    and \<beta>f: "\<And>a. finite_pattern_formed (\<beta> a)"
    and G: "G = fimage (\<lambda>(s,e',p'). Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p'))
        (finite_schema_premises S) |\<union>|
      fimage (\<lambda>(s,M). Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M))
        (finite_schema_materials S)"
    and nd: "nd = Resolution_Node q e c S p (fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables S))"
  shows "resolution_invariant P d t
    (Resolution_State (G |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|})) (finsert nd (resolution_nodes st)) W)"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_invariant_add)

lemma resolution_pattern_invariant_remove:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and ground: "finite_material_ground_satisfied M"
  shows "resolution_pattern_invariant P d \<pi>
    (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st) W)"
proof -
  let ?g = "Resolution_Material_Goal q r M"
  let ?st = "Resolution_State (resolution_pending st |-| {|?g|}) (resolution_nodes st) W"
  have Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and root: "resolution_pattern_root_held d \<pi> st" and goals: "resolution_pattern_goals_placed d \<pi> st"
    and nodes: "resolution_pattern_nodes_placed P d \<pi> st" and dist: "resolution_positions_distinct st"
    using I unfolding resolution_pattern_invariant_def by blast+
  have linked_old: "resolution_node_linked P ?st m" if m: "m |\<in>| resolution_nodes st" for m
  proof -
    let ?S = "resolution_node_schema m" and ?q = "resolution_node_position m"
      and ?d = "resolution_node_site m" and ?c = "resolution_node_clause m"
    have linked: "resolution_node_linked P st m" using nodes m unfolding resolution_pattern_nodes_placed_def by blast
    have clause: "((?d,?c),?S) |\<in>| finite_system_clauses P" using linked unfolding resolution_node_linked_def by blast
    have mat_formed: "fBall (finite_schema_materials ?S) (\<lambda>(s,M). finite_material_formed M)"
      using finite_system_formed_parts(2)[OF Pf clause] unfolding finite_schema_formed_def by blast
    obtain i' \<iota>' where if12: "(?d,i') |\<in>| finite_system_interfaces P" "resolution_node_call m = finite_pattern_substitute \<iota>' i'"
      using linked unfolding resolution_node_linked_def by blast
    obtain \<beta>' where B: "resolution_node_bindings m = fimage (\<lambda>a. (a,\<beta>' a)) (finite_schema_variables ?S)"
        and hd: "resolution_node_call m = finite_pattern_substitute \<beta>' (finite_schema_conclusion ?S)"
        and prem: "\<forall>s e' p'. (s,e',p') |\<in>| finite_schema_premises ?S \<longrightarrow>
          Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending st \<or>
          (\<exists>m'. m' |\<in>| resolution_nodes st \<and> resolution_node_position m'=?q@[s] \<and>
            resolution_node_site m'=e' \<and> resolution_node_call m'=finite_pattern_substitute \<beta>' p')"
        and mat: "\<forall>s M'. (s,M') |\<in>| finite_schema_materials ?S \<longrightarrow>
          Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M') |\<in>| resolution_pending st \<or>
          resolution_material_done \<beta>' M'"
      using linked unfolding resolution_node_linked_def by blast
    have prem': "\<forall>s e' p'. (s,e',p') |\<in>| finite_schema_premises ?S \<longrightarrow>
        Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e' (finite_pattern_substitute \<beta>' p') |\<in>| resolution_pending ?st \<or>
        (\<exists>m'. m' |\<in>| resolution_nodes ?st \<and> resolution_node_position m'=?q@[s] \<and>
          resolution_node_site m'=e' \<and> resolution_node_call m'=finite_pattern_substitute \<beta>' p')"
      using prem by (auto simp: resolution_fset_simps)
    have mat': "\<forall>s M'. (s,M') |\<in>| finite_schema_materials ?S \<longrightarrow>
        Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M') |\<in>| resolution_pending ?st \<or>
        resolution_material_done \<beta>' M'"
    proof (intro allI impI)
      fix s M' assume sM: "(s,M') |\<in>| finite_schema_materials ?S"
      have Mf: "finite_material_formed M'" using mat_formed sM by fastforce
      show "Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M') |\<in>| resolution_pending ?st \<or>
          resolution_material_done \<beta>' M'"
      proof (cases "Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta>' M') = ?g")
        case True
        then have "finite_material_pattern_substitute \<beta>' M' = M" by simp
        then have "resolution_material_done \<beta>' M'" using resolution_material_done_ground[OF Mf, of \<beta>'] ground by simp
        then show ?thesis by blast
      next
        case False
        then show ?thesis using mat sM by (auto simp: resolution_fset_simps)
      qed
    qed
    show ?thesis unfolding resolution_node_linked_def
      apply (intro conjI)
        apply (use if12 in blast)
       apply (rule clause)
      apply (rule exI[of _ \<beta>'], intro conjI)
         apply (rule B)
        apply (rule hd)
       apply (rule prem')
      apply (rule mat')
      done
  qed
  have root': "resolution_pattern_root_held d \<pi> ?st"
    using root by (auto simp: resolution_pattern_root_held_def resolution_fset_simps)
  have goals': "resolution_pattern_goals_placed d \<pi> ?st"
    using goals unfolding resolution_pattern_goals_placed_def by (auto simp: resolution_fset_simps)
  have nodes': "resolution_pattern_nodes_placed P d \<pi> ?st"
    using nodes linked_old unfolding resolution_pattern_nodes_placed_def by (simp only: resolution_state.sel) blast
  have dist': "resolution_positions_distinct ?st"
    using dist unfolding resolution_positions_distinct_def by (auto simp: resolution_fset_simps)
  show ?thesis using Pf \<pi>f root' goals' nodes' dist' unfolding resolution_pattern_invariant_def by blast
qed

lemma resolution_invariant_remove:
  assumes I: "resolution_invariant P d t st"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and ground: "finite_material_ground_satisfied M"
  shows "resolution_invariant P d t
    (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st) W)"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_invariant_remove)

lemma finite_call_successors_member:
  assumes "st' |\<in>| finite_call_successors P st q r e p"
  obtains i c S u where "(e,i) |\<in>| finite_system_interfaces P" "((e,c),S) |\<in>| finite_system_clauses P"
    "finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
    "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}))
        (finsert (finite_clause_node q e c S) (resolution_nodes st)) (resolution_witnesses st))"
  using assms unfolding finite_call_successors_def
  by (auto simp: resolution_fset_simps split: if_splits option.splits)

lemma finite_rename_apart_substitute:
  "finite_pattern_substitute \<sigma> (finite_rename_apart w f) = finite_pattern_substitute (\<lambda>a. \<sigma> (w,a)) f"
  by (simp add: finite_rename_apart_def finite_rename_as_substitute finite_pattern_substitute_composes)

lemma resolution_pattern_call_step:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and step: "st' |\<in>| finite_call_successors P st q r e p"
  shows "resolution_pattern_invariant P d \<pi> st'"
proof -
  obtain i c S u where interface: "(e,i) |\<in>| finite_system_interfaces P" and clause: "((e,c),S) |\<in>| finite_system_clauses P"
    and unify: "finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
    and st': "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q e c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r e p|}))
        (finsert (finite_clause_node q e c S) (resolution_nodes st)) (resolution_witnesses st))"
    using step by (rule finite_call_successors_member)
  let ?\<sigma> = "finite_binding_substitution u"
  have Pf: "finite_system_formed P" using I by (simp add: resolution_pattern_invariant_def)
  have i_f: "finite_pattern_formed i" by (rule finite_system_formed_parts(1)[OF Pf interface])
  have Sf: "finite_schema_formed S" by (rule finite_system_formed_parts(2)[OF Pf clause])
  have "resolution_goal_formed (Resolution_Call_Goal q r e p)"
    using I goal unfolding resolution_pattern_invariant_def resolution_pattern_goals_placed_def by blast
  then have gf: "finite_pattern_formed p" by simp
  have concl_f: "finite_pattern_formed (finite_schema_conclusion S)" using Sf by (simp add: finite_schema_formed_def)
  have Ef: "\<forall>x\<in>set [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)]. finite_pattern_formed (fst x) \<and> finite_pattern_formed (snd x)"
    using i_f gf concl_f by (simp only: finite_rename_apart_def finite_rename_pattern_formed list.set ball_simps fst_conv snd_conv)
      simp
  have \<sigma>f: "\<And>x. finite_pattern_formed (?\<sigma> x)" by (rule finite_unifier_formed[OF unify Ef])
  have eqs: "finite_pattern_substitute ?\<sigma> (finite_rename_apart (q,False) i) = finite_pattern_substitute ?\<sigma> p"
      "finite_pattern_substitute ?\<sigma> (finite_rename_apart (q,True) (finite_schema_conclusion S)) = finite_pattern_substitute ?\<sigma> p"
    using finite_unify_pairs_sound[OF unify] by simp_all
  define \<beta> where "\<beta> = (\<lambda>a. ?\<sigma> ((q,True),a))"
  define \<iota> where "\<iota> = (\<lambda>a. ?\<sigma> ((q,False),a))"
  let ?st1 = "resolution_state_substitute ?\<sigma> st"
  let ?g1 = "Resolution_Call_Goal q r e (finite_pattern_substitute ?\<sigma> p)"
  let ?G = "fimage (\<lambda>(s,e',p'). Resolution_Call_Goal (q@[s]) (Some (e,c,s)) e' (finite_pattern_substitute \<beta> p'))
        (finite_schema_premises S) |\<union>|
      fimage (\<lambda>(s,M). Resolution_Material_Goal (q@[s]) (e,c,s) (finite_material_pattern_substitute \<beta> M))
        (finite_schema_materials S)"
  let ?nd = "Resolution_Node q e c S (finite_pattern_substitute ?\<sigma> p) (fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables S))"
  have I1: "resolution_pattern_invariant P d \<pi> ?st1" by (rule resolution_pattern_invariant_substitute[OF I \<sigma>f])
  have goal1: "?g1 |\<in>| resolution_pending ?st1"
    using fimageI[OF goal, of "resolution_goal_substitute ?\<sigma>"] by simp
  have iface: "finite_pattern_substitute ?\<sigma> p = finite_pattern_substitute \<iota> i"
    using eqs(1) by (simp add: finite_rename_apart_substitute \<iota>_def)
  have head: "finite_pattern_substitute ?\<sigma> p = finite_pattern_substitute \<beta> (finite_schema_conclusion S)"
    using eqs(2) by (simp add: finite_rename_apart_substitute \<beta>_def)
  have \<beta>f: "\<And>a. finite_pattern_formed (\<beta> a)" by (simp add: \<beta>_def \<sigma>f)
  have I2: "resolution_pattern_invariant P d \<pi> (Resolution_State (?G |\<union>| (resolution_pending ?st1 |-| {|?g1|}))
      (finsert ?nd (resolution_nodes ?st1)) (resolution_witnesses st'))"
    by (rule resolution_pattern_invariant_add[OF I1 goal1 clause interface iface head \<beta>f refl refl])
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_pattern_invariant_def)
  have pend: "resolution_pending st' = ?G |\<union>| (resolution_pending ?st1 |-| {|?g1|})"
    unfolding st' resolution_state_substitute_fields resolution_state.sel fimage_funion
      finite_clause_goals_substitute resolution_goal_minus_image[OF dist goal]
    by (simp add: \<beta>_def)
  have nods: "resolution_nodes st' = finsert ?nd (resolution_nodes ?st1)"
    unfolding st' resolution_state_substitute_fields resolution_state.sel
    by (simp add: finite_clause_node_substitute eqs(2) \<beta>_def)
  have "resolution_pattern_invariant P d \<pi> (Resolution_State (resolution_pending st') (resolution_nodes st') (resolution_witnesses st'))"
    using I2 by (simp only: pend nods)
  then show ?thesis by (simp only: resolution_pattern_invariant_state_fields)
qed

lemma resolution_call_step:
  assumes I: "resolution_invariant P d t st"
    and goal: "Resolution_Call_Goal q r e p |\<in>| resolution_pending st"
    and step: "st' |\<in>| finite_call_successors P st q r e p"
  shows "resolution_invariant P d t st'"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_call_step)

lemma finite_material_successors_member:
  assumes "st' |\<in>| finite_material_successors st q r M"
  obtains Ws W E u where "finite_material_resolution M = Material_Solutions Ws" "W |\<in>| Ws"
    "E |\<in>| finite_material_instance_pairs W M" "finite_unify_pairs E = Some u"
    "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
  using assms unfolding finite_material_successors_def
  by (auto simp: resolution_fset_simps split: finite_material_outcome.splits option.splits)

lemma resolution_pattern_material_step:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and step: "st' |\<in>| finite_material_successors st q r M"
  shows "resolution_pattern_invariant P d \<pi> st'"
proof -
  obtain Ws W E u where res: "finite_material_resolution M = Material_Solutions Ws" and W: "W |\<in>| Ws"
    and E: "E |\<in>| finite_material_instance_pairs W M" and unify: "finite_unify_pairs E = Some u"
    and st': "st' = resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|}) (resolution_nodes st)
        (resolution_witnesses st))"
    using step by (rule finite_material_successors_member)
  let ?\<sigma> = "finite_binding_substitution u"
  have sol: "finite_material_solution M W" using finite_material_resolution_exact[OF res] W by blast
  have "resolution_goal_formed (Resolution_Material_Goal q r M)"
    using I goal unfolding resolution_pattern_invariant_def resolution_pattern_goals_placed_def by blast
  then have Mf: "finite_material_formed M" by simp
  have Wf: "fBall W (\<lambda>(a,t). finite_term_formed t)"
    using sol by (simp add: finite_material_solution_def finite_term_bindings_formed_def)
  have Ef: "\<forall>x\<in>set E. finite_pattern_formed (fst x) \<and> finite_pattern_formed (snd x)"
    using finite_material_instance_pairs_member[OF E] Mf finite_pattern_instance_term_formed[OF Wf]
    by (auto simp: finite_material_formed_def)
  have \<sigma>f: "\<And>x. finite_pattern_formed (?\<sigma> x)" by (rule finite_unifier_formed[OF unify Ef])
  let ?st1 = "resolution_state_substitute ?\<sigma> st"
  let ?g1 = "Resolution_Material_Goal q r (finite_material_pattern_substitute ?\<sigma> M)"
  have I1: "resolution_pattern_invariant P d \<pi> ?st1" by (rule resolution_pattern_invariant_substitute[OF I \<sigma>f])
  have goal1: "?g1 |\<in>| resolution_pending ?st1"
    using fimageI[OF goal, of "resolution_goal_substitute ?\<sigma>"] by simp
  have ground: "finite_material_ground_satisfied (finite_material_pattern_substitute ?\<sigma> M)"
    by (rule finite_material_step_ground[OF sol E unify])
  have I2: "resolution_pattern_invariant P d \<pi> (Resolution_State (resolution_pending ?st1 |-| {|?g1|}) (resolution_nodes ?st1)
      (resolution_witnesses st'))"
    by (rule resolution_pattern_invariant_remove[OF I1 goal1 ground])
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_pattern_invariant_def)
  have pend: "resolution_pending st' = resolution_pending ?st1 |-| {|?g1|}"
    unfolding st' resolution_state_substitute_fields resolution_state.sel resolution_goal_minus_image[OF dist goal]
    by simp
  have nods: "resolution_nodes st' = resolution_nodes ?st1" by (simp add: st')
  have "resolution_pattern_invariant P d \<pi> (Resolution_State (resolution_pending st') (resolution_nodes st') (resolution_witnesses st'))"
    using I2 by (simp only: pend nods)
  then show ?thesis by (simp only: resolution_pattern_invariant_state_fields)
qed

lemma resolution_material_step:
  assumes I: "resolution_invariant P d t st"
    and goal: "Resolution_Material_Goal q r M |\<in>| resolution_pending st"
    and step: "st' |\<in>| finite_material_successors st q r M"
  shows "resolution_invariant P d t st'"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_material_step)

lemma resolution_pattern_goal_step:
  assumes "resolution_pattern_invariant P d \<pi> st" and "g |\<in>| resolution_pending st"
    and "st' |\<in>| finite_goal_successors P st g"
  shows "resolution_pattern_invariant P d \<pi> st'"
  using assms by (cases g) (auto intro: resolution_pattern_call_step resolution_pattern_material_step)

lemma resolution_goal_step:
  assumes "resolution_invariant P d t st" and "g |\<in>| resolution_pending st"
    and "st' |\<in>| finite_goal_successors P st g"
  shows "resolution_invariant P d t st'"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_goal_step)

text \<open>
  A witness construction is formed when every value it returns is a formed term: its values enter a
  certificate's bindings, which the checker requires formed. The empty construction is formed.
\<close>

definition finite_witness_construction_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> bool" where
  "finite_witness_construction_formed \<kappa> \<longleftrightarrow>
    (\<forall>P d S B a v. witness_value \<kappa> P d S B a = Some v \<longrightarrow> finite_term_formed v)"

lemma no_witness_construction_formed: "finite_witness_construction_formed no_witness_construction"
  by (simp add: finite_witness_construction_formed_def no_witness_construction_def)

lemma resolution_pattern_construction_step:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_pattern_invariant P d \<pi> (finite_construction_step \<kappa> P st nd)"
proof -
  let ?G = "resolution_pending st"
  have \<sigma>f: "\<And>z. finite_pattern_formed (finite_construction_substitution \<kappa> P ?G nd z)"
    using \<kappa> by (auto simp: finite_construction_substitution_def finite_registered_value_def
      finite_witness_construction_formed_def split: prod.splits option.splits)
  have "resolution_pattern_invariant P d \<pi> (Resolution_State ?G (resolution_nodes st) (resolution_witnesses st |\<union>|
      ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
          Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||})
        (finite_constructed \<kappa> P ?G nd))))"
    using I by (simp only: resolution_pattern_invariant_state_fields)
  then show ?thesis unfolding finite_construction_step_def Let_def
    by (rule resolution_pattern_invariant_substitute[OF _ \<sigma>f])
qed

lemma resolution_construction_step:
  assumes I: "resolution_invariant P d t st" and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_invariant P d t (finite_construction_step \<kappa> P st nd)"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_construction_step)

section \<open>Every successful branch keeps the invariant\<close>

lemma finite_outcome_union_fields [simp]:
  "resolution_found (finite_outcome_union Os) = ffUnion (fimage resolution_found Os)"
  "resolution_diagnoses (finite_outcome_union Os) = ffUnion (fimage resolution_diagnoses Os)"
  by (simp_all add: finite_outcome_union_def)

lemma finite_resolution_select_goals:
  "finite_resolution_select \<kappa> P st = Select_Goals G \<Longrightarrow> G |\<subseteq>| resolution_pending st"
  by (auto simp: finite_resolution_select_def finite_goal_selection_def finite_first_goals_def Let_def
    resolution_fset_simps split: if_splits)

lemma finite_resolution_pattern_search_found:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_pattern_invariant P d \<pi> st \<Longrightarrow>
    st' |\<in>| resolution_found (finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P n st) \<Longrightarrow>
    resolution_pattern_invariant P d \<pi> st' \<and> resolution_pending st'={||}"
proof (induction n arbitrary: st)
  case 0
  then show ?case by (auto simp: resolution_fset_simps split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "resolution_pending st={||}")
    case True
    with Suc.prems show ?thesis by (simp add: resolution_fset_simps)
  next
    case False
    show ?thesis
    proof (cases "finite_resolution_select \<kappa> P st")
      case (Select_Construction N)
      with Suc.prems False obtain nd where
        "st' |\<in>| resolution_found (finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P n
          (finite_construction_step \<kappa> P st nd))"
        by (auto simp: resolution_fset_simps)
      then show ?thesis using Suc.IH resolution_pattern_construction_step[OF Suc.prems(1) \<kappa>] by blast
    next
      case (Select_Goals G)
      with Suc.prems False obtain g where g: "g |\<in>| G"
        and found: "st' |\<in>| resolution_found (finite_goal_outcome
          (finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P n) P st g)"
        by (auto simp: resolution_fset_simps)
      have pending: "g |\<in>| resolution_pending st" using finite_resolution_select_goals[OF Select_Goals] g by blast
      from found obtain s where s: "s |\<in>| finite_goal_successors P st g"
        and found': "st' |\<in>| resolution_found (finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P n s)"
        by (auto simp: finite_goal_outcome_def Let_def resolution_fset_simps split: if_splits)
      then show ?thesis using Suc.IH resolution_pattern_goal_step[OF Suc.prems(1) pending s] by blast
    next
      case Select_None
      with Suc.prems False show ?thesis by (simp add: resolution_fset_simps)
    qed
  qed
qed

lemma finite_resolution_search_found:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "resolution_invariant P d t st \<Longrightarrow>
    st' |\<in>| resolution_found (finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P n st) \<Longrightarrow>
    resolution_invariant P d t st' \<and> resolution_pending st'={||}"
  using assms unfolding resolution_invariant_pattern by (rule finite_resolution_pattern_search_found)

section \<open>The certificate of a successful branch is accepted\<close>

lemma resolution_pattern_node_call_formed:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and nd: "nd |\<in>| resolution_nodes st"
  shows "finite_schema_call_formed P (resolution_node_site nd) (finite_residual_term (resolution_node_call nd))"
proof -
  have Pf: "finite_system_formed P" using I by (simp add: resolution_pattern_invariant_def)
  have callf: "finite_pattern_formed (resolution_node_call nd)" and linked: "resolution_node_linked P st nd"
    using I nd unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast+
  obtain i \<iota> where interface: "(resolution_node_site nd,i) |\<in>| finite_system_interfaces P"
    and iface: "resolution_node_call nd = finite_pattern_substitute \<iota> i"
    using linked unfolding resolution_node_linked_def by blast
  have i_f: "finite_pattern_formed i" by (rule finite_system_formed_parts(1)[OF Pf interface])
  have "finite_pattern_accepts i (finite_residual_term (resolution_node_call nd))"
    using finite_pattern_accepts_substitute[OF i_f] callf by (simp add: iface)
  then show ?thesis using Pf interface unfolding finite_schema_call_formed_def by fastforce
qed

lemma resolution_node_call_formed:
  assumes I: "resolution_invariant P d t st" and nd: "nd |\<in>| resolution_nodes st"
  shows "finite_schema_call_formed P (resolution_node_site nd) (finite_residual_term (resolution_node_call nd))"
  using assms unfolding resolution_invariant_pattern by (rule resolution_pattern_node_call_formed)

abbreviation resolution_subtree ::
    "('a,'s,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "resolution_subtree N nd \<equiv> ffilter (\<lambda>m. take (length (resolution_node_position nd)) (resolution_node_position m)=
    resolution_node_position nd) N"

lemma resolution_subtree_child:
  assumes nd: "nd |\<in>| N" and m: "resolution_node_position m=resolution_node_position nd@[s]"
  shows "fcard (resolution_subtree N m) < fcard (resolution_subtree N nd)"
proof (rule pfsubset_fcard_mono)
  have sub: "resolution_subtree N m |\<subseteq>| resolution_subtree N nd"
  proof
    fix x assume "x |\<in>| resolution_subtree N m"
    then have "x |\<in>| N" and "take (length (resolution_node_position nd)+1) (resolution_node_position x)=resolution_node_position nd@[s]"
      using m by (simp_all add: resolution_fset_simps)
    then show "x |\<in>| resolution_subtree N nd"
      by (auto simp: resolution_fset_simps dest: arg_cong[where f="take (length (resolution_node_position nd))"])
  qed
  have "nd |\<notin>| resolution_subtree N m" using m by (simp add: resolution_fset_simps)
  moreover have "nd |\<in>| resolution_subtree N nd" using nd by (simp add: resolution_fset_simps)
  ultimately show "resolution_subtree N m |\<subset>| resolution_subtree N nd" using sub by blast
qed

text \<open>
  The goals pending under a position are those whose position it prefixes. A node with none under it has a
  checked certificate: its premises are nodes and its material premises done, whatever is pending elsewhere, so
  the certificate is accepted in subtree form; a branch with no pending goal is its instance at every node.
\<close>

abbreviation resolution_pending_under ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "resolution_pending_under st q \<equiv> ffilter (\<lambda>g. take (length q) (resolution_goal_position g)=q) (resolution_pending st)"

lemma resolution_pending_under_empty:
  "resolution_pending_under st q={||} \<longleftrightarrow>
    (\<forall>g. g |\<in>| resolution_pending st \<longrightarrow> take (length q) (resolution_goal_position g)\<noteq>q)"
  by (auto simp: fset_eq_iff resolution_fset_simps)

lemma finite_node_proof_subtree_accepted:
  assumes I: "resolution_pattern_invariant P d \<pi> st"
  shows "nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_pending_under st (resolution_node_position nd)={||} \<Longrightarrow>
    fcard (resolution_subtree (resolution_nodes st) nd) \<le> k \<Longrightarrow>
    finite_checks_schema_proof P (finite_node_proof k (resolution_nodes st) nd) (resolution_node_site nd)
      (finite_residual_term (resolution_node_call nd))"
proof (induction k arbitrary: nd)
  case 0
  have mem: "nd \<in> fset (resolution_subtree (resolution_nodes st) nd)" using 0(1) by (simp add: resolution_fset_simps)
  have "0 < card (fset (resolution_subtree (resolution_nodes st) nd))"
    using mem by (metis card_gt_0_iff empty_iff finite_fset)
  then have "0 < fcard (resolution_subtree (resolution_nodes st) nd)" by (simp only: fcard.rep_eq)
  with 0(3) show ?case by linarith
next
  case (Suc k)
  let ?N = "resolution_nodes st" and ?S = "resolution_node_schema nd" and ?q = "resolution_node_position nd"
  let ?d = "resolution_node_site nd" and ?c = "resolution_node_clause nd"
  let ?t = "finite_residual_term (resolution_node_call nd)"
  have none: "take (length ?q) (resolution_goal_position g)\<noteq>?q" if "g |\<in>| resolution_pending st" for g
    using Suc.prems(2) that unfolding resolution_pending_under_empty by blast
  have Pf: "finite_system_formed P" using I by (simp add: resolution_pattern_invariant_def)
  have placed: "\<forall>a x. (a,x) |\<in>| resolution_node_bindings nd \<longrightarrow> finite_pattern_formed x"
    and linked: "resolution_node_linked P st nd"
    using I Suc.prems(1) unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast+
  have distinct: "m=m'" if "m |\<in>| ?N" "m' |\<in>| ?N" "resolution_node_position m=resolution_node_position m'" for m m'
    using I that unfolding resolution_pattern_invariant_def resolution_positions_distinct_def by blast
  have clause: "((?d,?c),?S) |\<in>| finite_system_clauses P" using linked unfolding resolution_node_linked_def by blast
  obtain \<beta> where B: "resolution_node_bindings nd = fimage (\<lambda>a. (a,\<beta> a)) (finite_schema_variables ?S)"
      and head: "resolution_node_call nd = finite_pattern_substitute \<beta> (finite_schema_conclusion ?S)"
      and prem0: "\<forall>s e p. (s,e,p) |\<in>| finite_schema_premises ?S \<longrightarrow>
        Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta> p) |\<in>| resolution_pending st \<or>
        (\<exists>m. m |\<in>| ?N \<and> resolution_node_position m=?q@[s] \<and>
          resolution_node_site m=e \<and> resolution_node_call m=finite_pattern_substitute \<beta> p)"
      and mat0: "\<forall>s M. (s,M) |\<in>| finite_schema_materials ?S \<longrightarrow>
        Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta> M) |\<in>| resolution_pending st \<or>
        resolution_material_done \<beta> M"
    using linked unfolding resolution_node_linked_def by blast
  have prem: "\<exists>m. m |\<in>| ?N \<and> resolution_node_position m=?q@[s] \<and> resolution_node_site m=e \<and>
      resolution_node_call m=finite_pattern_substitute \<beta> p" if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using prem0 that none[of "Resolution_Call_Goal (?q@[s]) (Some (?d,?c,s)) e (finite_pattern_substitute \<beta> p)"]
    by auto
  have mat: "resolution_material_done \<beta> M" if "(s,M) |\<in>| finite_schema_materials ?S" for s M
    using mat0 that none[of "Resolution_Material_Goal (?q@[s]) (?d,?c,s) (finite_material_pattern_substitute \<beta> M)"]
    by auto
  let ?V = "finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) (finite_schema_variables ?S)"
  have Sf: "finite_schema_formed ?S" by (rule finite_system_formed_parts(2)[OF Pf clause])
  have \<beta>f: "finite_pattern_formed (\<beta> a)" if "a |\<in>| finite_schema_variables ?S" for a
    using placed that by (auto simp: B resolution_fset_simps)
  have V: "finite_node_values nd = ?V"
    by (simp add: finite_node_values_def B finite_ground_bindings_def fset.map_comp comp_def)
  have Vf: "finite_term_bindings_formed (finite_schema_variables ?S) ?V"
    by (rule finite_ground_bindings_formed) (simp add: \<beta>f)
  have Vfun: "finite_relation_functional ?V" using Vf by (simp add: finite_term_bindings_formed_def)
  have unique: "x=y" if "finite_pattern_instance ?V p x" "finite_pattern_instance ?V p y" for p x y
    using finite_pattern_instance_unique[OF Vfun] that by blast
  have concl_f: "finite_pattern_formed (finite_schema_conclusion ?S)" using Sf by (simp add: finite_schema_formed_def)
  have prem_fun: "finite_relation_functional (finite_schema_premises ?S)" using Sf by (simp add: finite_schema_formed_def)
  have prem_f: "finite_pattern_formed p" if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using Sf that unfolding finite_schema_formed_def by fastforce
  have prem_v: "finite_pattern_variables p |\<subseteq>| finite_schema_variables ?S" if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using that by (force simp: finite_schema_variables_def resolution_fset_simps)
  have mat_v: "finite_material_variables M |\<subseteq>| finite_schema_variables ?S" if "(s,M) |\<in>| finite_schema_materials ?S" for s M
    using that by (force simp: finite_schema_variables_def resolution_fset_simps)
  have inst_p: "finite_pattern_instance ?V p (finite_residual_term (finite_pattern_substitute \<beta> p))"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    by (rule finite_ground_instance_residual[OF prem_f[OF that] prem_v[OF that]])
  let ?H = "finite_instantiated_premises ?S ?V"
  have Hmem: "(s,e,x) |\<in>| ?H \<longleftrightarrow> (\<exists>p. (s,e,p) |\<in>| finite_schema_premises ?S \<and> finite_pattern_instance ?V p x)" for s e x
    by (simp add: finite_instantiated_premises_member finite_pattern_instances_member)
  have Hfun: "finite_relation_functional ?H"
    unfolding finite_relation_functional_def
  proof (intro fBallI impI)
    fix x y assume x: "x |\<in>| ?H" and y: "y |\<in>| ?H" and eq: "fst x=fst y"
    obtain s e a where xs: "x=(s,e,a)" by (cases x) auto
    obtain s' e' b where ys: "y=(s',e',b)" by (cases y) auto
    obtain p where p: "(s,e,p) |\<in>| finite_schema_premises ?S" "finite_pattern_instance ?V p a" using x Hmem xs by blast
    obtain p' where p': "(s',e',p') |\<in>| finite_schema_premises ?S" "finite_pattern_instance ?V p' b" using y Hmem ys by blast
    have "(e,p)=(e',p')" using prem_fun p(1) p'(1) eq xs ys unfolding finite_relation_functional_def by fastforce
    then show "snd x=snd y" using unique p(2) p'(2) xs ys by auto
  qed
  have Hin: "(s,e,finite_residual_term (finite_pattern_substitute \<beta> p)) |\<in>| ?H"
    if "(s,e,p) |\<in>| finite_schema_premises ?S" for s e p
    using Hmem inst_p[OF that] that by blast
  have Hdom: "fimage fst ?H = fimage fst (finite_schema_premises ?S)"
    unfolding fset_eq_iff
  proof (intro allI iffI)
    fix s assume "s |\<in>| fimage fst ?H"
    then obtain x where x: "x |\<in>| ?H" "s=fst x" by (auto simp: fimage.rep_eq)
    obtain e a where "x=(s,e,a)" using x(2) by (cases x) auto
    then obtain p where "(s,e,p) |\<in>| finite_schema_premises ?S" using x(1) Hmem by blast
    then show "s |\<in>| fimage fst (finite_schema_premises ?S)" by (force simp: fimage.rep_eq)
  next
    fix s assume "s |\<in>| fimage fst (finite_schema_premises ?S)"
    then obtain x where x: "x |\<in>| finite_schema_premises ?S" "s=fst x" by (auto simp: fimage.rep_eq)
    obtain e p where "x=(s,e,p)" using x(2) by (cases x) auto
    then have "(s,e,finite_residual_term (finite_pattern_substitute \<beta> p)) |\<in>| ?H" using Hin x(1) by blast
    then show "s |\<in>| fimage fst ?H" by (force simp: fimage.rep_eq)
  qed
  have Hcover: "fBall (finite_schema_premises ?S) (\<lambda>(s,d,p). fBex ?H (\<lambda>(r,e,t). r=s \<and> e=d \<and> finite_pattern_instance ?V p t))"
  proof (rule fBallI, clarify)
    fix s d p assume sp: "(s,d,p) |\<in>| finite_schema_premises ?S"
    have "(s,d,finite_residual_term (finite_pattern_substitute \<beta> p)) |\<in>| ?H" by (rule Hin[OF sp])
    then show "fBex ?H (\<lambda>(r,e,t). r=s \<and> e=d \<and> finite_pattern_instance ?V p t)" using inst_p[OF sp] by force
  qed
  have Hprem: "finite_schema_premise_instance ?S ?V ?H"
    unfolding finite_schema_premise_instance_def using Hfun Hdom Hcover by blast
  have sat: "finite_schema_material_satisfied ?S ?V"
    unfolding finite_schema_material_satisfied_def
  proof (rule fBallI, clarify)
    fix s M assume sM: "(s,M) |\<in>| finite_schema_materials ?S"
    have fin: "resolution_material_done \<beta> M" by (rule mat[OF sM])
    have restrict: "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) ?V =
        finite_ground_bindings (\<lambda>a. finite_residual_term (\<beta> a)) (finite_material_variables M)"
      using mat_v[OF sM] by (auto simp: fset_eq_iff resolution_fset_simps)
    have "finite_material_satisfied (ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) ?V) M"
      using fin by (simp add: restrict resolution_material_done_def)
    then show "finite_material_satisfied ?V M" by (simp add: finite_material_satisfied_restrict)
  qed
  have calls: "finite_schema_call_formed P e x" if xH: "(s,e,x) |\<in>| ?H" for s e x
  proof -
    obtain p where p: "(s,e,p) |\<in>| finite_schema_premises ?S" "finite_pattern_instance ?V p x"
      using iffD1[OF Hmem xH] by blast
    obtain m where m: "m |\<in>| ?N" "resolution_node_site m=e" "resolution_node_call m=finite_pattern_substitute \<beta> p"
      using prem[OF p(1)] by blast
    have x: "x=finite_residual_term (resolution_node_call m)"
      using unique[OF p(2) inst_p[OF p(1)]] by (simp only: m(3))
    from resolution_pattern_node_call_formed[OF I m(1)] show ?thesis unfolding m(2) x .
  qed
  have admitted: "finite_admitted_schema_instance P ?d ?c ?V ?t ?H"
    unfolding finite_admitted_schema_instance_def
  proof (intro conjI)
    show "finite_schema_call_formed P ?d ?t" by (rule resolution_pattern_node_call_formed[OF I Suc.prems(1)])
    have cv: "finite_pattern_variables (finite_schema_conclusion ?S) |\<subseteq>| finite_schema_variables ?S"
      unfolding finite_schema_variables_def by (rule le_supI1) (rule sup_ge1)
    have ci: "finite_pattern_instance ?V (finite_schema_conclusion ?S) ?t"
      unfolding head by (rule finite_ground_instance_residual[OF concl_f cv])
    have "finite_schema_instance ?S ?V ?t ?H"
      unfolding finite_schema_instance_def using Sf Vf ci Hprem by blast
    then show "fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=?d \<and> k=?c \<and>
        finite_schema_instance S ?V ?t ?H \<and> finite_schema_material_satisfied S ?V)"
      using clause sat by fastforce
    show "fBall ?H (\<lambda>(s,e,x). finite_schema_call_formed P e x)" using calls by fastforce
  qed
  have reading: "?H |\<in>| finite_admitted_premise_readings P ?d ?c ?V ?t"
    by (simp add: finite_admitted_premise_reading_exact admitted)
  let ?B = "ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,finite_node_proof k ?N m))
      (ffilter (\<lambda>m. resolution_node_position m=?q@[s]) ?N)) (finite_schema_premises ?S))"
  have Bmem: "(s,pf) |\<in>| ?B \<longleftrightarrow> (\<exists>e p m. (s,e,p) |\<in>| finite_schema_premises ?S \<and> m |\<in>| ?N \<and>
      resolution_node_position m=?q@[s] \<and> pf=finite_node_proof k ?N m)" for s pf
  proof
    assume "(s,pf) |\<in>| ?B"
    then show "\<exists>e p m. (s,e,p) |\<in>| finite_schema_premises ?S \<and> m |\<in>| ?N \<and>
        resolution_node_position m=?q@[s] \<and> pf=finite_node_proof k ?N m"
      by (auto simp: resolution_fset_simps)
  next
    assume "\<exists>e p m. (s,e,p) |\<in>| finite_schema_premises ?S \<and> m |\<in>| ?N \<and>
        resolution_node_position m=?q@[s] \<and> pf=finite_node_proof k ?N m"
    then obtain e p m where w: "(s,e,p) |\<in>| finite_schema_premises ?S" "m |\<in>| ?N"
        "resolution_node_position m=?q@[s]" "pf=finite_node_proof k ?N m" by blast
    show "(s,pf) |\<in>| ?B"
      unfolding ffUnion.rep_eq fimage.rep_eq image_image
      by (rule UN_I[of "(s,e,p)"]) (use w in \<open>auto simp: resolution_fset_simps\<close>)
  qed
  have Bfun: "finite_relation_functional ?B"
    unfolding finite_relation_functional_def
  proof (intro fBallI impI)
    fix x y assume x: "x |\<in>| ?B" and y: "y |\<in>| ?B" and eq: "fst x=fst y"
    obtain s pf where xs: "x=(s,pf)" by (cases x)
    obtain s' pf' where ys: "y=(s',pf')" by (cases y)
    from x have xB: "(s,pf) |\<in>| ?B" by (simp only: xs)
    from y have yB: "(s',pf') |\<in>| ?B" by (simp only: ys)
    obtain m where m: "m |\<in>| ?N" "resolution_node_position m=?q@[s]" "pf=finite_node_proof k ?N m"
      using iffD1[OF Bmem xB] by blast
    obtain m' where m': "m' |\<in>| ?N" "resolution_node_position m'=?q@[s']" "pf'=finite_node_proof k ?N m'"
      using iffD1[OF Bmem yB] by blast
    have "m=m'" using distinct[OF m(1) m'(1)] m(2) m'(2) eq xs ys by simp
    then show "snd x=snd y" using m(3) m'(3) xs ys by simp
  qed
  have Bdom: "fimage fst ?B = fimage fst ?H"
    unfolding Hdom fset_eq_iff
  proof (intro allI iffI)
    fix s assume "s |\<in>| fimage fst ?B"
    then obtain x where x: "x |\<in>| ?B" "s=fst x" by (auto simp: fimage.rep_eq)
    obtain pf where "x=(s,pf)" using x(2) by (cases x) auto
    then have xB: "(s,pf) |\<in>| ?B" using x(1) by (simp only:)
    obtain e p where "(s,e,p) |\<in>| finite_schema_premises ?S" using iffD1[OF Bmem xB] by blast
    then show "s |\<in>| fimage fst (finite_schema_premises ?S)" by (force simp: fimage.rep_eq)
  next
    fix s assume "s |\<in>| fimage fst (finite_schema_premises ?S)"
    then obtain x where x: "x |\<in>| finite_schema_premises ?S" "s=fst x" by (auto simp: fimage.rep_eq)
    obtain e p where sp: "x=(s,e,p)" using x(2) by (cases x) auto
    have xp: "(s,e,p) |\<in>| finite_schema_premises ?S" using x(1) sp by (simp only:)
    obtain m where m: "m |\<in>| ?N" "resolution_node_position m=?q@[s]" using prem[OF xp] by blast
    have "(s,finite_node_proof k ?N m) |\<in>| ?B" by (rule iffD2[OF Bmem]) (use xp m in blast)
    then show "s |\<in>| fimage fst ?B" by (force simp: fimage.rep_eq)
  qed
  have children: "\<exists>e x. (s,e,x) |\<in>| ?H \<and> finite_checks_schema_proof P pf e x" if sB: "(s,pf) |\<in>| ?B" for s pf
  proof -
    obtain e p m where p: "(s,e,p) |\<in>| finite_schema_premises ?S" and m: "m |\<in>| ?N"
      "resolution_node_position m=?q@[s]" "pf=finite_node_proof k ?N m"
      using iffD1[OF Bmem sB] by blast
    obtain m' where m': "m' |\<in>| ?N" "resolution_node_position m'=?q@[s]" "resolution_node_site m'=e"
        "resolution_node_call m'=finite_pattern_substitute \<beta> p"
      using prem[OF p] by blast
    have same: "m'=m" using distinct[OF m'(1) m(1)] m'(2) m(2) by simp
    have under: "resolution_pending_under st (resolution_node_position m)={||}"
      unfolding resolution_pending_under_empty m(2)
    proof (intro allI impI)
      fix g assume g: "g |\<in>| resolution_pending st"
      show "take (length (?q@[s])) (resolution_goal_position g)\<noteq>?q@[s]"
      proof
        assume at: "take (length (?q@[s])) (resolution_goal_position g)=?q@[s]"
        have "take (length ?q) (take (length (?q@[s])) (resolution_goal_position g))=?q" unfolding at by simp
        then have "take (length ?q) (resolution_goal_position g)=?q" by simp
        with none[OF g] show False by blast
      qed
    qed
    have depth: "fcard (resolution_subtree ?N m) \<le> k"
      using resolution_subtree_child[OF Suc.prems(1) m(2)] Suc.prems(3) by simp
    have sm: "resolution_node_site m=e" using m'(3) same by (simp only:)
    have cm: "resolution_node_call m=finite_pattern_substitute \<beta> p" using m'(4) same by (simp only:)
    have "finite_checks_schema_proof P pf e (finite_residual_term (resolution_node_call m))"
      using Suc.IH[OF m(1) under depth] unfolding m(3) sm .
    moreover have "(s,e,finite_residual_term (resolution_node_call m)) |\<in>| ?H"
      unfolding cm by (rule Hin[OF p])
    ultimately show ?thesis by blast
  qed
  have "finite_checks_schema_proof P (Schema_Proof ?c ?V ?B) ?d ?t"
    unfolding finite_checks_schema_proof_node
    using Bfun reading Bdom children by blast
  then show ?case by (simp add: V)
qed

lemma finite_node_proof_pattern_accepted:
  assumes I: "resolution_pattern_invariant P d \<pi> st" and closed: "resolution_pending st={||}"
  shows "nd |\<in>| resolution_nodes st \<Longrightarrow> fcard (resolution_subtree (resolution_nodes st) nd) \<le> k \<Longrightarrow>
    finite_checks_schema_proof P (finite_node_proof k (resolution_nodes st) nd) (resolution_node_site nd)
      (finite_residual_term (resolution_node_call nd))"
  by (rule finite_node_proof_subtree_accepted[OF I]) (simp_all add: closed fset_eq_iff resolution_fset_simps)

lemma finite_node_proof_accepted:
  assumes I: "resolution_invariant P d t st" and closed: "resolution_pending st={||}"
  shows "nd |\<in>| resolution_nodes st \<Longrightarrow> fcard (resolution_subtree (resolution_nodes st) nd) \<le> k \<Longrightarrow>
    finite_checks_schema_proof P (finite_node_proof k (resolution_nodes st) nd) (resolution_node_site nd)
      (finite_residual_term (resolution_node_call nd))"
  using assms unfolding resolution_invariant_pattern by (rule finite_node_proof_pattern_accepted)

text \<open>
  Every certificate a closed branch from a pattern goal gives is accepted at its root call's ground instance, the
  residual of the root node's call, which is an instance of the pattern.
\<close>

theorem finite_resolution_pattern_certificates_accepted:
  assumes Pf: "finite_system_formed P" and \<pi>f: "finite_pattern_formed \<pi>"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and found: "st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d \<pi>))"
    and cert: "c |\<in>| finite_state_proofs st"
  shows "\<exists>nd \<rho>. nd |\<in>| resolution_nodes st \<and> resolution_node_position nd=[] \<and> resolution_node_site nd=d \<and>
    resolution_node_call nd=finite_pattern_substitute \<rho> \<pi> \<and>
    c=finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st) nd \<and>
    finite_checks_schema_proof P c d (finite_residual_term (resolution_node_call nd))"
proof -
  have "resolution_pattern_invariant P d \<pi> st \<and> resolution_pending st={||}"
    using finite_resolution_pattern_search_found[OF \<kappa> resolution_pattern_initial_invariant[OF Pf \<pi>f]] found
    by (simp add: finite_resolution_search_def)
  then have I: "resolution_pattern_invariant P d \<pi> st" and closed: "resolution_pending st={||}" by blast+
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd=[]"
    and c: "c=finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st) nd"
    using cert by (auto simp: finite_state_proofs_def resolution_fset_simps)
  obtain \<rho> where site: "resolution_node_site nd=d" and call: "resolution_node_call nd=finite_pattern_substitute \<rho> \<pi>"
    using I nd unfolding resolution_pattern_invariant_def resolution_pattern_nodes_placed_def by blast
  have "fcard (resolution_subtree (resolution_nodes st) nd) \<le> fcard (resolution_nodes st)"
    by (rule fcard_mono) auto
  from finite_node_proof_pattern_accepted[OF I closed nd(1) this]
  have "finite_checks_schema_proof P c d (finite_residual_term (resolution_node_call nd))"
    by (simp only: c site)
  then show ?thesis using nd c site call by blast
qed

theorem finite_resolution_certificates_accepted:
  assumes Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and found: "st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_initial_state d t))"
    and cert: "p |\<in>| finite_state_proofs st"
  shows "finite_checks_schema_proof P p d t"
proof -
  have \<pi>f: "finite_pattern_formed (finite_exact_term_pattern t)" using tf by simp
  have found': "st |\<in>| resolution_found (finite_resolution_search \<kappa> P n (finite_pattern_state d (finite_exact_term_pattern t)))"
    using found by (simp only: finite_initial_pattern_state)
  show ?thesis
    using finite_resolution_pattern_certificates_accepted[OF Pf \<pi>f \<kappa> found' cert]
    by (auto simp: finite_exact_term_pattern_substitute)
qed

lemma finite_resolution_search_refuses_nothing:
  "Resolution_Refused p |\<notin>| resolution_diagnoses (finite_resolution_search_by sel \<kappa> P n st)"
  by (induction n arbitrary: st) (auto simp: finite_goal_outcome_def finite_unconstructed_def Let_def
    resolution_fset_simps split: resolution_selection.splits if_splits)

text \<open>
  At a formed program, a formed call and a formed construction, the resolver keeps every certificate its
  successful branches give: it resolves exactly when a branch succeeds, with all of their certificates,
  and its diagnosis never holds a refused certificate.
\<close>

theorem finite_program_resolution_certificates:
  assumes Pf: "finite_system_formed P" and tf: "finite_term_formed t"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
  shows "finite_program_resolution \<kappa> P d t n = (let R = finite_resolution_search \<kappa> P n (finite_initial_state d t);
      C = ffUnion (fimage finite_state_proofs (resolution_found R)) in
    if C\<noteq>{||} then Finite_Resolved C else if resolution_diagnoses R={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R))"
proof -
  let ?R = "finite_resolution_search \<kappa> P n (finite_initial_state d t)"
  let ?C = "ffUnion (fimage finite_state_proofs (resolution_found ?R))"
  have all: "ffilter (\<lambda>p. finite_checks_schema_proof P p d t) ?C = ?C"
    using finite_resolution_certificates_accepted[OF Pf tf \<kappa>] by (auto simp: fset_eq_iff resolution_fset_simps)
  show ?thesis by (auto simp: finite_program_resolution_def Let_def all)
qed

corollary finite_program_resolution_no_refused:
  assumes "finite_system_formed P" and "finite_term_formed t" and "finite_witness_construction_formed \<kappa>"
    and "finite_program_resolution \<kappa> P d t n = Finite_Unresolved D"
  shows "Resolution_Refused p |\<notin>| D"
  using assms finite_resolution_search_refuses_nothing[of p "finite_resolution_select \<kappa> P" \<kappa> P n]
  by (auto simp: finite_program_resolution_certificates finite_resolution_search_def Let_def split: if_splits)

end
