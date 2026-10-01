theory Factor_Deferred_Commitments
  imports Factor_Deferred_Search Factor_Access_Commitments
begin

section \<open>R5's committed search over the deferred search\<close>

text \<open>
  D1d (DECISIONS.md, task 495's entry, its addition "The step at the given's depth"). F2c's committed search reads a
  committed representation (@{text committed_representation_structure}); here the deferred search (D1b) writes it: its
  node positions are the inner node tree's keys, a call's successors at the focus its clause alternatives through the
  deferred bind (@{const search_call_successors_with}, no solved call reused), a committed material premise's its
  solutions' through the same bind, and a production's substitution through the deferred bind too.

  A deferred state keeps every variable at a node's position or at the root of a call goal there
  (@{const deferred_parts_formed}), so a substitution binding a variable where no node stands, or introducing one, has
  no deferred state projecting to its result: the structure asks the substitution at every map identical outside a
  set. The committed representation's states are therefore the deferred search or, where a substitution or a state
  shared again leaves that premise, the shared search (F2c's @{const shared_committed_representation}), which writes
  every operation as it does. A substitution is bound in the deferred state exactly when every variable it moves is a
  goal's, at a node's position, and its images' variables are goals' at a node's position outside its domain; a state
  shared again is deferred exactly when its variables are rooted (@{const search_variables_rooted}). Both are tested
  where the state is written, never on a formed state again.
\<close>

fun committed_inner :: "('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "committed_inner (Inl d) = deferred_inner d"
| "committed_inner (Inr r) = r"

fun deferred_committed_project ::
    "('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "deferred_committed_project (Inl d) = deferred_project d"
| "deferred_committed_project (Inr r) = search_project r"

fun deferred_committed_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search \<Rightarrow> bool" where
  "deferred_committed_formed \<kappa> P (Inl d) \<longleftrightarrow> deferred_formed \<kappa> P d \<and> search_placeable (deferred_project d)"
| "deferred_committed_formed \<kappa> P (Inr r) \<longleftrightarrow>
    (search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r"

definition deferred_committed_of :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_committed_of P st = (if search_variables_rooted st then Inl (deferred_of P st) else Inr (search_of P st))"

lemma deferred_committed_of:
  assumes pl: "search_placeable st"
  shows "deferred_committed_formed \<kappa> P (deferred_committed_of P st)"
    and "deferred_committed_project (deferred_committed_of P st) = st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have "deferred_committed_formed \<kappa> P (deferred_committed_of P st) \<and> deferred_committed_project (deferred_committed_of P st) = st"
  proof (cases "search_variables_rooted st")
    case True
    then show ?thesis using deferred_of_rooted(1,2)[OF d True] pl by (simp add: deferred_committed_of_def)
  next
    case False
    then show ?thesis using search_of[OF d] search_of_classes[OF d] pl
      by (simp add: deferred_committed_of_def)
  qed
  then show "deferred_committed_formed \<kappa> P (deferred_committed_of P st)"
    and "deferred_committed_project (deferred_committed_of P st) = st" by blast+
qed

subsection \<open>A substitution through the deferred bind\<close>

text \<open>
  The goals' variables, listed by the goals' structure: a variable a substitution moves is bound in the deferred state
  only where a goal holds it (no order of the names is read).
\<close>

definition deferred_goal_variables :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('s,'a) resolution_variable list" where
  "deferred_goal_variables d = concat (map (\<lambda>z. shared_goal_variable_list (shared_entry_goal (snd z)))
    (RBT.entries (shared_goals (search_state (deferred_inner d)))))"

lemma deferred_goal_variables_unbound:
  assumes d: "deferred_formed \<kappa> P d" and x: "x \<in> set (deferred_goal_variables d)"
  shows "binding_map (deferred_store d) x = None"
proof -
  let ?s = "search_state (deferred_inner d)"
  obtain q h where e: "(q,h) \<in> set (RBT.entries (shared_goals ?s))"
    and xh: "x \<in> set (shared_goal_variable_list (shared_entry_goal h))"
    using x by (auto simp: deferred_goal_variables_def)
  have at: "RBT.lookup (shared_goals ?s) q = Some h" using e by (simp add: RBT.lookup_in_tree)
  have st: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF deferred_formedD(1)[OF d]] .
  have gf: "shared_goal_formed (search_table (deferred_inner d)) (shared_entry_goal h)"
    using shared_entries_formed(1)[OF st at] by (simp add: goal_entry_formed_def)
  have "x |\<in>| shared_goal_variables (shared_entry_goal h)" using shared_goal_variable_list[OF gf] xh by simp
  then show ?thesis by (rule deferred_formedD(7)[OF d at])
qed

definition deferred_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_substitute P \<sigma> D d = (let G = deferred_goal_variables d;
      L = remdups (filter (\<lambda>a. a |\<in>| D \<and> \<sigma> a \<noteq> Finite_Variable a) G);
      at = (\<lambda>x. RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None) in
    if fBall D (\<lambda>a. \<sigma> a = Finite_Variable a \<or> a \<in> set G) \<and>
      list_all (\<lambda>a. at a \<and> fBall (finite_pattern_variables (\<sigma> a)) (\<lambda>b. b \<notin> set L \<and> b \<in> set G \<and> at b)) L
    then Inl (let r1 = search_reshare (plain_grounds \<sigma> D) (deferred_inner d) in
      deferred_bind P (map (\<lambda>a. (a, keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> a))) L)
        (d\<lparr>deferred_inner := r1\<rparr>))
    else deferred_committed_of P (resolution_state_substitute \<sigma> (deferred_project d)))"

theorem deferred_substitute:
  fixes d :: "('a,'s::linorder,'d,'c) deferred_search"
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a"
  shows "deferred_committed_formed \<kappa> P (deferred_substitute P \<sigma> D d)"
    and "deferred_committed_project (deferred_substitute P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d)"
proof -
  let ?r = "deferred_inner d" let ?S = "deferred_store d" let ?G = "deferred_goal_variables d"
  let ?at = "\<lambda>x. RBT.lookup (shared_nodes (search_state ?r)) (fst (fst x)) \<noteq> None"
  define L where "L = remdups (filter (\<lambda>a. a |\<in>| D \<and> \<sigma> a \<noteq> Finite_Variable a) ?G)"
  define ok where "ok \<longleftrightarrow> fBall D (\<lambda>a. \<sigma> a = Finite_Variable a \<or> a \<in> set ?G) \<and>
    list_all (\<lambda>a. ?at a \<and> fBall (finite_pattern_variables (\<sigma> a)) (\<lambda>b. b \<notin> set L \<and> b \<in> set ?G \<and> ?at b)) L"
  define r1 where "r1 = search_reshare (plain_grounds \<sigma> D) ?r"
  define s where "s = map (\<lambda>a. (a, keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> a))) L"
  let ?db = "d\<lparr>deferred_inner := r1\<rparr>"
  have eq: "deferred_substitute P \<sigma> D d = (if ok then Inl (deferred_bind P s ?db)
      else deferred_committed_of P (resolution_state_substitute \<sigma> (deferred_project d)))"
    by (simp only: deferred_substitute_def Let_def L_def ok_def r1_def s_def)
  have pls: "search_placeable (resolution_state_substitute \<sigma> (deferred_project d))" by (rule search_placeable_substitute[OF pl])
  have both: "deferred_committed_formed \<kappa> P (deferred_substitute P \<sigma> D d) \<and>
      deferred_committed_project (deferred_substitute P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d)"
  proof (cases ok)
    case False
    then show ?thesis using deferred_committed_of(1)[OF pls, of \<kappa> P] deferred_committed_of(2)[OF pls, of P] eq by simp
  next
    case True
    note okT = True
    have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
    note R1 = deferred_reshare[where G = "plain_grounds \<sigma> D", OF d]
    have d1: "deferred_formed \<kappa> P ?db" using R1(1) by (simp add: r1_def)
    have p1: "deferred_project ?db = deferred_project d" using R1(2) by (simp add: r1_def)
    have s1: "shared_state_formed \<kappa> P (search_state r1)" unfolding r1_def using search_formedD(1)[OF search_reshare(1)[OF r]] .
    have x1: "share_state_formed (shared_sharing (search_state r1))" using shared_entries_formed(3)[OF s1] .
    have rep: "keyed_state_represents (shared_sharing (search_state r1)) (search_table r1)"
      and tf1: "table_formed (search_table r1)" using share_state_formed_table[OF x1] by simp_all
    have held: "table_holds (search_table r1) t" if "t |\<in>| pattern_grounds (\<sigma> z)" "z |\<in>| D" for z t
      unfolding r1_def by (rule search_reshare(4)[OF r], rule plain_grounds_member[where \<tau> = \<sigma>, OF that])
    have ex: "shared_pattern_formed (search_table r1) (keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> z)) \<and>
        shared_pattern_project (search_table r1) (keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> z)) = \<sigma> z"
      if "z |\<in>| D" for z
      using keyed_pattern_at_exact[OF rep tf1] held[OF _ that] by blast
    have LD: "z |\<in>| D \<and> \<sigma> z \<noteq> Finite_Variable z \<and> z \<in> set ?G" if "z \<in> set L" for z using that by (simp add: L_def)
    have exL: "shared_pattern_project (search_table r1) (keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> z)) = \<sigma> z"
      if "z \<in> set L" for z using ex LD[OF that] by blast
    have keys: "set (map fst s) = set L" by (simp add: s_def comp_def)
    have sf: "shared_bindings_formed (search_table (deferred_inner ?db)) s"
      using ex LD by (auto simp: s_def shared_bindings_formed_def)
    have ps: "shared_bindings_project (search_table r1) s = map (\<lambda>z. (z, \<sigma> z)) L"
      unfolding s_def shared_bindings_project_def by (simp add: map_eq_conv exL)
    have ok1: "?at a \<and> fBall (finite_pattern_variables (\<sigma> a)) (\<lambda>b. b \<notin> set L \<and> b \<in> set ?G \<and> ?at b)"
      if "a \<in> set L" for a using okT that by (simp add: ok_def list_all_iff)
    have nodes1: "RBT.lookup (shared_nodes (search_state r1)) q = RBT.lookup (shared_nodes (search_state ?r)) q" for q
      using search_reshare(6)[OF r, of "plain_grounds \<sigma> D"] by (simp add: r1_def)
    have ub: "binding_map ?S x = None" if "x \<in> set ?G" for x by (rule deferred_goal_variables_unbound[OF d that])
    have dom: "\<forall>a. a \<in> set (map fst s) \<longrightarrow> binding_map (deferred_store ?db) a = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst a)) \<noteq> None"
      using ub ok1 LD keys nodes1 by simp
    have fbL: "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a = \<sigma> a"
      if "a \<in> set L" for a using that by (simp add: ps finite_binding_substitution_def map_of_map_restrict)
    have img: "\<forall>a b. a \<in> set (map fst s) \<longrightarrow>
        b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a) \<longrightarrow>
        b \<notin> set (map fst s) \<and> binding_map (deferred_store ?db) b = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst b)) \<noteq> None"
    proof (intro allI impI)
      fix a b assume a: "a \<in> set (map fst s)"
        and b: "b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a)"
      have aL: "a \<in> set L" using a keys by simp
      have "b |\<in>| finite_pattern_variables (\<sigma> a)" using b fbL[OF aL] by simp
      then have "b \<notin> set L \<and> b \<in> set ?G \<and> ?at b" using ok1[OF aL] by blast
      then show "b \<notin> set (map fst s) \<and> binding_map (deferred_store ?db) b = None \<and>
          RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst b)) \<noteq> None"
        using ub keys nodes1 by simp
    qed
    note B = deferred_bind[OF d1 sf dom img]
    have fb: "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) = \<sigma>"
    proof (rule ext)
      fix z
      show "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) z = \<sigma> z"
      proof (cases "z \<in> set L")
        case True
        then show ?thesis by (rule fbL)
      next
        case False
        have "\<sigma> z = Finite_Variable z"
        proof (cases "z |\<in>| D")
          case True
          have "\<sigma> z = Finite_Variable z \<or> z \<in> set ?G" using okT True by (simp add: ok_def)
          then show ?thesis using False True by (auto simp: L_def)
        next
          case False
          then show ?thesis by (rule out)
        qed
        then show ?thesis using False by (simp add: ps finite_binding_substitution_def map_of_map_restrict)
      qed
    qed
    have pr: "deferred_project (deferred_bind P s ?db) = resolution_state_substitute \<sigma> (deferred_project d)"
      using B(2) fb p1 by simp
    show ?thesis using B(1) pr pls eq okT by simp
  qed
  then show "deferred_committed_formed \<kappa> P (deferred_substitute P \<sigma> D d)"
    and "deferred_committed_project (deferred_substitute P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d)"
    by blast+
qed

subsection \<open>The committed successors through the deferred bind\<close>

definition deferred_call_successors :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) deferred_search fset" where
  "deferred_call_successors P d h = (case shared_entry_goal h of
      Shared_Call_Goal q rr e gp \<Rightarrow>
        search_call_successors_with (\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)) P (deferred_inner d) q e gp
    | Shared_Material_Goal q rr gM \<Rightarrow> {||})"

definition deferred_solution_successors :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow>
    ('a,'s,'d,'c) deferred_search fset" where
  "deferred_solution_successors P d h Ws = (case shared_entry_goal h of
      Shared_Material_Goal q rr gM \<Rightarrow> search_solution_successors_with (\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)) P
        (deferred_inner d) q gM (shared_material_project (search_table (deferred_inner d)) gM) Ws
    | Shared_Call_Goal q rr e gp \<Rightarrow> {||})"

subsection \<open>The committed representation\<close>

definition deferred_committed_representation :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry,
      ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) committed_representation" where
  "deferred_committed_representation \<kappa> P = \<lparr>
    rep_access = (\<lambda>s. case s of Inl d \<Rightarrow> deferred_access \<kappa> P d | Inr r \<Rightarrow> rep_access (shared_committed_representation \<kappa> P) r),
    rep_empty = (\<lambda>s. RBT.is_empty (shared_goals (search_state (committed_inner s)))),
    rep_project = deferred_committed_project,
    rep_refresh = (\<lambda>s. case s of Inl d \<Rightarrow> Inl d | Inr r \<Rightarrow> Inr (rep_refresh (shared_committed_representation \<kappa> P) r)),
    rep_construct = (\<lambda>s m. case s of Inl d \<Rightarrow> Inl (deferred_construct \<kappa> P d m)
      | Inr r \<Rightarrow> Inr (rep_construct (shared_committed_representation \<kappa> P) r m)),
    rep_successors = (\<lambda>s h. case s of Inl d \<Rightarrow> fimage Inl (deferred_successors \<kappa> P d h)
      | Inr r \<Rightarrow> fimage Inr (rep_successors (shared_committed_representation \<kappa> P) r h)),
    rep_node_positions = (\<lambda>s. fset_of_list (RBT.keys (shared_nodes (search_state (committed_inner s))))),
    rep_call_successors = (\<lambda>s h. case s of Inl d \<Rightarrow> fimage Inl (deferred_call_successors P d h)
      | Inr r \<Rightarrow> fimage Inr (rep_call_successors (shared_committed_representation \<kappa> P) r h)),
    rep_solution_successors = (\<lambda>s h Ws. case s of Inl d \<Rightarrow> fimage Inl (deferred_solution_successors P d h Ws)
      | Inr r \<Rightarrow> fimage Inr (rep_solution_successors (shared_committed_representation \<kappa> P) r h Ws)),
    rep_substitute = (\<lambda>s \<sigma> D. case s of Inl d \<Rightarrow> deferred_substitute P \<sigma> D d
      | Inr r \<Rightarrow> Inr (rep_substitute (shared_committed_representation \<kappa> P) r \<sigma> D)),
    rep_share = deferred_committed_of P\<rparr>"

lemma deferred_committed_fields:
  "rep_access (deferred_committed_representation \<kappa> P) (Inl d) = deferred_access \<kappa> P d"
  "rep_access (deferred_committed_representation \<kappa> P) (Inr r) = rep_access (shared_committed_representation \<kappa> P) r"
  "rep_project (deferred_committed_representation \<kappa> P) = deferred_committed_project"
  "rep_refresh (deferred_committed_representation \<kappa> P) (Inl d) = Inl d"
  "rep_refresh (deferred_committed_representation \<kappa> P) (Inr r) = Inr (rep_refresh (shared_committed_representation \<kappa> P) r)"
  "rep_construct (deferred_committed_representation \<kappa> P) (Inl d) m = Inl (deferred_construct \<kappa> P d m)"
  "rep_construct (deferred_committed_representation \<kappa> P) (Inr r) m = Inr (rep_construct (shared_committed_representation \<kappa> P) r m)"
  "rep_successors (deferred_committed_representation \<kappa> P) (Inl d) h = fimage Inl (deferred_successors \<kappa> P d h)"
  "rep_successors (deferred_committed_representation \<kappa> P) (Inr r) h =
    fimage Inr (rep_successors (shared_committed_representation \<kappa> P) r h)"
  "rep_node_positions (deferred_committed_representation \<kappa> P) s =
    fset_of_list (RBT.keys (shared_nodes (search_state (committed_inner s))))"
  "rep_call_successors (deferred_committed_representation \<kappa> P) (Inl d) h = fimage Inl (deferred_call_successors P d h)"
  "rep_call_successors (deferred_committed_representation \<kappa> P) (Inr r) h =
    fimage Inr (rep_call_successors (shared_committed_representation \<kappa> P) r h)"
  "rep_solution_successors (deferred_committed_representation \<kappa> P) (Inl d) h Ws =
    fimage Inl (deferred_solution_successors P d h Ws)"
  "rep_solution_successors (deferred_committed_representation \<kappa> P) (Inr r) h Ws =
    fimage Inr (rep_solution_successors (shared_committed_representation \<kappa> P) r h Ws)"
  "rep_substitute (deferred_committed_representation \<kappa> P) (Inl d) \<sigma> D = deferred_substitute P \<sigma> D d"
  "rep_substitute (deferred_committed_representation \<kappa> P) (Inr r) \<sigma> D =
    Inr (rep_substitute (shared_committed_representation \<kappa> P) r \<sigma> D)"
  "rep_share (deferred_committed_representation \<kappa> P) = deferred_committed_of P"
  by (simp_all add: deferred_committed_representation_def)

lemma deferred_committed_images:
  "fimage deferred_committed_project (fimage Inl X) = fimage deferred_project X"
  "fimage deferred_committed_project (fimage Inr Y) = fimage search_project Y"
  by (simp_all add: fset.map_comp comp_def)

lemma deferred_committed_formed_images:
  "(\<forall>s'. s' |\<in>| fimage Inl X \<longrightarrow> deferred_committed_formed \<kappa> P s') \<longleftrightarrow>
    (\<forall>d. d |\<in>| X \<longrightarrow> deferred_committed_formed \<kappa> P (Inl d))"
  "(\<forall>s'. s' |\<in>| fimage Inr Y \<longrightarrow> deferred_committed_formed \<kappa> P s') \<longleftrightarrow>
    (\<forall>r. r |\<in>| Y \<longrightarrow> deferred_committed_formed \<kappa> P (Inr r))"
  by (blast intro: fimageI elim: fimageE)+

theorem deferred_committed_structure:
  assumes sock: "clause_sockets_distinct P"
  shows "committed_representation_structure (deferred_committed_representation \<kappa> P) (deferred_committed_formed \<kappa> P) \<kappa> P"
proof -
  let ?S = "shared_committed_representation \<kappa> P" and ?R = "deferred_committed_representation \<kappa> P"
  interpret b: committed_representation_structure ?S
      "\<lambda>r. (search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" \<kappa> P
    by (rule shared_kept_structure[OF shared_committed_structure[OF sock] sock]) simp
  have pj: "rep_project ?S = search_project" by (simp add: shared_committed_representation_def fun_eq_iff)
  have ac: "rep_access ?S = shared_access \<kappa> P" by (simp add: shared_committed_representation_def)
  show ?thesis
  proof (rule committed_representation_structure.intro, goal_cases)
    case (1 s)
    show ?case
    proof (cases s)
      case (Inl d)
      then show ?thesis using 1 deferred_access_formed[of \<kappa> P d] by (simp add: deferred_committed_fields)
    next
      case (Inr r)
      then show ?thesis using 1 b.access[of r] by (simp add: deferred_committed_fields pj)
    qed
  next
    case (2 s)
    show ?case
    proof (cases s)
      case (Inl d)
      then show ?thesis using 2 by (simp add: deferred_committed_fields)
    next
      case (Inr r)
      then show ?thesis using 2 b.refresh[of r] by (simp add: deferred_committed_fields pj)
    qed
  next
    case (3 s m q)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" using 3(1) Inl by simp_all
      have n: "m |\<in>| access_nodes_at (deferred_access \<kappa> P d) q"
        using 3(2) Inl by (simp add: deferred_committed_fields)
      show ?thesis using deferred_construct[OF f n] Inl by (simp add: deferred_committed_fields)
    next
      case (Inr r)
      then show ?thesis using 3 b.construct[of r m q] by (simp add: deferred_committed_fields pj, metis)
    qed
  next
    case (4 s h)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" using 4(1) Inl by simp_all
      have h: "h |\<in>| access_goals (deferred_access \<kappa> P d)" using 4(2) Inl by (simp add: deferred_committed_fields)
      note c = deferred_successors[OF f sock h]
      show ?thesis unfolding Inl deferred_committed_fields deferred_committed_project.simps deferred_committed_images
        deferred_committed_formed_images deferred_committed_formed.simps using c by blast
    next
      case (Inr r)
      have f: "(search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" using 4(1) Inr by simp
      have h: "h |\<in>| access_goals (rep_access ?S r)" using 4(2) Inr by (simp only: deferred_committed_fields)
      note c = b.successors[OF f h, unfolded pj]
      show ?thesis unfolding Inr deferred_committed_fields deferred_committed_project.simps deferred_committed_images
        deferred_committed_formed_images deferred_committed_formed.simps using c by blast
    qed
  next
    case (5 s h q rr e p)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" using 5(1) Inl by simp_all
      let ?r = "deferred_inner d"
      have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF f(1)] .
      have h: "h |\<in>| access_goals (shared_access \<kappa> P ?r)"
        using 5(2) Inl by (simp add: deferred_committed_fields deferred_access_def)
      have g: "shared_goal_project (search_table ?r) (shared_entry_goal h) = Resolution_Call_Goal q rr e p"
        using 5(3) Inl by (simp add: deferred_committed_fields deferred_access_def shared_access_simps)
      have atq: "RBT.lookup (shared_goals (search_state ?r)) q = Some h" using shared_goal_at[OF r h g] by simp
      obtain gp where eg: "shared_entry_goal h = Shared_Call_Goal q rr e gp"
        and pp: "shared_pattern_project (search_table ?r) gp = p" using g by (cases "shared_entry_goal h") auto
      let ?rz = "search_reshare (search_call_grounds P q e) ?r"
      let ?\<beta> = "\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)"
      have step: "\<And>i c S \<sigma>. (i,c,S,\<sigma>) |\<in>| shared_call_alternatives P (shared_sharing (search_state ?rz)) q e gp \<Longrightarrow>
          ((e,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> shared_bindings_formed (search_table ?rz) \<sigma> \<Longrightarrow>
          (deferred_formed \<kappa> P (?\<beta> \<sigma> (search_call_place P ?rz q e c S)) \<and>
            search_placeable (deferred_project (?\<beta> \<sigma> (search_call_place P ?rz q e c S)))) \<and>
          deferred_project (?\<beta> \<sigma> (search_call_place P ?rz q e c S)) =
            finite_call_alternative_state (deferred_project d) q rr e (shared_pattern_project (search_table ?r) gp)
              (i,c,S,shared_bindings_project (search_table ?rz) \<sigma>)"
        using deferred_call_alternative[OF f sock atq eg] by blast
      note c = search_call_successors_with[where F = "\<lambda>d'. deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d')"
        and proj = deferred_project and st = "deferred_project d" and \<beta> = ?\<beta>, OF r atq eg step]
      have e: "fimage deferred_project (search_call_successors_with ?\<beta> P ?r q e gp) =
          finite_call_successors P (deferred_project d) q rr e p"
        using c(1) pp by (simp add: finite_call_successors_alternatives)
      show ?thesis unfolding Inl deferred_committed_fields deferred_call_successors_def eg shared_goal.case
        deferred_committed_project.simps deferred_committed_images deferred_committed_formed_images
        deferred_committed_formed.simps using e c(2) by blast
    next
      case (Inr r)
      have f: "(search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" using 5(1) Inr by simp
      have h: "h |\<in>| access_goals (rep_access ?S r)" using 5(2) Inr by (simp only: deferred_committed_fields)
      have g: "access_goal (rep_access ?S r) h = Resolution_Call_Goal q rr e p" using 5(3) Inr by (simp only: deferred_committed_fields)
      note c = b.call[OF f h g, unfolded pj]
      show ?thesis unfolding Inr deferred_committed_fields deferred_committed_project.simps deferred_committed_images
        deferred_committed_formed_images deferred_committed_formed.simps using c by blast
    qed
  next
    case (6 s h q rr M Ws)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" using 6(1) Inl by simp_all
      let ?r = "deferred_inner d"
      have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF f(1)] .
      have h: "h |\<in>| access_goals (shared_access \<kappa> P ?r)"
        using 6(2) Inl by (simp add: deferred_committed_fields deferred_access_def)
      have g: "shared_goal_project (search_table ?r) (shared_entry_goal h) = Resolution_Material_Goal q rr M"
        using 6(3) Inl by (simp add: deferred_committed_fields deferred_access_def shared_access_simps)
      have atq: "RBT.lookup (shared_goals (search_state ?r)) q = Some h" using shared_goal_at[OF r h g] by simp
      obtain gM where eg: "shared_entry_goal h = Shared_Material_Goal q rr gM"
        and pM: "shared_material_project (search_table ?r) gM = M" using g by (cases "shared_entry_goal h") auto
      let ?M = "shared_material_project (search_table ?r) gM"
      let ?rz = "search_reshare (solution_grounds Ws ?M) ?r"
      let ?\<beta> = "\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)"
      have step: "\<And>E \<sigma>. (E,\<sigma>) |\<in>| shared_solution_alternatives (shared_sharing (search_state ?rz)) gM ?M Ws \<Longrightarrow>
          shared_bindings_formed (search_table ?rz) \<sigma> \<Longrightarrow>
          (deferred_formed \<kappa> P (?\<beta> \<sigma> (search_remove_goal q ?rz)) \<and>
            search_placeable (deferred_project (?\<beta> \<sigma> (search_remove_goal q ?rz)))) \<and>
          deferred_project (?\<beta> \<sigma> (search_remove_goal q ?rz)) =
            finite_material_alternative_state (deferred_project d) q rr ?M (E, shared_bindings_project (search_table ?rz) \<sigma>)"
        using deferred_material_alternative[OF f atq eg] by blast
      note c = search_solution_successors_with[where F = "\<lambda>d'. deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d')"
        and proj = deferred_project and st = "deferred_project d" and \<beta> = ?\<beta> and Ws = Ws, OF r atq eg step]
      have e: "fimage deferred_project (search_solution_successors_with ?\<beta> P ?r q gM ?M Ws) =
          finite_solution_successors (deferred_project d) q rr M Ws"
        using c(1) pM by (simp add: finite_solution_successors_alternatives)
      show ?thesis unfolding Inl deferred_committed_fields deferred_solution_successors_def eg shared_goal.case
        deferred_committed_project.simps deferred_committed_images deferred_committed_formed_images
        deferred_committed_formed.simps using e c(2) by blast
    next
      case (Inr r)
      have f: "(search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" using 6(1) Inr by simp
      have h: "h |\<in>| access_goals (rep_access ?S r)" using 6(2) Inr by (simp only: deferred_committed_fields)
      have g: "access_goal (rep_access ?S r) h = Resolution_Material_Goal q rr M" using 6(3) Inr
        by (simp only: deferred_committed_fields)
      note c = b.solution[OF f h g, unfolded pj]
      show ?thesis unfolding Inr deferred_committed_fields deferred_committed_project.simps deferred_committed_images
        deferred_committed_formed_images deferred_committed_formed.simps using c by blast
    qed
  next
    case (7 s q)
    have k: "q |\<in>| fset_of_list (RBT.keys (shared_nodes (search_state (committed_inner s)))) \<longleftrightarrow>
        RBT.lookup (shared_nodes (search_state (committed_inner s))) q \<noteq> None"
      by (auto simp: fset_of_list_elem RBT.lookup_keys[symmetric])
    have o: "option_fset (RBT.lookup (shared_nodes (search_state (committed_inner s))) q) \<noteq> {||} \<longleftrightarrow>
        RBT.lookup (shared_nodes (search_state (committed_inner s))) q \<noteq> None"
      by (cases "RBT.lookup (shared_nodes (search_state (committed_inner s))) q") simp_all
    show ?case using k o
      by (cases s) (simp_all add: deferred_committed_fields deferred_access_def ac shared_access_simps)
  next
    case (8 s \<sigma> D)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" using 8(1) Inl by simp_all
      note c = deferred_substitute[OF f 8(2)]
      show ?thesis unfolding Inl deferred_committed_fields deferred_committed_project.simps using c by blast
    next
      case (Inr r)
      have f: "(search_formed \<kappa> P r \<and> search_placeable (search_project r)) \<and> search_classes_formed r" using 8(1) Inr by simp
      note c = b.substitute[OF f 8(2), unfolded pj]
      show ?thesis unfolding Inr deferred_committed_fields deferred_committed_project.simps deferred_committed_formed.simps
        using c by blast
    qed
  next
    case (9 s)
    have pl: "search_placeable (deferred_committed_project s)" using 9 by (cases s) simp_all
    show ?case using deferred_committed_of(1)[OF pl, of \<kappa> P] deferred_committed_of(2)[OF pl]
      by (simp add: deferred_committed_fields)
  qed
qed

theorem deferred_committed_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and guard: "\<And>s h F st. deferred_committed_formed \<kappa> P s \<Longrightarrow>
      h |\<in>| access_goals (rep_access (deferred_committed_representation \<kappa> P) s) \<Longrightarrow> \<not> gd s h \<Longrightarrow>
      \<not> commit_call K F st (access_goal (rep_access (deferred_committed_representation \<kappa> P) s) h) \<and>
      \<not> commit_material K F st (access_goal (rep_access (deferred_committed_representation \<kappa> P) s) h) \<and>
      \<not> pr st (access_goal (rep_access (deferred_committed_representation \<kappa> P) s) h)"
  shows "represented_committed_search (deferred_committed_representation \<kappa> P) pr gd \<kappa> K P n F B (deferred_committed_of P st) =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B st"
proof -
  interpret committed_representation_formed "deferred_committed_representation \<kappa> P" "deferred_committed_formed \<kappa> P" \<kappa> P K pr gd
    by (rule committed_representation_formed.intro[OF deferred_committed_structure[OF sock]], unfold_locales)
      (rule guard)
  show ?thesis using search[OF deferred_committed_of(1)[OF pl]] deferred_committed_of(2)[OF pl]
    by (simp add: deferred_committed_fields)
qed

subsection \<open>The commitment access and the kept selection\<close>

text \<open>
  The commitment's tests read beside the access what the inner shared search keeps as it is (the positions holding a
  node, a node's site and clause, a goal's site): the deferred state's is the inner search's. A node's call variables
  are the deferred access's own, read from the node's record (@{const deferred_call_variables}).
\<close>

theorem deferred_commitment_formed:
  assumes d: "deferred_formed \<kappa> P d"
  shows "commitment_formed \<kappa> P (deferred_access \<kappa> P d) (deferred_project d) (shared_commitment_access (deferred_inner d))"
proof -
  let ?r = "deferred_inner d"
  show ?thesis
    apply (rule commitment_formed.intro[OF deferred_access_formed[OF d]])
    apply unfold_locales
    subgoal for q
      by (cases "RBT.lookup (shared_nodes (search_state ?r)) q")
        (simp_all add: shared_commitment_access_def deferred_access_def shared_access_simps fset_of_list.rep_eq
          RBT.lookup_keys[symmetric] domIff)
    subgoal for n q
      by (simp add: shared_commitment_access_def deferred_access_def deferred_node_def shared_derivation_project_simps)
    subgoal for n q
      by (simp add: shared_commitment_access_def deferred_access_def deferred_node_def shared_derivation_project_simps)
    subgoal for h
      by (cases "shared_entry_goal h") (simp_all add: shared_commitment_access_def deferred_access_def shared_access_simps)
    done
qed

definition deferred_commitment_access :: "('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,'a,'s,'d) commitment_access" where
  "deferred_commitment_access s = shared_commitment_access (committed_inner s)"

lemma deferred_committed_commitment_formed:
  assumes f: "deferred_committed_formed \<kappa> P s"
  shows "commitment_formed \<kappa> P (rep_access (deferred_committed_representation \<kappa> P) s)
    (rep_project (deferred_committed_representation \<kappa> P) s) (deferred_commitment_access s)"
proof (cases s)
  case (Inl d)
  then show ?thesis using f deferred_commitment_formed[of \<kappa> P d]
    by (simp add: deferred_committed_fields deferred_commitment_access_def)
next
  case (Inr r)
  then show ?thesis using f shared_commitment_formed[of \<kappa> P r]
    by (simp add: deferred_committed_fields deferred_commitment_access_def shared_committed_representation_def)
qed

text \<open>
  The kept selection reads the inner search's classes over the state's access: the deferred access differs from the
  shared one in its node fields alone (@{thm [source] committed_kept_select_over}).
\<close>

definition deferred_focus_empty :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    's list option \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search \<Rightarrow> bool" where
  "deferred_focus_empty \<kappa> P F s \<longleftrightarrow> shared_focus_empty \<kappa> P F (committed_inner s)"

lemma deferred_focus_empty:
  "deferred_focus_empty \<kappa> P F s \<longleftrightarrow> access_focus_goals F (rep_access (deferred_committed_representation \<kappa> P) s) = {||}"
  by (cases s) (simp_all add: deferred_focus_empty_def shared_focus_empty deferred_committed_fields
    deferred_access_def access_focus_goals_def shared_committed_representation_def)

text \<open>
  The kept selection of a deferred committed state at a closed class @{text Z} (task 989): today's at the empty class,
  the selection at a table at the inner search's own closed class, both its instances.
\<close>

lemma deferred_kept_select_at:
  assumes f: "deferred_committed_formed \<kappa> P s"
    and Z: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state (committed_inner s))) p"
    and EC: "\<And>h. E h \<Longrightarrow> shared_goal_is_call (shared_entry_goal h)"
  shows "committed_kept_select_at Z \<kappa> P (ffilter X) F (committed_inner s) (rep_access (deferred_committed_representation \<kappa> P) s) =
    access_select_in E X (access_focused F (rep_access (deferred_committed_representation \<kappa> P) s))"
proof (cases s)
  case (Inl d)
  have r: "search_formed \<kappa> P (deferred_inner d)" and K: "search_classes_formed (deferred_inner d)"
    using f Inl deferred_formedD(1,2) by auto
  have Zd: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state (deferred_inner d))) p" using Z Inl by simp
  have "committed_kept_select_at Z \<kappa> P (ffilter X) F (deferred_inner d) (deferred_access \<kappa> P d) =
      access_select_in E X (access_focused F (deferred_access \<kappa> P d))"
    unfolding deferred_access_def by (rule committed_kept_select_at_over[OF r K Zd]) (erule EC, rule refl)
  then show ?thesis using Inl by (simp add: deferred_committed_fields)
next
  case (Inr r)
  have r: "search_formed \<kappa> P r" and K: "search_classes_formed r" using f Inr by simp_all
  have Zr: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state r)) p" using Z Inr by simp
  have e: "(shared_access \<kappa> P r)\<lparr>access_node := access_node (shared_access \<kappa> P r),
      access_free := access_free (shared_access \<kappa> P r), access_value_none := access_value_none (shared_access \<kappa> P r),
      access_call_variables := access_call_variables (shared_access \<kappa> P r)\<rparr> = shared_access \<kappa> P r"
    by simp
  have "committed_kept_select_at Z \<kappa> P (ffilter X) F r (shared_access \<kappa> P r) =
      access_select_in E X (access_focused F (shared_access \<kappa> P r))"
    by (rule committed_kept_select_at_over[OF r K Zr EC, where N = "access_node (shared_access \<kappa> P r)"
      and Fr = "access_free (shared_access \<kappa> P r)" and VN = "access_value_none (shared_access \<kappa> P r)"
      and C = "access_call_variables (shared_access \<kappa> P r)", unfolded e]) simp_all
  then show ?thesis using Inr by (simp add: deferred_committed_fields shared_committed_representation_def)
qed

lemma deferred_kept_select:
  assumes f: "deferred_committed_formed \<kappa> P s"
  shows "committed_kept_select \<kappa> P (ffilter X) F (committed_inner s) (rep_access (deferred_committed_representation \<kappa> P) s) =
    access_select X (access_focused F (rep_access (deferred_committed_representation \<kappa> P) s))"
proof -
  have Z: "\<And>p. RBT.lookup RBT.empty p = class_value (\<lambda>h. False) (shared_goals (search_state (committed_inner s))) p"
    by (simp add: class_value_def split: option.split)
  have "committed_kept_select_at RBT.empty \<kappa> P (ffilter X) F (committed_inner s)
      (rep_access (deferred_committed_representation \<kappa> P) s) =
      access_select_in (\<lambda>h. False) X (access_focused F (rep_access (deferred_committed_representation \<kappa> P) s))"
    by (rule deferred_kept_select_at[OF f Z]) simp
  then show ?thesis by (simp only: committed_kept_select_at_empty access_select_in_empty)
qed

definition deferred_kept_tests_select where
  "deferred_kept_tests_select \<kappa> P T gd F s V x =
    committed_kept_select \<kappa> P (ffilter (\<lambda>h. gd s h \<and> tests_priority T F s V x h)) F (committed_inner s) V"

lemma deferred_kept_selected_formed:
  assumes tf: "tested_representation_formed (deferred_committed_representation \<kappa> P) Fi \<kappa> P K pr T gd"
    and fi: "\<And>s. Fi s \<Longrightarrow> deferred_committed_formed \<kappa> P s"
  shows "selected_representation_formed (deferred_committed_representation \<kappa> P) Fi \<kappa> P K pr T gd
    (deferred_focus_empty \<kappa> P) (deferred_kept_tests_select \<kappa> P T gd) (tests_prepare T)"
proof (rule selected_representation_formed.intro[OF tf], unfold_locales, goal_cases)
  case (1 s F)
  show ?case by (rule deferred_focus_empty)
next
  case (2 s F)
  show ?case unfolding deferred_kept_tests_select_def by (rule deferred_kept_select[OF fi[OF 2]])
next
  case (3 s F B rec)
  show ?case by (rule refl)
qed

theorem deferred_kept_committed_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
  shows "selected_committed_search (deferred_committed_representation \<kappa> P)
      (projected_tests (deferred_committed_representation \<kappa> P) K pr (\<lambda>r h. True)) (\<lambda>r h. True) (deferred_focus_empty \<kappa> P)
      (deferred_kept_tests_select \<kappa> P (projected_tests (deferred_committed_representation \<kappa> P) K pr (\<lambda>r h. True)) (\<lambda>r h. True))
      (tests_prepare (projected_tests (deferred_committed_representation \<kappa> P) K pr (\<lambda>r h. True))) \<kappa> P n F B
      (deferred_committed_of P st) =
    finite_committed_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> K P n F B st"
proof -
  let ?R = "deferred_committed_representation \<kappa> P" and ?Fi = "deferred_committed_formed \<kappa> P"
  have cf: "committed_representation_formed ?R ?Fi \<kappa> P K pr (\<lambda>r h. True)"
    by (rule committed_representation_formed.intro[OF deferred_committed_structure[OF sock]], unfold_locales) simp
  interpret selected_representation_formed ?R ?Fi \<kappa> P K pr "projected_tests ?R K pr (\<lambda>r h. True)" "\<lambda>r h. True"
      "deferred_focus_empty \<kappa> P" "deferred_kept_tests_select \<kappa> P (projected_tests ?R K pr (\<lambda>r h. True)) (\<lambda>r h. True)"
      "tests_prepare (projected_tests ?R K pr (\<lambda>r h. True))"
    by (rule deferred_kept_selected_formed[OF committed_representation_formed.tested[OF cf]]) simp
  show ?thesis using selected_committed[OF deferred_committed_of(1)[OF pl]] deferred_committed_of(2)[OF pl]
    by (simp add: deferred_committed_fields)
qed

text \<open>
  R5's committed search is computed over the deferred representation where the program's sockets are distinct and the
  state is placeable, and as R5's elsewhere; the representation's first state is deferred where the state's variables
  are rooted, shared otherwise, so the equation holds at every input.
\<close>

declare finite_committed_search_kept_code [code del]

lemma finite_committed_search_deferred_code [code]:
  "finite_committed_search \<kappa> K P n F B st = (if clause_sockets_distinct P \<and> search_placeable st
    then selected_committed_search (deferred_committed_representation \<kappa> P)
      (projected_tests (deferred_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True)) (\<lambda>r h. True)
      (deferred_focus_empty \<kappa> P)
      (deferred_kept_tests_select \<kappa> P
        (projected_tests (deferred_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True)) (\<lambda>r h. True))
      (tests_prepare (projected_tests (deferred_committed_representation \<kappa> P) K (finite_commitment_priority K) (\<lambda>r h. True)))
      \<kappa> P n F B (deferred_committed_of P st)
    else finite_committed_search_by (finite_committed_select \<kappa> K P) \<kappa> K P n F B st)"
  by (simp add: finite_committed_search_def deferred_kept_committed_search)

export_code finite_committed_search checking SML

section \<open>The committed search over the deferred search at a table of certified calls\<close>

text \<open>
  GT3b (task 970). D1d's committed representation at a table: its successors close a goal the inner search's index
  closes, the store and records standing (@{const deferred_successors_in}, @{const search_successors_in}); a state
  shared again or substituted outside the deferred bind is made with the table's calls attached
  (@{text deferred_committed_of_in}, @{text deferred_substitute_in}), so the table's calls are kept by every step.
  Its search is GT2a's committed search at the table at the projection (@{text deferred_kept_committed_search_in}).
\<close>

definition deferred_committed_of_in :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_committed_of_in C P st =
    (if search_variables_rooted st then Inl (deferred_of_in C P st) else Inr (search_of_in C P st))"

lemma deferred_committed_of_in:
  assumes pl: "search_placeable st"
  shows "deferred_committed_formed \<kappa> P (deferred_committed_of_in C P st)"
    and "deferred_committed_project (deferred_committed_of_in C P st) = st"
    and "search_calls (committed_inner (deferred_committed_of_in C P st)) = C"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have "deferred_committed_formed \<kappa> P (deferred_committed_of_in C P st) \<and>
      deferred_committed_project (deferred_committed_of_in C P st) = st \<and>
      search_calls (committed_inner (deferred_committed_of_in C P st)) = C"
  proof (cases "search_variables_rooted st")
    case True
    then show ?thesis using deferred_of_in_rooted[OF d True] pl
      by (simp add: deferred_committed_of_in_def)
  next
    case False
    then show ?thesis using search_of_in[OF d] pl
      by (simp add: deferred_committed_of_in_def)
  qed
  then show "deferred_committed_formed \<kappa> P (deferred_committed_of_in C P st)"
    and "deferred_committed_project (deferred_committed_of_in C P st) = st"
    and "search_calls (committed_inner (deferred_committed_of_in C P st)) = C" by blast+
qed

text \<open>A state shared again from a carried table's sharing (task 989): the deferred state of the carried search where
  its variables are rooted, the carried search otherwise.\<close>

definition deferred_committed_of_carried :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<times> (nat,'d fset) rbt \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_committed_of_carried C X P st = (let r = search_of_carried C X P st in
    if search_variables_rooted st then Inl (deferred_of_search r) else Inr r)"

lemma deferred_committed_of_carried:
  assumes pl: "search_placeable st"
  shows "deferred_committed_formed \<kappa> P (deferred_committed_of_carried C (table_carry C) P st)"
    and "deferred_committed_project (deferred_committed_of_carried C (table_carry C) P st) = st"
    and "search_calls (committed_inner (deferred_committed_of_carried C (table_carry C) P st)) = C"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  note sc = search_of_carried_table[OF d, where C = C]
  have "deferred_committed_formed \<kappa> P (deferred_committed_of_carried C (table_carry C) P st) \<and>
      deferred_committed_project (deferred_committed_of_carried C (table_carry C) P st) = st \<and>
      search_calls (committed_inner (deferred_committed_of_carried C (table_carry C) P st)) = C"
  proof (cases "search_variables_rooted st")
    case True
    then show ?thesis using deferred_of_search_rooted[OF sc(1) sc(4) sc(2) True] sc(3) pl
      by (simp add: deferred_committed_of_carried_def)
  next
    case False
    then show ?thesis using sc pl by (simp add: deferred_committed_of_carried_def)
  qed
  then show "deferred_committed_formed \<kappa> P (deferred_committed_of_carried C (table_carry C) P st)"
    and "deferred_committed_project (deferred_committed_of_carried C (table_carry C) P st) = st"
    and "search_calls (committed_inner (deferred_committed_of_carried C (table_carry C) P st)) = C" by blast+
qed

text \<open>A substitution at a table: through the deferred bind where @{const deferred_substitute} binds, the table's calls
  attached where the state is made again.\<close>

definition deferred_substitute_carried :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<times> (nat,'d fset) rbt \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_substitute_carried C X P \<sigma> D d = (let G = deferred_goal_variables d;
      L = remdups (filter (\<lambda>a. a |\<in>| D \<and> \<sigma> a \<noteq> Finite_Variable a) G);
      at = (\<lambda>x. RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None) in
    if fBall D (\<lambda>a. \<sigma> a = Finite_Variable a \<or> a \<in> set G) \<and>
      list_all (\<lambda>a. at a \<and> fBall (finite_pattern_variables (\<sigma> a)) (\<lambda>b. b \<notin> set L \<and> b \<in> set G \<and> at b)) L
    then Inl (let r1 = search_reshare (plain_grounds \<sigma> D) (deferred_inner d) in
      deferred_bind P (map (\<lambda>a. (a, keyed_pattern_at (shared_sharing (search_state r1)) (\<sigma> a))) L)
        (d\<lparr>deferred_inner := r1\<rparr>))
    else deferred_committed_of_carried C X P (resolution_state_substitute \<sigma> (deferred_project d)))"

text \<open>At a table the substitution re-shares from the table's sharing state, made once where the representation is
  made (@{text deferred_committed_representation_in}); @{text deferred_substitute_in} is it at @{const table_carry}.\<close>

definition deferred_substitute_in :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search" where
  "deferred_substitute_in C P \<sigma> D d = deferred_substitute_carried C (table_carry C) P \<sigma> D d"

theorem deferred_substitute_in:
  fixes d :: "('a,'s::linorder,'d,'c) deferred_search"
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Finite_Variable a"
  shows "deferred_committed_formed \<kappa> P (deferred_substitute_in C P \<sigma> D d)"
    and "deferred_committed_project (deferred_substitute_in C P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d)"
    and "search_calls (deferred_inner d) = C \<Longrightarrow> search_calls (committed_inner (deferred_substitute_in C P \<sigma> D d)) = C"
proof -
  note sub = deferred_substitute[where D = D and \<sigma> = \<sigma>, OF d pl out]
  have pl': "search_placeable (resolution_state_substitute \<sigma> (deferred_project d))" by (rule search_placeable_substitute[OF pl])
  note ofi = deferred_committed_of_carried[OF pl']
  have all: "deferred_committed_formed \<kappa> P (deferred_substitute_in C P \<sigma> D d) \<and>
      deferred_committed_project (deferred_substitute_in C P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d) \<and>
      (search_calls (deferred_inner d) = C \<longrightarrow> search_calls (committed_inner (deferred_substitute_in C P \<sigma> D d)) = C)"
    using sub ofi unfolding deferred_substitute_in_def deferred_substitute_carried_def deferred_substitute_def Let_def
    by (auto simp: search_calls_frame split: if_splits)
  then show "deferred_committed_formed \<kappa> P (deferred_substitute_in C P \<sigma> D d)"
    and "deferred_committed_project (deferred_substitute_in C P \<sigma> D d) = resolution_state_substitute \<sigma> (deferred_project d)"
    and "search_calls (deferred_inner d) = C \<Longrightarrow> search_calls (committed_inner (deferred_substitute_in C P \<sigma> D d)) = C"
    by blast+
qed

lemma deferred_call_successors_frame:
  assumes "d' |\<in>| deferred_call_successors P d h"
  shows "search_frame (deferred_inner d') = search_frame (deferred_inner d)"
proof (cases "shared_entry_goal h")
  case (Shared_Call_Goal q rr e gp)
  have m: "d' |\<in>| search_call_successors_with (\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)) P (deferred_inner d) q e gp"
    using assms Shared_Call_Goal by (simp add: deferred_call_successors_def)
  show ?thesis by (rule search_call_successors_with_frame[where g = "\<lambda>d. search_frame (deferred_inner d)", OF m]) simp
next
  case (Shared_Material_Goal q rr gM)
  then show ?thesis using assms by (simp add: deferred_call_successors_def)
qed

lemma deferred_solution_successors_frame:
  assumes "d' |\<in>| deferred_solution_successors P d h Ws"
  shows "search_frame (deferred_inner d') = search_frame (deferred_inner d)"
proof (cases "shared_entry_goal h")
  case (Shared_Material_Goal q rr gM)
  have m: "d' |\<in>| search_solution_successors_with (\<lambda>\<sigma> r. deferred_bind P \<sigma> (deferred_at q d r)) P (deferred_inner d) q gM
      (shared_material_project (search_table (deferred_inner d)) gM) Ws"
    using assms Shared_Material_Goal by (simp add: deferred_solution_successors_def)
  show ?thesis by (rule search_solution_successors_with_frame[where g = "\<lambda>d. search_frame (deferred_inner d)", OF m]) simp
next
  case (Shared_Call_Goal q rr e gp)
  then show ?thesis using assms by (simp add: deferred_solution_successors_def)
qed

definition deferred_committed_representation_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d \<times> finite_factor_term) list \<Rightarrow>
    (('a,'s::linorder,'d,'c) deferred_search + ('a,'s,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry,
      ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) committed_representation" where
  "deferred_committed_representation_in \<kappa> P C = (let X = table_carry C in (deferred_committed_representation \<kappa> P)\<lparr>
    rep_successors := (\<lambda>s h. case s of Inl d \<Rightarrow> fimage Inl (deferred_successors_in \<kappa> P d h)
      | Inr r \<Rightarrow> fimage Inr (search_successors_in \<kappa> P r h)),
    rep_substitute := (\<lambda>s \<sigma> D. case s of Inl d \<Rightarrow> deferred_substitute_carried C X P \<sigma> D d
      | Inr r \<Rightarrow> Inr (search_substitute_plain P \<sigma> D r)),
    rep_share := deferred_committed_of_carried C X P\<rparr>)"

lemma deferred_committed_in_fields:
  "rep_access (deferred_committed_representation_in \<kappa> P C) = rep_access (deferred_committed_representation \<kappa> P)"
  "rep_empty (deferred_committed_representation_in \<kappa> P C) = rep_empty (deferred_committed_representation \<kappa> P)"
  "rep_project (deferred_committed_representation_in \<kappa> P C) = deferred_committed_project"
  "rep_refresh (deferred_committed_representation_in \<kappa> P C) = rep_refresh (deferred_committed_representation \<kappa> P)"
  "rep_construct (deferred_committed_representation_in \<kappa> P C) = rep_construct (deferred_committed_representation \<kappa> P)"
  "rep_node_positions (deferred_committed_representation_in \<kappa> P C) = rep_node_positions (deferred_committed_representation \<kappa> P)"
  "rep_call_successors (deferred_committed_representation_in \<kappa> P C) =
    rep_call_successors (deferred_committed_representation \<kappa> P)"
  "rep_solution_successors (deferred_committed_representation_in \<kappa> P C) =
    rep_solution_successors (deferred_committed_representation \<kappa> P)"
  "rep_successors (deferred_committed_representation_in \<kappa> P C) (Inl d) h = fimage Inl (deferred_successors_in \<kappa> P d h)"
  "rep_successors (deferred_committed_representation_in \<kappa> P C) (Inr r) h = fimage Inr (search_successors_in \<kappa> P r h)"
  "rep_substitute (deferred_committed_representation_in \<kappa> P C) (Inl d) \<sigma> D = deferred_substitute_in C P \<sigma> D d"
  "rep_substitute (deferred_committed_representation_in \<kappa> P C) (Inr r) \<sigma> D = Inr (search_substitute_plain P \<sigma> D r)"
  "rep_share (deferred_committed_representation_in \<kappa> P C) = deferred_committed_of_carried C (table_carry C) P"
  by (simp_all add: deferred_committed_representation_in_def deferred_committed_representation_def Let_def
    deferred_substitute_in_def)

theorem deferred_committed_structure_in:
  assumes sock: "clause_sockets_distinct P"
    and tbl: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "committed_representation_structure_in (deferred_committed_representation_in \<kappa> P C)
    (\<lambda>s. deferred_committed_formed \<kappa> P s \<and> search_calls (committed_inner s) = C) \<kappa> P \<Theta>"
proof -
  let ?R = "deferred_committed_representation \<kappa> P" and ?Q = "deferred_committed_representation_in \<kappa> P C"
  interpret b: committed_representation_structure ?R "deferred_committed_formed \<kappa> P" \<kappa> P
    by (rule deferred_committed_structure[OF sock])
  note fd = deferred_committed_in_fields[of \<kappa> P C]
  show ?thesis
  proof (rule committed_representation_structure_in.intro, goal_cases)
    case (1 s)
    then show ?case using b.access[of s] by (simp add: fd deferred_committed_fields)
  next
    case (2 s)
    then show ?case using b.refresh[of s]
      by (cases s) (auto simp: fd deferred_committed_fields shared_committed_representation_def search_calls_frame)
  next
    case (3 s m q)
    then show ?case using b.construct[of s m q]
      by (cases s) (auto simp: fd deferred_committed_fields shared_committed_representation_def search_calls_frame)
  next
    case (4 s h)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" "search_calls (deferred_inner d) = C"
        using 4(1) Inl by simp_all
      have h: "h |\<in>| access_goals (deferred_access \<kappa> P d)" using 4(2) Inl by (simp add: fd deferred_committed_fields)
      have D': "\<And>e t. (e,t) \<in> set (search_calls (deferred_inner d)) \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
        using tbl f(3) by simp
      note c = deferred_successors_in[OF f(1) f(2) sock h D']
      have p: "fimage (rep_project ?Q) (rep_successors ?Q s h) =
          finite_goal_successors_in \<Theta> P (rep_project ?Q s) (access_goal (rep_access ?Q s) h)"
        using c(1) Inl by (simp add: fd deferred_committed_fields deferred_committed_images comp_def)
      have q: "deferred_committed_formed \<kappa> P s' \<and> search_calls (committed_inner s') = C"
        if s': "s' |\<in>| rep_successors ?Q s h" for s'
      proof -
        obtain d' where e: "s' = Inl d'" and m: "d' |\<in>| deferred_successors_in \<kappa> P d h" using s' Inl by (auto simp: fd)
        show ?thesis using c(2)[OF m] f(3) e by (simp add: search_calls_frame)
      qed
      show ?thesis using p q by blast
    next
      case (Inr r)
      have f: "search_formed \<kappa> P r" "search_placeable (search_project r)" "search_classes_formed r" "search_calls r = C"
        using 4(1) Inr by simp_all
      have h: "h |\<in>| access_goals (shared_access \<kappa> P r)" using 4(2) Inr
        by (simp add: fd deferred_committed_fields shared_committed_representation_def)
      have D': "\<And>e t. (e,t) \<in> set (search_calls r) \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None" using tbl f(4) by simp
      note c = search_successors_in[OF f(1) f(2) sock h D']
      have p: "fimage (rep_project ?Q) (rep_successors ?Q s h) =
          finite_goal_successors_in \<Theta> P (rep_project ?Q s) (access_goal (rep_access ?Q s) h)"
        using c(1) Inr
        by (simp add: fd deferred_committed_fields deferred_committed_images shared_committed_representation_def comp_def)
      have q: "deferred_committed_formed \<kappa> P s' \<and> search_calls (committed_inner s') = C"
        if s': "s' |\<in>| rep_successors ?Q s h" for s'
      proof -
        obtain r' where e: "s' = Inr r'" and m: "r' |\<in>| search_successors_in \<kappa> P r h" using s' Inr by (auto simp: fd)
        show ?thesis using c(2)[OF m] c(3)[OF m f(3)] f(4) e by (simp add: search_calls_frame)
      qed
      show ?thesis using p q by blast
    qed
  next
    case (5 s h q rr d p)
    have f: "deferred_committed_formed \<kappa> P s" "search_calls (committed_inner s) = C" using 5(1) by simp_all
    have h: "h |\<in>| access_goals (rep_access ?R s)" and g: "access_goal (rep_access ?R s) h = Resolution_Call_Goal q rr d p"
      using 5(2,3) by (simp_all add: fd)
    note c = b.call[OF f(1) h g]
    have k: "search_calls (committed_inner s') = C" if s': "s' |\<in>| rep_call_successors ?R s h" for s'
    proof (cases s)
      case (Inl dd)
      then obtain d' where e: "s' = Inl d'" and m: "d' |\<in>| deferred_call_successors P dd h"
        using s' by (auto simp: deferred_committed_fields)
      show ?thesis using deferred_call_successors_frame[OF m] f(2) Inl e by (simp add: search_calls_frame)
    next
      case (Inr r)
      then obtain r' where e: "s' = Inr r'" and m: "r' |\<in>| rep_call_successors (shared_committed_representation \<kappa> P) r h"
        using s' by (auto simp: deferred_committed_fields)
      show ?thesis using shared_call_successors_frame[OF m] f(2) Inr e by (simp add: search_calls_frame)
    qed
    show ?case using c k by (auto simp: fd deferred_committed_fields)
  next
    case (6 s h q rr M Ws)
    have f: "deferred_committed_formed \<kappa> P s" "search_calls (committed_inner s) = C" using 6(1) by simp_all
    have h: "h |\<in>| access_goals (rep_access ?R s)" and g: "access_goal (rep_access ?R s) h = Resolution_Material_Goal q rr M"
      using 6(2,3) by (simp_all add: fd)
    note c = b.solution[OF f(1) h g, of Ws]
    have k: "search_calls (committed_inner s') = C" if s': "s' |\<in>| rep_solution_successors ?R s h Ws" for s'
    proof (cases s)
      case (Inl dd)
      then obtain d' where e: "s' = Inl d'" and m: "d' |\<in>| deferred_solution_successors P dd h Ws"
        using s' by (auto simp: deferred_committed_fields)
      show ?thesis using deferred_solution_successors_frame[OF m] f(2) Inl e by (simp add: search_calls_frame)
    next
      case (Inr r)
      then obtain r' where e: "s' = Inr r'"
        and m: "r' |\<in>| rep_solution_successors (shared_committed_representation \<kappa> P) r h Ws"
        using s' by (auto simp: deferred_committed_fields)
      show ?thesis using shared_solution_successors_frame[OF m] f(2) Inr e by (simp add: search_calls_frame)
    qed
    show ?case using c k by (auto simp: fd deferred_committed_fields)
  next
    case (7 s q)
    then show ?case using b.positions[of s q] by (simp add: fd deferred_committed_fields)
  next
    case (8 s \<sigma> D)
    show ?case
    proof (cases s)
      case (Inl d)
      have f: "deferred_formed \<kappa> P d" "search_placeable (deferred_project d)" "search_calls (deferred_inner d) = C"
        using 8(1) Inl by simp_all
      note c = deferred_substitute_in[where \<sigma> = \<sigma> and D = D and C = C, OF f(1) f(2) 8(2)]
      show ?thesis using c(1) c(2) c(3) f(3) Inl by (simp add: fd)
    next
      case (Inr r)
      have f: "deferred_committed_formed \<kappa> P (Inr r)" "search_calls r = C" using 8(1) Inr by simp_all
      note c = b.substitute[of "Inr r" D \<sigma>, OF f(1) 8(2)]
      show ?thesis using c f(2) Inr
        by (simp add: fd deferred_committed_fields shared_committed_representation_def search_calls_frame, metis)
    qed
  next
    case (9 s)
    have pl: "search_placeable (deferred_committed_project s)" using 9 by (cases s) simp_all
    show ?case using deferred_committed_of_carried[OF pl] by (simp add: fd)
  qed
qed

text \<open>The closing test a deferred state reads is its inner search's.\<close>

lemma deferred_committed_closes:
  assumes f: "deferred_committed_formed \<kappa> P s" and c: "search_calls (committed_inner s) = C"
    and tbl: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
    and h: "h |\<in>| access_goals (rep_access (deferred_committed_representation_in \<kappa> P C) s)"
  shows "search_closes (committed_inner s) h \<longleftrightarrow>
    finite_table_closes \<Theta> (access_goal (rep_access (deferred_committed_representation_in \<kappa> P C) s) h)"
proof -
  have r: "search_formed \<kappa> P (committed_inner s)" using f by (cases s) (auto dest: deferred_formedD(1))
  have eg: "access_goals (rep_access (deferred_committed_representation_in \<kappa> P C) s) =
      access_goals (shared_access \<kappa> P (committed_inner s))"
    by (cases s) (simp_all add: deferred_committed_in_fields deferred_committed_fields deferred_access_def
      shared_committed_representation_def)
  have ea: "access_goal (rep_access (deferred_committed_representation_in \<kappa> P C) s) =
      access_goal (shared_access \<kappa> P (committed_inner s))"
    by (cases s) (simp_all add: deferred_committed_in_fields deferred_committed_fields deferred_access_def
      shared_committed_representation_def)
  have D': "\<And>d t. (d,t) \<in> set (search_calls (committed_inner s)) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
    using tbl c by simp
  show ?thesis using search_closes_table[OF r _ D'] h unfolding eg ea by blast
qed

lemma deferred_kept_select_in:
  assumes f: "deferred_committed_formed \<kappa> P s"
  shows "committed_kept_select_in \<kappa> P (ffilter X) F (committed_inner s) (rep_access (deferred_committed_representation_in \<kappa> P C) s) =
    access_select_in (search_closes (committed_inner s)) X
      (access_focused F (rep_access (deferred_committed_representation_in \<kappa> P C) s))"
proof -
  have r: "search_formed \<kappa> P (committed_inner s)" using f by (cases s) (auto dest: deferred_formedD(1))
  have "committed_kept_select_at (search_closed (committed_inner s)) \<kappa> P (ffilter X) F (committed_inner s)
      (rep_access (deferred_committed_representation \<kappa> P) s) =
      access_select_in (search_closes (committed_inner s)) X (access_focused F (rep_access (deferred_committed_representation \<kappa> P) s))"
    by (rule deferred_kept_select_at[OF f search_closed_class[OF r]]) (erule search_closes_call)
  then show ?thesis by (simp add: committed_kept_select_in_at deferred_committed_in_fields)
qed

definition deferred_kept_tests_select_in where
  "deferred_kept_tests_select_in \<kappa> P T gd F s V x =
    committed_kept_select_in \<kappa> P (ffilter (\<lambda>h. gd s h \<and> tests_priority T F s V x h)) F (committed_inner s) V"

lemma deferred_kept_selected_formed_in:
  assumes tf: "tested_representation_formed_in (deferred_committed_representation_in \<kappa> P C) Fi \<kappa> P \<Theta> K pr T gd
      (\<lambda>s. search_closes (committed_inner s))"
    and fi: "\<And>s. Fi s \<Longrightarrow> deferred_committed_formed \<kappa> P s"
  shows "selected_representation_formed_in (deferred_committed_representation_in \<kappa> P C) Fi \<kappa> P \<Theta> K pr T gd
    (\<lambda>s. search_closes (committed_inner s)) (deferred_focus_empty \<kappa> P) (deferred_kept_tests_select_in \<kappa> P T gd)
    (tests_prepare T)"
proof (rule selected_representation_formed_in.intro[OF tf], unfold_locales, goal_cases)
  case (1 s F)
  show ?case using deferred_focus_empty[of \<kappa> P F s] by (simp add: deferred_committed_in_fields)
next
  case (2 s F)
  show ?case unfolding deferred_kept_tests_select_in_def by (rule deferred_kept_select_in[OF fi[OF 2]])
next
  case (3 s F B rec)
  show ?case by (rule refl)
qed

theorem deferred_kept_committed_search_in:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and tbl: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "selected_committed_search (deferred_committed_representation_in \<kappa> P C)
      (projected_tests (deferred_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True)) (\<lambda>r h. True)
      (deferred_focus_empty \<kappa> P)
      (deferred_kept_tests_select_in \<kappa> P (projected_tests (deferred_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True))
        (\<lambda>r h. True))
      (tests_prepare (projected_tests (deferred_committed_representation_in \<kappa> P C) K pr (\<lambda>r h. True))) \<kappa> P n F B
      (deferred_committed_of_in C P st) =
    finite_committed_search_by_in \<Theta> (finite_resolution_select_in \<Theta> pr \<kappa> P) \<kappa> K P n F B st"
proof -
  let ?Q = "deferred_committed_representation_in \<kappa> P C"
  let ?Fi = "\<lambda>s. deferred_committed_formed \<kappa> P s \<and> search_calls (committed_inner s) = C"
  have st: "committed_representation_structure_in ?Q ?Fi \<kappa> P \<Theta>" by (rule deferred_committed_structure_in[OF sock tbl])
  have cl: "search_closes (committed_inner s) h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access ?Q s) h)"
    if s: "?Fi s" and h: "h |\<in>| access_goals (rep_access ?Q s)" for s h
    using deferred_committed_closes[OF conjunct1[OF s] conjunct2[OF s] tbl h] .
  interpret selected_representation_formed_in ?Q ?Fi \<kappa> P \<Theta> K pr "projected_tests ?Q K pr (\<lambda>r h. True)" "\<lambda>r h. True"
      "\<lambda>s. search_closes (committed_inner s)" "deferred_focus_empty \<kappa> P"
      "deferred_kept_tests_select_in \<kappa> P (projected_tests ?Q K pr (\<lambda>r h. True)) (\<lambda>r h. True)"
      "tests_prepare (projected_tests ?Q K pr (\<lambda>r h. True))"
    by (rule deferred_kept_selected_formed_in[OF projected_tested_in[OF st cl]]) simp_all
  have f: "?Fi (deferred_committed_of_in C P st)"
    using deferred_committed_of_in[OF pl] by simp
  show ?thesis using selected_committed[OF f] deferred_committed_of_in(2)[OF pl] by (simp add: deferred_committed_in_fields)
qed

end
