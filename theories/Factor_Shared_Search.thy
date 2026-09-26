theory Factor_Shared_Search
  imports Factor_Shared_Resolution Factor_Search_Representations
begin

section \<open>The shared search state\<close>

text \<open>
  Build F2b2 (b) of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size" (divided at
  q135): R3's search over F2b2 (a)'s shared state (@{text Factor_Shared_Resolution}), every ground subterm held once
  in one table and two ground calls compared as references, numbers. The search reads the state through the access
  stated once in @{text Factor_Search_Representations}: this theory gives the shared state's access, proves it formed,
  and gives the refresh, the construction step and the successors over the shared state; the search is then the
  representation's search, R3's by @{thm [source] represented_search}, and computes R3's search.

  Beside (a)'s state the search keeps what F2b2 (c) keeps over F2b1's: the goal positions holding a registered variable
  at each position (the positions the construction reads), and every value the construction returned, beside its
  node. The first is kept by every step that changes a goal; the second is filled by the refresh and never dropped.
  A goal holding no registered variable is never held back, so the selection tests only the goals that hold one.
\<close>

record (overloaded) ('a,'s::linorder,'d,'c) shared_search =
  search_state :: "('a,'s,'d,'c) shared_state"
  search_registered :: "('s list, 's list fset) rbt"
  search_values :: "('s list, (('a,'s,'d,'c) shared_derivation \<times> 'a \<times> finite_factor_term) fset) rbt"

abbreviation search_table :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> shape list" where
  "search_table r \<equiv> shared_state_table (search_state r)"

abbreviation search_project :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "search_project r \<equiv> shared_state_project (search_state r)"

definition shared_goal_registered :: "('a,'s,'d,'c) shared_goal_entry \<Rightarrow> 's list fset" where
  "shared_goal_registered h =
    fimage (\<lambda>x. fst (fst x)) (ffilter (\<lambda>x. snd (fst x)) (shared_goal_variables (shared_entry_goal h)))"

definition option_registered :: "('a,'s,'d,'c) shared_goal_entry option \<Rightarrow> 's list fset" where
  "option_registered go = (case go of None \<Rightarrow> {||} | Some h \<Rightarrow> shared_goal_registered h)"

lemma shared_goal_registered_member:
  "p |\<in>| shared_goal_registered h \<longleftrightarrow> (\<exists>a. ((p,True),a) |\<in>| shared_goal_variables (shared_entry_goal h))"
  by (force simp: shared_goal_registered_def fimage.rep_eq ffilter.rep_eq)

definition search_registered_formed :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_registered_formed r \<longleftrightarrow> (\<forall>q h p. RBT.lookup (shared_goals (search_state r)) q = Some h \<longrightarrow>
    p |\<in>| shared_goal_registered h \<longrightarrow> q |\<in>| tree_bucket (search_registered r) p)"

definition search_values_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_values_formed \<kappa> P r \<longleftrightarrow> (\<forall>p z. z |\<in>| tree_bucket (search_values r) p \<longrightarrow>
    shared_derivation_formed (search_table r) (fst z) \<and>
    finite_registered_value \<kappa> P (shared_derivation_project (search_table r) (fst z)) (fst (snd z)) = Some (snd (snd z)))"

definition search_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_formed \<kappa> P r \<longleftrightarrow> shared_state_formed \<kappa> P (search_state r) \<and> search_registered_formed r \<and>
    search_values_formed \<kappa> P r"

lemma search_formedD:
  assumes "search_formed \<kappa> P r"
  shows "shared_state_formed \<kappa> P (search_state r)" "search_registered_formed r" "search_values_formed \<kappa> P r"
  using assms by (simp_all add: search_formed_def)

subsection \<open>Reading a node's kept values and free registered variables\<close>

definition search_kept_value :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> 'a \<Rightarrow>
    finite_factor_term option" where
  "search_kept_value r nd a = (case sorted_list_of_fset (fimage (\<lambda>z. Ordered_Factor_Term (snd (snd z)))
      (ffilter (\<lambda>z. fst z = nd \<and> fst (snd z) = a) (tree_bucket (search_values r) (shared_derivation_position nd)))) of
    [] \<Rightarrow> None | t # ts \<Rightarrow> Some (case t of Ordered_Factor_Term v \<Rightarrow> v))"

definition search_value :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> 'a \<Rightarrow> finite_factor_term option" where
  "search_value \<kappa> P r nd a = (case search_kept_value r nd a of Some v \<Rightarrow> Some v
    | None \<Rightarrow> finite_registered_value \<kappa> P (shared_derivation_project (search_table r) nd) a)"

lemma search_value:
  assumes r: "search_values_formed \<kappa> P r"
  shows "search_value \<kappa> P r nd a = finite_registered_value \<kappa> P (shared_derivation_project (search_table r) nd) a"
proof -
  let ?E = "ffilter (\<lambda>z. fst z = nd \<and> fst (snd z) = a) (tree_bucket (search_values r) (shared_derivation_position nd))"
  have E: "finite_registered_value \<kappa> P (shared_derivation_project (search_table r) nd) a = Some (snd (snd z))"
    if "z |\<in>| ?E" for z
    using that r by (auto simp: search_values_formed_def ffilter.rep_eq)
  show ?thesis
  proof (cases "sorted_list_of_fset (fimage (\<lambda>z. Ordered_Factor_Term (snd (snd z))) ?E)")
    case Nil
    then show ?thesis unfolding search_value_def search_kept_value_def by simp
  next
    case (Cons t ts)
    have "t \<in> set (sorted_list_of_fset (fimage (\<lambda>z. Ordered_Factor_Term (snd (snd z))) ?E))" using Cons by simp
    then have "t |\<in>| fimage (\<lambda>z. Ordered_Factor_Term (snd (snd z))) ?E" by (simp add: sorted_list_of_fset.rep_eq)
    then obtain z where z: "z |\<in>| ?E" and t: "t = Ordered_Factor_Term (snd (snd z))" by (auto elim!: fimageE)
    show ?thesis unfolding search_value_def search_kept_value_def Cons using E[OF z] t by simp
  qed
qed


definition shared_free_registered :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow>
    'a fset" where
  "shared_free_registered \<kappa> nd = ffilter
    (\<lambda>a. (a, Shared_Variable ((shared_derivation_position nd,True),a)) |\<in>| shared_derivation_bindings nd)
    (witness_registered \<kappa> (shared_derivation_site nd) (shared_derivation_schema nd))"

lemma shared_free_registered:
  "shared_free_registered \<kappa> nd = finite_free_registered \<kappa> (shared_derivation_project T nd)"
proof -
  have "(a, Finite_Variable ((shared_derivation_position nd,True),a)) |\<in>|
      fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd) \<longleftrightarrow>
    (a, Shared_Variable ((shared_derivation_position nd,True),a)) |\<in>| shared_derivation_bindings nd" for a
  proof
    assume "(a, Finite_Variable ((shared_derivation_position nd,True),a)) |\<in>|
      fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd)"
    then obtain z where e: "(a, Finite_Variable ((shared_derivation_position nd,True),a)) = (fst z, shared_pattern_project T (snd z))"
      and z: "z |\<in>| shared_derivation_bindings nd"
      by (rule fimageE)
    have z12: "fst z = a \<and> snd z = Shared_Variable ((shared_derivation_position nd,True),a)"
      using e[symmetric] by simp
    have "z = (a, Shared_Variable ((shared_derivation_position nd,True),a))" using z12 by (simp add: prod_eq_iff)
    then show "(a, Shared_Variable ((shared_derivation_position nd,True),a)) |\<in>| shared_derivation_bindings nd"
      using z by simp
  next
    assume z: "(a, Shared_Variable ((shared_derivation_position nd,True),a)) |\<in>| shared_derivation_bindings nd"
    have "(a, Finite_Variable ((shared_derivation_position nd,True),a)) =
        (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (a, Shared_Variable ((shared_derivation_position nd,True),a))"
      by simp
    then show "(a, Finite_Variable ((shared_derivation_position nd,True),a)) |\<in>|
      fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd)"
      using z unfolding fimage.rep_eq by (rule image_eqI)
  qed
  then show ?thesis
    by (simp add: shared_free_registered_def finite_free_registered_def shared_derivation_project_def)
qed

subsection \<open>Kinds, leaves and keys of shared goals\<close>

fun shared_goal_is_call :: "('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_goal_is_call (Shared_Call_Goal q r d p) = True"
| "shared_goal_is_call (Shared_Material_Goal q r M) = False"

fun shared_has_leaf :: "'v shared_pattern \<Rightarrow> bool" where
  "shared_has_leaf (Shared_Variable a) = False"
| "shared_has_leaf (Shared_Ground i) = True"
| "shared_has_leaf (Shared_Node A p r) = (shared_has_leaf p \<or> shared_has_leaf r)"

lemma finite_pattern_has_leaf_exact: "finite_pattern_has_leaf (finite_exact_term_pattern t)"
  by (induction t) simp_all

lemma shared_has_leaf: "shared_has_leaf p \<longleftrightarrow> finite_pattern_has_leaf (shared_pattern_project T p)"
  by (induction p) (auto split: option.splits simp: finite_pattern_has_leaf_exact)

fun shared_goal_leaf :: "('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_goal_leaf (Shared_Call_Goal q r d p) = shared_has_leaf p"
| "shared_goal_leaf (Shared_Material_Goal q r M) = False"

fun shared_goal_solvable :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_goal_solvable T (Shared_Call_Goal q r d p) = False"
| "shared_goal_solvable T (Shared_Material_Goal q r M) =
    (finite_material_resolution (shared_material_project T M) \<noteq> Material_Waits)"

fun shared_call_key :: "('a,'s,'d,'c) shared_goal \<Rightarrow> nat" where
  "shared_call_key (Shared_Call_Goal q r d (Shared_Ground i)) = i"
| "shared_call_key g = 0"

definition shared_closes :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "shared_closes hn h = (case shared_entry_goal h of
      Shared_Call_Goal q r d p \<Rightarrow> shared_derivation_site (shared_entry_node hn) = d \<and>
        shared_derivation_call (shared_entry_node hn) = p
    | Shared_Material_Goal q r M \<Rightarrow> False)"

definition shared_same :: "('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "shared_same h' h = (case shared_entry_goal h of
      Shared_Call_Goal q r d p \<Rightarrow> (case shared_entry_goal h' of Shared_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p
        | Shared_Material_Goal q' r' M \<Rightarrow> False)
    | Shared_Material_Goal q r M \<Rightarrow> False)"

text \<open>
  A collapsed pattern without variables is a reference, and two references of a formed table are equal exactly when
  their projections are: a collapsed pattern projects to a ground call exactly when it is that call's reference.
\<close>

lemma collapsed_ground_project_eq:
  fixes p q :: "'v shared_pattern"
  assumes tf: "table_formed T" and p: "shared_pattern_formed T p" "shared_collapsed p"
    and pv: "shared_pattern_variables p = {||}" and q: "shared_pattern_formed T q" "shared_collapsed q"
  shows "shared_pattern_project T q = shared_pattern_project T p \<longleftrightarrow> q = p"
proof
  assume eq: "shared_pattern_project T q = shared_pattern_project T p"
  obtain i where i: "p = Shared_Ground i" using shared_collapsed_ground[OF p(2) pv] by blast
  have "shared_pattern_variables q = {||}"
    using eq pv shared_pattern_variables_project[OF p(1)] shared_pattern_variables_project[OF q(1)] by simp
  then obtain j where j: "q = Shared_Ground j" using shared_collapsed_ground[OF q(2)] by blast
  have fj: "shared_pattern_formed T (Shared_Ground j :: 'v shared_pattern)" using q(1) j by simp
  have fi: "shared_pattern_formed T (Shared_Ground i :: 'v shared_pattern)" using p(1) i by simp
  have e2: "shared_pattern_project T (Shared_Ground j :: 'v shared_pattern) =
      shared_pattern_project T (Shared_Ground i :: 'v shared_pattern)"
    using eq i j by (simp only:)
  have "j = i" using shared_ground_equality[OF tf fj fi] e2 by blast
  then show "q = p" using i j by simp
qed simp

section \<open>The access of a shared search state\<close>

definition shared_access :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) search_access" where
  "shared_access \<kappa> P r = (let s = search_state r; T = shared_state_table s in
    \<lparr>access_goals = tree_values (shared_goals s),
     access_goals_at = \<lambda>q. option_fset (RBT.lookup (shared_goals s) q),
     access_nodes_at = \<lambda>q. option_fset (RBT.lookup (shared_nodes s) q),
     access_goal = \<lambda>h. shared_goal_project T (shared_entry_goal h),
     access_node = \<lambda>hn. shared_derivation_project T (shared_entry_node hn),
     access_goal_position = \<lambda>h. shared_goal_position (shared_entry_goal h),
     access_node_position = \<lambda>hn. shared_derivation_position (shared_entry_node hn),
     access_variables = \<lambda>h. shared_goal_variables (shared_entry_goal h),
     access_alternatives = shared_entry_alternatives,
     access_is_call = \<lambda>h. shared_goal_is_call (shared_entry_goal h),
     access_solvable = \<lambda>h. shared_goal_solvable T (shared_entry_goal h),
     access_leaf = \<lambda>h. shared_goal_leaf (shared_entry_goal h),
     access_key = \<lambda>h. shared_call_key (shared_entry_goal h),
     access_closes = shared_closes,
     access_same = shared_same,
     access_goal_calls = tree_bucket (shared_goal_calls s),
     access_node_calls = tree_bucket (shared_node_calls s),
     access_open = tree_count (shared_open s),
     access_holders = tree_bucket (shared_holders s),
     access_free = \<lambda>hn. shared_free_registered \<kappa> (shared_entry_node hn),
     access_value_none = \<lambda>hn a. a |\<in>| tree_bucket (shared_unconstructed s) (shared_derivation_position (shared_entry_node hn))
       \<or> search_value \<kappa> P r (shared_entry_node hn) a = None,
     access_registered = fset_of_list (RBT.keys (search_registered r)),
     access_holdable = \<lambda>h. shared_goal_registered h \<noteq> {||},
     access_witnesses = shared_witnesses s\<rparr>)"

lemma shared_access_simps:
  "access_goals (shared_access \<kappa> P r) = tree_values (shared_goals (search_state r))"
  "access_goals_at (shared_access \<kappa> P r) q = option_fset (RBT.lookup (shared_goals (search_state r)) q)"
  "access_nodes_at (shared_access \<kappa> P r) q = option_fset (RBT.lookup (shared_nodes (search_state r)) q)"
  "access_goal (shared_access \<kappa> P r) h = shared_goal_project (search_table r) (shared_entry_goal h)"
  "access_node (shared_access \<kappa> P r) hn = shared_derivation_project (search_table r) (shared_entry_node hn)"
  "access_goal_position (shared_access \<kappa> P r) h = shared_goal_position (shared_entry_goal h)"
  "access_node_position (shared_access \<kappa> P r) hn = shared_derivation_position (shared_entry_node hn)"
  "access_variables (shared_access \<kappa> P r) h = shared_goal_variables (shared_entry_goal h)"
  "access_alternatives (shared_access \<kappa> P r) h = shared_entry_alternatives h"
  "access_is_call (shared_access \<kappa> P r) h = shared_goal_is_call (shared_entry_goal h)"
  "access_solvable (shared_access \<kappa> P r) h = shared_goal_solvable (search_table r) (shared_entry_goal h)"
  "access_leaf (shared_access \<kappa> P r) h = shared_goal_leaf (shared_entry_goal h)"
  "access_key (shared_access \<kappa> P r) h = shared_call_key (shared_entry_goal h)"
  "access_closes (shared_access \<kappa> P r) = shared_closes"
  "access_same (shared_access \<kappa> P r) = shared_same"
  "access_goal_calls (shared_access \<kappa> P r) = tree_bucket (shared_goal_calls (search_state r))"
  "access_node_calls (shared_access \<kappa> P r) = tree_bucket (shared_node_calls (search_state r))"
  "access_open (shared_access \<kappa> P r) = tree_count (shared_open (search_state r))"
  "access_holders (shared_access \<kappa> P r) = tree_bucket (shared_holders (search_state r))"
  "access_free (shared_access \<kappa> P r) hn = shared_free_registered \<kappa> (shared_entry_node hn)"
  "access_value_none (shared_access \<kappa> P r) hn a \<longleftrightarrow>
    a |\<in>| tree_bucket (shared_unconstructed (search_state r)) (shared_derivation_position (shared_entry_node hn)) \<or>
    search_value \<kappa> P r (shared_entry_node hn) a = None"
  "access_registered (shared_access \<kappa> P r) = fset_of_list (RBT.keys (search_registered r))"
  "access_holdable (shared_access \<kappa> P r) h \<longleftrightarrow> shared_goal_registered h \<noteq> {||}"
  "access_witnesses (shared_access \<kappa> P r) = shared_witnesses (search_state r)"
  by (simp_all add: shared_access_def Let_def)

lemma shared_goal_lookup_position:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_goals s) q = Some h"
  shows "shared_goal_position (shared_entry_goal h) = q"
  using shared_entries_formed(1)[OF s at] by (simp add: goal_entry_formed_def)

lemma shared_node_lookup_position:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_nodes s) q = Some hn"
  shows "shared_derivation_position (shared_entry_node hn) = q"
  using shared_entries_formed(2)[OF s at] by (simp add: node_entry_formed_def)

theorem shared_access_formed:
  assumes r: "search_formed \<kappa> P r"
  shows "access_formed \<kappa> P (shared_access \<kappa> P r) (search_project r)"
proof -
  let ?s = "search_state r" let ?T = "search_table r"
  have s: "shared_state_formed \<kappa> P ?s" and reg: "search_registered_formed r" and vf: "search_values_formed \<kappa> P r"
    using search_formedD[OF r] by simp_all
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have gpos: "\<And>q h. RBT.lookup (shared_goals ?s) q = Some h \<Longrightarrow> shared_goal_position (shared_entry_goal h) = q"
    by (rule shared_goal_lookup_position[OF s])
  have npos: "\<And>q hn. RBT.lookup (shared_nodes ?s) q = Some hn \<Longrightarrow> shared_derivation_position (shared_entry_node hn) = q"
    by (rule shared_node_lookup_position[OF s])
  have gf: "\<And>q h. RBT.lookup (shared_goals ?s) q = Some h \<Longrightarrow> goal_entry_formed P ?T q h"
    by (rule shared_entries_formed(1)[OF s])
  have nf: "\<And>q hn. RBT.lookup (shared_nodes ?s) q = Some hn \<Longrightarrow> node_entry_formed ?T q hn"
    by (rule shared_entries_formed(2)[OF s])
  have rec: "\<And>q. shared_recorded_at ?s q" using s by (simp add: shared_state_formed_def)
  have goal_values: "h |\<in>| tree_values (shared_goals ?s) \<longleftrightarrow>
      RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h" for h
    using gpos by (auto simp: tree_values_member)
  have galt: "h |\<in>| option_fset (RBT.lookup (shared_goals ?s) q) \<longleftrightarrow> RBT.lookup (shared_goals ?s) q = Some h" for h q
    by (cases "RBT.lookup (shared_goals ?s) q") auto
  have nalt: "hn |\<in>| option_fset (RBT.lookup (shared_nodes ?s) q) \<longleftrightarrow> RBT.lookup (shared_nodes ?s) q = Some hn" for hn q
    by (cases "RBT.lookup (shared_nodes ?s) q") auto
  show ?thesis
  proof (unfold_locales, unfold shared_access_simps galt nalt goal_values)
    show "resolution_pending (search_project r) =
        fimage (\<lambda>h. shared_goal_project ?T (shared_entry_goal h)) (tree_values (shared_goals ?s))"
      by (simp add: shared_state_project_fields)
  next
    fix h q
    show "RBT.lookup (shared_goals ?s) q = Some h \<longleftrightarrow>
        RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h \<and>
        shared_goal_position (shared_entry_goal h) = q"
      using gpos by auto
  next
    fix h h'
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and h': "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h')) = Some h'"
      and eq: "shared_goal_project ?T (shared_entry_goal h) = shared_goal_project ?T (shared_entry_goal h')"
    have p: "shared_goal_position (shared_entry_goal h) = shared_goal_position (shared_entry_goal h')"
      using arg_cong[OF eq, of resolution_goal_position] by (simp only: shared_goal_project_position)
    have "Some h = Some h'" using h h' p by metis
    then show "h = h'" by simp
  next
    fix h show "shared_goal_position (shared_entry_goal h) =
        resolution_goal_position (shared_goal_project ?T (shared_entry_goal h))" by simp
  next
    fix h assume "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
    from goal_entry_variables[OF gf[OF this]]
    show "shared_goal_variables (shared_entry_goal h) =
        resolution_goal_variables (shared_goal_project ?T (shared_entry_goal h))" .
  next
    fix h assume "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
    from gf[OF this] show "shared_entry_alternatives h =
        finite_goal_alternatives P (shared_goal_project ?T (shared_entry_goal h))"
      by (simp add: goal_entry_formed_def)
  next
    fix h show "shared_goal_is_call (shared_entry_goal h) \<longleftrightarrow>
        resolution_is_call (shared_goal_project ?T (shared_entry_goal h))"
      by (cases "shared_entry_goal h") simp_all
  next
    fix h show "shared_goal_solvable ?T (shared_entry_goal h) \<longleftrightarrow>
        finite_solvable_material_goal (shared_goal_project ?T (shared_entry_goal h))"
      by (cases "shared_entry_goal h") simp_all
  next
    fix h show "shared_goal_leaf (shared_entry_goal h) \<longleftrightarrow>
        finite_leaf_call_goal (shared_goal_project ?T (shared_entry_goal h))"
      by (cases "shared_entry_goal h") (simp_all add: shared_has_leaf[of _ ?T])
  next
    fix h assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and held: "finite_held \<kappa> (search_project r) (shared_goal_project ?T (shared_entry_goal h))"
    obtain p a where "((p,True),a) |\<in>| resolution_goal_variables (shared_goal_project ?T (shared_entry_goal h))"
      using held unfolding finite_held_def by (elim fBexE) blast
    then have "((p,True),a) |\<in>| shared_goal_variables (shared_entry_goal h)"
      using goal_entry_variables[OF gf[OF h]] by simp
    then show "shared_goal_registered h \<noteq> {||}" using shared_goal_registered_member by blast
  next
    fix nd
    show "nd |\<in>| resolution_nodes (search_project r) \<longleftrightarrow> (\<exists>hn. RBT.lookup (shared_nodes ?s) (resolution_node_position nd) = Some hn \<and>
        shared_derivation_project ?T (shared_entry_node hn) = nd)"
    proof
      assume "nd |\<in>| resolution_nodes (search_project r)"
      then obtain q hn where at: "RBT.lookup (shared_nodes ?s) q = Some hn"
        and e: "shared_derivation_project ?T (shared_entry_node hn) = nd"
        unfolding shared_state_project_member(2) by blast
      have "resolution_node_position nd = q" using e npos[OF at] by auto
      then show "\<exists>hn. RBT.lookup (shared_nodes ?s) (resolution_node_position nd) = Some hn \<and>
          shared_derivation_project ?T (shared_entry_node hn) = nd" using at e by blast
    next
      assume "\<exists>hn. RBT.lookup (shared_nodes ?s) (resolution_node_position nd) = Some hn \<and>
          shared_derivation_project ?T (shared_entry_node hn) = nd"
      then show "nd |\<in>| resolution_nodes (search_project r)" unfolding shared_state_project_member(2) by blast
    qed
  next
    fix hn q assume "RBT.lookup (shared_nodes ?s) q = Some hn"
    then show "shared_derivation_position (shared_entry_node hn) = q \<and>
        resolution_node_position (shared_derivation_project ?T (shared_entry_node hn)) = q"
      using npos by simp
  next
    fix hn q show "shared_free_registered \<kappa> (shared_entry_node hn) =
        finite_free_registered \<kappa> (shared_derivation_project ?T (shared_entry_node hn))"
      by (rule shared_free_registered)
  next
    fix hn q a assume at: "RBT.lookup (shared_nodes ?s) q = Some hn"
    have u: "a |\<in>| tree_bucket (shared_unconstructed ?s) q \<Longrightarrow>
        finite_registered_value \<kappa> P (shared_derivation_project ?T (shared_entry_node hn)) a = None"
      using s at by (auto simp: shared_state_formed_def)
    show "a |\<in>| tree_bucket (shared_unconstructed ?s) (shared_derivation_position (shared_entry_node hn)) \<or>
        search_value \<kappa> P r (shared_entry_node hn) a = None \<longleftrightarrow>
        finite_registered_value \<kappa> P (shared_derivation_project ?T (shared_entry_node hn)) a = None"
      using u npos[OF at] search_value[OF vf] by auto
  next
    fix h q rr d p hn q'
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and g: "shared_goal_project ?T (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
      and ground: "finite_pattern_variables p = {||}" and n: "RBT.lookup (shared_nodes ?s) q' = Some hn"
    obtain ps where e: "shared_entry_goal h = Shared_Call_Goal q rr d ps" and pp: "shared_pattern_project ?T ps = p"
      using g by (cases "shared_entry_goal h") auto
    have psf: "shared_pattern_formed ?T ps" "shared_collapsed ps"
      using gf[OF h] e by (simp_all add: goal_entry_formed_def)
    have psv: "shared_pattern_variables ps = {||}" using shared_pattern_variables_project[OF psf(1)] pp ground by simp
    have cf: "shared_pattern_formed ?T (shared_derivation_call (shared_entry_node hn))"
        "shared_collapsed (shared_derivation_call (shared_entry_node hn))"
      using nf[OF n] by (simp_all add: node_entry_formed_def shared_derivation_formed_def)
    note eqv = collapsed_ground_project_eq[OF tf psf psv cf]
    show "shared_closes hn h \<longleftrightarrow> resolution_node_site (shared_derivation_project ?T (shared_entry_node hn)) = d \<and>
        resolution_node_call (shared_derivation_project ?T (shared_entry_node hn)) = p"
      using eqv pp e by (auto simp: shared_closes_def shared_derivation_project_def)
  next
    fix h q rr d p hn q'
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and g: "shared_goal_project ?T (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
      and ground: "finite_pattern_variables p = {||}" and n: "RBT.lookup (shared_nodes ?s) q' = Some hn"
      and c: "shared_closes hn h"
    obtain ps where e: "shared_entry_goal h = Shared_Call_Goal q rr d ps" and pp: "shared_pattern_project ?T ps = p"
      using g by (cases "shared_entry_goal h") auto
    have psf: "shared_pattern_formed ?T ps" "shared_collapsed ps"
      using gf[OF h] e by (simp_all add: goal_entry_formed_def)
    have psv: "shared_pattern_variables ps = {||}" using shared_pattern_variables_project[OF psf(1)] pp ground by simp
    obtain i where i: "ps = Shared_Ground i" using shared_collapsed_ground[OF psf(2) psv] by blast
    have call: "shared_derivation_call (shared_entry_node hn) = Shared_Ground i" using c e i by (simp add: shared_closes_def)
    have "q' |\<in>| tree_bucket (shared_node_calls ?s) i"
    proof -
      have "i |\<in>| shared_call_refs (shared_derivation_call (shared_entry_node hn))" using call by simp
      then show ?thesis using rec[of q'] n unfolding shared_recorded_at_def by blast
    qed
    then show "q' |\<in>| tree_bucket (shared_node_calls ?s) (shared_call_key (shared_entry_goal h))" using e i by simp
  next
    fix h h' q rr d p
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and h': "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h')) = Some h'"
      and g: "shared_goal_project ?T (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
      and ground: "finite_pattern_variables p = {||}"
    obtain ps where e: "shared_entry_goal h = Shared_Call_Goal q rr d ps" and pp: "shared_pattern_project ?T ps = p"
      using g by (cases "shared_entry_goal h") auto
    have psf: "shared_pattern_formed ?T ps" "shared_collapsed ps"
      using gf[OF h] e by (simp_all add: goal_entry_formed_def)
    have psv: "shared_pattern_variables ps = {||}" using shared_pattern_variables_project[OF psf(1)] pp ground by simp
    show "shared_same h' h \<longleftrightarrow> (case shared_goal_project ?T (shared_entry_goal h') of
        Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    proof (cases "shared_entry_goal h'")
      case (Shared_Call_Goal q' r' d' ps')
      have cf: "shared_pattern_formed ?T ps'" "shared_collapsed ps'"
        using gf[OF h'] Shared_Call_Goal by (simp_all add: goal_entry_formed_def)
      show ?thesis using collapsed_ground_project_eq[OF tf psf psv cf] pp e Shared_Call_Goal
        by (auto simp: shared_same_def)
    qed (simp add: shared_same_def e)
  next
    fix h h' q rr d p
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and h': "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h')) = Some h'"
      and g: "shared_goal_project ?T (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
      and ground: "finite_pattern_variables p = {||}" and sm: "shared_same h' h"
    obtain ps where e: "shared_entry_goal h = Shared_Call_Goal q rr d ps" and pp: "shared_pattern_project ?T ps = p"
      using g by (cases "shared_entry_goal h") auto
    have psf: "shared_pattern_formed ?T ps" "shared_collapsed ps"
      using gf[OF h] e by (simp_all add: goal_entry_formed_def)
    have psv: "shared_pattern_variables ps = {||}" using shared_pattern_variables_project[OF psf(1)] pp ground by simp
    obtain i where i: "ps = Shared_Ground i" using shared_collapsed_ground[OF psf(2) psv] by blast
    obtain q' r' where e': "shared_entry_goal h' = Shared_Call_Goal q' r' d (Shared_Ground i)"
      using sm e i by (cases "shared_entry_goal h'") (auto simp: shared_same_def)
    have "shared_goal_position (shared_entry_goal h') |\<in>| tree_bucket (shared_goal_calls ?s) i"
    proof -
      have "i |\<in>| shared_goal_call_refs (shared_entry_goal h')" using e' by simp
      then show ?thesis using rec[of "shared_goal_position (shared_entry_goal h')"] h'
        unfolding shared_recorded_at_def by blast
    qed
    then show "shared_goal_position (shared_entry_goal h') |\<in>|
        tree_bucket (shared_goal_calls ?s) (shared_call_key (shared_entry_goal h))" using e i by simp
  next
    fix nd assume nd: "nd |\<in>| resolution_nodes (search_project r)"
    have c: "tree_count (shared_open ?s) p = card (tree_keys_under (shared_goals ?s) p)" for p
      using s by (simp add: shared_state_formed_def)
    have "tree_count (shared_open ?s) (resolution_node_position nd) = 0 \<longleftrightarrow>
        tree_keys_under (shared_goals ?s) (resolution_node_position nd) = {}"
      by (simp add: c card_0_eq[OF tree_keys_under_finite])
    also have "\<dots> \<longleftrightarrow> \<not> fBex (resolution_pending (search_project r)) (\<lambda>g.
        take (length (resolution_node_position nd)) (resolution_goal_position g) = resolution_node_position nd)"
    proof -
      let ?p = "resolution_node_position nd"
      have "(\<exists>q. RBT.lookup (shared_goals ?s) q \<noteq> None \<and> take (length ?p) q = ?p) \<longleftrightarrow>
          fBex (resolution_pending (search_project r)) (\<lambda>g. take (length ?p) (resolution_goal_position g) = ?p)"
      proof
        assume "\<exists>q. RBT.lookup (shared_goals ?s) q \<noteq> None \<and> take (length ?p) q = ?p"
        then obtain q h where q: "RBT.lookup (shared_goals ?s) q = Some h" "take (length ?p) q = ?p" by auto
        have m: "shared_goal_project ?T (shared_entry_goal h) |\<in>| resolution_pending (search_project r)"
          unfolding shared_state_project_member(1) using q(1) by blast
        have "resolution_goal_position (shared_goal_project ?T (shared_entry_goal h)) = q" using gpos[OF q(1)] by simp
        then show "fBex (resolution_pending (search_project r)) (\<lambda>g. take (length ?p) (resolution_goal_position g) = ?p)"
          using m q(2) by blast
      next
        assume "fBex (resolution_pending (search_project r)) (\<lambda>g. take (length ?p) (resolution_goal_position g) = ?p)"
        then obtain g where g: "g |\<in>| resolution_pending (search_project r)"
          "take (length ?p) (resolution_goal_position g) = ?p" by blast
        then obtain q h where at: "RBT.lookup (shared_goals ?s) q = Some h"
          and e: "shared_goal_project ?T (shared_entry_goal h) = g"
          unfolding shared_state_project_member(1) by blast
        have "resolution_goal_position g = q" using e gpos[OF at] by auto
        then show "\<exists>q. RBT.lookup (shared_goals ?s) q \<noteq> None \<and> take (length ?p) q = ?p" using at g(2) by auto
      qed
      then show ?thesis unfolding tree_keys_under_def Collect_empty_eq by blast
    qed
    finally show "tree_count (shared_open ?s) (resolution_node_position nd) = 0 \<longleftrightarrow>
        finite_solved_node (search_project r) nd"
      by (simp add: finite_solved_node_def)
  next
    fix h x
    assume h: "RBT.lookup (shared_goals ?s) (shared_goal_position (shared_entry_goal h)) = Some h"
      and x: "x |\<in>| shared_goal_variables (shared_entry_goal h)"
    show "shared_goal_position (shared_entry_goal h) |\<in>| tree_bucket (shared_holders ?s) (fst (fst x))"
      using rec[of "shared_goal_position (shared_entry_goal h)"] h x unfolding shared_recorded_at_def by blast
  next
    fix g z b
    assume g: "g |\<in>| resolution_pending (search_project r)"
      and x: "((z,True),b) |\<in>| resolution_goal_variables g"
    obtain q h where at: "RBT.lookup (shared_goals ?s) q = Some h" and gh: "shared_goal_project ?T (shared_entry_goal h) = g"
      using g by (auto simp: shared_state_project_member(1))
    have "((z,True),b) |\<in>| shared_goal_variables (shared_entry_goal h)" using x gh goal_entry_variables[OF gf[OF at]] by simp
    then have "z |\<in>| shared_goal_registered h" using shared_goal_registered_member by blast
    then have "q |\<in>| tree_bucket (search_registered r) z" using reg at by (simp add: search_registered_formed_def)
    then obtain G where G: "RBT.lookup (search_registered r) z = Some G"
      unfolding tree_bucket_def by (auto split: option.splits)
    have "z \<in> set (RBT.keys (search_registered r))" using G RBT.lookup_keys[of "search_registered r"] by (metis domI)
    then show "z |\<in>| fset_of_list (RBT.keys (search_registered r))" by (simp add: fset_of_list.rep_eq)
  next
    show "shared_witnesses ?s = resolution_witnesses (search_project r)" by (simp add: shared_state_project_fields)
  qed
qed

section \<open>Steps over the shared search state\<close>

text \<open>
  Every step changes the goal at one position through (a)'s operations, and moves that position between the buckets
  of the registered positions of the goal it leaves and of the goal it enters, as F2b2 (c) moves it. The table only
  extends, so every kept value stays the value at its node.
\<close>

definition search_update :: "'s list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_update q s' r = r\<lparr>search_state := s', search_registered := tree_move q
    (option_registered (RBT.lookup (shared_goals (search_state r)) q)) (option_registered (RBT.lookup (shared_goals s') q))
    (search_registered r)\<rparr>"

lemma search_values_extends:
  assumes v: "search_values_formed \<kappa> P r" and tf: "table_formed (search_table r)"
    and ext: "table_extends (search_table r) (shared_state_table s')"
  shows "search_values_formed \<kappa> P (r\<lparr>search_state := s', search_registered := t\<rparr>)"
  unfolding search_values_formed_def
proof (intro allI impI)
  fix p z assume "z |\<in>| tree_bucket (search_values (r\<lparr>search_state := s', search_registered := t\<rparr>)) p"
  then have z0: "z |\<in>| tree_bucket (search_values r) p" by simp
  have f: "shared_derivation_formed (search_table r) (fst z)"
    and val: "finite_registered_value \<kappa> P (shared_derivation_project (search_table r) (fst z)) (fst (snd z)) = Some (snd (snd z))"
    using v z0 unfolding search_values_formed_def by blast+
  note e = shared_derivation_extends[OF tf f ext]
  show "shared_derivation_formed (search_table (r\<lparr>search_state := s', search_registered := t\<rparr>)) (fst z) \<and>
      finite_registered_value \<kappa> P (shared_derivation_project (search_table (r\<lparr>search_state := s', search_registered := t\<rparr>)) (fst z))
        (fst (snd z)) = Some (snd (snd z))"
    using e val by simp
qed

theorem search_update:
  assumes r: "search_formed \<kappa> P r" and s': "shared_state_formed \<kappa> P s'"
    and ext: "table_extends (search_table r) (shared_state_table s')"
    and same: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals (search_state r)) p"
  shows "search_formed \<kappa> P (search_update q s' r)"
proof -
  have reg: "search_registered_formed r" and v: "search_values_formed \<kappa> P r" and s: "shared_state_formed \<kappa> P (search_state r)"
    using search_formedD[OF r] by simp_all
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  let ?A = "option_registered (RBT.lookup (shared_goals (search_state r)) q)"
  let ?B = "option_registered (RBT.lookup (shared_goals s') q)"
  have rf: "search_registered_formed (search_update q s' r)"
    unfolding search_registered_formed_def
  proof (intro allI impI)
    fix p h z assume at: "RBT.lookup (shared_goals (search_state (search_update q s' r))) p = Some h"
      and z: "z |\<in>| shared_goal_registered h"
    have at': "RBT.lookup (shared_goals s') p = Some h" using at by (simp add: search_update_def)
    show "p |\<in>| tree_bucket (search_registered (search_update q s' r)) z"
    proof (cases "p = q")
      case True
      then have "z |\<in>| ?B" using at' z by (simp add: option_registered_def)
      then show ?thesis using True by (simp add: search_update_def tree_move)
    next
      case False
      then have "RBT.lookup (shared_goals (search_state r)) p = Some h" using at' same[OF False] by simp
      then have "p |\<in>| tree_bucket (search_registered r) z" using reg z by (simp add: search_registered_formed_def)
      then show ?thesis using False by (simp add: search_update_def tree_move)
    qed
  qed
  have vf: "search_values_formed \<kappa> P (search_update q s' r)"
    unfolding search_update_def by (rule search_values_extends[OF v tf ext])
  show ?thesis using s' rf vf by (simp add: search_formed_def search_update_def)
qed

lemma search_update_fields [simp]:
  "search_state (search_update q s' r) = s'" "search_values (search_update q s' r) = search_values r"
  by (simp_all add: search_update_def)

definition search_put_goal :: "'s list \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_put_goal q h r = search_update q (shared_put_goal q h (search_state r)) r"

definition search_remove_goal :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_remove_goal q r = search_update q (shared_remove_goal q (search_state r)) r"

definition search_put_node :: "'s list \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_put_node q hn r = r\<lparr>search_state := shared_put_node q hn (search_state r)\<rparr>"

lemma search_put_goal:
  assumes r: "search_formed \<kappa> P r" and h: "goal_entry_formed P (search_table r) q h"
    and free: "RBT.lookup (shared_goals (search_state r)) q = None"
  shows "search_formed \<kappa> P (search_put_goal q h r)"
    and "search_state (search_put_goal q h r) = shared_put_goal q h (search_state r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  show "search_formed \<kappa> P (search_put_goal q h r)" unfolding search_put_goal_def
    by (rule search_update[OF r shared_put_goal(1)[OF s h free]]) (simp_all add: shared_put_goal_def)
  show "search_state (search_put_goal q h r) = shared_put_goal q h (search_state r)" by (simp add: search_put_goal_def)
qed

lemma search_remove_goal:
  assumes r: "search_formed \<kappa> P r" and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
  shows "search_formed \<kappa> P (search_remove_goal q r)"
    and "search_state (search_remove_goal q r) = shared_remove_goal q (search_state r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  show "search_formed \<kappa> P (search_remove_goal q r)" unfolding search_remove_goal_def
    by (rule search_update[OF r shared_remove_goal(1)[OF s at]]) (simp_all add: shared_remove_goal_def)
  show "search_state (search_remove_goal q r) = shared_remove_goal q (search_state r)" by (simp add: search_remove_goal_def)
qed

lemma search_put_node:
  assumes r: "search_formed \<kappa> P r" and hn: "node_entry_formed (search_table r) q hn"
    and free: "RBT.lookup (shared_nodes (search_state r)) q = None"
  shows "search_formed \<kappa> P (search_put_node q hn r)"
    and "search_state (search_put_node q hn r) = shared_put_node q hn (search_state r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" and reg: "search_registered_formed r"
    and v: "search_values_formed \<kappa> P r" using search_formedD[OF r] by simp_all
  have s': "shared_state_formed \<kappa> P (shared_put_node q hn (search_state r))" by (rule shared_put_node(1)[OF s hn free])
  have g: "\<And>p. RBT.lookup (shared_goals (shared_put_node q hn (search_state r))) p = RBT.lookup (shared_goals (search_state r)) p"
    and t: "shared_sharing (shared_put_node q hn (search_state r)) = shared_sharing (search_state r)"
    by (simp_all add: shared_put_node_def)
  have rf: "search_registered_formed (search_put_node q hn r)"
    using reg g by (simp add: search_registered_formed_def search_put_node_def)
  have tb: "search_table (search_put_node q hn r) = search_table r" using t by (simp add: search_put_node_def)
  have vv: "search_values (search_put_node q hn r) = search_values r" by (simp add: search_put_node_def)
  have vf: "search_values_formed \<kappa> P (search_put_node q hn r)" using v unfolding search_values_formed_def tb vv .
  show "search_formed \<kappa> P (search_put_node q hn r)" using s' rf vf by (simp add: search_formed_def search_put_node_def)
  show "search_state (search_put_node q hn r) = shared_put_node q hn (search_state r)" by (simp add: search_put_node_def)
qed

subsection \<open>Substitution\<close>

definition search_substitute_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_substitute_at P \<sigma> D q r = search_update q (shared_substitute_at P \<sigma> D q (search_state r)) r"

definition search_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_substitute P \<sigma> D r =
    fold (search_substitute_at P \<sigma> D) (sorted_list_of_fset (shared_substitute_positions D (search_state r))) r"

lemma search_substitute_state:
  "search_state (fold (search_substitute_at P \<sigma> D) qs r) = fold (shared_substitute_at P \<sigma> D) qs (search_state r)"
  by (induction qs arbitrary: r) (simp_all add: search_substitute_at_def)

lemma search_substitute_fold:
  assumes r: "search_formed \<kappa> P r" and tf0: "table_formed T0" and ext: "table_extends T0 (search_table r)"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_formed \<kappa> P (fold (search_substitute_at P \<sigma> D) qs r) \<and>
    table_extends T0 (search_table (fold (search_substitute_at P \<sigma> D) qs r))"
  using r ext
proof (induction qs arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF Cons.prems(1)] by simp
  have \<sigma>t: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)"
    using shared_pattern_extends(1)[OF tf0 \<sigma>f Cons.prems(2)] .
  note k = shared_substitute_at[where D = D and q = q, OF s \<sigma>t \<sigma>c out]
  have f1: "search_formed \<kappa> P (search_substitute_at P \<sigma> D q r)"
    unfolding search_substitute_at_def by (rule search_update[OF Cons.prems(1) k(1) k(2) k(3)])
  have e1: "table_extends T0 (search_table (search_substitute_at P \<sigma> D q r))"
    using table_extends_trans[OF Cons.prems(2) k(2)] by (simp add: search_substitute_at_def)
  show ?case using Cons.IH[OF f1 e1] by simp
qed

theorem search_substitute:
  assumes r: "search_formed \<kappa> P r"
    and \<sigma>f: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_formed \<kappa> P (search_substitute P \<sigma> D r)"
    and "table_extends (search_table r) (search_table (search_substitute P \<sigma> D r))"
    and "search_project (search_substitute P \<sigma> D r) =
      resolution_state_substitute (\<lambda>a. shared_pattern_project (search_table r) (\<sigma> a)) (search_project r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  note f = search_substitute_fold[OF r tf table_extends_refl \<sigma>f \<sigma>c out]
  show "search_formed \<kappa> P (search_substitute P \<sigma> D r)" using f by (simp add: search_substitute_def)
  show "table_extends (search_table r) (search_table (search_substitute P \<sigma> D r))" using f by (simp add: search_substitute_def)
  have "search_state (search_substitute P \<sigma> D r) = shared_state_substitute P \<sigma> D (search_state r)"
    by (simp add: search_substitute_def search_substitute_state shared_state_substitute_def)
  then show "search_project (search_substitute P \<sigma> D r) =
      resolution_state_substitute (\<lambda>a. shared_pattern_project (search_table r) (\<sigma> a)) (search_project r)"
    using shared_state_substitute(3)[OF s \<sigma>f \<sigma>c out] by simp
qed

subsection \<open>A plain substitution, its ground terms shared first\<close>

text \<open>
  A substitution of R3's patterns is shared into the table: the ground terms of its values are shared once, in their
  order, and each value is read against the resulting state, collapsed. Its projection is the plain substitution.
\<close>

definition plain_grounds :: "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> finite_factor_term fset" where
  "plain_grounds \<tau> D = ffUnion (fimage (\<lambda>a. pattern_grounds (\<tau> a)) D)"

definition search_reshare :: "finite_factor_term fset \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_reshare G r = r\<lparr>search_state := shared_reshare (keyed_share_grounds G (shared_sharing (search_state r))) (search_state r)\<rparr>"

lemma search_reshare:
  assumes r: "search_formed \<kappa> P r"
  shows "search_formed \<kappa> P (search_reshare G r)" and "search_project (search_reshare G r) = search_project r"
    and "table_extends (search_table r) (search_table (search_reshare G r))"
    and "\<And>t. t |\<in>| G \<Longrightarrow> table_holds (search_table (search_reshare G r)) t"
    and "shared_goals (search_state (search_reshare G r)) = shared_goals (search_state r)"
    and "shared_nodes (search_state (search_reshare G r)) = shared_nodes (search_state r)"
    and "shared_sharing (search_state (search_reshare G r)) = keyed_share_grounds G (shared_sharing (search_state r))"
proof -
  let ?x = "keyed_share_grounds G (shared_sharing (search_state r))"
  have s: "shared_state_formed \<kappa> P (search_state r)" and reg: "search_registered_formed r" and v: "search_values_formed \<kappa> P r"
    using search_formedD[OF r] by simp_all
  have x0: "share_state_formed (shared_sharing (search_state r))" using shared_entries_formed(3)[OF s] .
  note k = keyed_share_grounds[where G = G, OF x0]
  have tb: "search_table (search_reshare G r) = share_state_table ?x"
    by (simp add: search_reshare_def shared_reshare_def)
  note e = shared_reshare[OF s k(1) k(2)]
  show "table_extends (search_table r) (search_table (search_reshare G r))" using k(2) tb by simp
  show "\<And>t. t |\<in>| G \<Longrightarrow> table_holds (search_table (search_reshare G r)) t" using k(3) tb by simp
  show "shared_goals (search_state (search_reshare G r)) = shared_goals (search_state r)"
    "shared_nodes (search_state (search_reshare G r)) = shared_nodes (search_state r)"
    "shared_sharing (search_state (search_reshare G r)) = ?x"
    by (simp_all add: search_reshare_def shared_reshare_def)
  show "search_project (search_reshare G r) = search_project r" using e(2) by (simp add: search_reshare_def)
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have vf: "search_values_formed \<kappa> P (r\<lparr>search_state := shared_reshare ?x (search_state r), search_registered := search_registered r\<rparr>)"
    by (rule search_values_extends[OF v tf]) (simp add: shared_reshare_def k(2))
  have rf: "search_registered_formed (search_reshare G r)"
    using reg by (simp add: search_registered_formed_def search_reshare_def shared_reshare_def)
  show "search_formed \<kappa> P (search_reshare G r)"
    using e(1) rf vf by (simp add: search_formed_def search_reshare_def)
qed

definition search_substitute_plain :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_substitute_plain P \<tau> D r = (let r1 = search_reshare (plain_grounds \<tau> D) r in
    search_substitute P (\<lambda>a. keyed_pattern_at (shared_sharing (search_state r1)) (\<tau> a)) D r1)"

theorem search_substitute_plain:
  assumes r: "search_formed \<kappa> P r" and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<tau> a = Finite_Variable a"
  shows "search_formed \<kappa> P (search_substitute_plain P \<tau> D r)"
    and "search_project (search_substitute_plain P \<tau> D r) = resolution_state_substitute \<tau> (search_project r)"
    and "table_extends (search_table r) (search_table (search_substitute_plain P \<tau> D r))"
proof -
  let ?r1 = "search_reshare (plain_grounds \<tau> D) r"
  let ?x = "shared_sharing (search_state ?r1)" let ?T1 = "search_table ?r1"
  let ?\<sigma> = "\<lambda>a. keyed_pattern_at ?x (\<tau> a)"
  note h = search_reshare[where G = "plain_grounds \<tau> D", OF r]
  have s1: "shared_state_formed \<kappa> P (search_state ?r1)" using search_formedD[OF h(1)] by simp
  have x1: "share_state_formed ?x" using shared_entries_formed(3)[OF s1] .
  have rep: "keyed_state_represents ?x ?T1" and tf1: "table_formed ?T1" using share_state_formed_table[OF x1] by simp_all
  have held: "table_holds ?T1 t" if "t |\<in>| pattern_grounds (\<tau> a)" for a t
  proof (cases "a |\<in>| D")
    case True
    then have "t |\<in>| plain_grounds \<tau> D" using that by (auto simp: plain_grounds_def ffUnion.rep_eq fimage.rep_eq)
    then show ?thesis by (rule h(4))
  next
    case False
    then show ?thesis using that out[OF False] by simp
  qed
  have ex: "shared_pattern_formed ?T1 (?\<sigma> a) \<and> shared_pattern_project ?T1 (?\<sigma> a) = \<tau> a \<and> shared_collapsed (?\<sigma> a)" for a
    using keyed_pattern_at_exact[OF rep tf1] held[of _ a] by blast
  have out': "\<And>a. a |\<notin>| D \<Longrightarrow> ?\<sigma> a = Shared_Variable a" using out by simp
  note k = search_substitute[OF h(1), of ?\<sigma> D]
  have eq: "search_substitute_plain P \<tau> D r = search_substitute P ?\<sigma> D ?r1"
    by (simp add: search_substitute_plain_def Let_def)
  show "search_formed \<kappa> P (search_substitute_plain P \<tau> D r)" using k(1) ex out' eq by simp
  show "table_extends (search_table r) (search_table (search_substitute_plain P \<tau> D r))"
    using table_extends_trans[OF h(3) k(2)] ex out' eq by simp
  have "(\<lambda>a. shared_pattern_project ?T1 (?\<sigma> a)) = \<tau>" using ex by (simp add: fun_eq_iff)
  then show "search_project (search_substitute_plain P \<tau> D r) = resolution_state_substitute \<tau> (search_project r)"
    using k(3) ex out' eq h(2) by simp
qed

subsection \<open>F4: every value the construction returned is kept, computed once\<close>

text \<open>
  At each registered position the construction is asked, once, of every ready registered variable of the node there
  that has neither a kept value nor a place among the variables for which it returned nothing. A position holds one
  node, so the variables for which it returned nothing there are exactly F2b1's (review 770's follow-up 6).
\<close>

definition search_goal_holders :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry fset" where
  "search_goal_holders r x = ffilter (\<lambda>h. x |\<in>| shared_goal_variables (shared_entry_goal h))
    (ffUnion (fimage (\<lambda>q. option_fset (RBT.lookup (shared_goals (search_state r)) q))
      (tree_bucket (shared_holders (search_state r)) (fst (fst x)))))"

definition search_ready :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> 's list \<Rightarrow> 'a \<Rightarrow> bool" where
  "search_ready r p a = (let x = ((p,True),a); H = search_goal_holders r x in
    H \<noteq> {||} \<and> fBall H (\<lambda>h. shared_goal_variables (shared_entry_goal h) |\<subseteq>| {|x|}))"

lemma search_ready: "search_ready r p a = access_ready (shared_access \<kappa> P r) p a"
  by (simp add: search_ready_def search_goal_holders_def access_ready_def access_goal_holders_def shared_access_def Let_def)

definition search_refresh_at :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_refresh_at \<kappa> P p r = (case RBT.lookup (shared_nodes (search_state r)) p of None \<Rightarrow> r
    | Some hn \<Rightarrow> (let s = search_state r; nd = shared_entry_node hn;
        A = ffilter (\<lambda>a. search_ready r p a \<and> a |\<notin>| tree_bucket (shared_unconstructed s) p \<and>
          search_kept_value r nd a = None) (shared_free_registered \<kappa> nd);
        V = fimage (\<lambda>a. (a, finite_registered_value \<kappa> P (shared_derivation_project (search_table r) nd) a)) A;
        S = fimage (\<lambda>w. (nd, fst w, the (snd w))) (ffilter (\<lambda>w. snd w \<noteq> None) V);
        U = fimage fst (ffilter (\<lambda>w. snd w = None) V) in
      r\<lparr>search_state := s\<lparr>shared_unconstructed := (if U = {||} then shared_unconstructed s
          else RBT.insert p (tree_bucket (shared_unconstructed s) p |\<union>| U) (shared_unconstructed s))\<rparr>,
        search_values := (if S = {||} then search_values r
          else RBT.insert p (tree_bucket (search_values r) p |\<union>| S) (search_values r))\<rparr>))"

definition search_refresh :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_refresh \<kappa> P r = fold (search_refresh_at \<kappa> P) (RBT.keys (search_registered r)) r"

lemma search_refresh_at:
  assumes r: "search_formed \<kappa> P r"
  shows "search_formed \<kappa> P (search_refresh_at \<kappa> P p r) \<and> search_project (search_refresh_at \<kappa> P p r) = search_project r"
proof (cases "RBT.lookup (shared_nodes (search_state r)) p")
  case None
  then show ?thesis using r by (simp add: search_refresh_at_def)
next
  case (Some hn)
  let ?s = "search_state r" and ?nd = "shared_entry_node hn" and ?T = "search_table r"
  define A where "A = ffilter (\<lambda>a. search_ready r p a \<and> a |\<notin>| tree_bucket (shared_unconstructed ?s) p \<and>
    search_kept_value r ?nd a = None) (shared_free_registered \<kappa> ?nd)"
  define V where "V = fimage (\<lambda>a. (a, finite_registered_value \<kappa> P (shared_derivation_project ?T ?nd) a)) A"
  define S where "S = fimage (\<lambda>w. (?nd, fst w, the (snd w))) (ffilter (\<lambda>w. snd w \<noteq> None) V)"
  define U where "U = fimage fst (ffilter (\<lambda>w. snd w = None) V)"
  define Z where "Z = (if U = {||} then shared_unconstructed ?s
    else RBT.insert p (tree_bucket (shared_unconstructed ?s) p |\<union>| U) (shared_unconstructed ?s))"
  define W where "W = (if S = {||} then search_values r else RBT.insert p (tree_bucket (search_values r) p |\<union>| S) (search_values r))"
  have e: "search_refresh_at \<kappa> P p r = r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>"
    using Some by (simp add: search_refresh_at_def Let_def A_def V_def S_def U_def Z_def W_def)
  have s: "shared_state_formed \<kappa> P ?s" and reg: "search_registered_formed r" and v: "search_values_formed \<kappa> P r"
    using search_formedD[OF r] by simp_all
  have nf: "node_entry_formed ?T p hn" using shared_entries_formed(2)[OF s Some] .
  have Ua: "finite_registered_value \<kappa> P (shared_derivation_project ?T ?nd) a = None" if "a |\<in>| U" for a
    using that by (auto simp: U_def V_def ffilter.rep_eq fimage.rep_eq)
  have Sz: "fst z = ?nd \<and> finite_registered_value \<kappa> P (shared_derivation_project ?T (fst z)) (fst (snd z)) = Some (snd (snd z))"
    if "z |\<in>| S" for z
    using that by (auto simp: S_def V_def ffilter.rep_eq fimage.rep_eq)
  have u: "\<forall>q a hn'. a |\<in>| tree_bucket Z q \<longrightarrow> RBT.lookup (shared_nodes ?s) q = Some hn' \<longrightarrow>
      finite_registered_value \<kappa> P (shared_derivation_project ?T (shared_entry_node hn')) a = None"
  proof (intro allI impI)
    fix q a hn' assume a: "a |\<in>| tree_bucket Z q" and n: "RBT.lookup (shared_nodes ?s) q = Some hn'"
    show "finite_registered_value \<kappa> P (shared_derivation_project ?T (shared_entry_node hn')) a = None"
    proof (cases "q = p \<and> a |\<in>| U")
      case True
      then have "hn' = hn" using n Some by simp
      then show ?thesis using Ua True by simp
    next
      case False
      then have "a |\<in>| tree_bucket (shared_unconstructed ?s) q" using a by (auto simp: Z_def split: if_splits)
      then show ?thesis using s n unfolding shared_state_formed_def by blast
    qed
  qed
  have sf: "shared_state_formed \<kappa> P (?s\<lparr>shared_unconstructed := Z\<rparr>)"
    using s u unfolding shared_state_formed_def shared_recorded_at_def by simp
  have vf: "search_values_formed \<kappa> P (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)"
    unfolding search_values_formed_def
  proof (intro allI impI)
    fix q z assume z: "z |\<in>| tree_bucket (search_values (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)) q"
    have tb: "search_table (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>) = ?T" by simp
    show "shared_derivation_formed (search_table (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)) (fst z) \<and>
        finite_registered_value \<kappa> P (shared_derivation_project
          (search_table (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)) (fst z)) (fst (snd z)) =
        Some (snd (snd z))"
      unfolding tb
    proof (cases "q = p \<and> z |\<in>| S")
      case True
      then show "shared_derivation_formed ?T (fst z) \<and>
          finite_registered_value \<kappa> P (shared_derivation_project ?T (fst z)) (fst (snd z)) = Some (snd (snd z))"
      proof -
        have z1: "fst z = ?nd" using Sz[of z] True by blast
        have z2: "finite_registered_value \<kappa> P (shared_derivation_project ?T (fst z)) (fst (snd z)) = Some (snd (snd z))"
          using Sz[of z] True by blast
        show ?thesis using z2 nf unfolding z1 by (simp add: node_entry_formed_def)
      qed
    next
      case False
      then have z0: "z |\<in>| tree_bucket (search_values r) q" using z by (auto simp: W_def split: if_splits)
      show "shared_derivation_formed ?T (fst z) \<and>
          finite_registered_value \<kappa> P (shared_derivation_project ?T (fst z)) (fst (snd z)) = Some (snd (snd z))"
        using v z0 unfolding search_values_formed_def by blast
    qed
  qed
  have rf: "search_registered_formed (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)"
    using reg by (simp add: search_registered_formed_def)
  have pj: "shared_state_project (?s\<lparr>shared_unconstructed := Z\<rparr>) = shared_state_project ?s"
    by (simp add: shared_state_project_def)
  show ?thesis using e sf vf rf pj by (simp add: search_formed_def)
qed

lemma search_refresh:
  assumes r: "search_formed \<kappa> P r"
  shows "search_formed \<kappa> P (search_refresh \<kappa> P r) \<and> search_project (search_refresh \<kappa> P r) = search_project r"
proof -
  have "search_formed \<kappa> P t \<Longrightarrow> search_formed \<kappa> P (fold (search_refresh_at \<kappa> P) ps t) \<and>
      search_project (fold (search_refresh_at \<kappa> P) ps t) = search_project t" for ps t
  proof (induction ps arbitrary: t)
    case (Cons a ps)
    note s = search_refresh_at[OF Cons.prems, of a]
    show ?case using Cons.IH[OF conjunct1[OF s]] conjunct2[OF s] by simp
  qed simp
  then show ?thesis using r by (simp add: search_refresh_def)
qed

subsection \<open>The construction step\<close>

definition search_construct :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_construct \<kappa> P r hn = (let nd = shared_entry_node hn; q = shared_derivation_position nd;
      C = access_constructed (shared_access \<kappa> P r) hn;
      \<tau> = (\<lambda>z. case z of ((q',b),a) \<Rightarrow> if b \<and> q' = q \<and> a |\<in>| C then (case search_value \<kappa> P r nd a of
          Some v \<Rightarrow> finite_exact_term_pattern v | None \<Rightarrow> Finite_Variable z) else Finite_Variable z);
      W = ffUnion (fimage (\<lambda>a. case search_value \<kappa> P r nd a of Some v \<Rightarrow> {|(((q,True),a),v)|} | None \<Rightarrow> {||}) C) in
    search_substitute_plain P \<tau> (fimage (\<lambda>a. ((q,True),a)) C)
      (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := shared_witnesses (search_state r) |\<union>| W\<rparr>\<rparr>))"

lemma search_witnesses_update:
  "search_formed \<kappa> P (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) \<longleftrightarrow> search_formed \<kappa> P r"
  "search_project (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) =
    Resolution_State (resolution_pending (search_project r)) (resolution_nodes (search_project r)) W"
  by (simp_all add: search_formed_def shared_state_formed_def shared_recorded_at_def search_registered_formed_def
      search_values_formed_def shared_state_project_def)

theorem search_construct:
  assumes r: "search_formed \<kappa> P r" and n: "hn |\<in>| access_nodes_at (shared_access \<kappa> P r) q0"
  shows "search_formed \<kappa> P (search_construct \<kappa> P r hn)"
    and "search_project (search_construct \<kappa> P r hn) =
      finite_construction_step \<kappa> P (search_project r) (access_node (shared_access \<kappa> P r) hn)"
proof -
  interpret access_formed \<kappa> P "shared_access \<kappa> P r" "search_project r" by (rule shared_access_formed[OF r])
  let ?V = "shared_access \<kappa> P r" let ?nd = "shared_entry_node hn" let ?q = "shared_derivation_position ?nd"
  let ?n = "access_node ?V hn" let ?G = "resolution_pending (search_project r)"
  let ?C = "access_constructed ?V hn"
  have v: "search_values_formed \<kappa> P r" using search_formedD[OF r] by simp
  have C: "?C = finite_constructed \<kappa> P ?G ?n" by (rule constructed[OF n])
  have val: "search_value \<kappa> P r ?nd a = finite_registered_value \<kappa> P ?n a" for a
    using search_value[OF v] by (simp add: shared_access_simps)
  have pos: "resolution_node_position ?n = ?q" by (simp add: shared_access_simps)
  define \<tau> where "\<tau> = (\<lambda>z. case z of ((q',b),a) \<Rightarrow> if b \<and> q' = ?q \<and> a |\<in>| ?C then (case search_value \<kappa> P r ?nd a of
      Some v \<Rightarrow> finite_exact_term_pattern v | None \<Rightarrow> Finite_Variable z) else Finite_Variable z)"
  define W where "W = ffUnion (fimage (\<lambda>a. case search_value \<kappa> P r ?nd a of Some v \<Rightarrow> {|(((?q,True),a),v)|}
    | None \<Rightarrow> {||}) ?C)"
  let ?r1 = "r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := shared_witnesses (search_state r) |\<union>| W\<rparr>\<rparr>"
  have e: "search_construct \<kappa> P r hn = search_substitute_plain P \<tau> (fimage (\<lambda>a. ((?q,True),a)) ?C) ?r1"
    by (simp add: search_construct_def Let_def \<tau>_def W_def)
  have f1: "search_formed \<kappa> P ?r1" using r by (simp add: search_witnesses_update)
  have out: "\<tau> z = Finite_Variable z" if "z |\<notin>| fimage (\<lambda>a. ((?q,True),a)) ?C" for z
    using that by (auto simp: \<tau>_def fimage.rep_eq split: prod.splits)
  note k = search_substitute_plain[where \<tau> = \<tau> and D = "fimage (\<lambda>a. ((?q,True),a)) ?C", OF f1 out]
  show "search_formed \<kappa> P (search_construct \<kappa> P r hn)" using k(1) e by simp
  have \<sigma>: "\<tau> = finite_construction_substitution \<kappa> P ?G ?n"
    by (auto simp: fun_eq_iff \<tau>_def finite_construction_substitution_def C val pos split: prod.splits)
  have Wv: "W = ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P ?n a of
      Some v \<Rightarrow> {|(((resolution_node_position ?n,True),a),v)|} | None \<Rightarrow> {||}) (finite_constructed \<kappa> P ?G ?n))"
    by (simp add: W_def C val pos cong: option.case_cong)
  have w: "search_project ?r1 = Resolution_State ?G (resolution_nodes (search_project r))
      (resolution_witnesses (search_project r) |\<union>| W)"
    using search_witnesses_update(2)[where r = r and W = "shared_witnesses (search_state r) |\<union>| W"]
      shared_state_project_fields(3)[of "search_state r"] by simp
  have p1: "search_project (search_construct \<kappa> P r hn) = resolution_state_substitute \<tau> (search_project ?r1)"
    using k(2) e by simp
  show "search_project (search_construct \<kappa> P r hn) = finite_construction_step \<kappa> P (search_project r) ?n"
    unfolding p1 unfolding w unfolding \<sigma> Wv finite_construction_step_def Let_def by (rule refl)
qed

section \<open>One goal and one node at a position\<close>

text \<open>
  The shared state holds one goal and one node at a position. R3's search keeps them so from a state every goal and
  node of which, but at the root, stands under a node: a clause's premises are placed under the node it adds, at
  positions no goal or node holds, since none stands under a position where a call waits. A clause's premise sockets
  are distinct (@{text clause_sockets_distinct}), as a formed program's are.
\<close>

definition search_placeable :: "('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "search_placeable st \<longleftrightarrow> resolution_positions_distinct st \<and>
    fBall (resolution_pending st) (\<lambda>g. resolution_goal_position g \<noteq> [] \<longrightarrow>
      butlast (resolution_goal_position g) |\<in>| fimage resolution_node_position (resolution_nodes st)) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. resolution_node_position nd \<noteq> [] \<longrightarrow>
      butlast (resolution_node_position nd) |\<in>| fimage resolution_node_position (resolution_nodes st))"

definition clause_sockets_distinct :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "clause_sockets_distinct P \<longleftrightarrow> fBall (finite_system_clauses P) (\<lambda>z. case z of ((d,c),S) \<Rightarrow>
    finite_relation_functional (finite_schema_premises S) \<and> finite_relation_functional (finite_schema_materials S) \<and>
    fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||})"

lemma resolution_positions_distinct_code [code]:
  "resolution_positions_distinct st \<longleftrightarrow>
    fBall (resolution_nodes st) (\<lambda>nd. fBall (resolution_nodes st) (\<lambda>m.
      resolution_node_position nd = resolution_node_position m \<longrightarrow> nd = m)) \<and>
    fBall (resolution_pending st) (\<lambda>g. fBall (resolution_pending st) (\<lambda>h.
      resolution_goal_position g = resolution_goal_position h \<longrightarrow> g = h)) \<and>
    fBall (resolution_pending st) (\<lambda>g. fBall (resolution_nodes st) (\<lambda>nd.
      resolution_is_call g \<longrightarrow> resolution_goal_position g \<noteq> resolution_node_position nd))"
  unfolding resolution_positions_distinct_def by blast

lemma search_placeable_substitute:
  assumes pl: "search_placeable st"
  shows "search_placeable (resolution_state_substitute \<sigma> st)"
proof -
  have np: "fimage resolution_node_position (resolution_nodes (resolution_state_substitute \<sigma> st)) =
      fimage resolution_node_position (resolution_nodes st)"
    by (simp add: fset.map_comp comp_def)
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  have d': "resolution_positions_distinct (resolution_state_substitute \<sigma> st)"
    unfolding resolution_positions_distinct_def
  proof (intro conjI allI impI)
    fix nd m assume "nd |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
      "m |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
      "resolution_node_position nd = resolution_node_position m"
    then obtain nd0 m0 where "nd0 |\<in>| resolution_nodes st" "m0 |\<in>| resolution_nodes st"
      "nd = resolution_node_substitute \<sigma> nd0" "m = resolution_node_substitute \<sigma> m0"
      "resolution_node_position nd0 = resolution_node_position m0"
      by (auto elim!: fimageE)
    then show "nd = m" using d unfolding resolution_positions_distinct_def by metis
  next
    fix g h assume "g |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
      "h |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
      "resolution_goal_position g = resolution_goal_position h"
    then obtain g0 h0 where "g0 |\<in>| resolution_pending st" "h0 |\<in>| resolution_pending st"
      "g = resolution_goal_substitute \<sigma> g0" "h = resolution_goal_substitute \<sigma> h0"
      "resolution_goal_position g0 = resolution_goal_position h0"
      by (auto elim!: fimageE)
    then show "g = h" using d unfolding resolution_positions_distinct_def by metis
  next
    fix g nd assume "g |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)"
      "nd |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)" "resolution_is_call g"
    then obtain g0 nd0 where "g0 |\<in>| resolution_pending st" "nd0 |\<in>| resolution_nodes st"
      "g = resolution_goal_substitute \<sigma> g0" "nd = resolution_node_substitute \<sigma> nd0" "resolution_is_call g0"
      by (auto elim!: fimageE)
    then show "resolution_goal_position g \<noteq> resolution_node_position nd"
      using d unfolding resolution_positions_distinct_def by simp
  qed
  show ?thesis using pl d' np unfolding search_placeable_def by (auto simp: fimage.rep_eq)
qed

lemma search_placeable_fewer:
  assumes pl: "search_placeable st"
  shows "search_placeable (Resolution_State (resolution_pending st |-| G) (resolution_nodes st) W)"
  using pl unfolding search_placeable_def resolution_positions_distinct_def by auto

lemma search_placeable_witnesses:
  assumes pl: "search_placeable st"
  shows "search_placeable (Resolution_State (resolution_pending st) (resolution_nodes st) W)"
  using search_placeable_fewer[OF pl, of "{||}" W] by simp

lemma clause_goals_distinct:
  assumes f1: "finite_relation_functional (finite_schema_premises S)"
    and f2: "finite_relation_functional (finite_schema_materials S)"
    and dj: "fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||}"
    and g: "g |\<in>| finite_clause_goals q d c S" and h: "h |\<in>| finite_clause_goals q d c S"
    and p: "resolution_goal_position g = resolution_goal_position h"
  shows "g = h"
proof -
  have f1': "x = y" if "x |\<in>| finite_schema_premises S" "y |\<in>| finite_schema_premises S" "fst x = fst y" for x y
    using f1 that unfolding finite_relation_functional_def by (metis prod.expand)
  have f2': "x = y" if "x |\<in>| finite_schema_materials S" "y |\<in>| finite_schema_materials S" "fst x = fst y" for x y
    using f2 that unfolding finite_relation_functional_def by (metis prod.expand)
  have dj': "fst x \<noteq> fst y" if "x |\<in>| finite_schema_premises S" "y |\<in>| finite_schema_materials S" for x y
    using dj that by (auto simp: fset_eq_iff)
  from g h p show ?thesis unfolding finite_clause_goals_def
    by (auto dest: f1' f2' dj')
qed

lemma clause_goals_below:
  "g |\<in>| finite_clause_goals q d c S \<Longrightarrow> resolution_goal_position g \<noteq> [] \<and> butlast (resolution_goal_position g) = q"
  by (auto simp: finite_clause_goals_def)

lemma search_placeable_call:
  assumes pl: "search_placeable st" and g: "Resolution_Call_Goal q rr d p |\<in>| resolution_pending st"
    and f1: "finite_relation_functional (finite_schema_premises S)"
    and f2: "finite_relation_functional (finite_schema_materials S)"
    and dj: "fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||}"
  shows "search_placeable (Resolution_State (finite_clause_goals q d c S |\<union>|
      (resolution_pending st |-| {|Resolution_Call_Goal q rr d p|}))
      (finsert (finite_clause_node q d c S) (resolution_nodes st)) W)"
proof -
  let ?g = "Resolution_Call_Goal q rr d p" and ?G = "finite_clause_goals q d c S" and ?cn = "finite_clause_node q d c S"
  have d: "resolution_positions_distinct st" and gp: "\<And>h. h |\<in>| resolution_pending st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) |\<in>| fimage resolution_node_position (resolution_nodes st)"
    and np: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd \<noteq> [] \<Longrightarrow>
      butlast (resolution_node_position nd) |\<in>| fimage resolution_node_position (resolution_nodes st)"
    using pl unfolding search_placeable_def by auto
  have noq: "resolution_node_position nd \<noteq> q" if "nd |\<in>| resolution_nodes st" for nd
    using d g that unfolding resolution_positions_distinct_def by fastforce
  have qnodes: "q |\<notin>| fimage resolution_node_position (resolution_nodes st)" using noq by (auto simp: fimage.rep_eq)
  have cnq: "resolution_node_position ?cn = q" by (simp add: finite_clause_node_def)
  have oldg: "resolution_goal_position h \<noteq> resolution_goal_position h'" if "h |\<in>| resolution_pending st" "h' |\<in>| ?G" for h h'
  proof
    assume e: "resolution_goal_position h = resolution_goal_position h'"
    have "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = q"
      using clause_goals_below[OF that(2)] e by simp
    then show False using gp[OF that(1)] qnodes by simp
  qed
  have oldn: "resolution_node_position nd \<noteq> resolution_goal_position h'" if "nd |\<in>| resolution_nodes st" "h' |\<in>| ?G" for nd h'
  proof
    assume e: "resolution_node_position nd = resolution_goal_position h'"
    have "resolution_node_position nd \<noteq> [] \<and> butlast (resolution_node_position nd) = q"
      using clause_goals_below[OF that(2)] e by simp
    then show False using np[OF that(1)] qnodes by simp
  qed
  have other: "resolution_goal_position h \<noteq> q" if "h |\<in>| resolution_pending st" "h \<noteq> ?g" for h
    using d g that unfolding resolution_positions_distinct_def by force
  have cn_placed: "q \<noteq> [] \<Longrightarrow> butlast q |\<in>| fimage resolution_node_position (resolution_nodes st)"
    using gp[OF g] by simp
  have gd: "\<And>h h'. h |\<in>| ?G \<Longrightarrow> h' |\<in>| ?G \<Longrightarrow> resolution_goal_position h = resolution_goal_position h' \<Longrightarrow> h = h'"
    by (rule clause_goals_distinct[OF f1 f2 dj])
  show ?thesis
    unfolding search_placeable_def resolution_positions_distinct_def resolution_state.sel
  proof (intro conjI allI impI fBallI)
    fix nd m assume "nd |\<in>| finsert ?cn (resolution_nodes st)" "m |\<in>| finsert ?cn (resolution_nodes st)"
      "resolution_node_position nd = resolution_node_position m"
    then show "nd = m" using d noq cnq unfolding resolution_positions_distinct_def by (metis finsert_iff)
  next
    fix h h' assume h: "h |\<in>| ?G |\<union>| (resolution_pending st |-| {|?g|})" and h': "h' |\<in>| ?G |\<union>| (resolution_pending st |-| {|?g|})"
      and e: "resolution_goal_position h = resolution_goal_position h'"
    have dg: "\<And>g g'. g |\<in>| resolution_pending st \<Longrightarrow> g' |\<in>| resolution_pending st \<Longrightarrow>
        resolution_goal_position g = resolution_goal_position g' \<Longrightarrow> g = g'"
      using d unfolding resolution_positions_distinct_def by blast
    have hc: "h |\<in>| ?G \<or> h |\<in>| resolution_pending st" and hc': "h' |\<in>| ?G \<or> h' |\<in>| resolution_pending st"
      using h h' by auto
    then show "h = h'"
    proof (elim disjE)
      assume "h |\<in>| ?G" "h' |\<in>| ?G" then show ?thesis using gd e by blast
    next
      assume "h |\<in>| ?G" "h' |\<in>| resolution_pending st" then show ?thesis using oldg[of h' h] e by simp
    next
      assume "h |\<in>| resolution_pending st" "h' |\<in>| ?G" then show ?thesis using oldg[of h h'] e by simp
    next
      assume "h |\<in>| resolution_pending st" "h' |\<in>| resolution_pending st" then show ?thesis using dg e by blast
    qed
  next
    fix h nd assume h: "h |\<in>| ?G |\<union>| (resolution_pending st |-| {|?g|})" and nd: "nd |\<in>| finsert ?cn (resolution_nodes st)"
      and call: "resolution_is_call h"
    show "resolution_goal_position h \<noteq> resolution_node_position nd"
    proof (cases "h |\<in>| ?G")
      case True
      note hG = this
      have b: "resolution_goal_position h \<noteq> [] \<and> butlast (resolution_goal_position h) = q"
        by (rule clause_goals_below[OF hG])
      show ?thesis
      proof
        assume e: "resolution_goal_position h = resolution_node_position nd"
        show False
        proof (cases "nd = ?cn")
          case True
          then have "resolution_goal_position h = q" using e cnq by simp
          then have "q \<noteq> [] \<and> butlast q = q" using b by simp
          then have l: "q \<noteq> [] \<and> length (butlast q) = length q" by simp
          then have "0 < length q" by simp
          moreover have "length q - 1 = length q" using l by simp
          ultimately show False by linarith
        next
          case False
          then have ndn: "nd |\<in>| resolution_nodes st" using nd by simp
          show False using oldn[OF ndn hG] e by simp
        qed
      qed
    next
      case False
      then have ho: "h |\<in>| resolution_pending st" "h \<noteq> ?g" using h by auto
      have dc: "\<And>g' nd'. g' |\<in>| resolution_pending st \<Longrightarrow> nd' |\<in>| resolution_nodes st \<Longrightarrow> resolution_is_call g' \<Longrightarrow>
          resolution_goal_position g' \<noteq> resolution_node_position nd'"
        using d unfolding resolution_positions_distinct_def by blast
      show ?thesis
      proof (cases "nd = ?cn")
        case True
        then show ?thesis using other[OF ho] cnq by simp
      next
        case False
        then have "nd |\<in>| resolution_nodes st" using nd by simp
        then show ?thesis using dc[OF ho(1) _ call] by simp
      qed
    qed
  next
    fix h assume h: "h \<in> fset (?G |\<union>| (resolution_pending st |-| {|?g|}))" and ne: "resolution_goal_position h \<noteq> []"
    show "butlast (resolution_goal_position h) |\<in>| fimage resolution_node_position (finsert ?cn (resolution_nodes st))"
    proof (cases "h |\<in>| ?G")
      case True
      then show ?thesis using clause_goals_below[OF True] cnq by simp
    next
      case False
      then have "h |\<in>| resolution_pending st" using h by auto
      then show ?thesis using gp ne by auto
    qed
  next
    fix nd assume nd: "nd \<in> fset (finsert ?cn (resolution_nodes st))" and ne: "resolution_node_position nd \<noteq> []"
    show "butlast (resolution_node_position nd) |\<in>| fimage resolution_node_position (finsert ?cn (resolution_nodes st))"
      using nd ne np cn_placed cnq by auto
  qed
qed

section \<open>The successors of a goal\<close>

text \<open>
  A call is expanded by R3's alternatives, each read at the goal's projection: the goal is removed, the ground terms of
  the clause's premises and node shared, the premises placed at their positions and the node at the goal's, and the
  alternative's unifier shared and substituted, collapsed. A material goal is removed and its solution's unifier
  substituted. Each projects to R3's alternative state.
\<close>

definition search_place_goals :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('s list \<times> ('a,'s,'d,'c) resolution_goal) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_place_goals P rows r = fold (\<lambda>z t. search_put_goal (fst z)
    (Shared_Goal_Entry (shared_goal_of (shared_sharing (search_state t)) (snd z)) (finite_goal_alternatives P (snd z))) t) rows r"

lemma search_place_goals:
  assumes t: "search_formed \<kappa> P t" and d: "distinct (map fst rows)"
    and free: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> RBT.lookup (shared_goals (search_state t)) q = None"
    and pos: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> resolution_goal_position g = q"
    and held: "\<And>q g u. (q,g) \<in> set rows \<Longrightarrow> u |\<in>| goal_grounds g \<Longrightarrow> table_holds (search_table t) u"
  shows "search_formed \<kappa> P (search_place_goals P rows t) \<and>
    shared_sharing (search_state (search_place_goals P rows t)) = shared_sharing (search_state t) \<and>
    (\<forall>p. RBT.lookup (shared_nodes (search_state (search_place_goals P rows t))) p = RBT.lookup (shared_nodes (search_state t)) p) \<and>
    resolution_pending (search_project (search_place_goals P rows t)) =
      resolution_pending (search_project t) |\<union>| fset_of_list (map snd rows) \<and>
    resolution_nodes (search_project (search_place_goals P rows t)) = resolution_nodes (search_project t) \<and>
    resolution_witnesses (search_project (search_place_goals P rows t)) = resolution_witnesses (search_project t)"
  using assms
proof (induction rows arbitrary: t)
  case Nil
  then show ?case by (simp add: search_place_goals_def)
next
  case (Cons z rows)
  obtain q g where z: "z = (q,g)" by (cases z)
  let ?x = "shared_sharing (search_state t)" and ?T = "search_table t"
  let ?h = "Shared_Goal_Entry (shared_goal_of ?x g) (finite_goal_alternatives P g)"
  let ?t' = "search_put_goal q ?h t"
  have s: "shared_state_formed \<kappa> P (search_state t)" using search_formedD[OF Cons.prems(1)] by simp
  have xf: "share_state_formed ?x" using shared_entries_formed(3)[OF s] .
  have rep: "keyed_state_represents ?x ?T" and tf: "table_formed ?T" using share_state_formed_table[OF xf] by simp_all
  have hd: "\<And>u. u |\<in>| goal_grounds g \<Longrightarrow> table_holds ?T u" using Cons.prems(5) z by auto
  have ex: "shared_goal_formed ?T (shared_goal_of ?x g) \<and> shared_goal_project ?T (shared_goal_of ?x g) = g"
    using shared_goal_of_exact[OF rep tf hd] .
  have pq: "shared_goal_position (shared_goal_of ?x g) = q"
    using Cons.prems(4)[of q g] z ex shared_goal_project_position[of ?T "shared_goal_of ?x g"] by simp
  have hf: "goal_entry_formed P ?T q ?h" using ex pq by (simp add: goal_entry_formed_def)
  have fr: "RBT.lookup (shared_goals (search_state t)) q = None" using Cons.prems(3)[of q g] z by simp
  note put = search_put_goal[OF Cons.prems(1) hf fr]
  note sp = shared_put_goal[OF s hf fr]
  have sh: "shared_sharing (search_state ?t') = ?x" using put(2) by (simp add: shared_put_goal_def)
  have nl: "\<And>p. RBT.lookup (shared_nodes (search_state ?t')) p = RBT.lookup (shared_nodes (search_state t)) p"
    using put(2) by (simp add: shared_put_goal_def)
  have d': "distinct (map fst rows)" using Cons.prems(2) by simp
  have nq: "(q,g') \<notin> set rows" for g'
  proof
    assume "(q,g') \<in> set rows"
    then have "q \<in> set (map fst rows)" by force
    with Cons.prems(2) z show False by simp
  qed
  have free': "\<And>q' g'. (q',g') \<in> set rows \<Longrightarrow> RBT.lookup (shared_goals (search_state ?t')) q' = None"
  proof -
    fix q' g' assume m: "(q',g') \<in> set rows"
    then have "q' \<noteq> q" using nq by auto
    then show "RBT.lookup (shared_goals (search_state ?t')) q' = None"
      using Cons.prems(3)[of q' g'] m put(2) by (simp add: shared_put_goal_def)
  qed
  have pos': "\<And>q' g'. (q',g') \<in> set rows \<Longrightarrow> resolution_goal_position g' = q'" using Cons.prems(4) by auto
  have held': "\<And>q' g' u. (q',g') \<in> set rows \<Longrightarrow> u |\<in>| goal_grounds g' \<Longrightarrow> table_holds (search_table ?t') u"
    using Cons.prems(5) sh by auto
  note IH = Cons.IH[OF put(1) d' free' pos' held']
  have unf: "search_place_goals P (z # rows) t = search_place_goals P rows ?t'" by (simp add: search_place_goals_def z)
  have p1: "resolution_pending (search_project ?t') = resolution_pending (search_project t) |\<union>| {|g|}"
    using sp(2) ex put(2) by simp
  have p2: "resolution_nodes (search_project ?t') = resolution_nodes (search_project t)" using sp(3) put(2) by simp
  have p3: "resolution_witnesses (search_project ?t') = resolution_witnesses (search_project t)" using sp(4) put(2) by simp
  show ?case unfolding unf using IH sh nl p1 p2 p3 z by (auto intro!: fset_eqI)
qed

definition search_call_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> ('d \<times> 'c \<times> 's) option \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
    'a finite_term_pattern \<times> 'c \<times> ('a,'s,'d) finite_factor_schema \<times>
      (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable finite_term_pattern) list \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_call_state P r q rr d p z = (case z of (i,c,S,u) \<Rightarrow> (let G = finite_clause_goals q d c S;
      nd = finite_clause_node q d c S;
      r1 = search_reshare (ffUnion (fimage goal_grounds G) |\<union>| node_grounds nd) (search_remove_goal q r);
      r2 = search_place_goals P (finite_functional_rows (fimage (\<lambda>g. (resolution_goal_position g, g)) G)) r1;
      r3 = search_put_node q (enter_node (shared_derivation_of (shared_sharing (search_state r2)) nd)) r2 in
    search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) r3))"

definition search_material_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> ('s,'a) resolution_variable finite_pattern_pairs \<times>
      (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable finite_term_pattern) list \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_material_state P r q z = (case z of (E,u) \<Rightarrow>
    search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) (search_remove_goal q r))"

lemma call_alternative_clause:
  assumes "z |\<in>| finite_call_alternative_set P q d p"
  shows "\<exists>i c S u. z = (i,c,S,u) \<and> ((d,c),S) |\<in>| finite_system_clauses P"
  using assms unfolding finite_call_alternative_set_def
  by (auto simp: ffUnion.rep_eq fimage.rep_eq split: if_splits option.splits)

theorem search_call_state:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_goal_project (search_table r) (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
    and z: "z |\<in>| finite_call_alternative_set P q d p"
  shows "search_formed \<kappa> P (search_call_state P r q rr d p z)"
    and "search_project (search_call_state P r q rr d p z) = finite_call_alternative_state (search_project r) q rr d p z"
    and "search_placeable (search_project (search_call_state P r q rr d p z))"
proof -
  obtain i c S u where zz: "z = (i,c,S,u)" and cl: "((d,c),S) |\<in>| finite_system_clauses P"
    using call_alternative_clause[OF z] by blast
  have f1: "finite_relation_functional (finite_schema_premises S)"
    and f2: "finite_relation_functional (finite_schema_materials S)"
    and dj: "fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||}"
    using fbspec[OF sock[unfolded clause_sockets_distinct_def] cl] by simp_all
  let ?g = "Resolution_Call_Goal q rr d p" and ?G = "finite_clause_goals q d c S" and ?nd = "finite_clause_node q d c S"
  let ?st = "search_project r"
  have gin: "?g |\<in>| resolution_pending ?st"
    using at g unfolding shared_state_project_member(1) by blast
  have d: "resolution_positions_distinct ?st" and gp: "\<And>h. h |\<in>| resolution_pending ?st \<Longrightarrow> resolution_goal_position h \<noteq> [] \<Longrightarrow>
      butlast (resolution_goal_position h) |\<in>| fimage resolution_node_position (resolution_nodes ?st)"
    using pl unfolding search_placeable_def by auto
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have noq: "resolution_node_position nd \<noteq> q" if "nd |\<in>| resolution_nodes ?st" for nd
    using d gin that unfolding resolution_positions_distinct_def by fastforce
  have qnodes: "q |\<notin>| fimage resolution_node_position (resolution_nodes ?st)" using noq by (auto simp: fimage.rep_eq)
  note r0 = search_remove_goal[OF r at]
  let ?r0 = "search_remove_goal q r"
  note sr0 = shared_remove_goal[OF s at]
  have p0: "resolution_pending (search_project ?r0) = resolution_pending ?st |-| {|?g|}"
    "resolution_nodes (search_project ?r0) = resolution_nodes ?st"
    "resolution_witnesses (search_project ?r0) = resolution_witnesses ?st"
    using sr0(2-4) r0(2) g by simp_all
  let ?Gr = "ffUnion (fimage goal_grounds ?G) |\<union>| node_grounds ?nd"
  let ?r1 = "search_reshare ?Gr ?r0"
  note r1 = search_reshare[where G = ?Gr, OF r0(1)]
  let ?rows = "finite_functional_rows (fimage (\<lambda>g. (resolution_goal_position g, g)) ?G)"
  have rfun: "finite_relation_functional (fimage (\<lambda>g. (resolution_goal_position g, g)) ?G)"
    unfolding finite_relation_functional_def
  proof (intro fBallI impI)
    fix a b assume "a \<in> fset (fimage (\<lambda>g. (resolution_goal_position g, g)) ?G)"
      "b \<in> fset (fimage (\<lambda>g. (resolution_goal_position g, g)) ?G)" "fst a = fst b"
    then show "snd a = snd b" using clause_goals_distinct[OF f1 f2 dj] by (auto simp: fimage.rep_eq)
  qed
  have rows: "set ?rows = fset (fimage (\<lambda>g. (resolution_goal_position g, g)) ?G)"
    using finite_functional_rows_exact[OF rfun] .
  have rfree: "RBT.lookup (shared_goals (search_state ?r1)) q' = None" if "(q',g') \<in> set ?rows" for q' g'
  proof -
    have gG: "g' |\<in>| ?G" and pq: "resolution_goal_position g' = q'" using that rows by (auto simp: fimage.rep_eq)
    show ?thesis
    proof (cases "RBT.lookup (shared_goals (search_state ?r1)) q'")
      case (Some h')
      then have "RBT.lookup (shared_goals (search_state ?r0)) q' = Some h'" using r1(5) by simp
      then have m: "shared_goal_project (search_table ?r0) (shared_entry_goal h') |\<in>| resolution_pending (search_project ?r0)"
        unfolding shared_state_project_member(1) by blast
      have "resolution_goal_position (shared_goal_project (search_table ?r0) (shared_entry_goal h')) = q'"
        using shared_goal_lookup_position[OF search_formedD(1)[OF r0(1)] \<open>RBT.lookup (shared_goals (search_state ?r0)) q' = Some h'\<close>]
        by simp
      moreover have "q' \<noteq> [] \<and> butlast q' = q" using clause_goals_below[OF gG] pq by simp
      ultimately show ?thesis using gp[of "shared_goal_project (search_table ?r0) (shared_entry_goal h')"] m p0 qnodes by auto
    qed simp
  qed
  have rpos: "\<And>q' g'. (q',g') \<in> set ?rows \<Longrightarrow> resolution_goal_position g' = q'" using rows by (auto simp: fimage.rep_eq)
  have rheld: "table_holds (search_table ?r1) t" if "(q',g') \<in> set ?rows" "t |\<in>| goal_grounds g'" for q' g' t
  proof -
    have "g' |\<in>| ?G" using that(1) rows by (auto simp: fimage.rep_eq)
    then have "t |\<in>| ?Gr" using that(2) by (auto simp: ffUnion.rep_eq fimage.rep_eq)
    then show ?thesis by (rule r1(4))
  qed
  have rd: "distinct (map fst ?rows)" by (rule finite_functional_rows_distinct_keys[OF rfun])
  let ?r2 = "search_place_goals P ?rows ?r1"
  note r2 = search_place_goals[OF r1(1) rd rfree rpos rheld]
  let ?x = "shared_sharing (search_state ?r2)"
  have x2: "?x = shared_sharing (search_state ?r1)" using r2 by simp
  have s2: "shared_state_formed \<kappa> P (search_state ?r2)" using search_formedD[OF conjunct1[OF r2]] by simp
  have xf: "share_state_formed ?x" using shared_entries_formed(3)[OF s2] .
  have rep: "keyed_state_represents ?x (search_table ?r2)" and tf2: "table_formed (search_table ?r2)"
    using share_state_formed_table[OF xf] by simp_all
  have ndh: "\<And>t. t |\<in>| node_grounds ?nd \<Longrightarrow> table_holds (search_table ?r2) t"
    using r1(4) x2 by (simp add: share_state_table_def)
  have ex: "shared_derivation_formed (search_table ?r2) (shared_derivation_of ?x ?nd) \<and>
      shared_derivation_project (search_table ?r2) (shared_derivation_of ?x ?nd) = ?nd"
    using shared_derivation_of_exact[OF rep tf2 ndh] .
  have ndpos: "shared_derivation_position (shared_derivation_of ?x ?nd) = q" by (simp add: shared_derivation_of_def finite_clause_node_def)
  have hnf: "node_entry_formed (search_table ?r2) q (enter_node (shared_derivation_of ?x ?nd))"
    using enter_node_formed[OF conjunct1[OF ex] ndpos] .
  have nfree: "RBT.lookup (shared_nodes (search_state ?r2)) q = None"
  proof (cases "RBT.lookup (shared_nodes (search_state r)) q")
    case (Some hn)
    have "shared_derivation_project (search_table r) (shared_entry_node hn) |\<in>| resolution_nodes ?st"
      unfolding shared_state_project_member(2) using Some by blast
    moreover have "resolution_node_position (shared_derivation_project (search_table r) (shared_entry_node hn)) = q"
      using shared_node_lookup_position[OF s Some] by simp
    ultimately show ?thesis using noq by blast
  next
    case None
    have "RBT.lookup (shared_nodes (search_state ?r0)) q = None"
      using None r0(2) by (simp add: shared_remove_goal_def shared_replace_def)
    then show ?thesis using r2 r1(6) by simp
  qed
  let ?r3 = "search_put_node q (enter_node (shared_derivation_of ?x ?nd)) ?r2"
  note r3 = search_put_node[OF conjunct1[OF r2] hnf nfree]
  note sp3 = shared_put_node[OF s2 hnf nfree]
  have p3: "search_project ?r3 = Resolution_State (?G |\<union>| (resolution_pending ?st |-| {|?g|}))
      (finsert ?nd (resolution_nodes ?st)) (resolution_witnesses ?st)"
  proof -
    have g3: "resolution_pending (search_project ?r3) = ?G |\<union>| (resolution_pending ?st |-| {|?g|})"
    proof -
      have "fset_of_list (map snd ?rows) = ?G"
        by (unfold fset_of_list_eq_set) (simp add: rows fimage.rep_eq image_image)
      then show ?thesis using sp3(2) r3(2) r2 r1(2) p0 by (auto simp: fset_eq_iff)
    qed
    have n3: "resolution_nodes (search_project ?r3) = finsert ?nd (resolution_nodes ?st)"
      using sp3(3) r3(2) r2 r1(2) p0 ex by (auto simp: fset_eq_iff)
    have w3: "resolution_witnesses (search_project ?r3) = resolution_witnesses ?st"
      using sp3(4) r3(2) r2 r1(2) p0 by simp
    show ?thesis using g3 n3 w3 by (cases "search_project ?r3") simp
  qed
  have out: "\<And>a. a |\<notin>| fset_of_list (map fst u) \<Longrightarrow> finite_binding_substitution u a = Finite_Variable a"
    by (rule finite_binding_substitution_outside)
  note k = search_substitute_plain[where \<tau> = "finite_binding_substitution u" and D = "fset_of_list (map fst u)",
    OF r3(1) out]
  have e: "search_call_state P r q rr d p z =
      search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) ?r3"
    by (simp add: search_call_state_def zz Let_def)
  show "search_formed \<kappa> P (search_call_state P r q rr d p z)" using k(1) e by simp
  show pr: "search_project (search_call_state P r q rr d p z) = finite_call_alternative_state ?st q rr d p z"
    using k(2) e p3 by (simp add: finite_call_alternative_state_def zz)
  have "search_placeable (search_project ?r3)"
    using search_placeable_call[OF pl gin f1 f2 dj, where c = c and W = "resolution_witnesses ?st"] p3 by simp
  then show "search_placeable (search_project (search_call_state P r q rr d p z))"
    using k(2) e search_placeable_substitute by simp
qed

theorem search_material_state:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_goal_project (search_table r) (shared_entry_goal h) = Resolution_Material_Goal q rr M"
  shows "search_formed \<kappa> P (search_material_state P r q z)"
    and "search_project (search_material_state P r q z) = finite_material_alternative_state (search_project r) q rr M z"
    and "search_placeable (search_project (search_material_state P r q z))"
proof -
  obtain E u where zz: "z = (E,u)" by (cases z)
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  note r0 = search_remove_goal[OF r at]
  note sr0 = shared_remove_goal[OF s at]
  have p0: "search_project (search_remove_goal q r) = Resolution_State
      (resolution_pending (search_project r) |-| {|Resolution_Material_Goal q rr M|})
      (resolution_nodes (search_project r)) (resolution_witnesses (search_project r))"
    using sr0(2-4) r0(2) g by (cases "search_project (search_remove_goal q r)") simp
  have out: "\<And>a. a |\<notin>| fset_of_list (map fst u) \<Longrightarrow> finite_binding_substitution u a = Finite_Variable a"
    by (rule finite_binding_substitution_outside)
  note k = search_substitute_plain[where \<tau> = "finite_binding_substitution u" and D = "fset_of_list (map fst u)",
    OF r0(1) out]
  have e: "search_material_state P r q z =
      search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) (search_remove_goal q r)"
    by (simp add: search_material_state_def zz)
  show "search_formed \<kappa> P (search_material_state P r q z)" using k(1) e by simp
  show "search_project (search_material_state P r q z) = finite_material_alternative_state (search_project r) q rr M z"
    using k(2) e p0 by (simp add: finite_material_alternative_state_def zz)
  have "search_placeable (search_project (search_remove_goal q r))"
    using search_placeable_fewer[OF pl] p0 by simp
  then show "search_placeable (search_project (search_material_state P r q z))"
    using k(2) e search_placeable_substitute by simp
qed

definition search_successors :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) shared_search fset" where
  "search_successors \<kappa> P r h = (case shared_goal_project (search_table r) (shared_entry_goal h) of
      Resolution_Call_Goal q rr d p \<Rightarrow> if access_reusable (shared_access \<kappa> P r) h then {|search_remove_goal q r|}
        else fimage (search_call_state P r q rr d p) (finite_call_alternative_set P q d p)
    | Resolution_Material_Goal q rr M \<Rightarrow> fimage (search_material_state P r q) (finite_material_alternative_set M))"

theorem search_successors:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
  shows "fimage search_project (search_successors \<kappa> P r h) =
      finite_goal_successors P (search_project r) (access_goal (shared_access \<kappa> P r) h)"
    and "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
proof -
  interpret access_formed \<kappa> P "shared_access \<kappa> P r" "search_project r" by (rule shared_access_formed[OF r])
  let ?T = "search_table r" let ?st = "search_project r"
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have at: "RBT.lookup (shared_goals (search_state r)) (shared_goal_position (shared_entry_goal h)) = Some h"
    using h by (auto simp: shared_access_simps tree_values_member dest: shared_goal_lookup_position[OF s])
  have closed: "search_project (search_remove_goal q r) = finite_goal_closed ?st g"
    if "RBT.lookup (shared_goals (search_state r)) q = Some h'" "shared_goal_project ?T (shared_entry_goal h') = g" for q h' g
    using shared_remove_goal(2-4)[OF s that(1)] search_remove_goal(2)[OF r that(1)] that(2)
    by (cases "search_project (search_remove_goal q r)") (simp add: finite_goal_closed_def)
  have closed_ok: "search_formed \<kappa> P (search_remove_goal q r) \<and> search_placeable (search_project (search_remove_goal q r))"
    if "RBT.lookup (shared_goals (search_state r)) q = Some h'" "shared_goal_project ?T (shared_entry_goal h') = g" for q h' g
    using search_remove_goal(1)[OF r that(1)] closed[OF that] search_placeable_fewer[OF pl]
    by (simp add: finite_goal_closed_def)
  show "fimage search_project (search_successors \<kappa> P r h) = finite_goal_successors P ?st (access_goal (shared_access \<kappa> P r) h)"
  proof (cases "shared_goal_project ?T (shared_entry_goal h)")
    case (Resolution_Call_Goal q rr d p)
    have q: "shared_goal_position (shared_entry_goal h) = q"
      using arg_cong[OF Resolution_Call_Goal, of resolution_goal_position] by simp
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at q by simp
    have reuse: "access_reusable (shared_access \<kappa> P r) h \<longleftrightarrow> finite_reusable ?st (Resolution_Call_Goal q rr d p)"
      using reusable[OF h] Resolution_Call_Goal by (simp add: shared_access_simps)
    show ?thesis
    proof (cases "access_reusable (shared_access \<kappa> P r) h")
      case True
      then show ?thesis using reuse closed[OF atq Resolution_Call_Goal] Resolution_Call_Goal
        by (simp add: search_successors_def shared_access_simps)
    next
      case False
      have "fimage search_project (fimage (search_call_state P r q rr d p) (finite_call_alternative_set P q d p)) =
          fimage (finite_call_alternative_state ?st q rr d p) (finite_call_alternative_set P q d p)"
        unfolding fset.map_comp comp_def
        by (rule fset.map_cong0) (rule search_call_state(2)[OF r pl sock atq Resolution_Call_Goal])
      then show ?thesis using False reuse Resolution_Call_Goal
        by (simp add: search_successors_def shared_access_simps finite_call_successors_alternatives)
    qed
  next
    case (Resolution_Material_Goal q rr M)
    have q: "shared_goal_position (shared_entry_goal h) = q"
      using arg_cong[OF Resolution_Material_Goal, of resolution_goal_position] by simp
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at q by simp
    have "fimage search_project (fimage (search_material_state P r q) (finite_material_alternative_set M)) =
        fimage (finite_material_alternative_state ?st q rr M) (finite_material_alternative_set M)"
      unfolding fset.map_comp comp_def
      by (rule fset.map_cong0) (rule search_material_state(2)[OF r pl atq Resolution_Material_Goal])
    then show ?thesis using Resolution_Material_Goal
      by (simp add: search_successors_def shared_access_simps finite_material_successors_alternatives)
  qed
  show "search_formed \<kappa> P s' \<and> search_placeable (search_project s')" if "s' |\<in>| search_successors \<kappa> P r h"
  proof (cases "shared_goal_project ?T (shared_entry_goal h)")
    case (Resolution_Call_Goal q rr d p)
    have q: "shared_goal_position (shared_entry_goal h) = q"
      using arg_cong[OF Resolution_Call_Goal, of resolution_goal_position] by simp
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at q by simp
    show ?thesis using that closed_ok[OF atq Resolution_Call_Goal]
      search_call_state(1,3)[OF r pl sock atq Resolution_Call_Goal] Resolution_Call_Goal
      by (auto simp: search_successors_def split: if_splits elim!: fimageE)
  next
    case (Resolution_Material_Goal q rr M)
    have q: "shared_goal_position (shared_entry_goal h) = q"
      using arg_cong[OF Resolution_Material_Goal, of resolution_goal_position] by simp
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at q by simp
    show ?thesis using that search_material_state(1,3)[OF r pl atq Resolution_Material_Goal] Resolution_Material_Goal
      by (auto simp: search_successors_def elim!: fimageE)
  qed
qed

section \<open>The shared search\<close>

text \<open>
  The shared state of an R3 state shares its ground terms once and places its goals and nodes (@{thm [source]
  share_resolution_state}); its registered positions are read from its goals, and no value is kept yet. The shared
  search is the representation's search over the shared state's access and steps; it is R3's search wherever R3's
  search keeps one goal and one node at a position, and so R3's search's code equation.
\<close>

definition search_of :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_of P st = (let s = share_resolution_state P st in
    \<lparr>search_state = s, search_registered = fold (\<lambda>z t. tree_add (fst z) (shared_goal_registered (snd z)) t)
      (RBT.entries (shared_goals s)) RBT.empty, search_values = RBT.empty\<rparr>)"

lemma tree_add_fold_member:
  "q |\<in>| tree_bucket (fold (\<lambda>z t. tree_add (fst z) (f (snd z)) t) xs t0) p \<longleftrightarrow>
    q |\<in>| tree_bucket t0 p \<or> (\<exists>h. (q,h) \<in> set xs \<and> p |\<in>| f h)"
  by (induction xs arbitrary: t0) auto

lemma search_of:
  assumes d: "resolution_positions_distinct st"
  shows "search_formed \<kappa> P (search_of P st)" and "search_project (search_of P st) = st"
proof -
  let ?s = "share_resolution_state P st"
  have s: "shared_state_formed \<kappa> P ?s" and p: "shared_state_project ?s = st" using share_resolution_state[OF d] by simp_all
  have rf: "search_registered_formed (search_of P st)"
    unfolding search_registered_formed_def search_of_def Let_def
    by (auto simp: tree_add_fold_member RBT.lookup_in_tree)
  have vf: "search_values_formed \<kappa> P (search_of P st)" by (simp add: search_values_formed_def search_of_def Let_def)
  show "search_formed \<kappa> P (search_of P st)" using s rf vf by (simp add: search_formed_def search_of_def Let_def)
  show "search_project (search_of P st) = st" using p by (simp add: search_of_def Let_def)
qed

definition shared_representation :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) resolution_representation" where
  "shared_representation \<kappa> P = \<lparr>rep_access = shared_access \<kappa> P, rep_empty = (\<lambda>r. RBT.is_empty (shared_goals (search_state r))),
    rep_project = (\<lambda>r. search_project r), rep_refresh = search_refresh \<kappa> P, rep_construct = search_construct \<kappa> P,
    rep_successors = search_successors \<kappa> P\<rparr>"

lemma rbt_is_empty_values: "RBT.is_empty t \<longleftrightarrow> tree_values t = {||}"
proof
  assume "RBT.is_empty t"
  then have "t = RBT.empty" by simp
  then show "tree_values t = {||}" by simp
next
  assume e: "tree_values t = {||}"
  have "RBT.lookup t k = None" for k
  proof (cases "RBT.lookup t k")
    case (Some v)
    then have "v |\<in>| tree_values t" by (auto simp: tree_values_member)
    then show ?thesis using e by simp
  qed simp
  then have "RBT.lookup t = Map.empty" by (intro ext) simp
  then have "t = RBT.empty" by (simp only: RBT.lookup_empty_empty)
  then show "RBT.is_empty t" by simp
qed

lemma rbt_empty_values: "t = RBT.empty \<longleftrightarrow> tree_values t = {||}"
  using rbt_is_empty_values[of t] by simp

theorem shared_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
  shows "represented_search (shared_representation \<kappa> P) (\<lambda>r h. False) \<kappa> P n (search_of P st) =
      finite_resolution_search \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "shared_representation \<kappa> P"
  let ?F = "\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r)"
  have "represented_search ?R (\<lambda>r h. False) \<kappa> P n (search_of P st) =
      finite_resolution_search_by (finite_resolution_select_at (\<lambda>st g. False) \<kappa> P) \<kappa> P n (rep_project ?R (search_of P st))"
  proof (rule represented_search[where F = ?F])
    show "?F (search_of P st)" using search_of[OF d] pl by simp
  next
    fix s assume "?F s"
    then show "access_formed \<kappa> P (rep_access ?R s) (rep_project ?R s)"
      using shared_access_formed[OF conjunct1[OF \<open>?F s\<close>]] by (simp add: shared_representation_def)
  next
    fix s assume f: "?F s"
    have "resolution_pending (search_project s) = fimage (\<lambda>h. shared_goal_project (search_table s) (shared_entry_goal h))
        (tree_values (shared_goals (search_state s)))" by (simp add: shared_state_project_fields)
    then show "rep_empty ?R s \<longleftrightarrow> resolution_pending (rep_project ?R s) = {||}"
      by (simp add: shared_representation_def rbt_empty_values)
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s) \<and> rep_project ?R (rep_refresh ?R s) = rep_project ?R s"
      using search_refresh[OF conjunct1[OF f]] conjunct2[OF f] by (simp add: shared_representation_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (shared_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "shared_access \<kappa> P s"] m by (auto simp: shared_representation_def)
    note c = search_construct[OF conjunct1[OF f] n]
    have "search_placeable (search_project (search_construct \<kappa> P s m))"
      unfolding c(2) finite_construction_step_def Let_def
      by (rule search_placeable_substitute, rule search_placeable_witnesses[OF conjunct2[OF f]])
    then show "?F (rep_construct ?R s m) \<and>
        rep_project ?R (rep_construct ?R s m) = finite_construction_step \<kappa> P (rep_project ?R s) (access_node (rep_access ?R s) m)"
      using c by (simp add: shared_representation_def)
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    note sc = search_successors[OF conjunct1[OF f] conjunct2[OF f] sock, of h]
    show "fimage (rep_project ?R) (rep_successors ?R s h) =
        finite_goal_successors P (rep_project ?R s) (access_goal (rep_access ?R s) h) \<and>
        (\<forall>s'. s' |\<in>| rep_successors ?R s h \<longrightarrow> ?F s')"
      using sc h by (simp add: shared_representation_def)
  next
    fix s h show "False \<longleftrightarrow> False" by simp
  qed
  then show ?thesis using search_of(2)[OF d] by (simp add: finite_resolution_search_def shared_representation_def)
qed

text \<open>
  R3's search is computed over the shared state where R3's search keeps one goal and one node at a position, and over
  F2b1's indexed state elsewhere; the two coincide with R3's, so the equation holds at every input, at the search's
  general type.
\<close>

declare finite_resolution_search_code [code del]

lemma finite_resolution_search_shared_code [code]:
  "finite_resolution_search \<kappa> P n st = (if clause_sockets_distinct P \<and> search_placeable st
    then represented_search (shared_representation \<kappa> P) (\<lambda>r h. False) \<kappa> P n (search_of P st)
    else indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st))"
  using shared_search[of P st \<kappa> n] finite_resolution_search_code[of \<kappa> P n st] by simp

export_code finite_resolution_search checking SML

end
