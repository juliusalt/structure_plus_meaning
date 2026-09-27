theory Factor_Deferred_Search
  imports Factor_Shared_Search Shared_Binding_Stores
begin

section \<open>The deferred search\<close>

text \<open>
  Build D1b of DECISIONS.md, task 495's entry, its addition "The step at the given's depth" (task 903): a third instance
  of the search representation over F2's shared search, whose nodes are kept as placed and read through D1a's binding
  store (@{text Shared_Binding_Stores}). A step substitutes the goals as the shared search does and records its unifier in
  the store; a node's call variables change by the store's variables law, a record keyed by numbers, and a node is
  resolved once in the shared state, when its call becomes ground, and otherwise only where the access decodes it.

  A number is a key and nothing else: the positions of the nodes are numbered by their first occurrence
  (@{text keyed_reference_step} at the position itself), the names of the variables the search meets by theirs
  (@{text value_reference_step}), and a variable's key is its position's number, its flag and its name's number,
  injective on the numbered variables. The store is D1a's tree at that key; each node's record holds its call's current
  variables as a keyed set, and the holder index maps a variable's key to the numbers of the nodes whose call holds it.
  No number is presented, compared across searches, or read where an order of positions is.
\<close>

subsection \<open>A shared pattern's variables, listed by its structure\<close>

text \<open>A formed pattern's variables in the order of its structure, a node holding none not walked.\<close>

fun shared_variable_list :: "'a shared_pattern \<Rightarrow> 'a list" where
  "shared_variable_list (Shared_Variable a) = [a]"
| "shared_variable_list (Shared_Ground i) = []"
| "shared_variable_list (Shared_Node A p q) = (if A = {||} then [] else shared_variable_list p @ shared_variable_list q)"

lemma shared_variable_list:
  "shared_pattern_formed T p \<Longrightarrow> set (shared_variable_list p) = fset (shared_pattern_variables p)"
  by (induction p) auto

subsection \<open>Numbers and keys\<close>

type_synonym 's position_numbering = "('s list, nat) rbt \<times> nat \<times> 's list list"
type_synonym deferred_key = "nat \<times> bool \<times> nat"

definition position_number :: "'s::linorder position_numbering \<Rightarrow> 's list \<Rightarrow> nat" where
  "position_number N p = (case RBT.lookup (fst N) p of Some i \<Rightarrow> Suc i | None \<Rightarrow> 0)"

definition name_number :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "name_number L a = (case value_reference_index a L of Some i \<Rightarrow> Suc i | None \<Rightarrow> 0)"

definition positions_numbered :: "'s::linorder position_numbering \<Rightarrow> bool" where
  "positions_numbered N \<longleftrightarrow> (\<exists>T. keyed_reference_state id N T)"

record (overloaded) ('a,'s::linorder,'d,'c) deferred_search =
  deferred_inner :: "('a,'s,'d,'c) shared_search"
  deferred_tree :: "(deferred_key, ('s,'a) resolution_variable) binding_tree"
  deferred_positions :: "'s position_numbering"
  deferred_names :: "'a list"
  deferred_records :: "(nat, 's list \<times> (deferred_key, unit) rbt) rbt"
  deferred_holders :: "(deferred_key, nat fset) rbt"

definition deferred_key :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> deferred_key" where
  "deferred_key d x = (position_number (deferred_positions d) (fst (fst x)), snd (fst x),
    name_number (deferred_names d) (snd x))"

definition deferred_numbered :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> bool" where
  "deferred_numbered d x \<longleftrightarrow> position_number (deferred_positions d) (fst (fst x)) \<noteq> 0 \<and>
    name_number (deferred_names d) (snd x) \<noteq> 0"

definition deferred_decode :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> deferred_key \<Rightarrow> ('s,'a) resolution_variable" where
  "deferred_decode d k = (case k of (n,b,m) \<Rightarrow>
    ((rev (snd (snd (deferred_positions d))) ! (n - 1), b), deferred_names d ! (m - 1)))"

lemma deferred_decode_key:
  assumes N: "positions_numbered (deferred_positions d)" and x: "deferred_numbered d x"
  shows "deferred_decode d (deferred_key d x) = x"
proof -
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  obtain M n R where e: "deferred_positions d = (M,n,R)" by (cases "deferred_positions d") auto
  have R: "R = rev T" and M: "\<And>y. RBT.lookup M y = value_reference_index y T"
    using T by (simp_all add: e keyed_reference_state_def)
  obtain p b a where xx: "x = ((p,b),a)" by (cases x) auto
  obtain i where i: "RBT.lookup M p = Some i"
    using x by (auto simp: deferred_numbered_def position_number_def e xx split: option.splits)
  obtain j where j: "value_reference_index a (deferred_names d) = Some j"
    using x by (auto simp: deferred_numbered_def name_number_def xx split: option.splits)
  have "T ! i = p" using value_reference_index_read[of p T i] i M by simp
  moreover have "deferred_names d ! j = a" using value_reference_index_read[OF j] by simp
  ultimately show ?thesis using i j R
    by (simp add: deferred_decode_def deferred_key_def position_number_def name_number_def e xx)
qed

lemma deferred_key_inj:
  assumes N: "positions_numbered (deferred_positions d)"
    and x: "deferred_numbered d x" and y: "deferred_numbered d y" and k: "deferred_key d x = deferred_key d y"
  shows "x = y"
  using deferred_decode_key[OF N x] deferred_decode_key[OF N y] k by metis

subsection \<open>The store and the projection\<close>

definition deferred_store :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('s,'a) resolution_variable binding_store" where
  "deferred_store d = binding_tree_store (deferred_key d) (deferred_tree d)"

definition deferred_substitution :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern" where
  "deferred_substitution d x =
    shared_pattern_project (search_table (deferred_inner d)) (binding_substitution (deferred_store d) x)"

text \<open>
  The deferred search presents R3's state of its shared search with every node resolved through the store; no goal
  holds a variable the store binds (@{text deferred_formed}), so the goals stand as they are.
\<close>

definition deferred_project :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "deferred_project d = resolution_state_substitute (deferred_substitution d) (search_project (deferred_inner d))"

definition derivation_resolve :: "('s,'a) resolution_variable binding_store \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow>
    ('a,'s,'d,'c) shared_derivation" where
  "derivation_resolve S nd = Shared_Derivation (shared_derivation_position nd) (shared_derivation_site nd)
    (shared_derivation_clause nd) (shared_derivation_schema nd) (binding_resolve S (shared_derivation_call nd))
    (fimage (\<lambda>z. (fst z, binding_resolve S (snd z))) (shared_derivation_bindings nd))"

lemma derivation_resolve_fields [simp]:
  "shared_derivation_position (derivation_resolve S nd) = shared_derivation_position nd"
  "shared_derivation_site (derivation_resolve S nd) = shared_derivation_site nd"
  "shared_derivation_clause (derivation_resolve S nd) = shared_derivation_clause nd"
  "shared_derivation_schema (derivation_resolve S nd) = shared_derivation_schema nd"
  "shared_derivation_call (derivation_resolve S nd) = binding_resolve S (shared_derivation_call nd)"
  "shared_derivation_bindings (derivation_resolve S nd) =
    fimage (\<lambda>z. (fst z, binding_resolve S (snd z))) (shared_derivation_bindings nd)"
  by (simp_all add: derivation_resolve_def)

lemma derivation_resolve_project:
  assumes S: "binding_store_formed T S" and nd: "shared_derivation_formed T nd"
  shows "shared_derivation_project T (derivation_resolve S nd) =
    resolution_node_substitute (\<lambda>x. shared_pattern_project T (binding_substitution S x)) (shared_derivation_project T nd)"
proof -
  let ?\<sigma> = "\<lambda>x. shared_pattern_project T (binding_substitution S x)"
  have c: "shared_pattern_formed T (shared_derivation_call nd)" using nd by (simp add: shared_derivation_formed_def)
  have b: "shared_pattern_project T (binding_resolve S (snd z)) = finite_pattern_substitute ?\<sigma> (shared_pattern_project T (snd z))"
    if "z |\<in>| shared_derivation_bindings nd" for z
    using binding_resolve_project[OF S] that nd by (auto simp: shared_derivation_formed_def)
  have B: "fimage (\<lambda>z. (fst z, shared_pattern_project T (binding_resolve S (snd z)))) (shared_derivation_bindings nd) =
      fimage (\<lambda>z. (fst z, finite_pattern_substitute ?\<sigma> (shared_pattern_project T (snd z)))) (shared_derivation_bindings nd)"
    by (rule fset.map_cong0) (simp add: b)
  show ?thesis using binding_resolve_project[OF S c] B
    by (simp add: derivation_resolve_def shared_derivation_project_def fset.map_comp comp_def split_def)
qed

subsection \<open>Dereferencing: whether a resolution is a variable\<close>

text \<open>
  A resolution is a variable exactly when following the store's variable bindings from the pattern ends at an unbound
  variable: the chain is followed and no pattern is built.
\<close>

function binding_deref_from :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow>
    'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "binding_deref_from n r M (Shared_Variable a) = (case M a of
      Some (r', q) \<Rightarrow> (if r \<le> r' \<and> r' < n then binding_deref_from n (Suc r') M q else Shared_Variable a)
    | None \<Rightarrow> Shared_Variable a)"
| "binding_deref_from n r M (Shared_Ground i) = Shared_Ground i"
| "binding_deref_from n r M (Shared_Node A p q) = Shared_Node A p q"
  by pat_completeness auto
termination by (relation "measure (\<lambda>(n, r, M, p). n - r)") auto

definition binding_deref :: "'a binding_store \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "binding_deref S = binding_deref_from (binding_next_rank S) 0 (binding_map S)"

lemma binding_resolve_from_deref:
  "binding_resolve_from n r M p = Shared_Variable x \<longleftrightarrow> binding_deref_from n r M p = Shared_Variable x"
proof (induction n r M p rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  then show ?case by simp
next
  case (unbound n r M a)
  then show ?case by (auto split: option.splits prod.splits)
next
  case (ground n r M i)
  then show ?case by simp
next
  case (node n r M A p q)
  then show ?case by (simp add: shared_node_def)
qed

lemma binding_resolve_variable:
  "binding_resolve S p = Shared_Variable x \<longleftrightarrow> binding_deref S p = Shared_Variable x"
  by (simp add: binding_resolve_def binding_deref_def binding_resolve_from_deref)

subsection \<open>Formation\<close>

abbreviation deferred_call :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow>
    ('s,'a) resolution_variable shared_pattern" where
  "deferred_call d hn \<equiv> binding_resolve (deferred_store d) (shared_derivation_call (shared_entry_node hn))"

text \<open>
  A node's clauses: its position numbered, its record holding its position and exactly the keys of its resolved call's
  variables, every one of them numbered, the node in the bucket of each, and a node whose resolved call is ground
  resolved in the shared state, its call holding no variable.
\<close>

definition deferred_node_formed :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> 's list \<Rightarrow> bool" where
  "deferred_node_formed d q \<longleftrightarrow> (\<forall>hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<longrightarrow>
    position_number (deferred_positions d) q \<noteq> 0 \<and>
    (\<exists>K. RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K) \<and>
      set (RBT.keys K) = deferred_key d ` fset (shared_pattern_variables (deferred_call d hn))) \<and>
    fBall (shared_pattern_variables (deferred_call d hn)) (deferred_numbered d) \<and>
    fBall (shared_pattern_variables (deferred_call d hn))
      (\<lambda>x. position_number (deferred_positions d) q |\<in>| tree_bucket (deferred_holders d) (deferred_key d x)) \<and>
    (shared_pattern_variables (deferred_call d hn) = {||} \<longrightarrow>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||}))"

text \<open>
  The state's clauses: the shared search formed with its classes, the positions numbered, the store formed over the
  table, its tree keyed by keys of numbered variables, every variable it binds and every goal's variable positioned at
  a node, no goal holding a variable it binds, and every record at the number of its position, where a node stands.
\<close>

definition deferred_parts_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> bool" where
  "deferred_parts_formed \<kappa> P d \<longleftrightarrow> search_formed \<kappa> P (deferred_inner d) \<and> search_classes_formed (deferred_inner d) \<and>
    positions_numbered (deferred_positions d) \<and>
    binding_store_formed (search_table (deferred_inner d)) (deferred_store d) \<and>
    (\<forall>k v. RBT.lookup (snd (deferred_tree d)) k = Some v \<longrightarrow> (\<exists>x. deferred_numbered d x \<and> deferred_key d x = k)) \<and>
    (\<forall>x. binding_map (deferred_store d) x \<noteq> None \<longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None) \<and>
    (\<forall>q h x. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store d) x = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None) \<and>
    (\<forall>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<longrightarrow> n \<noteq> 0 \<and>
      n = position_number (deferred_positions d) q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None)"

definition deferred_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> bool" where
  "deferred_formed \<kappa> P d \<longleftrightarrow> deferred_parts_formed \<kappa> P d \<and> (\<forall>q. deferred_node_formed d q)"

lemma deferred_formedD:
  assumes "deferred_formed \<kappa> P d"
  shows "search_formed \<kappa> P (deferred_inner d)" "search_classes_formed (deferred_inner d)"
    "positions_numbered (deferred_positions d)"
    "binding_store_formed (search_table (deferred_inner d)) (deferred_store d)"
    "\<And>k v. RBT.lookup (snd (deferred_tree d)) k = Some v \<Longrightarrow> \<exists>x. deferred_numbered d x \<and> deferred_key d x = k"
    "\<And>x. binding_map (deferred_store d) x \<noteq> None \<Longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None"
    "\<And>q h x. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<Longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow> binding_map (deferred_store d) x = None"
    "\<And>q h x. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<Longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None"
    "\<And>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow> n = position_number (deferred_positions d) q"
    "\<And>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
    "\<And>q. deferred_node_formed d q"
  using assms unfolding deferred_formed_def deferred_parts_formed_def by blast+

lemma deferred_node_formedD:
  assumes "deferred_node_formed d q" and "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
  shows "position_number (deferred_positions d) q \<noteq> 0"
    "\<exists>K. RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K) \<and>
      set (RBT.keys K) = deferred_key d ` fset (shared_pattern_variables (deferred_call d hn))"
    "\<And>x. x |\<in>| shared_pattern_variables (deferred_call d hn) \<Longrightarrow> deferred_numbered d x"
    "\<And>x. x |\<in>| shared_pattern_variables (deferred_call d hn) \<Longrightarrow>
      position_number (deferred_positions d) q |\<in>| tree_bucket (deferred_holders d) (deferred_key d x)"
    "shared_pattern_variables (deferred_call d hn) = {||} \<Longrightarrow>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||}"
  using assms unfolding deferred_node_formed_def by blast+

subsection \<open>The access\<close>

text \<open>
  The access of the shared search with its node fields read through the store: a node decoded at its resolution, the
  registered variables it leaves free found by following the store from its bindings, the construction's value read
  at the resolved node, and its call's variables read from its record.
\<close>

definition deferred_node :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow>
    ('a,'s,'d,'c) resolution_node" where
  "deferred_node d hn = shared_derivation_project (search_table (deferred_inner d))
    (derivation_resolve (deferred_store d) (shared_entry_node hn))"

definition deferred_free :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset" where
  "deferred_free \<kappa> d hn = ffilter (\<lambda>a. fBex (shared_derivation_bindings (shared_entry_node hn))
      (\<lambda>z. fst z = a \<and> binding_deref (deferred_store d) (snd z) =
        Shared_Variable ((shared_derivation_position (shared_entry_node hn),True),a)))
    (witness_registered \<kappa> (shared_derivation_site (shared_entry_node hn)) (shared_derivation_schema (shared_entry_node hn)))"

definition deferred_call_variables :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow>
    ('s,'a) resolution_variable fset" where
  "deferred_call_variables d hn = (case RBT.lookup (deferred_records d)
      (position_number (deferred_positions d) (shared_derivation_position (shared_entry_node hn))) of
    None \<Rightarrow> {||} | Some z \<Rightarrow> fimage (deferred_decode d) (fset_of_list (RBT.keys (snd z))))"

definition deferred_access :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) search_access" where
  "deferred_access \<kappa> P d = (shared_access \<kappa> P (deferred_inner d))\<lparr>access_node := deferred_node d,
    access_free := deferred_free \<kappa> d,
    access_value_none := \<lambda>hn a. finite_registered_value \<kappa> P (deferred_node d hn) a = None,
    access_call_variables := deferred_call_variables d\<rparr>"

lemma deferred_node_entry:
  assumes d: "deferred_formed \<kappa> P d" and n: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
  shows "node_entry_formed (search_table (deferred_inner d)) q hn"
  using shared_entries_formed(2)[OF search_formedD(1)[OF deferred_formedD(1)[OF d]] n] .

lemma deferred_node_substitute:
  assumes d: "deferred_formed \<kappa> P d" and n: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
  shows "deferred_node d hn = resolution_node_substitute (deferred_substitution d)
    (shared_derivation_project (search_table (deferred_inner d)) (shared_entry_node hn))"
proof -
  have "shared_derivation_formed (search_table (deferred_inner d)) (shared_entry_node hn)"
    using deferred_node_entry[OF d n] by (simp add: node_entry_formed_def)
  moreover have "deferred_substitution d =
      (\<lambda>x. shared_pattern_project (search_table (deferred_inner d)) (binding_substitution (deferred_store d) x))"
    by (simp add: fun_eq_iff deferred_substitution_def)
  ultimately show ?thesis using derivation_resolve_project[OF deferred_formedD(4)[OF d]]
    by (simp add: deferred_node_def)
qed

lemma deferred_goal_fixed:
  assumes d: "deferred_formed \<kappa> P d" and h: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
  shows "resolution_goal_substitute (deferred_substitution d)
      (shared_goal_project (search_table (deferred_inner d)) (shared_entry_goal h)) =
    shared_goal_project (search_table (deferred_inner d)) (shared_entry_goal h)"
proof (rule resolution_goal_substitute_outside)
  let ?T = "search_table (deferred_inner d)"
  have gf: "goal_entry_formed P ?T q h"
    using shared_entries_formed(1)[OF search_formedD(1)[OF deferred_formedD(1)[OF d]] h] .
  fix x assume "x |\<in>| resolution_goal_variables (shared_goal_project ?T (shared_entry_goal h))"
  then have "x |\<in>| shared_goal_variables (shared_entry_goal h)" using goal_entry_variables[OF gf] by simp
  then have "binding_map (deferred_store d) x = None" by (rule deferred_formedD(7)[OF d h])
  then show "deferred_substitution d x = Finite_Variable x"
    using binding_resolve_unbound[of "Shared_Variable x" "deferred_store d"]
    by (simp add: deferred_substitution_def binding_substitution_def)
qed

lemma deferred_pending:
  assumes d: "deferred_formed \<kappa> P d"
  shows "resolution_pending (deferred_project d) = resolution_pending (search_project (deferred_inner d))"
proof -
  have "fimage (resolution_goal_substitute (deferred_substitution d)) (resolution_pending (search_project (deferred_inner d))) =
      resolution_pending (search_project (deferred_inner d))"
  proof (rule fimage_fixed)
    fix g assume "g |\<in>| resolution_pending (search_project (deferred_inner d))"
    then obtain q h where "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
      "g = shared_goal_project (search_table (deferred_inner d)) (shared_entry_goal h)"
      unfolding shared_state_project_member(1) by metis
    then show "resolution_goal_substitute (deferred_substitution d) g = g" using deferred_goal_fixed[OF d] by simp
  qed
  then show ?thesis by (simp add: deferred_project_def)
qed

lemma deferred_node_call_ground:
  assumes d: "deferred_formed \<kappa> P d" and n: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
    and p: "finite_pattern_variables p = {||}"
  shows "resolution_node_call (deferred_node d hn) = p \<longleftrightarrow>
    shared_pattern_project (search_table (deferred_inner d)) (shared_derivation_call (shared_entry_node hn)) = p"
proof -
  let ?T = "search_table (deferred_inner d)" and ?S = "deferred_store d" and ?c = "shared_derivation_call (shared_entry_node hn)"
  have S: "binding_store_formed ?T ?S" using deferred_formedD(4)[OF d] .
  have cf: "shared_pattern_formed ?T ?c" using deferred_node_entry[OF d n] by (simp add: node_entry_formed_def shared_derivation_formed_def)
  have rf: "shared_pattern_formed ?T (binding_resolve ?S ?c)" by (rule binding_resolve_formed[OF S cf])
  have call: "resolution_node_call (deferred_node d hn) = shared_pattern_project ?T (binding_resolve ?S ?c)"
    by (simp add: deferred_node_def)
  show ?thesis
  proof
    assume e: "resolution_node_call (deferred_node d hn) = p"
    have "shared_pattern_variables (binding_resolve ?S ?c) = {||}"
      using e p call shared_pattern_variables_project[OF rf] by simp
    then have "shared_pattern_variables ?c = {||}" by (rule deferred_node_formedD(5)[OF deferred_formedD(11)[OF d] n])
    then have "binding_resolve ?S ?c = ?c" by (intro binding_resolve_unbound) simp
    then show "shared_pattern_project ?T ?c = p" using e call by simp
  next
    assume e: "shared_pattern_project ?T ?c = p"
    have "shared_pattern_variables ?c = {||}" using e p shared_pattern_variables_project[OF cf] by simp
    then have "binding_resolve ?S ?c = ?c" by (intro binding_resolve_unbound) simp
    then show "resolution_node_call (deferred_node d hn) = p" using e call by simp
  qed
qed

lemma deferred_free_exact:
  assumes d: "deferred_formed \<kappa> P d" and n: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
  shows "deferred_free \<kappa> d hn = finite_free_registered \<kappa> (deferred_node d hn)"
proof -
  let ?T = "search_table (deferred_inner d)" and ?S = "deferred_store d" and ?nd = "shared_entry_node hn"
  have B: "resolution_node_bindings (deferred_node d hn) =
      fimage (\<lambda>z. (fst z, shared_pattern_project ?T (binding_resolve ?S (snd z)))) (shared_derivation_bindings ?nd)"
    by (simp add: deferred_node_def shared_derivation_project_def fset.map_comp comp_def)
  have mem: "(a, Finite_Variable x) |\<in>| resolution_node_bindings (deferred_node d hn) \<longleftrightarrow>
      fBex (shared_derivation_bindings ?nd) (\<lambda>z. fst z = a \<and> binding_deref ?S (snd z) = Shared_Variable x)" for a x
  proof -
    have "(a, Finite_Variable x) |\<in>| fimage (\<lambda>z. (fst z, shared_pattern_project ?T (binding_resolve ?S (snd z))))
        (shared_derivation_bindings ?nd) \<longleftrightarrow>
      fBex (shared_derivation_bindings ?nd) (\<lambda>z. fst z = a \<and> Finite_Variable x = shared_pattern_project ?T (binding_resolve ?S (snd z)))"
      by (auto simp: fimage_iff)
    then show ?thesis unfolding B eq_commute[of "Finite_Variable x"] shared_pattern_project_variable binding_resolve_variable .
  qed
  have f: "resolution_node_site (deferred_node d hn) = shared_derivation_site ?nd"
    "resolution_node_schema (deferred_node d hn) = shared_derivation_schema ?nd"
    "resolution_node_position (deferred_node d hn) = shared_derivation_position ?nd"
    by (simp_all add: deferred_node_def)
  show ?thesis unfolding deferred_free_def finite_free_registered_def mem f by (rule refl)
qed

lemma deferred_call_variables_exact:
  assumes d: "deferred_formed \<kappa> P d" and n: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
  shows "deferred_call_variables d hn = finite_pattern_variables (resolution_node_call (deferred_node d hn))"
proof -
  let ?T = "search_table (deferred_inner d)" and ?S = "deferred_store d" and ?c = "shared_derivation_call (shared_entry_node hn)"
  let ?V = "shared_pattern_variables (binding_resolve ?S ?c)"
  have S: "binding_store_formed ?T ?S" using deferred_formedD(4)[OF d] .
  have N: "positions_numbered (deferred_positions d)" using deferred_formedD(3)[OF d] .
  have nf: "deferred_node_formed d q" using deferred_formedD(11)[OF d] .
  have pos: "shared_derivation_position (shared_entry_node hn) = q"
    using deferred_node_entry[OF d n] by (simp add: node_entry_formed_def)
  have cf: "shared_pattern_formed ?T ?c" using deferred_node_entry[OF d n] by (simp add: node_entry_formed_def shared_derivation_formed_def)
  have rf: "shared_pattern_formed ?T (binding_resolve ?S ?c)" by (rule binding_resolve_formed[OF S cf])
  obtain K where K: "RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K)"
    and keys: "set (RBT.keys K) = deferred_key d ` fset ?V" using deferred_node_formedD(2)[OF nf n] by blast
  have num: "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_numbered d x" by (rule deferred_node_formedD(3)[OF nf n])
  have "fimage (deferred_decode d) (fset_of_list (RBT.keys K)) = ?V"
  proof (rule fset_eqI)
    fix x
    have "x |\<in>| fimage (deferred_decode d) (fset_of_list (RBT.keys K)) \<longleftrightarrow> x \<in> deferred_decode d ` set (RBT.keys K)"
      by (simp add: fimage.rep_eq fset_of_list.rep_eq)
    also have "\<dots> \<longleftrightarrow> x \<in> fset ?V" unfolding keys image_image using deferred_decode_key[OF N num] by (auto simp: image_iff)
    finally show "x |\<in>| fimage (deferred_decode d) (fset_of_list (RBT.keys K)) \<longleftrightarrow> x |\<in>| ?V" by simp
  qed
  then show ?thesis using K pos shared_pattern_variables_project[OF rf]
    by (simp add: deferred_call_variables_def deferred_node_def)
qed

theorem deferred_access_formed:
  assumes d: "deferred_formed \<kappa> P d"
  shows "access_formed \<kappa> P (deferred_access \<kappa> P d) (deferred_project d)"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r"
  let ?V0 = "shared_access \<kappa> P ?r" let ?st0 = "search_project ?r" let ?\<sigma> = "deferred_substitution d"
  have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
  interpret A0: access_formed \<kappa> P ?V0 ?st0 by (rule shared_access_formed[OF r])
  have pend: "resolution_pending (deferred_project d) = resolution_pending ?st0" by (rule deferred_pending[OF d])
  have nodes: "resolution_nodes (deferred_project d) = fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes ?st0)"
    by (simp add: deferred_project_def)
  have at: "RBT.lookup (shared_nodes ?s) q = Some n" if "n |\<in>| access_nodes_at ?V0 q" for n q
    using that by (cases "RBT.lookup (shared_nodes ?s) q") (simp_all add: shared_access_simps option_fset_def)
  have node: "access_node (deferred_access \<kappa> P d) n = resolution_node_substitute ?\<sigma> (access_node ?V0 n)"
    if "n |\<in>| access_nodes_at ?V0 q" for n q
    using deferred_node_substitute[OF d at[OF that]] by (simp add: deferred_access_def shared_access_simps)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 1 show ?case using A0.pending pend by (simp add: deferred_access_def)
  next
    case (2 h q) show ?case using A0.goals_at by (simp add: deferred_access_def)
  next
    case (3 h h') then show ?case using A0.goal_inj by (simp add: deferred_access_def)
  next
    case (4 h) then show ?case using A0.goal_position by (simp add: deferred_access_def)
  next
    case (5 h) then show ?case using A0.variables by (simp add: deferred_access_def)
  next
    case (6 h) then show ?case using A0.alternatives by (simp add: deferred_access_def)
  next
    case (7 h) then show ?case using A0.is_call by (simp add: deferred_access_def)
  next
    case (8 h) then show ?case using A0.solvable by (simp add: deferred_access_def)
  next
    case (9 h) then show ?case using A0.leaf by (simp add: deferred_access_def)
  next
    case (10 n q)
    then have n: "n |\<in>| access_nodes_at ?V0 q" by (simp add: deferred_access_def)
    show ?case using deferred_call_variables_exact[OF d at[OF n]] by (simp add: deferred_access_def)
  next
    case (11 h)
    then have hg: "h |\<in>| access_goals ?V0" and held: "finite_held \<kappa> (deferred_project d) (access_goal ?V0 h)"
      by (simp_all add: deferred_access_def)
    obtain p a where "((p,True),a) |\<in>| resolution_goal_variables (access_goal ?V0 h)"
      using held unfolding finite_held_def by (elim fBexE) blast
    then have "((p,True),a) |\<in>| shared_goal_variables (shared_entry_goal h)"
      using A0.variables[OF hg] by (simp add: shared_access_simps)
    then have "shared_goal_registered h \<noteq> {||}" using shared_goal_registered_member by blast
    then show ?case by (simp add: deferred_access_def shared_access_simps)
  next
    case (12 nd)
    show ?case
    proof
      assume "nd |\<in>| resolution_nodes (deferred_project d)"
      then obtain nd0 where nd0: "nd0 |\<in>| resolution_nodes ?st0" and e: "nd = resolution_node_substitute ?\<sigma> nd0"
        unfolding nodes by blast
      obtain n where n: "n |\<in>| access_nodes_at ?V0 (resolution_node_position nd0)" and a: "access_node ?V0 n = nd0"
        using nd0 unfolding A0.nodes[of nd0] by blast
      show "\<exists>n. n |\<in>| access_nodes_at (deferred_access \<kappa> P d) (resolution_node_position nd) \<and>
          access_node (deferred_access \<kappa> P d) n = nd"
        using n a e node[OF n] by (auto simp: deferred_access_def)
    next
      assume "\<exists>n. n |\<in>| access_nodes_at (deferred_access \<kappa> P d) (resolution_node_position nd) \<and>
          access_node (deferred_access \<kappa> P d) n = nd"
      then obtain n where n: "n |\<in>| access_nodes_at ?V0 (resolution_node_position nd)"
        and a: "access_node (deferred_access \<kappa> P d) n = nd" by (auto simp: deferred_access_def)
      have p0: "resolution_node_position (access_node ?V0 n) = resolution_node_position nd" using A0.node_at[OF n] by simp
      have "access_node ?V0 n |\<in>| resolution_nodes ?st0"
        unfolding A0.nodes[of "access_node ?V0 n"] p0 using n by blast
      then show "nd |\<in>| resolution_nodes (deferred_project d)" unfolding nodes using a node[OF n] by blast
    qed
  next
    case (13 n q)
    then have n: "n |\<in>| access_nodes_at ?V0 q" by (simp add: deferred_access_def)
    show ?case using A0.node_at[OF n] node[OF n] by (simp add: deferred_access_def)
  next
    case (14 n q)
    then have n: "n |\<in>| access_nodes_at ?V0 q" by (simp add: deferred_access_def)
    show ?case using deferred_free_exact[OF d at[OF n]] by (simp add: deferred_access_def)
  next
    case (15 n q a) show ?case by (simp add: deferred_access_def)
  next
    case (16 h q rr dd p n q')
    then have hg: "h |\<in>| access_goals ?V0" and g: "access_goal ?V0 h = Resolution_Call_Goal q rr dd p"
      and pv: "finite_pattern_variables p = {||}" and n: "n |\<in>| access_nodes_at ?V0 q'"
      by (simp_all add: deferred_access_def)
    have c: "access_closes ?V0 n h \<longleftrightarrow> resolution_node_site (access_node ?V0 n) = dd \<and> resolution_node_call (access_node ?V0 n) = p"
      by (rule A0.closes[OF hg g pv n])
    have e: "resolution_node_call (deferred_node d n) = p \<longleftrightarrow> resolution_node_call (access_node ?V0 n) = p"
      using deferred_node_call_ground[OF d at[OF n] pv] by (simp add: shared_access_simps)
    have s: "resolution_node_site (deferred_node d n) = resolution_node_site (access_node ?V0 n)"
      by (simp add: deferred_node_def shared_access_simps)
    show ?case using c e s by (simp add: deferred_access_def)
  next
    case (17 h q rr dd p n q')
    then show ?case using A0.node_calls by (simp add: deferred_access_def)
  next
    case (18 h h' q rr dd p)
    then show ?case using A0.same by (simp add: deferred_access_def)
  next
    case (19 h h' q rr dd p)
    then show ?case using A0.goal_calls by (simp add: deferred_access_def)
  next
    case (20 nd)
    then obtain nd0 where nd0: "nd0 |\<in>| resolution_nodes ?st0" and e: "nd = resolution_node_substitute ?\<sigma> nd0"
      unfolding nodes by blast
    have "access_open ?V0 (resolution_node_position nd0) = 0 \<longleftrightarrow> finite_solved_node ?st0 nd0" by (rule A0.solved[OF nd0])
    then show ?case using e pend by (simp add: deferred_access_def finite_solved_node_def)
  next
    case (21 h x)
    then show ?case using A0.holders by (simp add: deferred_access_def)
  next
    case (22 g z b)
    then show ?case using A0.registered pend by (simp add: deferred_access_def)
  next
    case 23 show ?case using A0.witnesses by (simp add: deferred_access_def deferred_project_def resolution_state_substitute_def)
  qed
qed

subsection \<open>Numbering keeps the numbers it gave\<close>

text \<open>A step's table extends the table it was given by the value alone (@{thm [source] value_reference_step_table}).\<close>

lemma value_reference_add_extends:
  "\<exists>U. value_reference_add x T = T @ U" "set (value_reference_add x T) = insert x (set T)"
  by (auto simp: value_reference_add_def)

lemma value_reference_add_fold: "set (fold value_reference_add xs T) = set T \<union> set xs"
  by (induction xs arbitrary: T) (auto simp: value_reference_add_extends(2))

lemma position_number_table:
  assumes "keyed_reference_state id N T"
  shows "position_number N p = (case value_reference_index p T of Some i \<Rightarrow> Suc i | None \<Rightarrow> 0)"
  using assms by (cases N) (simp add: position_number_def keyed_reference_state_def)

lemma position_number_nonzero:
  assumes "keyed_reference_state id N T"
  shows "position_number N p \<noteq> 0 \<longleftrightarrow> p \<in> set T"
  using value_reference_index_absent[of p T] by (auto simp: position_number_table[OF assms] split: option.splits)

lemma position_number_extends:
  assumes "keyed_reference_state id N T" "keyed_reference_state id N' (T @ U)" "p \<in> set T"
  shows "position_number N' p = position_number N p"
  using assms by (simp add: position_number_table value_reference_index_append_member)

lemma position_number_inj:
  assumes N: "keyed_reference_state id N T" and e: "position_number N p = position_number N p'" and p: "position_number N p \<noteq> 0"
  shows "p = p'"
proof -
  obtain i where i: "value_reference_index p T = Some i" using p by (auto simp: position_number_table[OF N] split: option.splits)
  have "value_reference_index p' T = Some i" using e i by (auto simp: position_number_table[OF N] split: option.splits)
  then show ?thesis using value_reference_index_read[OF i] value_reference_index_read[of p' T i] by simp
qed

lemma keyed_reference_step_table:
  assumes "keyed_reference_state id N T"
  shows "keyed_reference_state id (snd (keyed_reference_step id q N)) (snd (value_reference_step q T))"
  using keyed_reference_step_exact[OF inj_on_id assms] by simp

lemma name_number_nonzero: "name_number L a \<noteq> 0 \<longleftrightarrow> a \<in> set L"
  using value_reference_index_absent[of a L] by (auto simp: name_number_def split: option.splits)

lemma name_number_extends: "a \<in> set L \<Longrightarrow> name_number (L @ U) a = name_number L a"
  by (simp add: name_number_def value_reference_index_append_member)

definition deferred_number_names :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "deferred_number_names as L = fold (\<lambda>a L. snd (value_reference_step a L)) as L"

lemma deferred_number_names:
  "\<exists>U. deferred_number_names as L = L @ U" "set (deferred_number_names as L) = set L \<union> set as"
proof -
  have "(\<exists>U. fold (\<lambda>a L. snd (value_reference_step a L)) as L = L @ U) \<and>
      set (fold (\<lambda>a L. snd (value_reference_step a L)) as L) = set L \<union> set as"
  proof (induction as arbitrary: L)
    case (Cons a as)
    obtain U1 where u1: "snd (value_reference_step a L) = L @ U1"
      using value_reference_add_extends(1)[of a L] by (auto simp: value_reference_step_table)
    have s1: "set (snd (value_reference_step a L)) = insert a (set L)"
      by (simp add: value_reference_step_table value_reference_add_extends(2))
    show ?case using Cons.IH[of "snd (value_reference_step a L)"] u1 s1 by auto
  qed simp
  then show "\<exists>U. deferred_number_names as L = L @ U" "set (deferred_number_names as L) = set L \<union> set as"
    by (simp_all add: deferred_number_names_def)
qed

subsection \<open>A search renumbered keeps its store and its formation\<close>

text \<open>
  A renumbering extends the positions' and the names' tables: every numbered variable keeps its key, so the store read
  through the tree is the same store and every clause keeps holding.
\<close>

definition deferred_renumbered :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> bool" where
  "deferred_renumbered d d' \<longleftrightarrow>
    d' = d\<lparr>deferred_positions := deferred_positions d', deferred_names := deferred_names d'\<rparr> \<and>
    (\<forall>T. keyed_reference_state id (deferred_positions d) T \<longrightarrow>
      (\<exists>U. keyed_reference_state id (deferred_positions d') (T @ U))) \<and>
    (\<exists>U. deferred_names d' = deferred_names d @ U)"

lemma deferred_renumbered_key:
  assumes re: "deferred_renumbered d d'" and N: "positions_numbered (deferred_positions d)" and x: "deferred_numbered d x"
  shows "deferred_key d' x = deferred_key d x" and "deferred_numbered d' x"
proof -
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  obtain U where U: "keyed_reference_state id (deferred_positions d') (T @ U)" using re T by (auto simp: deferred_renumbered_def)
  obtain V where V: "deferred_names d' = deferred_names d @ V" using re by (auto simp: deferred_renumbered_def)
  have p: "fst (fst x) \<in> set T" using x position_number_nonzero[OF T] by (simp add: deferred_numbered_def)
  have a: "snd x \<in> set (deferred_names d)"
    using x name_number_nonzero[of "deferred_names d" "snd x"] unfolding deferred_numbered_def by blast
  have pe: "position_number (deferred_positions d') (fst (fst x)) = position_number (deferred_positions d) (fst (fst x))"
    by (rule position_number_extends[OF T U p])
  have ae: "name_number (deferred_names d') (snd x) = name_number (deferred_names d) (snd x)"
    using name_number_extends[OF a] V by simp
  show "deferred_key d' x = deferred_key d x" using pe ae by (simp add: deferred_key_def)
  show "deferred_numbered d' x" using pe ae x by (simp add: deferred_numbered_def)
qed

lemma deferred_renumbered_positions:
  assumes re: "deferred_renumbered d d'" and N: "positions_numbered (deferred_positions d)"
  shows "positions_numbered (deferred_positions d')"
  using re N by (auto simp: deferred_renumbered_def positions_numbered_def)

lemma deferred_renumbered_fields:
  assumes re: "deferred_renumbered d d'"
  shows "deferred_inner d' = deferred_inner d" "deferred_tree d' = deferred_tree d"
    "deferred_records d' = deferred_records d" "deferred_holders d' = deferred_holders d"
proof -
  have e: "d' = d\<lparr>deferred_positions := deferred_positions d', deferred_names := deferred_names d'\<rparr>"
    using re by (simp add: deferred_renumbered_def)
  show "deferred_inner d' = deferred_inner d" by (subst e) simp
  show "deferred_tree d' = deferred_tree d" by (subst e) simp
  show "deferred_records d' = deferred_records d" by (subst e) simp
  show "deferred_holders d' = deferred_holders d" by (subst e) simp
qed

lemma deferred_key_zero:
  assumes "\<not> deferred_numbered d x" and "deferred_numbered d y"
  shows "deferred_key d x \<noteq> deferred_key d y"
  using assms by (auto simp: deferred_key_def deferred_numbered_def)

lemma deferred_renumbered_store:
  assumes re: "deferred_renumbered d d'" and parts: "deferred_parts_formed \<kappa> P d"
  shows "deferred_store d' = deferred_store d"
proof -
  have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
  have N': "positions_numbered (deferred_positions d')" by (rule deferred_renumbered_positions[OF re N])
  have tk: "\<And>k v. RBT.lookup (snd (deferred_tree d)) k = Some v \<Longrightarrow> \<exists>y. deferred_numbered d y \<and> deferred_key d y = k"
    using parts unfolding deferred_parts_formed_def by blast
  have tree: "deferred_tree d' = deferred_tree d" using deferred_renumbered_fields(2)[OF re] .
  have "RBT.lookup (snd (deferred_tree d)) (deferred_key d' x) = RBT.lookup (snd (deferred_tree d)) (deferred_key d x)" for x
  proof (cases "deferred_numbered d x")
    case True
    then show ?thesis using deferred_renumbered_key(1)[OF re N] by simp
  next
    case False
    have old: "RBT.lookup (snd (deferred_tree d)) (deferred_key d x) = None"
    proof (rule ccontr)
      assume "RBT.lookup (snd (deferred_tree d)) (deferred_key d x) \<noteq> None"
      then obtain y where "deferred_numbered d y" "deferred_key d y = deferred_key d x" using tk by blast
      then show False using deferred_key_zero[OF False] by metis
    qed
    have new: "RBT.lookup (snd (deferred_tree d)) (deferred_key d' x) = None"
    proof (rule ccontr)
      assume "RBT.lookup (snd (deferred_tree d)) (deferred_key d' x) \<noteq> None"
      then obtain y where y: "deferred_numbered d y" and k: "deferred_key d y = deferred_key d' x" using tk by blast
      have y': "deferred_numbered d' y" and ky: "deferred_key d' y = deferred_key d y"
        using deferred_renumbered_key[OF re N y] by simp_all
      show False
      proof (cases "deferred_numbered d' x")
        case True
        then have "x = y" using deferred_key_inj[OF N' True y'] k ky by simp
        then show False using False y by simp
      next
        case False
        then show False using deferred_key_zero[OF False y'] k ky by simp
      qed
    qed
    show ?thesis using old new by simp
  qed
  then show ?thesis by (simp add: deferred_store_def binding_tree_store_def tree fun_eq_iff)
qed

lemma deferred_renumbered_parts:
  assumes re: "deferred_renumbered d d'" and parts: "deferred_parts_formed \<kappa> P d"
  shows "deferred_parts_formed \<kappa> P d'"
proof -
  have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  obtain U where U: "keyed_reference_state id (deferred_positions d') (T @ U)" using re T by (auto simp: deferred_renumbered_def)
  note st = deferred_renumbered_store[OF re parts] and f = deferred_renumbered_fields[OF re]
  have tk0: "\<And>k v. RBT.lookup (snd (deferred_tree d)) k = Some v \<Longrightarrow> \<exists>y. deferred_numbered d y \<and> deferred_key d y = k"
    using parts unfolding deferred_parts_formed_def by blast
  have tk: "\<exists>y. deferred_numbered d' y \<and> deferred_key d' y = k" if lk: "RBT.lookup (snd (deferred_tree d')) k = Some v" for k v
  proof -
    obtain y where "deferred_numbered d y" "deferred_key d y = k" using tk0[of k v] lk f(2) by metis
    then show ?thesis using deferred_renumbered_key[OF re N] by metis
  qed
  have rc: "n \<noteq> 0 \<and> n = position_number (deferred_positions d') q \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner d'))) q \<noteq> None"
    if "RBT.lookup (deferred_records d') n = Some (q, K)" for n q K
  proof -
    have rc0: "\<And>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions d) q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
      using parts unfolding deferred_parts_formed_def by blast
    have o: "n \<noteq> 0 \<and> n = position_number (deferred_positions d) q \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
      using rc0[of n q K] that f(3) by metis
    have "q \<in> set T" using o position_number_nonzero[OF T] by metis
    then show ?thesis using o position_number_extends[OF T U] f by simp
  qed
  show ?thesis using parts st f tk rc deferred_renumbered_positions[OF re N]
    unfolding deferred_parts_formed_def by simp
qed

lemma deferred_renumbered_node:
  assumes re: "deferred_renumbered d d'" and parts: "deferred_parts_formed \<kappa> P d" and nf: "deferred_node_formed d q"
  shows "deferred_node_formed d' q"
proof -
  have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  obtain U where U: "keyed_reference_state id (deferred_positions d') (T @ U)" using re T by (auto simp: deferred_renumbered_def)
  note st = deferred_renumbered_store[OF re parts] and f = deferred_renumbered_fields[OF re]
  show ?thesis unfolding deferred_node_formed_def
  proof (intro allI impI)
    fix hn assume at': "RBT.lookup (shared_nodes (search_state (deferred_inner d'))) q = Some hn"
    have at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn" using at' f by simp
    let ?V = "shared_pattern_variables (deferred_call d hn)"
    have c: "deferred_call d' hn = deferred_call d hn" using st by simp
    have q0: "position_number (deferred_positions d) q \<noteq> 0" by (rule deferred_node_formedD(1)[OF nf at])
    have qe: "position_number (deferred_positions d') q = position_number (deferred_positions d) q"
      using position_number_extends[OF T U] q0 position_number_nonzero[OF T] by metis
    obtain K where K: "RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K)"
      and keys: "set (RBT.keys K) = deferred_key d ` fset ?V" using deferred_node_formedD(2)[OF nf at] by blast
    have num: "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_numbered d x" by (rule deferred_node_formedD(3)[OF nf at])
    have ke: "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_key d' x = deferred_key d x" using deferred_renumbered_key(1)[OF re N num] .
    have "deferred_key d' ` fset ?V = deferred_key d ` fset ?V" using ke by (auto simp: image_iff)
    then have keys': "set (RBT.keys K) = deferred_key d' ` fset ?V" using keys by simp
    have num': "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_numbered d' x" using deferred_renumbered_key(2)[OF re N num] .
    have hold: "\<And>x. x |\<in>| ?V \<Longrightarrow>
        position_number (deferred_positions d') q |\<in>| tree_bucket (deferred_holders d') (deferred_key d' x)"
      using deferred_node_formedD(4)[OF nf at] ke qe f by simp
    have gr: "?V = {||} \<Longrightarrow> shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||}"
      by (rule deferred_node_formedD(5)[OF nf at])
    show "position_number (deferred_positions d') q \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records d') (position_number (deferred_positions d') q) = Some (q, K) \<and>
        set (RBT.keys K) = deferred_key d' ` fset (shared_pattern_variables (deferred_call d' hn))) \<and>
      fBall (shared_pattern_variables (deferred_call d' hn)) (deferred_numbered d') \<and>
      fBall (shared_pattern_variables (deferred_call d' hn))
        (\<lambda>x. position_number (deferred_positions d') q |\<in>| tree_bucket (deferred_holders d') (deferred_key d' x)) \<and>
      (shared_pattern_variables (deferred_call d' hn) = {||} \<longrightarrow>
        shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||})"
      using q0 qe K keys' num' hold gr c f by auto
  qed
qed

subsection \<open>Recording a node\<close>

text \<open>
  A node is recorded at its position's number: the position and the names of its call's variables numbered, its record
  the keyed set of its call's variables, and its number added to the holders of each. Recording a node whose call holds
  no variable the store binds establishes its clauses and keeps every other node's.
\<close>

definition deferred_renumber :: "'s::linorder list \<Rightarrow> ('s,'a) resolution_variable shared_pattern \<Rightarrow>
    ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_renumber q p d = d\<lparr>deferred_positions := snd (keyed_reference_step id q (deferred_positions d)),
    deferred_names := deferred_number_names (map snd (shared_variable_list p)) (deferred_names d)\<rparr>"

lemma deferred_renumber_fields [simp]:
  "deferred_inner (deferred_renumber q p d) = deferred_inner d" "deferred_tree (deferred_renumber q p d) = deferred_tree d"
  "deferred_records (deferred_renumber q p d) = deferred_records d"
  "deferred_holders (deferred_renumber q p d) = deferred_holders d"
  "deferred_positions (deferred_renumber q p d) = snd (keyed_reference_step id q (deferred_positions d))"
  "deferred_names (deferred_renumber q p d) = deferred_number_names (map snd (shared_variable_list p)) (deferred_names d)"
  by (simp_all add: deferred_renumber_def)

definition deferred_record_at :: "nat \<Rightarrow> 's::linorder list \<Rightarrow> deferred_key list \<Rightarrow>
    ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_record_at n q ks d = d\<lparr>deferred_records := RBT.insert n (q, fold (\<lambda>k t. RBT.insert k () t) ks RBT.empty)
      (deferred_records d), deferred_holders := tree_add n (fset_of_list ks) (deferred_holders d)\<rparr>"

lemma deferred_record_at_fields [simp]:
  "deferred_inner (deferred_record_at n q ks d) = deferred_inner d"
  "deferred_tree (deferred_record_at n q ks d) = deferred_tree d"
  "deferred_positions (deferred_record_at n q ks d) = deferred_positions d"
  "deferred_names (deferred_record_at n q ks d) = deferred_names d"
  "deferred_records (deferred_record_at n q ks d) =
    RBT.insert n (q, fold (\<lambda>k t. RBT.insert k () t) ks RBT.empty) (deferred_records d)"
  "deferred_holders (deferred_record_at n q ks d) = tree_add n (fset_of_list ks) (deferred_holders d)"
  by (simp_all add: deferred_record_at_def)

definition deferred_record_node :: "'s::linorder list \<Rightarrow> ('s,'a) resolution_variable shared_pattern \<Rightarrow>
    ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_record_node q p d = (let d1 = deferred_renumber q p d in
    deferred_record_at (position_number (deferred_positions d1) q) q (map (deferred_key d1) (shared_variable_list p)) d1)"

lemma fold_insert_unit_keys: "set (RBT.keys (fold (\<lambda>k t. RBT.insert k () t) ks t)) = set ks \<union> set (RBT.keys t)"
proof -
  have "dom (RBT.lookup (fold (\<lambda>k t. RBT.insert k () t) ks t)) = set ks \<union> dom (RBT.lookup t)"
    by (induction ks arbitrary: t) auto
  then show ?thesis by (simp add: RBT.lookup_keys)
qed

lemma deferred_record_node:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
    and p: "p = shared_derivation_call (shared_entry_node hn)"
    and unbound: "\<forall>x. x |\<in>| shared_pattern_variables p \<longrightarrow> binding_map (deferred_store d) x = None"
    and placed: "\<forall>x. x |\<in>| shared_pattern_variables p \<longrightarrow>
      fst (fst x) = q \<or> position_number (deferred_positions d) (fst (fst x)) \<noteq> 0"
  shows "deferred_parts_formed \<kappa> P (deferred_record_node q p d)"
    and "deferred_node_formed (deferred_record_node q p d) q"
    and "\<And>q'. deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_record_node q p d) q'"
    and "deferred_inner (deferred_record_node q p d) = deferred_inner d"
    and "deferred_store (deferred_record_node q p d) = deferred_store d"
    and "\<And>q'. position_number (deferred_positions d) q' \<noteq> 0 \<Longrightarrow>
      position_number (deferred_positions (deferred_record_node q p d)) q' \<noteq> 0"
    and "position_number (deferred_positions (deferred_record_node q p d)) q \<noteq> 0"
proof -
  let ?d1 = "deferred_renumber q p d"
  let ?n = "position_number (deferred_positions ?d1) q" and ?ks = "map (deferred_key ?d1) (shared_variable_list p)"
  let ?K = "fold (\<lambda>k t. RBT.insert k () t) ?ks RBT.empty"
  have e: "deferred_record_node q p d = deferred_record_at ?n q ?ks ?d1"
    by (simp add: deferred_record_node_def Let_def)
  have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  have T1: "keyed_reference_state id (deferred_positions ?d1) (snd (value_reference_step q T))"
    using keyed_reference_step_table[OF T] by simp
  obtain U where U: "snd (value_reference_step q T) = T @ U"
    using value_reference_add_extends(1)[of q T] by (auto simp: value_reference_step_table)
  have re: "deferred_renumbered d ?d1"
  proof -
    have "\<forall>T'. keyed_reference_state id (deferred_positions d) T' \<longrightarrow>
        (\<exists>U. keyed_reference_state id (deferred_positions ?d1) (T' @ U))"
    proof (intro allI impI)
      fix T' assume "keyed_reference_state id (deferred_positions d) T'"
      then have "T' = T" using T by (cases "deferred_positions d") (simp add: keyed_reference_state_def)
      then show "\<exists>U. keyed_reference_state id (deferred_positions ?d1) (T' @ U)" using T1 U by auto
    qed
    then show ?thesis using deferred_number_names(1) by (simp add: deferred_renumbered_def deferred_renumber_def)
  qed
  have parts1: "deferred_parts_formed \<kappa> P ?d1" by (rule deferred_renumbered_parts[OF re parts])
  have st1: "deferred_store ?d1 = deferred_store d" by (rule deferred_renumbered_store[OF re parts])
  have N1: "positions_numbered (deferred_positions ?d1)" using T1 by (auto simp: positions_numbered_def)
  have qT1: "q \<in> set (snd (value_reference_step q T))" by (simp add: value_reference_step_table value_reference_add_extends(2))
  have n0: "?n \<noteq> 0" using position_number_nonzero[OF T1] qT1 by simp
  have pf: "shared_pattern_formed (search_table (deferred_inner d)) p"
    using shared_entries_formed(2)[OF search_formedD(1)[OF conjunct1[OF parts[unfolded deferred_parts_formed_def]]] at] p
    by (simp add: node_entry_formed_def shared_derivation_formed_def)
  have vl: "set (shared_variable_list p) = fset (shared_pattern_variables p)" by (rule shared_variable_list[OF pf])
  have num1: "deferred_numbered ?d1 x" if "x |\<in>| shared_pattern_variables p" for x
  proof -
    have "fst (fst x) \<in> set (snd (value_reference_step q T))"
      using placed[rule_format, OF that] position_number_nonzero[OF T] U qT1 by auto
    then have a: "position_number (deferred_positions ?d1) (fst (fst x)) \<noteq> 0" using position_number_nonzero[OF T1] by simp
    have "snd x \<in> set (deferred_names ?d1)" using that vl deferred_number_names(2) by force
    then show ?thesis using a name_number_nonzero[of "deferred_names ?d1" "snd x"] unfolding deferred_numbered_def by blast
  qed
  have keyE: "deferred_key (deferred_record_node q p d) = deferred_key ?d1" by (simp add: e fun_eq_iff deferred_key_def)
  have stE: "deferred_store (deferred_record_node q p d) = deferred_store d"
    unfolding deferred_store_def keyE using st1 by (simp add: e deferred_store_def)
  have numE: "deferred_numbered (deferred_record_node q p d) = deferred_numbered ?d1"
    by (simp add: e fun_eq_iff deferred_numbered_def)
  have posE: "deferred_positions (deferred_record_node q p d) = deferred_positions ?d1" by (simp add: e)
  have innE: "deferred_inner (deferred_record_node q p d) = deferred_inner d" by (simp add: e)
  show "deferred_inner (deferred_record_node q p d) = deferred_inner d" by (rule innE)
  show "deferred_store (deferred_record_node q p d) = deferred_store d" by (rule stE)
  show "position_number (deferred_positions (deferred_record_node q p d)) q \<noteq> 0" using n0 posE by simp
  show "\<And>q'. position_number (deferred_positions d) q' \<noteq> 0 \<Longrightarrow>
      position_number (deferred_positions (deferred_record_node q p d)) q' \<noteq> 0"
    using position_number_nonzero[OF T] position_number_nonzero[OF T1] U posE by auto
  show "deferred_parts_formed \<kappa> P (deferred_record_node q p d)"
  proof -
    have rc: "n' \<noteq> 0 \<and> n' = position_number (deferred_positions ?d1) q' \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q' \<noteq> None"
      if "RBT.lookup (RBT.insert ?n (q, ?K) (deferred_records ?d1)) n' = Some (q', K')" for n' q' K'
    proof (cases "n' = ?n")
      case True
      then show ?thesis using that n0 at by auto
    next
      case False
      have a: "RBT.lookup (deferred_records ?d1) n' = Some (q', K')" using False that by simp
      have b: "\<And>n q K. RBT.lookup (deferred_records ?d1) n = Some (q, K) \<Longrightarrow> n \<noteq> 0 \<and>
          n = position_number (deferred_positions ?d1) q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q \<noteq> None"
        using parts1 unfolding deferred_parts_formed_def by blast
      have i1: "deferred_inner ?d1 = deferred_inner d" by simp
      show ?thesis using b[OF a] .
    qed
    have eqs0: "deferred_store (deferred_record_node q p d) = deferred_store ?d1" by (simp only: stE st1)
    have eqs: "deferred_inner (deferred_record_node q p d) = deferred_inner ?d1"
      "deferred_positions (deferred_record_node q p d) = deferred_positions ?d1"
      "deferred_tree (deferred_record_node q p d) = deferred_tree ?d1"
      "deferred_records (deferred_record_node q p d) = RBT.insert ?n (q, ?K) (deferred_records ?d1)"
      by (simp_all only: e deferred_record_at_fields deferred_renumber_fields)
    show ?thesis unfolding deferred_parts_formed_def eqs eqs0 keyE numE
      using parts1[unfolded deferred_parts_formed_def] rc by blast
  qed
  have V: "shared_pattern_variables (deferred_call (deferred_record_node q p d) hn) = shared_pattern_variables p"
  proof -
    have "binding_resolve (deferred_store d) p = p" by (rule binding_resolve_unbound) (use unbound in blast)
    then show ?thesis using stE p by simp
  qed
  show "deferred_node_formed (deferred_record_node q p d) q"
    unfolding deferred_node_formed_def
  proof (intro allI impI)
    fix hn' assume "RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_node q p d)))) q = Some hn'"
    then have hn': "hn' = hn" using at innE by simp
    have K: "set (RBT.keys ?K) = deferred_key (deferred_record_node q p d) ` fset (shared_pattern_variables p)"
      using fold_insert_unit_keys[of ?ks RBT.empty] vl keyE by simp
    have recs: "RBT.lookup (deferred_records (deferred_record_node q p d)) ?n = Some (q, ?K)"
      by (simp only: e deferred_record_at_fields RBT.lookup_insert fun_upd_same)
    have hold: "?n |\<in>| tree_bucket (deferred_holders (deferred_record_node q p d)) (deferred_key ?d1 x)"
      if "x |\<in>| shared_pattern_variables p" for x
    proof -
      have "deferred_key ?d1 x \<in> set ?ks" using that vl by simp
      then show ?thesis by (simp add: e fset_of_list_elem fset_of_list.rep_eq)
    qed
    show "position_number (deferred_positions (deferred_record_node q p d)) q \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records (deferred_record_node q p d))
          (position_number (deferred_positions (deferred_record_node q p d)) q) = Some (q, K) \<and>
        set (RBT.keys K) = deferred_key (deferred_record_node q p d) `
          fset (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))) \<and>
      fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
        (deferred_numbered (deferred_record_node q p d)) \<and>
      fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
        (\<lambda>x. position_number (deferred_positions (deferred_record_node q p d)) q |\<in>|
          tree_bucket (deferred_holders (deferred_record_node q p d)) (deferred_key (deferred_record_node q p d) x)) \<and>
      (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn') = {||} \<longrightarrow>
        shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||})"
    proof (intro conjI)
      show "position_number (deferred_positions (deferred_record_node q p d)) q \<noteq> 0" unfolding posE by (rule n0)
      show "\<exists>K. RBT.lookup (deferred_records (deferred_record_node q p d))
          (position_number (deferred_positions (deferred_record_node q p d)) q) = Some (q, K) \<and>
        set (RBT.keys K) = deferred_key (deferred_record_node q p d) `
          fset (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))"
        unfolding posE hn' V using recs K by blast
      show "fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
        (deferred_numbered (deferred_record_node q p d))"
        unfolding hn' V numE using num1 by blast
      show "fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
        (\<lambda>x. position_number (deferred_positions (deferred_record_node q p d)) q |\<in>|
          tree_bucket (deferred_holders (deferred_record_node q p d)) (deferred_key (deferred_record_node q p d) x))"
        unfolding hn' V posE keyE using hold by blast
      show "shared_pattern_variables (deferred_call (deferred_record_node q p d) hn') = {||} \<longrightarrow>
        shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
        unfolding hn' V using p by simp
    qed
  qed
  show "deferred_node_formed (deferred_record_node q p d) q'" if nf: "deferred_node_formed d q'" for q'
  proof (cases "q' = q")
    case True
    then show ?thesis using \<open>deferred_node_formed (deferred_record_node q p d) q\<close> by simp
  next
    case False
    have nf1: "deferred_node_formed ?d1 q'" by (rule deferred_renumbered_node[OF re parts nf])
    show ?thesis unfolding deferred_node_formed_def
    proof (intro allI impI)
      fix hn' assume a': "RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_node q p d)))) q' = Some hn'"
      have a1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q' = Some hn'" using a' innE by simp
      have q'0: "position_number (deferred_positions ?d1) q' \<noteq> 0" by (rule deferred_node_formedD(1)[OF nf1 a1])
      have ne: "position_number (deferred_positions ?d1) q' \<noteq> ?n"
      proof
        assume "position_number (deferred_positions ?d1) q' = ?n"
        then have "q' = q" using position_number_inj[OF T1 _ q'0] by blast
        then show False using False by simp
      qed
      have c: "deferred_call (deferred_record_node q p d) hn' = deferred_call ?d1 hn'" using stE st1 by simp
      have recs': "RBT.lookup (deferred_records (deferred_record_node q p d)) (position_number (deferred_positions ?d1) q') =
          RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q')"
        by (simp only: e deferred_record_at_fields RBT.lookup_insert fun_upd_other[OF ne])
      have hold': "tree_bucket (deferred_holders ?d1) k |\<subseteq>| tree_bucket (deferred_holders (deferred_record_node q p d)) k" for k
        by (auto simp: e)
      show "position_number (deferred_positions (deferred_record_node q p d)) q' \<noteq> 0 \<and>
        (\<exists>K. RBT.lookup (deferred_records (deferred_record_node q p d))
            (position_number (deferred_positions (deferred_record_node q p d)) q') = Some (q', K) \<and>
          set (RBT.keys K) = deferred_key (deferred_record_node q p d) `
            fset (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))) \<and>
        fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
          (deferred_numbered (deferred_record_node q p d)) \<and>
        fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
          (\<lambda>x. position_number (deferred_positions (deferred_record_node q p d)) q' |\<in>|
            tree_bucket (deferred_holders (deferred_record_node q p d)) (deferred_key (deferred_record_node q p d) x)) \<and>
        (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn') = {||} \<longrightarrow>
          shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||})"
      proof (intro conjI)
        show "position_number (deferred_positions (deferred_record_node q p d)) q' \<noteq> 0" unfolding posE by (rule q'0)
        show "\<exists>K. RBT.lookup (deferred_records (deferred_record_node q p d))
            (position_number (deferred_positions (deferred_record_node q p d)) q') = Some (q', K) \<and>
          set (RBT.keys K) = deferred_key (deferred_record_node q p d) `
            fset (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))"
          unfolding posE recs' c keyE using deferred_node_formedD(2)[OF nf1 a1] .
        show "fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
          (deferred_numbered (deferred_record_node q p d))"
          unfolding c numE using deferred_node_formedD(3)[OF nf1 a1] by blast
        show "fBall (shared_pattern_variables (deferred_call (deferred_record_node q p d) hn'))
          (\<lambda>x. position_number (deferred_positions (deferred_record_node q p d)) q' |\<in>|
            tree_bucket (deferred_holders (deferred_record_node q p d)) (deferred_key (deferred_record_node q p d) x))"
          unfolding c posE keyE
          by (intro fBallI) (rule fsubsetD[OF hold'], rule deferred_node_formedD(4)[OF nf1 a1], assumption)
        show "shared_pattern_variables (deferred_call (deferred_record_node q p d) hn') = {||} \<longrightarrow>
          shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
          unfolding c using deferred_node_formedD(5)[OF nf1 a1] by blast
      qed
    qed
  qed
qed

subsection \<open>The deferred search of an R3 state\<close>

text \<open>
  The deferred search starts from the shared search of an R3 state, its store empty: every node position numbered first,
  then every node recorded. It needs every variable of a goal and of a node's call to stand at a node's position, as
  R3's own renaming apart places them (an initial state is ground).
\<close>

definition search_variables_placed :: "('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "search_variables_placed st \<longleftrightarrow>
    fBall (resolution_pending st) (\<lambda>g. fBall (resolution_goal_variables g)
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st))) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. fBall (finite_pattern_variables (resolution_node_call nd))
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)))"

definition deferred_of :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_of P st = (let r = search_of P st; es = RBT.entries (shared_nodes (search_state r)) in
    fold (\<lambda>z d. deferred_record_node (fst z) (shared_derivation_call (shared_entry_node (snd z))) d) es
      \<lparr>deferred_inner = r, deferred_tree = binding_tree_empty,
       deferred_positions = snd (keyed_reference_sequence id (map fst es) (RBT.empty, 0, [])),
       deferred_names = [], deferred_records = RBT.empty, deferred_holders = RBT.empty\<rparr>)"

lemma binding_tree_store_empty: "binding_tree_store key binding_tree_empty = binding_store_empty"
  by (simp add: binding_tree_store_def binding_tree_empty_def binding_store_empty_def)

theorem deferred_of:
  fixes st :: "('a,'s::linorder,'d,'c) resolution_state"
  assumes d: "resolution_positions_distinct st" and v: "search_variables_placed st"
  shows "deferred_formed \<kappa> P (deferred_of P st)" and "deferred_project (deferred_of P st) = st"
    and "deferred_inner (deferred_of P st) = search_of P st"
proof -
  let ?r = "search_of P st" let ?s = "search_state ?r" let ?es = "RBT.entries (shared_nodes ?s)"
  let ?N0 = "snd (keyed_reference_sequence id (map fst ?es) (RBT.empty, 0, []))"
  let ?T0 = "snd (value_reference_sequence (map fst ?es) [])"
  let ?d0 = "\<lparr>deferred_inner = ?r, deferred_tree = binding_tree_empty, deferred_positions = ?N0,
    deferred_names = [], deferred_records = RBT.empty, deferred_holders = RBT.empty\<rparr>
    :: ('a,'s,'d,'c) deferred_search"
  have r: "search_formed \<kappa> P ?r" and pr: "search_project ?r = st" using search_of[OF d] by simp_all
  have K: "search_classes_formed ?r" using search_of_classes[OF d] .
  have T0: "keyed_reference_state id ?N0 ?T0"
    using keyed_reference_sequence_exact[OF inj_on_id keyed_reference_state_empty, of "map fst ?es"] by simp
  have nodepos: "q \<in> set ?T0" if "RBT.lookup (shared_nodes ?s) q \<noteq> None" for q
  proof -
    have "q \<in> set (map fst ?es)"
      using that RBT.map_of_entries[of "shared_nodes ?s"] map_of_eq_None_iff[of ?es q] by (metis list.set_map)
    then show ?thesis by (simp add: value_reference_sequence_table value_reference_add_fold)
  qed
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have placed_at: "RBT.lookup (shared_nodes ?s) (fst (fst x)) \<noteq> None"
    if px: "fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)" for x :: "('s,'a) resolution_variable"
  proof -
    obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = fst (fst x)"
      using px by (auto elim!: fimageE)
    have "nd |\<in>| resolution_nodes (search_project ?r)" using nd(1) pr by simp
    then obtain q hn where qh: "RBT.lookup (shared_nodes ?s) q = Some hn"
      and ndq: "shared_derivation_project (search_table ?r) (shared_entry_node hn) = nd"
      unfolding shared_state_project_member(2) by blast
    have "shared_derivation_position (shared_entry_node hn) = q"
      using shared_entries_formed(2)[OF s qh] by (simp add: node_entry_formed_def)
    then have "q = fst (fst x)" using ndq nd(2) by (auto simp: shared_derivation_project_def)
    then show ?thesis using qh by simp
  qed
  have st0: "deferred_store ?d0 = binding_store_empty" by (simp add: deferred_store_def binding_tree_store_empty)
  have goalv: "RBT.lookup (shared_nodes ?s) (fst (fst x)) \<noteq> None"
    if "RBT.lookup (shared_goals ?s) q = Some h" "x |\<in>| shared_goal_variables (shared_entry_goal h)" for q h x
  proof -
    have gf: "goal_entry_formed P (search_table ?r) q h" using shared_entries_formed(1)[OF s that(1)] .
    have "shared_goal_project (search_table ?r) (shared_entry_goal h) |\<in>| resolution_pending (search_project ?r)"
      unfolding shared_state_project_member(1) using that(1) by blast
    then have "shared_goal_project (search_table ?r) (shared_entry_goal h) |\<in>| resolution_pending st" using pr by simp
    moreover have "x |\<in>| resolution_goal_variables (shared_goal_project (search_table ?r) (shared_entry_goal h))"
      using that(2) goal_entry_variables[OF gf] by simp
    ultimately show ?thesis using v placed_at unfolding search_variables_placed_def by blast
  qed
  have parts0: "deferred_parts_formed \<kappa> P ?d0"
    unfolding deferred_parts_formed_def using r K T0 st0 goalv binding_store_empty_formed
    by (auto simp: positions_numbered_def binding_tree_empty_def binding_store_empty_def)
  define step where "step = (\<lambda>(z :: 's list \<times> ('a,'s,'d,'c) shared_node_entry) d. deferred_record_node (fst z) (shared_derivation_call (shared_entry_node (snd z))) d
    :: ('a,'s,'d,'c) deferred_search)"
  have fold: "deferred_parts_formed \<kappa> P (fold step zs d) \<and> deferred_inner (fold step zs d) = ?r \<and>
      deferred_store (fold step zs d) = binding_store_empty \<and>
      (\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions (fold step zs d)) q \<noteq> 0) \<and>
      (\<forall>q. q \<in> Q \<union> fst ` set zs \<longrightarrow> deferred_node_formed (fold step zs d) q)"
    if "deferred_parts_formed \<kappa> P d" "deferred_inner d = ?r" "deferred_store d = binding_store_empty"
      "\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions d) q \<noteq> 0"
      "\<forall>q\<in>Q. deferred_node_formed d q" "set zs \<subseteq> set ?es" for zs d Q
    using that
  proof (induction zs arbitrary: d Q)
    case Nil
    then show ?case by simp
  next
    case (Cons z zs)
    obtain q hn where z: "z = (q, hn)" by (cases z)
    have at: "RBT.lookup (shared_nodes ?s) q = Some hn" using Cons.prems(6) z by (simp add: RBT.lookup_in_tree)
    have at': "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn" using at Cons.prems(2) by simp
    let ?c = "shared_derivation_call (shared_entry_node hn)"
    have nf0: "node_entry_formed (search_table ?r) q hn" using shared_entries_formed(2)[OF s at] .
    have cvars: "fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)" if "x |\<in>| shared_pattern_variables ?c" for x
    proof -
      have "shared_derivation_project (search_table ?r) (shared_entry_node hn) |\<in>| resolution_nodes (search_project ?r)"
        unfolding shared_state_project_member(2) using at by blast
      then have m: "shared_derivation_project (search_table ?r) (shared_entry_node hn) |\<in>| resolution_nodes st"
        using pr by simp
      have "x |\<in>| finite_pattern_variables (resolution_node_call (shared_derivation_project (search_table ?r) (shared_entry_node hn)))"
        using that shared_pattern_variables_project[of "search_table ?r" ?c] nf0
        by (simp add: node_entry_formed_def shared_derivation_formed_def)
      then show ?thesis using v m unfolding search_variables_placed_def by blast
    qed
    have unb: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow> binding_map (deferred_store d) x = None"
      using Cons.prems(3) by (simp add: binding_store_empty_def)
    have plc: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow>
        fst (fst x) = q \<or> position_number (deferred_positions d) (fst (fst x)) \<noteq> 0"
      using cvars placed_at Cons.prems(4) by blast
    have unbA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow> binding_map (deferred_store d) x = None" using unb by blast
    have plcA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow>
        fst (fst x) = q \<or> position_number (deferred_positions d) (fst (fst x)) \<noteq> 0" using plc by blast
    note R = deferred_record_node[OF Cons.prems(1) at' refl unbA plcA]
    let ?d' = "deferred_record_node q ?c d"
    have IH: "deferred_parts_formed \<kappa> P (fold step zs ?d') \<and> deferred_inner (fold step zs ?d') = ?r \<and>
        deferred_store (fold step zs ?d') = binding_store_empty \<and>
        (\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions (fold step zs ?d')) q \<noteq> 0) \<and>
        (\<forall>q'. q' \<in> insert q Q \<union> fst ` set zs \<longrightarrow> deferred_node_formed (fold step zs ?d') q')"
    proof (rule Cons.IH)
      show "deferred_parts_formed \<kappa> P ?d'" by (rule R(1))
      show "deferred_inner ?d' = ?r" using R(4) Cons.prems(2) by simp
      show "deferred_store ?d' = binding_store_empty" using R(5) Cons.prems(3) by simp
      show "\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions ?d') q \<noteq> 0"
        using R(6) Cons.prems(4) by blast
      show "\<forall>q'\<in>insert q Q. deferred_node_formed ?d' q'" using R(2,3) Cons.prems(5) by blast
      show "set zs \<subseteq> set ?es" using Cons.prems(6) by simp
    qed
    show ?case using IH by (simp add: z step_def)
  qed
  have dof: "deferred_of P st = fold step ?es ?d0" by (simp add: deferred_of_def step_def Let_def)
  have npos0: "\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions ?d0) q \<noteq> 0"
  proof (intro allI impI)
    fix q assume "RBT.lookup (shared_nodes ?s) q \<noteq> None"
    then have "q \<in> set ?T0" by (rule nodepos)
    then show "position_number (deferred_positions ?d0) q \<noteq> 0" using position_number_nonzero[OF T0, of q] by simp
  qed
  have in0: "deferred_inner ?d0 = ?r" by simp
  have nf0: "\<forall>q\<in>{}. deferred_node_formed ?d0 q" by simp
  note F = fold[where Q = "{}", OF parts0 in0 st0 npos0 nf0 order_refl]
  have allq: "deferred_node_formed (deferred_of P st) q" for q
  proof (cases "RBT.lookup (shared_nodes ?s) q")
    case None
    then show ?thesis using F dof by (simp add: deferred_node_formed_def)
  next
    case (Some hn)
    then have "map_of ?es q = Some hn" by (simp add: RBT.map_of_entries)
    then have "(q, hn) \<in> set ?es" by (rule map_of_SomeD)
    then have qm: "q \<in> fst ` set ?es" by (rule rev_image_eqI) simp
    have Fn: "\<forall>q. q \<in> {} \<union> fst ` set ?es \<longrightarrow> deferred_node_formed (fold step ?es ?d0) q" using F by blast
    show ?thesis unfolding dof using Fn qm by blast
  qed
  show "deferred_formed \<kappa> P (deferred_of P st)" using F dof allq by (simp add: deferred_formed_def)
  show inner: "deferred_inner (deferred_of P st) = search_of P st" using F dof by simp
  have sv: "deferred_substitution (deferred_of P st) = Finite_Variable"
    using F dof by (simp add: fun_eq_iff deferred_substitution_def binding_substitution_def binding_resolve_empty)
  have g: "fimage (resolution_goal_substitute Finite_Variable) (resolution_pending st) = resolution_pending st"
    by (rule fimage_fixed) (rule resolution_goal_substitute_outside, simp)
  have n: "fimage (resolution_node_substitute Finite_Variable) (resolution_nodes st) = resolution_nodes st"
    by (rule fimage_fixed) (rule resolution_node_substitute_outside, simp)
  show "deferred_project (deferred_of P st) = st"
    unfolding deferred_project_def sv inner pr resolution_state_substitute_def g n by (cases st) simp
qed

subsection \<open>Substituting the goals alone\<close>

text \<open>
  A step of the deferred search substitutes the goals as the shared search substitutes them and leaves every node as it
  is: the goal at a position is substituted and re-entered (@{thm [source] shared_goal_entry_substitute}), the node there,
  if any, kept, the store holding what the node's call is now.
\<close>

definition shared_goal_substitute_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_goal_substitute_at P \<sigma> D q s = (case RBT.lookup (shared_goals s) q of None \<Rightarrow> s
    | Some h \<Rightarrow> (case shared_goal_entry_substitute P \<sigma> D h (shared_sharing s) of (h', x) \<Rightarrow>
        shared_replace q (Some h') (RBT.lookup (shared_nodes s) q) (shared_reshare x s)))"

lemma shared_goal_substitute_at:
  assumes s: "shared_state_formed \<kappa> P s"
    and \<sigma>f: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_state_formed \<kappa> P (shared_goal_substitute_at P \<sigma> D q s)"
    and "table_extends (shared_state_table s) (shared_state_table (shared_goal_substitute_at P \<sigma> D q s))"
    and "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals (shared_goal_substitute_at P \<sigma> D q s)) p = RBT.lookup (shared_goals s) p"
    and "\<And>p. RBT.lookup (shared_nodes (shared_goal_substitute_at P \<sigma> D q s)) p = RBT.lookup (shared_nodes s) p"
    and "shared_goal_view (shared_goal_substitute_at P \<sigma> D q s) q =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_goal_view s q)"
    and "shared_witnesses (shared_goal_substitute_at P \<sigma> D q s) = shared_witnesses s"
proof -
  let ?s' = "shared_goal_substitute_at P \<sigma> D q s" and ?T0 = "shared_state_table s"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T0 (\<sigma> a)"
  have x0: "share_state_formed (shared_sharing s)" and tf0: "table_formed ?T0" using shared_entries_formed(3,4)[OF s] .
  have all: "shared_state_formed \<kappa> P ?s' \<and> table_extends ?T0 (shared_state_table ?s') \<and>
      (\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_goals ?s') p = RBT.lookup (shared_goals s) p) \<and>
      (\<forall>p. RBT.lookup (shared_nodes ?s') p = RBT.lookup (shared_nodes s) p) \<and>
      shared_goal_view ?s' q = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view s q) \<and>
      shared_witnesses ?s' = shared_witnesses s"
  proof (cases "RBT.lookup (shared_goals s) q")
    case None
    then show ?thesis using s by (simp add: shared_goal_substitute_at_def shared_goal_view_def table_extends_refl)
  next
    case (Some h)
    obtain h' x where e: "shared_goal_entry_substitute P \<sigma> D h (shared_sharing s) = (h', x)"
      by (cases "shared_goal_entry_substitute P \<sigma> D h (shared_sharing s)")
    have hf: "goal_entry_formed P ?T0 q h" using shared_entries_formed(1)[OF s Some] .
    have k: "share_state_formed x \<and> table_extends ?T0 (share_state_table x) \<and> goal_entry_formed P (share_state_table x) q h' \<and>
        shared_goal_project (share_state_table x) (shared_entry_goal h') =
          resolution_goal_substitute ?\<tau> (shared_goal_project ?T0 (shared_entry_goal h))"
      using shared_goal_entry_substitute[where D = D, OF x0 hf \<sigma>f \<sigma>c out[rule_format]] e by simp
    let ?sr = "shared_reshare x s"
    have xf: "share_state_formed x" and ext: "table_extends ?T0 (share_state_table x)" using k by simp_all
    have srf: "shared_state_formed \<kappa> P ?sr" using shared_reshare(1)[OF s xf ext] .
    have tbl: "shared_state_table ?sr = share_state_table x" by (simp add: shared_reshare_def)
    have no: "node_entry_formed (shared_state_table ?sr) q hn" if "RBT.lookup (shared_nodes s) q = Some hn" for hn
      using node_entry_extends[OF tf0 shared_entries_formed(2)[OF s that] ext] tbl by simp
    have eq: "?s' = shared_replace q (Some h') (RBT.lookup (shared_nodes s) q) ?sr"
      by (simp add: shared_goal_substitute_at_def Some e)
    have f': "shared_state_formed \<kappa> P ?s'" unfolding eq
      by (rule shared_replace_formed[OF srf]) (use k tbl no in \<open>simp_all\<close>)
    have tbl': "shared_state_table ?s' = share_state_table x" unfolding eq using tbl by simp
    show ?thesis using f' tbl' ext k Some unfolding eq by (simp add: shared_goal_view_def shared_reshare_def)
  qed
  show "shared_state_formed \<kappa> P ?s'" using all by blast
  show "table_extends ?T0 (shared_state_table ?s')" using all by blast
  show "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals ?s') p = RBT.lookup (shared_goals s) p" using all by blast
  show "\<And>p. RBT.lookup (shared_nodes ?s') p = RBT.lookup (shared_nodes s) p" using all by blast
  show "shared_goal_view ?s' q = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view s q)" using all by blast
  show "shared_witnesses ?s' = shared_witnesses s" using all by blast
qed

definition search_goal_substitute_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_goal_substitute_at P \<sigma> D q r = search_update q (shared_goal_substitute_at P \<sigma> D q (search_state r)) r"

definition search_goal_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_goal_substitute P \<sigma> D r =
    fold (search_goal_substitute_at P \<sigma> D) (sorted_list_of_fset (shared_substitute_positions D (search_state r))) r"

lemma search_goal_substitute_fold:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and tf0: "table_formed T0"
    and ext: "table_extends T0 (search_table r)"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_formed \<kappa> P (fold (search_goal_substitute_at P \<sigma> D) qs r) \<and>
    search_classes_formed (fold (search_goal_substitute_at P \<sigma> D) qs r) \<and>
    table_extends T0 (search_table (fold (search_goal_substitute_at P \<sigma> D) qs r)) \<and>
    (\<forall>p. RBT.lookup (shared_nodes (search_state (fold (search_goal_substitute_at P \<sigma> D) qs r))) p =
      RBT.lookup (shared_nodes (search_state r)) p)"
  using r K ext
proof (induction qs arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  have outA: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" using out by blast
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF Cons.prems(1)] .
  have \<sigma>t: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)" using shared_pattern_extends(1)[OF tf0 \<sigma>f Cons.prems(3)] .
  note k = shared_goal_substitute_at[where D = D and q = q, OF s \<sigma>t \<sigma>c outA]
  let ?r1 = "search_goal_substitute_at P \<sigma> D q r"
  have f1: "search_formed \<kappa> P ?r1" unfolding search_goal_substitute_at_def
    by (rule search_update[OF Cons.prems(1)]) (simp_all add: k(1) k(2) k(3))
  have K1: "search_classes_formed ?r1" unfolding search_goal_substitute_at_def
    by (rule search_update_classes[OF Cons.prems(1) Cons.prems(2) f1[unfolded search_goal_substitute_at_def]])
      (simp_all add: k(2) k(3) k(4))
  have e1: "table_extends T0 (search_table ?r1)"
    using table_extends_trans[OF Cons.prems(3) k(2)] by (simp add: search_goal_substitute_at_def)
  have n1: "\<And>p. RBT.lookup (shared_nodes (search_state ?r1)) p = RBT.lookup (shared_nodes (search_state r)) p"
    using k(4) by (simp add: search_goal_substitute_at_def)
  show ?case using Cons.IH[OF f1 K1 e1] n1 by simp
qed

lemma shared_goal_substitute_at_views:
  assumes s: "shared_state_formed \<kappa> P s"
    and \<sigma>f: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_goal_view (shared_goal_substitute_at P \<sigma> D q s) p = (if p = q then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_goal_view s p)
      else shared_goal_view s p)"
    and "shared_node_view (shared_goal_substitute_at P \<sigma> D q s) p = shared_node_view s p"
proof -
  let ?s' = "shared_goal_substitute_at P \<sigma> D q s" and ?T = "shared_state_table s"
  note k = shared_goal_substitute_at[where D = D and q = q, OF s \<sigma>f \<sigma>c out]
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  show "shared_goal_view ?s' p = (if p = q then map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project ?T (\<sigma> a)))
      (shared_goal_view s p) else shared_goal_view s p)"
  proof (cases "p = q")
    case True
    then show ?thesis using k(5) by simp
  next
    case False
    show ?thesis
    proof (cases "RBT.lookup (shared_goals s) p")
      case (Some h)
      from goal_entry_extends[OF tf shared_entries_formed(1)[OF s Some] k(2)] Some k(3)[OF False] False show ?thesis
        by (simp add: shared_goal_view_def)
    next
      case None
      with k(3)[OF False] False show ?thesis by (simp add: shared_goal_view_def)
    qed
  qed
  show "shared_node_view ?s' p = shared_node_view s p"
  proof (cases "RBT.lookup (shared_nodes s) p")
    case (Some hn)
    from node_entry_extends[OF tf shared_entries_formed(2)[OF s Some] k(2)] Some k(4)[of p] show ?thesis
      by (simp add: shared_node_view_def)
  next
    case None
    with k(4)[of p] show ?thesis by (simp add: shared_node_view_def)
  qed
qed

lemma shared_goal_substitute_fold_views:
  assumes s: "shared_state_formed \<kappa> P s" and tf0: "table_formed T0" and ext: "table_extends T0 (shared_state_table s)"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" and qs: "distinct qs"
  shows "shared_state_formed \<kappa> P (fold (shared_goal_substitute_at P \<sigma> D) qs s) \<and>
    table_extends T0 (shared_state_table (fold (shared_goal_substitute_at P \<sigma> D) qs s)) \<and>
    (\<forall>p. shared_goal_view (fold (shared_goal_substitute_at P \<sigma> D) qs s) p = (if p \<in> set qs then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (shared_goal_view s p)
      else shared_goal_view s p)) \<and>
    (\<forall>p. shared_node_view (fold (shared_goal_substitute_at P \<sigma> D) qs s) p = shared_node_view s p) \<and>
    shared_witnesses (fold (shared_goal_substitute_at P \<sigma> D) qs s) = shared_witnesses s"
  using s ext qs
proof (induction qs arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  let ?s1 = "shared_goal_substitute_at P \<sigma> D q s"
  have \<sigma>t: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" using shared_pattern_extends(1)[OF tf0 \<sigma>f Cons.prems(2)] .
  have \<tau>: "(\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a)) = (\<lambda>a. shared_pattern_project T0 (\<sigma> a))"
    using shared_pattern_extends(2)[OF tf0 \<sigma>f Cons.prems(2)] by simp
  note k = shared_goal_substitute_at[where D = D and q = q, OF Cons.prems(1) \<sigma>t \<sigma>c out]
  note v = shared_goal_substitute_at_views[where D = D and q = q, OF Cons.prems(1) \<sigma>t \<sigma>c out]
  have e1: "table_extends T0 (shared_state_table ?s1)" using table_extends_trans[OF Cons.prems(2) k(2)] .
  have IH: "shared_state_formed \<kappa> P (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1) \<and>
      table_extends T0 (shared_state_table (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1)) \<and>
      (\<forall>p. shared_goal_view (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1) p = (if p \<in> set qs then
        map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (shared_goal_view ?s1 p)
        else shared_goal_view ?s1 p)) \<and>
      (\<forall>p. shared_node_view (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1) p = shared_node_view ?s1 p) \<and>
      shared_witnesses (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1) = shared_witnesses ?s1"
    by (rule Cons.IH[OF k(1) e1]) (use Cons.prems(3) in simp)
  have nq: "q \<notin> set qs" using Cons.prems(3) by simp
  have gv: "shared_goal_view (fold (shared_goal_substitute_at P \<sigma> D) qs ?s1) p = (if p \<in> set (q # qs) then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (shared_goal_view s p)
      else shared_goal_view s p)" for p
  proof (cases "p = q")
    case True
    then show ?thesis using IH nq v(1)[of q] \<tau> by simp
  next
    case False
    then show ?thesis using IH v(1)[of p] by simp
  qed
  show ?case using IH gv v(2) k(6) by simp
qed

theorem search_goal_substitute:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and \<sigma>f: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_formed \<kappa> P (search_goal_substitute P \<sigma> D r)" and "search_classes_formed (search_goal_substitute P \<sigma> D r)"
    and "table_extends (search_table r) (search_table (search_goal_substitute P \<sigma> D r))"
    and "\<And>p. RBT.lookup (shared_nodes (search_state (search_goal_substitute P \<sigma> D r))) p =
      RBT.lookup (shared_nodes (search_state r)) p"
proof -
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF search_formedD(1)[OF r]] .
  note f = search_goal_substitute_fold[where D = D and qs = "sorted_list_of_fset (shared_substitute_positions D (search_state r))",
      OF r K tf table_extends_refl \<sigma>f \<sigma>c out]
  show "search_formed \<kappa> P (search_goal_substitute P \<sigma> D r)" using f by (simp add: search_goal_substitute_def)
  show "search_classes_formed (search_goal_substitute P \<sigma> D r)" using f by (simp add: search_goal_substitute_def)
  show "table_extends (search_table r) (search_table (search_goal_substitute P \<sigma> D r))"
    using f by (simp add: search_goal_substitute_def)
  show "\<And>p. RBT.lookup (shared_nodes (search_state (search_goal_substitute P \<sigma> D r))) p =
      RBT.lookup (shared_nodes (search_state r)) p" using f by (simp add: search_goal_substitute_def)
qed

lemma search_goal_substitute_state:
  "search_state (fold (search_goal_substitute_at P \<sigma> D) qs r) = fold (shared_goal_substitute_at P \<sigma> D) qs (search_state r)"
  by (induction qs arbitrary: r) (simp_all add: search_goal_substitute_at_def)

text \<open>
  The goals substituted alone project to the shared substitution's goals, the nodes as they were: a goal the holder
  index does not reach holds no variable of the domain.
\<close>

theorem search_goal_substitute_project:
  assumes r: "search_formed \<kappa> P r"
    and \<sigma>f: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_project (search_goal_substitute P \<sigma> D r) = Resolution_State
    (fimage (resolution_goal_substitute (\<lambda>a. shared_pattern_project (search_table r) (\<sigma> a))) (resolution_pending (search_project r)))
    (resolution_nodes (search_project r)) (resolution_witnesses (search_project r))"
proof -
  let ?s = "search_state r" and ?T = "search_table r"
  let ?qs = "sorted_list_of_fset (shared_substitute_positions D ?s)"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T (\<sigma> a)"
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have outA: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" using out by blast
  note f = shared_goal_substitute_fold_views[where D = D and qs = ?qs, OF s tf table_extends_refl \<sigma>f \<sigma>c outA]
  have eq: "search_state (search_goal_substitute P \<sigma> D r) = fold (shared_goal_substitute_at P \<sigma> D) ?qs ?s"
    by (simp add: search_goal_substitute_def search_goal_substitute_state)
  have g: "shared_goal_view (search_state (search_goal_substitute P \<sigma> D r)) p =
      map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view ?s p)" for p
  proof (cases "p \<in> set ?qs")
    case True
    then show ?thesis using f eq by simp
  next
    case False
    then have pn: "p |\<notin>| shared_substitute_positions D ?s" by simp
    have "shared_goal_view ?s p = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view ?s p)"
      by (rule shared_substitute_unvisited(1)[OF s _ pn]) (rule out)
    then show ?thesis using f eq False by simp
  qed
  have n: "shared_node_view (search_state (search_goal_substitute P \<sigma> D r)) p = map_option id (shared_node_view ?s p)" for p
    using f eq by (simp add: option.map_id)
  have w: "shared_witnesses (search_state (search_goal_substitute P \<sigma> D r)) = shared_witnesses ?s" using f eq by simp
  show ?thesis using shared_state_project_views[OF g n w] by (simp add: fset.map_id)
qed

subsection \<open>The variables a substitution leaves\<close>

text \<open>A pattern's substitution holds only variables of the images of its variables, a goal's likewise.\<close>

lemma finite_pattern_substitute_within:
  "(\<And>y. y |\<in>| finite_pattern_variables p \<Longrightarrow> fset (finite_pattern_variables (\<tau> y)) \<subseteq> A) \<Longrightarrow>
    fset (finite_pattern_variables (finite_pattern_substitute \<tau> p)) \<subseteq> A"
  by (induction p) auto

lemma resolution_goal_substitute_within:
  assumes w: "\<And>y. y |\<in>| resolution_goal_variables g \<Longrightarrow> fset (finite_pattern_variables (\<tau> y)) \<subseteq> A"
  shows "fset (resolution_goal_variables (resolution_goal_substitute \<tau> g)) \<subseteq> A"
proof -
  have f: "fset (finite_pattern_variables (finite_pattern_substitute \<tau> p)) \<subseteq> A"
    if sub: "finite_pattern_variables p |\<subseteq>| resolution_goal_variables g" for p
  proof (rule finite_pattern_substitute_within)
    fix y assume "y |\<in>| finite_pattern_variables p"
    then have "y |\<in>| resolution_goal_variables g" using sub by blast
    then show "fset (finite_pattern_variables (\<tau> y)) \<subseteq> A" by (rule w)
  qed
  show ?thesis
  proof (cases g)
    case (Resolution_Call_Goal q r d p)
    then show ?thesis using f[of p] by simp
  next
    case (Resolution_Material_Goal q r M)
    have "fset (finite_pattern_variables (finite_pattern_substitute \<tau> (finite_material_source M))) \<subseteq> A"
      "fset (finite_pattern_variables (finite_pattern_substitute \<tau> (finite_material_atoms M))) \<subseteq> A"
      "fset (finite_pattern_variables (finite_pattern_substitute \<tau> (finite_material_edges M))) \<subseteq> A"
      "fset (finite_pattern_variables (finite_pattern_substitute \<tau> (finite_material_counts M))) \<subseteq> A"
      "fset (finite_pattern_variables (finite_pattern_substitute \<tau> (finite_material_functions M))) \<subseteq> A"
      by (rule f; auto simp: Resolution_Material_Goal finite_material_variables_def)+
    then show ?thesis using Resolution_Material_Goal
      by (simp add: finite_material_variables_def finite_material_pattern_substitute_def)
  qed
qed

subsection \<open>A node resolved once, when its call is ground\<close>

text \<open>
  A node whose call the store resolves to a ground pattern is resolved in the shared state: its call is collapsed to
  its reference (@{const keyed_binding_resolve}), its bindings resolved, and it is re-entered at its position. The store
  resolves the node to itself afterwards, so the deferred projection is kept.
\<close>

definition deferred_ground_derivation :: "('s,'a) resolution_variable binding_store \<Rightarrow>
    ('s,'a) resolution_variable shared_pattern \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> ('a,'s,'d,'c) shared_derivation" where
  "deferred_ground_derivation S c nd = Shared_Derivation (shared_derivation_position nd) (shared_derivation_site nd)
    (shared_derivation_clause nd) (shared_derivation_schema nd) c
    (fimage (\<lambda>z. (fst z, binding_resolve S (snd z))) (shared_derivation_bindings nd))"

definition deferred_ground :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_ground q d = (case RBT.lookup (shared_nodes (search_state (deferred_inner d))) q of None \<Rightarrow> d
    | Some hn \<Rightarrow> (case keyed_binding_resolve (deferred_store d) (shared_derivation_call (shared_entry_node hn))
        (shared_sharing (search_state (deferred_inner d))) of (c, x) \<Rightarrow>
      d\<lparr>deferred_inner := search_update q (shared_put_node q
        (enter_node (deferred_ground_derivation (deferred_store d) c (shared_entry_node hn)))
        (shared_reshare x (search_state (deferred_inner d)))) (deferred_inner d)\<rparr>))"

lemma deferred_inner_update_key [simp]: "deferred_key (d\<lparr>deferred_inner := r\<rparr>) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def)

lemma deferred_inner_update [simp]:
  "deferred_numbered (d\<lparr>deferred_inner := r\<rparr>) = deferred_numbered d"
  "deferred_store (d\<lparr>deferred_inner := r\<rparr>) = deferred_store d"
  by (simp_all add: fun_eq_iff deferred_numbered_def deferred_store_def)

lemma binding_resolve_idempotent:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
  shows "binding_resolve S (binding_resolve S p) = binding_resolve S p"
  by (rule binding_resolve_unbound) (use binding_resolve_variables[OF S p] in blast)

lemma deferred_ground_fixed:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
  shows "finite_pattern_substitute (\<lambda>x. shared_pattern_project T (binding_substitution S x))
    (shared_pattern_project T (binding_resolve S p)) = shared_pattern_project T (binding_resolve S p)"
  using binding_resolve_project[OF S binding_resolve_formed[OF S p]] binding_resolve_idempotent[OF S p] by simp

lemma derivation_resolve_fixed:
  assumes S: "binding_store_formed T S" and nd: "shared_derivation_formed T nd"
  shows "resolution_node_substitute (\<lambda>x. shared_pattern_project T (binding_substitution S x))
    (shared_derivation_project T (derivation_resolve S nd)) = shared_derivation_project T (derivation_resolve S nd)"
proof -
  let ?\<sigma> = "\<lambda>x. shared_pattern_project T (binding_substitution S x)"
  have c: "shared_pattern_formed T (shared_derivation_call nd)" using nd by (simp add: shared_derivation_formed_def)
  have b: "finite_pattern_substitute ?\<sigma> (shared_pattern_project T (binding_resolve S (snd z))) =
      shared_pattern_project T (binding_resolve S (snd z))" if "z |\<in>| shared_derivation_bindings nd" for z
    using deferred_ground_fixed[OF S] nd that by (simp add: shared_derivation_formed_def)
  have B: "fimage (\<lambda>z. (fst z, finite_pattern_substitute ?\<sigma> (shared_pattern_project T (binding_resolve S (snd z)))))
      (shared_derivation_bindings nd) =
    fimage (\<lambda>z. (fst z, shared_pattern_project T (binding_resolve S (snd z)))) (shared_derivation_bindings nd)"
    by (rule fset.map_cong0) (simp add: b)
  show ?thesis using deferred_ground_fixed[OF S c] B
    by (simp add: shared_derivation_project_def fset.map_comp comp_def case_prod_beta)
qed

theorem deferred_ground:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
    and gr: "shared_pattern_variables (deferred_call d hn) = {||}"
  shows "deferred_parts_formed \<kappa> P (deferred_ground q d)"
    and "\<exists>r'. deferred_ground q d = d\<lparr>deferred_inner := r'\<rparr>"
    and "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
    and "\<exists>hn'. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) q = Some hn' \<and>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_ground q d) q'"
    and "position_number (deferred_positions d) q \<noteq> 0 \<Longrightarrow>
      RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K) \<Longrightarrow>
      set (RBT.keys K) = {} \<Longrightarrow> deferred_node_formed (deferred_ground q d) q"
    and "deferred_project (deferred_ground q d) = deferred_project d"
    and "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground q d)))"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T0 = "search_table ?r" let ?S = "deferred_store d"
  let ?nd = "shared_entry_node hn" let ?c = "shared_derivation_call ?nd" let ?x0 = "shared_sharing ?s"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" and S: "binding_store_formed ?T0 ?S"
    using parts unfolding deferred_parts_formed_def by blast+
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have x0: "share_state_formed ?x0" and tf0: "table_formed ?T0" using shared_entries_formed(3,4)[OF s] .
  have nf0: "node_entry_formed ?T0 q hn" using shared_entries_formed(2)[OF s at] .
  have ndf: "shared_derivation_formed ?T0 ?nd" and pos: "shared_derivation_position ?nd = q"
    using nf0 by (simp_all add: node_entry_formed_def)
  have cf: "shared_pattern_formed ?T0 ?c" and cc: "shared_collapsed ?c" using ndf by (simp_all add: shared_derivation_formed_def)
  have rf: "shared_pattern_formed ?T0 (binding_resolve ?S ?c)" by (rule binding_resolve_formed[OF S cf])
  obtain c' x1 where kc: "keyed_binding_resolve ?S ?c ?x0 = (c', x1)" by (cases "keyed_binding_resolve ?S ?c ?x0")
  have kc': "keyed_share_collapse (binding_resolve ?S ?c) ?x0 = (c', x1)"
    using kc keyed_binding_resolve_collapse[OF S cf cc, of ?x0] by simp
  have kb: "keyed_collapse_bindings [(undefined, binding_resolve ?S ?c)] ?x0 = ([(undefined, c')], x1)"
    using kc' by simp
  have col: "share_state_formed x1 \<and> table_extends ?T0 (share_state_table x1) \<and>
      shared_pattern_formed (share_state_table x1) c' \<and>
      shared_pattern_project (share_state_table x1) c' = shared_pattern_project ?T0 (binding_resolve ?S ?c) \<and>
      shared_collapsed c'"
    using keyed_collapse_bindings[OF x0, of "[(undefined, binding_resolve ?S ?c)]"] rf kb
    by (simp add: shared_bindings_formed_def shared_bindings_project_def)
  let ?T1 = "share_state_table x1"
  have x1: "share_state_formed x1" and ext: "table_extends ?T0 ?T1" and c'f: "shared_pattern_formed ?T1 c'"
    and c'p: "shared_pattern_project ?T1 c' = shared_pattern_project ?T0 (binding_resolve ?S ?c)"
    and c'c: "shared_collapsed c'" using col by simp_all
  have c'v: "shared_pattern_variables c' = {||}"
    using c'p shared_pattern_variables_project[OF c'f] shared_pattern_variables_project[OF rf] gr by simp
  let ?nd' = "deferred_ground_derivation ?S c' ?nd"
  have bf: "shared_pattern_formed ?T1 (binding_resolve ?S (snd z))" and
    bp: "shared_pattern_project ?T1 (binding_resolve ?S (snd z)) = shared_pattern_project ?T0 (binding_resolve ?S (snd z))"
    if "z |\<in>| shared_derivation_bindings ?nd" for z
  proof -
    have "shared_pattern_formed ?T0 (snd z)" using ndf that by (simp add: shared_derivation_formed_def)
    then have "shared_pattern_formed ?T0 (binding_resolve ?S (snd z))" by (rule binding_resolve_formed[OF S])
    then show "shared_pattern_formed ?T1 (binding_resolve ?S (snd z))"
      "shared_pattern_project ?T1 (binding_resolve ?S (snd z)) = shared_pattern_project ?T0 (binding_resolve ?S (snd z))"
      using shared_pattern_extends[OF tf0 _ ext] by blast+
  qed
  have nd'f: "shared_derivation_formed ?T1 ?nd'"
    using c'f c'c bf by (auto simp: shared_derivation_formed_def deferred_ground_derivation_def)
  let ?s1 = "shared_reshare x1 ?s"
  have s1: "shared_state_formed \<kappa> P ?s1" using shared_reshare(1)[OF s x1 ext] .
  have tbl1: "shared_state_table ?s1 = ?T1" by (simp add: shared_reshare_def)
  let ?s2 = "shared_put_node q (enter_node ?nd') ?s1"
  have no: "node_entry_formed (shared_state_table ?s1) q (enter_node ?nd')"
    using nd'f pos tbl1 by (simp add: node_entry_formed_def enter_node_def deferred_ground_derivation_def)
  have s2: "shared_state_formed \<kappa> P ?s2" unfolding shared_put_node_def
    by (rule shared_replace_formed[OF s1]) (use shared_entries_formed(1)[OF s1] no in simp_all)
  have tbl2: "shared_state_table ?s2 = ?T1" using tbl1 by (simp add: shared_put_node_def)
  have goals2: "RBT.lookup (shared_goals ?s2) p = RBT.lookup (shared_goals ?s) p" for p
    by (simp add: shared_put_node_def shared_reshare_def)
  have nodes2: "RBT.lookup (shared_nodes ?s2) p = (if p = q then Some (enter_node ?nd') else RBT.lookup (shared_nodes ?s) p)" for p
    by (simp add: shared_put_node_def shared_reshare_def)
  let ?r' = "search_update q ?s2 ?r"
  have eq: "deferred_ground q d = d\<lparr>deferred_inner := ?r'\<rparr>" by (simp add: deferred_ground_def at kc)
  have r': "search_formed \<kappa> P ?r'" by (rule search_update[OF r s2]) (simp_all add: tbl2 ext goals2)
  have K': "search_classes_formed ?r'"
    by (rule search_update_classes[OF r K r']) (simp_all add: tbl2 ext goals2 nodes2)
  have S': "binding_store_formed ?T1 ?S"
    using binding_store_formed_extended[OF S tf0] ext by (simp add: table_extends_def)
  show "\<exists>r'. deferred_ground q d = d\<lparr>deferred_inner := r'\<rparr>" using eq by blast
  show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground q d)))"
    using ext tbl2 eq by simp
  show "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p" using nodes2 eq by simp
  show "\<exists>hn'. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) q = Some hn' \<and>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
    using nodes2 eq c'v by (simp add: deferred_ground_derivation_def)
  have nodes': "RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p \<noteq> None \<longleftrightarrow>
      RBT.lookup (shared_nodes ?s) p \<noteq> None" for p
    using nodes2 at eq by simp
  have goals': "RBT.lookup (shared_goals (search_state (deferred_inner (deferred_ground q d)))) p =
      RBT.lookup (shared_goals ?s) p" for p using goals2 eq by simp
  show "deferred_parts_formed \<kappa> P (deferred_ground q d)"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner (deferred_ground q d))" using r' eq by simp
    show "search_classes_formed (deferred_inner (deferred_ground q d))" using K' eq by simp
    show "positions_numbered (deferred_positions (deferred_ground q d))"
      using parts eq unfolding deferred_parts_formed_def by simp
    show "binding_store_formed (search_table (deferred_inner (deferred_ground q d))) (deferred_store (deferred_ground q d))"
      using S' tbl2 eq by simp
    show "\<forall>k v. RBT.lookup (snd (deferred_tree (deferred_ground q d))) k = Some v \<longrightarrow>
        (\<exists>x. deferred_numbered (deferred_ground q d) x \<and> deferred_key (deferred_ground q d) x = k)"
      using parts eq unfolding deferred_parts_formed_def by simp
    show "\<forall>x. binding_map (deferred_store (deferred_ground q d)) x \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) (fst (fst x)) \<noteq> None"
      using parts eq nodes' unfolding deferred_parts_formed_def by simp
    show "\<forall>q' h x. RBT.lookup (shared_goals (search_state (deferred_inner (deferred_ground q d)))) q' = Some h \<longrightarrow>
        x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store (deferred_ground q d)) x = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) (fst (fst x)) \<noteq> None"
      using parts eq nodes' goals' unfolding deferred_parts_formed_def by simp
    show "\<forall>n q' K. RBT.lookup (deferred_records (deferred_ground q d)) n = Some (q', K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions (deferred_ground q d)) q' \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) q' \<noteq> None"
      using parts eq nodes' unfolding deferred_parts_formed_def by simp
  qed
  show "deferred_node_formed (deferred_ground q d) q'" if ne: "q' \<noteq> q" and nf: "deferred_node_formed d q'" for q'
    using nf nodes2[of q'] ne eq unfolding deferred_node_formed_def by simp
  show "deferred_node_formed (deferred_ground q d) q"
    if n0: "position_number (deferred_positions d) q \<noteq> 0"
      and rec: "RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K)"
      and keys: "set (RBT.keys K) = {}" for K
  proof -
    have v': "shared_pattern_variables (binding_resolve ?S c') = {||}"
      using binding_resolve_unbound[of c' ?S] c'v by simp
    show ?thesis unfolding deferred_node_formed_def
      using n0 rec keys v' c'v nodes2[of q] eq by (simp add: deferred_ground_derivation_def)
  qed
  show "deferred_project (deferred_ground q d) = deferred_project d"
  proof -
    let ?\<sigma> = "deferred_substitution d"
    have \<sigma>': "deferred_substitution (deferred_ground q d) = ?\<sigma>"
    proof -
      have "shared_pattern_project ?T1 (binding_substitution ?S y) = shared_pattern_project ?T0 (binding_substitution ?S y)" for y
      proof -
        have "shared_pattern_formed ?T0 (binding_substitution ?S y)"
          unfolding binding_substitution_def by (rule binding_resolve_formed[OF S]) simp
        then show ?thesis using shared_pattern_extends(2)[OF tf0 _ ext] by blast
      qed
      then show ?thesis using eq tbl2 by (simp add: fun_eq_iff deferred_substitution_def)
    qed
    have \<sigma>eq: "?\<sigma> = (\<lambda>x. shared_pattern_project ?T0 (binding_substitution ?S x))"
      by (simp add: fun_eq_iff deferred_substitution_def)
    have old': "shared_derivation_project ?T1 ?nd' = shared_derivation_project ?T0 (derivation_resolve ?S ?nd)"
    proof -
      have "fimage (\<lambda>z. (fst z, shared_pattern_project ?T1 (binding_resolve ?S (snd z)))) (shared_derivation_bindings ?nd) =
          fimage (\<lambda>z. (fst z, shared_pattern_project ?T0 (binding_resolve ?S (snd z)))) (shared_derivation_bindings ?nd)"
        by (rule fset.map_cong0) (simp add: bp)
      then show ?thesis using c'p
        by (simp add: shared_derivation_project_def deferred_ground_derivation_def fset.map_comp comp_def)
    qed
    have old: "resolution_node_substitute ?\<sigma> (shared_derivation_project ?T0 ?nd) = shared_derivation_project ?T1 ?nd'"
      unfolding old' \<sigma>eq by (rule derivation_resolve_project[OF S ndf, symmetric])
    have fixed_new: "resolution_node_substitute ?\<sigma> (shared_derivation_project ?T1 ?nd') = shared_derivation_project ?T1 ?nd'"
      unfolding old' \<sigma>eq by (rule derivation_resolve_fixed[OF S ndf])
    define k where "k = (\<lambda>x. if resolution_node_position x = q then shared_derivation_project ?T1 ?nd' else x)"
    have gv: "shared_goal_view ?s2 p = map_option id (shared_goal_view ?s p)" for p
    proof (cases "RBT.lookup (shared_goals ?s) p")
      case (Some h)
      from goal_entry_extends[OF tf0 shared_entries_formed(1)[OF s Some] ext] Some goals2[of p] tbl2 show ?thesis
        by (simp add: shared_goal_view_def)
    qed (simp add: shared_goal_view_def goals2)
    have nv: "shared_node_view ?s2 p = map_option k (shared_node_view ?s p)" for p
    proof (cases "p = q")
      case True
      then show ?thesis using at pos tbl2 nodes2 by (simp add: shared_node_view_def k_def shared_derivation_project_def)
    next
      case False
      show ?thesis
      proof (cases "RBT.lookup (shared_nodes ?s) p")
        case (Some hn2)
        have p2: "shared_derivation_position (shared_entry_node hn2) = p"
          using shared_entries_formed(2)[OF s Some] by (simp add: node_entry_formed_def)
        from node_entry_extends[OF tf0 shared_entries_formed(2)[OF s Some] ext] Some nodes2[of p] False tbl2 p2 show ?thesis
          by (simp add: shared_node_view_def k_def shared_derivation_project_def)
      qed (simp add: shared_node_view_def nodes2 False)
    qed
    have wv: "shared_witnesses ?s2 = shared_witnesses ?s" by (simp add: shared_put_node_def shared_reshare_def)
    have pj: "search_project ?r' = Resolution_State (fimage id (resolution_pending (search_project ?r)))
        (fimage k (resolution_nodes (search_project ?r))) (resolution_witnesses (search_project ?r))"
      using shared_state_project_views[OF gv nv wv] by simp
    have kf: "resolution_node_substitute ?\<sigma> (k x) = resolution_node_substitute ?\<sigma> x"
      if xin: "x |\<in>| resolution_nodes (search_project ?r)" for x
    proof (cases "resolution_node_position x = q")
      case True
      obtain p hp where hp: "RBT.lookup (shared_nodes ?s) p = Some hp" and xe: "x = shared_derivation_project ?T0 (shared_entry_node hp)"
        using xin unfolding shared_state_project_member(2) by blast
      have "shared_derivation_position (shared_entry_node hp) = p"
        using shared_entries_formed(2)[OF s hp] by (simp add: node_entry_formed_def)
      then have "p = q" using True xe by (simp add: shared_derivation_project_def)
      then have "x = shared_derivation_project ?T0 ?nd" using hp at xe by simp
      then show ?thesis using True fixed_new old k_def by simp
    qed (simp add: k_def)
    have kN: "fimage (resolution_node_substitute ?\<sigma>) (fimage k (resolution_nodes (search_project ?r))) =
        fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes (search_project ?r))"
      unfolding fset.map_comp by (rule fset.map_cong0) (simp add: kf)
    have \<sigma>'': "deferred_substitution (d\<lparr>deferred_inner := ?r'\<rparr>) = ?\<sigma>" using \<sigma>' eq by simp
    have "deferred_project (deferred_ground q d) = resolution_state_substitute ?\<sigma> (search_project ?r')"
      using \<sigma>'' eq by (simp add: deferred_project_def)
    also have "\<dots> = Resolution_State (fimage (resolution_goal_substitute ?\<sigma>) (resolution_pending (search_project ?r)))
        (fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes (search_project ?r))) (resolution_witnesses (search_project ?r))"
      unfolding pj resolution_state_substitute_def using kN by (simp add: fset.map_id)
    also have "\<dots> = deferred_project d" by (simp add: deferred_project_def resolution_state_substitute_def)
    finally show ?thesis .
  qed
qed

subsection \<open>The unifier recorded in the store\<close>

text \<open>
  The tree binds the unifier at the keys of its domain; every variable it binds is numbered, and every key the tree
  holds is a numbered variable's, so the store read through the tree is D1a's store with the unifier bound.
\<close>

lemma binding_tree_fold_other:
  "\<forall>b\<in>set (map fst s). key b \<noteq> k \<Longrightarrow>
    RBT.lookup (fold (\<lambda>(a, p) t. RBT.insert (key a) (n, p) t) (rev s) t) k = RBT.lookup t k"
  by (induction s) (auto simp: RBT.lookup_insert split: prod.splits)

lemma deferred_tree_update_key [simp]: "deferred_key (d\<lparr>deferred_tree := K\<rparr>) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def)

lemma deferred_tree_update_numbered [simp]: "deferred_numbered (d\<lparr>deferred_tree := K\<rparr>) = deferred_numbered d"
  by (simp add: fun_eq_iff deferred_numbered_def)

lemma deferred_store_bind:
  assumes N: "positions_numbered (deferred_positions d)"
    and num: "\<And>a. a \<in> set (map fst s) \<Longrightarrow> deferred_numbered d a"
  shows "deferred_store (d\<lparr>deferred_tree := binding_tree_bind (deferred_key d) (deferred_tree d) s\<rparr>) =
    store_bind (deferred_store d) (shared_binding_substitution s) (shared_binding_domain s)"
proof -
  let ?Q = "{x. deferred_numbered d x}" and ?K = "deferred_tree d" and ?key = "deferred_key d"
  have key: "inj_on ?key ?Q" using deferred_key_inj[OF N] unfolding inj_on_def by blast
  have sQ: "set (map fst s) \<subseteq> ?Q" using num by blast
  have m: "RBT.lookup (snd (binding_tree_bind ?key ?K s)) (?key b) = bound_map (fst ?K)
      (\<lambda>a. RBT.lookup (snd ?K) (?key a)) (shared_binding_substitution s) (shared_binding_domain s) b" for b
  proof (cases "deferred_numbered d b")
    case True
    note fl = binding_tree_fold_lookup[OF key sQ, where b = b and n = "fst ?K" and t = "snd ?K"]
    show ?thesis
    proof (cases "map_of s b")
      case None
      then have "b |\<notin>| shared_binding_domain s"
        by (simp add: shared_binding_domain_def fset_of_list.rep_eq map_of_eq_None_iff)
      then show ?thesis using fl True None by (simp add: binding_tree_bind_def bound_map_def)
    next
      case (Some p)
      then have "b |\<in>| shared_binding_domain s"
        by (force simp: shared_binding_domain_def fset_of_list.rep_eq dest: map_of_SomeD)
      then show ?thesis using fl True Some by (simp add: binding_tree_bind_def bound_map_def shared_binding_substitution_def)
    qed
  next
    case False
    have out: "\<forall>a\<in>set (map fst s). ?key a \<noteq> ?key b"
    proof
      fix a assume "a \<in> set (map fst s)"
      then have a: "deferred_numbered d a" by (rule num)
      show "?key a \<noteq> ?key b" using deferred_key_zero[OF False a] by auto
    qed
    have "b \<notin> set (map fst s)" using num False by blast
    then have "b |\<notin>| shared_binding_domain s" by (simp add: shared_binding_domain_def fset_of_list_elem fset_of_list.rep_eq)
    then show ?thesis using binding_tree_fold_other[OF out, where n = "fst ?K" and t = "snd ?K"]
      by (simp add: binding_tree_bind_def bound_map_def)
  qed
  have fs: "fst (binding_tree_bind ?key ?K s) = Suc (fst ?K)" by (simp add: binding_tree_bind_def)
  show ?thesis using m fs by (simp add: deferred_store_def binding_tree_store_def store_bind_def fun_eq_iff)
qed

subsection \<open>A node whose call the unifier reaches\<close>

text \<open>
  A node the bind reaches is stale for the store before the bind: its record holds its resolution's variables under
  that store. Its update reads the store's variables law off its record: a key whose variable the unifier binds is
  replaced by the keys of that variable's image, the others kept, the node added to the holders of each; a node whose
  variables become none is resolved (@{const deferred_ground}).
\<close>

definition deferred_node_stale :: "('s,'a) resolution_variable binding_store \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    's list \<Rightarrow> bool" where
  "deferred_node_stale S d q \<longleftrightarrow> (\<forall>hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<longrightarrow>
    position_number (deferred_positions d) q \<noteq> 0 \<and>
    (\<exists>K. RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K) \<and>
      set (RBT.keys K) = deferred_key d ` fset (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn))))) \<and>
    fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn)))) (deferred_numbered d))"

definition deferred_update_keys :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    (deferred_key, unit) rbt \<Rightarrow> deferred_key list" where
  "deferred_update_keys d \<sigma> D K = concat (map (\<lambda>k. if deferred_decode d k |\<in>| D
      then map (deferred_key d) (shared_variable_list (\<sigma> (deferred_decode d k))) else [k]) (RBT.keys K))"

definition deferred_update :: "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> nat \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_update \<sigma> D n d = (case RBT.lookup (deferred_records d) n of None \<Rightarrow> d | Some z \<Rightarrow>
    (let ks = deferred_update_keys d \<sigma> D (snd z); d1 = deferred_record_at n (fst z) ks d in
      if ks = [] then deferred_ground (fst z) d1 else d1))"

lemma deferred_record_at_key [simp]: "deferred_key (deferred_record_at n q ks d) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def)

lemma deferred_record_at_store [simp]:
  "deferred_numbered (deferred_record_at n q ks d) = deferred_numbered d"
  "deferred_store (deferred_record_at n q ks d) = deferred_store d"
  by (simp_all add: fun_eq_iff deferred_numbered_def deferred_store_def)

lemma deferred_record_at_project [simp]: "deferred_project (deferred_record_at n q ks d) = deferred_project d"
  by (simp add: deferred_project_def deferred_substitution_def[abs_def])

lemma deferred_record_at_parts:
  assumes parts: "deferred_parts_formed \<kappa> P d" and n: "n \<noteq> 0" "n = position_number (deferred_positions d) q"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
  shows "deferred_parts_formed \<kappa> P (deferred_record_at n q ks d)"
proof -
  have b: "\<And>n' q' K'. RBT.lookup (deferred_records d) n' = Some (q', K') \<Longrightarrow> n' \<noteq> 0 \<and>
      n' = position_number (deferred_positions d) q' \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d))) q' \<noteq> None"
    using parts unfolding deferred_parts_formed_def by blast
  have rc: "\<forall>n' q' K'. RBT.lookup (deferred_records (deferred_record_at n q ks d)) n' = Some (q', K') \<longrightarrow> n' \<noteq> 0 \<and>
      n' = position_number (deferred_positions (deferred_record_at n q ks d)) q' \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_at n q ks d)))) q' \<noteq> None"
  proof (intro allI impI)
    fix n' q' K' assume "RBT.lookup (deferred_records (deferred_record_at n q ks d)) n' = Some (q', K')"
    then show "n' \<noteq> 0 \<and> n' = position_number (deferred_positions (deferred_record_at n q ks d)) q' \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_at n q ks d)))) q' \<noteq> None"
      using b[of n' q' K'] n at by (cases "n' = n") simp_all
  qed
  show ?thesis using parts rc unfolding deferred_parts_formed_def by simp
qed

lemma deferred_node_formed_stale:
  "deferred_node_formed d q \<Longrightarrow> deferred_node_stale (deferred_store d) d q"
  unfolding deferred_node_formed_def deferred_node_stale_def by blast

lemma unifier_ready_extends:
  assumes ready: "unifier_ready T M \<sigma> D" and tf: "table_formed T" and ext: "table_extends T T'"
  shows "unifier_ready T' M \<sigma> D"
  using ready shared_pattern_extends(1)[OF tf _ ext] unfolding unifier_ready_def by blast

lemma deferred_update:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and S: "binding_store_formed (search_table (deferred_inner d)) S"
    and ready: "unifier_ready (search_table (deferred_inner d)) (binding_map S) \<sigma> D"
    and st: "deferred_store d = store_bind S \<sigma> D"
    and num: "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and rec: "RBT.lookup (deferred_records d) n = Some (q, K)"
    and stale: "deferred_node_stale S d q"
  shows "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d)"
    and "deferred_node_formed (deferred_update \<sigma> D n d) q"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q'"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_stale S d q' \<Longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q'"
    and "deferred_project (deferred_update \<sigma> D n d) = deferred_project d"
    and "deferred_store (deferred_update \<sigma> D n d) = deferred_store d"
    and "deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d"
    and "deferred_names (deferred_update \<sigma> D n d) = deferred_names d"
    and "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
    and "deferred_records (deferred_update \<sigma> D n d) =
      RBT.insert n (q, fold (\<lambda>k t. RBT.insert k () t) (deferred_update_keys d \<sigma> D K) RBT.empty) (deferred_records d)"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r"
  have r: "search_formed \<kappa> P ?r" and N: "positions_numbered (deferred_positions d)"
    using parts unfolding deferred_parts_formed_def by blast+
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have nq: "n \<noteq> 0 \<and> n = position_number (deferred_positions d) q \<and> RBT.lookup (shared_nodes ?s) q \<noteq> None"
    using parts rec unfolding deferred_parts_formed_def by blast
  obtain hn where at: "RBT.lookup (shared_nodes ?s) q = Some hn" using nq by blast
  let ?c = "shared_derivation_call (shared_entry_node hn)"
  let ?V = "shared_pattern_variables (binding_resolve S ?c)"
  let ?V' = "shared_pattern_variables (binding_resolve (deferred_store d) ?c)"
  have cf: "shared_pattern_formed ?T ?c"
    using shared_entries_formed(2)[OF s at] by (simp add: node_entry_formed_def shared_derivation_formed_def)
  have keysK: "set (RBT.keys K) = deferred_key d ` fset ?V" and numV: "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_numbered d x"
    using stale at rec nq unfolding deferred_node_stale_def by auto
  have V': "x |\<in>| ?V' \<longleftrightarrow> x |\<in>| ?V \<and> x |\<notin>| D \<or> (\<exists>a. a |\<in>| ?V \<and> a |\<in>| D \<and> x |\<in>| shared_pattern_variables (\<sigma> a))" for x
    using store_bind_variables[OF S ready cf] st by simp
  have \<sigma>f: "\<And>a. a |\<in>| D \<Longrightarrow> shared_pattern_formed ?T (\<sigma> a)" using ready unfolding unifier_ready_def by blast
  have \<sigma>vl: "set (shared_variable_list (\<sigma> a)) = fset (shared_pattern_variables (\<sigma> a))" if "a |\<in>| D" for a
    by (rule shared_variable_list[OF \<sigma>f[OF that]])
  have dk: "deferred_decode d (deferred_key d x) = x" if "x |\<in>| ?V" for x using deferred_decode_key[OF N numV[OF that]] .
  let ?ks = "deferred_update_keys d \<sigma> D K"
  have ks: "set ?ks = deferred_key d ` fset ?V'"
  proof -
    have mem: "z \<in> set ?ks \<longleftrightarrow> (\<exists>x. x |\<in>| ?V \<and> (if x |\<in>| D
        then z \<in> deferred_key d ` fset (shared_pattern_variables (\<sigma> x)) else z = deferred_key d x))" for z
    proof -
      have "z \<in> set ?ks \<longleftrightarrow> (\<exists>k\<in>set (RBT.keys K). z \<in> set (if deferred_decode d k |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> (deferred_decode d k))) else [k]))"
        by (simp only: deferred_update_keys_def set_concat set_map image_image UN_iff)
      also have "\<dots> \<longleftrightarrow> (\<exists>x. x |\<in>| ?V \<and> z \<in> set (if x |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> x)) else [deferred_key d x]))"
      proof
        assume "\<exists>k\<in>set (RBT.keys K). z \<in> set (if deferred_decode d k |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> (deferred_decode d k))) else [k])"
        then obtain k where k: "k \<in> set (RBT.keys K)" and zk: "z \<in> set (if deferred_decode d k |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> (deferred_decode d k))) else [k])" by blast
        from k obtain x where x: "x |\<in>| ?V" "k = deferred_key d x" unfolding keysK by blast
        show "\<exists>x. x |\<in>| ?V \<and> z \<in> set (if x |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> x)) else [deferred_key d x])"
        proof -
          have "z \<in> set (if x |\<in>| D then map (deferred_key d) (shared_variable_list (\<sigma> x)) else [deferred_key d x])"
            using zk unfolding x(2) dk[OF x(1)] .
          then show ?thesis using x(1) by blast
        qed
      next
        assume "\<exists>x. x |\<in>| ?V \<and> z \<in> set (if x |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> x)) else [deferred_key d x])"
        then obtain x where x: "x |\<in>| ?V" and zx: "z \<in> set (if x |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> x)) else [deferred_key d x])" by blast
        have kx: "deferred_key d x \<in> set (RBT.keys K)" using x unfolding keysK by blast
        show "\<exists>k\<in>set (RBT.keys K). z \<in> set (if deferred_decode d k |\<in>| D
          then map (deferred_key d) (shared_variable_list (\<sigma> (deferred_decode d k))) else [k])"
        proof -
          have "z \<in> set (if deferred_decode d (deferred_key d x) |\<in>| D then map (deferred_key d)
              (shared_variable_list (\<sigma> (deferred_decode d (deferred_key d x)))) else [deferred_key d x])"
            unfolding dk[OF x] by (rule zx)
          then show ?thesis using kx by blast
        qed
      qed
      also have "\<dots> \<longleftrightarrow> (\<exists>x. x |\<in>| ?V \<and> (if x |\<in>| D
          then z \<in> deferred_key d ` fset (shared_pattern_variables (\<sigma> x)) else z = deferred_key d x))"
        using \<sigma>vl by (auto split: if_splits)
      finally show ?thesis .
    qed
    show ?thesis
    proof (rule set_eqI)
      fix z show "z \<in> set ?ks \<longleftrightarrow> z \<in> deferred_key d ` fset ?V'"
      proof
        assume "z \<in> set ?ks"
        then obtain x where x: "x |\<in>| ?V" and zx: "if x |\<in>| D
            then z \<in> deferred_key d ` fset (shared_pattern_variables (\<sigma> x)) else z = deferred_key d x"
          unfolding mem by blast
        show "z \<in> deferred_key d ` fset ?V'"
        proof (cases "x |\<in>| D")
          case True
          then obtain y where y: "y |\<in>| shared_pattern_variables (\<sigma> x)" "z = deferred_key d y" using zx by auto
          have "y |\<in>| ?V'" unfolding V' using x True y(1) by blast
          then show ?thesis using y(2) by blast
        next
          case False
          have "x |\<in>| ?V'" unfolding V' using x False by blast
          then show ?thesis using zx False by auto
        qed
      next
        assume "z \<in> deferred_key d ` fset ?V'"
        then obtain y where y1: "y |\<in>| ?V'" and y2: "z = deferred_key d y" by blast
        from y1[unfolded V'] show "z \<in> set ?ks"
        proof (elim disjE conjE exE)
          assume "y |\<in>| ?V" "y |\<notin>| D"
          then show ?thesis unfolding mem using y2 by (intro exI[of _ y]) auto
        next
          fix a assume "a |\<in>| ?V" "a |\<in>| D" "y |\<in>| shared_pattern_variables (\<sigma> a)"
          then show ?thesis unfolding mem using y2 by (intro exI[of _ a]) auto
        qed
      qed
    qed
  qed
  have numV': "deferred_numbered d x" if "x |\<in>| ?V'" for x using that numV num unfolding V' by blast
  let ?d1 = "deferred_record_at n q ?ks d"
  have eq: "deferred_update \<sigma> D n d = (if ?ks = [] then deferred_ground q ?d1 else ?d1)"
    by (simp add: deferred_update_def rec Let_def)
  have parts1: "deferred_parts_formed \<kappa> P ?d1" using deferred_record_at_parts[OF parts] nq by blast
  have at1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q = Some hn" using at by simp
  have rec1: "RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q) =
      Some (q, fold (\<lambda>k t. RBT.insert k () t) ?ks RBT.empty)" using nq by simp
  have keys1: "set (RBT.keys (fold (\<lambda>k t. RBT.insert k () t) ?ks RBT.empty)) = deferred_key d ` fset ?V'"
    using fold_insert_unit_keys[of ?ks RBT.empty] ks by simp
  have nf1: "deferred_node_formed ?d1 q" if ne: "?ks \<noteq> []"
  proof -
    have "?V' \<noteq> {||}" using ne ks by auto
    then show ?thesis unfolding deferred_node_formed_def
      using at1 nq rec1 keys1 numV' by (auto simp: fset_of_list_elem ks)
  qed
  have other_rec: "RBT.lookup (deferred_records ?d1) (position_number (deferred_positions d) q') =
      RBT.lookup (deferred_records d) (position_number (deferred_positions d) q')"
    if ne: "q' \<noteq> q" and n0: "position_number (deferred_positions d) q' \<noteq> 0" for q'
  proof -
    obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
    have "position_number (deferred_positions d) q' \<noteq> n" using position_number_inj[OF T _ n0] ne nq by metis
    then show ?thesis by simp
  qed
  have other1: "deferred_node_formed ?d1 q'" if ne: "q' \<noteq> q" and nf: "deferred_node_formed d q'" for q'
    unfolding deferred_node_formed_def
  proof (intro allI impI)
    fix hn' assume a': "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q' = Some hn'"
    have a: "RBT.lookup (shared_nodes ?s) q' = Some hn'" using a' by simp
    note D = deferred_node_formedD[OF nf a]
    show "position_number (deferred_positions ?d1) q' \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q') = Some (q', K) \<and>
        set (RBT.keys K) = deferred_key ?d1 ` fset (shared_pattern_variables (deferred_call ?d1 hn'))) \<and>
      fBall (shared_pattern_variables (deferred_call ?d1 hn')) (deferred_numbered ?d1) \<and>
      fBall (shared_pattern_variables (deferred_call ?d1 hn'))
        (\<lambda>x. position_number (deferred_positions ?d1) q' |\<in>| tree_bucket (deferred_holders ?d1) (deferred_key ?d1 x)) \<and>
      (shared_pattern_variables (deferred_call ?d1 hn') = {||} \<longrightarrow>
        shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||})"
      using D other_rec[OF ne D(1)] by auto
  qed
  have stale1: "deferred_node_stale S ?d1 q'" if ne: "q' \<noteq> q" and sf: "deferred_node_stale S d q'" for q'
    unfolding deferred_node_stale_def
  proof (intro allI impI)
    fix hn' assume a': "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q' = Some hn'"
    have a: "RBT.lookup (shared_nodes ?s) q' = Some hn'" using a' by simp
    have q'0: "position_number (deferred_positions d) q' \<noteq> 0" using sf a unfolding deferred_node_stale_def by blast
    show "position_number (deferred_positions ?d1) q' \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q') = Some (q', K) \<and>
        set (RBT.keys K) = deferred_key ?d1 ` fset (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn'))))) \<and>
      fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn')))) (deferred_numbered ?d1)"
      using sf a other_rec[OF ne q'0] unfolding deferred_node_stale_def by auto
  qed
  show "deferred_records (deferred_update \<sigma> D n d) =
      RBT.insert n (q, fold (\<lambda>k t. RBT.insert k () t) ?ks RBT.empty) (deferred_records d)"
  proof (cases "?ks = []")
    case True
    obtain r' where "deferred_ground q ?d1 = ?d1\<lparr>deferred_inner := r'\<rparr>"
      using deferred_ground(2)[OF parts1 at1] True ks by (auto simp: st)
    then show ?thesis using eq True by simp
  qed (use eq in simp)
  show "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d)"
       "deferred_node_formed (deferred_update \<sigma> D n d) q"
       "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q'"
       "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_stale S d q' \<Longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q'"
       "deferred_project (deferred_update \<sigma> D n d) = deferred_project d"
       "deferred_store (deferred_update \<sigma> D n d) = deferred_store d"
       "deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d"
       "deferred_names (deferred_update \<sigma> D n d) = deferred_names d"
       "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
  proof -
    consider (ground) "?ks = []" | (kept) "?ks \<noteq> []" by blast
    then have all: "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d) \<and> deferred_node_formed (deferred_update \<sigma> D n d) q \<and>
      (\<forall>q'. q' \<noteq> q \<longrightarrow> deferred_node_formed d q' \<longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q') \<and>
      (\<forall>q'. q' \<noteq> q \<longrightarrow> deferred_node_stale S d q' \<longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q') \<and>
      deferred_project (deferred_update \<sigma> D n d) = deferred_project d \<and>
      deferred_store (deferred_update \<sigma> D n d) = deferred_store d \<and>
      deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d \<and>
      deferred_names (deferred_update \<sigma> D n d) = deferred_names d \<and>
      table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
    proof cases
      case ground
      have gr: "shared_pattern_variables (deferred_call ?d1 hn) = {||}" using ground ks by auto
      note G = deferred_ground[OF parts1 at1 gr]
      obtain r' where e': "deferred_ground q ?d1 = ?d1\<lparr>deferred_inner := r'\<rparr>" using G(2) by blast
      have ext': "table_extends ?T (search_table r')" using G(8) e' by simp
      have nfq: "deferred_node_formed (deferred_ground q ?d1) q"
        using G(6)[of "fold (\<lambda>k t. RBT.insert k () t) ?ks RBT.empty"] rec1 nq keys1 ground ks by auto
      have n3: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state r')) p =
          RBT.lookup (shared_nodes (search_state (deferred_inner d))) p" using G(3) e' by simp
      have stale_g: "deferred_node_stale S (deferred_ground q ?d1) q'" if ne: "q' \<noteq> q" and sf: "deferred_node_stale S ?d1 q'" for q'
        using sf n3[OF ne] unfolding deferred_node_stale_def e' by simp
      have upd: "deferred_update \<sigma> D n d = deferred_ground q ?d1" using eq ground by simp
      show ?thesis unfolding upd
      proof (intro conjI allI impI)
        show "deferred_parts_formed \<kappa> P (deferred_ground q ?d1)" by (rule G(1))
        show "deferred_node_formed (deferred_ground q ?d1) q" by (rule nfq)
        show "deferred_node_formed (deferred_ground q ?d1) q'" if "q' \<noteq> q" "deferred_node_formed d q'" for q'
          using G(5)[OF that(1) other1[OF that]] .
        show "deferred_node_stale S (deferred_ground q ?d1) q'" if "q' \<noteq> q" "deferred_node_stale S d q'" for q'
          using stale_g[OF that(1) stale1[OF that]] .
        show "deferred_project (deferred_ground q ?d1) = deferred_project d" using G(7) by simp
        show "deferred_store (deferred_ground q ?d1) = deferred_store d" using e' by simp
        show "deferred_positions (deferred_ground q ?d1) = deferred_positions d" using e' by simp
        show "deferred_names (deferred_ground q ?d1) = deferred_names d" using e' by simp
        show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground q ?d1)))"
          using ext' e' by simp
      qed
    next
      case kept
      have upd: "deferred_update \<sigma> D n d = ?d1" using eq kept by simp
      show ?thesis unfolding upd
      proof (intro conjI allI impI)
        show "deferred_parts_formed \<kappa> P ?d1" by (rule parts1)
        show "deferred_node_formed ?d1 q" by (rule nf1[OF kept])
        show "deferred_node_formed ?d1 q'" if "q' \<noteq> q" "deferred_node_formed d q'" for q' using other1[OF that] .
        show "deferred_node_stale S ?d1 q'" if "q' \<noteq> q" "deferred_node_stale S d q'" for q' using stale1[OF that] .
        show "deferred_project ?d1 = deferred_project d" by simp
        show "deferred_store ?d1 = deferred_store d" by simp
        show "deferred_positions ?d1 = deferred_positions d" by simp
        show "deferred_names ?d1 = deferred_names d" by simp
        show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner ?d1))"
          by (simp add: table_extends_refl)
      qed
    qed
    show "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d)" using all by blast
    show "deferred_node_formed (deferred_update \<sigma> D n d) q" using all by blast
    show "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q'" using all by blast
    show "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_stale S d q' \<Longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q'"
      using all by blast
    show "deferred_project (deferred_update \<sigma> D n d) = deferred_project d" using all by blast
    show "deferred_store (deferred_update \<sigma> D n d) = deferred_store d" using all by blast
    show "deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d" using all by blast
    show "deferred_names (deferred_update \<sigma> D n d) = deferred_names d" using all by blast
    show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
      using all by blast
  qed
qed

lemma deferred_ground_nodes:
  "p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p =
    RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
  by (simp add: deferred_ground_def shared_put_node_def shared_reshare_def split: option.splits prod.splits)

lemma deferred_update_nodes:
  "RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow> p \<noteq> q \<Longrightarrow>
    RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_update \<sigma> D n d)))) p =
    RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
  by (simp add: deferred_update_def Let_def deferred_ground_nodes)

lemma deferred_numbered_cong:
  "deferred_positions d' = deferred_positions d \<Longrightarrow> deferred_names d' = deferred_names d \<Longrightarrow>
    deferred_numbered d' = deferred_numbered d"
  by (simp add: fun_eq_iff deferred_numbered_def)

text \<open>
  The update runs over the numbers the holder index gives for the unifier's domain, each once: a node it reaches is
  stale before and formed after, every other node formed throughout, the projection and the store kept.
\<close>

lemma deferred_update_fold:
  assumes "deferred_parts_formed \<kappa> P d"
    and "binding_store_formed (search_table (deferred_inner d)) S"
    and "unifier_ready (search_table (deferred_inner d)) (binding_map S) \<sigma> D"
    and "deferred_store d = store_bind S \<sigma> D"
    and "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and "distinct ns"
    and "\<forall>q. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None \<longrightarrow>
      position_number (deferred_positions d) q \<in> set ns \<longrightarrow> deferred_node_stale S d q"
    and "\<forall>q. position_number (deferred_positions d) q \<notin> set ns \<longrightarrow> deferred_node_formed d q"
  shows "deferred_formed \<kappa> P (fold (deferred_update \<sigma> D) ns d) \<and>
    deferred_project (fold (deferred_update \<sigma> D) ns d) = deferred_project d \<and>
    deferred_store (fold (deferred_update \<sigma> D) ns d) = deferred_store d"
  using assms
proof (induction ns arbitrary: d)
  case Nil
  then show ?case by (simp add: deferred_formed_def)
next
  case (Cons n ns)
  have N: "positions_numbered (deferred_positions d)" using Cons.prems(1) unfolding deferred_parts_formed_def by blast
  obtain T where T: "keyed_reference_state id (deferred_positions d) T" using N by (auto simp: positions_numbered_def)
  have tf: "table_formed (search_table (deferred_inner d))"
    using shared_entries_formed(4)[OF search_formedD(1)] Cons.prems(1) unfolding deferred_parts_formed_def by blast
  have nsd: "distinct ns" and nn: "n \<notin> set ns" using Cons.prems(6) by simp_all
  show ?case
  proof (cases "RBT.lookup (deferred_records d) n")
    case None
    have u: "deferred_update \<sigma> D n d = d" by (simp add: deferred_update_def None)
    have st': "\<forall>q. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None \<longrightarrow>
        position_number (deferred_positions d) q \<in> set ns \<longrightarrow> deferred_node_stale S d q" using Cons.prems(7) by simp
    have fm': "\<forall>q. position_number (deferred_positions d) q \<notin> set ns \<longrightarrow> deferred_node_formed d q"
    proof (intro allI impI)
      fix q assume nq: "position_number (deferred_positions d) q \<notin> set ns"
      show "deferred_node_formed d q"
      proof (cases "position_number (deferred_positions d) q = n")
        case True
        show ?thesis
        proof (cases "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q")
          case None
          then show ?thesis unfolding deferred_node_formed_def by simp
        next
          case (Some hn)
          then have "deferred_node_stale S d q" using Cons.prems(7) True by simp
          then have "RBT.lookup (deferred_records d) n \<noteq> None" using Some True unfolding deferred_node_stale_def by auto
          then show ?thesis using None by simp
        qed
      next
        case False
        then show ?thesis using Cons.prems(8) nq by simp
      qed
    qed
    have IH: "deferred_formed \<kappa> P (fold (deferred_update \<sigma> D) ns d) \<and>
        deferred_project (fold (deferred_update \<sigma> D) ns d) = deferred_project d \<and>
        deferred_store (fold (deferred_update \<sigma> D) ns d) = deferred_store d"
      using Cons.IH[OF Cons.prems(1-5) nsd st' fm'] .
    show ?thesis using IH u by simp
  next
    case (Some z)
    obtain q0 K where z: "z = (q0, K)" by (cases z)
    have rec: "RBT.lookup (deferred_records d) n = Some (q0, K)" using Some z by simp
    have nq0: "n \<noteq> 0 \<and> n = position_number (deferred_positions d) q0 \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner d))) q0 \<noteq> None"
      using Cons.prems(1) rec unfolding deferred_parts_formed_def by blast
    have stale0: "deferred_node_stale S d q0" using Cons.prems(7) nq0 by simp
    note U = deferred_update[OF Cons.prems(1-5) rec stale0]
    let ?d' = "deferred_update \<sigma> D n d"
    have numE: "deferred_numbered ?d' = deferred_numbered d" by (rule deferred_numbered_cong[OF U(7) U(8)])
    have S': "binding_store_formed (search_table (deferred_inner ?d')) S"
      using binding_store_formed_extended[OF Cons.prems(2) tf] U(9) by (simp add: table_extends_def)
    have ready': "unifier_ready (search_table (deferred_inner ?d')) (binding_map S) \<sigma> D"
      by (rule unifier_ready_extends[OF Cons.prems(3) tf U(9)])
    have st': "deferred_store ?d' = store_bind S \<sigma> D" using U(6) Cons.prems(4) by simp
    have num': "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered ?d' b"
      using Cons.prems(5) numE by simp
    have ne: "q \<noteq> q0" if "position_number (deferred_positions d) q \<in> set ns" for q
      using that nq0 nn by auto
    have stale': "\<forall>q. RBT.lookup (shared_nodes (search_state (deferred_inner ?d'))) q \<noteq> None \<longrightarrow>
        position_number (deferred_positions ?d') q \<in> set ns \<longrightarrow> deferred_node_stale S ?d' q"
    proof (intro allI impI)
      fix q assume a: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d'))) q \<noteq> None"
        and m: "position_number (deferred_positions ?d') q \<in> set ns"
      have m': "position_number (deferred_positions d) q \<in> set ns" using m U(7) by simp
      have a': "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
        using a deferred_update_nodes[OF rec ne[OF m']] by simp
      have "deferred_node_stale S d q" using Cons.prems(7) a' m' by simp
      then show "deferred_node_stale S ?d' q" by (rule U(4)[OF ne[OF m']])
    qed
    have formed': "\<forall>q. position_number (deferred_positions ?d') q \<notin> set ns \<longrightarrow> deferred_node_formed ?d' q"
    proof (intro allI impI)
      fix q assume m: "position_number (deferred_positions ?d') q \<notin> set ns"
      have m': "position_number (deferred_positions d) q \<notin> set ns" using m U(7) by simp
      show "deferred_node_formed ?d' q"
      proof (cases "q = q0")
        case True
        then show ?thesis using U(2) by simp
      next
        case False
        have "position_number (deferred_positions d) q \<noteq> n"
        proof
          assume "position_number (deferred_positions d) q = n"
          then have "position_number (deferred_positions d) q0 = position_number (deferred_positions d) q" using nq0 by simp
          then have "q0 = q" using position_number_inj[OF T] nq0 by metis
          then show False using False by simp
        qed
        then have "deferred_node_formed d q" using Cons.prems(8) m' by simp
        then show ?thesis by (rule U(3)[OF False])
      qed
    qed
    have IH: "deferred_formed \<kappa> P (fold (deferred_update \<sigma> D) ns ?d') \<and>
        deferred_project (fold (deferred_update \<sigma> D) ns ?d') = deferred_project ?d' \<and>
        deferred_store (fold (deferred_update \<sigma> D) ns ?d') = deferred_store ?d'"
      using Cons.IH[OF U(1) S' ready' st' num' nsd stale' formed'] .
    show ?thesis using IH U(5) U(6) by simp
  qed
qed

subsection \<open>The deferred bind\<close>

text \<open>
  The unifier is collapsed as @{const search_bind} collapses it; the names of its variables are numbered; the goals
  are substituted alone; the store records it; and each node the holder index finds for its domain is updated. Its
  projection is the shared bind's (@{thm [source] search_bind}), and its formation is kept.
\<close>

lemma keyed_collapse_bindings_keys: "map fst (fst (keyed_collapse_bindings s x)) = map fst s"
  by (induction s x rule: keyed_collapse_bindings.induct) (auto split: prod.splits)

definition deferred_bound_names ::
    "(('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow> 'a list" where
  "deferred_bound_names s = concat (map (\<lambda>z. snd (fst z) # map snd (shared_variable_list (snd z))) s)"

definition deferred_bind :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_bind P s d = (case keyed_collapse_bindings s (shared_sharing (search_state (deferred_inner d))) of (s', x) \<Rightarrow>
    let D = shared_binding_domain s';
      d1 = d\<lparr>deferred_names := deferred_number_names (deferred_bound_names s') (deferred_names d)\<rparr>;
      d2 = (d1\<lparr>deferred_tree := binding_tree_bind (deferred_key d1) (deferred_tree d1) s'\<rparr>)\<lparr>deferred_inner :=
        search_goal_substitute P (shared_binding_substitution s') D (search_share x (deferred_inner d1))\<rparr>
    in fold (deferred_update (shared_binding_substitution s') D)
      (sorted_list_of_fset (ffUnion (fimage (\<lambda>a. tree_bucket (deferred_holders d2) (deferred_key d2 a)) D))) d2)"

lemma derivation_resolve_extends:
  assumes S: "binding_store_formed T S" and tf: "table_formed T" and nd: "shared_derivation_formed T nd"
    and ext: "table_extends T T'"
  shows "shared_derivation_project T' (derivation_resolve S nd) = shared_derivation_project T (derivation_resolve S nd)"
proof -
  have e: "shared_pattern_project T' (binding_resolve S p) = shared_pattern_project T (binding_resolve S p)"
    if "shared_pattern_formed T p" for p
    using shared_pattern_extends(2)[OF tf binding_resolve_formed[OF S that] ext] .
  have c: "shared_pattern_formed T (shared_derivation_call nd)" using nd by (simp add: shared_derivation_formed_def)
  have B: "fimage (\<lambda>z. (fst z, shared_pattern_project T' (binding_resolve S (snd z)))) (shared_derivation_bindings nd) =
      fimage (\<lambda>z. (fst z, shared_pattern_project T (binding_resolve S (snd z)))) (shared_derivation_bindings nd)"
    by (rule fset.map_cong0) (use e nd in \<open>simp add: shared_derivation_formed_def\<close>)
  show ?thesis using e[OF c] B by (simp add: shared_derivation_project_def fset.map_comp comp_def)
qed

lemma derivation_resolve_bind:
  assumes S: "binding_store_formed T S" and ready: "unifier_ready T (binding_map S) \<sigma> D"
    and nd: "shared_derivation_formed T nd"
  shows "resolution_node_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_derivation_project T (derivation_resolve S nd)) =
    shared_derivation_project T (derivation_resolve (store_bind S \<sigma> D) nd)"
proof -
  let ?\<tau> = "\<lambda>a. shared_pattern_project T (\<sigma> a)"
  have out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a" using ready unfolding unifier_ready_def by blast
  have p: "finite_pattern_substitute ?\<tau> (shared_pattern_project T (binding_resolve S p)) =
      shared_pattern_project T (binding_resolve (store_bind S \<sigma> D) p)" if "shared_pattern_formed T p" for p
    using shared_substitute_project[OF binding_resolve_formed[OF S that] out] store_bind_resolve[OF S ready that] by simp
  have c: "shared_pattern_formed T (shared_derivation_call nd)" using nd by (simp add: shared_derivation_formed_def)
  have B: "fimage (\<lambda>z. (fst z, finite_pattern_substitute ?\<tau> (shared_pattern_project T (binding_resolve S (snd z)))))
      (shared_derivation_bindings nd) =
    fimage (\<lambda>z. (fst z, shared_pattern_project T (binding_resolve (store_bind S \<sigma> D) (snd z)))) (shared_derivation_bindings nd)"
    by (rule fset.map_cong0) (use p nd in \<open>simp add: shared_derivation_formed_def\<close>)
  show ?thesis using p[OF c] B by (simp add: shared_derivation_project_def fset.map_comp comp_def case_prod_beta)
qed

theorem deferred_bind:
  assumes d: "deferred_formed \<kappa> P d" and sf: "shared_bindings_formed (search_table (deferred_inner d)) s"
    and dom: "\<forall>a. a \<in> set (map fst s) \<longrightarrow> binding_map (deferred_store d) a = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst a)) \<noteq> None"
    and img: "\<forall>a b. a \<in> set (map fst s) \<longrightarrow>
      b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner d)) s) a) \<longrightarrow>
      b \<notin> set (map fst s) \<and> binding_map (deferred_store d) b = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst b)) \<noteq> None"
  shows "deferred_formed \<kappa> P (deferred_bind P s d)"
    and "deferred_project (deferred_bind P s d) = resolution_state_substitute
      (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner d)) s)) (deferred_project d)"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r" let ?S = "deferred_store d"
  let ?x0 = "shared_sharing ?s" let ?\<tau>0 = "finite_binding_substitution (shared_bindings_project ?T s)"
  have parts: "deferred_parts_formed \<kappa> P d" and nfs: "\<And>q. deferred_node_formed d q"
    using d unfolding deferred_formed_def by blast+
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" and N: "positions_numbered (deferred_positions d)"
    and S: "binding_store_formed ?T ?S" using parts unfolding deferred_parts_formed_def by blast+
  have st: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have x0: "share_state_formed ?x0" and tf: "table_formed ?T" using shared_entries_formed(3,4)[OF st] .
  obtain s' x where kc: "keyed_collapse_bindings s ?x0 = (s', x)" by (cases "keyed_collapse_bindings s ?x0")
  have C: "share_state_formed x \<and> table_extends ?T (share_state_table x) \<and> shared_bindings_formed (share_state_table x) s' \<and>
      shared_bindings_project (share_state_table x) s' = shared_bindings_project ?T s \<and> (\<forall>z\<in>set s'. shared_collapsed (snd z))"
    using keyed_collapse_bindings[OF x0 sf] kc by simp
  let ?Tx = "share_state_table x" let ?\<sigma> = "shared_binding_substitution s'" let ?D = "shared_binding_domain s'"
  have xf: "share_state_formed x" and extx: "table_extends ?T ?Tx" and sf': "shared_bindings_formed ?Tx s'"
    and pe: "shared_bindings_project ?Tx s' = shared_bindings_project ?T s" and cs: "\<forall>z\<in>set s'. shared_collapsed (snd z)"
    using C by simp_all
  have tfx: "table_formed ?Tx" using xf by (simp add: share_state_formed_def)
  have keys: "map fst s' = map fst s" using keyed_collapse_bindings_keys[of s ?x0] kc by simp
  have Dm: "a |\<in>| ?D \<longleftrightarrow> a \<in> set (map fst s)" for a
    using keys by (simp add: shared_binding_domain_def fset_of_list_elem fset_of_list.rep_eq)
  have \<sigma>f: "\<And>a. shared_pattern_formed ?Tx (?\<sigma> a)" by (rule shared_binding_substitution_formed[OF sf'])
  have \<sigma>c: "\<And>a. shared_collapsed (?\<sigma> a)"
  proof -
    fix a show "shared_collapsed (?\<sigma> a)"
    proof (cases "map_of s' a")
      case (Some p)
      then have "(a, p) \<in> set s'" by (rule map_of_SomeD)
      then show ?thesis using cs Some by (force simp: shared_binding_substitution_def)
    qed (simp add: shared_binding_substitution_def)
  qed
  have out: "\<And>a. a |\<notin>| ?D \<Longrightarrow> ?\<sigma> a = Shared_Variable a" by (rule shared_binding_substitution_outside)
  have \<tau>: "shared_pattern_project ?Tx (?\<sigma> a) = ?\<tau>0 a" for a
    using shared_binding_substitution_project[of ?Tx s' a] pe by simp
  have \<sigma>v: "shared_pattern_variables (?\<sigma> a) = finite_pattern_variables (?\<tau>0 a)" for a
    using shared_pattern_variables_project[OF \<sigma>f[of a]] \<tau>[of a] by simp
  have domS: "\<forall>a. a |\<in>| ?D \<longrightarrow> binding_map ?S a = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst a)) \<noteq> None"
    using dom Dm by simp
  have imgD: "\<forall>a b. a |\<in>| ?D \<longrightarrow> b |\<in>| shared_pattern_variables (?\<sigma> a) \<longrightarrow>
      b |\<notin>| ?D \<and> binding_map ?S b = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst b)) \<noteq> None"
    using img Dm \<sigma>v by simp
  let ?L = "deferred_bound_names s'"
  let ?d1 = "d\<lparr>deferred_names := deferred_number_names ?L (deferred_names d)\<rparr>"
  have re: "deferred_renumbered d ?d1"
    unfolding deferred_renumbered_def using deferred_number_names(1)[of ?L "deferred_names d"]
    by (auto intro!: exI[where x = "[]"])
  have parts1: "deferred_parts_formed \<kappa> P ?d1" by (rule deferred_renumbered_parts[OF re parts])
  have nf1: "deferred_node_formed ?d1 q" for q by (rule deferred_renumbered_node[OF re parts nfs])
  have st1: "deferred_store ?d1 = ?S" by (rule deferred_renumbered_store[OF re parts])
  have N1: "positions_numbered (deferred_positions ?d1)" using N by simp
  have posnum: "position_number (deferred_positions d) (fst (fst b)) \<noteq> 0"
    if pb: "RBT.lookup (shared_nodes ?s) (fst (fst b)) \<noteq> None" for b
  proof -
    obtain hn where "RBT.lookup (shared_nodes ?s) (fst (fst b)) = Some hn" using pb by blast
    then show ?thesis by (rule deferred_node_formedD(1)[OF nfs])
  qed
  have names: "set (deferred_names ?d1) = set (deferred_names d) \<union> set ?L" using deferred_number_names(2) by simp
  have numL: "deferred_numbered ?d1 b" if "snd b \<in> set ?L" and "RBT.lookup (shared_nodes ?s) (fst (fst b)) \<noteq> None" for b
  proof -
    have n1: "deferred_names ?d1 = deferred_number_names ?L (deferred_names d)" by simp
    have "snd b \<in> set (deferred_names ?d1)" unfolding n1 deferred_number_names(2) using that(1) by (rule UnI2)
    then have "name_number (deferred_names ?d1) (snd b) \<noteq> 0" by (rule iffD2[OF name_number_nonzero])
    moreover have "position_number (deferred_positions ?d1) (fst (fst b)) \<noteq> 0" using posnum[OF that(2)] by simp
    ultimately show ?thesis unfolding deferred_numbered_def by blast
  qed
  have pair: "\<exists>p. map_of s' a = Some p \<and> (a, p) \<in> set s' \<and> ?\<sigma> a = p" if "a |\<in>| ?D" for a
  proof -
    obtain p where "map_of s' a = Some p" using \<open>a |\<in>| ?D\<close>
      by (cases "map_of s' a") (auto simp: shared_binding_domain_def fset_of_list_elem fset_of_list.rep_eq map_of_eq_None_iff)
    then show ?thesis using map_of_SomeD by (auto simp: shared_binding_substitution_def)
  qed
  have numD: "deferred_numbered ?d1 a" if a: "a |\<in>| ?D" for a
  proof -
    obtain p where "(a, p) \<in> set s'" using pair[OF a] by blast
    then have "snd a \<in> set ?L" by (force simp: deferred_bound_names_def)
    then show ?thesis using numL domS a by blast
  qed
  have num\<sigma>: "deferred_numbered ?d1 b" if a: "a |\<in>| ?D" and b: "b |\<in>| shared_pattern_variables (?\<sigma> a)" for a b
  proof -
    obtain p where p: "(a, p) \<in> set s'" "?\<sigma> a = p" using pair[OF a] by blast
    have pf: "shared_pattern_formed ?Tx p" using sf' p(1) by (auto simp: shared_bindings_formed_def)
    have "b \<in> set (shared_variable_list p)" using b p(2) shared_variable_list[OF pf] by simp
    then have "snd b \<in> set ?L" using p(1) by (force simp: deferred_bound_names_def)
    then show ?thesis using numL imgD a b by blast
  qed
  let ?K1 = "binding_tree_bind (deferred_key ?d1) (deferred_tree d) s'"
  let ?r2 = "search_goal_substitute P ?\<sigma> ?D (search_share x ?r)"
  let ?d2 = "(?d1\<lparr>deferred_tree := ?K1\<rparr>)\<lparr>deferred_inner := ?r2\<rparr>"
  let ?ns = "sorted_list_of_fset (ffUnion (fimage (\<lambda>a. tree_bucket (deferred_holders ?d2) (deferred_key ?d2 a)) ?D))"
  have eq: "deferred_bind P s d = fold (deferred_update ?\<sigma> ?D) ?ns ?d2" by (simp add: deferred_bind_def kc Let_def)
  have st2: "deferred_store ?d2 = store_bind ?S ?\<sigma> ?D"
  proof -
    have "deferred_store (?d1\<lparr>deferred_tree := binding_tree_bind (deferred_key ?d1) (deferred_tree ?d1) s'\<rparr>) =
        store_bind (deferred_store ?d1) ?\<sigma> ?D"
      by (rule deferred_store_bind[OF N1]) (metis Dm keys numD)
    then show ?thesis using st1 by simp
  qed
  have r1: "search_formed \<kappa> P (search_share x ?r)" using search_share(1)[OF r xf extx] .
  have tbl1: "search_table (search_share x ?r) = ?Tx" using search_share(3)[OF r xf extx] .
  have K1: "search_classes_formed (search_share x ?r)" by (rule search_share_classes[OF r xf extx K])
  have \<sigma>f1: "\<And>a. shared_pattern_formed (search_table (search_share x ?r)) (?\<sigma> a)" using \<sigma>f tbl1 by simp
  have r2: "search_formed \<kappa> P ?r2" by (rule search_goal_substitute(1)[OF r1 K1 \<sigma>f1 \<sigma>c]) (rule out)
  have K2: "search_classes_formed ?r2" by (rule search_goal_substitute(2)[OF r1 K1 \<sigma>f1 \<sigma>c]) (rule out)
  have ext2: "table_extends ?Tx (search_table ?r2)"
  proof -
    have "table_extends (search_table (search_share x ?r)) (search_table ?r2)"
      by (rule search_goal_substitute(3)[OF r1 K1 \<sigma>f1 \<sigma>c]) (rule out)
    then show ?thesis using tbl1 by simp
  qed
  let ?T2 = "search_table ?r2"
  have nodes2: "RBT.lookup (shared_nodes (search_state ?r2)) p = RBT.lookup (shared_nodes ?s) p" for p
  proof -
    have "RBT.lookup (shared_nodes (search_state ?r2)) p = RBT.lookup (shared_nodes (search_state (search_share x ?r))) p"
      by (rule search_goal_substitute(4)[OF r1 K1 \<sigma>f1 \<sigma>c]) (rule out)
    then show ?thesis using search_share(5)[OF r xf extx] by simp
  qed
  have proj2: "search_project ?r2 = Resolution_State (fimage (resolution_goal_substitute ?\<tau>0) (resolution_pending (search_project ?r)))
      (resolution_nodes (search_project ?r)) (resolution_witnesses (search_project ?r))"
  proof -
    have "search_project ?r2 = Resolution_State
        (fimage (resolution_goal_substitute (\<lambda>a. shared_pattern_project (search_table (search_share x ?r)) (?\<sigma> a)))
          (resolution_pending (search_project (search_share x ?r))))
        (resolution_nodes (search_project (search_share x ?r))) (resolution_witnesses (search_project (search_share x ?r)))"
      by (rule search_goal_substitute_project[OF r1 \<sigma>f1 \<sigma>c]) (rule out)
    moreover have "(\<lambda>a. shared_pattern_project (search_table (search_share x ?r)) (?\<sigma> a)) = ?\<tau>0"
      using \<tau> tbl1 by (simp add: fun_eq_iff)
    ultimately show ?thesis using search_share(2)[OF r xf extx] by simp
  qed
  have T2e: "table_extends ?T ?T2" using table_extends_trans[OF extx ext2] .
  have S2: "binding_store_formed ?T2 ?S" using binding_store_formed_extended[OF S tf] T2e by (simp add: table_extends_def)
  have \<sigma>f2: "\<And>a. shared_pattern_formed ?T2 (?\<sigma> a)" using shared_pattern_extends(1)[OF tfx \<sigma>f ext2] .
  have \<tau>2: "(\<lambda>a. shared_pattern_project ?T2 (?\<sigma> a)) = ?\<tau>0"
    using shared_pattern_extends(2)[OF tfx \<sigma>f ext2] \<tau> by (simp add: fun_eq_iff)
  have ready2: "unifier_ready ?T2 (binding_map ?S) ?\<sigma> ?D"
    unfolding unifier_ready_def using out domS \<sigma>f2 \<sigma>c imgD by blast
  have S'f: "binding_store_formed ?T2 (store_bind ?S ?\<sigma> ?D)" by (rule store_bind_formed[OF S2 ready2])
  have parts2: "deferred_parts_formed \<kappa> P ?d2"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner ?d2)" using r2 by simp
    show "search_classes_formed (deferred_inner ?d2)" using K2 by simp
    show "positions_numbered (deferred_positions ?d2)" using N by simp
    show "binding_store_formed (search_table (deferred_inner ?d2)) (deferred_store ?d2)" using S'f st2 by simp
    show "\<forall>k v. RBT.lookup (snd (deferred_tree ?d2)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered ?d2 y \<and> deferred_key ?d2 y = k)"
    proof (intro allI impI)
      fix k v assume l: "RBT.lookup (snd (deferred_tree ?d2)) k = Some v"
      show "\<exists>y. deferred_numbered ?d2 y \<and> deferred_key ?d2 y = k"
      proof (cases "\<exists>b\<in>set (map fst s'). deferred_key ?d1 b = k")
        case True
        then obtain b where b: "b \<in> set (map fst s')" "deferred_key ?d1 b = k" by blast
        have "b |\<in>| ?D" using b(1) keys Dm by simp
        then show ?thesis using numD b(2) by (intro exI[of _ b]) simp
      next
        case False
        have "RBT.lookup (snd ?K1) k = RBT.lookup (snd (deferred_tree d)) k"
          unfolding binding_tree_bind_def snd_conv by (rule binding_tree_fold_other) (use False in auto)
        then have "RBT.lookup (snd (deferred_tree d)) k = Some v" using l by simp
        then have l1: "RBT.lookup (snd (deferred_tree ?d1)) k = Some v" by simp
        have tk1: "\<And>k v. RBT.lookup (snd (deferred_tree ?d1)) k = Some v \<Longrightarrow>
            \<exists>y. deferred_numbered ?d1 y \<and> deferred_key ?d1 y = k"
          using parts1 unfolding deferred_parts_formed_def by blast
        obtain y where "deferred_numbered ?d1 y" "deferred_key ?d1 y = k" using tk1[OF l1] by blast
        then show ?thesis by (intro exI[of _ y]) simp
      qed
    qed
    show "\<forall>y. binding_map (deferred_store ?d2) y \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None"
    proof (intro allI impI)
      fix y assume "binding_map (deferred_store ?d2) y \<noteq> None"
      then have "y |\<in>| ?D \<or> binding_map ?S y \<noteq> None" using st2 by (auto simp: store_bind_def bound_map_def split: if_splits)
      moreover have "binding_map ?S y \<noteq> None \<Longrightarrow> RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      ultimately have "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" using domS by blast
      then show "RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None" using nodes2 by simp
    qed
    show "\<forall>q h y. RBT.lookup (shared_goals (search_state (deferred_inner ?d2))) q = Some h \<longrightarrow>
        y |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store ?d2) y = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None"
    proof (intro allI impI)
      fix q h y assume gq: "RBT.lookup (shared_goals (search_state (deferred_inner ?d2))) q = Some h"
        and yv: "y |\<in>| shared_goal_variables (shared_entry_goal h)"
      let ?A = "{z. binding_map (store_bind ?S ?\<sigma> ?D) z = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst z)) \<noteq> None}"
      have gq2: "RBT.lookup (shared_goals (search_state ?r2)) q = Some h" using gq by simp
      have "shared_goal_project ?T2 (shared_entry_goal h) |\<in>| resolution_pending (search_project ?r2)"
        unfolding shared_state_project_member(1) using gq2 by blast
      then obtain g0 where g0: "g0 |\<in>| resolution_pending (search_project ?r)"
        and ge: "shared_goal_project ?T2 (shared_entry_goal h) = resolution_goal_substitute ?\<tau>0 g0"
        unfolding proj2 by auto
      obtain q0 h0 where h0: "RBT.lookup (shared_goals ?s) q0 = Some h0"
        and g0e: "shared_goal_project ?T (shared_entry_goal h0) = g0"
        using g0 unfolding shared_state_project_member(1) by blast
      have old: "binding_map ?S z = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst z)) \<noteq> None"
        if "z |\<in>| resolution_goal_variables g0" for z
      proof -
        have "z |\<in>| shared_goal_variables (shared_entry_goal h0)"
          using that g0e goal_entry_variables[OF shared_entries_formed(1)[OF st h0]] by simp
        then show ?thesis using parts h0 unfolding deferred_parts_formed_def by blast
      qed
      have within: "fset (resolution_goal_variables (resolution_goal_substitute ?\<tau>0 g0)) \<subseteq> ?A"
      proof (rule resolution_goal_substitute_within)
        fix z assume z: "z |\<in>| resolution_goal_variables g0"
        show "fset (finite_pattern_variables (?\<tau>0 z)) \<subseteq> ?A"
        proof (cases "z |\<in>| ?D")
          case True
          show ?thesis
          proof
            fix b assume b: "b \<in> fset (finite_pattern_variables (?\<tau>0 z))"
            then have bv: "b |\<in>| shared_pattern_variables (?\<sigma> z)" using \<sigma>v[of z] by simp
            have "b |\<notin>| ?D \<and> binding_map ?S b = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst b)) \<noteq> None"
              using imgD True bv by blast
            then show "b \<in> ?A" by (simp add: store_bind_def bound_map_def)
          qed
        next
          case False
          have "?\<tau>0 z = Finite_Variable z" using \<tau>[of z] out[OF False] by simp
          then show ?thesis using old[OF z] False by (simp add: store_bind_def bound_map_def)
        qed
      qed
      have hf2: "goal_entry_formed P ?T2 q h" using shared_entries_formed(1)[OF search_formedD(1)[OF r2] gq2] .
      have "y |\<in>| resolution_goal_variables (resolution_goal_substitute ?\<tau>0 g0)"
        using yv goal_entry_variables[OF hf2] ge by simp
      then have "y \<in> ?A" using within by blast
      then show "binding_map (deferred_store ?d2) y = None \<and>
          RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None"
        using st2 nodes2 by simp
    qed
    show "\<forall>n q K. RBT.lookup (deferred_records ?d2) n = Some (q, K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions ?d2) q \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) q \<noteq> None"
      using parts nodes2 unfolding deferred_parts_formed_def by simp
  qed
  have holders: "position_number (deferred_positions d) q \<in> set ?ns"
    if at: "RBT.lookup (shared_nodes ?s) q = Some hn" and a: "a |\<in>| shared_pattern_variables (deferred_call d hn)"
      and aD: "a |\<in>| ?D" for q hn a
  proof -
    have at1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q = Some hn" using at by simp
    have "position_number (deferred_positions ?d1) q |\<in>| tree_bucket (deferred_holders ?d1) (deferred_key ?d1 a)"
      using deferred_node_formedD(4)[OF nf1 at1] a st1 by simp
    then show ?thesis using aD by (force simp: ffUnion.rep_eq fimage.rep_eq)
  qed
  have stale2: "\<forall>q. RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) q \<noteq> None \<longrightarrow>
      position_number (deferred_positions ?d2) q \<in> set ?ns \<longrightarrow> deferred_node_stale ?S ?d2 q"
  proof (intro allI impI)
    fix q
    show "deferred_node_stale ?S ?d2 q" unfolding deferred_node_stale_def
    proof (intro allI impI)
      fix hn assume at2: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) q = Some hn"
      have at1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q = Some hn" using at2 nodes2 by simp
      note F = deferred_node_formedD[OF nf1 at1]
      show "position_number (deferred_positions ?d2) q \<noteq> 0 \<and>
        (\<exists>K. RBT.lookup (deferred_records ?d2) (position_number (deferred_positions ?d2) q) = Some (q, K) \<and>
          set (RBT.keys K) = deferred_key ?d2 ` fset (shared_pattern_variables (binding_resolve ?S (shared_derivation_call (shared_entry_node hn))))) \<and>
        fBall (shared_pattern_variables (binding_resolve ?S (shared_derivation_call (shared_entry_node hn)))) (deferred_numbered ?d2)"
        using F st1 by simp
    qed
  qed
  have formed2: "\<forall>q. position_number (deferred_positions ?d2) q \<notin> set ?ns \<longrightarrow> deferred_node_formed ?d2 q"
  proof (intro allI impI)
    fix q assume m: "position_number (deferred_positions ?d2) q \<notin> set ?ns"
    show "deferred_node_formed ?d2 q" unfolding deferred_node_formed_def
    proof (intro allI impI)
      fix hn assume at2: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) q = Some hn"
      have at: "RBT.lookup (shared_nodes ?s) q = Some hn" using at2 nodes2 by simp
      have at1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q = Some hn" using at by simp
      note F = deferred_node_formedD[OF nf1 at1]
      let ?c = "shared_derivation_call (shared_entry_node hn)"
      have cf: "shared_pattern_formed ?T2 ?c"
        using shared_entries_formed(2)[OF search_formedD(1)[OF r2]] at2
        by (simp add: node_entry_formed_def shared_derivation_formed_def)
      have disj: "shared_pattern_variables (binding_resolve ?S ?c) |\<inter>| ?D = {||}"
      proof -
        have False if a: "a |\<in>| shared_pattern_variables (binding_resolve ?S ?c)" "a |\<in>| ?D" for a
          using holders[OF at a(1) a(2)] m by simp
        then show ?thesis by blast
      qed
      have call2: "deferred_call ?d2 hn = binding_resolve ?S ?c"
      proof -
        have "deferred_call ?d2 hn = shared_substitute ?\<sigma> ?D (binding_resolve ?S ?c)"
          using store_bind_resolve[OF S2 ready2 cf] st2 by simp
        also have "\<dots> = binding_resolve ?S ?c" by (rule shared_substitute_unbound) (use out disj in auto)
        finally show ?thesis .
      qed
      show "position_number (deferred_positions ?d2) q \<noteq> 0 \<and>
        (\<exists>K. RBT.lookup (deferred_records ?d2) (position_number (deferred_positions ?d2) q) = Some (q, K) \<and>
          set (RBT.keys K) = deferred_key ?d2 ` fset (shared_pattern_variables (deferred_call ?d2 hn))) \<and>
        fBall (shared_pattern_variables (deferred_call ?d2 hn)) (deferred_numbered ?d2) \<and>
        fBall (shared_pattern_variables (deferred_call ?d2 hn))
          (\<lambda>y. position_number (deferred_positions ?d2) q |\<in>| tree_bucket (deferred_holders ?d2) (deferred_key ?d2 y)) \<and>
        (shared_pattern_variables (deferred_call ?d2 hn) = {||} \<longrightarrow>
          shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||})"
        unfolding call2 using F st1 by simp
    qed
  qed
  have S2': "binding_store_formed (search_table (deferred_inner ?d2)) ?S" using S2 by simp
  have ready2': "unifier_ready (search_table (deferred_inner ?d2)) (binding_map ?S) ?\<sigma> ?D" using ready2 by simp
  have num2: "\<forall>a b. a |\<in>| ?D \<longrightarrow> b |\<in>| shared_pattern_variables (?\<sigma> a) \<longrightarrow> deferred_numbered ?d2 b"
    using num\<sigma> by simp
  have nsd: "distinct ?ns" by simp
  note FOLD = deferred_update_fold[OF parts2 S2' ready2' st2 num2 nsd stale2 formed2]
  show "deferred_formed \<kappa> P (deferred_bind P s d)" using FOLD eq by simp
  let ?\<sigma>2 = "deferred_substitution ?d2" and ?\<sigma>1 = "deferred_substitution d"
  have \<sigma>2: "?\<sigma>2 = (\<lambda>y. shared_pattern_project ?T2 (binding_substitution (store_bind ?S ?\<sigma> ?D) y))"
    using st2 by (simp add: fun_eq_iff deferred_substitution_def)
  have gfix: "resolution_goal_substitute ?\<sigma>2 g = g" if gm: "g |\<in>| resolution_pending (search_project ?r2)" for g
  proof (rule resolution_goal_substitute_outside)
    fix y assume y: "y |\<in>| resolution_goal_variables g"
    obtain q h where gq: "RBT.lookup (shared_goals (search_state ?r2)) q = Some h"
      and ge: "shared_goal_project ?T2 (shared_entry_goal h) = g" using gm unfolding shared_state_project_member(1) by blast
    have yv: "y |\<in>| shared_goal_variables (shared_entry_goal h)"
      using y ge goal_entry_variables[OF shared_entries_formed(1)[OF search_formedD(1)[OF r2] gq]] by simp
    have gc: "\<And>q h y. RBT.lookup (shared_goals (search_state (deferred_inner ?d2))) q = Some h \<Longrightarrow>
        y |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow> binding_map (deferred_store ?d2) y = None"
      using parts2 unfolding deferred_parts_formed_def by blast
    have "binding_map (deferred_store ?d2) y = None" using gc[of q h y] gq yv by simp
    then show "?\<sigma>2 y = Finite_Variable y"
      using binding_resolve_unbound[of "Shared_Variable y" "deferred_store ?d2"]
      by (simp add: deferred_substitution_def binding_substitution_def)
  qed
  have nfix: "resolution_node_substitute ?\<sigma>2 nd0 = resolution_node_substitute ?\<tau>0 (resolution_node_substitute ?\<sigma>1 nd0)"
    if nm: "nd0 |\<in>| resolution_nodes (search_project ?r)" for nd0
  proof -
    obtain q hn where at: "RBT.lookup (shared_nodes ?s) q = Some hn"
      and e0: "shared_derivation_project ?T (shared_entry_node hn) = nd0" using nm unfolding shared_state_project_member(2) by blast
    let ?nd = "shared_entry_node hn"
    have ndf: "shared_derivation_formed ?T ?nd" using shared_entries_formed(2)[OF st at] by (simp add: node_entry_formed_def)
    have ndf2: "shared_derivation_formed ?T2 ?nd" and pe2: "shared_derivation_project ?T2 ?nd = shared_derivation_project ?T ?nd"
      using shared_derivation_extends[OF tf ndf T2e] by simp_all
    have l: "resolution_node_substitute ?\<sigma>2 nd0 = shared_derivation_project ?T2 (derivation_resolve (store_bind ?S ?\<sigma> ?D) ?nd)"
      using derivation_resolve_project[OF S'f ndf2] e0 pe2 \<sigma>2 by simp
    have r1: "resolution_node_substitute ?\<sigma>1 nd0 = shared_derivation_project ?T2 (derivation_resolve ?S ?nd)"
      using derivation_resolve_project[OF S ndf] e0 derivation_resolve_extends[OF S tf ndf T2e]
      by (simp add: deferred_substitution_def[abs_def])
    show ?thesis using l r1 derivation_resolve_bind[OF S2 ready2 ndf2] \<tau>2 by simp
  qed
  have "deferred_project (deferred_bind P s d) = deferred_project ?d2" using FOLD eq by simp
  also have "\<dots> = resolution_state_substitute ?\<sigma>2 (search_project ?r2)" by (simp add: deferred_project_def)
  also have "\<dots> = Resolution_State (fimage (resolution_goal_substitute ?\<tau>0) (resolution_pending (search_project ?r)))
      (fimage (\<lambda>nd. resolution_node_substitute ?\<tau>0 (resolution_node_substitute ?\<sigma>1 nd)) (resolution_nodes (search_project ?r)))
      (resolution_witnesses (search_project ?r))"
  proof -
    have G: "fimage (resolution_goal_substitute ?\<sigma>2) (resolution_pending (search_project ?r2)) =
        resolution_pending (search_project ?r2)" by (rule fimage_fixed) (rule gfix)
    have Nn: "fimage (resolution_node_substitute ?\<sigma>2) (resolution_nodes (search_project ?r)) =
        fimage (\<lambda>nd. resolution_node_substitute ?\<tau>0 (resolution_node_substitute ?\<sigma>1 nd)) (resolution_nodes (search_project ?r))"
      by (rule fset.map_cong0) (rule nfix)
    show ?thesis using G Nn proj2 by (simp add: resolution_state_substitute_def)
  qed
  also have "\<dots> = resolution_state_substitute ?\<tau>0 (deferred_project d)"
    using deferred_pending[OF d]
    by (simp add: deferred_project_def resolution_state_substitute_def fset.map_comp comp_def)
  finally show "deferred_project (deferred_bind P s d) = resolution_state_substitute ?\<tau>0 (deferred_project d)" .
qed

subsection \<open>The deferred place\<close>

text \<open>
  A clause is placed as the shared search places it (@{const search_call_place}); the node it puts at the goal's
  position is numbered there and its record made. Every variable of the placed node and of the goals it places stands
  at that position, where no node stood before, so the store binds none of them.
\<close>

lemma search_place_goals_nodes:
  "RBT.lookup (shared_nodes (search_state (search_place_goals P rows r))) p = RBT.lookup (shared_nodes (search_state r)) p"
  unfolding search_place_goals_def
  by (induction rows arbitrary: r) (simp_all add: search_put_goal_def shared_put_goal_def)

lemma search_call_place_nodes:
  "p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (search_call_place P r q e c S))) p =
    RBT.lookup (shared_nodes (search_state r)) p"
  by (simp add: search_call_place_def Let_def search_put_node_def shared_put_node_def search_place_goals_nodes
      search_reshare_def shared_reshare_def search_remove_goal_def shared_remove_goal_def)

lemma finite_clause_goals_positioned:
  "g |\<in>| finite_clause_goals q e c S \<Longrightarrow> x |\<in>| resolution_goal_variables g \<Longrightarrow> fst (fst x) = q"
  by (auto simp: finite_clause_goals_def finite_rename_apart_variables finite_rename_material_def
      finite_material_variables_def finite_pattern_variables_map)

lemma finite_clause_node_positioned:
  "x |\<in>| finite_pattern_variables (resolution_node_call (finite_clause_node q e c S)) \<Longrightarrow> fst (fst x) = q"
  by (auto simp: finite_clause_node_def finite_rename_apart_variables)

definition deferred_place :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    's list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_place P dd q e c S = (let r' = search_call_place P (deferred_inner dd) q e c S in
    case RBT.lookup (shared_nodes (search_state r')) q of None \<Rightarrow> dd\<lparr>deferred_inner := r'\<rparr>
    | Some hn \<Rightarrow> deferred_record_node q (shared_derivation_call (shared_entry_node hn)) (dd\<lparr>deferred_inner := r'\<rparr>))"

theorem deferred_place:
  assumes dd: "deferred_formed \<kappa> P dd" and pl: "search_placeable (search_project (deferred_inner dd))"
    and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state (deferred_inner dd))) q = Some h"
    and g: "shared_goal_project (search_table (deferred_inner dd)) (shared_entry_goal h) = Resolution_Call_Goal q rr e p"
    and cl: "((e,c),S) |\<in>| finite_system_clauses P"
  shows "deferred_formed \<kappa> P (deferred_place P dd q e c S)"
    and "deferred_project (deferred_place P dd q e c S) = Resolution_State
      (finite_clause_goals q e c S |\<union>| (resolution_pending (deferred_project dd) |-| {|Resolution_Call_Goal q rr e p|}))
      (finsert (finite_clause_node q e c S) (resolution_nodes (deferred_project dd))) (resolution_witnesses (deferred_project dd))"
    and "search_placeable (search_project (deferred_inner (deferred_place P dd q e c S)))"
proof -
  let ?r = "deferred_inner dd" let ?s = "search_state ?r" let ?T = "search_table ?r" let ?S = "deferred_store dd"
  let ?st = "search_project ?r" let ?r' = "search_call_place P ?r q e c S" let ?g = "Resolution_Call_Goal q rr e p"
  let ?nd = "finite_clause_node q e c S" let ?G = "finite_clause_goals q e c S" let ?T' = "search_table ?r'"
  have parts: "deferred_parts_formed \<kappa> P dd" and nfs: "\<And>q. deferred_node_formed dd q"
    using dd unfolding deferred_formed_def by blast+
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" and S: "binding_store_formed ?T ?S"
    using parts unfolding deferred_parts_formed_def by blast+
  have st: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF st] .
  note CP = search_call_place_classed[OF r pl sock at g cl]
  have r': "search_formed \<kappa> P ?r'" by (rule CP(1))
  have K': "search_classes_formed ?r'" by (rule CP(5)[OF K])
  have pj: "search_project ?r' = Resolution_State (?G |\<union>| (resolution_pending ?st |-| {|?g|}))
      (finsert ?nd (resolution_nodes ?st)) (resolution_witnesses ?st)" by (rule CP(2))
  have ext: "table_extends ?T ?T'" by (rule CP(4))
  have st': "shared_state_formed \<kappa> P (search_state ?r')" using search_formedD(1)[OF r'] .
  have gin: "?g |\<in>| resolution_pending ?st" using at g unfolding shared_state_project_member(1) by blast
  have dpos: "resolution_positions_distinct ?st" using pl unfolding search_placeable_def by blast
  have noq: "resolution_node_position nd \<noteq> q" if "nd |\<in>| resolution_nodes ?st" for nd
    using dpos gin that unfolding resolution_positions_distinct_def by fastforce
  have nodepos: "shared_derivation_position (shared_entry_node hn) = p'"
    if "RBT.lookup (shared_nodes ?s) p' = Some hn" for p' hn
    using shared_entries_formed(2)[OF st that] by (simp add: node_entry_formed_def)
  have noq_at: "RBT.lookup (shared_nodes ?s) q = None"
  proof (rule ccontr)
    assume "RBT.lookup (shared_nodes ?s) q \<noteq> None"
    then obtain hn where hn: "RBT.lookup (shared_nodes ?s) q = Some hn" by blast
    have "shared_derivation_project ?T (shared_entry_node hn) |\<in>| resolution_nodes ?st"
      unfolding shared_state_project_member(2) using hn by blast
    moreover have "resolution_node_position (shared_derivation_project ?T (shared_entry_node hn)) = q"
      using nodepos[OF hn] by (simp add: shared_derivation_project_def)
    ultimately show False using noq by blast
  qed
  have old_nodes: "RBT.lookup (shared_nodes (search_state ?r')) p' = RBT.lookup (shared_nodes ?s) p'" if "p' \<noteq> q" for p'
    by (rule search_call_place_nodes[OF that])
  have bound_ne: "fst (fst y) \<noteq> q" if "binding_map ?S y \<noteq> None" for y
  proof -
    have "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" using parts that unfolding deferred_parts_formed_def by blast
    then show ?thesis using noq_at by auto
  qed
  have atq: "\<exists>hn. RBT.lookup (shared_nodes (search_state ?r')) q = Some hn \<and>
      shared_derivation_project ?T' (shared_entry_node hn) = ?nd"
  proof -
    have "?nd |\<in>| resolution_nodes (search_project ?r')" using pj by simp
    then obtain p' hn where hn: "RBT.lookup (shared_nodes (search_state ?r')) p' = Some hn"
      and e: "shared_derivation_project ?T' (shared_entry_node hn) = ?nd"
      unfolding shared_state_project_member(2) by blast
    have "shared_derivation_position (shared_entry_node hn) = p'"
      using shared_entries_formed(2)[OF st' hn] by (simp add: node_entry_formed_def)
    then have "p' = q" using e by (simp add: shared_derivation_project_def finite_clause_node_def)
    then show ?thesis using hn e by blast
  qed
  then obtain hq where hq: "RBT.lookup (shared_nodes (search_state ?r')) q = Some hq"
    and hqp: "shared_derivation_project ?T' (shared_entry_node hq) = ?nd" by blast
  let ?c = "shared_derivation_call (shared_entry_node hq)"
  have cf: "shared_pattern_formed ?T' ?c"
    using shared_entries_formed(2)[OF st' hq] by (simp add: node_entry_formed_def shared_derivation_formed_def)
  have cvars: "fst (fst x) = q" if "x |\<in>| shared_pattern_variables ?c" for x
  proof -
    have callp: "shared_pattern_project ?T' ?c = resolution_node_call ?nd"
      using arg_cong[OF hqp, of resolution_node_call] by (simp add: shared_derivation_project_def)
    have "x |\<in>| finite_pattern_variables (resolution_node_call ?nd)"
      using that shared_pattern_variables_project[OF cf] callp by simp
    then show ?thesis by (rule finite_clause_node_positioned)
  qed
  let ?d0 = "dd\<lparr>deferred_inner := ?r'\<rparr>"
  have S': "binding_store_formed ?T' ?S" using binding_store_formed_extended[OF S tf] ext by (simp add: table_extends_def)
  have parts0: "deferred_parts_formed \<kappa> P ?d0"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner ?d0)" using r' by simp
    show "search_classes_formed (deferred_inner ?d0)" using K' by simp
    show "positions_numbered (deferred_positions ?d0)" using parts unfolding deferred_parts_formed_def by simp
    show "binding_store_formed (search_table (deferred_inner ?d0)) (deferred_store ?d0)" using S' by simp
    have tk: "\<forall>k v. RBT.lookup (snd (deferred_tree dd)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered dd y \<and> deferred_key dd y = k)"
      using parts unfolding deferred_parts_formed_def by blast
    show "\<forall>k v. RBT.lookup (snd (deferred_tree ?d0)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered ?d0 y \<and> deferred_key ?d0 y = k)"
      using tk by simp
    show "\<forall>y. binding_map (deferred_store ?d0) y \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) (fst (fst y)) \<noteq> None"
    proof (intro allI impI)
      fix y assume b: "binding_map (deferred_store ?d0) y \<noteq> None"
      have bnd: "\<And>y. binding_map ?S y \<noteq> None \<Longrightarrow> RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      have "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" using bnd b by simp
      then show "RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) (fst (fst y)) \<noteq> None"
        using old_nodes[OF bound_ne] b by simp
    qed
    show "\<forall>q' h' y. RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) q' = Some h' \<longrightarrow>
        y |\<in>| shared_goal_variables (shared_entry_goal h') \<longrightarrow> binding_map (deferred_store ?d0) y = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) (fst (fst y)) \<noteq> None"
    proof (intro allI impI)
      fix q' h' y assume gq: "RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) q' = Some h'"
        and yv: "y |\<in>| shared_goal_variables (shared_entry_goal h')"
      have gq': "RBT.lookup (shared_goals (search_state ?r')) q' = Some h'" using gq by simp
      let ?g' = "shared_goal_project ?T' (shared_entry_goal h')"
      have yv': "y |\<in>| resolution_goal_variables ?g'"
        using yv goal_entry_variables[OF shared_entries_formed(1)[OF st' gq']] by simp
      have m: "?g' |\<in>| resolution_pending (search_project ?r')" unfolding shared_state_project_member(1) using gq' by blast
      have "?g' |\<in>| ?G |\<union>| (resolution_pending ?st |-| {|?g|})" using m unfolding pj resolution_state.sel(1) .
      then have "?g' |\<in>| ?G \<or> ?g' |\<in>| resolution_pending ?st" by (simp only: funion_iff fminus_iff) blast
      have gcl: "\<And>q h y. RBT.lookup (shared_goals ?s) q = Some h \<Longrightarrow> y |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow>
          binding_map ?S y = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      consider (new) "?g' |\<in>| ?G" | (old) "?g' |\<in>| resolution_pending ?st" using \<open>?g' |\<in>| ?G \<or> _\<close> by blast
      then have ok: "binding_map ?S y = None \<and> RBT.lookup (shared_nodes (search_state ?r')) (fst (fst y)) \<noteq> None"
      proof cases
        case new
        have yq: "fst (fst y) = q" by (rule finite_clause_goals_positioned[OF new yv'])
        have "binding_map ?S y = None" using bound_ne yq by blast
        then show ?thesis using yq hq by simp
      next
        case old
        then obtain q0 h0 where h0: "RBT.lookup (shared_goals ?s) q0 = Some h0"
          and e0: "shared_goal_project ?T (shared_entry_goal h0) = ?g'"
          unfolding shared_state_project_member(1) by blast
        have yh: "y |\<in>| shared_goal_variables (shared_entry_goal h0)"
          using yv' e0 goal_entry_variables[OF shared_entries_formed(1)[OF st h0]] by simp
        have o: "binding_map ?S y = None \<and> RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" by (rule gcl[OF h0 yh])
        then have ne: "fst (fst y) \<noteq> q" using noq_at by auto
        then show ?thesis using o old_nodes[OF ne] by simp
      qed
      then show "binding_map (deferred_store ?d0) y = None \<and>
          RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) (fst (fst y)) \<noteq> None" by simp
    qed
    show "\<forall>n q' K. RBT.lookup (deferred_records ?d0) n = Some (q', K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions ?d0) q' \<and> RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) q' \<noteq> None"
    proof (intro allI impI)
      fix n q' K assume rq: "RBT.lookup (deferred_records ?d0) n = Some (q', K)"
      have recs: "\<And>n q' K. RBT.lookup (deferred_records dd) n = Some (q', K) \<Longrightarrow> n \<noteq> 0 \<and>
          n = position_number (deferred_positions dd) q' \<and> RBT.lookup (shared_nodes ?s) q' \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      have o: "n \<noteq> 0 \<and> n = position_number (deferred_positions dd) q' \<and> RBT.lookup (shared_nodes ?s) q' \<noteq> None"
        using recs rq by simp
      then have "q' \<noteq> q" using noq_at by auto
      then show "n \<noteq> 0 \<and> n = position_number (deferred_positions ?d0) q' \<and>
          RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) q' \<noteq> None" using o old_nodes by simp
    qed
  qed
  have nf0: "deferred_node_formed ?d0 q'" if "q' \<noteq> q" for q'
    using nfs[of q'] old_nodes[OF that] unfolding deferred_node_formed_def by simp
  have at0: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) q = Some hq" using hq by simp
  have unb: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow> binding_map (deferred_store ?d0) x = None"
    using cvars bound_ne by fastforce
  have plc: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow>
      fst (fst x) = q \<or> position_number (deferred_positions ?d0) (fst (fst x)) \<noteq> 0" using cvars by blast
  have unbA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow> binding_map (deferred_store ?d0) x = None" using unb by blast
  have plcA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow>
      fst (fst x) = q \<or> position_number (deferred_positions ?d0) (fst (fst x)) \<noteq> 0" using plc by blast
  note R = deferred_record_node[OF parts0 at0 refl unbA plcA]
  have eq: "deferred_place P dd q e c S = deferred_record_node q ?c ?d0" by (simp add: deferred_place_def Let_def hq)
  show "deferred_formed \<kappa> P (deferred_place P dd q e c S)"
    unfolding eq deferred_formed_def
  proof (intro conjI allI)
    show "deferred_parts_formed \<kappa> P (deferred_record_node q ?c ?d0)" by (rule R(1))
    fix q' show "deferred_node_formed (deferred_record_node q ?c ?d0) q'"
    proof (cases "q' = q")
      case True
      then show ?thesis using R(2) by simp
    next
      case False
      then show ?thesis by (rule R(3)[OF nf0])
    qed
  qed
  show "search_placeable (search_project (deferred_inner (deferred_place P dd q e c S)))"
    unfolding eq R(4) using CP(3) by simp
  show "deferred_project (deferred_place P dd q e c S) = Resolution_State
      (?G |\<union>| (resolution_pending (deferred_project dd) |-| {|?g|}))
      (finsert ?nd (resolution_nodes (deferred_project dd))) (resolution_witnesses (deferred_project dd))"
  proof -
    let ?\<sigma> = "deferred_substitution dd"
    have \<sigma>': "deferred_substitution (deferred_record_node q ?c ?d0) = ?\<sigma>"
    proof -
      have "shared_pattern_project ?T' (binding_substitution ?S y) = shared_pattern_project ?T (binding_substitution ?S y)" for y
      proof -
        have "shared_pattern_formed ?T (binding_substitution ?S y)"
          unfolding binding_substitution_def by (rule binding_resolve_formed[OF S]) simp
        then show ?thesis using shared_pattern_extends(2)[OF tf _ ext] by blast
      qed
      then show ?thesis using R(4) R(5) by (simp add: fun_eq_iff deferred_substitution_def)
    qed
    have fixq: "?\<sigma> ((q,True),a) = Finite_Variable ((q,True),a)" for a
    proof -
      have "binding_map ?S ((q,True),a) = None" using bound_ne by fastforce
      then show ?thesis using binding_resolve_unbound[of "Shared_Variable ((q,True),a)" ?S]
        by (simp add: deferred_substitution_def binding_substitution_def)
    qed
    have Gfix: "fimage (resolution_goal_substitute ?\<sigma>) ?G = ?G"
    proof -
      have "fimage (resolution_goal_substitute ?\<sigma>) ?G = fimage (resolution_goal_substitute Finite_Variable) ?G"
        unfolding finite_clause_goals_substitute using fixq by simp
      also have "\<dots> = ?G" by (rule fimage_fixed) (rule resolution_goal_substitute_outside, simp)
      finally show ?thesis .
    qed
    have Nfix: "resolution_node_substitute ?\<sigma> ?nd = ?nd"
    proof -
      have "resolution_node_substitute ?\<sigma> ?nd = resolution_node_substitute Finite_Variable ?nd"
        unfolding finite_clause_node_substitute finite_rename_apart_substitute using fixq by simp
      also have "\<dots> = ?nd" by (rule resolution_node_substitute_outside) simp
      finally show ?thesis .
    qed
    have pend: "fimage (resolution_goal_substitute ?\<sigma>) (resolution_pending ?st |-| {|?g|}) = resolution_pending ?st |-| {|?g|}"
    proof (rule fimage_fixed)
      fix z assume "z |\<in>| resolution_pending ?st |-| {|?g|}"
      then have "z |\<in>| resolution_pending ?st" by simp
      then obtain q0 h0 where h0: "RBT.lookup (shared_goals ?s) q0 = Some h0" and e0: "shared_goal_project ?T (shared_entry_goal h0) = z"
        unfolding shared_state_project_member(1) by blast
      show "resolution_goal_substitute ?\<sigma> z = z" using deferred_goal_fixed[OF dd h0] e0 by blast
    qed
    have "deferred_project (deferred_place P dd q e c S) = resolution_state_substitute ?\<sigma> (search_project ?r')"
      unfolding eq using \<sigma>' R(4) by (simp add: deferred_project_def)
    also have "\<dots> = Resolution_State (?G |\<union>| (resolution_pending ?st |-| {|?g|}))
        (finsert ?nd (fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes ?st))) (resolution_witnesses ?st)"
      unfolding pj resolution_state_substitute_def using Gfix Nfix pend by (simp add: fimage_funion)
    also have "\<dots> = Resolution_State (?G |\<union>| (resolution_pending (deferred_project dd) |-| {|?g|}))
        (finsert ?nd (resolution_nodes (deferred_project dd))) (resolution_witnesses (deferred_project dd))"
      using deferred_pending[OF dd] by (simp add: deferred_project_def resolution_state_substitute_def)
    finally show ?thesis .
  qed
qed

end
