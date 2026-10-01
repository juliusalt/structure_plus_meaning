theory Factor_Deferred_Search
  imports Factor_Shared_Search Shared_Binding_Stores Ranged_Carrier_Indexes "HOL-Library.IArray"
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
  deferred_goal_records :: "('s list, (deferred_key, unit) rbt) rbt"

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
      (RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None \<or>
        (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))) \<and>
    (\<forall>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<longrightarrow> n \<noteq> 0 \<and>
      n = position_number (deferred_positions d) q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None)"

text \<open>
  A goal's clause (D3a, task 977): its record, kept at the goal's position, holds exactly the keys of its variables, every
  one numbered, as a node's record holds its call's. A goal without a record is a call goal at the root: its variables
  stand at the root position, numbered only once a node stands there, and the bind reads it by its own cache (D1b'').
  A record at a position where no goal stands is never read.
\<close>

definition shared_root_goal :: "('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_root_goal g \<longleftrightarrow> (case g of Shared_Call_Goal q r e p \<Rightarrow> q = [] | Shared_Material_Goal q r M \<Rightarrow> False)"

lemma shared_root_goal_iff: "shared_root_goal g \<longleftrightarrow> (\<exists>rr e p. g = Shared_Call_Goal [] rr e p)"
  by (cases g) (auto simp: shared_root_goal_def)

definition deferred_goal_formed :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> 's list \<Rightarrow> bool" where
  "deferred_goal_formed d q \<longleftrightarrow> (\<forall>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<longrightarrow>
    (case RBT.lookup (deferred_goal_records d) q of None \<Rightarrow> shared_root_goal (shared_entry_goal h)
    | Some K \<Rightarrow> set (RBT.keys K) = deferred_key d ` fset (shared_goal_variables (shared_entry_goal h)) \<and>
        fBall (shared_goal_variables (shared_entry_goal h)) (deferred_numbered d)))"

definition deferred_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> bool" where
  "deferred_formed \<kappa> P d \<longleftrightarrow> deferred_parts_formed \<kappa> P d \<and> (\<forall>q. deferred_node_formed d q) \<and>
    (\<forall>q. deferred_goal_formed d q)"

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
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) (fst (fst x)) \<noteq> None \<or>
        (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p))"
    "\<And>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow> n = position_number (deferred_positions d) q"
    "\<And>n q K. RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
    "\<And>q. deferred_node_formed d q"
    "\<And>q. deferred_goal_formed d q"
  using assms unfolding deferred_formed_def deferred_parts_formed_def by blast+

lemma deferred_goal_formedD:
  assumes "deferred_goal_formed d q" and "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
  shows "RBT.lookup (deferred_goal_records d) q = None \<Longrightarrow> shared_root_goal (shared_entry_goal h)"
    and "RBT.lookup (deferred_goal_records d) q = Some K \<Longrightarrow>
      set (RBT.keys K) = deferred_key d ` fset (shared_goal_variables (shared_entry_goal h))"
    and "RBT.lookup (deferred_goal_records d) q = Some K \<Longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow> deferred_numbered d x"
  using assms unfolding deferred_goal_formed_def by auto

text \<open>
  A goal's clause depends on the goal's variables, whether it is a root call goal, its record and the keys of its
  numbered variables: a step keeping these keeps the clause.
\<close>

lemma deferred_goal_formed_cong:
  assumes f: "deferred_goal_formed d q"
    and goals: "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner d'))) q = Some h' \<Longrightarrow>
      \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<and>
        shared_goal_variables (shared_entry_goal h') = shared_goal_variables (shared_entry_goal h) \<and>
        (shared_root_goal (shared_entry_goal h') \<longleftrightarrow> shared_root_goal (shared_entry_goal h))"
    and recs: "RBT.lookup (deferred_goal_records d') q = RBT.lookup (deferred_goal_records d) q"
    and keys: "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key d' x = deferred_key d x \<and> deferred_numbered d' x"
  shows "deferred_goal_formed d' q"
  unfolding deferred_goal_formed_def
proof (intro allI impI)
  fix h' assume at': "RBT.lookup (shared_goals (search_state (deferred_inner d'))) q = Some h'"
  obtain h where at: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
    and v: "shared_goal_variables (shared_entry_goal h') = shared_goal_variables (shared_entry_goal h)"
    and rt: "shared_root_goal (shared_entry_goal h') \<longleftrightarrow> shared_root_goal (shared_entry_goal h)" using goals[OF at'] by blast
  show "case RBT.lookup (deferred_goal_records d') q of None \<Rightarrow> shared_root_goal (shared_entry_goal h')
    | Some K \<Rightarrow> set (RBT.keys K) = deferred_key d' ` fset (shared_goal_variables (shared_entry_goal h')) \<and>
        fBall (shared_goal_variables (shared_entry_goal h')) (deferred_numbered d')"
  proof (cases "RBT.lookup (deferred_goal_records d) q")
    case None
    then show ?thesis using recs rt deferred_goal_formedD(1)[OF f at] by simp
  next
    case (Some K)
    have k: "set (RBT.keys K) = deferred_key d ` fset (shared_goal_variables (shared_entry_goal h))"
      by (rule deferred_goal_formedD(2)[OF f at Some])
    have n: "\<And>x. x |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow> deferred_numbered d x"
      by (rule deferred_goal_formedD(3)[OF f at Some])
    have ke: "deferred_key d' ` fset (shared_goal_variables (shared_entry_goal h)) =
        deferred_key d ` fset (shared_goal_variables (shared_entry_goal h))"
      using keys n by (auto simp: image_iff)
    have nu: "fBall (shared_goal_variables (shared_entry_goal h)) (deferred_numbered d')" using keys n by blast
    show ?thesis using recs Some k v ke nu by simp
  qed
qed

lemma deferred_goal_formed_same:
  assumes f: "deferred_goal_formed d q"
    and goals: "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner d'))) q = Some h' \<Longrightarrow>
      \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
    and recs: "RBT.lookup (deferred_goal_records d') q = RBT.lookup (deferred_goal_records d) q"
    and keys: "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key d' x = deferred_key d x \<and> deferred_numbered d' x"
  shows "deferred_goal_formed d' q"
  by (rule deferred_goal_formed_cong[OF f _ recs keys]) (fastforce dest: goals)

lemma deferred_goal_records_update_key [simp]: "deferred_key (d\<lparr>deferred_goal_records := G\<rparr>) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def)

lemma deferred_goal_records_update [simp]:
  "deferred_numbered (d\<lparr>deferred_goal_records := G\<rparr>) = deferred_numbered d"
  "deferred_store (d\<lparr>deferred_goal_records := G\<rparr>) = deferred_store d"
  by (simp_all add: fun_eq_iff deferred_numbered_def deferred_store_def)

lemma deferred_goal_records_update_formed [simp]:
  "deferred_parts_formed \<kappa> P (d\<lparr>deferred_goal_records := G\<rparr>) = deferred_parts_formed \<kappa> P d"
  "deferred_node_formed (d\<lparr>deferred_goal_records := G\<rparr>) = deferred_node_formed d"
  by (simp_all add: fun_eq_iff deferred_parts_formed_def deferred_node_formed_def)

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

text \<open>
  A key is decoded only where the access reads a node's call variables, through an array of the numbered positions made
  once where the access is built (review 904's follow-up 2), never through the reversed numbering at each key.
\<close>

definition deferred_decode_in :: "'s list iarray \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> deferred_key \<Rightarrow>
    ('s,'a) resolution_variable" where
  "deferred_decode_in A d k = (case k of (n,b,m) \<Rightarrow> ((A !! (n - 1), b), deferred_names d ! (m - 1)))"

definition deferred_call_variables_in :: "'s list iarray \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset" where
  "deferred_call_variables_in A d hn = (case RBT.lookup (deferred_records d)
      (position_number (deferred_positions d) (shared_derivation_position (shared_entry_node hn))) of
    None \<Rightarrow> {||} | Some z \<Rightarrow> fimage (deferred_decode_in A d) (fset_of_list (RBT.keys (snd z))))"

lemma deferred_call_variables_in:
  "deferred_call_variables_in (IArray (rev (snd (snd (deferred_positions d))))) d = deferred_call_variables d"
proof (rule ext)
  fix hn
  have e: "deferred_decode_in (IArray (rev (snd (snd (deferred_positions d))))) d = deferred_decode d"
    by (simp add: fun_eq_iff deferred_decode_in_def deferred_decode_def split: prod.split)
  show "deferred_call_variables_in (IArray (rev (snd (snd (deferred_positions d))))) d hn = deferred_call_variables d hn"
    unfolding deferred_call_variables_in_def deferred_call_variables_def e ..
qed

lemma deferred_access_code [code]:
  "deferred_access \<kappa> P d = (let A = IArray (rev (snd (snd (deferred_positions d)))) in
    (shared_access \<kappa> P (deferred_inner d))\<lparr>access_node := deferred_node d, access_free := deferred_free \<kappa> d,
      access_value_none := \<lambda>hn a. finite_registered_value \<kappa> P (deferred_node d hn) a = None,
      access_call_variables := deferred_call_variables_in A d\<rparr>)"
  by (simp add: deferred_access_def deferred_call_variables_in)

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

lemma deferred_renumbered_goal_records:
  assumes re: "deferred_renumbered d d'"
  shows "deferred_goal_records d' = deferred_goal_records d"
proof -
  have e: "d' = d\<lparr>deferred_positions := deferred_positions d', deferred_names := deferred_names d'\<rparr>"
    using re by (simp add: deferred_renumbered_def)
  show ?thesis by (subst e) simp
qed

lemma deferred_renumbered_goal:
  assumes re: "deferred_renumbered d d'" and parts: "deferred_parts_formed \<kappa> P d" and gf: "deferred_goal_formed d q"
  shows "deferred_goal_formed d' q"
proof -
  have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
  show ?thesis
  proof (rule deferred_goal_formed_same[OF gf])
    show "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner d'))) q = Some h' \<Longrightarrow>
      \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
      using deferred_renumbered_fields(1)[OF re] by simp
    show "RBT.lookup (deferred_goal_records d') q = RBT.lookup (deferred_goal_records d) q"
      using deferred_renumbered_goal_records[OF re] by simp
    show "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key d' x = deferred_key d x \<and> deferred_numbered d' x"
      using deferred_renumbered_key[OF re N] by blast
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

subsection \<open>Recording a goal\<close>

text \<open>
  D3a (task 977). A goal is recorded at its position: the names of its variables numbered, its record the keyed set of
  its variables over @{const deferred_key}, as a node's. A call goal at the root is not recorded: its variables stand at
  the root position, unnumbered while no node stands there, and the bind reads it by its cache.
\<close>

fun shared_goal_variable_list :: "('a,'s,'d,'c) shared_goal \<Rightarrow> ('s,'a) resolution_variable list" where
  "shared_goal_variable_list (Shared_Call_Goal q r d p) = shared_variable_list p"
| "shared_goal_variable_list (Shared_Material_Goal q r M) = shared_variable_list (shared_material_source M) @
    shared_variable_list (shared_material_atoms M) @ shared_variable_list (shared_material_edges M) @
    shared_variable_list (shared_material_counts M) @ shared_variable_list (shared_material_functions M)"

lemma shared_goal_variable_list:
  "shared_goal_formed T g \<Longrightarrow> set (shared_goal_variable_list g) = fset (shared_goal_variables g)"
  by (cases g) (auto simp: shared_material_formed_def shared_material_variables_def shared_variable_list)

lemma deferred_record_node_goal_records [simp]:
  "deferred_goal_records (deferred_record_node q p d) = deferred_goal_records d"
  by (simp add: deferred_record_node_def deferred_record_at_def deferred_renumber_def Let_def)

lemma deferred_record_node_keys:
  assumes parts: "deferred_parts_formed \<kappa> P d" and x: "deferred_numbered d x"
  shows "deferred_key (deferred_record_node q p d) x = deferred_key d x \<and> deferred_numbered (deferred_record_node q p d) x"
proof -
  let ?d1 = "deferred_renumber q p d"
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
  have k: "deferred_key (deferred_record_node q p d) = deferred_key ?d1"
    by (simp add: deferred_record_node_def deferred_record_at_def Let_def fun_eq_iff deferred_key_def)
  have n: "deferred_numbered (deferred_record_node q p d) = deferred_numbered ?d1"
    by (simp add: deferred_record_node_def deferred_record_at_def Let_def fun_eq_iff deferred_numbered_def)
  show ?thesis using deferred_renumbered_key[OF re N x] k n by simp
qed

definition deferred_record_goal :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_record_goal p d = (case RBT.lookup (shared_goals (search_state (deferred_inner d))) p of None \<Rightarrow> d
    | Some h \<Rightarrow> if shared_root_goal (shared_entry_goal h) then d else
      (let vs = shared_goal_variable_list (shared_entry_goal h);
        d1 = d\<lparr>deferred_names := deferred_number_names (map snd vs) (deferred_names d)\<rparr> in
      d1\<lparr>deferred_goal_records := RBT.insert p (fold (\<lambda>k t. RBT.insert k () t) (map (deferred_key d1) vs) RBT.empty)
        (deferred_goal_records d1)\<rparr>))"

definition deferred_record_goals :: "'s::linorder list list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_record_goals ps d = fold deferred_record_goal ps d"

lemma deferred_record_goal:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and placed: "\<forall>h x. RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h) \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      position_number (deferred_positions d) (fst (fst x)) \<noteq> 0"
    and root: "\<forall>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      shared_root_goal (shared_entry_goal h) \<longrightarrow> RBT.lookup (deferred_goal_records d) p = None"
  shows "deferred_parts_formed \<kappa> P (deferred_record_goal p d) \<and> deferred_goal_formed (deferred_record_goal p d) p \<and>
    (\<forall>q. q \<noteq> p \<longrightarrow> deferred_goal_formed d q \<longrightarrow> deferred_goal_formed (deferred_record_goal p d) q) \<and>
    (\<forall>q. deferred_node_formed d q \<longrightarrow> deferred_node_formed (deferred_record_goal p d) q) \<and>
    deferred_inner (deferred_record_goal p d) = deferred_inner d \<and> deferred_store (deferred_record_goal p d) = deferred_store d \<and>
    deferred_positions (deferred_record_goal p d) = deferred_positions d \<and>
    deferred_records (deferred_record_goal p d) = deferred_records d \<and>
    deferred_holders (deferred_record_goal p d) = deferred_holders d \<and> deferred_tree (deferred_record_goal p d) = deferred_tree d \<and>
    (\<forall>q. q \<noteq> p \<longrightarrow> RBT.lookup (deferred_goal_records (deferred_record_goal p d)) q = RBT.lookup (deferred_goal_records d) q) \<and>
    (\<forall>x. deferred_numbered d x \<longrightarrow> deferred_key (deferred_record_goal p d) x = deferred_key d x \<and>
      deferred_numbered (deferred_record_goal p d) x)"
proof -
  let ?s = "search_state (deferred_inner d)"
  show ?thesis
  proof (cases "RBT.lookup (shared_goals ?s) p")
    case None
    have e: "deferred_record_goal p d = d" by (simp add: deferred_record_goal_def None)
    have "deferred_goal_formed d p" by (simp add: deferred_goal_formed_def None)
    then show ?thesis using parts e by simp
  next
    case (Some h)
    show ?thesis
    proof (cases "shared_root_goal (shared_entry_goal h)")
      case True
      have e: "deferred_record_goal p d = d" by (simp add: deferred_record_goal_def Some True)
      have "deferred_goal_formed d p" using root[rule_format, OF Some True] Some True by (simp add: deferred_goal_formed_def)
      then show ?thesis using parts e by simp
    next
      case False
      let ?vs = "shared_goal_variable_list (shared_entry_goal h)"
      let ?d1 = "d\<lparr>deferred_names := deferred_number_names (map snd ?vs) (deferred_names d)\<rparr>"
      let ?K = "fold (\<lambda>k t. RBT.insert k () t) (map (deferred_key ?d1) ?vs) RBT.empty"
      have e: "deferred_record_goal p d = ?d1\<lparr>deferred_goal_records := RBT.insert p ?K (deferred_goal_records ?d1)\<rparr>"
        by (simp add: deferred_record_goal_def Some False Let_def)
      have re: "deferred_renumbered d ?d1"
        unfolding deferred_renumbered_def using deferred_number_names(1)[of "map snd ?vs" "deferred_names d"]
        by (auto intro!: exI[where x = "[]"])
      have N: "positions_numbered (deferred_positions d)" using parts by (simp add: deferred_parts_formed_def)
      have parts1: "deferred_parts_formed \<kappa> P ?d1" by (rule deferred_renumbered_parts[OF re parts])
      have st1: "deferred_store ?d1 = deferred_store d" by (rule deferred_renumbered_store[OF re parts])
      have gf: "shared_goal_formed (search_table (deferred_inner d)) (shared_entry_goal h)"
        using shared_entries_formed(1)[OF search_formedD(1)[OF conjunct1[OF parts[unfolded deferred_parts_formed_def]]] Some]
        by (simp add: goal_entry_formed_def)
      have vl: "set ?vs = fset (shared_goal_variables (shared_entry_goal h))" by (rule shared_goal_variable_list[OF gf])
      have num: "deferred_numbered ?d1 x" if "x |\<in>| shared_goal_variables (shared_entry_goal h)" for x
      proof -
        have a: "position_number (deferred_positions ?d1) (fst (fst x)) \<noteq> 0" using placed[rule_format, OF Some False that] by simp
        have "snd x \<in> set (deferred_names ?d1)" using that vl deferred_number_names(2) by force
        then show ?thesis using a name_number_nonzero[of "deferred_names ?d1" "snd x"] unfolding deferred_numbered_def by blast
      qed
      have keys: "set (RBT.keys ?K) = deferred_key ?d1 ` fset (shared_goal_variables (shared_entry_goal h))"
        using fold_insert_unit_keys[of "map (deferred_key ?d1) ?vs" RBT.empty] vl by simp
      have kE: "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key ?d1 x = deferred_key d x \<and> deferred_numbered ?d1 x"
        using deferred_renumbered_key[OF re N] by blast
      have gp: "deferred_goal_formed (deferred_record_goal p d) p"
        unfolding deferred_goal_formed_def e using Some keys num by auto
      have go: "deferred_goal_formed (deferred_record_goal p d) q" if ne: "q \<noteq> p" and f: "deferred_goal_formed d q" for q
        by (rule deferred_goal_formed_same[OF f]) (use ne kE in \<open>simp_all add: e\<close>)
      have nf: "deferred_node_formed (deferred_record_goal p d) q" if "deferred_node_formed d q" for q
        using deferred_renumbered_node[OF re parts that] e by simp
      show ?thesis using parts1 gp go nf st1 kE e by simp
    qed
  qed
qed

lemma deferred_record_goals:
  assumes "deferred_parts_formed \<kappa> P d"
    and "\<forall>p h x. p \<in> set ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h) \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      position_number (deferred_positions d) (fst (fst x)) \<noteq> 0"
    and "\<forall>p h. p \<in> set ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      shared_root_goal (shared_entry_goal h) \<longrightarrow> RBT.lookup (deferred_goal_records d) p = None"
    and "\<forall>q. q \<notin> set ps \<longrightarrow> deferred_goal_formed d q"
  shows "deferred_parts_formed \<kappa> P (deferred_record_goals ps d) \<and> (\<forall>q. deferred_goal_formed (deferred_record_goals ps d) q) \<and>
    (\<forall>q. deferred_node_formed d q \<longrightarrow> deferred_node_formed (deferred_record_goals ps d) q) \<and>
    deferred_inner (deferred_record_goals ps d) = deferred_inner d \<and> deferred_store (deferred_record_goals ps d) = deferred_store d \<and>
    deferred_positions (deferred_record_goals ps d) = deferred_positions d \<and>
    deferred_records (deferred_record_goals ps d) = deferred_records d \<and>
    deferred_holders (deferred_record_goals ps d) = deferred_holders d \<and>
    deferred_tree (deferred_record_goals ps d) = deferred_tree d"
  using assms unfolding deferred_record_goals_def
proof (induction ps arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  let ?d' = "deferred_record_goal p d"
  have pl: "\<forall>h x. RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h) \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      position_number (deferred_positions d) (fst (fst x)) \<noteq> 0"
    by (intro allI impI) (rule Cons.prems(2)[rule_format], auto)
  have rt: "\<forall>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) p = Some h \<longrightarrow>
      shared_root_goal (shared_entry_goal h) \<longrightarrow> RBT.lookup (deferred_goal_records d) p = None" using Cons.prems(3) by simp
  note R = deferred_record_goal[OF Cons.prems(1) pl rt]
  have parts': "deferred_parts_formed \<kappa> P ?d'" using R by blast
  have inner': "deferred_inner ?d' = deferred_inner d" using R by blast
  have pos': "deferred_positions ?d' = deferred_positions d" using R by blast
  have pl': "\<forall>p' h x. p' \<in> set ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner ?d'))) p' = Some h \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h) \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      position_number (deferred_positions ?d') (fst (fst x)) \<noteq> 0"
    unfolding inner' pos' by (intro allI impI) (rule Cons.prems(2)[rule_format], auto)
  have rt': "\<forall>p' h. p' \<in> set ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner ?d'))) p' = Some h \<longrightarrow>
      shared_root_goal (shared_entry_goal h) \<longrightarrow> RBT.lookup (deferred_goal_records ?d') p' = None"
  proof (intro allI impI)
    fix p' h assume m: "p' \<in> set ps" and a: "RBT.lookup (shared_goals (search_state (deferred_inner ?d'))) p' = Some h"
      and r: "shared_root_goal (shared_entry_goal h)"
    have a0: "RBT.lookup (shared_goals (search_state (deferred_inner d))) p' = Some h" using a inner' by simp
    have n0: "RBT.lookup (deferred_goal_records d) p' = None" using Cons.prems(3) m a0 r by simp
    show "RBT.lookup (deferred_goal_records ?d') p' = None"
    proof (cases "p' = p")
      case True
      then have "?d' = d" using a0 r by (simp add: deferred_record_goal_def)
      then show ?thesis using n0 by simp
    next
      case False
      then show ?thesis using R n0 by simp
    qed
  qed
  have ot': "\<forall>q. q \<notin> set ps \<longrightarrow> deferred_goal_formed ?d' q"
  proof (intro allI impI)
    fix q assume q: "q \<notin> set ps"
    show "deferred_goal_formed ?d' q"
    proof (cases "q = p")
      case True
      then show ?thesis using R by blast
    next
      case False
      then have "deferred_goal_formed d q" using Cons.prems(4) q by simp
      then show ?thesis using R False by blast
    qed
  qed
  note IH = Cons.IH[OF parts' pl' rt' ot']
  show ?case using IH R by auto
qed

subsection \<open>The deferred search of an R3 state\<close>

text \<open>
  The deferred search starts from the shared search of an R3 state, its store empty: every node position numbered first,
  then every node recorded. It needs every variable of a node's call to stand at a node's position, as R3's own renaming
  apart places them, and every variable of a goal to stand there too or at the root position of a call goal at the root,
  where no node stands yet: a query's root (@{text finite_pattern_state}) holds its variables there. Such a variable is
  bound only once the root call places its node, so it is never numbered nor recorded before its position is.
\<close>

definition search_variables_placed :: "('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "search_variables_placed st \<longleftrightarrow>
    fBall (resolution_pending st) (\<lambda>g. fBall (resolution_goal_variables g)
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st))) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. fBall (finite_pattern_variables (resolution_node_call nd))
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)))"

definition root_call_goal where
  "root_call_goal g \<longleftrightarrow> (case g of Resolution_Call_Goal q r e p \<Rightarrow> q = [] | Resolution_Material_Goal q r M \<Rightarrow> False)"

lemma root_call_goal_iff: "root_call_goal g \<longleftrightarrow> (\<exists>rr e p. g = Resolution_Call_Goal [] rr e p)"
  by (cases g) (auto simp: root_call_goal_def)

definition search_variables_rooted :: "('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "search_variables_rooted st \<longleftrightarrow>
    fBall (resolution_pending st) (\<lambda>g. fBall (resolution_goal_variables g)
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st) \<or>
        (fst (fst x) = [] \<and> root_call_goal g))) \<and>
    fBall (resolution_nodes st) (\<lambda>nd. fBall (finite_pattern_variables (resolution_node_call nd))
      (\<lambda>x. fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)))"

lemma search_variables_placed_rooted: "search_variables_placed st \<Longrightarrow> search_variables_rooted st"
  unfolding search_variables_placed_def search_variables_rooted_def by blast

lemma shared_goal_project_call:
  "shared_goal_project T g = Resolution_Call_Goal q rr e p \<Longrightarrow> \<exists>gp. g = Shared_Call_Goal q rr e gp"
  by (cases g) auto

definition deferred_of :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_of P st = (let r = search_of P st; es = RBT.entries (shared_nodes (search_state r)) in
    deferred_record_goals (RBT.keys (shared_goals (search_state r)))
      (fold (\<lambda>z d. deferred_record_node (fst z) (shared_derivation_call (shared_entry_node (snd z))) d) es
        \<lparr>deferred_inner = r, deferred_tree = binding_tree_empty,
         deferred_positions = snd (keyed_reference_sequence id (map fst es) (RBT.empty, 0, [])),
         deferred_names = [], deferred_records = RBT.empty, deferred_holders = RBT.empty,
         deferred_goal_records = RBT.empty\<rparr>))"

lemma binding_tree_store_empty: "binding_tree_store key binding_tree_empty = binding_store_empty"
  by (simp add: binding_tree_store_def binding_tree_empty_def binding_store_empty_def)

text \<open>
  The deferred state of a shared search records its nodes over that search, whatever table the search was shared
  from: the deferred state of an R3 state is the one of its shared search (@{text deferred_of_search_of}).
\<close>

definition deferred_of_search :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_of_search r = (let es = RBT.entries (shared_nodes (search_state r)) in
    deferred_record_goals (RBT.keys (shared_goals (search_state r)))
      (fold (\<lambda>z d. deferred_record_node (fst z) (shared_derivation_call (shared_entry_node (snd z))) d) es
        \<lparr>deferred_inner = r, deferred_tree = binding_tree_empty,
         deferred_positions = snd (keyed_reference_sequence id (map fst es) (RBT.empty, 0, [])),
         deferred_names = [], deferred_records = RBT.empty, deferred_holders = RBT.empty,
         deferred_goal_records = RBT.empty\<rparr>))"

lemma deferred_of_search_of: "deferred_of P st = deferred_of_search (search_of P st)"
  by (simp add: deferred_of_def deferred_of_search_def Let_def)

theorem deferred_of_search_rooted:
  fixes r :: "('a,'s::linorder,'d,'c) shared_search" and st :: "('a,'s,'d,'c) resolution_state"
  assumes r0: "search_formed \<kappa> P r" and K0: "search_classes_formed r" and pr0: "search_project r = st"
    and v: "search_variables_rooted st"
  shows "deferred_formed \<kappa> P (deferred_of_search r)" and "deferred_project (deferred_of_search r) = st"
    and "deferred_inner (deferred_of_search r) = r"
proof -
  let ?r = "r" let ?s = "search_state ?r" let ?es = "RBT.entries (shared_nodes ?s)"
  let ?N0 = "snd (keyed_reference_sequence id (map fst ?es) (RBT.empty, 0, []))"
  let ?Ts = "snd (value_reference_sequence (map fst ?es) [])"
  let ?ds = "\<lparr>deferred_inner = ?r, deferred_tree = binding_tree_empty, deferred_positions = ?N0,
    deferred_names = [], deferred_records = RBT.empty, deferred_holders = RBT.empty, deferred_goal_records = RBT.empty\<rparr>
    :: ('a,'s,'d,'c) deferred_search"
  have r: "search_formed \<kappa> P ?r" and pr: "search_project ?r = st" using r0 pr0 by simp_all
  have K: "search_classes_formed ?r" using K0 .
  have T0: "keyed_reference_state id ?N0 ?Ts"
    using keyed_reference_sequence_exact[OF inj_on_id keyed_reference_state_empty, of "map fst ?es"] by simp
  have nodepos: "q \<in> set ?Ts" if "RBT.lookup (shared_nodes ?s) q \<noteq> None" for q
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
  have st0: "deferred_store ?ds = binding_store_empty" by (simp add: deferred_store_def binding_tree_store_empty)
  have goalv: "RBT.lookup (shared_nodes ?s) (fst (fst x)) \<noteq> None \<or>
      (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p))"
    if "RBT.lookup (shared_goals ?s) q = Some h" "x |\<in>| shared_goal_variables (shared_entry_goal h)" for q h x
  proof -
    have gf: "goal_entry_formed P (search_table ?r) q h" using shared_entries_formed(1)[OF s that(1)] .
    have "shared_goal_project (search_table ?r) (shared_entry_goal h) |\<in>| resolution_pending (search_project ?r)"
      unfolding shared_state_project_member(1) using that(1) by blast
    then have "shared_goal_project (search_table ?r) (shared_entry_goal h) |\<in>| resolution_pending st" using pr by simp
    moreover have "x |\<in>| resolution_goal_variables (shared_goal_project (search_table ?r) (shared_entry_goal h))"
      using that(2) goal_entry_variables[OF gf] by simp
    ultimately have "fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st) \<or>
        (fst (fst x) = [] \<and> (\<exists>rr e p. shared_goal_project (search_table ?r) (shared_entry_goal h) = Resolution_Call_Goal [] rr e p))"
      using v unfolding search_variables_rooted_def root_call_goal_iff by blast
    then show ?thesis
    proof
      assume "fst (fst x) |\<in>| fimage resolution_node_position (resolution_nodes st)"
      then show ?thesis using placed_at by blast
    next
      assume "fst (fst x) = [] \<and>
        (\<exists>rr e p. shared_goal_project (search_table ?r) (shared_entry_goal h) = Resolution_Call_Goal [] rr e p)"
      then obtain rr e p where r: "fst (fst x) = []"
        "shared_goal_project (search_table ?r) (shared_entry_goal h) = Resolution_Call_Goal [] rr e p" by blast
      obtain gp where "shared_entry_goal h = Shared_Call_Goal [] rr e gp" using shared_goal_project_call[OF r(2)] by blast
      then show ?thesis using r(1) by blast
    qed
  qed
  have parts0: "deferred_parts_formed \<kappa> P ?ds"
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
      then show ?thesis using v m unfolding search_variables_rooted_def by blast
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
  have dof: "deferred_of_search r = deferred_record_goals (RBT.keys (shared_goals ?s)) (fold step ?es ?ds)"
    by (simp add: deferred_of_search_def step_def Let_def)
  have npos0: "\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions ?ds) q \<noteq> 0"
  proof (intro allI impI)
    fix q assume "RBT.lookup (shared_nodes ?s) q \<noteq> None"
    then have "q \<in> set ?Ts" by (rule nodepos)
    then show "position_number (deferred_positions ?ds) q \<noteq> 0" using position_number_nonzero[OF T0, of q] by simp
  qed
  have in0: "deferred_inner ?ds = ?r" by simp
  have nf0: "\<forall>q\<in>{}. deferred_node_formed ?ds q" by simp
  note F = fold[where Q = "{}", OF parts0 in0 st0 npos0 nf0 order_refl]
  have allq: "deferred_node_formed (fold step ?es ?ds) q" for q
  proof (cases "RBT.lookup (shared_nodes ?s) q")
    case None
    then show ?thesis using F by (simp add: deferred_node_formed_def)
  next
    case (Some hn)
    then have "map_of ?es q = Some hn" by (simp add: RBT.map_of_entries)
    then have "(q, hn) \<in> set ?es" by (rule map_of_SomeD)
    then have qm: "q \<in> fst ` set ?es" by (rule rev_image_eqI) simp
    have Fn: "\<forall>q. q \<in> {} \<union> fst ` set ?es \<longrightarrow> deferred_node_formed (fold step ?es ?ds) q" using F by blast
    show ?thesis using Fn qm by blast
  qed
  let ?d0 = "fold step ?es ?ds"
  have gr0: "deferred_goal_records ?d0 = RBT.empty"
    by (subst fold_value_kept[where g = deferred_goal_records]) (simp_all add: step_def)
  have parts0': "deferred_parts_formed \<kappa> P ?d0" and in0': "deferred_inner ?d0 = ?r"
    and npos: "\<forall>q. RBT.lookup (shared_nodes ?s) q \<noteq> None \<longrightarrow> position_number (deferred_positions ?d0) q \<noteq> 0"
    using F by blast+
  have pl: "position_number (deferred_positions ?d0) (fst (fst x)) \<noteq> 0"
    if "p \<in> set (RBT.keys (shared_goals ?s))" and a: "RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) p = Some h"
      and nr: "\<not> shared_root_goal (shared_entry_goal h)" and x: "x |\<in>| shared_goal_variables (shared_entry_goal h)" for p h x
  proof -
    have "binding_map (deferred_store ?d0) x = None \<and>
        (RBT.lookup (shared_nodes (search_state (deferred_inner ?d0))) (fst (fst x)) \<noteq> None \<or>
          (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
      using parts0' a x unfolding deferred_parts_formed_def by blast
    then have "RBT.lookup (shared_nodes ?s) (fst (fst x)) \<noteq> None" using nr in0' by (auto simp: shared_root_goal_iff)
    then show ?thesis using npos by blast
  qed
  have ot: "deferred_goal_formed ?d0 q" if "q \<notin> set (RBT.keys (shared_goals ?s))" for q
  proof -
    have "RBT.lookup (shared_goals ?s) q = None" using that RBT.lookup_keys[of "shared_goals ?s"] by auto
    then show ?thesis using in0' by (simp add: deferred_goal_formed_def)
  qed
  have plA: "\<forall>p h x. p \<in> set (RBT.keys (shared_goals ?s)) \<longrightarrow>
      RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) p = Some h \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h) \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      position_number (deferred_positions ?d0) (fst (fst x)) \<noteq> 0" using pl by blast
  have rtA: "\<forall>p h. p \<in> set (RBT.keys (shared_goals ?s)) \<longrightarrow>
      RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) p = Some h \<longrightarrow>
      shared_root_goal (shared_entry_goal h) \<longrightarrow> RBT.lookup (deferred_goal_records ?d0) p = None" using gr0 by simp
  have otA: "\<forall>q. q \<notin> set (RBT.keys (shared_goals ?s)) \<longrightarrow> deferred_goal_formed ?d0 q" using ot by blast
  note G = deferred_record_goals[OF parts0' plA rtA otA]
  have G': "deferred_parts_formed \<kappa> P (deferred_of_search r) \<and> (\<forall>q. deferred_goal_formed (deferred_of_search r) q) \<and>
      (\<forall>q. deferred_node_formed ?d0 q \<longrightarrow> deferred_node_formed (deferred_of_search r) q) \<and>
      deferred_inner (deferred_of_search r) = deferred_inner ?d0 \<and> deferred_store (deferred_of_search r) = deferred_store ?d0"
    unfolding dof using G by simp
  show "deferred_formed \<kappa> P (deferred_of_search r)" using G' allq by (simp add: deferred_formed_def)
  show inner: "deferred_inner (deferred_of_search r) = r" using G' in0' by simp
  have sv: "deferred_substitution (deferred_of_search r) = Finite_Variable"
    using F G' by (simp add: fun_eq_iff deferred_substitution_def binding_substitution_def binding_resolve_empty)
  have g: "fimage (resolution_goal_substitute Finite_Variable) (resolution_pending st) = resolution_pending st"
    by (rule fimage_fixed) (rule resolution_goal_substitute_outside, simp)
  have n: "fimage (resolution_node_substitute Finite_Variable) (resolution_nodes st) = resolution_nodes st"
    by (rule fimage_fixed) (rule resolution_node_substitute_outside, simp)
  show "deferred_project (deferred_of_search r) = st"
    unfolding deferred_project_def sv inner pr resolution_state_substitute_def g n by (cases st) simp
qed

theorem deferred_of_rooted:
  fixes st :: "('a,'s::linorder,'d,'c) resolution_state"
  assumes d: "resolution_positions_distinct st" and v: "search_variables_rooted st"
  shows "deferred_formed \<kappa> P (deferred_of P st)" and "deferred_project (deferred_of P st) = st"
    and "deferred_inner (deferred_of P st) = search_of P st"
  using deferred_of_search_rooted[OF search_of(1)[OF d] search_of_classes[OF d] search_of(2)[OF d] v]
  by (simp_all add: deferred_of_search_of)

theorem deferred_of:
  fixes st :: "('a,'s::linorder,'d,'c) resolution_state"
  assumes d: "resolution_positions_distinct st" and v: "search_variables_placed st"
  shows "deferred_formed \<kappa> P (deferred_of P st)" and "deferred_project (deferred_of P st) = st"
    and "deferred_inner (deferred_of P st) = search_of P st"
  using deferred_of_rooted[OF d search_variables_placed_rooted[OF v]] by blast+

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
  let ?s' = "shared_goal_substitute_at P \<sigma> D q s" and ?Ts = "shared_state_table s"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?Ts (\<sigma> a)"
  have x0: "share_state_formed (shared_sharing s)" and tf0: "table_formed ?Ts" using shared_entries_formed(3,4)[OF s] .
  have all: "shared_state_formed \<kappa> P ?s' \<and> table_extends ?Ts (shared_state_table ?s') \<and>
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
    have hf: "goal_entry_formed P ?Ts q h" using shared_entries_formed(1)[OF s Some] .
    have k: "share_state_formed x \<and> table_extends ?Ts (share_state_table x) \<and> goal_entry_formed P (share_state_table x) q h' \<and>
        shared_goal_project (share_state_table x) (shared_entry_goal h') =
          resolution_goal_substitute ?\<tau> (shared_goal_project ?Ts (shared_entry_goal h))"
      using shared_goal_entry_substitute[where D = D, OF x0 hf \<sigma>f \<sigma>c out[rule_format]] e by simp
    let ?sr = "shared_reshare x s"
    have xf: "share_state_formed x" and ext: "table_extends ?Ts (share_state_table x)" using k by simp_all
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
  show "table_extends ?Ts (shared_state_table ?s')" using all by blast
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

definition deferred_ground_node :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_ground_node q d = (case RBT.lookup (shared_nodes (search_state (deferred_inner d))) q of None \<Rightarrow> d
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

theorem deferred_ground_node:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
    and gr: "shared_pattern_variables (deferred_call d hn) = {||}"
  shows "deferred_parts_formed \<kappa> P (deferred_ground_node q d)"
    and "\<exists>r'. deferred_ground_node q d = d\<lparr>deferred_inner := r'\<rparr>"
    and "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
    and "\<exists>hn'. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) q = Some hn' \<and>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_ground_node q d) q'"
    and "position_number (deferred_positions d) q \<noteq> 0 \<Longrightarrow>
      RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K) \<Longrightarrow>
      set (RBT.keys K) = {} \<Longrightarrow> deferred_node_formed (deferred_ground_node q d) q"
    and "deferred_project (deferred_ground_node q d) = deferred_project d"
    and "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground_node q d)))"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?Ts = "search_table ?r" let ?S = "deferred_store d"
  let ?nd = "shared_entry_node hn" let ?c = "shared_derivation_call ?nd" let ?x0 = "shared_sharing ?s"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" and S: "binding_store_formed ?Ts ?S"
    using parts unfolding deferred_parts_formed_def by blast+
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have x0: "share_state_formed ?x0" and tf0: "table_formed ?Ts" using shared_entries_formed(3,4)[OF s] .
  have nf0: "node_entry_formed ?Ts q hn" using shared_entries_formed(2)[OF s at] .
  have ndf: "shared_derivation_formed ?Ts ?nd" and pos: "shared_derivation_position ?nd = q"
    using nf0 by (simp_all add: node_entry_formed_def)
  have cf: "shared_pattern_formed ?Ts ?c" and cc: "shared_collapsed ?c" using ndf by (simp_all add: shared_derivation_formed_def)
  have rf: "shared_pattern_formed ?Ts (binding_resolve ?S ?c)" by (rule binding_resolve_formed[OF S cf])
  obtain c' x1 where kc: "keyed_binding_resolve ?S ?c ?x0 = (c', x1)" by (cases "keyed_binding_resolve ?S ?c ?x0")
  have kc': "keyed_share_collapse (binding_resolve ?S ?c) ?x0 = (c', x1)"
    using kc keyed_binding_resolve_collapse[OF S cf cc, of ?x0] by simp
  have kb: "keyed_collapse_bindings [(undefined, binding_resolve ?S ?c)] ?x0 = ([(undefined, c')], x1)"
    using kc' by simp
  have col: "share_state_formed x1 \<and> table_extends ?Ts (share_state_table x1) \<and>
      shared_pattern_formed (share_state_table x1) c' \<and>
      shared_pattern_project (share_state_table x1) c' = shared_pattern_project ?Ts (binding_resolve ?S ?c) \<and>
      shared_collapsed c'"
    using keyed_collapse_bindings[OF x0, of "[(undefined, binding_resolve ?S ?c)]"] rf kb
    by (simp add: shared_bindings_formed_def shared_bindings_project_def)
  let ?T1 = "share_state_table x1"
  have x1: "share_state_formed x1" and ext: "table_extends ?Ts ?T1" and c'f: "shared_pattern_formed ?T1 c'"
    and c'p: "shared_pattern_project ?T1 c' = shared_pattern_project ?Ts (binding_resolve ?S ?c)"
    and c'c: "shared_collapsed c'" using col by simp_all
  have c'v: "shared_pattern_variables c' = {||}"
    using c'p shared_pattern_variables_project[OF c'f] shared_pattern_variables_project[OF rf] gr by simp
  let ?nd' = "deferred_ground_derivation ?S c' ?nd"
  have bf: "shared_pattern_formed ?T1 (binding_resolve ?S (snd z))" and
    bp: "shared_pattern_project ?T1 (binding_resolve ?S (snd z)) = shared_pattern_project ?Ts (binding_resolve ?S (snd z))"
    if "z |\<in>| shared_derivation_bindings ?nd" for z
  proof -
    have "shared_pattern_formed ?Ts (snd z)" using ndf that by (simp add: shared_derivation_formed_def)
    then have "shared_pattern_formed ?Ts (binding_resolve ?S (snd z))" by (rule binding_resolve_formed[OF S])
    then show "shared_pattern_formed ?T1 (binding_resolve ?S (snd z))"
      "shared_pattern_project ?T1 (binding_resolve ?S (snd z)) = shared_pattern_project ?Ts (binding_resolve ?S (snd z))"
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
  have eq: "deferred_ground_node q d = d\<lparr>deferred_inner := ?r'\<rparr>" by (simp add: deferred_ground_node_def at kc)
  have r': "search_formed \<kappa> P ?r'" by (rule search_update[OF r s2]) (simp_all add: tbl2 ext goals2)
  have K': "search_classes_formed ?r'"
    by (rule search_update_classes[OF r K r']) (simp_all add: tbl2 ext goals2 nodes2)
  have S': "binding_store_formed ?T1 ?S"
    using binding_store_formed_extended[OF S tf0] ext by (simp add: table_extends_def)
  show "\<exists>r'. deferred_ground_node q d = d\<lparr>deferred_inner := r'\<rparr>" using eq by blast
  show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground_node q d)))"
    using ext tbl2 eq by simp
  show "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p" using nodes2 eq by simp
  show "\<exists>hn'. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) q = Some hn' \<and>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}"
    using nodes2 eq c'v by (simp add: deferred_ground_derivation_def)
  have nodes': "RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) p \<noteq> None \<longleftrightarrow>
      RBT.lookup (shared_nodes ?s) p \<noteq> None" for p
    using nodes2 at eq by simp
  have goals': "RBT.lookup (shared_goals (search_state (deferred_inner (deferred_ground_node q d)))) p =
      RBT.lookup (shared_goals ?s) p" for p using goals2 eq by simp
  show "deferred_parts_formed \<kappa> P (deferred_ground_node q d)"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner (deferred_ground_node q d))" using r' eq by simp
    show "search_classes_formed (deferred_inner (deferred_ground_node q d))" using K' eq by simp
    show "positions_numbered (deferred_positions (deferred_ground_node q d))"
      using parts eq unfolding deferred_parts_formed_def by simp
    show "binding_store_formed (search_table (deferred_inner (deferred_ground_node q d))) (deferred_store (deferred_ground_node q d))"
      using S' tbl2 eq by simp
    show "\<forall>k v. RBT.lookup (snd (deferred_tree (deferred_ground_node q d))) k = Some v \<longrightarrow>
        (\<exists>x. deferred_numbered (deferred_ground_node q d) x \<and> deferred_key (deferred_ground_node q d) x = k)"
      using parts eq unfolding deferred_parts_formed_def by simp
    show "\<forall>x. binding_map (deferred_store (deferred_ground_node q d)) x \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) (fst (fst x)) \<noteq> None"
      using parts eq nodes' unfolding deferred_parts_formed_def by simp
    show "\<forall>q' h x. RBT.lookup (shared_goals (search_state (deferred_inner (deferred_ground_node q d)))) q' = Some h \<longrightarrow>
        x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store (deferred_ground_node q d)) x = None \<and>
        (RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) (fst (fst x)) \<noteq> None \<or>
          (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
      using parts eq nodes' goals' unfolding deferred_parts_formed_def by simp
    show "\<forall>n q' K. RBT.lookup (deferred_records (deferred_ground_node q d)) n = Some (q', K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions (deferred_ground_node q d)) q' \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) q' \<noteq> None"
      using parts eq nodes' unfolding deferred_parts_formed_def by simp
  qed
  show "deferred_node_formed (deferred_ground_node q d) q'" if ne: "q' \<noteq> q" and nf: "deferred_node_formed d q'" for q'
    using nf nodes2[of q'] ne eq unfolding deferred_node_formed_def by simp
  show "deferred_node_formed (deferred_ground_node q d) q"
    if n0: "position_number (deferred_positions d) q \<noteq> 0"
      and rec: "RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K)"
      and keys: "set (RBT.keys K) = {}" for K
  proof -
    have v': "shared_pattern_variables (binding_resolve ?S c') = {||}"
      using binding_resolve_unbound[of c' ?S] c'v by simp
    show ?thesis unfolding deferred_node_formed_def
      using n0 rec keys v' c'v nodes2[of q] eq by (simp add: deferred_ground_derivation_def)
  qed
  show "deferred_project (deferred_ground_node q d) = deferred_project d"
  proof -
    let ?\<sigma> = "deferred_substitution d"
    have \<sigma>': "deferred_substitution (deferred_ground_node q d) = ?\<sigma>"
    proof -
      have "shared_pattern_project ?T1 (binding_substitution ?S y) = shared_pattern_project ?Ts (binding_substitution ?S y)" for y
      proof -
        have "shared_pattern_formed ?Ts (binding_substitution ?S y)"
          unfolding binding_substitution_def by (rule binding_resolve_formed[OF S]) simp
        then show ?thesis using shared_pattern_extends(2)[OF tf0 _ ext] by blast
      qed
      then show ?thesis using eq tbl2 by (simp add: fun_eq_iff deferred_substitution_def)
    qed
    have \<sigma>eq: "?\<sigma> = (\<lambda>x. shared_pattern_project ?Ts (binding_substitution ?S x))"
      by (simp add: fun_eq_iff deferred_substitution_def)
    have old': "shared_derivation_project ?T1 ?nd' = shared_derivation_project ?Ts (derivation_resolve ?S ?nd)"
    proof -
      have "fimage (\<lambda>z. (fst z, shared_pattern_project ?T1 (binding_resolve ?S (snd z)))) (shared_derivation_bindings ?nd) =
          fimage (\<lambda>z. (fst z, shared_pattern_project ?Ts (binding_resolve ?S (snd z)))) (shared_derivation_bindings ?nd)"
        by (rule fset.map_cong0) (simp add: bp)
      then show ?thesis using c'p
        by (simp add: shared_derivation_project_def deferred_ground_derivation_def fset.map_comp comp_def)
    qed
    have old: "resolution_node_substitute ?\<sigma> (shared_derivation_project ?Ts ?nd) = shared_derivation_project ?T1 ?nd'"
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
      obtain p hp where hp: "RBT.lookup (shared_nodes ?s) p = Some hp" and xe: "x = shared_derivation_project ?Ts (shared_entry_node hp)"
        using xin unfolding shared_state_project_member(2) by blast
      have "shared_derivation_position (shared_entry_node hp) = p"
        using shared_entries_formed(2)[OF s hp] by (simp add: node_entry_formed_def)
      then have "p = q" using True xe by (simp add: shared_derivation_project_def)
      then have "x = shared_derivation_project ?Ts ?nd" using hp at xe by simp
      then show ?thesis using True fixed_new old k_def by simp
    qed (simp add: k_def)
    have kN: "fimage (resolution_node_substitute ?\<sigma>) (fimage k (resolution_nodes (search_project ?r))) =
        fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes (search_project ?r))"
      unfolding fset.map_comp by (rule fset.map_cong0) (simp add: kf)
    have \<sigma>'': "deferred_substitution (d\<lparr>deferred_inner := ?r'\<rparr>) = ?\<sigma>" using \<sigma>' eq by simp
    have "deferred_project (deferred_ground_node q d) = resolution_state_substitute ?\<sigma> (search_project ?r')"
      using \<sigma>'' eq by (simp add: deferred_project_def)
    also have "\<dots> = Resolution_State (fimage (resolution_goal_substitute ?\<sigma>) (resolution_pending (search_project ?r)))
        (fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes (search_project ?r))) (resolution_witnesses (search_project ?r))"
      unfolding pj resolution_state_substitute_def using kN by (simp add: fset.map_id)
    also have "\<dots> = deferred_project d" by (simp add: deferred_project_def resolution_state_substitute_def)
    finally show ?thesis .
  qed
qed

subsection \<open>Resolving a node memoizes every binding its resolution meets\<close>

text \<open>
  A node grounded is resolved after every bound variable its call reaches through the store is memoized
  (@{const store_memoize}, through the tree, @{text binding_tree_compress}): children first by the store's own ranks, so
  each binding is resolved once, meeting its children's references, whichever node of a chain is grounded first. The
  store stays a memoization of what it was (@{const store_memoized}); every other field but the inner search's table and
  sharing is kept, so every node's resolved call holds the variables it held and the projection is kept.
\<close>

definition deferred_memoize_at :: "('s,'a) resolution_variable \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_memoize_at x d = (case RBT.lookup (snd (deferred_tree d)) (deferred_key d x) of None \<Rightarrow> d
    | Some z \<Rightarrow> (case keyed_binding_resolve (deferred_store d) (snd z) (shared_sharing (search_state (deferred_inner d))) of
      (q, st') \<Rightarrow> d\<lparr>deferred_tree := binding_tree_compress (deferred_key d) (deferred_tree d) x q,
        deferred_inner := search_share st' (deferred_inner d)\<rparr>))"

function deferred_memoize_from :: "nat \<Rightarrow> nat \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) deferred_search"
  and deferred_memoize_list :: "nat \<Rightarrow> nat \<Rightarrow> ('s,'a) resolution_variable list \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_memoize_from n r x d = (case RBT.lookup (snd (deferred_tree d)) (deferred_key d x) of None \<Rightarrow> d
    | Some z \<Rightarrow> if r \<le> fst z \<and> fst z < n
      then deferred_memoize_at x (deferred_memoize_list n (Suc (fst z)) (shared_variable_list (snd z)) d) else d)"
| "deferred_memoize_list n r [] d = d"
| "deferred_memoize_list n r (y # ys) d = deferred_memoize_list n r ys (deferred_memoize_from n r y d)"
  by pat_completeness auto
termination by (relation "measures [\<lambda>p. case p of Inl (n, r, x, d) \<Rightarrow> n - r | Inr (n, r, ys, d) \<Rightarrow> n - r,
    \<lambda>p. case p of Inl _ \<Rightarrow> 0 | Inr (n, r, ys, d) \<Rightarrow> Suc (length ys)]") auto

definition deferred_memoize_node :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_memoize_node q d = (case RBT.lookup (shared_nodes (search_state (deferred_inner d))) q of None \<Rightarrow> d
    | Some hn \<Rightarrow> deferred_memoize_list (fst (deferred_tree d)) 0
        (shared_variable_list (shared_derivation_call (shared_entry_node hn))) d)"

definition deferred_ground :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_ground q d = deferred_ground_node q (deferred_memoize_node q d)"

definition deferred_memoized :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> bool" where
  "deferred_memoized d d' \<longleftrightarrow> store_memoized (search_table (deferred_inner d)) (deferred_store d)
      (search_table (deferred_inner d')) (deferred_store d') \<and>
    deferred_positions d' = deferred_positions d \<and> deferred_names d' = deferred_names d \<and>
    deferred_records d' = deferred_records d \<and> deferred_holders d' = deferred_holders d \<and>
    shared_nodes (search_state (deferred_inner d')) = shared_nodes (search_state (deferred_inner d)) \<and>
    shared_goals (search_state (deferred_inner d')) = shared_goals (search_state (deferred_inner d)) \<and>
    search_project (deferred_inner d') = search_project (deferred_inner d)"

lemma deferred_memoized_refl:
  assumes parts: "deferred_parts_formed \<kappa> P d"
  shows "deferred_memoized d d"
proof -
  have S: "binding_store_formed (search_table (deferred_inner d)) (deferred_store d)"
    and r: "search_formed \<kappa> P (deferred_inner d)" using parts unfolding deferred_parts_formed_def by blast+
  have tf: "table_formed (search_table (deferred_inner d))" using shared_entries_formed(4)[OF search_formedD(1)[OF r]] .
  show ?thesis using store_memoized_refl[OF S tf] by (simp add: deferred_memoized_def)
qed

lemma deferred_memoized_trans:
  assumes parts: "deferred_parts_formed \<kappa> P d" and m1: "deferred_memoized d d1" and m2: "deferred_memoized d1 d2"
  shows "deferred_memoized d d2"
proof -
  have r: "search_formed \<kappa> P (deferred_inner d)" using parts unfolding deferred_parts_formed_def by blast
  have tf: "table_formed (search_table (deferred_inner d))" using shared_entries_formed(4)[OF search_formedD(1)[OF r]] .
  have sm1: "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner d1)) (deferred_store d1)"
    using m1 by (simp add: deferred_memoized_def)
  have sm2: "store_memoized (search_table (deferred_inner d1)) (deferred_store d1) (search_table (deferred_inner d2)) (deferred_store d2)"
    using m2 by (simp add: deferred_memoized_def)
  have "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner d2)) (deferred_store d2)"
    by (rule store_memoized_trans[OF sm1 sm2 tf])
  then show ?thesis using m1 m2 by (simp add: deferred_memoized_def)
qed

lemma deferred_memoized_extends:
  "deferred_memoized d d' \<Longrightarrow> table_extends (search_table (deferred_inner d)) (search_table (deferred_inner d'))"
  by (simp add: deferred_memoized_def store_memoized_def table_extends_def)

text \<open>The parts' clauses read the store only through its bound variables and the tree only through its keys.\<close>

lemma deferred_parts_transfer:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and r: "search_formed \<kappa> P (deferred_inner d')" and K: "search_classes_formed (deferred_inner d')"
    and fields: "deferred_positions d' = deferred_positions d" "deferred_names d' = deferred_names d"
      "deferred_records d' = deferred_records d"
    and nodes: "shared_nodes (search_state (deferred_inner d')) = shared_nodes (search_state (deferred_inner d))"
    and goals: "shared_goals (search_state (deferred_inner d')) = shared_goals (search_state (deferred_inner d))"
    and S: "binding_store_formed (search_table (deferred_inner d')) (deferred_store d')"
    and keys: "\<And>k v. RBT.lookup (snd (deferred_tree d')) k = Some v \<Longrightarrow> RBT.lookup (snd (deferred_tree d)) k \<noteq> None"
    and dom: "\<And>x. binding_map (deferred_store d') x = None \<longleftrightarrow> binding_map (deferred_store d) x = None"
  shows "deferred_parts_formed \<kappa> P d'"
proof -
  have key: "deferred_key d' = deferred_key d" using fields by (simp add: fun_eq_iff deferred_key_def)
  have num: "deferred_numbered d' = deferred_numbered d" using fields by (simp add: fun_eq_iff deferred_numbered_def)
  have tk: "\<forall>k v. RBT.lookup (snd (deferred_tree d')) k = Some v \<longrightarrow> (\<exists>x. deferred_numbered d' x \<and> deferred_key d' x = k)"
  proof (intro allI impI)
    fix k v assume "RBT.lookup (snd (deferred_tree d')) k = Some v"
    then obtain v' where "RBT.lookup (snd (deferred_tree d)) k = Some v'" using keys by blast
    then obtain y where "deferred_numbered d y" "deferred_key d y = k" using parts unfolding deferred_parts_formed_def by blast
    then show "\<exists>x. deferred_numbered d' x \<and> deferred_key d' x = k" unfolding key num by blast
  qed
  have bound: "\<forall>x. binding_map (deferred_store d') x \<noteq> None \<longrightarrow>
      RBT.lookup (shared_nodes (search_state (deferred_inner d'))) (fst (fst x)) \<noteq> None"
    using parts dom nodes unfolding deferred_parts_formed_def by simp
  have gl: "\<forall>q h x. RBT.lookup (shared_goals (search_state (deferred_inner d'))) q = Some h \<longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store d') x = None \<and>
      (RBT.lookup (shared_nodes (search_state (deferred_inner d'))) (fst (fst x)) \<noteq> None \<or>
        (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
    using parts dom nodes goals unfolding deferred_parts_formed_def by simp
  have rc: "\<forall>n q K. RBT.lookup (deferred_records d') n = Some (q, K) \<longrightarrow> n \<noteq> 0 \<and>
      n = position_number (deferred_positions d') q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d'))) q \<noteq> None"
    using parts fields nodes unfolding deferred_parts_formed_def by simp
  have N: "positions_numbered (deferred_positions d')" using parts fields unfolding deferred_parts_formed_def by simp
  show ?thesis unfolding deferred_parts_formed_def using r K N S tk bound gl rc by blast
qed

lemma deferred_memoize_at:
  assumes parts: "deferred_parts_formed \<kappa> P d"
  shows "deferred_parts_formed \<kappa> P (deferred_memoize_at x d) \<and> deferred_memoized d (deferred_memoize_at x d)"
proof (cases "RBT.lookup (snd (deferred_tree d)) (deferred_key d x)")
  case None
  then show ?thesis using parts deferred_memoized_refl[OF parts] by (simp add: deferred_memoize_at_def)
next
  case (Some z)
  obtain ra qa where z: "z = (ra, qa)" by (cases z)
  let ?r = "deferred_inner d" let ?T = "search_table ?r" let ?S = "deferred_store d"
  let ?x0 = "shared_sharing (search_state ?r)"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" and N: "positions_numbered (deferred_positions d)"
    and S: "binding_store_formed ?T ?S" using parts unfolding deferred_parts_formed_def by blast+
  have s: "shared_state_formed \<kappa> P (search_state ?r)" using search_formedD(1)[OF r] .
  have x0: "share_state_formed ?x0" and tf: "table_formed ?T" using shared_entries_formed(3,4)[OF s] .
  have from_key: "deferred_numbered d y" if "deferred_numbered d y'" "deferred_key d y' = deferred_key d y" for y y'
    using that by (auto simp: deferred_numbered_def deferred_key_def)
  have numx: "deferred_numbered d x"
  proof -
    obtain y where "deferred_numbered d y" "deferred_key d y = deferred_key d x"
      using parts Some unfolding deferred_parts_formed_def by blast
    then show ?thesis by (rule from_key)
  qed
  have kinj: "b = x" if "deferred_key d b = deferred_key d x" for b
    using deferred_key_inj[OF N from_key[OF numx that[symmetric]] numx that] .
  have a: "binding_map ?S x = Some (ra, qa)" using Some z by (simp add: deferred_store_def binding_tree_store_def)
  have qa: "shared_pattern_formed ?T qa" "shared_collapsed qa" using binding_store_formedD(3)[OF S] a by blast+
  obtain q st' where kc: "keyed_binding_resolve ?S qa ?x0 = (q, st')" by (cases "keyed_binding_resolve ?S qa ?x0")
  have kc': "keyed_share_collapse (binding_resolve ?S qa) ?x0 = (q, st')"
    using kc keyed_binding_resolve_collapse[OF S qa, of ?x0] by simp
  have kb: "keyed_collapse_bindings [(undefined, binding_resolve ?S qa)] ?x0 = ([(undefined, q)], st')" using kc' by simp
  have rf: "shared_pattern_formed ?T (binding_resolve ?S qa)" by (rule binding_resolve_formed[OF S qa(1)])
  have col: "share_state_formed st' \<and> table_extends ?T (share_state_table st') \<and>
      shared_pattern_formed (share_state_table st') q \<and>
      shared_pattern_project (share_state_table st') q = shared_pattern_project ?T (binding_resolve ?S qa) \<and>
      shared_collapsed q"
    using keyed_collapse_bindings[OF x0, of "[(undefined, binding_resolve ?S qa)]"] rf kb
    by (simp add: shared_bindings_formed_def shared_bindings_project_def)
  let ?T1 = "share_state_table st'"
  have xf: "share_state_formed st'" and extx: "table_extends ?T ?T1" and qf: "shared_pattern_formed ?T1 q"
    and qp: "shared_pattern_project ?T1 q = shared_pattern_project ?T (binding_resolve ?S qa)" and qc: "shared_collapsed q"
    using col by simp_all
  have ext: "\<forall>i u. reference_term ?T i = Some u \<longrightarrow> reference_term ?T1 i = Some u" using extx by (simp add: table_extends_def)
  have tf1: "table_formed ?T1" using xf by (simp add: share_state_formed_def)
  have qv: "shared_pattern_variables q = shared_pattern_variables (binding_resolve ?S qa)"
    using qp shared_pattern_variables_project[OF qf] shared_pattern_variables_project[OF rf] by simp
  have unbound: "\<forall>b. b |\<in>| shared_pattern_variables q \<longrightarrow> binding_map ?S b = None"
    using binding_resolve_variables[OF S qa(1)] qv by auto
  have Sc: "binding_store_formed ?T1 (store_compress ?S x q)" by (rule store_compress_formed[OF S a tf ext qf qc unbound])
  have Rc: "\<forall>p. shared_pattern_formed ?T p \<longrightarrow>
      shared_pattern_project ?T1 (binding_resolve (store_compress ?S x q) p) = shared_pattern_project ?T (binding_resolve ?S p)"
    using store_compress_resolve[OF S a tf ext unbound qp] by blast
  let ?m = "d\<lparr>deferred_tree := binding_tree_compress (deferred_key d) (deferred_tree d) x q,
    deferred_inner := search_share st' ?r\<rparr>"
  have m: "deferred_memoize_at x d = ?m" by (simp add: deferred_memoize_at_def Some z kc)
  have rank_m: "binding_next_rank (deferred_store ?m) = binding_next_rank (store_compress ?S x q)"
    using Some z by (simp add: deferred_store_def binding_tree_store_def binding_tree_compress_def store_compress_def)
  have map_m: "binding_map (deferred_store ?m) = binding_map (store_compress ?S x q)"
  proof (rule HOL.ext)
    fix b
    show "binding_map (deferred_store ?m) b = binding_map (store_compress ?S x q) b"
    proof (cases "b = x")
      case True
      then show ?thesis using Some z a
        by (simp add: deferred_store_def binding_tree_store_def binding_tree_compress_def store_compress_def RBT.lookup_insert
            deferred_key_def)
    next
      case False
      then have "deferred_key d b \<noteq> deferred_key d x" using kinj by blast
      then show ?thesis using Some z False
        by (auto simp: deferred_store_def binding_tree_store_def binding_tree_compress_def store_compress_def RBT.lookup_insert
            deferred_key_def)
    qed
  qed
  have store_m: "deferred_store ?m = store_compress ?S x q"
    by (rule binding_store.equality) (simp only: rank_m, simp only: map_m, simp)
  note sh = search_share[OF r xf extx]
  have dom: "binding_map (deferred_store ?m) b = None \<longleftrightarrow> binding_map ?S b = None" for b
    using a store_m by (simp add: store_compress_def)
  have keys: "RBT.lookup (snd (deferred_tree d)) k \<noteq> None" if "RBT.lookup (snd (deferred_tree ?m)) k = Some v" for k v
    using that Some z by (auto simp: binding_tree_compress_def RBT.lookup_insert split: if_splits)
  have parts_m: "deferred_parts_formed \<kappa> P ?m"
    by (rule deferred_parts_transfer[OF parts]) (use sh search_share_classes[OF r xf extx K] Sc store_m dom keys in simp_all)
  have sm: "store_memoized ?T ?S ?T1 (deferred_store ?m)"
    using tf1 ext Sc Rc dom a store_m unfolding store_memoized_def by (simp add: store_compress_def)
  show ?thesis unfolding m using parts_m sm sh by (simp add: deferred_memoized_def)
qed

lemma deferred_memoize:
  shows "deferred_parts_formed \<kappa> P d \<Longrightarrow>
      deferred_parts_formed \<kappa> P (deferred_memoize_from n r x d) \<and> deferred_memoized d (deferred_memoize_from n r x d)"
    and "deferred_parts_formed \<kappa> P d \<Longrightarrow>
      deferred_parts_formed \<kappa> P (deferred_memoize_list n r xs d) \<and> deferred_memoized d (deferred_memoize_list n r xs d)"
proof (induction n r x d and n r xs d rule: deferred_memoize_from_deferred_memoize_list.induct)
  case (1 n r x d)
  note pd = 1(2)
  show ?case
  proof (cases "RBT.lookup (snd (deferred_tree d)) (deferred_key d x)")
    case None
    then have e: "deferred_memoize_from n r x d = d" by simp
    show ?thesis unfolding e using pd deferred_memoized_refl[OF pd] by simp
  next
    case (Some z)
    show ?thesis
    proof (cases "r \<le> fst z \<and> fst z < n")
      case True
      let ?l = "deferred_memoize_list n (Suc (fst z)) (shared_variable_list (snd z)) d"
      have e: "deferred_memoize_from n r x d = deferred_memoize_at x ?l" using Some True by simp
      have l: "deferred_parts_formed \<kappa> P ?l \<and> deferred_memoized d ?l" using 1(1)[OF Some True pd] .
      note A = deferred_memoize_at[OF conjunct1[OF l], of x]
      have "deferred_memoized d (deferred_memoize_at x ?l)"
        by (rule deferred_memoized_trans[OF pd conjunct2[OF l] conjunct2[OF A]])
      then show ?thesis unfolding e using A by simp
    next
      case False
      then have e: "deferred_memoize_from n r x d = d" using Some by auto
      show ?thesis unfolding e using pd deferred_memoized_refl[OF pd] by simp
    qed
  qed
next
  case (2 n r d)
  then show ?case using deferred_memoized_refl[OF 2] by simp
next
  case (3 n r y ys d)
  have A: "deferred_parts_formed \<kappa> P (deferred_memoize_from n r y d) \<and> deferred_memoized d (deferred_memoize_from n r y d)"
    using 3 by blast
  have B: "deferred_parts_formed \<kappa> P (deferred_memoize_list n r ys (deferred_memoize_from n r y d)) \<and>
      deferred_memoized (deferred_memoize_from n r y d) (deferred_memoize_list n r ys (deferred_memoize_from n r y d))"
    using 3 A by blast
  show ?case using B deferred_memoized_trans[OF 3(3) conjunct2[OF A] conjunct2[OF B]] by simp
qed

lemma deferred_memoize_node:
  assumes parts: "deferred_parts_formed \<kappa> P d"
  shows "deferred_parts_formed \<kappa> P (deferred_memoize_node q d) \<and> deferred_memoized d (deferred_memoize_node q d)"
  using parts deferred_memoize(2)[OF parts] deferred_memoized_refl[OF parts]
  by (simp add: deferred_memoize_node_def split: option.splits)

lemma deferred_memoized_transfer:
  assumes parts: "deferred_parts_formed \<kappa> P d" and m: "deferred_memoized d d'"
  shows "\<And>q hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<Longrightarrow>
      shared_pattern_variables (deferred_call d' hn) = shared_pattern_variables (deferred_call d hn)"
    and "\<And>q. deferred_node_formed d q \<Longrightarrow> deferred_node_formed d' q"
    and "deferred_project d' = deferred_project d"
proof -
  let ?r = "deferred_inner d" let ?T = "search_table ?r" let ?S = "deferred_store d"
  have r: "search_formed \<kappa> P ?r" and S: "binding_store_formed ?T ?S" using parts unfolding deferred_parts_formed_def by blast+
  have s: "shared_state_formed \<kappa> P (search_state ?r)" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have sm: "store_memoized ?T ?S (search_table (deferred_inner d')) (deferred_store d')"
    using m by (simp add: deferred_memoized_def)
  show v: "shared_pattern_variables (deferred_call d' hn) = shared_pattern_variables (deferred_call d hn)"
    if at: "RBT.lookup (shared_nodes (search_state ?r)) q = Some hn" for q hn
  proof -
    have "shared_pattern_formed ?T (shared_derivation_call (shared_entry_node hn))"
      using shared_entries_formed(2)[OF s at] by (simp add: node_entry_formed_def shared_derivation_formed_def)
    then show ?thesis by (rule store_memoized_variables[OF sm S tf])
  qed
  have key: "deferred_key d' = deferred_key d" using m by (simp add: fun_eq_iff deferred_key_def deferred_memoized_def)
  have num: "deferred_numbered d' = deferred_numbered d" using m by (simp add: fun_eq_iff deferred_numbered_def deferred_memoized_def)
  show "deferred_node_formed d' q" if nf: "deferred_node_formed d q" for q
    unfolding deferred_node_formed_def
  proof (intro allI impI)
    fix hn assume at': "RBT.lookup (shared_nodes (search_state (deferred_inner d'))) q = Some hn"
    have at: "RBT.lookup (shared_nodes (search_state ?r)) q = Some hn" using at' m by (simp add: deferred_memoized_def)
    note D = deferred_node_formedD[OF nf at]
    show "position_number (deferred_positions d') q \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records d') (position_number (deferred_positions d') q) = Some (q, K) \<and>
        set (RBT.keys K) = deferred_key d' ` fset (shared_pattern_variables (deferred_call d' hn))) \<and>
      fBall (shared_pattern_variables (deferred_call d' hn)) (deferred_numbered d') \<and>
      fBall (shared_pattern_variables (deferred_call d' hn))
        (\<lambda>x. position_number (deferred_positions d') q |\<in>| tree_bucket (deferred_holders d') (deferred_key d' x)) \<and>
      (shared_pattern_variables (deferred_call d' hn) = {||} \<longrightarrow>
        shared_pattern_variables (shared_derivation_call (shared_entry_node hn)) = {||})"
      using D v[OF at] key num m by (simp add: deferred_memoized_def)
  qed
  have sub: "deferred_substitution d' = deferred_substitution d"
  proof (rule ext)
    fix x
    show "deferred_substitution d' x = deferred_substitution d x"
      using sm by (simp add: deferred_substitution_def binding_substitution_def store_memoized_def)
  qed
  show "deferred_project d' = deferred_project d" using sub m by (simp add: deferred_project_def deferred_memoized_def)
qed

text \<open>
  The ground step: its store a memoization of the one it had, its inner search changed, and the other fields kept, the
  rest as @{thm [source] deferred_ground_node} states it.
\<close>

lemma deferred_memoize_kept:
  shows "deferred_positions (deferred_memoize_from n r x d) = deferred_positions d \<and>
      deferred_names (deferred_memoize_from n r x d) = deferred_names d \<and>
      deferred_goal_records (deferred_memoize_from n r x d) = deferred_goal_records d \<and>
      shared_goals (search_state (deferred_inner (deferred_memoize_from n r x d))) = shared_goals (search_state (deferred_inner d))"
    and "deferred_positions (deferred_memoize_list n r xs d) = deferred_positions d \<and>
      deferred_names (deferred_memoize_list n r xs d) = deferred_names d \<and>
      deferred_goal_records (deferred_memoize_list n r xs d) = deferred_goal_records d \<and>
      shared_goals (search_state (deferred_inner (deferred_memoize_list n r xs d))) = shared_goals (search_state (deferred_inner d))"
  by (induction n r x d and n r xs d rule: deferred_memoize_from_deferred_memoize_list.induct)
    (auto simp: deferred_memoize_at_def search_share_def shared_reshare_def split: option.splits prod.splits)

lemma deferred_ground_kept:
  "deferred_positions (deferred_ground q d) = deferred_positions d"
  "deferred_names (deferred_ground q d) = deferred_names d"
  "deferred_goal_records (deferred_ground q d) = deferred_goal_records d"
  "RBT.lookup (shared_goals (search_state (deferred_inner (deferred_ground q d)))) p =
    RBT.lookup (shared_goals (search_state (deferred_inner d))) p"
  by (simp_all add: deferred_ground_def deferred_ground_node_def deferred_memoize_node_def deferred_memoize_kept
      shared_put_node_def shared_replace_def shared_reshare_def search_update_def split: option.splits prod.splits)

lemma deferred_memoize_node_goal_records: "deferred_goal_records (deferred_memoize_node q d) = deferred_goal_records d"
  by (simp add: deferred_memoize_node_def deferred_memoize_kept split: option.split)

theorem deferred_ground:
  assumes parts: "deferred_parts_formed \<kappa> P d"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
    and gr: "shared_pattern_variables (deferred_call d hn) = {||}"
  shows "deferred_parts_formed \<kappa> P (deferred_ground q d)"
    and "\<exists>r' K'. deferred_ground q d = d\<lparr>deferred_inner := r', deferred_tree := K'\<rparr> \<and>
      store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table r')
        (deferred_store (d\<lparr>deferred_inner := r', deferred_tree := K'\<rparr>))"
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
  let ?m = "deferred_memoize_node q d"
  note M = deferred_memoize_node[OF parts, of q]
  have pm: "deferred_parts_formed \<kappa> P ?m" and mm: "deferred_memoized d ?m" using M by simp_all
  note T = deferred_memoized_transfer[OF parts mm]
  have mf: "deferred_positions ?m = deferred_positions d" "deferred_names ?m = deferred_names d"
    "deferred_records ?m = deferred_records d" "deferred_holders ?m = deferred_holders d"
    "shared_nodes (search_state (deferred_inner ?m)) = shared_nodes (search_state (deferred_inner d))"
    using mm by (simp_all add: deferred_memoized_def)
  have atm: "RBT.lookup (shared_nodes (search_state (deferred_inner ?m))) q = Some hn" using at mf(5) by simp
  have grm: "shared_pattern_variables (deferred_call ?m hn) = {||}" using T(1)[OF at] gr by simp
  note G = deferred_ground_node[OF pm atm grm]
  have eq: "deferred_ground q d = deferred_ground_node q ?m" by (simp add: deferred_ground_def)
  have md0: "?m = d\<lparr>deferred_inner := deferred_inner ?m, deferred_tree := deferred_tree ?m\<rparr>"
    using mf(1-4) deferred_memoize_node_goal_records[of q d] by simp
  obtain r0 K0 where md: "?m = d\<lparr>deferred_inner := r0, deferred_tree := K0\<rparr>" using md0 by blast
  obtain r' where e: "deferred_ground_node q ?m = ?m\<lparr>deferred_inner := r'\<rparr>" using G(2) by blast
  have e': "deferred_ground q d = d\<lparr>deferred_inner := r', deferred_tree := K0\<rparr>" using eq e md by simp
  have r'f: "search_formed \<kappa> P r'" using G(1) e by (simp add: deferred_parts_formed_def)
  have tf': "table_formed (search_table r')" using shared_entries_formed(4)[OF search_formedD(1)[OF r'f]] .
  have Sm: "binding_store_formed (search_table (deferred_inner ?m)) (deferred_store ?m)"
    using pm unfolding deferred_parts_formed_def by blast
  have rm: "search_formed \<kappa> P (deferred_inner ?m)" using pm unfolding deferred_parts_formed_def by blast
  have tfm: "table_formed (search_table (deferred_inner ?m))" using shared_entries_formed(4)[OF search_formedD(1)[OF rm]] .
  have x2: "\<forall>i u. reference_term (search_table (deferred_inner ?m)) i = Some u \<longrightarrow> reference_term (search_table r') i = Some u"
    using G(8) e by (simp add: table_extends_def)
  have sm2: "store_memoized (search_table (deferred_inner ?m)) (deferred_store ?m) (search_table r') (deferred_store ?m)"
    by (rule store_memoized_extended[OF Sm tfm tf' x2])
  have r: "search_formed \<kappa> P (deferred_inner d)" using parts unfolding deferred_parts_formed_def by blast
  have tf: "table_formed (search_table (deferred_inner d))" using shared_entries_formed(4)[OF search_formedD(1)[OF r]] .
  have sm1: "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner ?m)) (deferred_store ?m)"
    using mm by (simp add: deferred_memoized_def)
  have kk: "\<And>r K. deferred_key (d\<lparr>deferred_inner := r, deferred_tree := K\<rparr>) = deferred_key d"
    by (simp add: fun_eq_iff deferred_key_def)
  have st': "deferred_store (d\<lparr>deferred_inner := r', deferred_tree := K0\<rparr>) = deferred_store ?m"
    by (simp add: md deferred_store_def kk)
  show "\<exists>r' K'. deferred_ground q d = d\<lparr>deferred_inner := r', deferred_tree := K'\<rparr> \<and>
      store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table r')
        (deferred_store (d\<lparr>deferred_inner := r', deferred_tree := K'\<rparr>))"
    by (intro exI[of _ r'] exI[of _ K0]) (simp add: e' st' store_memoized_trans[OF sm1 sm2 tf])
  show "deferred_parts_formed \<kappa> P (deferred_ground q d)" using G(1) eq by simp
  show "RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p" if "p \<noteq> q" for p
    using G(3)[OF that] eq mf(5) by simp
  show "\<exists>hn'. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) q = Some hn' \<and>
      shared_pattern_variables (shared_derivation_call (shared_entry_node hn')) = {||}" using G(4) eq by simp
  show "deferred_node_formed (deferred_ground q d) q'" if "q' \<noteq> q" "deferred_node_formed d q'" for q'
    using G(5)[OF that(1) T(2)[OF that(2)]] eq by simp
  show "deferred_node_formed (deferred_ground q d) q"
    if "position_number (deferred_positions d) q \<noteq> 0"
      "RBT.lookup (deferred_records d) (position_number (deferred_positions d) q) = Some (q, K)" "set (RBT.keys K) = {}"
    using G(6)[of K] that mf eq by simp
  show "deferred_project (deferred_ground q d) = deferred_project d" using G(7) T(3) eq by simp
  show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground q d)))"
    using table_extends_trans[OF deferred_memoized_extends[OF mm] G(8)] eq by simp
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
    fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn)))) (deferred_numbered d) \<and>
    fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn))))
      (\<lambda>x. position_number (deferred_positions d) q |\<in>| tree_bucket (deferred_holders d) (deferred_key d x)))"

text \<open>
  D3a (task 977): the update reads the domain's keys, not the record's. The keys of the domain and of each image's
  variables are computed once for the unifier (@{text deferred_domain_keys}); at a record holding one of the domain's
  keys those keys are removed and their images' keys inserted, the node added to the holders of the inserted keys only
  (the record's other keys already hold it), and no key is decoded. A nonempty record holding none of the domain's keys
  is left as it is.
\<close>

definition deferred_domain_keys :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    (deferred_key \<times> deferred_key list) list" where
  "deferred_domain_keys d \<sigma> D = sorted_list_of_fset
    (fimage (\<lambda>a. (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))) D)"

definition deferred_record_update :: "(deferred_key \<times> deferred_key list) list \<Rightarrow> (deferred_key, unit) rbt \<Rightarrow>
    (deferred_key, unit) rbt \<times> deferred_key list" where
  "deferred_record_update Dk K = (let H = filter (\<lambda>y. RBT.lookup K (fst y) \<noteq> None) Dk; I = concat (map snd H) in
    (fold (\<lambda>k t. RBT.insert k () t) I (fold (\<lambda>y t. RBT.delete (fst y) t) H K), I))"

definition deferred_record_put :: "nat \<Rightarrow> 's::linorder list \<Rightarrow> (deferred_key, unit) rbt \<Rightarrow> deferred_key fset \<Rightarrow>
    ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_record_put n q K X d = d\<lparr>deferred_records := RBT.insert n (q, K) (deferred_records d),
    deferred_holders := tree_add n X (deferred_holders d)\<rparr>"

definition deferred_update_at :: "(deferred_key \<times> deferred_key list) list \<Rightarrow> nat \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_update_at Dk n d = (case RBT.lookup (deferred_records d) n of None \<Rightarrow> d | Some z \<Rightarrow>
    if \<not> RBT.is_empty (snd z) \<and> list_all (\<lambda>y. RBT.lookup (snd z) (fst y) = None) Dk then d else
    (case deferred_record_update Dk (snd z) of (K', I) \<Rightarrow>
      let d1 = deferred_record_put n (fst z) K' (fset_of_list I) d in
      if RBT.is_empty K' then deferred_ground (fst z) d1 else d1))"

definition deferred_update :: "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> nat \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_update \<sigma> D n d = deferred_update_at (deferred_domain_keys d \<sigma> D) n d"

lemma fold_delete_keys: "set (RBT.keys (fold (\<lambda>y t. RBT.delete (f y) t) ys t)) = set (RBT.keys t) - f ` set ys"
proof -
  have "dom (RBT.lookup (fold (\<lambda>y t. RBT.delete (f y) t) ys t)) = dom (RBT.lookup t) - f ` set ys"
    by (induction ys arbitrary: t) auto
  then show ?thesis by (simp add: RBT.lookup_keys)
qed

lemma rbt_is_empty_keys: "RBT.is_empty K \<longleftrightarrow> set (RBT.keys K) = {}"
proof -
  have "RBT.is_empty K \<longleftrightarrow> RBT.lookup K = Map.empty" by simp
  also have "\<dots> \<longleftrightarrow> dom (RBT.lookup K) = {}" by auto
  finally show ?thesis by (simp add: RBT.lookup_keys)
qed

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

lemma deferred_record_at_goal_records [simp]:
  "deferred_goal_records (deferred_record_at n q ks d) = deferred_goal_records d"
  by (simp add: deferred_record_at_def)

lemma deferred_record_put_fields [simp]:
  "deferred_inner (deferred_record_put n q K X d) = deferred_inner d"
  "deferred_tree (deferred_record_put n q K X d) = deferred_tree d"
  "deferred_positions (deferred_record_put n q K X d) = deferred_positions d"
  "deferred_names (deferred_record_put n q K X d) = deferred_names d"
  "deferred_goal_records (deferred_record_put n q K X d) = deferred_goal_records d"
  "deferred_records (deferred_record_put n q K X d) = RBT.insert n (q, K) (deferred_records d)"
  "deferred_holders (deferred_record_put n q K X d) = tree_add n X (deferred_holders d)"
  by (simp_all add: deferred_record_put_def)

lemma deferred_record_put_key [simp]: "deferred_key (deferred_record_put n q K X d) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def)

lemma deferred_record_put_store [simp]:
  "deferred_numbered (deferred_record_put n q K X d) = deferred_numbered d"
  "deferred_store (deferred_record_put n q K X d) = deferred_store d"
  by (simp_all add: fun_eq_iff deferred_numbered_def deferred_store_def)

lemma deferred_record_put_project [simp]: "deferred_project (deferred_record_put n q K X d) = deferred_project d"
  by (simp add: deferred_project_def deferred_substitution_def[abs_def])

lemma deferred_record_put_parts:
  assumes parts: "deferred_parts_formed \<kappa> P d" and n: "n \<noteq> 0" "n = position_number (deferred_positions d) q"
    and at: "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None"
  shows "deferred_parts_formed \<kappa> P (deferred_record_put n q K X d)"
proof -
  have b: "\<And>n' q' K'. RBT.lookup (deferred_records d) n' = Some (q', K') \<Longrightarrow> n' \<noteq> 0 \<and>
      n' = position_number (deferred_positions d) q' \<and> RBT.lookup (shared_nodes (search_state (deferred_inner d))) q' \<noteq> None"
    using parts unfolding deferred_parts_formed_def by blast
  have rc: "\<forall>n' q' K'. RBT.lookup (deferred_records (deferred_record_put n q K X d)) n' = Some (q', K') \<longrightarrow> n' \<noteq> 0 \<and>
      n' = position_number (deferred_positions (deferred_record_put n q K X d)) q' \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_put n q K X d)))) q' \<noteq> None"
  proof (intro allI impI)
    fix n' q' K' assume "RBT.lookup (deferred_records (deferred_record_put n q K X d)) n' = Some (q', K')"
    then show "n' \<noteq> 0 \<and> n' = position_number (deferred_positions (deferred_record_put n q K X d)) q' \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_record_put n q K X d)))) q' \<noteq> None"
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
    and st: "store_memoized T0 (store_bind S \<sigma> D) (search_table (deferred_inner d)) (deferred_store d)"
    and num: "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and rec: "RBT.lookup (deferred_records d) n = Some (q, K)"
    and stale: "deferred_node_stale S d q"
    and tf0: "table_formed T0" and S0: "binding_store_formed T0 (store_bind S \<sigma> D)"
    and c0: "\<forall>hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<longrightarrow>
      shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))"
  shows "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d)"
    and "deferred_node_formed (deferred_update \<sigma> D n d) q"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q'"
    and "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_stale S d q' \<Longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q'"
    and "deferred_project (deferred_update \<sigma> D n d) = deferred_project d"
    and "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner (deferred_update \<sigma> D n d))) (deferred_store (deferred_update \<sigma> D n d))"
    and "deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d"
    and "deferred_names (deferred_update \<sigma> D n d) = deferred_names d"
    and "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
    and "\<And>n'. n' \<noteq> n \<Longrightarrow> RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n' = RBT.lookup (deferred_records d) n'"
    and "\<exists>K'. RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n = Some (q, K')"
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
    and holdV: "\<And>x. x |\<in>| ?V \<Longrightarrow> n |\<in>| tree_bucket (deferred_holders d) (deferred_key d x)"
    using stale at rec nq unfolding deferred_node_stale_def by auto
  have V': "x |\<in>| ?V' \<longleftrightarrow> x |\<in>| ?V \<and> x |\<notin>| D \<or> (\<exists>a. a |\<in>| ?V \<and> a |\<in>| D \<and> x |\<in>| shared_pattern_variables (\<sigma> a))" for x
    using store_bind_variables[OF S ready cf] store_memoized_variables[OF st S0 tf0 c0[rule_format, OF at]] by simp
  have \<sigma>f: "\<And>a. a |\<in>| D \<Longrightarrow> shared_pattern_formed ?T (\<sigma> a)" using ready unfolding unifier_ready_def by blast
  have \<sigma>vl: "set (shared_variable_list (\<sigma> a)) = fset (shared_pattern_variables (\<sigma> a))" if "a |\<in>| D" for a
    by (rule shared_variable_list[OF \<sigma>f[OF that]])
  have inK: "RBT.lookup K (deferred_key d a) \<noteq> None \<longleftrightarrow> a |\<in>| ?V" for a
  proof
    assume "RBT.lookup K (deferred_key d a) \<noteq> None"
    then have "deferred_key d a \<in> set (RBT.keys K)" by (simp add: RBT.lookup_keys[symmetric] domIff)
    then obtain x where x: "x |\<in>| ?V" "deferred_key d x = deferred_key d a" unfolding keysK by auto
    have an: "deferred_numbered d a"
    proof (rule ccontr)
      assume "\<not> deferred_numbered d a"
      then show False using deferred_key_zero[of d a x] numV[OF x(1)] x(2) by simp
    qed
    have "x = a" using deferred_key_inj[OF N numV[OF x(1)] an] x(2) by blast
    then show "a |\<in>| ?V" using x(1) by simp
  next
    assume "a |\<in>| ?V"
    then have "deferred_key d a \<in> set (RBT.keys K)" unfolding keysK by blast
    then show "RBT.lookup K (deferred_key d a) \<noteq> None" by (simp add: RBT.lookup_keys[symmetric] domIff)
  qed
  let ?Dk = "deferred_domain_keys d \<sigma> D"
  let ?H = "filter (\<lambda>y. RBT.lookup K (fst y) \<noteq> None) ?Dk"
  let ?I = "concat (map snd ?H)"
  let ?K' = "fold (\<lambda>k t. RBT.insert k () t) ?I (fold (\<lambda>y t. RBT.delete (fst y) t) ?H K)"
  have Dk: "y \<in> set ?Dk \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))))" for y
    by (auto simp: deferred_domain_keys_def)
  have H: "y \<in> set ?H \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))))"
    for y
  proof
    assume "y \<in> set ?H"
    then have y: "y \<in> set ?Dk" "RBT.lookup K (fst y) \<noteq> None" by simp_all
    then obtain a where a: "a |\<in>| D" "y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
      using Dk by blast
    have "a |\<in>| ?V" using y(2) a(2) inK[of a] by simp
    then show "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
      using a by blast
  next
    assume "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
    then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
      by blast
    have "y \<in> set ?Dk" using Dk a by blast
    moreover have "RBT.lookup K (fst y) \<noteq> None" using inK[of a] a by simp
    ultimately show "y \<in> set ?H" by simp
  qed
  have I: "z \<in> set ?I \<longleftrightarrow> (\<exists>a b. a |\<in>| D \<and> a |\<in>| ?V \<and> b |\<in>| shared_pattern_variables (\<sigma> a) \<and> z = deferred_key d b)"
    for z
  proof -
    have "z \<in> set ?I \<longleftrightarrow> (\<exists>y\<in>set ?H. z \<in> set (snd y))" unfolding set_concat set_map by blast
    also have "\<dots> \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a)))"
    proof
      assume "\<exists>y\<in>set ?H. z \<in> set (snd y)"
      then obtain y where y: "y \<in> set ?H" "z \<in> set (snd y)" by blast
      obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
        using H y(1) by blast
      have "z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a))" using y(2) unfolding a(3) by simp
      then show "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a))" using a(1,2) by blast
    next
      assume "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a))"
      then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a))" by blast
      have y: "(deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))) \<in> set ?H" using H a(1,2) by blast
      have "z \<in> set (snd (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))))"
        using a(3) by (simp only: snd_conv set_map)
      then show "\<exists>y\<in>set ?H. z \<in> set (snd y)" using y by blast
    qed
    also have "\<dots> \<longleftrightarrow> (\<exists>a b. a |\<in>| D \<and> a |\<in>| ?V \<and> b |\<in>| shared_pattern_variables (\<sigma> a) \<and> z = deferred_key d b)"
    proof -
      have "z \<in> deferred_key d ` set (shared_variable_list (\<sigma> a)) \<longleftrightarrow>
          (\<exists>b. b |\<in>| shared_pattern_variables (\<sigma> a) \<and> z = deferred_key d b)" if "a |\<in>| D" for a
        unfolding \<sigma>vl[OF that] by blast
      then show ?thesis by blast
    qed
    finally show ?thesis .
  qed
  have Hk: "z \<in> fst ` set ?H \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a)" for z
  proof
    assume "z \<in> fst ` set ?H"
    then obtain y where y: "y \<in> set ?H" "z = fst y" by blast
    obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "y = (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))"
      using H y(1) by blast
    have "z = deferred_key d a" using a(3) y(2) by simp
    then show "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a" using a(1,2) by blast
  next
    assume "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a"
    then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z = deferred_key d a" by blast
    have y: "(deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))) \<in> set ?H" using H a(1,2) by blast
    have "z = fst (deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a)))" using a(3) by (simp only: fst_conv)
    then show "z \<in> fst ` set ?H" using y by blast
  qed
  have keys': "set (RBT.keys ?K') = deferred_key d ` fset ?V'"
  proof (rule set_eqI)
    fix z
    have "z \<in> set (RBT.keys ?K') \<longleftrightarrow> z \<in> set ?I \<or> (z \<in> set (RBT.keys K) \<and> z \<notin> fst ` set ?H)"
      by (simp add: fold_insert_unit_keys fold_delete_keys)
    also have "\<dots> \<longleftrightarrow> z \<in> deferred_key d ` fset ?V'"
    proof
      assume "z \<in> set ?I \<or> (z \<in> set (RBT.keys K) \<and> z \<notin> fst ` set ?H)"
      then show "z \<in> deferred_key d ` fset ?V'"
      proof
        assume "z \<in> set ?I"
        then obtain a b where ab: "a |\<in>| D" "a |\<in>| ?V" "b |\<in>| shared_pattern_variables (\<sigma> a)" "z = deferred_key d b"
          using I by blast
        have "b |\<in>| ?V'" using V'[of b] ab by blast
        then show ?thesis using ab(4) by blast
      next
        assume z: "z \<in> set (RBT.keys K) \<and> z \<notin> fst ` set ?H"
        then obtain x where x: "x |\<in>| ?V" "z = deferred_key d x" unfolding keysK by blast
        have "x |\<notin>| D" using z x Hk by blast
        then have "x |\<in>| ?V'" using V'[of x] x(1) by blast
        then show ?thesis using x(2) by blast
      qed
    next
      assume "z \<in> deferred_key d ` fset ?V'"
      then obtain y where y: "y |\<in>| ?V'" "z = deferred_key d y" by blast
      from y(1)[unfolded V'] show "z \<in> set ?I \<or> (z \<in> set (RBT.keys K) \<and> z \<notin> fst ` set ?H)"
      proof (elim disjE conjE exE)
        assume yV: "y |\<in>| ?V" and yD: "y |\<notin>| D"
        have "z \<notin> fst ` set ?H"
        proof
          assume "z \<in> fst ` set ?H"
          then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z = deferred_key d a" using Hk by blast
          have "a = y" using deferred_key_inj[OF N numV[OF a(2)] numV[OF yV]] a(3) y(2) by simp
          then show False using a(1) yD by simp
        qed
        then show ?thesis using yV y(2) keysK by blast
      next
        fix a assume "a |\<in>| ?V" "a |\<in>| D" "y |\<in>| shared_pattern_variables (\<sigma> a)"
        then show ?thesis using I y(2) by blast
      qed
    qed
    finally show "z \<in> set (RBT.keys ?K') \<longleftrightarrow> z \<in> deferred_key d ` fset ?V'" .
  qed
  have numV': "deferred_numbered d x" if "x |\<in>| ?V'" for x using that numV num unfolding V' by blast
  let ?d1 = "deferred_record_put n q ?K' (fset_of_list ?I) d"
  have hold1: "n |\<in>| tree_bucket (deferred_holders ?d1) (deferred_key ?d1 x)" if "x |\<in>| ?V'" for x
  proof -
    from that[unfolded V'] show ?thesis
    proof (elim disjE conjE exE)
      assume "x |\<in>| ?V" "x |\<notin>| D"
      then show ?thesis using holdV by simp
    next
      fix a assume "a |\<in>| ?V" "a |\<in>| D" "x |\<in>| shared_pattern_variables (\<sigma> a)"
      then have "deferred_key d x \<in> set ?I" using I by blast
      then show ?thesis by (simp add: fset_of_list_elem)
    qed
  qed
  have eqU: "deferred_update \<sigma> D n d = (if \<not> RBT.is_empty K \<and> list_all (\<lambda>y. RBT.lookup K (fst y) = None) ?Dk then d
      else if RBT.is_empty ?K' then deferred_ground q ?d1 else ?d1)"
    by (simp add: deferred_update_def deferred_update_at_def rec deferred_record_update_def Let_def)
  have parts1: "deferred_parts_formed \<kappa> P ?d1" using deferred_record_put_parts[OF parts] nq by blast
  have at1: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) q = Some hn" using at by simp
  have rec1: "RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q) = Some (q, ?K')" using nq by simp
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
    have r': "RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q') =
        RBT.lookup (deferred_records d) (position_number (deferred_positions d) q')" using other_rec[OF ne q'0] by simp
    show "position_number (deferred_positions ?d1) q' \<noteq> 0 \<and>
      (\<exists>K. RBT.lookup (deferred_records ?d1) (position_number (deferred_positions ?d1) q') = Some (q', K) \<and>
        set (RBT.keys K) = deferred_key ?d1 ` fset (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn'))))) \<and>
      fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn')))) (deferred_numbered ?d1) \<and>
      fBall (shared_pattern_variables (binding_resolve S (shared_derivation_call (shared_entry_node hn'))))
        (\<lambda>x. position_number (deferred_positions ?d1) q' |\<in>| tree_bucket (deferred_holders ?d1) (deferred_key ?d1 x))"
      using sf a r' unfolding deferred_node_stale_def by auto
  qed
  have Sd: "binding_store_formed ?T (deferred_store d)" using parts unfolding deferred_parts_formed_def by blast
  consider (skip) "\<not> RBT.is_empty K \<and> list_all (\<lambda>y. RBT.lookup K (fst y) = None) ?Dk"
    | (ground) "\<not> (\<not> RBT.is_empty K \<and> list_all (\<lambda>y. RBT.lookup K (fst y) = None) ?Dk)" "RBT.is_empty ?K'"
    | (kept) "\<not> (\<not> RBT.is_empty K \<and> list_all (\<lambda>y. RBT.lookup K (fst y) = None) ?Dk)" "\<not> RBT.is_empty ?K'" by blast
  then have all: "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d) \<and> deferred_node_formed (deferred_update \<sigma> D n d) q \<and>
      (\<forall>q'. q' \<noteq> q \<longrightarrow> deferred_node_formed d q' \<longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q') \<and>
      (\<forall>q'. q' \<noteq> q \<longrightarrow> deferred_node_stale S d q' \<longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q') \<and>
      deferred_project (deferred_update \<sigma> D n d) = deferred_project d \<and>
      store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner (deferred_update \<sigma> D n d))) (deferred_store (deferred_update \<sigma> D n d)) \<and>
      deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d \<and>
      deferred_names (deferred_update \<sigma> D n d) = deferred_names d \<and>
      table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d))) \<and>
      (\<forall>n'. n' \<noteq> n \<longrightarrow> RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n' = RBT.lookup (deferred_records d) n') \<and>
      (\<exists>K'. RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n = Some (q, K'))"
  proof cases
    case skip
    have upd: "deferred_update \<sigma> D n d = d" unfolding eqU if_P[OF skip] by (rule refl)
    have dj: "\<not> (a |\<in>| ?V \<and> a |\<in>| D)" for a
    proof
      assume a: "a |\<in>| ?V \<and> a |\<in>| D"
      then have "(deferred_key d a, map (deferred_key d) (shared_variable_list (\<sigma> a))) \<in> set ?Dk" using Dk by blast
      then have "RBT.lookup K (deferred_key d a) = None" using skip by (auto simp: list_all_iff)
      then show False using inK a by blast
    qed
    have VV: "?V' = ?V" by (rule fset_eqI) (use V' dj in blast)
    have ne: "?V \<noteq> {||}"
    proof
      assume "?V = {||}"
      then have "set (RBT.keys K) = {}" using keysK by simp
      then show False using skip rbt_is_empty_keys by blast
    qed
    have nfq: "deferred_node_formed d q"
      unfolding deferred_node_formed_def using nq rec keysK numV holdV VV ne at by auto
    show ?thesis unfolding upd using parts nfq store_memoized_refl[OF Sd tf] rec by (simp add: table_extends_refl)
  next
    case ground
    have gr: "shared_pattern_variables (deferred_call ?d1 hn) = {||}"
      using ground(2) keys' rbt_is_empty_keys[of ?K'] by auto
    note G = deferred_ground[OF parts1 at1 gr]
    obtain r' K' where e': "deferred_ground q ?d1 = ?d1\<lparr>deferred_inner := r', deferred_tree := K'\<rparr>"
      and sm': "store_memoized (search_table (deferred_inner ?d1)) (deferred_store ?d1) (search_table r')
        (deferred_store (?d1\<lparr>deferred_inner := r', deferred_tree := K'\<rparr>))" using G(2) by blast
    have ext': "table_extends ?T (search_table r')" using G(8) e' by simp
    have nfq: "deferred_node_formed (deferred_ground q ?d1) q"
      using G(6)[of ?K'] rec1 nq keys' ground(2) rbt_is_empty_keys[of ?K'] by auto
    have n3: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state r')) p =
        RBT.lookup (shared_nodes (search_state (deferred_inner d))) p" using G(3) e' by simp
    have stale_g: "deferred_node_stale S (deferred_ground q ?d1) q'" if ne: "q' \<noteq> q" and sf: "deferred_node_stale S ?d1 q'" for q'
      using sf n3[OF ne] unfolding deferred_node_stale_def e' by simp
    have upd: "deferred_update \<sigma> D n d = deferred_ground q ?d1"
      unfolding eqU if_not_P[OF ground(1)] if_P[OF ground(2)] by (rule refl)
    show ?thesis unfolding upd
    proof (intro conjI allI impI)
      show "deferred_parts_formed \<kappa> P (deferred_ground q ?d1)" by (rule G(1))
      show "deferred_node_formed (deferred_ground q ?d1) q" by (rule nfq)
      show "deferred_node_formed (deferred_ground q ?d1) q'" if "q' \<noteq> q" "deferred_node_formed d q'" for q'
        using G(5)[OF that(1) other1[OF that]] .
      show "deferred_node_stale S (deferred_ground q ?d1) q'" if "q' \<noteq> q" "deferred_node_stale S d q'" for q'
        using stale_g[OF that(1) stale1[OF that]] .
      show "deferred_project (deferred_ground q ?d1) = deferred_project d" using G(7) by simp
      show "store_memoized (search_table (deferred_inner d)) (deferred_store d)
          (search_table (deferred_inner (deferred_ground q ?d1))) (deferred_store (deferred_ground q ?d1))"
        using sm' e' by simp
      show "deferred_positions (deferred_ground q ?d1) = deferred_positions d" using e' by simp
      show "deferred_names (deferred_ground q ?d1) = deferred_names d" using e' by simp
      show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_ground q ?d1)))"
        using ext' e' by simp
      show "RBT.lookup (deferred_records (deferred_ground q ?d1)) n' = RBT.lookup (deferred_records d) n'" if "n' \<noteq> n" for n'
        using e' that by simp
      show "\<exists>K'. RBT.lookup (deferred_records (deferred_ground q ?d1)) n = Some (q, K')" using e' by simp
    qed
  next
    case kept
    have upd: "deferred_update \<sigma> D n d = ?d1" unfolding eqU if_not_P[OF kept(1)] if_not_P[OF kept(2)] by (rule refl)
    have ne: "?V' \<noteq> {||}" using kept(2) keys' rbt_is_empty_keys[of ?K'] by auto
    have nf1: "deferred_node_formed ?d1 q"
      unfolding deferred_node_formed_def using at1 nq rec1 keys' numV' hold1 ne by auto
    show ?thesis unfolding upd
    proof (intro conjI allI impI)
      show "deferred_parts_formed \<kappa> P ?d1" by (rule parts1)
      show "deferred_node_formed ?d1 q" by (rule nf1)
      show "deferred_node_formed ?d1 q'" if "q' \<noteq> q" "deferred_node_formed d q'" for q' using other1[OF that] .
      show "deferred_node_stale S ?d1 q'" if "q' \<noteq> q" "deferred_node_stale S d q'" for q' using stale1[OF that] .
      show "deferred_project ?d1 = deferred_project d" by simp
      show "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner ?d1))
          (deferred_store ?d1)" using store_memoized_refl[OF Sd tf] by simp
      show "deferred_positions ?d1 = deferred_positions d" by simp
      show "deferred_names ?d1 = deferred_names d" by simp
      show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner ?d1))"
        by (simp add: table_extends_refl)
      show "RBT.lookup (deferred_records ?d1) n' = RBT.lookup (deferred_records d) n'" if "n' \<noteq> n" for n'
        using that by simp
      show "\<exists>K'. RBT.lookup (deferred_records ?d1) n = Some (q, K')" by simp
    qed
  qed
  show "deferred_parts_formed \<kappa> P (deferred_update \<sigma> D n d)" using all by blast
  show "deferred_node_formed (deferred_update \<sigma> D n d) q" using all by blast
  show "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_formed d q' \<Longrightarrow> deferred_node_formed (deferred_update \<sigma> D n d) q'" using all by blast
  show "\<And>q'. q' \<noteq> q \<Longrightarrow> deferred_node_stale S d q' \<Longrightarrow> deferred_node_stale S (deferred_update \<sigma> D n d) q'"
    using all by blast
  show "deferred_project (deferred_update \<sigma> D n d) = deferred_project d" using all by blast
  show "store_memoized (search_table (deferred_inner d)) (deferred_store d) (search_table (deferred_inner (deferred_update \<sigma> D n d))) (deferred_store (deferred_update \<sigma> D n d))" using all by blast
  show "deferred_positions (deferred_update \<sigma> D n d) = deferred_positions d" using all by blast
  show "deferred_names (deferred_update \<sigma> D n d) = deferred_names d" using all by blast
  show "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_update \<sigma> D n d)))"
    using all by blast
  show "\<And>n'. n' \<noteq> n \<Longrightarrow> RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n' = RBT.lookup (deferred_records d) n'"
    using all by blast
  show "\<exists>K'. RBT.lookup (deferred_records (deferred_update \<sigma> D n d)) n = Some (q, K')" using all by blast
qed

lemma deferred_ground_node_nodes:
  "p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground_node q d)))) p =
    RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
  by (simp add: deferred_ground_node_def shared_put_node_def shared_reshare_def split: option.splits prod.splits)

lemma deferred_memoize_nodes:
  shows "shared_nodes (search_state (deferred_inner (deferred_memoize_from n r x d))) =
      shared_nodes (search_state (deferred_inner d))"
    and "shared_nodes (search_state (deferred_inner (deferred_memoize_list n r xs d))) =
      shared_nodes (search_state (deferred_inner d))"
  by (induction n r x d and n r xs d rule: deferred_memoize_from_deferred_memoize_list.induct)
    (auto simp: deferred_memoize_at_def search_share_def shared_reshare_def split: option.splits prod.splits)

lemma deferred_ground_nodes:
  "p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_ground q d)))) p =
    RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
  by (simp add: deferred_ground_def deferred_ground_node_nodes deferred_memoize_node_def deferred_memoize_nodes
      split: option.splits)

lemma deferred_update_at_kept:
  "deferred_positions (deferred_update_at Dk n d) = deferred_positions d"
  "deferred_names (deferred_update_at Dk n d) = deferred_names d"
  "deferred_goal_records (deferred_update_at Dk n d) = deferred_goal_records d"
  "RBT.lookup (shared_goals (search_state (deferred_inner (deferred_update_at Dk n d)))) p =
    RBT.lookup (shared_goals (search_state (deferred_inner d))) p"
  by (simp_all add: deferred_update_at_def deferred_record_update_def Let_def deferred_ground_kept
      split: option.split prod.split)

lemma deferred_update_at_key [simp]: "deferred_key (deferred_update_at Dk n d) = deferred_key d"
  by (simp add: fun_eq_iff deferred_key_def deferred_update_at_kept)

lemma deferred_update_at_fold:
  "fold (deferred_update_at (deferred_domain_keys d \<sigma> D)) ns d = fold (deferred_update \<sigma> D) ns d"
proof (induction ns arbitrary: d)
  case (Cons n ns)
  have k: "deferred_domain_keys (deferred_update_at (deferred_domain_keys d \<sigma> D) n d) \<sigma> D = deferred_domain_keys d \<sigma> D"
    by (simp add: deferred_domain_keys_def)
  show ?case using Cons.IH[of "deferred_update_at (deferred_domain_keys d \<sigma> D) n d"] k by (simp add: deferred_update_def)
qed simp

lemma deferred_update_nodes:
  "RBT.lookup (deferred_records d) n = Some (q, K) \<Longrightarrow> p \<noteq> q \<Longrightarrow>
    RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_update \<sigma> D n d)))) p =
    RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
  by (simp add: deferred_update_def deferred_update_at_def deferred_record_update_def Let_def deferred_ground_nodes
      split: prod.split)

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
    and "store_memoized T0 (store_bind S \<sigma> D) (search_table (deferred_inner d)) (deferred_store d)"
    and "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and "distinct ns"
    and "\<forall>q. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q \<noteq> None \<longrightarrow>
      position_number (deferred_positions d) q \<in> set ns \<longrightarrow> deferred_node_stale S d q"
    and "\<forall>q. position_number (deferred_positions d) q \<notin> set ns \<longrightarrow> deferred_node_formed d q"
    and "table_formed T0" and "binding_store_formed T0 (store_bind S \<sigma> D)"
    and "\<forall>q hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<longrightarrow>
      position_number (deferred_positions d) q \<in> set ns \<longrightarrow> shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))"
    and "\<forall>q. deferred_goal_formed d q"
  shows "deferred_formed \<kappa> P (fold (deferred_update \<sigma> D) ns d) \<and>
    deferred_project (fold (deferred_update \<sigma> D) ns d) = deferred_project d \<and>
    store_memoized (search_table (deferred_inner d)) (deferred_store d)
      (search_table (deferred_inner (fold (deferred_update \<sigma> D) ns d))) (deferred_store (fold (deferred_update \<sigma> D) ns d))"
  using assms
proof (induction ns arbitrary: d)
  case Nil
  have r0: "search_formed \<kappa> P (deferred_inner d)"
    and S0': "binding_store_formed (search_table (deferred_inner d)) (deferred_store d)"
    using Nil.prems(1) unfolding deferred_parts_formed_def by blast+
  have "table_formed (search_table (deferred_inner d))" using shared_entries_formed(4)[OF search_formedD(1)[OF r0]] .
  then show ?case using Nil.prems store_memoized_refl[OF S0'] by (simp add: deferred_formed_def)
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
    have u: "deferred_update \<sigma> D n d = d" by (simp add: deferred_update_def deferred_update_at_def None)
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
        store_memoized (search_table (deferred_inner d)) (deferred_store d)
          (search_table (deferred_inner (fold (deferred_update \<sigma> D) ns d))) (deferred_store (fold (deferred_update \<sigma> D) ns d))"
    proof -
      have c0n: "\<forall>q hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn \<longrightarrow>
          position_number (deferred_positions d) q \<in> set ns \<longrightarrow>
          shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))" using Cons.prems(11) by simp
      show ?thesis using Cons.IH[OF Cons.prems(1-5) nsd st' fm' Cons.prems(9,10) c0n Cons.prems(12)] .
    qed
    show ?thesis using IH u by simp
  next
    case (Some z)
    obtain q0 K where z: "z = (q0, K)" by (cases z)
    have rec: "RBT.lookup (deferred_records d) n = Some (q0, K)" using Some z by simp
    have nq0: "n \<noteq> 0 \<and> n = position_number (deferred_positions d) q0 \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner d))) q0 \<noteq> None"
      using Cons.prems(1) rec unfolding deferred_parts_formed_def by blast
    have stale0: "deferred_node_stale S d q0" using Cons.prems(7) nq0 by simp
    have c00: "\<forall>hn. RBT.lookup (shared_nodes (search_state (deferred_inner d))) q0 = Some hn \<longrightarrow>
        shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))" using Cons.prems(11) nq0 by simp
    note U = deferred_update[OF Cons.prems(1) Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) rec stale0
        Cons.prems(9) Cons.prems(10) c00]
    let ?d' = "deferred_update \<sigma> D n d"
    have numE: "deferred_numbered ?d' = deferred_numbered d" by (rule deferred_numbered_cong[OF U(7) U(8)])
    have S': "binding_store_formed (search_table (deferred_inner ?d')) S"
      using binding_store_formed_extended[OF Cons.prems(2) tf] U(9) by (simp add: table_extends_def)
    have ready': "unifier_ready (search_table (deferred_inner ?d')) (binding_map S) \<sigma> D"
      by (rule unifier_ready_extends[OF Cons.prems(3) tf U(9)])
    have st': "store_memoized T0 (store_bind S \<sigma> D) (search_table (deferred_inner ?d')) (deferred_store ?d')"
      by (rule store_memoized_trans[OF Cons.prems(4) U(6) Cons.prems(9)])
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
        store_memoized (search_table (deferred_inner ?d')) (deferred_store ?d')
          (search_table (deferred_inner (fold (deferred_update \<sigma> D) ns ?d'))) (deferred_store (fold (deferred_update \<sigma> D) ns ?d'))"
    proof -
      have c0': "\<forall>q hn. RBT.lookup (shared_nodes (search_state (deferred_inner ?d'))) q = Some hn \<longrightarrow>
          position_number (deferred_positions ?d') q \<in> set ns \<longrightarrow>
          shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))"
      proof (intro allI impI)
        fix q hn assume a: "RBT.lookup (shared_nodes (search_state (deferred_inner ?d'))) q = Some hn"
          and m: "position_number (deferred_positions ?d') q \<in> set ns"
        have m': "position_number (deferred_positions d) q \<in> set ns" using m U(7) by simp
        have "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = Some hn"
          using a deferred_update_nodes[OF rec ne[OF m']] by simp
        then show "shared_pattern_formed T0 (shared_derivation_call (shared_entry_node hn))" using Cons.prems(11) m' by simp
      qed
      have goal': "\<forall>q. deferred_goal_formed ?d' q"
      proof
        fix q'' show "deferred_goal_formed ?d' q''"
        proof (rule deferred_goal_formed_same[OF Cons.prems(12)[rule_format, of q'']])
          show "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner ?d'))) q'' = Some h' \<Longrightarrow>
            \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q'' = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
            by (simp add: deferred_update_def deferred_update_at_kept)
          show "RBT.lookup (deferred_goal_records ?d') q'' = RBT.lookup (deferred_goal_records d) q''"
            by (simp add: deferred_update_def deferred_update_at_kept)
          show "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key ?d' x = deferred_key d x \<and> deferred_numbered ?d' x"
            using numE U(7) U(8) by (simp add: deferred_key_def)
        qed
      qed
      show ?thesis using Cons.IH[OF U(1) S' ready' st' num' nsd stale' formed' Cons.prems(9,10) c0' goal'] .
    qed
    show ?thesis using IH U(5) store_memoized_trans[OF U(6) conjunct2[OF conjunct2[OF IH]] tf] by simp
  qed
qed

subsection \<open>The goal side of the bind, written by difference\<close>

text \<open>
  D3a (task 977). A goal the domain reaches is substituted and re-entered as the shared search does it
  (@{const shared_goal_entry_substitute}), but its record decides whether the domain reaches it (the domain's keys looked
  up in the record), the holder index gains the goal's position at its images' variables' position parts only (the old
  parts already hold it: the holder index is a superset), and the registered buckets change only where the record's
  difference adds a registered position or removes the last registered key of one (a range of the record's keys). A call
  goal at the root, which has no record, is substituted through the shared search's own step.
\<close>

lemma resolution_goal_substitute_variables:
  "z |\<in>| resolution_goal_variables (resolution_goal_substitute \<tau> g) \<longleftrightarrow>
    (\<exists>c. c |\<in>| resolution_goal_variables g \<and> z |\<in>| finite_pattern_variables (\<tau> c))"
proof -
  have p: "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<tau> p) \<longleftrightarrow>
      (\<exists>c. c |\<in>| finite_pattern_variables p \<and> z |\<in>| finite_pattern_variables (\<tau> c))" for p
    by (induction p) auto
  show ?thesis by (cases g) (auto simp: p finite_material_variables_def finite_material_pattern_substitute_def)
qed

lemma root_call_goal_substitute [simp]: "root_call_goal (resolution_goal_substitute \<tau> g) = root_call_goal g"
  by (cases g) (simp_all add: root_call_goal_def)

lemma shared_root_goal_project: "shared_root_goal g \<longleftrightarrow> root_call_goal (shared_goal_project T g)"
  by (cases g) (simp_all add: shared_root_goal_def root_call_goal_def)

lemma shared_goal_substituted_variables:
  assumes x: "share_state_formed x" and h: "goal_entry_formed P (share_state_table x) q h"
    and \<sigma>f: "\<And>a. shared_pattern_formed (share_state_table x) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
  shows "z |\<in>| shared_goal_variables (shared_entry_goal (fst (shared_goal_entry_substitute P \<sigma> D h x))) \<longleftrightarrow>
    (z |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<notin>| D) \<or>
    (\<exists>a. a |\<in>| shared_goal_variables (shared_entry_goal h) \<and> a |\<in>| D \<and> z |\<in>| shared_pattern_variables (\<sigma> a))"
proof -
  note k = shared_goal_entry_substitute[where D = D, OF x h \<sigma>f \<sigma>c out[rule_format]]
  let ?x' = "snd (shared_goal_entry_substitute P \<sigma> D h x)" and ?h' = "fst (shared_goal_entry_substitute P \<sigma> D h x)"
  let ?\<tau> = "\<lambda>a. shared_pattern_project (share_state_table x) (\<sigma> a)"
  have hf': "goal_entry_formed P (share_state_table ?x') q ?h'" using k by blast
  have pj: "shared_goal_project (share_state_table ?x') (shared_entry_goal ?h') =
      resolution_goal_substitute ?\<tau> (shared_goal_project (share_state_table x) (shared_entry_goal h))" using k by blast
  have tv: "finite_pattern_variables (?\<tau> a) = shared_pattern_variables (\<sigma> a)" for a
    using shared_pattern_variables_project[OF \<sigma>f[of a]] by simp
  have sv: "shared_pattern_variables (\<sigma> c) = {|c|}" if "c |\<notin>| D" for c using out[rule_format, OF that] by simp
  have e: "z |\<in>| shared_goal_variables (shared_entry_goal ?h') \<longleftrightarrow>
      (\<exists>c. c |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<in>| shared_pattern_variables (\<sigma> c))"
    unfolding goal_entry_variables[OF hf'] pj resolution_goal_substitute_variables goal_entry_variables[OF h] tv ..
  show ?thesis unfolding e
  proof
    assume "\<exists>c. c |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<in>| shared_pattern_variables (\<sigma> c)"
    then obtain c where c: "c |\<in>| shared_goal_variables (shared_entry_goal h)" "z |\<in>| shared_pattern_variables (\<sigma> c)"
      by blast
    show "(z |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<notin>| D) \<or>
      (\<exists>a. a |\<in>| shared_goal_variables (shared_entry_goal h) \<and> a |\<in>| D \<and> z |\<in>| shared_pattern_variables (\<sigma> a))"
    proof (cases "c |\<in>| D")
      case True
      then show ?thesis using c by blast
    next
      case False
      then show ?thesis using c sv[OF False] by simp
    qed
  next
    assume "(z |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<notin>| D) \<or>
      (\<exists>a. a |\<in>| shared_goal_variables (shared_entry_goal h) \<and> a |\<in>| D \<and> z |\<in>| shared_pattern_variables (\<sigma> a))"
    then show "\<exists>c. c |\<in>| shared_goal_variables (shared_entry_goal h) \<and> z |\<in>| shared_pattern_variables (\<sigma> c)"
    proof (elim disjE conjE exE)
      assume zh: "z |\<in>| shared_goal_variables (shared_entry_goal h)" and zD: "z |\<notin>| D"
      have "z |\<in>| shared_pattern_variables (\<sigma> z)" using sv[OF zD] by simp
      then show ?thesis using zh by blast
    next
      fix a assume "a |\<in>| shared_goal_variables (shared_entry_goal h)" "a |\<in>| D" "z |\<in>| shared_pattern_variables (\<sigma> a)"
      then show ?thesis by blast
    qed
  qed
qed

text \<open>
  The goal at a position written with its holders added at the given position parts only: every other field as
  @{const shared_replace} writes a goal whose node stays.
\<close>

definition shared_goal_write :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> 's list fset \<Rightarrow>
    ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_goal_write q h A s = s\<lparr>shared_goals := tree_option_put (shared_goals s) q (Some h),
    shared_holders := tree_add q A (shared_holders s),
    shared_open := open_count_put (shared_goals s) (shared_open s) q True,
    shared_goal_calls := tree_move q
      (case_option {||} (\<lambda>h. shared_goal_call_refs (shared_entry_goal h)) (RBT.lookup (shared_goals s) q))
      (shared_goal_call_refs (shared_entry_goal h)) (shared_goal_calls s)\<rparr>"

lemma shared_goal_write:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_goals s) q = Some h0"
    and h: "goal_entry_formed P (shared_state_table s) q h"
    and A: "\<forall>x. x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      x |\<notin>| shared_goal_variables (shared_entry_goal h0) \<longrightarrow> fst (fst x) |\<in>| A"
  shows "shared_state_formed \<kappa> P (shared_goal_write q h A s)"
    and "shared_state_table (shared_goal_write q h A s) = shared_state_table s"
    and "\<And>p. RBT.lookup (shared_goals (shared_goal_write q h A s)) p = (if p = q then Some h else RBT.lookup (shared_goals s) p)"
    and "shared_nodes (shared_goal_write q h A s) = shared_nodes s"
    and "shared_witnesses (shared_goal_write q h A s) = shared_witnesses s"
proof -
  let ?T = "shared_state_table s" and ?s' = "shared_goal_write q h A s"
  have rec0: "shared_recorded_at s p" for p using s by (simp add: shared_state_formed_def)
  have rec: "shared_recorded_at ?s' p" for p
  proof (cases "p = q")
    case True
    show ?thesis unfolding shared_recorded_at_def True
    proof (intro conjI allI impI)
      fix h' x assume a: "RBT.lookup (shared_goals ?s') q = Some h'" and x: "x |\<in>| shared_goal_variables (shared_entry_goal h')"
      have h': "h' = h" using a by (simp add: shared_goal_write_def)
      show "q |\<in>| tree_bucket (shared_holders ?s') (fst (fst x))"
      proof (cases "x |\<in>| shared_goal_variables (shared_entry_goal h0)")
        case True
        then have "q |\<in>| tree_bucket (shared_holders s) (fst (fst x))"
          using rec0[of q] at unfolding shared_recorded_at_def by blast
        then show ?thesis by (simp add: shared_goal_write_def)
      next
        case False
        then show ?thesis using A[rule_format, OF x[unfolded h'] False] by (simp add: shared_goal_write_def)
      qed
    next
      fix hn x assume a: "RBT.lookup (shared_nodes ?s') q = Some hn" and x: "x |\<in>| shared_entry_variables hn"
      have a0: "RBT.lookup (shared_nodes s) q = Some hn" using a by (simp add: shared_goal_write_def)
      have "q |\<in>| tree_bucket (shared_holders s) (fst (fst x))"
        using rec0[of q] a0 x unfolding shared_recorded_at_def by blast
      then show "q |\<in>| tree_bucket (shared_holders ?s') (fst (fst x))" by (simp add: shared_goal_write_def)
    next
      fix h' i assume a: "RBT.lookup (shared_goals ?s') q = Some h'" and i: "i |\<in>| shared_goal_call_refs (shared_entry_goal h')"
      then show "q |\<in>| tree_bucket (shared_goal_calls ?s') i" by (simp add: shared_goal_write_def tree_move)
    next
      fix hn i assume a: "RBT.lookup (shared_nodes ?s') q = Some hn"
        and i: "i |\<in>| shared_call_refs (shared_derivation_call (shared_entry_node hn))"
      then show "q |\<in>| tree_bucket (shared_node_calls ?s') i"
        using rec0[of q] by (simp add: shared_recorded_at_def shared_goal_write_def)
    qed
  next
    case False
    then show ?thesis using rec0[of p] by (auto simp: shared_recorded_at_def shared_goal_write_def tree_move)
  qed
  have gcalls: "i < length ?T" if "y |\<in>| tree_bucket (shared_goal_calls ?s') i" for i y
  proof (cases "i |\<in>| shared_goal_call_refs (shared_entry_goal h)")
    case True
    then show ?thesis using h shared_goal_call_refs_formed[of ?T] by (auto simp: goal_entry_formed_def)
  next
    case False
    then have "y |\<in>| tree_bucket (shared_goal_calls s) i" using that
      by (auto simp: shared_goal_write_def tree_move split: if_splits)
    then show ?thesis using s by (auto simp: shared_state_formed_def)
  qed
  have counts: "tree_count (shared_open ?s') p = open_count (shared_goals ?s') p" for p
  proof -
    have "\<And>p. tree_count (shared_open s) p = open_count (shared_goals s) p" using s by (simp add: shared_state_formed_def)
    from open_count_put_formed[OF this, of q "Some h" p] show ?thesis by (simp add: shared_goal_write_def)
  qed
  have gs: "\<And>p h'. RBT.lookup (shared_goals ?s') p = Some h' \<Longrightarrow> goal_entry_formed P ?T p h'"
    using h shared_entries_formed(1)[OF s] by (auto simp: shared_goal_write_def split: if_splits)
  have ns: "\<And>p hn. RBT.lookup (shared_nodes ?s') p = Some hn \<Longrightarrow> node_entry_formed ?T p hn"
    using shared_entries_formed(2)[OF s] by (simp add: shared_goal_write_def)
  have c1: "\<forall>i y. y |\<in>| tree_bucket (shared_goal_calls ?s') i \<longrightarrow> i < length (shared_state_table ?s')"
    using gcalls by (simp add: shared_goal_write_def)
  have c2: "\<forall>i y. y |\<in>| tree_bucket (shared_node_calls ?s') i \<longrightarrow> i < length (shared_state_table ?s')"
    using s by (simp add: shared_goal_write_def shared_state_formed_def)
  have g1: "\<forall>p h'. RBT.lookup (shared_goals ?s') p = Some h' \<longrightarrow> goal_entry_formed P (shared_state_table ?s') p h'"
    using gs by (simp add: shared_goal_write_def)
  have n1: "\<forall>p hn. RBT.lookup (shared_nodes ?s') p = Some hn \<longrightarrow> node_entry_formed (shared_state_table ?s') p hn"
    using ns by (simp add: shared_goal_write_def)
  have o1: "\<forall>p. tree_count (shared_open ?s') p = open_count (shared_goals ?s') p" using counts by simp
  have u1: "\<forall>p a hn. a |\<in>| tree_bucket (shared_unconstructed ?s') p \<longrightarrow> RBT.lookup (shared_nodes ?s') p = Some hn \<longrightarrow>
      finite_registered_value \<kappa> P (shared_derivation_project (shared_state_table ?s') (shared_entry_node hn)) a = None"
    using s by (simp add: shared_goal_write_def shared_state_formed_def)
  have sh: "share_state_formed (shared_sharing ?s')" "position_index_formed (shared_sharing ?s') (shared_positions ?s')"
    using s by (simp_all add: shared_goal_write_def shared_state_formed_def)
  show "shared_state_formed \<kappa> P ?s'" unfolding shared_state_formed_def using sh g1 n1 c1 c2 rec o1 u1 by blast
  show "shared_state_table ?s' = ?T" by (simp add: shared_goal_write_def)
  show "\<And>p. RBT.lookup (shared_goals ?s') p = (if p = q then Some h else RBT.lookup (shared_goals s) p)"
    by (simp add: shared_goal_write_def)
  show "shared_nodes ?s' = shared_nodes s" by (simp add: shared_goal_write_def)
  show "shared_witnesses ?s' = shared_witnesses s" by (simp add: shared_goal_write_def)
qed

text \<open>The registered buckets moved at the positions a difference adds and removes, every other bucket kept.\<close>

definition tree_shift :: "'q \<Rightarrow> 'k::linorder list \<Rightarrow> 'k list \<Rightarrow> ('k,'q fset) rbt \<Rightarrow> ('k,'q fset) rbt" where
  "tree_shift q A R t = fold (\<lambda>p t. tree_bucket_put t p (tree_bucket t p |-| {|q|})) R
    (fold (\<lambda>p t. tree_bucket_put t p (finsert q (tree_bucket t p))) A t)"

lemma tree_shift:
  "tree_bucket (tree_shift q A R t) p = (if p \<in> set R then tree_bucket t p |-| {|q|}
    else if p \<in> set A then finsert q (tree_bucket t p) else tree_bucket t p)"
proof -
  have a: "tree_bucket (fold (\<lambda>p t. tree_bucket_put t p (finsert q (tree_bucket t p))) A t) p =
      (if p \<in> set A then finsert q (tree_bucket t p) else tree_bucket t p)" for t
    by (induction A arbitrary: t) auto
  have r: "tree_bucket (fold (\<lambda>p t. tree_bucket_put t p (tree_bucket t p |-| {|q|})) R t) p =
      (if p \<in> set R then tree_bucket t p |-| {|q|} else tree_bucket t p)" for t
    by (induction R arbitrary: t) auto
  show ?thesis by (auto simp: tree_shift_def r a)
qed

definition search_goal_write :: "'s list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> 's list list \<Rightarrow> 's list list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_goal_write q s' A R r = r\<lparr>search_state := s', search_registered := tree_shift q A R (search_registered r),
    search_classes := classes_update (classes_touched q (search_state r) s') s' (search_classes r),
    search_closed := closed_put q s' (search_index r) (search_closed r)\<rparr>"

lemma search_goal_write_update:
  "search_goal_write q s' A R r = (search_update q s' r)\<lparr>search_registered := tree_shift q A R (search_registered r)\<rparr>"
  by (simp add: search_goal_write_def search_update_def)

lemma search_goal_write:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and s': "shared_state_formed \<kappa> P s'"
    and ext: "table_extends (search_table r) (shared_state_table s')"
    and same: "\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals (search_state r)) p"
    and nodes: "\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_nodes s') p = RBT.lookup (shared_nodes (search_state r)) p"
    and at0: "RBT.lookup (shared_goals (search_state r)) q = Some h0" and at: "RBT.lookup (shared_goals s') q = Some h"
    and A: "\<forall>p. p |\<in>| shared_goal_registered h \<longrightarrow> p |\<notin>| shared_goal_registered h0 \<longrightarrow> p \<in> set A"
    and R: "\<forall>p. p \<in> set R \<longrightarrow> p |\<notin>| shared_goal_registered h"
  shows "search_formed \<kappa> P (search_goal_write q s' A R r)" and "search_classes_formed (search_goal_write q s' A R r)"
    and "search_state (search_goal_write q s' A R r) = s'"
proof -
  have u: "search_formed \<kappa> P (search_update q s' r)" by (rule search_update[OF r s' ext]) (use same in blast)
  have Ku: "search_classes_formed (search_update q s' r)"
    by (rule search_update_classes[OF r K u ext]) (use same nodes in blast)+
  have reg0: "search_registered_formed r" using r by (simp add: search_formed_def)
  let ?t = "tree_shift q A R (search_registered r)"
  have reg: "search_registered_formed ((search_update q s' r)\<lparr>search_registered := ?t\<rparr>)"
    unfolding search_registered_formed_def
  proof (intro allI impI)
    fix p h' z assume a: "RBT.lookup (shared_goals (search_state ((search_update q s' r)\<lparr>search_registered := ?t\<rparr>))) p = Some h'"
      and z: "z |\<in>| shared_goal_registered h'"
    have a': "RBT.lookup (shared_goals s') p = Some h'" using a by (simp add: search_update_def)
    show "p |\<in>| tree_bucket (search_registered ((search_update q s' r)\<lparr>search_registered := ?t\<rparr>)) z"
    proof (cases "p = q")
      case True
      then have hh: "h' = h" using a' at by simp
      have zR: "z \<notin> set R" using R z hh by blast
      show ?thesis
      proof (cases "z |\<in>| shared_goal_registered h0")
        case True
        then have "q |\<in>| tree_bucket (search_registered r) z" using reg0 at0 by (simp add: search_registered_formed_def)
        then show ?thesis using \<open>p = q\<close> zR by (simp add: tree_shift)
      next
        case False
        then have "z \<in> set A" using A z hh by blast
        then show ?thesis using \<open>p = q\<close> zR by (simp add: tree_shift)
      qed
    next
      case False
      then have "RBT.lookup (shared_goals (search_state r)) p = Some h'" using a' same False by simp
      then have "p |\<in>| tree_bucket (search_registered r) z" using reg0 z by (simp add: search_registered_formed_def)
      then show ?thesis using False by (simp add: tree_shift)
    qed
  qed
  have vals: "search_values_formed \<kappa> P ((search_update q s' r)\<lparr>search_registered := ?t\<rparr>) =
      search_values_formed \<kappa> P (search_update q s' r)" by (simp add: search_values_formed_def)
  have clos: "search_closing_formed ((search_update q s' r)\<lparr>search_registered := ?t\<rparr>) =
      search_closing_formed (search_update q s' r)"
    unfolding search_closing_formed_def search_closes_def by (simp cong: option.case_cong)
  have uf: "shared_state_formed \<kappa> P (search_state (search_update q s' r)) \<and> search_values_formed \<kappa> P (search_update q s' r) \<and>
      search_closing_formed (search_update q s' r)" using u by (simp add: search_formed_def)
  show "search_formed \<kappa> P (search_goal_write q s' A R r)"
    unfolding search_goal_write_update search_formed_def using uf reg vals clos by simp
  show "search_classes_formed (search_goal_write q s' A R r)" using Ku by (simp add: search_goal_write_update)
  show "search_state (search_goal_write q s' A R r) = s'" by (simp add: search_goal_write_def)
qed

text \<open>
  The step at one position the holder index gives: no goal, kept; a goal without a record (the root call goal),
  substituted through the shared search's step; a goal whose record holds none of the domain's keys, kept; otherwise the
  goal substituted and re-entered, its record and the indexes written by the difference.
\<close>

definition deferred_goal_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    (('s,'a) resolution_variable \<times> deferred_key \<times> ('s,'a) resolution_variable list) list \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_goal_at P \<sigma> D Dg q d = (let r = deferred_inner d; s = search_state r in
    case RBT.lookup (shared_goals s) q of None \<Rightarrow> d
    | Some h \<Rightarrow> (case RBT.lookup (deferred_goal_records d) q of
        None \<Rightarrow> d\<lparr>deferred_inner := search_goal_substitute_at P \<sigma> D q r\<rparr>
      | Some K \<Rightarrow> (let H = filter (\<lambda>z. RBT.lookup K (fst (snd z)) \<noteq> None) Dg in
        if H = [] then d else
        (case shared_goal_substitute \<sigma> D (shared_entry_goal h) (shared_sharing s) of (g', x') \<Rightarrow>
          case enter_goal P x' g' of (h', x) \<Rightarrow>
          let I = concat (map (\<lambda>z. snd (snd z)) H);
            K' = fold (\<lambda>k t. RBT.insert k () t) (map (deferred_key d) I)
              (fold (\<lambda>z t. RBT.delete (fst (snd z)) t) H K);
            A = map (\<lambda>y. fst (fst y)) (filter (\<lambda>y. snd (fst y)) I);
            R = map (\<lambda>z. fst (fst (fst z))) (filter (\<lambda>z. snd (fst (fst z)) \<and>
              tree_range K' (\<lambda>k. k < (fst (fst (snd z)), True, 0)) (\<lambda>k. fst (fst (snd z)) < fst k) = []) H)
          in d\<lparr>deferred_inner := search_goal_write q
              (shared_goal_write q h' (fset_of_list (map (\<lambda>y. fst (fst y)) I)) (shared_reshare x s)) A R r,
            deferred_goal_records := RBT.insert q K' (deferred_goal_records d)\<rparr>))))"

lemma deferred_goal_at:
  assumes r: "search_formed \<kappa> P (deferred_inner d)" and K: "search_classes_formed (deferred_inner d)"
    and \<sigma>f: "\<And>a. shared_pattern_formed (search_table (deferred_inner d)) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
    and Dg: "\<And>z. z \<in> set Dg \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> z = (a, deferred_key d a, shared_variable_list (\<sigma> a)))"
    and N: "positions_numbered (deferred_positions d)"
    and numI: "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and gf: "deferred_goal_formed d q"
  shows "search_formed \<kappa> P (deferred_inner (deferred_goal_at P \<sigma> D Dg q d)) \<and>
    search_classes_formed (deferred_inner (deferred_goal_at P \<sigma> D Dg q d)) \<and>
    table_extends (search_table (deferred_inner d)) (search_table (deferred_inner (deferred_goal_at P \<sigma> D Dg q d))) \<and>
    (\<forall>p. RBT.lookup (shared_nodes (search_state (deferred_inner (deferred_goal_at P \<sigma> D Dg q d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p) \<and>
    shared_goal_view (search_state (deferred_inner (deferred_goal_at P \<sigma> D Dg q d))) q =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (search_table (deferred_inner d)) (\<sigma> a)))
        (shared_goal_view (search_state (deferred_inner d)) q) \<and>
    (\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner (deferred_goal_at P \<sigma> D Dg q d)))) p =
      RBT.lookup (shared_goals (search_state (deferred_inner d))) p) \<and>
    shared_witnesses (search_state (deferred_inner (deferred_goal_at P \<sigma> D Dg q d))) =
      shared_witnesses (search_state (deferred_inner d)) \<and>
    deferred_goal_formed (deferred_goal_at P \<sigma> D Dg q d) q \<and>
    (\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (deferred_goal_records (deferred_goal_at P \<sigma> D Dg q d)) p =
      RBT.lookup (deferred_goal_records d) p) \<and>
    deferred_positions (deferred_goal_at P \<sigma> D Dg q d) = deferred_positions d \<and>
    deferred_names (deferred_goal_at P \<sigma> D Dg q d) = deferred_names d \<and>
    deferred_tree (deferred_goal_at P \<sigma> D Dg q d) = deferred_tree d \<and>
    deferred_records (deferred_goal_at P \<sigma> D Dg q d) = deferred_records d \<and>
    deferred_holders (deferred_goal_at P \<sigma> D Dg q d) = deferred_holders d"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T (\<sigma> a)"
  let ?d' = "deferred_goal_at P \<sigma> D Dg q d"
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have outA: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" using out by blast
  show ?thesis
  proof (cases "RBT.lookup (shared_goals ?s) q")
    case None
    have e: "?d' = d" by (simp add: deferred_goal_at_def None Let_def)
    have "deferred_goal_formed d q" by (simp add: deferred_goal_formed_def None)
    then show ?thesis using e r K None by (simp add: shared_goal_view_def table_extends_refl)
  next
    case (Some h)
    note at = Some
    have hf: "goal_entry_formed P ?T q h" using shared_entries_formed(1)[OF s at] .
    show ?thesis
    proof (cases "RBT.lookup (deferred_goal_records d) q")
      case None
      note gN = None
      have root: "shared_root_goal (shared_entry_goal h)" by (rule deferred_goal_formedD(1)[OF gf at gN])
      let ?r1 = "search_goal_substitute_at P \<sigma> D q ?r"
      have e: "?d' = d\<lparr>deferred_inner := ?r1\<rparr>" by (simp add: deferred_goal_at_def at gN Let_def)
      note k = shared_goal_substitute_at[where D = D and q = q, OF s \<sigma>f \<sigma>c outA]
      have f1: "search_formed \<kappa> P ?r1" unfolding search_goal_substitute_at_def
        by (rule search_update[OF r]) (simp_all add: k(1) k(2) k(3))
      have K1: "search_classes_formed ?r1" unfolding search_goal_substitute_at_def
        by (rule search_update_classes[OF r K f1[unfolded search_goal_substitute_at_def]]) (simp_all add: k(2) k(3) k(4))
      have st1: "search_state ?r1 = shared_goal_substitute_at P \<sigma> D q ?s"
        by (simp add: search_goal_substitute_at_def search_update_def)
      have gv: "shared_goal_view (search_state ?r1) q = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view ?s q)"
        using k(5) st1 by simp
      obtain h' where h': "RBT.lookup (shared_goals (search_state ?r1)) q = Some h'"
        using gv at by (cases "RBT.lookup (shared_goals (search_state ?r1)) q") (simp_all add: shared_goal_view_def)
      have pj: "shared_goal_project (search_table ?r1) (shared_entry_goal h') =
          resolution_goal_substitute ?\<tau> (shared_goal_project ?T (shared_entry_goal h))"
        using gv h' at by (simp add: shared_goal_view_def)
      have root': "shared_root_goal (shared_entry_goal h')"
        using root pj shared_root_goal_project[of "shared_entry_goal h'" "search_table ?r1"]
          shared_root_goal_project[of "shared_entry_goal h" ?T] by simp
      have gq: "deferred_goal_formed ?d' q" unfolding deferred_goal_formed_def e using h' gN root' by simp
      have ext1: "table_extends ?T (search_table ?r1)" using k(2) st1 by simp
      have nodes1: "\<forall>p. RBT.lookup (shared_nodes (search_state ?r1)) p = RBT.lookup (shared_nodes ?s) p" using k(4) st1 by simp
      have goals1: "\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_goals (search_state ?r1)) p = RBT.lookup (shared_goals ?s) p"
        using k(3) st1 by simp
      have w1: "shared_witnesses (search_state ?r1) = shared_witnesses ?s" using k(6) st1 by simp
      show ?thesis unfolding e using f1 K1 ext1 nodes1 gv goals1 w1 gq[unfolded e] by simp
    next
      case (Some K)
      note gK = Some
      let ?V = "shared_goal_variables (shared_entry_goal h)"
      have keysK: "set (RBT.keys K) = deferred_key d ` fset ?V" by (rule deferred_goal_formedD(2)[OF gf at gK])
      have numV: "\<And>x. x |\<in>| ?V \<Longrightarrow> deferred_numbered d x" by (rule deferred_goal_formedD(3)[OF gf at gK])
      have inK: "RBT.lookup K (deferred_key d a) \<noteq> None \<longleftrightarrow> a |\<in>| ?V" for a
      proof
        assume "RBT.lookup K (deferred_key d a) \<noteq> None"
        then have "deferred_key d a \<in> set (RBT.keys K)" by (simp add: RBT.lookup_keys[symmetric] domIff)
        then obtain x where x: "x |\<in>| ?V" "deferred_key d x = deferred_key d a" unfolding keysK by auto
        have an: "deferred_numbered d a"
        proof (rule ccontr)
          assume "\<not> deferred_numbered d a"
          then show False using deferred_key_zero[of d a x] numV[OF x(1)] x(2) by simp
        qed
        have "x = a" using deferred_key_inj[OF N numV[OF x(1)] an] x(2) by blast
        then show "a |\<in>| ?V" using x(1) by simp
      next
        assume "a |\<in>| ?V"
        then have "deferred_key d a \<in> set (RBT.keys K)" unfolding keysK by blast
        then show "RBT.lookup K (deferred_key d a) \<noteq> None" by (simp add: RBT.lookup_keys[symmetric] domIff)
      qed
      let ?H = "filter (\<lambda>z. RBT.lookup K (fst (snd z)) \<noteq> None) Dg"
      have H: "z \<in> set ?H \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = (a, deferred_key d a, shared_variable_list (\<sigma> a)))" for z
        using Dg inK by auto
      show ?thesis
      proof (cases "?H = []")
        case True
        have e: "?d' = d" using True by (simp add: deferred_goal_at_def at gK Let_def)
        have disj: "a |\<notin>| D" if "a |\<in>| ?V" for a
        proof
          assume "a |\<in>| D"
          then have "(a, deferred_key d a, shared_variable_list (\<sigma> a)) \<in> set ?H" using H that by blast
          then show False unfolding True by simp
        qed
        have fixg: "resolution_goal_substitute ?\<tau> (shared_goal_project ?T (shared_entry_goal h)) =
            shared_goal_project ?T (shared_entry_goal h)"
        proof (rule resolution_goal_substitute_outside)
          fix y assume "y |\<in>| resolution_goal_variables (shared_goal_project ?T (shared_entry_goal h))"
          then have "y |\<in>| ?V" using goal_entry_variables[OF hf] by simp
          then have "y |\<notin>| D" by (rule disj)
          then show "?\<tau> y = Finite_Variable y" using out[rule_format] by simp
        qed
        show ?thesis using e r K gf fixg at by (simp add: shared_goal_view_def table_extends_refl)
      next
        case False
        note hit = False
        obtain g' x' where gx: "shared_goal_substitute \<sigma> D (shared_entry_goal h) (shared_sharing ?s) = (g', x')"
          by (cases "shared_goal_substitute \<sigma> D (shared_entry_goal h) (shared_sharing ?s)")
        obtain h' x where hx: "enter_goal P x' g' = (h', x)" by (cases "enter_goal P x' g'")
        have meet: "?V |\<inter>| D \<noteq> {||}"
        proof -
          obtain z where "z \<in> set ?H" using last_in_set[OF hit] by blast
          then obtain a where "a |\<in>| D" "a |\<in>| ?V" using H by blast
          then show ?thesis by blast
        qed
        have esub: "shared_goal_entry_substitute P \<sigma> D h (shared_sharing ?s) = (h', x)"
          using meet gx hx by (simp add: shared_goal_entry_substitute_def)
        have x0: "share_state_formed (shared_sharing ?s)" using shared_entries_formed(3)[OF s] .
        note k = shared_goal_entry_substitute[where D = D, OF x0 hf \<sigma>f \<sigma>c out[rule_format]]
        have xf: "share_state_formed x" and ext: "table_extends ?T (share_state_table x)"
          and hf': "goal_entry_formed P (share_state_table x) q h'"
          and pj: "shared_goal_project (share_state_table x) (shared_entry_goal h') =
            resolution_goal_substitute ?\<tau> (shared_goal_project ?T (shared_entry_goal h))"
          using k esub by simp_all
        have vars': "z |\<in>| shared_goal_variables (shared_entry_goal h') \<longleftrightarrow>
            (z |\<in>| ?V \<and> z |\<notin>| D) \<or> (\<exists>a. a |\<in>| ?V \<and> a |\<in>| D \<and> z |\<in>| shared_pattern_variables (\<sigma> a))" for z
          using shared_goal_substituted_variables[OF x0 hf \<sigma>f \<sigma>c out, of z] esub by simp
        let ?I = "concat (map (\<lambda>z. snd (snd z)) ?H)"
        let ?K' = "fold (\<lambda>k t. RBT.insert k () t) (map (deferred_key d) ?I) (fold (\<lambda>z t. RBT.delete (fst (snd z)) t) ?H K)"
        let ?A = "map (\<lambda>y. fst (fst y)) (filter (\<lambda>y. snd (fst y)) ?I)"
        let ?R = "map (\<lambda>z. fst (fst (fst z))) (filter (\<lambda>z. snd (fst (fst z)) \<and>
          tree_range ?K' (\<lambda>k. k < (fst (fst (snd z)), True, 0)) (\<lambda>k. fst (fst (snd z)) < fst k) = []) ?H)"
        let ?s1 = "shared_reshare x ?s"
        define s2 where "s2 = shared_goal_write q h' (fset_of_list (map (\<lambda>y. fst (fst y)) ?I)) ?s1"
        define r2 where "r2 = search_goal_write q s2 ?A ?R ?r"
        let ?s2 = "s2"
        let ?r2 = "r2"
        have e: "?d' = d\<lparr>deferred_inner := ?r2, deferred_goal_records := RBT.insert q ?K' (deferred_goal_records d)\<rparr>"
          using hit unfolding r2_def s2_def by (simp add: deferred_goal_at_def at gK gx hx Let_def)
        have I: "y \<in> set ?I \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y |\<in>| shared_pattern_variables (\<sigma> a))" for y
        proof
          assume "y \<in> set ?I"
          then obtain w where w: "w \<in> set ?H" "y \<in> set (snd (snd w))" unfolding set_concat set_map by blast
          obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "w = (a, deferred_key d a, shared_variable_list (\<sigma> a))"
            using H w(1) by blast
          have "y \<in> set (shared_variable_list (\<sigma> a))" using w(2) unfolding a(3) by simp
          then have "y |\<in>| shared_pattern_variables (\<sigma> a)" using shared_variable_list[OF \<sigma>f] by simp
          then show "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y |\<in>| shared_pattern_variables (\<sigma> a)" using a(1,2) by blast
        next
          assume "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> y |\<in>| shared_pattern_variables (\<sigma> a)"
          then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "y |\<in>| shared_pattern_variables (\<sigma> a)" by blast
          have w: "(a, deferred_key d a, shared_variable_list (\<sigma> a)) \<in> set ?H" using H a(1,2) by blast
          have "y \<in> set (snd (snd (a, deferred_key d a, shared_variable_list (\<sigma> a))))"
            using a(3) shared_variable_list[OF \<sigma>f] by simp
          then show "y \<in> set ?I" using w unfolding set_concat set_map by blast
        qed
        have Hk: "z \<in> (\<lambda>z. fst (snd z)) ` set ?H \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a)" for z
        proof
          assume "z \<in> (\<lambda>z. fst (snd z)) ` set ?H"
          then obtain w where w: "w \<in> set ?H" "z = fst (snd w)" by blast
          obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "w = (a, deferred_key d a, shared_variable_list (\<sigma> a))"
            using H w(1) by blast
          have "z = deferred_key d a" using w(2) a(3) by simp
          then show "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a" using a(1,2) by blast
        next
          assume "\<exists>a. a |\<in>| D \<and> a |\<in>| ?V \<and> z = deferred_key d a"
          then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z = deferred_key d a" by blast
          have w: "(a, deferred_key d a, shared_variable_list (\<sigma> a)) \<in> set ?H" using H a(1,2) by blast
          have "z = fst (snd (a, deferred_key d a, shared_variable_list (\<sigma> a)))" using a(3) by simp
          then show "z \<in> (\<lambda>z. fst (snd z)) ` set ?H" using w by blast
        qed
        have keys': "set (RBT.keys ?K') = deferred_key d ` fset (shared_goal_variables (shared_entry_goal h'))"
        proof (rule set_eqI)
          fix z
          have "z \<in> set (RBT.keys ?K') \<longleftrightarrow> z \<in> deferred_key d ` set ?I \<or>
              (z \<in> set (RBT.keys K) \<and> z \<notin> (\<lambda>z. fst (snd z)) ` set ?H)"
            by (simp add: fold_insert_unit_keys fold_delete_keys)
          also have "\<dots> \<longleftrightarrow> z \<in> deferred_key d ` fset (shared_goal_variables (shared_entry_goal h'))"
          proof
            assume "z \<in> deferred_key d ` set ?I \<or> (z \<in> set (RBT.keys K) \<and> z \<notin> (\<lambda>z. fst (snd z)) ` set ?H)"
            then show "z \<in> deferred_key d ` fset (shared_goal_variables (shared_entry_goal h'))"
            proof
              assume "z \<in> deferred_key d ` set ?I"
              then obtain b a where ab: "a |\<in>| D" "a |\<in>| ?V" "b |\<in>| shared_pattern_variables (\<sigma> a)" "z = deferred_key d b"
                using I by blast
              have "b |\<in>| shared_goal_variables (shared_entry_goal h')" using vars'[of b] ab by blast
              then show ?thesis using ab(4) by blast
            next
              assume z: "z \<in> set (RBT.keys K) \<and> z \<notin> (\<lambda>z. fst (snd z)) ` set ?H"
              then obtain y where y: "y |\<in>| ?V" "z = deferred_key d y" unfolding keysK by blast
              have "y |\<notin>| D" using z y Hk by blast
              then have "y |\<in>| shared_goal_variables (shared_entry_goal h')" using vars'[of y] y(1) by blast
              then show ?thesis using y(2) by blast
            qed
          next
            assume "z \<in> deferred_key d ` fset (shared_goal_variables (shared_entry_goal h'))"
            then obtain y where y: "y |\<in>| shared_goal_variables (shared_entry_goal h')" "z = deferred_key d y" by blast
            from y(1)[unfolded vars'] show "z \<in> deferred_key d ` set ?I \<or>
                (z \<in> set (RBT.keys K) \<and> z \<notin> (\<lambda>z. fst (snd z)) ` set ?H)"
            proof (elim disjE conjE exE)
              assume yV: "y |\<in>| ?V" and yD: "y |\<notin>| D"
              have "z \<notin> (\<lambda>z. fst (snd z)) ` set ?H"
              proof
                assume "z \<in> (\<lambda>z. fst (snd z)) ` set ?H"
                then obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z = deferred_key d a" using Hk by blast
                have "a = y" using deferred_key_inj[OF N numV[OF a(2)] numV[OF yV]] a(3) y(2) by simp
                then show False using a(1) yD by simp
              qed
              then show ?thesis using yV y(2) keysK by blast
            next
              fix a assume "a |\<in>| ?V" "a |\<in>| D" "y |\<in>| shared_pattern_variables (\<sigma> a)"
              then show ?thesis using I y(2) by blast
            qed
          qed
          finally show "z \<in> set (RBT.keys ?K') \<longleftrightarrow> z \<in> deferred_key d ` fset (shared_goal_variables (shared_entry_goal h'))" .
        qed
        have num': "deferred_numbered d y" if "y |\<in>| shared_goal_variables (shared_entry_goal h')" for y
          using that[unfolded vars'] numV numI by blast
        have s1: "shared_state_formed \<kappa> P ?s1" using shared_reshare(1)[OF s xf ext] .
        have at1: "RBT.lookup (shared_goals ?s1) q = Some h" using at by (simp add: shared_reshare_def)
        have hf1: "goal_entry_formed P (shared_state_table ?s1) q h'" using hf' by (simp add: shared_reshare_def)
        have Apos: "\<forall>y. y |\<in>| shared_goal_variables (shared_entry_goal h') \<longrightarrow>
            y |\<notin>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> fst (fst y) |\<in>| fset_of_list (map (\<lambda>y. fst (fst y)) ?I)"
        proof (intro allI impI)
          fix y assume y: "y |\<in>| shared_goal_variables (shared_entry_goal h')"
            and n: "y |\<notin>| shared_goal_variables (shared_entry_goal h)"
          obtain a where "a |\<in>| ?V" "a |\<in>| D" "y |\<in>| shared_pattern_variables (\<sigma> a)" using y[unfolded vars'] n by blast
          then have "y \<in> set ?I" using I by blast
          then show "fst (fst y) |\<in>| fset_of_list (map (\<lambda>y. fst (fst y)) ?I)" by (simp add: fset_of_list_elem)
        qed
        note W = shared_goal_write[OF s1 at1 hf1 Apos, folded s2_def]
        have s2: "shared_state_formed \<kappa> P ?s2" by (rule W(1))
        have ext2: "table_extends ?T (shared_state_table ?s2)" using ext W(2) by (simp add: shared_reshare_def)
        have same2: "\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_goals ?s2) p = RBT.lookup (shared_goals ?s) p"
          using W(3) by (simp add: shared_reshare_def)
        have nodes2: "\<And>p. RBT.lookup (shared_nodes ?s2) p = RBT.lookup (shared_nodes ?s) p"
          using W(4) by (simp add: shared_reshare_def)
        have at2: "RBT.lookup (shared_goals ?s2) q = Some h'" by (simp only: W(3) if_True simp_thms)
        have regA: "\<forall>p. p |\<in>| shared_goal_registered h' \<longrightarrow> p |\<notin>| shared_goal_registered h \<longrightarrow> p \<in> set ?A"
        proof (intro allI impI)
          fix p assume p1: "p |\<in>| shared_goal_registered h'" and p0: "p |\<notin>| shared_goal_registered h"
          obtain a0 where y: "((p,True),a0) |\<in>| shared_goal_variables (shared_entry_goal h')"
            using p1 unfolding shared_goal_registered_member by blast
          have "((p,True),a0) |\<notin>| ?V" using p0 unfolding shared_goal_registered_member by blast
          then obtain a where "a |\<in>| ?V" "a |\<in>| D" "((p,True),a0) |\<in>| shared_pattern_variables (\<sigma> a)"
            using y[unfolded vars'] by blast
          then have pI: "((p,True),a0) \<in> set ?I" using I by blast
          have pF: "((p,True),a0) \<in> set (filter (\<lambda>y. snd (fst y)) ?I)"
            using pI by (simp only: set_filter mem_Collect_eq prod.sel simp_thms)
          show "p \<in> set ?A" unfolding set_map by (rule rev_image_eqI[OF pF]) (simp only: prod.sel)
        qed
        have regR: "\<forall>p. p \<in> set ?R \<longrightarrow> p |\<notin>| shared_goal_registered h'"
        proof (intro allI impI notI)
          fix p assume p: "p \<in> set ?R" and reg: "p |\<in>| shared_goal_registered h'"
          obtain z where zf: "z \<in> set (filter (\<lambda>z. snd (fst (fst z)) \<and>
              tree_range ?K' (\<lambda>k. k < (fst (fst (snd z)), True, 0)) (\<lambda>k. fst (fst (snd z)) < fst k) = []) ?H)"
            and pz: "p = fst (fst (fst z))" using p unfolding set_map by blast
          have z: "z \<in> set ?H" "snd (fst (fst z))"
            "tree_range ?K' (\<lambda>k. k < (fst (fst (snd z)), True, 0)) (\<lambda>k. fst (fst (snd z)) < fst k) = []"
            using zf by (simp_all only: set_filter mem_Collect_eq simp_thms)
          obtain a where a: "a |\<in>| D" "a |\<in>| ?V" "z = (a, deferred_key d a, shared_variable_list (\<sigma> a))" using H z(1) by blast
          obtain b where b: "((p,True),b) |\<in>| shared_goal_variables (shared_entry_goal h')"
            using reg unfolding shared_goal_registered_member by blast
          let ?n = "fst (deferred_key d a)"
          have kb: "deferred_key d ((p,True),b) \<in> set (RBT.keys ?K')" using keys' b by blast
          have fk: "fst (deferred_key d ((p,True),b)) = ?n" using pz a(3) by (simp add: deferred_key_def)
          have LR: "key_range (\<lambda>k. k < (?n, True, 0)) (\<lambda>k. ?n < fst k)"
            unfolding key_range_def by (auto simp: less_eq_prod_def less_prod_def)
          have inr: "\<not> deferred_key d ((p,True),b) < (?n, True, 0) \<and> \<not> ?n < fst (deferred_key d ((p,True),b))"
            using fk by (auto simp: deferred_key_def less_prod_def)
          have "(deferred_key d ((p,True),b), ()) \<in> set (RBT.entries ?K')" using kb by (simp add: RBT.keys_entries)
          then have inT: "(deferred_key d ((p,True),b), ()) \<in> set (tree_range ?K' (\<lambda>k. k < (?n, True, 0)) (\<lambda>k. ?n < fst k))"
            using inr by (simp add: tree_range_entries[OF LR])
          have emp: "tree_range ?K' (\<lambda>k. k < (?n, True, 0)) (\<lambda>k. ?n < fst k) = []"
            using z(3) unfolding a(3) by (simp only: prod.sel)
          show False using inT unfolding emp by simp
        qed
        have nodes2': "\<forall>p. p \<noteq> q \<longrightarrow> RBT.lookup (shared_nodes ?s2) p = RBT.lookup (shared_nodes ?s) p" using nodes2 by simp
        note G = search_goal_write[OF r K s2 ext2 same2 nodes2' at at2 regA regR, folded r2_def]
        have gq: "deferred_goal_formed ?d' q" unfolding deferred_goal_formed_def e using G(3) at2 keys' num' by simp
        have vq: "shared_goal_view (search_state ?r2) q = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view ?s q)"
          using G(3) at2 at pj W(2) by (simp add: shared_goal_view_def shared_reshare_def)
        have w2: "shared_witnesses (search_state ?r2) = shared_witnesses ?s" using G(3) W(5) by (simp add: shared_reshare_def)
        have t2: "search_table ?r2 = shared_state_table ?s2" using G(3) by simp
        show ?thesis unfolding e using G(1,2,3) ext2 t2 nodes2 vq same2 w2 gq[unfolded e] by auto
      qed
    qed
  qed
qed

lemma deferred_goals_fold:
  assumes r: "search_formed \<kappa> P (deferred_inner d)" and K: "search_classes_formed (deferred_inner d)"
    and tf0: "table_formed T0" and ext: "table_extends T0 (search_table (deferred_inner d))"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
    and Dg: "\<And>z. z \<in> set Dg \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> z = (a, deferred_key d a, shared_variable_list (\<sigma> a)))"
    and N: "positions_numbered (deferred_positions d)"
    and numI: "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered d b"
    and gf: "\<And>q. deferred_goal_formed d q" and qs: "distinct qs"
  shows "search_formed \<kappa> P (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d)) \<and>
    search_classes_formed (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d)) \<and>
    table_extends T0 (search_table (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d))) \<and>
    (\<forall>p. RBT.lookup (shared_nodes (search_state (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p) \<and>
    (\<forall>p. shared_goal_view (search_state (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d))) p = (if p \<in> set qs then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a)))
        (shared_goal_view (search_state (deferred_inner d)) p)
      else shared_goal_view (search_state (deferred_inner d)) p)) \<and>
    (\<forall>p. shared_node_view (search_state (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d))) p =
      shared_node_view (search_state (deferred_inner d)) p) \<and>
    shared_witnesses (search_state (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs d))) =
      shared_witnesses (search_state (deferred_inner d)) \<and>
    (\<forall>q. deferred_goal_formed (fold (deferred_goal_at P \<sigma> D Dg) qs d) q) \<and>
    deferred_positions (fold (deferred_goal_at P \<sigma> D Dg) qs d) = deferred_positions d \<and>
    deferred_names (fold (deferred_goal_at P \<sigma> D Dg) qs d) = deferred_names d \<and>
    deferred_tree (fold (deferred_goal_at P \<sigma> D Dg) qs d) = deferred_tree d \<and>
    deferred_records (fold (deferred_goal_at P \<sigma> D Dg) qs d) = deferred_records d \<and>
    deferred_holders (fold (deferred_goal_at P \<sigma> D Dg) qs d) = deferred_holders d"
  using r K ext Dg N numI gf qs
proof (induction qs arbitrary: d)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  let ?d1 = "deferred_goal_at P \<sigma> D Dg q d"
  have s: "shared_state_formed \<kappa> P (search_state (deferred_inner d))" using search_formedD(1)[OF Cons.prems(1)] .
  have tf1: "table_formed (search_table (deferred_inner d))" using shared_entries_formed(4)[OF s] .
  have \<sigma>t: "\<And>a. shared_pattern_formed (search_table (deferred_inner d)) (\<sigma> a)"
    using shared_pattern_extends(1)[OF tf0 \<sigma>f Cons.prems(3)] .
  have \<tau>: "(\<lambda>a. shared_pattern_project (search_table (deferred_inner d)) (\<sigma> a)) = (\<lambda>a. shared_pattern_project T0 (\<sigma> a))"
    using shared_pattern_extends(2)[OF tf0 \<sigma>f Cons.prems(3)] by simp
  note A = deferred_goal_at[OF Cons.prems(1,2) \<sigma>t \<sigma>c out Cons.prems(4,5,6) Cons.prems(7)[of q]]
  have keysE: "deferred_key ?d1 = deferred_key d" using A by (simp add: fun_eq_iff deferred_key_def)
  have numE: "deferred_numbered ?d1 = deferred_numbered d" using A by (simp add: fun_eq_iff deferred_numbered_def)
  have T1: "table_extends (search_table (deferred_inner d)) (search_table (deferred_inner ?d1))" using A by blast
  have r1: "search_formed \<kappa> P (deferred_inner ?d1)" and K1: "search_classes_formed (deferred_inner ?d1)" using A by blast+
  have e1: "table_extends T0 (search_table (deferred_inner ?d1))" using table_extends_trans[OF Cons.prems(3) T1] .
  have Dg1: "\<And>z. z \<in> set Dg \<longleftrightarrow> (\<exists>a. a |\<in>| D \<and> z = (a, deferred_key ?d1 a, shared_variable_list (\<sigma> a)))"
    using Cons.prems(4) keysE by simp
  have N1: "positions_numbered (deferred_positions ?d1)" using Cons.prems(5) A by simp
  have numI1: "\<forall>a b. a |\<in>| D \<longrightarrow> b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> deferred_numbered ?d1 b"
    using Cons.prems(6) numE by simp
  have gf1: "deferred_goal_formed ?d1 q'" for q'
  proof (cases "q' = q")
    case True
    then show ?thesis using A by simp
  next
    case False
    show ?thesis
    proof (rule deferred_goal_formed_same[OF Cons.prems(7)[of q']])
      show "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner ?d1))) q' = Some h' \<Longrightarrow>
          \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q' = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
        using A False by simp
      show "RBT.lookup (deferred_goal_records ?d1) q' = RBT.lookup (deferred_goal_records d) q'" using A False by simp
      show "\<And>x. deferred_numbered d x \<Longrightarrow> deferred_key ?d1 x = deferred_key d x \<and> deferred_numbered ?d1 x"
        using keysE numE by simp
    qed
  qed
  have qsd: "distinct qs" and nq: "q \<notin> set qs" using Cons.prems(8) by simp_all
  have v1: "shared_goal_view (search_state (deferred_inner ?d1)) p = (if p = q then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (shared_goal_view (search_state (deferred_inner d)) p)
      else shared_goal_view (search_state (deferred_inner d)) p)" for p
  proof (cases "p = q")
    case True
    then show ?thesis using A \<tau> by simp
  next
    case False
    show ?thesis
    proof (cases "RBT.lookup (shared_goals (search_state (deferred_inner d))) p")
      case (Some h)
      have "RBT.lookup (shared_goals (search_state (deferred_inner ?d1))) p = Some h" using A False Some by simp
      then show ?thesis using goal_entry_extends[OF tf1 shared_entries_formed(1)[OF s Some] T1] Some False
        by (simp add: shared_goal_view_def)
    next
      case None
      have "RBT.lookup (shared_goals (search_state (deferred_inner ?d1))) p = None" using A False None by simp
      then show ?thesis using None False by (simp add: shared_goal_view_def)
    qed
  qed
  have n1: "shared_node_view (search_state (deferred_inner ?d1)) p = shared_node_view (search_state (deferred_inner d)) p" for p
  proof (cases "RBT.lookup (shared_nodes (search_state (deferred_inner d))) p")
    case (Some hn)
    have "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) p = Some hn" using A Some by simp
    then show ?thesis using node_entry_extends[OF tf1 shared_entries_formed(2)[OF s Some] T1] Some
      by (simp add: shared_node_view_def)
  next
    case None
    have "RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) p = None" using A None by simp
    then show ?thesis using None by (simp add: shared_node_view_def)
  qed
  note IH = Cons.IH[OF r1 K1 e1 Dg1 N1 numI1 gf1 qsd]
  have gv: "shared_goal_view (search_state (deferred_inner (fold (deferred_goal_at P \<sigma> D Dg) qs ?d1))) p = (if p \<in> set (q # qs) then
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (shared_goal_view (search_state (deferred_inner d)) p)
      else shared_goal_view (search_state (deferred_inner d)) p)" for p
  proof (cases "p = q")
    case True
    then show ?thesis using IH nq v1[of q] by simp
  next
    case False
    then show ?thesis using IH v1[of p] by simp
  qed
  show ?case using IH gv n1 A by simp
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
    let D = shared_binding_domain s'; \<sigma> = shared_binding_substitution s';
      d1 = d\<lparr>deferred_names := deferred_number_names (deferred_bound_names s') (deferred_names d)\<rparr>;
      Dg = map (\<lambda>a. (a, deferred_key d1 a, shared_variable_list (\<sigma> a))) (map fst s');
      r1 = search_share x (deferred_inner d1);
      d2 = fold (deferred_goal_at P \<sigma> D Dg) (sorted_list_of_fset (shared_substitute_positions D (search_state r1)))
        ((d1\<lparr>deferred_tree := binding_tree_bind (deferred_key d1) (deferred_tree d1) s'\<rparr>)\<lparr>deferred_inner := r1\<rparr>)
    in fold (deferred_update_at (deferred_domain_keys d2 \<sigma> D))
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
  let ?Dg = "map (\<lambda>a. (a, deferred_key ?d1 a, shared_variable_list (?\<sigma> a))) (map fst s')"
  let ?r1 = "search_share x ?r"
  let ?d0 = "(?d1\<lparr>deferred_tree := ?K1\<rparr>)\<lparr>deferred_inner := ?r1\<rparr>"
  let ?qs = "sorted_list_of_fset (shared_substitute_positions ?D (search_state ?r1))"
  define d2 where "d2 = fold (deferred_goal_at P ?\<sigma> ?D ?Dg) ?qs ?d0"
  let ?d2 = "d2"
  let ?r2 = "deferred_inner ?d2"
  let ?ns = "sorted_list_of_fset (ffUnion (fimage (\<lambda>a. tree_bucket (deferred_holders ?d2) (deferred_key ?d2 a)) ?D))"
  have eq0: "deferred_bind P s d = fold (deferred_update_at (deferred_domain_keys ?d2 ?\<sigma> ?D)) ?ns ?d2"
    unfolding d2_def by (simp add: deferred_bind_def kc Let_def)
  have eq: "deferred_bind P s d = fold (deferred_update ?\<sigma> ?D) ?ns ?d2" using eq0 deferred_update_at_fold by simp
  have r1: "search_formed \<kappa> P ?r1" using search_share(1)[OF r xf extx] .
  have tbl1: "search_table ?r1 = ?Tx" using search_share(3)[OF r xf extx] .
  have K1: "search_classes_formed ?r1" by (rule search_share_classes[OF r xf extx K])
  have s1f: "shared_state_formed \<kappa> P (search_state ?r1)" using search_formedD(1)[OF r1] .
  have gf0: "deferred_goal_formed ?d0 q" for q
  proof (rule deferred_goal_formed_same[OF deferred_renumbered_goal[OF re parts deferred_formedD(12)[OF d]]])
    show "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner ?d0))) q = Some h' \<Longrightarrow>
      \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner ?d1))) q = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
      using search_share(4)[OF r xf extx] by simp
    show "RBT.lookup (deferred_goal_records ?d0) q = RBT.lookup (deferred_goal_records ?d1) q" by simp
    show "\<And>y. deferred_numbered ?d1 y \<Longrightarrow> deferred_key ?d0 y = deferred_key ?d1 y \<and> deferred_numbered ?d0 y" by simp
  qed
  have Dg: "z \<in> set ?Dg \<longleftrightarrow> (\<exists>a. a |\<in>| ?D \<and> z = (a, deferred_key ?d0 a, shared_variable_list (?\<sigma> a)))" for z
    using Dm keys by auto
  have N0: "positions_numbered (deferred_positions ?d0)" using N by simp
  have num0: "\<forall>a b. a |\<in>| ?D \<longrightarrow> b |\<in>| shared_pattern_variables (?\<sigma> a) \<longrightarrow> deferred_numbered ?d0 b"
    using num\<sigma> by auto
  have outA: "\<forall>a. a |\<notin>| ?D \<longrightarrow> ?\<sigma> a = Shared_Variable a" using out by blast
  have qsd: "distinct ?qs" by simp
  have ext0: "table_extends ?Tx (search_table (deferred_inner ?d0))" using tbl1 by (simp add: table_extends_refl)
  have r0: "search_formed \<kappa> P (deferred_inner ?d0)" and K0: "search_classes_formed (deferred_inner ?d0)" using r1 K1 by simp_all
  note GS = deferred_goals_fold[OF r0 K0 tfx ext0 \<sigma>f \<sigma>c outA Dg N0 num0 gf0 qsd, folded d2_def]
  have r2: "search_formed \<kappa> P ?r2" and K2: "search_classes_formed ?r2" and ext2: "table_extends ?Tx (search_table ?r2)"
    using GS by simp_all
  have E2: "deferred_positions ?d2 = deferred_positions d" "deferred_names ?d2 = deferred_names ?d1"
    "deferred_tree ?d2 = ?K1" "deferred_records ?d2 = deferred_records d" "deferred_holders ?d2 = deferred_holders d"
    using GS by simp_all
  have keyE2: "deferred_key ?d2 = deferred_key ?d1" using E2 by (simp add: fun_eq_iff deferred_key_def)
  have numE2: "deferred_numbered ?d2 = deferred_numbered ?d1" using E2 by (simp add: fun_eq_iff deferred_numbered_def)
  note E2s [simp] = E2 keyE2 numE2
  have goals2: "\<forall>q. deferred_goal_formed ?d2 q" using GS by simp
  have st2: "deferred_store ?d2 = store_bind ?S ?\<sigma> ?D"
  proof -
    have "deferred_store (?d1\<lparr>deferred_tree := binding_tree_bind (deferred_key ?d1) (deferred_tree ?d1) s'\<rparr>) =
        store_bind (deferred_store ?d1) ?\<sigma> ?D"
      by (rule deferred_store_bind[OF N1]) (metis Dm keys numD)
    moreover have "deferred_store ?d2 = deferred_store (?d1\<lparr>deferred_tree := ?K1\<rparr>)"
      unfolding deferred_store_def keyE2 E2(3) by (simp add: deferred_key_def)
    ultimately show ?thesis using st1 by simp
  qed
  let ?T2 = "search_table ?r2"
  have nodes2: "RBT.lookup (shared_nodes (search_state ?r2)) p = RBT.lookup (shared_nodes ?s) p" for p
    using GS search_share(5)[OF r xf extx] by simp
  have proj2: "search_project ?r2 = Resolution_State (fimage (resolution_goal_substitute ?\<tau>0) (resolution_pending (search_project ?r)))
      (resolution_nodes (search_project ?r)) (resolution_witnesses (search_project ?r))"
  proof -
    let ?\<tau>x = "\<lambda>a. shared_pattern_project ?Tx (?\<sigma> a)"
    have \<tau>x: "?\<tau>x = ?\<tau>0" using \<tau> by (simp add: fun_eq_iff)
    have g: "shared_goal_view (search_state ?r2) p = map_option (resolution_goal_substitute ?\<tau>x) (shared_goal_view (search_state ?r1) p)"
      for p
    proof (cases "p \<in> set ?qs")
      case True
      then show ?thesis using GS by simp
    next
      case False
      then have pn: "p |\<notin>| shared_substitute_positions ?D (search_state ?r1)" by simp
      have "shared_goal_view (search_state ?r1) p =
          map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table (search_state ?r1)) (?\<sigma> a)))
            (shared_goal_view (search_state ?r1) p)"
        by (rule shared_substitute_unvisited(1)[OF s1f _ pn]) (rule out)
      then show ?thesis using GS False tbl1 by simp
    qed
    have n: "shared_node_view (search_state ?r2) p = map_option id (shared_node_view (search_state ?r1) p)" for p
      using GS by (simp add: option.map_id)
    have w: "shared_witnesses (search_state ?r2) = shared_witnesses (search_state ?r1)" using GS by simp
    show ?thesis using shared_state_project_views[OF g n w] search_share(2)[OF r xf extx] \<tau>x by (simp add: fset.map_id)
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
        (RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None \<or>
          (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
    proof (intro allI impI)
      fix q h y assume gq: "RBT.lookup (shared_goals (search_state (deferred_inner ?d2))) q = Some h"
        and yv: "y |\<in>| shared_goal_variables (shared_entry_goal h)"

      have gq2: "RBT.lookup (shared_goals (search_state ?r2)) q = Some h" using gq by simp
      have "shared_goal_project ?T2 (shared_entry_goal h) |\<in>| resolution_pending (search_project ?r2)"
        unfolding shared_state_project_member(1) using gq2 by blast
      then obtain g0 where g0: "g0 |\<in>| resolution_pending (search_project ?r)"
        and ge: "shared_goal_project ?T2 (shared_entry_goal h) = resolution_goal_substitute ?\<tau>0 g0"
        unfolding proj2 by auto
      obtain q0 h0 where h0: "RBT.lookup (shared_goals ?s) q0 = Some h0"
        and g0e: "shared_goal_project ?T (shared_entry_goal h0) = g0"
        using g0 unfolding shared_state_project_member(1) by blast
      let ?A = "{z. binding_map (store_bind ?S ?\<sigma> ?D) z = None \<and> (RBT.lookup (shared_nodes ?s) (fst (fst z)) \<noteq> None \<or>
          (fst (fst z) = [] \<and> (\<exists>rr e p. shared_entry_goal h0 = Shared_Call_Goal [] rr e p)))}"
      have old: "binding_map ?S z = None \<and> (RBT.lookup (shared_nodes ?s) (fst (fst z)) \<noteq> None \<or>
          (fst (fst z) = [] \<and> (\<exists>rr e p. shared_entry_goal h0 = Shared_Call_Goal [] rr e p)))"
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
      then have yA: "y \<in> ?A" using within by blast
      have hc: "\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p"
        if c0: "\<exists>rr e p. shared_entry_goal h0 = Shared_Call_Goal [] rr e p"
      proof -
        obtain rr1 e1 p1 where c: "shared_entry_goal h0 = Shared_Call_Goal [] rr1 e1 p1" using c0 by blast
        have "\<exists>p'. shared_goal_project ?T2 (shared_entry_goal h) = Resolution_Call_Goal [] rr1 e1 p'"
          using ge g0e[symmetric] c by simp
        then obtain p' where p': "shared_goal_project ?T2 (shared_entry_goal h) = Resolution_Call_Goal [] rr1 e1 p'" by blast
        obtain gp where "shared_entry_goal h = Shared_Call_Goal [] rr1 e1 gp" using shared_goal_project_call[OF p'] by blast
        then show ?thesis by blast
      qed
      show "binding_map (deferred_store ?d2) y = None \<and>
          (RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) (fst (fst y)) \<noteq> None \<or>
            (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
        using yA hc st2 nodes2 by auto
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
        fBall (shared_pattern_variables (binding_resolve ?S (shared_derivation_call (shared_entry_node hn)))) (deferred_numbered ?d2) \<and>
        fBall (shared_pattern_variables (binding_resolve ?S (shared_derivation_call (shared_entry_node hn))))
          (\<lambda>x. position_number (deferred_positions ?d2) q |\<in>| tree_bucket (deferred_holders ?d2) (deferred_key ?d2 x))"
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
  have r2f: "shared_state_formed \<kappa> P (search_state ?r2)" using search_formedD(1)[OF r2] .
  have tf2: "table_formed ?T2" using shared_entries_formed(4)[OF r2f] .
  have st2m: "store_memoized ?T2 (store_bind ?S ?\<sigma> ?D) (search_table (deferred_inner ?d2)) (deferred_store ?d2)"
    using store_memoized_refl[OF S'f tf2] st2 by simp
  have c02: "\<forall>q hn. RBT.lookup (shared_nodes (search_state (deferred_inner ?d2))) q = Some hn \<longrightarrow>
      position_number (deferred_positions ?d2) q \<in> set ?ns \<longrightarrow> shared_pattern_formed ?T2 (shared_derivation_call (shared_entry_node hn))"
    using shared_entries_formed(2)[OF r2f] by (auto simp: node_entry_formed_def shared_derivation_formed_def)
  note FOLD = deferred_update_fold[OF parts2 S2' ready2' st2m num2 nsd stale2 formed2 tf2 S'f c02 goals2]
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

text \<open>The positions of the goals a placed clause puts below its node: one at each of its premise sockets.\<close>

definition deferred_placed_positions :: "'s::linorder list \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's list list" where
  "deferred_placed_positions q S = sorted_list_of_fset (fimage (\<lambda>z. q @ [fst z]) (finite_schema_premises S) |\<union>|
    fimage (\<lambda>z. q @ [fst z]) (finite_schema_materials S))"

lemma deferred_placed_positions:
  "set (deferred_placed_positions q S) = fset (fimage resolution_goal_position (finite_clause_goals q d c S))"
  by (force simp: deferred_placed_positions_def finite_clause_goals_def fimage.rep_eq)

definition deferred_place :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    's list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_place P dd q e c S = (let r' = search_call_place P (deferred_inner dd) q e c S in
    case RBT.lookup (shared_nodes (search_state r')) q of None \<Rightarrow> dd\<lparr>deferred_inner := r'\<rparr>
    | Some hn \<Rightarrow> deferred_record_goals (deferred_placed_positions q (shared_derivation_schema (shared_entry_node hn)))
        (deferred_record_node q (shared_derivation_call (shared_entry_node hn)) (dd\<lparr>deferred_inner := r'\<rparr>)))"

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
    and "deferred_inner (deferred_place P dd q e c S) = search_call_place P (deferred_inner dd) q e c S"
    and "deferred_store (deferred_place P dd q e c S) = deferred_store dd"
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
  let ?ds = "dd\<lparr>deferred_inner := ?r'\<rparr>"
  have S': "binding_store_formed ?T' ?S" using binding_store_formed_extended[OF S tf] ext by (simp add: table_extends_def)
  have parts0: "deferred_parts_formed \<kappa> P ?ds"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner ?ds)" using r' by simp
    show "search_classes_formed (deferred_inner ?ds)" using K' by simp
    show "positions_numbered (deferred_positions ?ds)" using parts unfolding deferred_parts_formed_def by simp
    show "binding_store_formed (search_table (deferred_inner ?ds)) (deferred_store ?ds)" using S' by simp
    have tk: "\<forall>k v. RBT.lookup (snd (deferred_tree dd)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered dd y \<and> deferred_key dd y = k)"
      using parts unfolding deferred_parts_formed_def by blast
    show "\<forall>k v. RBT.lookup (snd (deferred_tree ?ds)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered ?ds y \<and> deferred_key ?ds y = k)"
      using tk by simp
    show "\<forall>y. binding_map (deferred_store ?ds) y \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) (fst (fst y)) \<noteq> None"
    proof (intro allI impI)
      fix y assume b: "binding_map (deferred_store ?ds) y \<noteq> None"
      have bnd: "\<And>y. binding_map ?S y \<noteq> None \<Longrightarrow> RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      have "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" using bnd b by simp
      then show "RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) (fst (fst y)) \<noteq> None"
        using old_nodes[OF bound_ne] b by simp
    qed
    show "\<forall>q' h' y. RBT.lookup (shared_goals (search_state (deferred_inner ?ds))) q' = Some h' \<longrightarrow>
        y |\<in>| shared_goal_variables (shared_entry_goal h') \<longrightarrow> binding_map (deferred_store ?ds) y = None \<and>
        (RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) (fst (fst y)) \<noteq> None \<or>
          (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h' = Shared_Call_Goal [] rr e p)))"
    proof (intro allI impI)
      fix q' h' y assume gq: "RBT.lookup (shared_goals (search_state (deferred_inner ?ds))) q' = Some h'"
        and yv: "y |\<in>| shared_goal_variables (shared_entry_goal h')"
      have gq': "RBT.lookup (shared_goals (search_state ?r')) q' = Some h'" using gq by simp
      let ?g' = "shared_goal_project ?T' (shared_entry_goal h')"
      have yv': "y |\<in>| resolution_goal_variables ?g'"
        using yv goal_entry_variables[OF shared_entries_formed(1)[OF st' gq']] by simp
      have m: "?g' |\<in>| resolution_pending (search_project ?r')" unfolding shared_state_project_member(1) using gq' by blast
      have "?g' |\<in>| ?G |\<union>| (resolution_pending ?st |-| {|?g|})" using m unfolding pj resolution_state.sel(1) .
      then have "?g' |\<in>| ?G \<or> ?g' |\<in>| resolution_pending ?st" by (simp only: funion_iff fminus_iff) blast
      have gcl: "\<And>q h y. RBT.lookup (shared_goals ?s) q = Some h \<Longrightarrow> y |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow>
          binding_map ?S y = None \<and> (RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None \<or>
            (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
        using parts unfolding deferred_parts_formed_def by blast
      consider (new) "?g' |\<in>| ?G" | (old) "?g' |\<in>| resolution_pending ?st" using \<open>?g' |\<in>| ?G \<or> _\<close> by blast
      then have ok: "binding_map ?S y = None \<and> (RBT.lookup (shared_nodes (search_state ?r')) (fst (fst y)) \<noteq> None \<or>
          (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h' = Shared_Call_Goal [] rr e p)))"
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
        have o: "binding_map ?S y = None \<and> (RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None \<or>
            (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h0 = Shared_Call_Goal [] rr e p)))" by (rule gcl[OF h0 yh])
        show ?thesis
        proof (cases "RBT.lookup (shared_nodes ?s) (fst (fst y)) = None")
          case False
          then have ne: "fst (fst y) \<noteq> q" using noq_at by auto
          then show ?thesis using o False old_nodes[OF ne] by simp
        next
          case True
          then obtain rr0 e1 p0 where r0: "fst (fst y) = []" "shared_entry_goal h0 = Shared_Call_Goal [] rr0 e1 p0"
            using o by blast
          have pj0: "shared_goal_project ?T' (shared_entry_goal h') = Resolution_Call_Goal [] rr0 e1 (shared_pattern_project ?T p0)"
            using e0[symmetric] r0(2) by simp
          obtain gp where "shared_entry_goal h' = Shared_Call_Goal [] rr0 e1 gp" using shared_goal_project_call[OF pj0] by blast
          then show ?thesis using o r0 by blast
        qed
      qed
      then show "binding_map (deferred_store ?ds) y = None \<and>
          (RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) (fst (fst y)) \<noteq> None \<or>
            (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h' = Shared_Call_Goal [] rr e p)))" by simp
    qed
    show "\<forall>n q' K. RBT.lookup (deferred_records ?ds) n = Some (q', K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions ?ds) q' \<and> RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) q' \<noteq> None"
    proof (intro allI impI)
      fix n q' K assume rq: "RBT.lookup (deferred_records ?ds) n = Some (q', K)"
      have recs: "\<And>n q' K. RBT.lookup (deferred_records dd) n = Some (q', K) \<Longrightarrow> n \<noteq> 0 \<and>
          n = position_number (deferred_positions dd) q' \<and> RBT.lookup (shared_nodes ?s) q' \<noteq> None"
        using parts unfolding deferred_parts_formed_def by blast
      have o: "n \<noteq> 0 \<and> n = position_number (deferred_positions dd) q' \<and> RBT.lookup (shared_nodes ?s) q' \<noteq> None"
        using recs rq by simp
      then have "q' \<noteq> q" using noq_at by auto
      then show "n \<noteq> 0 \<and> n = position_number (deferred_positions ?ds) q' \<and>
          RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) q' \<noteq> None" using o old_nodes by simp
    qed
  qed
  have nf0: "deferred_node_formed ?ds q'" if "q' \<noteq> q" for q'
    using nfs[of q'] old_nodes[OF that] unfolding deferred_node_formed_def by simp
  have at0: "RBT.lookup (shared_nodes (search_state (deferred_inner ?ds))) q = Some hq" using hq by simp
  have unb: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow> binding_map (deferred_store ?ds) x = None"
    using cvars bound_ne by fastforce
  have plc: "\<And>x. x |\<in>| shared_pattern_variables ?c \<Longrightarrow>
      fst (fst x) = q \<or> position_number (deferred_positions ?ds) (fst (fst x)) \<noteq> 0" using cvars by blast
  have unbA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow> binding_map (deferred_store ?ds) x = None" using unb by blast
  have plcA: "\<forall>x. x |\<in>| shared_pattern_variables ?c \<longrightarrow>
      fst (fst x) = q \<or> position_number (deferred_positions ?ds) (fst (fst x)) \<noteq> 0" using plc by blast
  note R = deferred_record_node[OF parts0 at0 refl unbA plcA]
  let ?dr = "deferred_record_node q ?c ?ds"
  have schema: "shared_derivation_schema (shared_entry_node hq) = S"
    using arg_cong[OF hqp, of resolution_node_schema] by (simp add: shared_derivation_project_def finite_clause_node_def)
  let ?ps = "deferred_placed_positions q S"
  have eq: "deferred_place P dd q e c S = deferred_record_goals ?ps ?dr" by (simp add: deferred_place_def Let_def hq schema)
  have psG: "set ?ps = fset (fimage resolution_goal_position ?G)" by (rule deferred_placed_positions)
  have dps: "resolution_positions_distinct (search_project ?r')" using CP(3) by (simp add: search_placeable_def)
  have inr: "deferred_inner ?dr = ?r'" using R(4) by simp
  have goal_pos: "shared_goal_position (shared_entry_goal h') = p'"
    if "RBT.lookup (shared_goals (search_state ?r')) p' = Some h'" for p' h'
    using shared_entries_formed(1)[OF st' that] by (simp add: goal_entry_formed_def)
  have new_goal: "shared_goal_project ?T' (shared_entry_goal h') |\<in>| ?G"
    if a: "RBT.lookup (shared_goals (search_state ?r')) p' = Some h'" and p': "p' \<in> set ?ps" for p' h'
  proof -
    obtain g0 where g0: "g0 |\<in>| ?G" "resolution_goal_position g0 = p'" using p' psG by auto
    have gm: "g0 |\<in>| resolution_pending (search_project ?r')" using g0(1) pj by simp
    have hm: "shared_goal_project ?T' (shared_entry_goal h') |\<in>| resolution_pending (search_project ?r')"
      unfolding shared_state_project_member(1) using a by blast
    have "resolution_goal_position (shared_goal_project ?T' (shared_entry_goal h')) = p'" using goal_pos[OF a] by simp
    then have "shared_goal_project ?T' (shared_entry_goal h') = g0"
      using dps gm hm g0(2) unfolding resolution_positions_distinct_def by metis
    then show ?thesis using g0(1) by simp
  qed
  have pl: "position_number (deferred_positions ?dr) (fst (fst x)) \<noteq> 0"
    if p': "p' \<in> set ?ps" and a: "RBT.lookup (shared_goals (search_state (deferred_inner ?dr))) p' = Some h'"
      and nr: "\<not> shared_root_goal (shared_entry_goal h')" and x: "x |\<in>| shared_goal_variables (shared_entry_goal h')" for p' h' x
  proof -
    have a': "RBT.lookup (shared_goals (search_state ?r')) p' = Some h'" using a inr by simp
    have "x |\<in>| resolution_goal_variables (shared_goal_project ?T' (shared_entry_goal h'))"
      using x goal_entry_variables[OF shared_entries_formed(1)[OF st' a']] by simp
    then have "fst (fst x) = q" by (rule finite_clause_goals_positioned[OF new_goal[OF a' p']])
    then show ?thesis using R(7) by simp
  qed
  have rt: "RBT.lookup (deferred_goal_records ?dr) p' = None"
    if p': "p' \<in> set ?ps" and a: "RBT.lookup (shared_goals (search_state (deferred_inner ?dr))) p' = Some h'"
      and rg: "shared_root_goal (shared_entry_goal h')" for p' h'
  proof -
    have a': "RBT.lookup (shared_goals (search_state ?r')) p' = Some h'" using a inr by simp
    have "p' = []" using goal_pos[OF a'] rg by (auto simp: shared_root_goal_iff)
    moreover have "p' \<noteq> []" using p' by (auto simp: deferred_placed_positions_def)
    ultimately show ?thesis by simp
  qed
  have ot: "deferred_goal_formed ?dr q'" if q': "q' \<notin> set ?ps" for q'
  proof (rule deferred_goal_formed_cong[OF deferred_formedD(12)[OF dd, of q']])
    fix h' assume a: "RBT.lookup (shared_goals (search_state (deferred_inner ?dr))) q' = Some h'"
    have a': "RBT.lookup (shared_goals (search_state ?r')) q' = Some h'" using a inr by simp
    let ?g' = "shared_goal_project ?T' (shared_entry_goal h')"
    have m: "?g' |\<in>| resolution_pending (search_project ?r')" unfolding shared_state_project_member(1) using a' by blast
    have m': "?g' |\<in>| ?G |\<union>| (resolution_pending ?st |-| {|?g|})" using m unfolding pj resolution_state.sel(1) .
    have pq: "resolution_goal_position ?g' = q'" using goal_pos[OF a'] by simp
    have nG: "?g' |\<notin>| ?G" using q' psG pq by force
    then have old: "?g' |\<in>| resolution_pending ?st" using m' by simp
    then obtain q0 h0 where h0: "RBT.lookup (shared_goals ?s) q0 = Some h0"
      and e0: "shared_goal_project ?T (shared_entry_goal h0) = ?g'"
      unfolding shared_state_project_member(1) by blast
    have "shared_goal_position (shared_entry_goal h0) = q0"
      using shared_entries_formed(1)[OF st h0] by (simp add: goal_entry_formed_def)
    then have q0: "q0 = q'" using e0 pq shared_goal_project_position[of ?T "shared_entry_goal h0"] by simp
    have v: "shared_goal_variables (shared_entry_goal h') = shared_goal_variables (shared_entry_goal h0)"
      using goal_entry_variables[OF shared_entries_formed(1)[OF st' a']]
        goal_entry_variables[OF shared_entries_formed(1)[OF st h0]] e0 by simp
    have rr: "shared_root_goal (shared_entry_goal h') \<longleftrightarrow> shared_root_goal (shared_entry_goal h0)"
      using shared_root_goal_project[of "shared_entry_goal h'" ?T'] shared_root_goal_project[of "shared_entry_goal h0" ?T] e0
      by simp
    show "\<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner dd))) q' = Some h \<and>
        shared_goal_variables (shared_entry_goal h') = shared_goal_variables (shared_entry_goal h) \<and>
        (shared_root_goal (shared_entry_goal h') \<longleftrightarrow> shared_root_goal (shared_entry_goal h))"
      using h0 q0 v rr by blast
  next
    show "RBT.lookup (deferred_goal_records ?dr) q' = RBT.lookup (deferred_goal_records dd) q'" by simp
  next
    fix y assume y: "deferred_numbered dd y"
    have "deferred_key ?dr y = deferred_key ?ds y \<and> deferred_numbered ?dr y"
      by (rule deferred_record_node_keys[OF parts0]) (use y in simp)
    then show "deferred_key ?dr y = deferred_key dd y \<and> deferred_numbered ?dr y" by simp
  qed
  have plA: "\<forall>p' h' x. p' \<in> set ?ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner ?dr))) p' = Some h' \<longrightarrow>
      \<not> shared_root_goal (shared_entry_goal h') \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h') \<longrightarrow>
      position_number (deferred_positions ?dr) (fst (fst x)) \<noteq> 0" using pl by blast
  have rtA: "\<forall>p' h'. p' \<in> set ?ps \<longrightarrow> RBT.lookup (shared_goals (search_state (deferred_inner ?dr))) p' = Some h' \<longrightarrow>
      shared_root_goal (shared_entry_goal h') \<longrightarrow> RBT.lookup (deferred_goal_records ?dr) p' = None" using rt by blast
  have otA: "\<forall>q'. q' \<notin> set ?ps \<longrightarrow> deferred_goal_formed ?dr q'" using ot by blast
  note G = deferred_record_goals[OF R(1) plA rtA otA]
  have nfr: "deferred_node_formed ?dr q'" for q'
  proof (cases "q' = q")
    case True
    then show ?thesis using R(2) by simp
  next
    case False
    then show ?thesis by (rule R(3)[OF nf0])
  qed
  show "deferred_formed \<kappa> P (deferred_place P dd q e c S)" unfolding eq deferred_formed_def using G nfr by blast
  show "search_placeable (search_project (deferred_inner (deferred_place P dd q e c S)))"
    unfolding eq using G inr CP(3) by simp
  show "deferred_inner (deferred_place P dd q e c S) = ?r'" unfolding eq using G inr by simp
  show "deferred_store (deferred_place P dd q e c S) = deferred_store dd" unfolding eq using G R(5) by simp
  show "deferred_project (deferred_place P dd q e c S) = Resolution_State
      (?G |\<union>| (resolution_pending (deferred_project dd) |-| {|?g|}))
      (finsert ?nd (resolution_nodes (deferred_project dd))) (resolution_witnesses (deferred_project dd))"
  proof -
    let ?\<sigma> = "deferred_substitution dd"
    have \<sigma>': "deferred_substitution (deferred_record_node q ?c ?ds) = ?\<sigma>"
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
    have sg: "deferred_substitution (deferred_record_goals ?ps ?dr) = deferred_substitution ?dr"
      using G by (simp add: fun_eq_iff deferred_substitution_def)
    have "deferred_project (deferred_place P dd q e c S) = resolution_state_substitute ?\<sigma> (search_project ?r')"
      unfolding eq using sg \<sigma>' G R(4) by (simp add: deferred_project_def)
    also have "\<dots> = Resolution_State (?G |\<union>| (resolution_pending ?st |-| {|?g|}))
        (finsert ?nd (fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes ?st))) (resolution_witnesses ?st)"
      unfolding pj resolution_state_substitute_def using Gfix Nfix pend by (simp add: fimage_funion)
    also have "\<dots> = Resolution_State (?G |\<union>| (resolution_pending (deferred_project dd) |-| {|?g|}))
        (finsert ?nd (resolution_nodes (deferred_project dd))) (resolution_witnesses (deferred_project dd))"
      using deferred_pending[OF dd] by (simp add: deferred_project_def resolution_state_substitute_def)
    finally show ?thesis .
  qed
qed

section \<open>The deferred steps\<close>

text \<open>
  Task 926, D1b's second part: the deferred search's successors are the shared search's over its access
  (@{const search_successors_with}), the bind the deferred bind and the node a call places recorded where the call
  branch hands its placed inner search to the bind (@{text deferred_at}); a goal closed by reuse or removed by a
  material alternative leaves the deferred parts as they are.
\<close>

subsection \<open>A unifier binds no variable to itself, and its images hold no variable of its domain\<close>

lemma finite_pattern_substitute_fixed:
  "finite_pattern_substitute \<sigma> p = p \<Longrightarrow> x |\<in>| finite_pattern_variables p \<Longrightarrow> \<sigma> x = Finite_Variable x"
  by (induction p) auto

lemma finite_unify_pairs_no_self:
  assumes "finite_unify_pairs E = Some s"
  shows "(x, Finite_Variable x) \<notin> set s"
  using assms
proof (induction E arbitrary: s rule: finite_unify_pairs.induct)
  case (2 a q E s)
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1)[OF True] "2.prems" show ?thesis by fastforce
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False "2.prems" show ?thesis by simp
    next
      case fresh: False
      from "2.prems" False fresh obtain s' where
        rec: "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = Some s'" and
        s: "s = (a, finite_pattern_substitute (finite_binding_substitution s') q) # s'"
        by auto
      have na: "a \<notin> finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E)"
        using finite_pairs_eliminate_variables[OF fresh, of E] by blast
      have img: "fset (finite_pattern_variables (snd y)) \<subseteq> finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E)"
        if "y \<in> set s'" for y
        using finite_unify_pairs_variables[OF rec] that by blast
      have ne: "finite_pattern_substitute (finite_binding_substitution s') q \<noteq> Finite_Variable a"
      proof (cases q)
        case (Finite_Variable z)
        then have za: "z \<noteq> a" using False by simp
        show ?thesis
        proof (cases "map_of s' z")
          case None
          then show ?thesis using Finite_Variable za by (simp add: finite_binding_substitution_def)
        next
          case (Some p)
          have "fset (finite_pattern_variables p) \<subseteq> finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E)"
            using img[OF map_of_SomeD[OF Some]] by simp
          then show ?thesis using Some Finite_Variable na by (auto simp: finite_binding_substitution_def)
        qed
      qed auto
      show ?thesis using "2.IH"(2)[OF False fresh rec] ne s by auto
    qed
  qed
qed (auto split: if_splits)

lemma finite_unify_pairs_domain_image:
  assumes u: "finite_unify_pairs E = Some u" and a: "a \<in> set (map fst u)"
    and b: "b |\<in>| finite_pattern_variables (finite_binding_substitution u a)"
  shows "b \<notin> set (map fst u)"
proof
  assume bd: "b \<in> set (map fst u)"
  have fixb: "finite_binding_substitution u b = Finite_Variable b"
    by (rule finite_pattern_substitute_fixed[OF finite_unify_pairs_idempotent[OF u, of a] b])
  obtain p where p: "map_of u b = Some p" using bd by (cases "map_of u b") (auto simp: map_of_eq_None_iff)
  have "(b, p) \<in> set u" by (rule map_of_SomeD[OF p])
  moreover have "p = Finite_Variable b" using fixb p by (simp add: finite_binding_substitution_def)
  ultimately show False using finite_unify_pairs_no_self[OF u, of b] by simp
qed

lemma shared_bindings_project_keys: "map fst (shared_bindings_project T s) = map fst s"
  by (induction s) (auto simp: shared_bindings_project_def)


lemma finite_instance_pairs_variables:
  "E |\<in>| finite_material_instance_pairs W M \<Longrightarrow> finite_pairs_variables E \<subseteq> fset (finite_material_variables M)"
  by (auto simp: finite_material_instance_pairs_def finite_pairs_variables_def finite_material_variables_def
      ffUnion.rep_eq fimage.rep_eq)

subsection \<open>The inner search changed where the deferred parts do not read it\<close>

text \<open>
  A deferred search whose inner search changes with its table only extended, its nodes kept and its goals holding no
  new variable stays formed, and presents the new inner search under the same substitution.
\<close>

lemma deferred_substitution_extends:
  assumes d: "deferred_formed \<kappa> P d" and tx: "table_extends (search_table (deferred_inner d)) (search_table r)"
  shows "deferred_substitution (d\<lparr>deferred_inner := r\<rparr>) = deferred_substitution d"
proof (rule ext)
  fix x
  let ?T = "search_table (deferred_inner d)" and ?S = "deferred_store d"
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF search_formedD(1)[OF deferred_formedD(1)[OF d]]] .
  have "shared_pattern_formed ?T (binding_substitution ?S x)"
    unfolding binding_substitution_def by (rule binding_resolve_formed[OF deferred_formedD(4)[OF d]]) simp
  then show "deferred_substitution (d\<lparr>deferred_inner := r\<rparr>) x = deferred_substitution d x"
    using shared_pattern_extends(2)[OF tf _ tx] by (simp add: deferred_substitution_def)
qed

lemma deferred_inner_formed:
  assumes d: "deferred_formed \<kappa> P d" and r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and tx: "table_extends (search_table (deferred_inner d)) (search_table r)"
    and nodes: "\<And>p. RBT.lookup (shared_nodes (search_state r)) p = RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
    and goals: "\<And>q h x. RBT.lookup (shared_goals (search_state r)) q = Some h \<Longrightarrow>
      x |\<in>| shared_goal_variables (shared_entry_goal h) \<Longrightarrow>
      \<exists>q' h'. RBT.lookup (shared_goals (search_state (deferred_inner d))) q' = Some h' \<and>
        x |\<in>| shared_goal_variables (shared_entry_goal h')"
    and entries: "\<And>q h. RBT.lookup (shared_goals (search_state r)) q = Some h \<Longrightarrow>
      \<exists>h'. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h' \<and> shared_entry_goal h' = shared_entry_goal h"
  shows "deferred_formed \<kappa> P (d\<lparr>deferred_inner := r\<rparr>)"
proof -
  let ?d = "d\<lparr>deferred_inner := r\<rparr>"
  have parts: "deferred_parts_formed \<kappa> P d" and nf: "\<And>q. deferred_node_formed d q"
    using d unfolding deferred_formed_def by blast+
  have tf: "table_formed (search_table (deferred_inner d))"
    using shared_entries_formed(4)[OF search_formedD(1)[OF deferred_formedD(1)[OF d]]] .
  have S: "binding_store_formed (search_table r) (deferred_store d)"
    using binding_store_formed_extended[OF deferred_formedD(4)[OF d] tf] tx by (simp add: table_extends_def)
  have g: "binding_map (deferred_store d) x = None \<and> (RBT.lookup (shared_nodes (search_state r)) (fst (fst x)) \<noteq> None \<or>
      (fst (fst x) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
    if gq: "RBT.lookup (shared_goals (search_state r)) q = Some h" and xv: "x |\<in>| shared_goal_variables (shared_entry_goal h)"
    for q h x
  proof -
    obtain h' where h': "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h'"
      "shared_entry_goal h' = shared_entry_goal h" using entries[OF gq] by blast
    have x': "x |\<in>| shared_goal_variables (shared_entry_goal h')" using xv h'(2) by simp
    show ?thesis using deferred_formedD(7,8)[OF d h'(1) x'] h'(2) nodes by metis
  qed
  have "deferred_parts_formed \<kappa> P ?d"
    unfolding deferred_parts_formed_def
  proof (intro conjI)
    show "search_formed \<kappa> P (deferred_inner ?d)" using r by simp
    show "search_classes_formed (deferred_inner ?d)" using K by simp
    show "positions_numbered (deferred_positions ?d)" using deferred_formedD(3)[OF d] by simp
    show "binding_store_formed (search_table (deferred_inner ?d)) (deferred_store ?d)" using S by simp
    show "\<forall>k v. RBT.lookup (snd (deferred_tree ?d)) k = Some v \<longrightarrow> (\<exists>y. deferred_numbered ?d y \<and> deferred_key ?d y = k)"
      using deferred_formedD(5)[OF d] by simp
    show "\<forall>y. binding_map (deferred_store ?d) y \<noteq> None \<longrightarrow>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d))) (fst (fst y)) \<noteq> None"
      using deferred_formedD(6)[OF d] nodes by simp
    show "\<forall>q h y. RBT.lookup (shared_goals (search_state (deferred_inner ?d))) q = Some h \<longrightarrow>
        y |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow> binding_map (deferred_store ?d) y = None \<and>
        (RBT.lookup (shared_nodes (search_state (deferred_inner ?d))) (fst (fst y)) \<noteq> None \<or>
          (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
    proof (intro allI impI)
      fix q h y assume gq: "RBT.lookup (shared_goals (search_state (deferred_inner ?d))) q = Some h"
        and yv: "y |\<in>| shared_goal_variables (shared_entry_goal h)"
      show "binding_map (deferred_store ?d) y = None \<and>
          (RBT.lookup (shared_nodes (search_state (deferred_inner ?d))) (fst (fst y)) \<noteq> None \<or>
            (fst (fst y) = [] \<and> (\<exists>rr e p. shared_entry_goal h = Shared_Call_Goal [] rr e p)))"
        using g[of q h y] gq yv by simp
    qed
    show "\<forall>n q K. RBT.lookup (deferred_records ?d) n = Some (q, K) \<longrightarrow> n \<noteq> 0 \<and>
        n = position_number (deferred_positions ?d) q \<and> RBT.lookup (shared_nodes (search_state (deferred_inner ?d))) q \<noteq> None"
      using parts nodes unfolding deferred_parts_formed_def by simp
  qed
  moreover have "deferred_node_formed ?d q" for q using nf[of q] nodes by (simp add: deferred_node_formed_def)
  moreover have "deferred_goal_formed ?d q" for q
  proof (rule deferred_goal_formed_same[OF deferred_formedD(12)[OF d]])
    show "\<And>h'. RBT.lookup (shared_goals (search_state (deferred_inner ?d))) q = Some h' \<Longrightarrow>
      \<exists>h. RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h \<and> shared_entry_goal h' = shared_entry_goal h"
      using entries by fastforce
    show "RBT.lookup (deferred_goal_records ?d) q = RBT.lookup (deferred_goal_records d) q" by simp
    show "\<And>y. deferred_numbered d y \<Longrightarrow> deferred_key ?d y = deferred_key d y \<and> deferred_numbered ?d y"
      by (simp add: deferred_key_def deferred_numbered_def)
  qed
  ultimately show ?thesis by (simp add: deferred_formed_def)
qed

lemma deferred_goals_fixed:
  assumes d: "deferred_formed \<kappa> P d" and z: "z |\<in>| resolution_pending (search_project (deferred_inner d))"
  shows "resolution_goal_substitute (deferred_substitution d) z = z"
proof -
  obtain q h where h: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
    and e: "shared_goal_project (search_table (deferred_inner d)) (shared_entry_goal h) = z"
    using z unfolding shared_state_project_member(1) by blast
  show ?thesis using deferred_goal_fixed[OF d h] e by blast
qed

lemma deferred_project_fields:
  assumes d: "deferred_formed \<kappa> P d"
  shows "deferred_project d = Resolution_State (resolution_pending (search_project (deferred_inner d)))
    (fimage (resolution_node_substitute (deferred_substitution d)) (resolution_nodes (search_project (deferred_inner d))))
    (resolution_witnesses (search_project (deferred_inner d)))"
  using deferred_pending[OF d] by (simp add: deferred_project_def resolution_state_substitute_def)

text \<open>A deferred search presenting a placeable state has a placeable inner search: its positions are the same.\<close>

lemma deferred_inner_placeable:
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)"
  shows "search_placeable (search_project (deferred_inner d))"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r" let ?st = "search_project ?r"
  let ?\<sigma> = "deferred_substitution d"
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF deferred_formedD(1)[OF d]] .
  note F = deferred_project_fields[OF d]
  have G: "resolution_pending (deferred_project d) = resolution_pending ?st" using F by simp
  have N: "resolution_nodes (deferred_project d) = fimage (resolution_node_substitute ?\<sigma>) (resolution_nodes ?st)" using F by simp
  have NP: "fimage resolution_node_position (resolution_nodes (deferred_project d)) =
      fimage resolution_node_position (resolution_nodes ?st)" unfolding N by (simp add: fset.map_comp comp_def)
  have dd: "resolution_positions_distinct (deferred_project d)" using pl by (simp add: search_placeable_def)
  have pos: "resolution_node_position nd = p" if "RBT.lookup (shared_nodes ?s) p = Some hn"
    "nd = shared_derivation_project ?T (shared_entry_node hn)" for p hn nd
    using shared_entries_formed(2)[OF s that(1)] that(2) by (simp add: node_entry_formed_def shared_derivation_project_def)
  have d': "resolution_positions_distinct ?st"
    unfolding resolution_positions_distinct_def
  proof (intro conjI allI impI)
    fix nd m assume n: "nd |\<in>| resolution_nodes ?st" and m: "m |\<in>| resolution_nodes ?st"
      and e: "resolution_node_position nd = resolution_node_position m"
    obtain p hn where hn: "RBT.lookup (shared_nodes ?s) p = Some hn" "nd = shared_derivation_project ?T (shared_entry_node hn)"
      using n unfolding shared_state_project_member(2) by metis
    obtain p' hm where hm: "RBT.lookup (shared_nodes ?s) p' = Some hm" "m = shared_derivation_project ?T (shared_entry_node hm)"
      using m unfolding shared_state_project_member(2) by metis
    have "p = p'" using pos[OF hn] pos[OF hm] e by simp
    then show "nd = m" using hn hm by simp
  next
    fix g h assume "g |\<in>| resolution_pending ?st" "h |\<in>| resolution_pending ?st"
      "resolution_goal_position g = resolution_goal_position h"
    then show "g = h" using dd G unfolding resolution_positions_distinct_def by metis
  next
    fix g nd assume g: "g |\<in>| resolution_pending ?st" and n: "nd |\<in>| resolution_nodes ?st" and c: "resolution_is_call g"
    have nd': "resolution_node_substitute ?\<sigma> nd |\<in>| resolution_nodes (deferred_project d)" using n N by simp
    have g': "g |\<in>| resolution_pending (deferred_project d)" using g G by simp
    have "resolution_goal_position g \<noteq> resolution_node_position (resolution_node_substitute ?\<sigma> nd)"
      using dd g' nd' c unfolding resolution_positions_distinct_def by blast
    then show "resolution_goal_position g \<noteq> resolution_node_position nd" by simp
  qed
  have pg: "fBall (resolution_pending ?st) (\<lambda>g. resolution_goal_position g \<noteq> [] \<longrightarrow>
      butlast (resolution_goal_position g) |\<in>| fimage resolution_node_position (resolution_nodes ?st))"
    using pl G NP by (simp add: search_placeable_def)
  have pn: "fBall (resolution_nodes ?st) (\<lambda>nd. resolution_node_position nd \<noteq> [] \<longrightarrow>
      butlast (resolution_node_position nd) |\<in>| fimage resolution_node_position (resolution_nodes ?st))"
  proof
    fix nd assume n: "nd |\<in>| resolution_nodes ?st"
    have nd': "resolution_node_substitute ?\<sigma> nd |\<in>| resolution_nodes (deferred_project d)" using n N by simp
    have "resolution_node_position (resolution_node_substitute ?\<sigma> nd) \<noteq> [] \<longrightarrow>
        butlast (resolution_node_position (resolution_node_substitute ?\<sigma> nd)) |\<in>|
          fimage resolution_node_position (resolution_nodes (deferred_project d))"
      using pl nd' unfolding search_placeable_def by blast
    then show "resolution_node_position nd \<noteq> [] \<longrightarrow>
        butlast (resolution_node_position nd) |\<in>| fimage resolution_node_position (resolution_nodes ?st)"
      using NP by simp
  qed
  show ?thesis using d' pg pn by (simp add: search_placeable_def)
qed

lemma deferred_reshare:
  assumes d: "deferred_formed \<kappa> P d"
  shows "deferred_formed \<kappa> P (d\<lparr>deferred_inner := search_reshare G (deferred_inner d)\<rparr>)"
    and "deferred_project (d\<lparr>deferred_inner := search_reshare G (deferred_inner d)\<rparr>) = deferred_project d"
    and "table_extends (search_table (deferred_inner d)) (search_table (search_reshare G (deferred_inner d)))"
proof -
  let ?r = "deferred_inner d"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" using deferred_formedD(1,2)[OF d] by blast+
  note h = search_reshare[where G = G, OF r]
  show "table_extends (search_table ?r) (search_table (search_reshare G ?r))" by (rule h(3))
  show "deferred_formed \<kappa> P (d\<lparr>deferred_inner := search_reshare G ?r\<rparr>)"
    by (rule deferred_inner_formed[OF d h(1) search_reshare_classes[OF r K] h(3)]) (auto simp: h(5,6))
  show "deferred_project (d\<lparr>deferred_inner := search_reshare G ?r\<rparr>) = deferred_project d"
    by (simp add: deferred_project_def deferred_substitution_extends[OF d h(3)] h(2))
qed

lemma deferred_remove_goal:
  assumes d: "deferred_formed \<kappa> P d" and at: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
  shows "deferred_formed \<kappa> P (d\<lparr>deferred_inner := search_remove_goal q (deferred_inner d)\<rparr>)"
    and "deferred_project (d\<lparr>deferred_inner := search_remove_goal q (deferred_inner d)\<rparr>) =
      finite_goal_closed (deferred_project d) (shared_goal_project (search_table (deferred_inner d)) (shared_entry_goal h))"
    and "search_table (search_remove_goal q (deferred_inner d)) = search_table (deferred_inner d)"
    and "\<And>p. RBT.lookup (shared_nodes (search_state (search_remove_goal q (deferred_inner d)))) p =
      RBT.lookup (shared_nodes (search_state (deferred_inner d))) p"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?r' = "search_remove_goal q ?r"
  let ?g = "shared_goal_project (search_table ?r) (shared_entry_goal h)"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" using deferred_formedD(1,2)[OF d] by blast+
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  note rm = search_remove_goal[OF r at]
  note sr = shared_remove_goal[OF s at]
  show tb: "search_table ?r' = search_table ?r" using rm(2) by (simp add: shared_remove_goal_def shared_replace_def)
  show nd: "RBT.lookup (shared_nodes (search_state ?r')) p = RBT.lookup (shared_nodes ?s) p" for p
    using rm(2) by (cases "RBT.lookup (shared_nodes ?s) q") (auto simp: shared_remove_goal_def shared_replace_def)
  have gl: "RBT.lookup (shared_goals (search_state ?r')) p = (if p = q then None else RBT.lookup (shared_goals ?s) p)" for p
    using rm(2) by (auto simp: shared_remove_goal_def shared_replace_def)
  have tx: "table_extends (search_table ?r) (search_table ?r')" using tb by (simp add: table_extends_def)
  show "deferred_formed \<kappa> P (d\<lparr>deferred_inner := ?r'\<rparr>)"
    by (rule deferred_inner_formed[OF d rm(1) search_remove_goal_classes[OF r K at] tx nd]) (auto simp: gl split: if_splits)
  have pj: "search_project ?r' = finite_goal_closed (search_project ?r) ?g"
    using sr(2-4) rm(2) by (cases "search_project ?r'") (simp add: finite_goal_closed_def)
  have fx: "fimage (resolution_goal_substitute (deferred_substitution d)) (resolution_pending (search_project ?r) |-| {|?g|}) =
      resolution_pending (search_project ?r) |-| {|?g|}"
    by (rule fimage_fixed) (rule deferred_goals_fixed[OF d], simp)
  show "deferred_project (d\<lparr>deferred_inner := ?r'\<rparr>) = finite_goal_closed (deferred_project d) ?g"
    using fx deferred_project_fields[OF d]
    by (simp add: deferred_project_def deferred_substitution_extends[OF d tx] pj finite_goal_closed_def
        resolution_state_substitute_def)
qed

subsection \<open>The successors\<close>

text \<open>
  The bind of a successor receives the inner search as the shared step leaves it: where that step placed a node at the
  goal's position, where none stood, the node is recorded; otherwise the deferred parts are kept.
\<close>

definition deferred_at :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_at q d r = (case RBT.lookup (shared_nodes (search_state r)) q of None \<Rightarrow> d\<lparr>deferred_inner := r\<rparr>
    | Some hn \<Rightarrow> if RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = None
      then deferred_record_goals (deferred_placed_positions q (shared_derivation_schema (shared_entry_node hn)))
        (deferred_record_node q (shared_derivation_call (shared_entry_node hn)) (d\<lparr>deferred_inner := r\<rparr>))
      else d\<lparr>deferred_inner := r\<rparr>)"

lemma deferred_at_place:
  assumes "RBT.lookup (shared_nodes (search_state (deferred_inner d))) q = None"
  shows "deferred_at q d (search_call_place P r q e c S) = deferred_place P (d\<lparr>deferred_inner := r\<rparr>) q e c S"
  using assms by (simp add: deferred_at_def deferred_place_def Let_def split: option.split)

lemma deferred_at_kept:
  assumes "RBT.lookup (shared_nodes (search_state r)) q = RBT.lookup (shared_nodes (search_state (deferred_inner d))) q"
  shows "deferred_at q d r = d\<lparr>deferred_inner := r\<rparr>"
  using assms by (simp add: deferred_at_def split: option.split)

definition deferred_successors :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) deferred_search fset" where
  "deferred_successors \<kappa> P d h = search_successors_with (deferred_access \<kappa> P d) (\<lambda>r. d\<lparr>deferred_inner := r\<rparr>)
    (\<lambda>q s r. deferred_bind P s (deferred_at q d r)) P (deferred_inner d) h"

lemma deferred_call_alternative:
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
    and g: "shared_entry_goal h = Shared_Call_Goal q rr e gp"
    and alt: "(i,c,S,s) |\<in>| shared_call_alternatives P
      (shared_sharing (search_state (search_reshare (search_call_grounds P q e) (deferred_inner d)))) q e gp"
  shows "(deferred_formed \<kappa> P (deferred_bind P s (deferred_at q d
        (search_call_place P (search_reshare (search_call_grounds P q e) (deferred_inner d)) q e c S))) \<and>
      search_placeable (deferred_project (deferred_bind P s (deferred_at q d
        (search_call_place P (search_reshare (search_call_grounds P q e) (deferred_inner d)) q e c S))))) \<and>
    deferred_project (deferred_bind P s (deferred_at q d
        (search_call_place P (search_reshare (search_call_grounds P q e) (deferred_inner d)) q e c S))) =
      finite_call_alternative_state (deferred_project d) q rr e (shared_pattern_project (search_table (deferred_inner d)) gp)
        (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q e) (deferred_inner d))) s)"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r"
  let ?G = "search_call_grounds P q e" let ?rs = "search_reshare ?G ?r" let ?Ts = "search_table ?rs"
  let ?x = "shared_sharing (search_state ?rs)" let ?ds = "d\<lparr>deferred_inner := ?rs\<rparr>"
  let ?p = "shared_pattern_project ?T gp" let ?rp = "search_call_place P ?rs q e c S"
  let ?d1 = "deferred_place P ?ds q e c S" let ?S = "deferred_store d"
  let ?E = "[(finite_rename_apart (q,False) i,?p), (finite_rename_apart (q,True) (finite_schema_conclusion S),?p)]"
  have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have pli: "search_placeable (search_project ?r)" by (rule deferred_inner_placeable[OF d pl])
  note h0 = search_reshare[where G = ?G, OF r]
  note R0 = deferred_reshare[where G = ?G, OF d]
  have gpf: "shared_pattern_formed ?T gp" using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gp0 = shared_pattern_extends[OF tf gpf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?rs)" using search_formedD(1)[OF h0(1)] .
  have tf0: "table_formed ?Ts" using shared_entries_formed(4)[OF s0] .
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have gpx: "shared_pattern_formed (share_state_table ?x) gp" "shared_pattern_project (share_state_table ?x) gp = ?p"
    using gp0 by simp_all
  have held: "\<forall>t. t |\<in>| ?G \<longrightarrow> table_holds (share_state_table ?x) t" using h0(4) by simp
  note A = shared_call_alternatives_project[OF x0 gpx(1) held]
  have cl: "((e,c),S) |\<in>| finite_system_clauses P" and sf0: "shared_bindings_formed ?Ts s" using A(2)[OF alt] by auto
  have mem: "(i,c,S,shared_bindings_project ?Ts s) |\<in>| finite_call_alternative_set P q e ?p"
    using fimageI[OF alt, of "\<lambda>(i,c,S,s). (i,c,S,shared_bindings_project (share_state_table ?x) s)"] A(1) gpx(2) by simp
  then have uu: "finite_unify_pairs ?E = Some (shared_bindings_project ?Ts s)"
    unfolding finite_call_alternative_set_member by auto
  have noq: "RBT.lookup (shared_nodes ?s) q = None"
  proof (rule ccontr)
    assume "RBT.lookup (shared_nodes ?s) q \<noteq> None"
    then obtain hn where hn: "RBT.lookup (shared_nodes ?s) q = Some hn" by blast
    have n: "shared_derivation_project ?T (shared_entry_node hn) |\<in>| resolution_nodes (search_project ?r)"
      unfolding shared_state_project_member(2) using hn by blast
    have gm: "Resolution_Call_Goal q rr e ?p |\<in>| resolution_pending (search_project ?r)"
      unfolding shared_state_project_member(1) using at g by force
    have "resolution_node_position (shared_derivation_project ?T (shared_entry_node hn)) = q"
      using shared_entries_formed(2)[OF s hn] by (simp add: node_entry_formed_def shared_derivation_project_def)
    then show False using pli n gm unfolding search_placeable_def resolution_positions_distinct_def by force
  qed
  have pl0: "search_placeable (search_project ?rs)" using h0(2) pli by simp
  have at0: "RBT.lookup (shared_goals (search_state ?rs)) q = Some h" using h0(5) at by simp
  have g0: "shared_goal_project ?Ts (shared_entry_goal h) = Resolution_Call_Goal q rr e ?p" using g gp0 by simp
  note CP = search_call_place_classed[OF h0(1) pl0 sock at0 g0 cl]
  have d0: "deferred_formed \<kappa> P ?ds" by (rule R0(1))
  have pl0': "search_placeable (search_project (deferred_inner ?ds))" using pl0 by simp
  have at0': "RBT.lookup (shared_goals (search_state (deferred_inner ?ds))) q = Some h" using at0 by simp
  have g0': "shared_goal_project (search_table (deferred_inner ?ds)) (shared_entry_goal h) = Resolution_Call_Goal q rr e ?p"
    using g0 by simp
  note P1 = deferred_place[OF d0 pl0' sock at0' g0' cl]
  have in1: "deferred_inner ?d1 = ?rp" using P1(4) by simp
  have st1: "deferred_store ?d1 = ?S" using P1(5) by simp
  have eqd: "deferred_at q d ?rp = ?d1" by (rule deferred_at_place[OF noq])
  have tx01: "table_extends ?Ts (search_table ?rp)" by (rule CP(4))
  note sb = shared_bindings_extends[OF tf0 tx01 sf0]
  have sf1: "shared_bindings_formed (search_table (deferred_inner ?d1)) s" using sb in1 by simp
  have u1: "shared_bindings_project (search_table (deferred_inner ?d1)) s = shared_bindings_project ?Ts s" using sb in1 by simp
  have nq: "RBT.lookup (shared_nodes (search_state ?rp)) q \<noteq> None"
  proof -
    have "finite_clause_node q e c S |\<in>| resolution_nodes (search_project ?rp)" using CP(2) by simp
    then obtain p' hn where hn: "RBT.lookup (shared_nodes (search_state ?rp)) p' = Some hn"
      and ee: "shared_derivation_project (search_table ?rp) (shared_entry_node hn) = finite_clause_node q e c S"
      unfolding shared_state_project_member(2) by blast
    have "shared_derivation_position (shared_entry_node hn) = p'"
      using shared_entries_formed(2)[OF search_formedD(1)[OF CP(1)] hn] by (simp add: node_entry_formed_def)
    then have "p' = q" using ee by (simp add: shared_derivation_project_def finite_clause_node_def)
    then show ?thesis using hn by simp
  qed
  have good: "binding_map (deferred_store ?d1) y = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst y)) \<noteq> None"
    if "y \<in> finite_pairs_variables ?E" for y
  proof -
    have "fst (fst y) = q \<or> y |\<in>| finite_pattern_variables ?p"
      using that by (auto simp: finite_pairs_variables_def finite_rename_apart_variables)
    then show ?thesis
    proof
      assume yq: "fst (fst y) = q"
      have "binding_map ?S y = None"
      proof (rule ccontr)
        assume "binding_map ?S y \<noteq> None"
        then have "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" by (rule deferred_formedD(6)[OF d])
        then show False using noq yq by simp
      qed
      then show ?thesis using st1 in1 nq yq by simp
    next
      assume yp: "y |\<in>| finite_pattern_variables ?p"
      have yg: "y |\<in>| shared_goal_variables (shared_entry_goal h)" using yp g shared_pattern_variables_project[OF gpf] by simp
      have ub: "binding_map ?S y = None" by (rule deferred_formedD(7)[OF d at yg])
      show ?thesis
      proof (cases "fst (fst y) = q")
        case True
        then show ?thesis using ub st1 in1 nq by simp
      next
        case ne: False
        have nn: "RBT.lookup (shared_nodes ?s) (fst (fst y)) \<noteq> None" using deferred_formedD(8)[OF d at yg] g ne by auto
        have "RBT.lookup (shared_nodes (search_state ?rp)) (fst (fst y)) = RBT.lookup (shared_nodes ?s) (fst (fst y))"
          using search_call_place_nodes[OF ne, of P ?rs e c S] h0(6) by simp
        then show ?thesis using ub nn st1 in1 by simp
      qed
    qed
  qed
  note vs = finite_unify_pairs_variables[OF uu]
  have keys: "set (map fst s) = set (map fst (shared_bindings_project ?Ts s))" by (simp only: shared_bindings_project_keys)
  have dom: "\<forall>a. a \<in> set (map fst s) \<longrightarrow> binding_map (deferred_store ?d1) a = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst a)) \<noteq> None"
  proof (intro allI impI)
    fix a assume "a \<in> set (map fst s)"
    then obtain z where z: "z \<in> set (shared_bindings_project ?Ts s)" "fst z = a" using keys by auto
    then have "a \<in> finite_pairs_variables ?E" using vs by blast
    then show "binding_map (deferred_store ?d1) a = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst a)) \<noteq> None" by (rule good)
  qed
  have img: "\<forall>a b. a \<in> set (map fst s) \<longrightarrow>
      b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?d1)) s) a) \<longrightarrow>
      b \<notin> set (map fst s) \<and> binding_map (deferred_store ?d1) b = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst b)) \<noteq> None"
  proof (intro allI impI)
    fix a b assume a: "a \<in> set (map fst s)"
      and b: "b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?d1)) s) a)"
    let ?u = "shared_bindings_project ?Ts s"
    have au: "a \<in> set (map fst ?u)" using a keys by simp
    have bu: "b |\<in>| finite_pattern_variables (finite_binding_substitution ?u a)" using b u1 by simp
    obtain pa where pa: "map_of ?u a = Some pa" using au by (cases "map_of ?u a") (auto simp: map_of_eq_None_iff)
    have "(a,pa) \<in> set ?u" by (rule map_of_SomeD[OF pa])
    then have "b \<in> finite_pairs_variables ?E" using vs bu pa by (fastforce simp: finite_binding_substitution_def)
    moreover have "b \<notin> set (map fst ?u)" by (rule finite_unify_pairs_domain_image[OF uu au bu])
    ultimately show "b \<notin> set (map fst s) \<and> binding_map (deferred_store ?d1) b = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst b)) \<noteq> None"
      using good keys by simp
  qed
  note B = deferred_bind[OF P1(1) sf1 dom img]
  have pj1: "deferred_project ?d1 = Resolution_State
      (finite_clause_goals q e c S |\<union>| (resolution_pending (deferred_project d) |-| {|Resolution_Call_Goal q rr e ?p|}))
      (finsert (finite_clause_node q e c S) (resolution_nodes (deferred_project d))) (resolution_witnesses (deferred_project d))"
    using P1(2) R0(2) by simp
  have pr: "deferred_project (deferred_bind P s ?d1) =
      finite_call_alternative_state (deferred_project d) q rr e ?p (i,c,S,shared_bindings_project ?Ts s)"
    using B(2) pj1 u1 by (simp add: finite_call_alternative_state_def)
  have pl1: "search_placeable (deferred_project ?d1)" unfolding deferred_project_def by (rule search_placeable_substitute[OF P1(3)])
  have pl2: "search_placeable (deferred_project (deferred_bind P s ?d1))" unfolding B(2) by (rule search_placeable_substitute[OF pl1])
  show ?thesis using B(1) pl2 pr eqd by simp
qed

lemma deferred_material_alternative:
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)"
    and at: "RBT.lookup (shared_goals (search_state (deferred_inner d))) q = Some h"
    and g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
    and alt: "(E,s) |\<in>| shared_solution_alternatives
      (shared_sharing (search_state (search_reshare (solution_grounds Ws (shared_material_project (search_table (deferred_inner d)) gM))
        (deferred_inner d))))
      gM (shared_material_project (search_table (deferred_inner d)) gM) Ws"
  shows "(deferred_formed \<kappa> P (deferred_bind P s (deferred_at q d (search_remove_goal q
        (search_reshare (solution_grounds Ws (shared_material_project (search_table (deferred_inner d)) gM)) (deferred_inner d))))) \<and>
      search_placeable (deferred_project (deferred_bind P s (deferred_at q d (search_remove_goal q
        (search_reshare (solution_grounds Ws (shared_material_project (search_table (deferred_inner d)) gM)) (deferred_inner d))))))) \<and>
    deferred_project (deferred_bind P s (deferred_at q d (search_remove_goal q
        (search_reshare (solution_grounds Ws (shared_material_project (search_table (deferred_inner d)) gM)) (deferred_inner d))))) =
      finite_material_alternative_state (deferred_project d) q rr (shared_material_project (search_table (deferred_inner d)) gM)
        (E, shared_bindings_project (search_table (search_reshare
          (solution_grounds Ws (shared_material_project (search_table (deferred_inner d)) gM)) (deferred_inner d))) s)"
proof -
  let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?T = "search_table ?r"
  let ?M = "shared_material_project ?T gM" let ?G = "solution_grounds Ws ?M"
  let ?rs = "search_reshare ?G ?r" let ?Ts = "search_table ?rs" let ?x = "shared_sharing (search_state ?rs)"
  let ?ds = "d\<lparr>deferred_inner := ?rs\<rparr>" let ?rm = "search_remove_goal q ?rs" let ?d1 = "d\<lparr>deferred_inner := ?rm\<rparr>"
  let ?S = "deferred_store d" let ?u = "shared_bindings_project ?Ts s"
  have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  note h0 = search_reshare[where G = ?G, OF r]
  note R0 = deferred_reshare[where G = ?G, OF d]
  have gf: "shared_material_formed ?T gM" using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gM0 = shared_material_extends[OF tf gf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?rs)" using search_formedD(1)[OF h0(1)] .
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have gMx: "shared_material_formed (share_state_table ?x) gM" "shared_material_project (share_state_table ?x) gM = ?M"
    using gM0 by simp_all
  have held: "\<forall>t. t |\<in>| solution_grounds Ws (shared_material_project (share_state_table ?x) gM) \<longrightarrow>
      table_holds (share_state_table ?x) t" using h0(4) gMx(2) by simp
  note A = shared_solution_alternatives_project[OF x0 gMx(1) held]
  have alt0: "(E,s) |\<in>| shared_solution_alternatives ?x gM (shared_material_project (share_state_table ?x) gM) Ws"
    using alt gMx(2) by simp
  have sf0: "shared_bindings_formed ?Ts s" using A(2)[OF alt0] by auto
  have m0: "(E, shared_bindings_project (share_state_table ?x) s) |\<in>|
      finite_solution_alternatives (shared_material_project (share_state_table ?x) gM) Ws"
    using fimageI[OF alt0, of "\<lambda>(E,s). (E, shared_bindings_project (share_state_table ?x) s)"] unfolding A(1) by simp
  have mem: "(E, ?u) |\<in>| finite_solution_alternatives ?M Ws" using m0 gMx(2) by simp
  then obtain W where W: "W |\<in>| Ws" "E |\<in>| finite_material_instance_pairs W ?M" and uu: "finite_unify_pairs E = Some ?u"
    by (auto simp: finite_solution_alternatives_member)
  have at0: "RBT.lookup (shared_goals (search_state (deferred_inner ?ds))) q = Some h" using h0(5) at by simp
  note D = deferred_remove_goal[OF R0(1) at0]
  have d1: "deferred_formed \<kappa> P ?d1" using D(1) by simp
  have nl: "RBT.lookup (shared_nodes (search_state ?rm)) p = RBT.lookup (shared_nodes ?s) p" for p
    using D(4)[of p] h0(6) by simp
  have eqd: "deferred_at q d ?rm = ?d1" by (rule deferred_at_kept) (rule nl)
  have g0: "shared_goal_project ?Ts (shared_entry_goal h) = Resolution_Material_Goal q rr ?M" using g gM0 by simp
  have pj1: "deferred_project ?d1 = finite_goal_closed (deferred_project d) (Resolution_Material_Goal q rr ?M)"
    using D(2) R0(2) g0 by simp
  have tb1: "search_table (deferred_inner ?d1) = ?Ts" using D(3) by simp
  have sf1: "shared_bindings_formed (search_table (deferred_inner ?d1)) s" using sf0 tb1 by simp
  have good: "binding_map (deferred_store ?d1) y = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst y)) \<noteq> None"
    if "y \<in> finite_pairs_variables E" for y
  proof -
    have "y |\<in>| finite_material_variables ?M" using finite_instance_pairs_variables[OF W(2)] that by blast
    then have yg: "y |\<in>| shared_goal_variables (shared_entry_goal h)"
      using goal_entry_variables[OF shared_entries_formed(1)[OF s at]] g by simp
    show ?thesis using deferred_formedD(7,8)[OF d at yg] nl g by auto
  qed
  note vs = finite_unify_pairs_variables[OF uu]
  have keys: "set (map fst s) = set (map fst ?u)" by (simp only: shared_bindings_project_keys)
  have dom: "\<forall>a. a \<in> set (map fst s) \<longrightarrow> binding_map (deferred_store ?d1) a = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst a)) \<noteq> None"
  proof (intro allI impI)
    fix a assume "a \<in> set (map fst s)"
    then obtain z where z: "z \<in> set ?u" "fst z = a" using keys by auto
    then have "a \<in> finite_pairs_variables E" using vs by blast
    then show "binding_map (deferred_store ?d1) a = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst a)) \<noteq> None" by (rule good)
  qed
  have img: "\<forall>a b. a \<in> set (map fst s) \<longrightarrow>
      b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?d1)) s) a) \<longrightarrow>
      b \<notin> set (map fst s) \<and> binding_map (deferred_store ?d1) b = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst b)) \<noteq> None"
  proof (intro allI impI)
    fix a b assume a: "a \<in> set (map fst s)"
      and b: "b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?d1)) s) a)"
    have au: "a \<in> set (map fst ?u)" using a keys by simp
    have bu: "b |\<in>| finite_pattern_variables (finite_binding_substitution ?u a)" using b tb1 by simp
    obtain pa where pa: "map_of ?u a = Some pa" using au by (cases "map_of ?u a") (auto simp: map_of_eq_None_iff)
    have "(a,pa) \<in> set ?u" by (rule map_of_SomeD[OF pa])
    then have "b \<in> finite_pairs_variables E" using vs bu pa by (fastforce simp: finite_binding_substitution_def)
    moreover have "b \<notin> set (map fst ?u)" by (rule finite_unify_pairs_domain_image[OF uu au bu])
    ultimately show "b \<notin> set (map fst s) \<and> binding_map (deferred_store ?d1) b = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?d1))) (fst (fst b)) \<noteq> None"
      using good keys by simp
  qed
  note B = deferred_bind[OF d1 sf1 dom img]
  have pr: "deferred_project (deferred_bind P s ?d1) = finite_material_alternative_state (deferred_project d) q rr ?M (E, ?u)"
    using B(2) pj1 tb1 by (simp add: finite_material_alternative_state_def finite_goal_closed_def)
  have pl1: "search_placeable (deferred_project ?d1)"
    unfolding pj1 using search_placeable_fewer[OF pl] by (simp add: finite_goal_closed_def)
  have pl2: "search_placeable (deferred_project (deferred_bind P s ?d1))" unfolding B(2) by (rule search_placeable_substitute[OF pl1])
  show ?thesis using B(1) pl2 pr eqd by simp
qed

theorem deferred_successors:
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (deferred_access \<kappa> P d)"
  shows "fimage deferred_project (deferred_successors \<kappa> P d h) =
      finite_goal_successors P (deferred_project d) (access_goal (deferred_access \<kappa> P d) h)"
    and "d' |\<in>| deferred_successors \<kappa> P d h \<Longrightarrow> deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d')"
proof -
  interpret access_formed \<kappa> P "deferred_access \<kappa> P d" "deferred_project d" by (rule deferred_access_formed[OF d])
  let ?r = "deferred_inner d" let ?T = "search_table ?r" let ?V = "deferred_access \<kappa> P d"
  let ?F = "\<lambda>d'. deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d')"
  have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
  have s: "shared_state_formed \<kappa> P (search_state ?r)" using search_formedD(1)[OF r] .
  have hg: "h |\<in>| access_goals (shared_access \<kappa> P ?r)" using h by (simp add: deferred_access_def)
  have at: "RBT.lookup (shared_goals (search_state ?r)) (shared_goal_position (shared_entry_goal h)) = Some h"
    using hg by (auto simp: shared_access_simps tree_values_member dest: shared_goal_lookup_position[OF s])
  have ag: "access_goal ?V h = shared_goal_project ?T (shared_entry_goal h)"
    by (simp add: deferred_access_def shared_access_simps)
  have reuse: "access_reusable ?V h \<longleftrightarrow> finite_reusable (deferred_project d) (Resolution_Call_Goal q rr e (shared_pattern_project ?T gp))"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr e gp" for q rr e gp
    using reusable[OF h] g ag by simp
  have closed: "?F (d\<lparr>deferred_inner := search_remove_goal q ?r\<rparr>) \<and>
      deferred_project (d\<lparr>deferred_inner := search_remove_goal q ?r\<rparr>) =
        finite_goal_closed (deferred_project d) (Resolution_Call_Goal q rr e (shared_pattern_project ?T gp))"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr e gp" and "access_reusable ?V h" for q rr e gp
  proof -
    have atq: "RBT.lookup (shared_goals (search_state ?r)) q = Some h" using at g by simp
    note D = deferred_remove_goal[OF d atq]
    have pl': "search_placeable (deferred_project (d\<lparr>deferred_inner := search_remove_goal q ?r\<rparr>))"
      unfolding D(2) using search_placeable_fewer[OF pl] by (simp add: finite_goal_closed_def)
    show ?thesis using D(1,2) pl' g by simp
  qed
  have call: "?F (deferred_bind P s (deferred_at q d (search_call_place P (search_reshare (search_call_grounds P q e) ?r) q e c S))) \<and>
      deferred_project (deferred_bind P s (deferred_at q d (search_call_place P (search_reshare (search_call_grounds P q e) ?r) q e c S))) =
        finite_call_alternative_state (deferred_project d) q rr e (shared_pattern_project ?T gp)
          (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q e) ?r)) s)"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr e gp"
      and alt: "(i,c,S,s) |\<in>| shared_call_alternatives P
        (shared_sharing (search_state (search_reshare (search_call_grounds P q e) ?r))) q e gp"
      and "((e,c),S) |\<in>| finite_system_clauses P"
      and "shared_bindings_formed (search_table (search_reshare (search_call_grounds P q e) ?r)) s"
    for q rr e gp i c S s
  proof -
    have atq: "RBT.lookup (shared_goals (search_state ?r)) q = Some h" using at g by simp
    show ?thesis by (rule deferred_call_alternative[OF d pl sock atq g alt])
  qed
  have mat: "?F (deferred_bind P s (deferred_at q d (search_remove_goal q
        (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) ?r)))) \<and>
      deferred_project (deferred_bind P s (deferred_at q d (search_remove_goal q
        (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) ?r)))) =
        finite_material_alternative_state (deferred_project d) q rr (shared_material_project ?T gM)
          (E, shared_bindings_project (search_table (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) ?r)) s)"
    if g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
      and alt: "(E,s) |\<in>| shared_solution_alternatives
        (shared_sharing (search_state (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) ?r)))
        gM (shared_material_project ?T gM) Ws"
      and "shared_bindings_formed (search_table (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) ?r)) s"
    for q rr gM Ws E s
  proof -
    have atq: "RBT.lookup (shared_goals (search_state ?r)) q = Some h" using at g by simp
    show ?thesis by (rule deferred_material_alternative[OF d pl atq g alt])
  qed
  have W1: "fimage deferred_project (search_successors_with ?V (\<lambda>r. d\<lparr>deferred_inner := r\<rparr>)
      (\<lambda>q s r. deferred_bind P s (deferred_at q d r)) P ?r h) =
      finite_goal_successors P (deferred_project d) (shared_goal_project ?T (shared_entry_goal h))"
    by (rule search_successors_with(1)[where F = ?F, OF r at])
      ((rule reuse; assumption), (rule closed; assumption), (rule call; assumption), (rule mat; assumption))
  show "fimage deferred_project (deferred_successors \<kappa> P d h) =
      finite_goal_successors P (deferred_project d) (access_goal ?V h)"
    using W1 ag by (simp add: deferred_successors_def)
  show "deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d')" if d': "d' |\<in>| deferred_successors \<kappa> P d h"
    by (rule search_successors_with(2)[where F = ?F and proj = deferred_project and st = "deferred_project d",
      OF r at _ _ _ _ d'[unfolded deferred_successors_def]])
      ((rule reuse; assumption), (rule closed; assumption), (rule call; assumption), (rule mat; assumption))
qed

subsection \<open>The selection over the kept classes\<close>

text \<open>
  The deferred search's access differs from the shared search's only in what it reads of the nodes, so the kept
  selection over it is its selection (@{thm [source] kept_select_over}).
\<close>

definition deferred_select :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "deferred_select \<kappa> P rp d = kept_select_by (ffilter rp) (deferred_inner d) (deferred_access \<kappa> P d)"

theorem deferred_select:
  assumes d: "deferred_formed \<kappa> P d"
  shows "deferred_select \<kappa> P rp d = access_select rp (deferred_access \<kappa> P d)"
  unfolding deferred_select_def deferred_access_def by (rule kept_select_over[OF deferred_formedD(1,2)[OF d]])

subsection \<open>The construction step\<close>

text \<open>
  The construction reads each value once at the resolved node (@{const deferred_node}) and binds the constructed
  registered variables to it through the deferred bind: no kept value is refreshed (the refresh is the identity), and
  the node the construction reads stays as placed. The bound variables are listed by the structure of the goals that
  hold them, a registered variable being ready only where a goal holds it; no order of the names is read.
\<close>

lemma plain_grounds_member: "t |\<in>| pattern_grounds (\<tau> a) \<Longrightarrow> a |\<in>| D \<Longrightarrow> t |\<in>| plain_grounds \<tau> D"
  by (auto simp: plain_grounds_def ffUnion.rep_eq fimage.rep_eq)

definition deferred_constructed_variables :: "('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> 's list \<Rightarrow> 'a fset \<Rightarrow>
    ('s,'a) resolution_variable list" where
  "deferred_constructed_variables d q C = remdups (filter (\<lambda>x. fst x = (q,True) \<and> snd x |\<in>| C)
    (concat (map (\<lambda>p. case RBT.lookup (shared_goals (search_state (deferred_inner d))) p of None \<Rightarrow> []
      | Some h \<Rightarrow> shared_goal_variable_list (shared_entry_goal h))
      (sorted_list_of_fset (tree_bucket (shared_holders (search_state (deferred_inner d))) q)))))"

definition deferred_construct :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_construct \<kappa> P d hn = (let nd = deferred_node d hn; q = shared_derivation_position (shared_entry_node hn);
      C = access_constructed (deferred_access \<kappa> P d) hn;
      \<tau> = (\<lambda>z. finite_exact_term_pattern (the (finite_registered_value \<kappa> P nd (snd z))));
      W = ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of Some v \<Rightarrow> {|(((q,True),a),v)|} | None \<Rightarrow> {||}) C);
      r = deferred_inner d;
      r1 = search_reshare (plain_grounds \<tau> (fimage (\<lambda>a. ((q,True),a)) C))
        (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := shared_witnesses (search_state r) |\<union>| W\<rparr>\<rparr>) in
    deferred_bind P (map (\<lambda>z. (z, keyed_pattern_at (shared_sharing (search_state r1)) (\<tau> z)))
      (deferred_constructed_variables d q C)) (d\<lparr>deferred_inner := r1\<rparr>))"

theorem deferred_construct:
  fixes d :: "('a,'s::linorder,'d,'c) deferred_search"
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)"
    and n: "hn |\<in>| access_nodes_at (deferred_access \<kappa> P d) q0"
  shows "deferred_formed \<kappa> P (deferred_construct \<kappa> P d hn) \<and> search_placeable (deferred_project (deferred_construct \<kappa> P d hn))"
    and "deferred_project (deferred_construct \<kappa> P d hn) =
      finite_construction_step \<kappa> P (deferred_project d) (access_node (deferred_access \<kappa> P d) hn)"
proof -
  interpret access_formed \<kappa> P "deferred_access \<kappa> P d" "deferred_project d" by (rule deferred_access_formed[OF d])
  let ?V = "deferred_access \<kappa> P d" let ?r = "deferred_inner d" let ?s = "search_state ?r" let ?S = "deferred_store d"
  let ?nd = "deferred_node d hn" let ?q = "shared_derivation_position (shared_entry_node hn)"
  let ?C = "access_constructed ?V hn" let ?G = "resolution_pending (deferred_project d)"
  let ?\<tau> = "\<lambda>z::('s,'a) resolution_variable. (finite_exact_term_pattern (the (finite_registered_value \<kappa> P ?nd (snd z)))
    :: ('s,'a) resolution_variable finite_term_pattern)"
  let ?X = "fimage (\<lambda>a. ((?q,True),a)) ?C"
  define W where "W = ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P ?nd a of
    Some v \<Rightarrow> {|(((?q,True),a),v)|} | None \<Rightarrow> {||}) ?C)"
  define rW where "rW = ?r\<lparr>search_state := ?s\<lparr>shared_witnesses := shared_witnesses ?s |\<union>| W\<rparr>\<rparr>"
  define r1 where "r1 = search_reshare (plain_grounds ?\<tau> ?X) rW"
  define xs where "xs = deferred_constructed_variables d ?q ?C"
  define s :: "(('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list"
    where "s = map (\<lambda>z. (z, keyed_pattern_at (shared_sharing (search_state r1)) (?\<tau> z))) xs"
  let ?dW = "d\<lparr>deferred_inner := rW\<rparr>" let ?db = "d\<lparr>deferred_inner := r1\<rparr>"
  have eq: "deferred_construct \<kappa> P d hn = deferred_bind P s ?db"
    by (simp add: deferred_construct_def Let_def W_def rW_def r1_def xs_def s_def)
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" using deferred_formedD(1,2)[OF d] by blast+
  have st: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have hn: "RBT.lookup (shared_nodes ?s) q0 = Some hn"
    using n by (cases "RBT.lookup (shared_nodes ?s) q0") (simp_all add: deferred_access_def shared_access_simps)
  have qq: "?q = q0" using shared_entries_formed(2)[OF st hn] by (simp add: node_entry_formed_def)
  have ndp: "resolution_node_position ?nd = ?q" by (simp add: deferred_node_def shared_derivation_project_def)
  have an: "access_node ?V hn = ?nd" by (simp add: deferred_access_def)
  have C: "?C = finite_constructed \<kappa> P ?G ?nd" using constructed[OF n] an by simp
  have rW: "search_formed \<kappa> P rW" unfolding rW_def using r by (simp add: search_witnesses_update)
  have KW: "search_classes_formed rW" unfolding rW_def by (rule search_witnesses_classes[OF r K])
  have txW: "table_extends (search_table ?r) (search_table rW)" by (simp add: rW_def table_extends_def)
  have dW: "deferred_formed \<kappa> P ?dW"
    by (rule deferred_inner_formed[OF d rW KW txW]) (auto simp: rW_def)
  have pW: "deferred_project ?dW = Resolution_State ?G (resolution_nodes (deferred_project d))
      (resolution_witnesses (deferred_project d) |\<union>| W)"
  proof -
    have "search_project rW = Resolution_State (resolution_pending (search_project ?r)) (resolution_nodes (search_project ?r))
        (shared_witnesses ?s |\<union>| W)"
      unfolding rW_def by (rule search_witnesses_update(2))
    then show ?thesis
      by (simp add: deferred_project_def deferred_substitution_extends[OF d txW] resolution_state_substitute_def
          shared_state_project_fields)
  qed
  note R1 = deferred_reshare[where G = "plain_grounds ?\<tau> ?X", OF dW]
  have d1: "deferred_formed \<kappa> P ?db" using R1(1) by (simp add: r1_def)
  have p1: "deferred_project ?db = deferred_project ?dW" using R1(2) by (simp add: r1_def)
  have s1: "shared_state_formed \<kappa> P (search_state r1)" unfolding r1_def using search_formedD(1)[OF search_reshare(1)[OF rW]] .
  have x1: "share_state_formed (shared_sharing (search_state r1))" using shared_entries_formed(3)[OF s1] .
  have rep: "keyed_state_represents (shared_sharing (search_state r1)) (search_table r1)"
    and tf1: "table_formed (search_table r1)" using share_state_formed_table[OF x1] by simp_all
  have held: "table_holds (search_table r1) t" if "t |\<in>| pattern_grounds (?\<tau> z)" "z |\<in>| ?X" for z t
    unfolding r1_def by (rule search_reshare(4)[OF rW], rule plain_grounds_member[where \<tau> = ?\<tau>, OF that])
  have ex: "shared_pattern_formed (search_table r1) (keyed_pattern_at (shared_sharing (search_state r1)) (?\<tau> z)) \<and>
      shared_pattern_project (search_table r1) (keyed_pattern_at (shared_sharing (search_state r1)) (?\<tau> z)) = ?\<tau> z"
    if "z |\<in>| ?X" for z
    using keyed_pattern_at_exact[OF rep tf1] held[OF _ that] by blast
  have xsX: "set xs = fset ?X"
  proof (rule set_eqI)
    fix x
    show "x \<in> set xs \<longleftrightarrow> x \<in> fset ?X"
    proof
      assume "x \<in> set xs"
      then have "fst x = (?q,True) \<and> snd x |\<in>| ?C" by (auto simp: xs_def deferred_constructed_variables_def)
      then show "x \<in> fset ?X" by (cases x) (auto simp: fimage.rep_eq image_iff)
    next
      assume "x \<in> fset ?X"
      then obtain a where a: "a |\<in>| ?C" and xa: "x = ((?q,True),a)" by (auto simp: fimage.rep_eq)
      have "access_ready ?V (access_node_position ?V hn) a" using a by (simp add: access_constructed_def)
      then have "access_goal_holders ?V x \<noteq> {||}" using xa
        by (simp add: access_ready_def Let_def deferred_access_def shared_access_simps)
      then obtain h where hh: "h |\<in>| access_goal_holders ?V x" by blast
      then obtain p where p: "p |\<in>| tree_bucket (shared_holders ?s) ?q" "RBT.lookup (shared_goals ?s) p = Some h"
        and xh: "x |\<in>| shared_goal_variables (shared_entry_goal h)"
        using xa by (auto simp: access_goal_holders_def deferred_access_def shared_access_simps ffUnion.rep_eq fimage.rep_eq
          option_fset_def split: option.splits)
      have gf: "shared_goal_formed (search_table ?r) (shared_entry_goal h)"
        using shared_entries_formed(1)[OF st p(2)] by (simp add: goal_entry_formed_def)
      have "x \<in> set (shared_goal_variable_list (shared_entry_goal h))" using shared_goal_variable_list[OF gf] xh by simp
      then show "x \<in> set xs" using p xa a by (force simp: xs_def deferred_constructed_variables_def)
    qed
  qed
  have keys: "set (map fst s) = set xs" by (simp add: s_def comp_def)
  have sf: "shared_bindings_formed (search_table (deferred_inner ?db)) s"
    using ex xsX by (auto simp: s_def shared_bindings_formed_def)
  have ps: "shared_bindings_project (search_table r1) s = map (\<lambda>z. (z, ?\<tau> z)) xs"
    unfolding s_def shared_bindings_project_def by (simp add: map_eq_conv ex xsX)
  have ub0: "binding_map ?S ((?q,True),a) = None \<and> RBT.lookup (shared_nodes (search_state r1)) ?q \<noteq> None"
    if a: "a |\<in>| ?C" for a
  proof -
    have "a |\<in>| deferred_free \<kappa> d hn" using a by (simp add: access_constructed_def deferred_access_def)
    then have "fBex (shared_derivation_bindings (shared_entry_node hn))
        (\<lambda>z. fst z = a \<and> binding_deref ?S (snd z) = Shared_Variable ((?q,True),a))"
      by (simp add: deferred_free_def)
    then obtain z where z: "z |\<in>| shared_derivation_bindings (shared_entry_node hn)" "fst z = a"
      and dz: "binding_deref ?S (snd z) = Shared_Variable ((?q,True),a)" by blast
    have rz: "binding_resolve ?S (snd z) = Shared_Variable ((?q,True),a)" by (rule binding_resolve_variable[THEN iffD2, OF dz])
    have zf: "shared_pattern_formed (search_table ?r) (snd z)"
      using shared_entries_formed(2)[OF st hn] z(1) by (auto simp: node_entry_formed_def shared_derivation_formed_def)
    have "binding_map ?S ((?q,True),a) = None"
      by (rule binding_resolve_variables[OF deferred_formedD(4)[OF d] zf]) (simp add: rz)
    moreover have "RBT.lookup (shared_nodes (search_state r1)) ?q \<noteq> None"
      using hn qq search_reshare(6)[OF rW, of "plain_grounds ?\<tau> ?X"] by (simp add: r1_def rW_def)
    ultimately show ?thesis by blast
  qed
  have ub: "binding_map ?S x = None \<and> RBT.lookup (shared_nodes (search_state r1)) (fst (fst x)) \<noteq> None"
    if xin: "x \<in> set xs" for x
  proof -
    obtain a where a: "a |\<in>| ?C" and xa: "x = ((?q,True),a)" using xin xsX by (auto simp: fimage.rep_eq)
    show ?thesis using ub0[OF a] unfolding xa by simp
  qed
  have dom: "\<forall>a. a \<in> set (map fst s) \<longrightarrow> binding_map (deferred_store ?db) a = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst a)) \<noteq> None"
    using ub keys by simp
  have img: "\<forall>a b. a \<in> set (map fst s) \<longrightarrow>
      b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a) \<longrightarrow>
      b \<notin> set (map fst s) \<and> binding_map (deferred_store ?db) b = None \<and>
      RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst b)) \<noteq> None"
  proof (intro allI impI)
    fix a b assume a: "a \<in> set (map fst s)"
      and b: "b |\<in>| finite_pattern_variables (finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a)"
    have "a \<in> set xs" using a keys by simp
    then have "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) a = ?\<tau> a"
      by (simp add: ps finite_binding_substitution_def map_of_map_restrict)
    then show "b \<notin> set (map fst s) \<and> binding_map (deferred_store ?db) b = None \<and>
        RBT.lookup (shared_nodes (search_state (deferred_inner ?db))) (fst (fst b)) \<noteq> None" using b by simp
  qed
  note B = deferred_bind[OF d1 sf dom img]
  have fb: "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) =
      finite_construction_substitution \<kappa> P ?G ?nd"
  proof (rule ext)
    fix z :: "('s,'a) resolution_variable"
    obtain q' b a where zz: "z = ((q',b),a)" by (cases z) auto
    show "finite_binding_substitution (shared_bindings_project (search_table (deferred_inner ?db)) s) z =
        finite_construction_substitution \<kappa> P ?G ?nd z"
    proof (cases "b \<and> q' = ?q \<and> a |\<in>| ?C")
      case True
      then obtain v where v: "finite_registered_value \<kappa> P ?nd a = Some v" using C by (auto simp: finite_constructed_def)
      have "z \<in> set xs" using True zz xsX by (auto simp: fimage.rep_eq)
      then show ?thesis using True zz v C ndp
        by (simp add: ps finite_binding_substitution_def map_of_map_restrict finite_construction_substitution_def)
    next
      case False
      have "z \<notin> set xs" using False zz xsX by (auto simp: fimage.rep_eq)
      then show ?thesis using False zz C ndp
        by (auto simp: ps finite_binding_substitution_def map_of_map_restrict finite_construction_substitution_def)
    qed
  qed
  have WW: "W = ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P ?nd a of
      Some v \<Rightarrow> {|(((resolution_node_position ?nd,True),a),v)|} | None \<Rightarrow> {||}) (finite_constructed \<kappa> P ?G ?nd))"
    unfolding W_def C ndp by (rule refl)
  have pr: "deferred_project (deferred_construct \<kappa> P d hn) = finite_construction_step \<kappa> P (deferred_project d) ?nd"
    unfolding eq B(2) fb p1 pW WW finite_construction_step_def Let_def by (rule refl)
  show "deferred_project (deferred_construct \<kappa> P d hn) =
      finite_construction_step \<kappa> P (deferred_project d) (access_node ?V hn)" using pr an by simp
  have "search_placeable (deferred_project (deferred_construct \<kappa> P d hn))"
    unfolding pr finite_construction_step_def Let_def
    by (rule search_placeable_substitute, rule search_placeable_witnesses[OF pl])
  then show "deferred_formed \<kappa> P (deferred_construct \<kappa> P d hn) \<and>
      search_placeable (deferred_project (deferred_construct \<kappa> P d hn))" using B(1) eq by simp
qed

section \<open>The deferred search\<close>

text \<open>
  The deferred search is the representation's search over the deferred state's access and steps
  (@{const represented_search}); its refresh is the identity, no kept value standing in it. It is R3's search wherever
  the shared search is and every variable stands at a node's position or at the root of a call goal there
  (@{const search_variables_rooted}); standing at a node's position alone is an instance.
\<close>

definition deferred_representation :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) deferred_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) resolution_representation" where
  "deferred_representation \<kappa> P = \<lparr>rep_access = deferred_access \<kappa> P,
    rep_empty = (\<lambda>d. RBT.is_empty (shared_goals (search_state (deferred_inner d)))),
    rep_project = deferred_project, rep_refresh = id, rep_construct = deferred_construct \<kappa> P,
    rep_successors = deferred_successors \<kappa> P\<rparr>"

theorem deferred_search_rooted:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_rooted st"
  shows "represented_search (deferred_representation \<kappa> P) (\<lambda>r h. False) \<kappa> P n (deferred_of P st) =
      finite_resolution_search \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "deferred_representation \<kappa> P"
  let ?F = "\<lambda>d. deferred_formed \<kappa> P d \<and> search_placeable (deferred_project d)"
  have "represented_search ?R (\<lambda>r h. False) \<kappa> P n (deferred_of P st) =
      finite_resolution_search_by (finite_resolution_select_at (\<lambda>st g. False) \<kappa> P) \<kappa> P n (rep_project ?R (deferred_of P st))"
  proof (rule represented_search[where F = ?F])
    show "?F (deferred_of P st)" using deferred_of_rooted(1,2)[OF d v] pl by simp
  next
    fix s assume "?F s"
    then show "access_formed \<kappa> P (rep_access ?R s) (rep_project ?R s)"
      using deferred_access_formed[OF conjunct1[OF \<open>?F s\<close>]] by (simp add: deferred_representation_def)
  next
    fix s assume f: "?F s"
    have "resolution_pending (deferred_project s) = fimage (\<lambda>h. shared_goal_project (search_table (deferred_inner s))
        (shared_entry_goal h)) (tree_values (shared_goals (search_state (deferred_inner s))))"
      using deferred_pending[OF conjunct1[OF f]] by (simp add: shared_state_project_fields)
    then show "rep_empty ?R s \<longleftrightarrow> resolution_pending (rep_project ?R s) = {||}"
      by (simp add: deferred_representation_def rbt_empty_values)
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s) \<and> rep_project ?R (rep_refresh ?R s) = rep_project ?R s"
      by (simp add: deferred_representation_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (deferred_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "deferred_access \<kappa> P s"] m by (auto simp: deferred_representation_def)
    note c = deferred_construct[OF conjunct1[OF f] conjunct2[OF f] n]
    show "?F (rep_construct ?R s m) \<and>
        rep_project ?R (rep_construct ?R s m) = finite_construction_step \<kappa> P (rep_project ?R s) (access_node (rep_access ?R s) m)"
      using c by (simp add: deferred_representation_def)
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    have h': "h |\<in>| access_goals (deferred_access \<kappa> P s)" using h by (simp add: deferred_representation_def)
    note sc = deferred_successors[OF conjunct1[OF f] conjunct2[OF f] sock h']
    show "fimage (rep_project ?R) (rep_successors ?R s h) =
        finite_goal_successors P (rep_project ?R s) (access_goal (rep_access ?R s) h) \<and>
        (\<forall>s'. s' |\<in>| rep_successors ?R s h \<longrightarrow> ?F s')"
      using sc by (simp add: deferred_representation_def)
  next
    fix s h show "False \<longleftrightarrow> False" by simp
  qed
  then show ?thesis using deferred_of_rooted(2)[OF d v]
    by (simp add: finite_resolution_search_def finite_resolution_search_in_def deferred_representation_def)
qed

theorem deferred_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_placed st"
  shows "represented_search (deferred_representation \<kappa> P) (\<lambda>r h. False) \<kappa> P n (deferred_of P st) =
      finite_resolution_search \<kappa> P n st"
  by (rule deferred_search_rooted[OF sock pl search_variables_placed_rooted[OF v]])

text \<open>The search over the kept classes: the deferred search's selection is the kept selection over its access.\<close>

theorem deferred_kept_search_rooted:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_rooted st"
  shows "selected_search (deferred_representation \<kappa> P) (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st) =
      finite_resolution_search \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "deferred_representation \<kappa> P"
  let ?F = "\<lambda>d. deferred_formed \<kappa> P d \<and> search_placeable (deferred_project d)"
  have "selected_search ?R (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st) =
      represented_search ?R (\<lambda>r h. False) \<kappa> P n (deferred_of P st)"
  proof (rule selected_search[where F = ?F])
    show "?F (deferred_of P st)" using deferred_of_rooted(1,2)[OF d v] pl by simp
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s)" by (simp add: deferred_representation_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (deferred_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "deferred_access \<kappa> P s"] m by (auto simp: deferred_representation_def)
    show "?F (rep_construct ?R s m)"
      using deferred_construct(1)[OF conjunct1[OF f] conjunct2[OF f] n] by (simp add: deferred_representation_def)
  next
    fix s h s' assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)" and s': "s' |\<in>| rep_successors ?R s h"
    have h': "h |\<in>| access_goals (deferred_access \<kappa> P s)" and s'': "s' |\<in>| deferred_successors \<kappa> P s h"
      using h s' by (simp_all add: deferred_representation_def)
    show "?F s'" by (rule deferred_successors(2)[OF conjunct1[OF f] conjunct2[OF f] sock h' s''])
  next
    fix s assume f: "?F s"
    show "deferred_select \<kappa> P (\<lambda>h. False) s = access_select ((\<lambda>r h. False) s) (rep_access ?R s)"
      using deferred_select[OF conjunct1[OF f]] by (simp add: deferred_representation_def)
  qed
  also have "\<dots> = finite_resolution_search \<kappa> P n st" by (rule deferred_search_rooted[OF sock pl v])
  finally show ?thesis .
qed

theorem deferred_kept_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_placed st"
  shows "selected_search (deferred_representation \<kappa> P) (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st) =
      finite_resolution_search \<kappa> P n st"
  by (rule deferred_kept_search_rooted[OF sock pl search_variables_placed_rooted[OF v]])

text \<open>
  R3's search is computed over the deferred state wherever every variable of the state stands at a node's position or
  at the root of a call goal there — a query's root among them — tested once at the entry, and over the shared state or
  F2b1's indexed state elsewhere; the three coincide with R3's, so the equation holds at every input, at the search's
  general type.
\<close>

declare finite_resolution_search_shared_code [code del]

lemma finite_resolution_search_deferred_code [code]:
  "finite_resolution_search \<kappa> P n st = (if clause_sockets_distinct P \<and> search_placeable st
    then (if search_variables_rooted st
      then selected_search (deferred_representation \<kappa> P) (deferred_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of P st)
      else selected_search (shared_representation \<kappa> P) (search_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of P st))
    else indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st))"
  using finite_resolution_search_shared_code[of \<kappa> P n st] deferred_kept_search_rooted[of P st \<kappa> n] by auto

export_code finite_resolution_search checking SML

section \<open>The deferred search at a table of certified calls\<close>

text \<open>
  GT3 (task 876) through D1b's deferred search: the table's index, its closing test and its class stand in the inner
  shared search the deferred search reads (@{const search_closing_formed}); a goal the index closes is removed from the
  inner search, its one successor, and the store and the records stand, a closing binding nothing. Every deferred step
  keeps the inner search's calls and index (@{const search_frame}).
\<close>

subsection \<open>The deferred steps keep the table's calls and index\<close>

lemma deferred_frame_records [simp]:
  "search_frame (deferred_inner (deferred_renumber q p d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_record_at n q ks d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_record_node q p d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (d\<lparr>deferred_inner := r\<rparr>)) = search_frame r"
  by (simp_all add: deferred_renumber_def deferred_record_at_def deferred_record_node_def Let_def)

lemma deferred_frame_memoize_at [simp]:
  "search_frame (deferred_inner (deferred_memoize_at x d)) = search_frame (deferred_inner d)"
  by (simp add: deferred_memoize_at_def split: option.splits prod.splits)

lemma deferred_frame_memoize:
  "search_frame (deferred_inner (deferred_memoize_from n r x d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_memoize_list n r ys d)) = search_frame (deferred_inner d)"
  by (induction n r x d and n r ys d rule: deferred_memoize_from_deferred_memoize_list.induct)
    (auto split: option.splits prod.splits)

lemma deferred_frame_ground [simp]:
  "search_frame (deferred_inner (deferred_memoize_node q d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_ground_node q d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_ground q d)) = search_frame (deferred_inner d)"
  "search_frame (deferred_inner (deferred_update \<sigma> D n d)) = search_frame (deferred_inner d)"
  by (simp_all add: deferred_memoize_node_def deferred_ground_node_def deferred_ground_def deferred_update_def
    deferred_update_at_def deferred_record_update_def deferred_frame_memoize Let_def split: option.split prod.split if_split)

lemma search_frame_goal_substitute [simp]:
  "search_frame (search_goal_substitute_at P \<sigma> D q r) = search_frame r"
  by (simp add: search_goal_substitute_at_def)

lemma search_frame_goal_substitutes [simp]:
  "search_frame (search_goal_substitute P \<sigma> D r) = search_frame r"
  unfolding search_goal_substitute_def by (rule fold_value_kept) simp

lemma deferred_frame_record_goal [simp]:
  "search_frame (deferred_inner (deferred_record_goal p d)) = search_frame (deferred_inner d)"
  by (simp add: deferred_record_goal_def Let_def split: option.split)

lemma deferred_frame_record_goals [simp]:
  "search_frame (deferred_inner (deferred_record_goals ps d)) = search_frame (deferred_inner d)"
  unfolding deferred_record_goals_def by (rule fold_value_kept) simp

lemma deferred_frame_update_at [simp]:
  "search_frame (deferred_inner (deferred_update_at Dk n d)) = search_frame (deferred_inner d)"
  by (simp add: deferred_update_at_def deferred_record_update_def Let_def split: option.split prod.split)

lemma search_frame_goal_write [simp]: "search_frame (search_goal_write q s' A R r) = search_frame r"
  by (simp add: search_goal_write_def search_frame_def)

lemma deferred_frame_goal_at [simp]:
  "search_frame (deferred_inner (deferred_goal_at P \<sigma> D Dg q d)) = search_frame (deferred_inner d)"
  by (simp add: deferred_goal_at_def Let_def split: option.split prod.split)

lemma deferred_frame_bind [simp]:
  "search_frame (deferred_inner (deferred_bind P s d)) = search_frame (deferred_inner d)"
proof -
  obtain s' x where k: "keyed_collapse_bindings s (shared_sharing (search_state (deferred_inner d))) = (s',x)"
    by (cases "keyed_collapse_bindings s (shared_sharing (search_state (deferred_inner d)))")
  let ?g = "\<lambda>d. search_frame (deferred_inner d)"
  have u: "?g (deferred_update_at Dk n t) = ?g t" for Dk n t by simp
  have v: "?g (deferred_goal_at P (shared_binding_substitution s') (shared_binding_domain s') Dg q t) = ?g t" for Dg q t by simp
  show ?thesis unfolding deferred_bind_def k Let_def prod.case
    by (subst fold_value_kept[where g = ?g, OF u], subst fold_value_kept[where g = ?g, OF v]) simp
qed

lemma deferred_frame_steps [simp]:
  "search_frame (deferred_inner (deferred_at q d r)) = search_frame r"
  "search_frame (deferred_inner (deferred_construct \<kappa> P d hn)) = search_frame (deferred_inner d)"
  by (simp_all add: deferred_at_def deferred_construct_def Let_def split: option.split)

lemma deferred_successors_frame:
  "d' |\<in>| deferred_successors \<kappa> P d h \<Longrightarrow> search_frame (deferred_inner d') = search_frame (deferred_inner d)"
  unfolding deferred_successors_def by (erule search_successors_with_frame) simp_all

subsection \<open>The table attached to the inner search\<close>

definition deferred_attach :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    ('a,'s,'d,'c) deferred_search" where
  "deferred_attach C d = d\<lparr>deferred_inner := search_attach C (deferred_inner d)\<rparr>"

lemma deferred_attach:
  assumes d: "deferred_formed \<kappa> P d"
  shows "deferred_formed \<kappa> P (deferred_attach C d)" and "deferred_project (deferred_attach C d) = deferred_project d"
    and "search_calls (deferred_inner (deferred_attach C d)) = C"
proof -
  let ?r = "deferred_inner d"
  have r: "search_formed \<kappa> P ?r" and K: "search_classes_formed ?r" using deferred_formedD(1,2)[OF d] by blast+
  note h = search_attach[where C = C, OF r]
  show "deferred_formed \<kappa> P (deferred_attach C d)" unfolding deferred_attach_def
    by (rule deferred_inner_formed[OF d h(1) h(7)[OF K] h(4)]) (auto simp: h(5,6))
  show "deferred_project (deferred_attach C d) = deferred_project d"
    by (simp add: deferred_attach_def deferred_project_def deferred_substitution_extends[OF d h(4)] h(2))
  show "search_calls (deferred_inner (deferred_attach C d)) = C" by (simp add: deferred_attach_def h(3))
qed

definition deferred_of_in :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) deferred_search" where
  "deferred_of_in C P st = deferred_attach C (deferred_of P st)"

lemma deferred_of_in_rooted:
  assumes d: "resolution_positions_distinct st" and v: "search_variables_rooted st"
  shows "deferred_formed \<kappa> P (deferred_of_in C P st)" and "deferred_project (deferred_of_in C P st) = st"
    and "search_calls (deferred_inner (deferred_of_in C P st)) = C"
  using deferred_attach[where C = C, OF deferred_of_rooted(1)[OF d v]] deferred_of_rooted(2)[OF d v]
  by (simp_all add: deferred_of_in_def)

subsection \<open>A goal the table closes has one successor, the store standing\<close>

definition deferred_successors_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) deferred_search fset" where
  "deferred_successors_in \<kappa> P d h = (if search_closes (deferred_inner d) h
    then {|d\<lparr>deferred_inner := search_remove_goal (shared_goal_position (shared_entry_goal h)) (deferred_inner d)\<rparr>|}
    else deferred_successors \<kappa> P d h)"

lemma deferred_access_goals [simp]:
  "access_goals (deferred_access \<kappa> P d) = access_goals (shared_access \<kappa> P (deferred_inner d))"
  "access_goal (deferred_access \<kappa> P d) = access_goal (shared_access \<kappa> P (deferred_inner d))"
  by (simp_all add: deferred_access_def)

theorem deferred_successors_in:
  assumes d: "deferred_formed \<kappa> P d" and pl: "search_placeable (deferred_project d)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (deferred_access \<kappa> P d)"
    and D: "\<And>e t. (e,t) \<in> set (search_calls (deferred_inner d)) \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
  shows "fimage deferred_project (deferred_successors_in \<kappa> P d h) =
      finite_goal_successors_in \<Theta> P (deferred_project d) (access_goal (deferred_access \<kappa> P d) h)"
    and "d' |\<in>| deferred_successors_in \<kappa> P d h \<Longrightarrow> deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d') \<and>
      search_frame (deferred_inner d') = search_frame (deferred_inner d)"
proof -
  let ?r = "deferred_inner d" let ?g = "access_goal (deferred_access \<kappa> P d) h"
  let ?q = "shared_goal_position (shared_entry_goal h)"
  have r: "search_formed \<kappa> P ?r" using deferred_formedD(1)[OF d] .
  have s: "shared_state_formed \<kappa> P (search_state ?r)" using search_formedD(1)[OF r] .
  have hg: "h |\<in>| access_goals (shared_access \<kappa> P ?r)" using h by simp
  obtain p where p: "RBT.lookup (shared_goals (search_state ?r)) p = Some h"
    using hg by (auto simp: shared_access_simps tree_values_member)
  have at: "RBT.lookup (shared_goals (search_state ?r)) ?q = Some h" using p shared_goal_lookup_position[OF s p] by simp
  have cl: "search_closes ?r h \<longleftrightarrow> finite_table_closes \<Theta> ?g" using search_closes_table[OF r hg D] by simp
  note rm = deferred_remove_goal[OF d at]
  have proj: "deferred_project (d\<lparr>deferred_inner := search_remove_goal ?q ?r\<rparr>) = finite_goal_closed (deferred_project d) ?g"
    using rm(2) by (simp add: shared_access_simps)
  show "fimage deferred_project (deferred_successors_in \<kappa> P d h) = finite_goal_successors_in \<Theta> P (deferred_project d) ?g"
  proof (cases "search_closes ?r h")
    case True
    then have tc: "finite_table_closes \<Theta> ?g" using cl by simp
    then obtain q' rr e p' where g: "?g = Resolution_Call_Goal q' rr e p'"
      by (cases ?g) (simp_all add: finite_table_closes_def)
    have "finite_goal_successors_in \<Theta> P (deferred_project d) ?g = {|finite_goal_closed (deferred_project d) ?g|}"
      using tc g by simp
    then show ?thesis using True proj by (simp add: deferred_successors_in_def)
  next
    case False
    then have nc: "\<not> finite_table_closes \<Theta> ?g" using cl by simp
    have "fimage deferred_project (deferred_successors_in \<kappa> P d h) = fimage deferred_project (deferred_successors \<kappa> P d h)"
      using False by (simp add: deferred_successors_in_def)
    also have "\<dots> = finite_goal_successors P (deferred_project d) ?g" by (rule deferred_successors(1)[OF d pl sock h])
    also have "\<dots> = finite_goal_successors_in \<Theta> P (deferred_project d) ?g"
      by (rule finite_goal_successors_in_open[OF nc, symmetric])
    finally show ?thesis .
  qed
  show "d' |\<in>| deferred_successors_in \<kappa> P d h \<Longrightarrow> deferred_formed \<kappa> P d' \<and> search_placeable (deferred_project d') \<and>
      search_frame (deferred_inner d') = search_frame (deferred_inner d)"
  proof -
    assume d': "d' |\<in>| deferred_successors_in \<kappa> P d h"
    show ?thesis
    proof (cases "search_closes ?r h")
      case True
      then have e: "d' = d\<lparr>deferred_inner := search_remove_goal ?q ?r\<rparr>" using d' by (simp add: deferred_successors_in_def)
      have "search_placeable (finite_goal_closed (deferred_project d) ?g)"
        unfolding finite_goal_closed_def by (rule search_placeable_fewer[OF pl])
      then show ?thesis using rm(1) proj by (simp add: e)
    next
      case False
      then have "d' |\<in>| deferred_successors \<kappa> P d h" using d' by (simp add: deferred_successors_in_def)
      then show ?thesis using deferred_successors(2)[OF d pl sock h] deferred_successors_frame by blast
    qed
  qed
qed

definition deferred_representation_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) deferred_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) resolution_representation" where
  "deferred_representation_in \<kappa> P = (deferred_representation \<kappa> P)\<lparr>rep_successors := deferred_successors_in \<kappa> P\<rparr>"

lemma deferred_representation_in_fields [simp]:
  "rep_access (deferred_representation_in \<kappa> P) = deferred_access \<kappa> P"
  "rep_empty (deferred_representation_in \<kappa> P) = (\<lambda>d. RBT.is_empty (shared_goals (search_state (deferred_inner d))))"
  "rep_project (deferred_representation_in \<kappa> P) = deferred_project"
  "rep_refresh (deferred_representation_in \<kappa> P) = id"
  "rep_construct (deferred_representation_in \<kappa> P) = deferred_construct \<kappa> P"
  "rep_successors (deferred_representation_in \<kappa> P) = deferred_successors_in \<kappa> P"
  by (simp_all add: deferred_representation_in_def deferred_representation_def)

theorem deferred_search_in_rooted:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_rooted st"
    and D: "\<And>e t. (e,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
  shows "represented_search_in (deferred_representation_in \<kappa> P) (\<lambda>d. search_closes (deferred_inner d)) (\<lambda>r h. False)
      \<kappa> P n (deferred_of_in C P st) = finite_resolution_search_in \<Theta> \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "deferred_representation_in \<kappa> P"
  let ?F = "\<lambda>d. deferred_formed \<kappa> P d \<and> search_placeable (deferred_project d) \<and> search_calls (deferred_inner d) = C"
  have DC: "\<And>d e t. ?F d \<Longrightarrow> (e,t) \<in> set (search_calls (deferred_inner d)) \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
    using D by simp
  have "represented_search_in ?R (\<lambda>d. search_closes (deferred_inner d)) (\<lambda>r h. False) \<kappa> P n (deferred_of_in C P st) =
      finite_resolution_search_by_in \<Theta> (finite_resolution_select_in \<Theta> (\<lambda>st g. False) \<kappa> P) \<kappa> P n
        (rep_project ?R (deferred_of_in C P st))"
  proof (rule represented_search_in[where F = ?F])
    show "?F (deferred_of_in C P st)" using deferred_of_in_rooted[OF d v] pl by simp
  next
    fix s assume f: "?F s"
    then show "access_formed \<kappa> P (rep_access ?R s) (rep_project ?R s)" using deferred_access_formed[OF conjunct1[OF f]] by simp
  next
    fix s assume f: "?F s"
    have "resolution_pending (deferred_project s) = fimage (\<lambda>h. shared_goal_project (search_table (deferred_inner s))
        (shared_entry_goal h)) (tree_values (shared_goals (search_state (deferred_inner s))))"
      using deferred_pending[OF conjunct1[OF f]] by (simp add: shared_state_project_fields)
    then show "rep_empty ?R s \<longleftrightarrow> resolution_pending (rep_project ?R s) = {||}" by (simp add: rbt_empty_values)
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s) \<and> rep_project ?R (rep_refresh ?R s) = rep_project ?R s" by simp
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (deferred_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "deferred_access \<kappa> P s"] m by auto
    note c = deferred_construct[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] n]
    have "search_calls (deferred_inner (deferred_construct \<kappa> P s m)) = search_calls (deferred_inner s)"
      using deferred_frame_steps(2)[of \<kappa> P s m] by (simp add: search_frame_def)
    then show "?F (rep_construct ?R s m) \<and>
        rep_project ?R (rep_construct ?R s m) = finite_construction_step \<kappa> P (rep_project ?R s) (access_node (rep_access ?R s) m)"
      using c f by simp
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    have h': "h |\<in>| access_goals (deferred_access \<kappa> P s)" using h by simp
    note sc = deferred_successors_in[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] sock h' DC[OF f]]
    show "fimage (rep_project ?R) (rep_successors ?R s h) =
        finite_goal_successors_in \<Theta> P (rep_project ?R s) (access_goal (rep_access ?R s) h) \<and>
        (\<forall>s'. s' |\<in>| rep_successors ?R s h \<longrightarrow> ?F s')"
      using sc(1) sc(2) f by (auto simp: search_frame_def)
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    have h': "h |\<in>| access_goals (shared_access \<kappa> P (deferred_inner s))" using h by simp
    show "search_closes (deferred_inner s) h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access ?R s) h)"
      using search_closes_table[OF deferred_formedD(1)[OF conjunct1[OF f]] h' DC[OF f]] by simp
  next
    fix s h show "False \<longleftrightarrow> False" by simp
  qed
  then show ?thesis using deferred_of_in_rooted(2)[OF d v] by (simp add: finite_resolution_search_in_def)
qed

subsection \<open>The closing among the inner search's kept classes\<close>

definition deferred_select_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) deferred_search \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "deferred_select_in \<kappa> P rp d =
    kept_select_by_in (search_closed (deferred_inner d)) (ffilter rp) (deferred_inner d) (deferred_access \<kappa> P d)"

theorem deferred_select_in:
  assumes d: "deferred_formed \<kappa> P d"
  shows "deferred_select_in \<kappa> P rp d = access_select_in (search_closes (deferred_inner d)) rp (deferred_access \<kappa> P d)"
  unfolding deferred_select_in_def deferred_access_def
  by (rule kept_select_over_in[OF deferred_formedD(1,2)[OF d] search_closed_class[OF deferred_formedD(1)[OF d]]
    search_closes_call])

theorem deferred_kept_search_in_rooted:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st" and v: "search_variables_rooted st"
    and D: "\<And>e t. (e,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
  shows "selected_search (deferred_representation_in \<kappa> P) (deferred_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of_in C P st) =
      finite_resolution_search_in \<Theta> \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "deferred_representation_in \<kappa> P"
  let ?F = "\<lambda>d. deferred_formed \<kappa> P d \<and> search_placeable (deferred_project d) \<and> search_calls (deferred_inner d) = C"
  have DC: "\<And>d e t. ?F d \<Longrightarrow> (e,t) \<in> set (search_calls (deferred_inner d)) \<longleftrightarrow> resolution_table_lookup \<Theta> (e,t) \<noteq> None"
    using D by simp
  have "selected_search ?R (deferred_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n (deferred_of_in C P st) =
      represented_search_in ?R (\<lambda>d. search_closes (deferred_inner d)) (\<lambda>r h. False) \<kappa> P n (deferred_of_in C P st)"
  proof (rule selected_search_in[where F = ?F])
    show "?F (deferred_of_in C P st)" using deferred_of_in_rooted[OF d v] pl by simp
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s)" by simp
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (deferred_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "deferred_access \<kappa> P s"] m by auto
    show "?F (rep_construct ?R s m)"
      using deferred_construct(1)[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] n] deferred_frame_steps(2)[of \<kappa> P s m] f
      by (simp add: search_frame_def)
  next
    fix s h s' assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)" and s': "s' |\<in>| rep_successors ?R s h"
    have h': "h |\<in>| access_goals (deferred_access \<kappa> P s)" and s'': "s' |\<in>| deferred_successors_in \<kappa> P s h"
      using h s' by simp_all
    note sc = deferred_successors_in[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] sock h' DC[OF f]]
    show "?F s'" using sc(2)[OF s''] f by (simp add: search_frame_def)
  next
    fix s assume f: "?F s"
    show "deferred_select_in \<kappa> P (\<lambda>h. False) s =
        access_select_in ((\<lambda>d. search_closes (deferred_inner d)) s) ((\<lambda>r h. False) s) (rep_access ?R s)"
      using deferred_select_in[OF conjunct1[OF f]] by simp
  qed
  also have "\<dots> = finite_resolution_search_in \<Theta> \<kappa> P n st" by (rule deferred_search_in_rooted[OF sock pl v D])
  finally show ?thesis .
qed

text \<open>
  The search at a listed table is computed over the deferred search wherever the state's variables are rooted, over
  the shared search elsewhere, both at the table; D1b's code equation is its instance at the empty table
  (@{thm [source] finite_resolution_search_listed_empty}).
\<close>

declare finite_resolution_search_listed_shared_code [code del]

lemma finite_resolution_search_listed_deferred_code [code]:
  "finite_resolution_search_listed es \<kappa> P n st = (if clause_sockets_distinct P \<and> search_placeable st
    then (if search_variables_rooted st
      then selected_search (deferred_representation_in \<kappa> P) (deferred_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n
        (deferred_of_in (map fst es) P st)
      else selected_search (shared_representation_in \<kappa> P) (search_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n
        (search_of_in (map fst es) P st))
    else finite_resolution_search_by_in (listed_table es) (finite_resolution_select_in (listed_table es) (\<lambda>st g. False) \<kappa> P)
      \<kappa> P n st)"
  using finite_resolution_search_listed_shared_code[of es \<kappa> P n st]
    deferred_kept_search_in_rooted[where C = "map fst es" and \<Theta> = "listed_table es", OF _ _ _ listed_table_calls,
      of P st \<kappa> n]
  by (auto simp: finite_resolution_search_listed_def)

export_code finite_resolution_search_listed checking SML

end
