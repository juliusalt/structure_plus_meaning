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

text \<open>
  It also keeps three classes of the selection (task 865): the candidate goals, the settled ones and the single ones,
  each a tree from the positions of its goals to their entries, so that the selection reads the first of a class in the
  order of positions and a step updates the classes only at the goals it touches.
\<close>

record (overloaded) ('a,'s::linorder,'d,'c) goal_classes =
  class_candidates :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt"
  class_settled :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt"
  class_single :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt"

record (overloaded) ('a,'s::linorder,'d,'c) shared_search =
  search_state :: "('a,'s,'d,'c) shared_state"
  search_registered :: "('s list, 's list fset) rbt"
  search_values :: "('s list, (('a,'s,'d,'c) shared_derivation \<times> 'a \<times> finite_factor_term) fset) rbt"
  search_classes :: "('a,'s,'d,'c) goal_classes"
  search_calls :: "('d \<times> finite_factor_term) list"
  search_index :: "(nat, 'd fset) rbt"
  search_closed :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt"

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

text \<open>
  The calls of a table of certified calls (task 876, GT3) are kept beside the search, each call's term shared into the
  search's term table: the index of the table's calls by reference holds at each reference the sites of the calls
  making that term (the bucket tree of the index notion, @{text Factor_Indexed_Resolution}). A ground call goal is
  closed by the table exactly when its site is in the bucket of its reference, below the root; the goals the table
  closes are kept as a class of their own, by position. The table's calls are read, never an entry's certificate.
  A search made without a table holds none: its index and its class are empty.
\<close>

fun shared_goal_closes :: "(nat,'d fset) rbt \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_goal_closes E (Shared_Call_Goal q r d (Shared_Ground i)) \<longleftrightarrow> q \<noteq> [] \<and> d |\<in>| tree_bucket E i"
| "shared_goal_closes E g \<longleftrightarrow> False"

lemma shared_goal_closes_cases:
  "shared_goal_closes E g \<longleftrightarrow> (\<exists>q r d i. g = Shared_Call_Goal q r d (Shared_Ground i) \<and> q \<noteq> [] \<and> d |\<in>| tree_bucket E i)"
  by (cases "(E,g)" rule: shared_goal_closes.cases) auto

lemma shared_goal_closes_empty [simp]: "\<not> shared_goal_closes RBT.empty g"
  by (simp add: shared_goal_closes_cases)

definition search_closes :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "search_closes r h \<longleftrightarrow> shared_goal_closes (search_index r) (shared_entry_goal h)"

definition calls_indexed :: "shape list \<Rightarrow> (nat,'d fset) rbt \<Rightarrow> ('d \<times> finite_factor_term) set \<Rightarrow> bool" where
  "calls_indexed T E D \<longleftrightarrow> (\<forall>d t. (d,t) \<in> D \<longrightarrow> (\<exists>i. reference_term T i = Some t \<and> d |\<in>| tree_bucket E i)) \<and>
    (\<forall>i d. d |\<in>| tree_bucket E i \<longrightarrow> (\<exists>t. reference_term T i = Some t \<and> (d,t) \<in> D))"

definition search_closing_formed :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_closing_formed r \<longleftrightarrow> calls_indexed (search_table r) (search_index r) (set (search_calls r)) \<and>
    (\<forall>p. RBT.lookup (search_closed r) p = (case RBT.lookup (shared_goals (search_state r)) p of None \<Rightarrow> None
      | Some h \<Rightarrow> if search_closes r h then Some h else None))"

definition search_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_formed \<kappa> P r \<longleftrightarrow> shared_state_formed \<kappa> P (search_state r) \<and> search_registered_formed r \<and>
    search_values_formed \<kappa> P r \<and> search_closing_formed r"

lemma search_formedD:
  assumes "search_formed \<kappa> P r"
  shows "shared_state_formed \<kappa> P (search_state r)" "search_registered_formed r" "search_values_formed \<kappa> P r"
  using assms by (simp_all add: search_formed_def)

lemma search_formed_closing: "search_formed \<kappa> P r \<Longrightarrow> search_closing_formed r"
  by (simp add: search_formed_def)

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

text \<open>
  What a search reads of its shared state alone is the state's access; the search's access adds what the witness
  construction and the kept values give: the registered variables a node leaves free, the values not constructed, the
  registered positions and the goals the selection may hold back.
\<close>

text \<open>
  The access over a given goal set: the state's access holds the state's goals, and a test of one goal, which reads no
  goal set, is made over the empty one (@{text state_access_goal_tests}), so that it never walks the goal tree.
\<close>

definition state_access_over :: "('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) search_access" where
  "state_access_over G s = (let T = shared_state_table s in
    \<lparr>access_goals = G,
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
     access_free = \<lambda>hn. {||}, access_value_none = \<lambda>hn a. True, access_registered = {||},
     access_holdable = \<lambda>h. False, access_witnesses = shared_witnesses s,
     access_call_variables = \<lambda>hn. shared_pattern_variables (shared_derivation_call (shared_entry_node hn))\<rparr>)"

text \<open>
  The table is read where a goal or a node is decoded, not where the access is built (#886's finding 4): the code
  unfolds the let into the decoding closures, and a call goal is not solvable without reading it. A node's call
  variables are read of its shared call, never decoded (#886's finding 2).
\<close>

lemma state_access_over_code [code]:
  "state_access_over G s =
    \<lparr>access_goals = G,
     access_goals_at = \<lambda>q. option_fset (RBT.lookup (shared_goals s) q),
     access_nodes_at = \<lambda>q. option_fset (RBT.lookup (shared_nodes s) q),
     access_goal = \<lambda>h. shared_goal_project (shared_state_table s) (shared_entry_goal h),
     access_node = \<lambda>hn. shared_derivation_project (shared_state_table s) (shared_entry_node hn),
     access_goal_position = \<lambda>h. shared_goal_position (shared_entry_goal h),
     access_node_position = \<lambda>hn. shared_derivation_position (shared_entry_node hn),
     access_variables = \<lambda>h. shared_goal_variables (shared_entry_goal h),
     access_alternatives = shared_entry_alternatives,
     access_is_call = \<lambda>h. shared_goal_is_call (shared_entry_goal h),
     access_solvable = \<lambda>h. (case shared_entry_goal h of Shared_Call_Goal q rr d p \<Rightarrow> False
       | Shared_Material_Goal q rr M \<Rightarrow> shared_goal_solvable (shared_state_table s) (shared_entry_goal h)),
     access_leaf = \<lambda>h. shared_goal_leaf (shared_entry_goal h),
     access_key = \<lambda>h. shared_call_key (shared_entry_goal h),
     access_closes = shared_closes,
     access_same = shared_same,
     access_goal_calls = tree_bucket (shared_goal_calls s),
     access_node_calls = tree_bucket (shared_node_calls s),
     access_open = tree_count (shared_open s),
     access_holders = tree_bucket (shared_holders s),
     access_free = \<lambda>hn. {||}, access_value_none = \<lambda>hn a. True, access_registered = {||},
     access_holdable = \<lambda>h. False, access_witnesses = shared_witnesses s,
     access_call_variables = \<lambda>hn. shared_pattern_variables (shared_derivation_call (shared_entry_node hn))\<rparr>"
  by (simp add: state_access_over_def Let_def fun_eq_iff split: shared_goal.split)

definition state_access :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) search_access" where
  "state_access s = state_access_over (tree_values (shared_goals s)) s"

definition shared_access :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c) search_access" where
  "shared_access \<kappa> P r = (let s = search_state r in (state_access s)\<lparr>
     access_free := \<lambda>hn. shared_free_registered \<kappa> (shared_entry_node hn),
     access_value_none := \<lambda>hn a. a |\<in>| tree_bucket (shared_unconstructed s) (shared_derivation_position (shared_entry_node hn))
       \<or> search_value \<kappa> P r (shared_entry_node hn) a = None,
     access_registered := fset_of_list (RBT.keys (search_registered r)),
     access_holdable := \<lambda>h. shared_goal_registered h \<noteq> {||}\<rparr>)"

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
  "access_call_variables (shared_access \<kappa> P r) hn = shared_pattern_variables (shared_derivation_call (shared_entry_node hn))"
  by (simp_all add: shared_access_def state_access_def state_access_over_def Let_def)

lemma shared_goal_lookup_position:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_goals s) q = Some h"
  shows "shared_goal_position (shared_entry_goal h) = q"
  using shared_entries_formed(1)[OF s at] by (simp add: goal_entry_formed_def)

lemma shared_node_lookup_position:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_nodes s) q = Some hn"
  shows "shared_derivation_position (shared_entry_node hn) = q"
  using shared_entries_formed(2)[OF s at] by (simp add: node_entry_formed_def)

text \<open>
  A formed state holds a pending goal under a position exactly when its goal tree holds a key under it, and its open
  count there is zero exactly when it holds none: the solvedness of a node read from the tree's keys.
\<close>

lemma shared_pending_under:
  assumes s: "shared_state_formed \<kappa> P s"
  shows "fBex (resolution_pending (shared_state_project s)) (\<lambda>g. take (length p) (resolution_goal_position g) = p) \<longleftrightarrow>
    (\<exists>q. RBT.lookup (shared_goals s) q \<noteq> None \<and> take (length p) q = p)"
proof
  assume "fBex (resolution_pending (shared_state_project s)) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
  then obtain g where g: "g |\<in>| resolution_pending (shared_state_project s)"
    "take (length p) (resolution_goal_position g) = p" by blast
  then obtain q h where at: "RBT.lookup (shared_goals s) q = Some h"
    and e: "shared_goal_project (shared_state_table s) (shared_entry_goal h) = g"
    unfolding shared_state_project_member(1) by blast
  have "resolution_goal_position g = q"
    using e shared_goal_lookup_position[OF s at] by (cases "shared_entry_goal h") auto
  then show "\<exists>q. RBT.lookup (shared_goals s) q \<noteq> None \<and> take (length p) q = p" using at g(2) by auto
next
  assume "\<exists>q. RBT.lookup (shared_goals s) q \<noteq> None \<and> take (length p) q = p"
  then obtain q h where at: "RBT.lookup (shared_goals s) q = Some h" and pre: "take (length p) q = p" by auto
  have m: "shared_goal_project (shared_state_table s) (shared_entry_goal h) |\<in>| resolution_pending (shared_state_project s)"
    unfolding shared_state_project_member(1) using at by blast
  have "resolution_goal_position (shared_goal_project (shared_state_table s) (shared_entry_goal h)) = q"
    using shared_goal_lookup_position[OF s at] by (cases "shared_entry_goal h") auto
  then show "fBex (resolution_pending (shared_state_project s)) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
    using m pre by blast
qed

lemma shared_open_zero:
  assumes s: "shared_state_formed \<kappa> P s"
  shows "tree_count (shared_open s) p = 0 \<longleftrightarrow> \<not> (\<exists>q. RBT.lookup (shared_goals s) q \<noteq> None \<and> take (length p) q = p)"
proof -
  have c: "tree_count (shared_open s) p = open_count (shared_goals s) p"
    using s by (simp add: shared_state_formed_def)
  have "tree_count (shared_open s) p = 0 \<longleftrightarrow> tree_keys_under (shared_goals s) p = {}"
    by (simp add: c open_count_zero)
  also have "\<dots> \<longleftrightarrow> \<not> (\<exists>q. RBT.lookup (shared_goals s) q \<noteq> None \<and> take (length p) q = p)"
    unfolding tree_keys_under_def Collect_empty_eq by blast
  finally show ?thesis .
qed

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
    fix n q assume "RBT.lookup (shared_nodes ?s) q = Some n"
    then have "shared_pattern_formed ?T (shared_derivation_call (shared_entry_node n))"
      using nf by (auto simp: node_entry_formed_def shared_derivation_formed_def)
    then show "shared_pattern_variables (shared_derivation_call (shared_entry_node n)) =
        finite_pattern_variables (resolution_node_call (shared_derivation_project ?T (shared_entry_node n)))"
      by (simp add: shared_derivation_project_def shared_pattern_variables_project)
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
    show "tree_count (shared_open ?s) (resolution_node_position nd) = 0 \<longleftrightarrow>
        finite_solved_node (search_project r) nd"
      by (simp only: finite_solved_node_def shared_open_zero[OF s] shared_pending_under[OF s])
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

section \<open>The selection's classes kept in the search\<close>

text \<open>
  #830's fix (1) (b), task 865: the choice's classes (@{thm [source] access_goal_choice_classes}) kept in the search.
  A class is a tree from the positions of the goals that pass its test to their entries; it is formed at a state when
  it holds exactly the goals of the state passing the test, the tests being R3's of the goals' values at the state's
  projection (@{text classes_formed}). A test of a ground call reads only the nodes and the goals making that call and
  the solvedness of those nodes (@{thm [source] goal_tests_frame}), so a step changing the goal and the node at one
  position changes only the tests of that position's goal and of the goals making a ground call whose presence the step
  changes: the call the goal or the node there makes, when its ground key changes, and the call a node at a prefix of the
  position makes, when the step changes whether a goal stands there and the prefix's open count moves between zero and
  nonzero; the goals the goal-call index finds for those references are the ones the step touches
  (@{text classes_touched}). A step that keeps every such key and presence, as a substitution does, touches its own
  position alone. A step updates the classes there, testing each goal through the state's access, and nowhere
  else (@{text classes_step}). Formation is established where a search state is made and kept by every step; it is never
  checked again.
\<close>

subsection \<open>The table's closing read through the index\<close>

lemma calls_indexed_extends:
  assumes I: "calls_indexed T E D" and ext: "table_extends T T'"
  shows "calls_indexed T' E D"
  using I ext unfolding calls_indexed_def table_extends_def by meson

lemma calls_indexed_bucket:
  assumes tf: "table_formed T" and I: "calls_indexed T E D" and t: "reference_term T i = Some t"
  shows "d |\<in>| tree_bucket E i \<longleftrightarrow> (d,t) \<in> D"
proof
  assume "d |\<in>| tree_bucket E i"
  then obtain u where "reference_term T i = Some u" "(d,u) \<in> D" using I unfolding calls_indexed_def by blast
  then show "(d,t) \<in> D" using t by simp
next
  assume "(d,t) \<in> D"
  then obtain j where j: "reference_term T j = Some t" "d |\<in>| tree_bucket E j" using I unfolding calls_indexed_def by blast
  have "j = i" by (rule reference_term_injective[OF tf j(1) t])
  then show "d |\<in>| tree_bucket E i" using j(2) by simp
qed

text \<open>
  The closing compares a goal's site and its shared reference with an entry's: by the canonical equality of
  references (@{thm [source] reference_term_injective}), a formed ground call goal is closed through the index exactly
  when the table holds its decoded call (@{const finite_table_closes}).
\<close>

lemma shared_goal_closes_table:
  assumes tf: "table_formed T" and I: "calls_indexed T E D"
    and D: "\<And>d t. (d,t) \<in> D \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
    and g: "shared_goal_formed T g"
  shows "shared_goal_closes E g \<longleftrightarrow> finite_table_closes \<Theta> (shared_goal_project T g)"
proof (cases g)
  case (Shared_Call_Goal q r d p)
  have pf: "shared_pattern_formed T p" and pc: "shared_collapsed p" using g Shared_Call_Goal by simp_all
  show ?thesis
  proof (cases "shared_pattern_variables p = {||}")
    case True
    obtain i where i: "p = Shared_Ground i" using shared_collapsed_ground[OF pc True] by blast
    obtain t where t: "reference_term T i = Some t" using table_formed_decodes[OF tf] pf i by auto
    show ?thesis using calls_indexed_bucket[OF tf I t, of d] D[of d t] t i Shared_Call_Goal
      by (auto simp: finite_table_closes_def split: option.splits)
  next
    case False
    have "finite_pattern_variables (shared_pattern_project T p) \<noteq> {||}"
      using False shared_pattern_variables_project[OF pf] by simp
    moreover have "\<not> shared_goal_closes E g" using False Shared_Call_Goal by (cases p) simp_all
    ultimately show ?thesis using Shared_Call_Goal by (simp add: finite_table_closes_def)
  qed
next
  case (Shared_Material_Goal q r M)
  then show ?thesis by (simp add: finite_table_closes_def)
qed

lemma search_closes_table:
  assumes r: "search_formed \<kappa> P r" and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
    and D: "\<And>d t. (d,t) \<in> set (search_calls r) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "search_closes r h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (shared_access \<kappa> P r) h)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" and c: "search_closing_formed r"
    using r by (simp_all add: search_formed_def)
  obtain q where q: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    using h by (auto simp: shared_access_simps tree_values_member)
  have gf: "shared_goal_formed (search_table r) (shared_entry_goal h)"
    using shared_entries_formed(1)[OF s q] by (simp add: goal_entry_formed_def)
  have tf: "table_formed (search_table r)" by (rule shared_entries_formed(4)[OF s])
  have I: "calls_indexed (search_table r) (search_index r) (set (search_calls r))"
    using c by (simp add: search_closing_formed_def)
  show ?thesis using shared_goal_closes_table[OF tf I D gf] by (simp add: search_closes_def shared_access_simps)
qed

lemma search_closes_call: "search_closes r h \<Longrightarrow> shared_goal_is_call (shared_entry_goal h)"
  by (cases "shared_entry_goal h") (simp_all add: search_closes_def)

lemma state_access_tests:
  "access_candidate (shared_access \<kappa> P r) h = access_candidate (state_access (search_state r)) h"
  "access_settled (shared_access \<kappa> P r) h = access_settled (state_access (search_state r)) h"
  "access_single (shared_access \<kappa> P r) h = access_single (state_access (search_state r)) h"
  by (simp_all add: shared_access_def Let_def access_candidate_def access_settled_def access_single_def
      access_pruned_def access_pruned_among_def access_reusable_def access_waits_def access_ground_def)

lemma state_access_goal_tests:
  "access_candidate (state_access s) h = access_candidate (state_access_over {||} s) h"
  "access_settled (state_access s) h = access_settled (state_access_over {||} s) h"
  "access_single (state_access s) h = access_single (state_access_over {||} s) h"
  by (simp_all add: state_access_def state_access_over_def Let_def access_candidate_def access_settled_def
      access_single_def access_pruned_def access_pruned_among_def access_reusable_def access_waits_def access_ground_def)

definition class_value :: "('e \<Rightarrow> bool) \<Rightarrow> ('k::linorder,'e) rbt \<Rightarrow> 'k \<Rightarrow> 'e option" where
  "class_value Q G p = (case RBT.lookup G p of None \<Rightarrow> None | Some h \<Rightarrow> if Q h then Some h else None)"

definition kept_candidate :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "kept_candidate T h \<longleftrightarrow> finite_candidate_goal (shared_goal_project T (shared_entry_goal h))"

definition kept_settled :: "shape list \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "kept_settled T st h \<longleftrightarrow> kept_candidate T h \<and>
    goal_settled (shared_entry_alternatives h) st (shared_goal_project T (shared_entry_goal h))"

definition kept_single :: "shape list \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "kept_single T st h \<longleftrightarrow> kept_candidate T h \<and>
    goal_single (shared_entry_alternatives h) st (shared_goal_project T (shared_entry_goal h))"

definition classes_formed :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) goal_classes \<Rightarrow> bool" where
  "classes_formed s K \<longleftrightarrow>
    (\<forall>p. RBT.lookup (class_candidates K) p = class_value (kept_candidate (shared_state_table s)) (shared_goals s) p) \<and>
    (\<forall>p. RBT.lookup (class_settled K) p =
      class_value (kept_settled (shared_state_table s) (shared_state_project s)) (shared_goals s) p) \<and>
    (\<forall>p. RBT.lookup (class_single K) p =
      class_value (kept_single (shared_state_table s) (shared_state_project s)) (shared_goals s) p)"

abbreviation search_classes_formed :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> bool" where
  "search_classes_formed r \<equiv> classes_formed (search_state r) (search_classes r)"

definition empty_classes :: "('a,'s::linorder,'d,'c) goal_classes" where
  "empty_classes = \<lparr>class_candidates = RBT.empty, class_settled = RBT.empty, class_single = RBT.empty\<rparr>"

text \<open>
  A class tree is written where it changes: a goal is put in the classes that hold it, and deleted only from a class
  that held it (q159's skip, review 885's follow-up 2).
\<close>

definition class_drop :: "'k::linorder \<Rightarrow> ('k,'e) rbt \<Rightarrow> ('k,'e) rbt" where
  "class_drop q t = (if RBT.lookup t q = None then t else RBT.delete q t)"

definition class_put :: "bool \<Rightarrow> 'k::linorder \<Rightarrow> 'e \<Rightarrow> ('k,'e) rbt \<Rightarrow> ('k,'e) rbt" where
  "class_put b q h t = (if b then RBT.insert q h t else class_drop q t)"

lemma class_drop_lookup [simp]: "RBT.lookup (class_drop q t) p = (if p = q then None else RBT.lookup t p)"
  by (auto simp: class_drop_def)

lemma class_put_lookup [simp]:
  "RBT.lookup (class_put b q h t) p = (if p = q then (if b then Some h else None) else RBT.lookup t p)"
  by (simp add: class_put_def)

definition classes_at :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) goal_classes \<Rightarrow>
    ('a,'s,'d,'c) goal_classes" where
  "classes_at s q K = (case RBT.lookup (shared_goals s) q of
      None \<Rightarrow> \<lparr>class_candidates = class_drop q (class_candidates K), class_settled = class_drop q (class_settled K),
        class_single = class_drop q (class_single K)\<rparr>
    | Some h \<Rightarrow> (let V = state_access_over {||} s; c = access_candidate V h in
        \<lparr>class_candidates = class_put c q h (class_candidates K),
         class_settled = class_put (c \<and> access_settled V h) q h (class_settled K),
         class_single = class_put (c \<and> access_single V h) q h (class_single K)\<rparr>))"

definition classes_update :: "'s list list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) goal_classes \<Rightarrow>
    ('a,'s,'d,'c) goal_classes" where
  "classes_update ps s K = fold (classes_at s) ps K"

lemma classes_at_lookup:
  "RBT.lookup (class_candidates (classes_at s q K)) p = (if p = q then
      class_value (access_candidate (state_access s)) (shared_goals s) p else RBT.lookup (class_candidates K) p)"
  "RBT.lookup (class_settled (classes_at s q K)) p = (if p = q then
      class_value (\<lambda>h. access_candidate (state_access s) h \<and> access_settled (state_access s) h) (shared_goals s) p
    else RBT.lookup (class_settled K) p)"
  "RBT.lookup (class_single (classes_at s q K)) p = (if p = q then
      class_value (\<lambda>h. access_candidate (state_access s) h \<and> access_single (state_access s) h) (shared_goals s) p
    else RBT.lookup (class_single K) p)"
  by (auto simp: classes_at_def class_value_def Let_def state_access_goal_tests split: option.split)

lemma classes_update_lookup:
  "RBT.lookup (class_candidates (classes_update ps s K)) p = (if p \<in> set ps then
      class_value (access_candidate (state_access s)) (shared_goals s) p else RBT.lookup (class_candidates K) p)"
  "RBT.lookup (class_settled (classes_update ps s K)) p = (if p \<in> set ps then
      class_value (\<lambda>h. access_candidate (state_access s) h \<and> access_settled (state_access s) h) (shared_goals s) p
    else RBT.lookup (class_settled K) p)"
  "RBT.lookup (class_single (classes_update ps s K)) p = (if p \<in> set ps then
      class_value (\<lambda>h. access_candidate (state_access s) h \<and> access_single (state_access s) h) (shared_goals s) p
    else RBT.lookup (class_single K) p)"
  by (induction ps arbitrary: K) (auto simp: classes_update_def classes_at_lookup)

text \<open>A goal's tests through the state's access are R3's tests of its value at a formed search.\<close>

lemma kept_tests:
  assumes r: "search_formed \<kappa> P r" and at: "RBT.lookup (shared_goals (search_state r)) p = Some h"
  shows "access_candidate (state_access (search_state r)) h \<longleftrightarrow> kept_candidate (search_table r) h"
    and "access_candidate (state_access (search_state r)) h \<and> access_settled (state_access (search_state r)) h \<longleftrightarrow>
      kept_settled (search_table r) (search_project r) h"
    and "access_candidate (state_access (search_state r)) h \<and> access_single (state_access (search_state r)) h \<longleftrightarrow>
      kept_single (search_table r) (search_project r) h"
proof -
  interpret V: access_formed \<kappa> P "shared_access \<kappa> P r" "search_project r" by (rule shared_access_formed[OF r])
  have h: "h |\<in>| access_goals (shared_access \<kappa> P r)" using at by (auto simp: shared_access_simps tree_values_member)
  note t = state_access_tests[of \<kappa> P r h, symmetric]
  show "access_candidate (state_access (search_state r)) h \<longleftrightarrow> kept_candidate (search_table r) h"
    using V.candidate[OF h] t(1) by (simp add: kept_candidate_def shared_access_simps)
  show "access_candidate (state_access (search_state r)) h \<and> access_settled (state_access (search_state r)) h \<longleftrightarrow>
      kept_settled (search_table r) (search_project r) h"
    using V.candidate[OF h] V.settled[OF h] t(1,2) by (simp add: kept_settled_def kept_candidate_def shared_access_simps)
  show "access_candidate (state_access (search_state r)) h \<and> access_single (state_access (search_state r)) h \<longleftrightarrow>
      kept_single (search_table r) (search_project r) h"
    using V.candidate[OF h] V.single[OF h] t(1,3) by (simp add: kept_single_def kept_candidate_def shared_access_simps)
qed

lemma classes_update_formed:
  assumes r: "search_formed \<kappa> P r"
    and out: "\<And>p. p \<notin> set ps \<Longrightarrow>
      RBT.lookup (class_candidates K) p = class_value (kept_candidate (search_table r)) (shared_goals (search_state r)) p \<and>
      RBT.lookup (class_settled K) p =
        class_value (kept_settled (search_table r) (search_project r)) (shared_goals (search_state r)) p \<and>
      RBT.lookup (class_single K) p =
        class_value (kept_single (search_table r) (search_project r)) (shared_goals (search_state r)) p"
  shows "classes_formed (search_state r) (classes_update ps (search_state r) K)"
proof -
  let ?G = "shared_goals (search_state r)" and ?V = "state_access (search_state r)"
  have v: "class_value (access_candidate ?V) ?G p = class_value (kept_candidate (search_table r)) ?G p \<and>
      class_value (\<lambda>h. access_candidate ?V h \<and> access_settled ?V h) ?G p =
        class_value (kept_settled (search_table r) (search_project r)) ?G p \<and>
      class_value (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) ?G p =
        class_value (kept_single (search_table r) (search_project r)) ?G p" for p
  proof (cases "RBT.lookup ?G p")
    case None
    then show ?thesis by (simp add: class_value_def)
  next
    case (Some h)
    then show ?thesis using kept_tests[OF r Some] by (simp add: class_value_def)
  qed
  show ?thesis unfolding classes_formed_def using out v by (auto simp: classes_update_lookup)
qed

subsection \<open>The goals a step touches\<close>

text \<open>
  The ground key of a goal or a node is the site and the reference of the call it makes when that call is ground, and
  nothing otherwise: at a formed entry it says exactly whether the entry makes a given ground call
  (@{text goal_ground_key_project}, @{text node_ground_key_project}), and at a position of a formed state whether the
  state holds a pending goal or a node making it there (@{text goal_ground_key_pending}, @{text node_ground_key_nodes}).
  A step names the references of the keys it changes (@{text changed_refs}).
\<close>

definition goal_ground_key :: "('a,'s,'d,'c) shared_goal_entry option \<Rightarrow> ('d \<times> nat) option" where
  "goal_ground_key go = (case go of None \<Rightarrow> None | Some h \<Rightarrow> (case shared_entry_goal h of
      Shared_Call_Goal q r d x \<Rightarrow> (case x of Shared_Ground i \<Rightarrow> Some (d,i) | Shared_Variable a \<Rightarrow> None
        | Shared_Node A p r' \<Rightarrow> None)
    | Shared_Material_Goal q r M \<Rightarrow> None))"

definition node_ground_key :: "('a,'s,'d,'c) shared_node_entry option \<Rightarrow> ('d \<times> nat) option" where
  "node_ground_key no = (case no of None \<Rightarrow> None | Some hn \<Rightarrow> (case shared_derivation_call (shared_entry_node hn) of
      Shared_Ground i \<Rightarrow> Some (shared_derivation_site (shared_entry_node hn), i) | Shared_Variable a \<Rightarrow> None
    | Shared_Node A p r \<Rightarrow> None))"

definition key_refs :: "('d \<times> nat) option \<Rightarrow> nat fset" where
  "key_refs k = (case k of None \<Rightarrow> {||} | Some di \<Rightarrow> {|snd di|})"

definition changed_refs :: "('d \<times> nat) option \<Rightarrow> ('d \<times> nat) option \<Rightarrow> nat fset" where
  "changed_refs k k' = (if k = k' then {||} else key_refs k |\<union>| key_refs k')"

lemma goal_ground_key_project:
  fixes h :: "('a,'s,'d,'c) shared_goal_entry"
  assumes tf: "table_formed T" and hf: "goal_entry_formed P T q h"
    and gf: "shared_pattern_formed T (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_collapsed (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_pattern_variables (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = {||}"
    and gp: "shared_pattern_project T (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = pc"
  shows "(\<exists>r'. shared_goal_project T (shared_entry_goal h) = Resolution_Call_Goal q r' d pc) \<longleftrightarrow>
    goal_ground_key (Some h) = Some (d,i)"
proof (cases "shared_entry_goal h")
  case (Shared_Call_Goal q0 r0 d0 x)
  have q0: "q0 = q" and xf: "shared_pattern_formed T x" "shared_collapsed x"
    using hf Shared_Call_Goal by (simp_all add: goal_entry_formed_def)
  have eq: "shared_pattern_project T x = pc \<longleftrightarrow> x = Shared_Ground i"
    by (subst gp[symmetric]) (rule collapsed_ground_project_eq[OF tf gf xf])
  show ?thesis using Shared_Call_Goal q0 eq by (cases x) (auto simp: goal_ground_key_def)
next
  case (Shared_Material_Goal q0 r0 M)
  then show ?thesis by (simp add: goal_ground_key_def)
qed

lemma node_ground_key_project:
  fixes hn :: "('a,'s,'d,'c) shared_node_entry"
  assumes tf: "table_formed T" and nf: "node_entry_formed T q hn"
    and gf: "shared_pattern_formed T (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_collapsed (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_pattern_variables (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = {||}"
    and gp: "shared_pattern_project T (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = pc"
  shows "resolution_node_site (shared_derivation_project T (shared_entry_node hn)) = d \<and>
      resolution_node_call (shared_derivation_project T (shared_entry_node hn)) = pc \<longleftrightarrow>
    node_ground_key (Some hn) = Some (d,i)"
proof -
  obtain x where x: "shared_derivation_call (shared_entry_node hn) = x" by blast
  have xf: "shared_pattern_formed T x" "shared_collapsed x"
    using nf x by (simp_all add: node_entry_formed_def shared_derivation_formed_def)
  have eq: "shared_pattern_project T x = pc \<longleftrightarrow> x = Shared_Ground i"
    by (subst gp[symmetric]) (rule collapsed_ground_project_eq[OF tf gf xf])
  show ?thesis using x eq by (cases x) (auto simp: node_ground_key_def shared_derivation_project_def)
qed

lemma goal_ground_key_pending:
  fixes s :: "('a,'s::linorder,'d,'c) shared_state"
  assumes s: "shared_state_formed \<kappa> P s"
    and gf: "shared_pattern_formed (shared_state_table s) (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_collapsed (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_pattern_variables (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = {||}"
    and gp: "shared_pattern_project (shared_state_table s) (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = pc"
  shows "(\<exists>r'. Resolution_Call_Goal q' r' d pc |\<in>| resolution_pending (shared_state_project s)) \<longleftrightarrow>
    goal_ground_key (RBT.lookup (shared_goals s) q') = Some (d,i)"
proof -
  have tf: "table_formed (shared_state_table s)" using shared_entries_formed(4)[OF s] .
  have k: "(\<exists>r'. shared_goal_project (shared_state_table s) (shared_entry_goal h) = Resolution_Call_Goal p2 r' d pc) \<longleftrightarrow>
      goal_ground_key (Some h) = Some (d,i)" if "RBT.lookup (shared_goals s) p2 = Some h" for p2 h
    by (rule goal_ground_key_project[OF tf shared_entries_formed(1)[OF s that] gf gp])
  have pos: "q'' = p2" if "RBT.lookup (shared_goals s) p2 = Some h"
      "shared_goal_project (shared_state_table s) (shared_entry_goal h) = Resolution_Call_Goal q'' r' d pc" for p2 h q'' r'
    using shared_goal_lookup_position[OF s that(1)] that(2) by (cases "shared_entry_goal h") simp_all
  show ?thesis
  proof
    assume "\<exists>r'. Resolution_Call_Goal q' r' d pc |\<in>| resolution_pending (shared_state_project s)"
    then obtain r' p2 h where a: "RBT.lookup (shared_goals s) p2 = Some h"
      and e: "shared_goal_project (shared_state_table s) (shared_entry_goal h) = Resolution_Call_Goal q' r' d pc"
      unfolding shared_state_project_member(1) by blast
    have "q' = p2" by (rule pos[OF a e])
    then show "goal_ground_key (RBT.lookup (shared_goals s) q') = Some (d,i)" using k[OF a] e a by auto
  next
    assume key: "goal_ground_key (RBT.lookup (shared_goals s) q') = Some (d,i)"
    then obtain h where a: "RBT.lookup (shared_goals s) q' = Some h"
      by (cases "RBT.lookup (shared_goals s) q'") (simp_all add: goal_ground_key_def)
    obtain r' where "shared_goal_project (shared_state_table s) (shared_entry_goal h) = Resolution_Call_Goal q' r' d pc"
      using k[OF a] key a by auto
    then show "\<exists>r'. Resolution_Call_Goal q' r' d pc |\<in>| resolution_pending (shared_state_project s)"
      unfolding shared_state_project_member(1) using a by blast
  qed
qed

lemma node_ground_key_nodes:
  fixes s :: "('a,'s::linorder,'d,'c) shared_state"
  assumes s: "shared_state_formed \<kappa> P s"
    and gf: "shared_pattern_formed (shared_state_table s) (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_collapsed (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern)"
      "shared_pattern_variables (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = {||}"
    and gp: "shared_pattern_project (shared_state_table s) (Shared_Ground i :: ('s,'a) resolution_variable shared_pattern) = pc"
  shows "(\<exists>nd. nd |\<in>| resolution_nodes (shared_state_project s) \<and> resolution_node_position nd = q' \<and>
      resolution_node_site nd = d \<and> resolution_node_call nd = pc) \<longleftrightarrow>
    node_ground_key (RBT.lookup (shared_nodes s) q') = Some (d,i)"
proof -
  let ?T = "shared_state_table s"
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have k: "resolution_node_site (shared_derivation_project ?T (shared_entry_node hn)) = d \<and>
      resolution_node_call (shared_derivation_project ?T (shared_entry_node hn)) = pc \<longleftrightarrow>
      node_ground_key (Some hn) = Some (d,i)" if "RBT.lookup (shared_nodes s) p2 = Some hn" for p2 hn
    by (rule node_ground_key_project[OF tf shared_entries_formed(2)[OF s that] gf gp])
  have pos: "resolution_node_position (shared_derivation_project ?T (shared_entry_node hn)) = p2"
    if "RBT.lookup (shared_nodes s) p2 = Some hn" for p2 hn
    using shared_node_lookup_position[OF s that] by (simp add: shared_derivation_project_def)
  show ?thesis
  proof
    assume "\<exists>nd. nd |\<in>| resolution_nodes (shared_state_project s) \<and> resolution_node_position nd = q' \<and>
      resolution_node_site nd = d \<and> resolution_node_call nd = pc"
    then obtain p2 hn where a: "RBT.lookup (shared_nodes s) p2 = Some hn"
      and e: "resolution_node_position (shared_derivation_project ?T (shared_entry_node hn)) = q'"
        "resolution_node_site (shared_derivation_project ?T (shared_entry_node hn)) = d"
        "resolution_node_call (shared_derivation_project ?T (shared_entry_node hn)) = pc"
      unfolding shared_state_project_member(2) by blast
    have "p2 = q'" using pos[OF a] e(1) by simp
    then show "node_ground_key (RBT.lookup (shared_nodes s) q') = Some (d,i)" using k[OF a] e(2,3) a by auto
  next
    assume key: "node_ground_key (RBT.lookup (shared_nodes s) q') = Some (d,i)"
    then obtain hn where a: "RBT.lookup (shared_nodes s) q' = Some hn"
      by (cases "RBT.lookup (shared_nodes s) q'") (simp_all add: node_ground_key_def)
    have "resolution_node_site (shared_derivation_project ?T (shared_entry_node hn)) = d \<and>
        resolution_node_call (shared_derivation_project ?T (shared_entry_node hn)) = pc" using k[OF a] key a by simp
    then show "\<exists>nd. nd |\<in>| resolution_nodes (shared_state_project s) \<and> resolution_node_position nd = q' \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = pc"
      unfolding shared_state_project_member(2) using a pos[OF a] by blast
  qed
qed

text \<open>
  A step at a position touches the references of the ground keys it changes there, of the goal and of the node, and, when
  it changes whether a goal stands there, the references of the nodes at the positions whose open count reaches or
  leaves zero: the position and the prefixes the change was carried along, read from the position upwards while the
  count's zeroness moves (@{text classes_carried}), the only nodes whose solvedness it changes. At formed states these are
  all the prefixes whose count moves between zero and nonzero (@{text classes_keys_prefix}).
\<close>

primrec classes_carried :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> nat \<Rightarrow>
    nat fset" where
  "classes_carried q s s' 0 = {||}"
| "classes_carried q s s' (Suc n) = (if (tree_count (shared_open s) (take n q) = 0) = (tree_count (shared_open s') (take n q) = 0)
    then {||} else key_refs (node_ground_key (RBT.lookup (shared_nodes s') (take n q))) |\<union>| classes_carried q s s' n)"

lemma classes_carried_member:
  assumes fl: "\<And>j. m \<le> j \<Longrightarrow> j \<le> n \<Longrightarrow>
      (tree_count (shared_open s) (take j q) = 0) \<noteq> (tree_count (shared_open s') (take j q) = 0)"
    and key: "i |\<in>| key_refs (node_ground_key (RBT.lookup (shared_nodes s') (take m q)))" and mn: "m \<le> n"
  shows "i |\<in>| classes_carried q s s' (Suc n)"
  using fl mn
proof (induction n)
  case 0
  then have m: "m = 0" by simp
  have f: "\<not> ((tree_count (shared_open s) (take 0 q) = 0) = (tree_count (shared_open s') (take 0 q) = 0))"
    using "0.prems"(1)[of 0] m by simp
  show ?case unfolding classes_carried.simps(2) if_not_P[OF f] using key m by simp
next
  case (Suc n)
  have f: "\<not> ((tree_count (shared_open s) (take (Suc n) q) = 0) = (tree_count (shared_open s') (take (Suc n) q) = 0))"
    using Suc.prems(1)[of "Suc n"] Suc.prems(2) by simp
  show ?case
  proof (cases "m = Suc n")
    case True
    then show ?thesis unfolding classes_carried.simps(2) if_not_P[OF f] using key by simp
  next
    case False
    have ih: "i |\<in>| classes_carried q s s' (Suc n)"
    proof (rule Suc.IH)
      fix j assume "m \<le> j" "j \<le> n"
      then show "(tree_count (shared_open s) (take j q) = 0) \<noteq> (tree_count (shared_open s') (take j q) = 0)"
        using Suc.prems(1)[of j] by simp
    next
      show "m \<le> n" using Suc.prems(2) False by simp
    qed
    show ?thesis unfolding classes_carried.simps(2) if_not_P[OF f] using ih by simp
  qed
qed

definition classes_keys :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> nat fset" where
  "classes_keys q s s' =
    changed_refs (goal_ground_key (RBT.lookup (shared_goals s) q)) (goal_ground_key (RBT.lookup (shared_goals s') q)) |\<union>|
    changed_refs (node_ground_key (RBT.lookup (shared_nodes s) q)) (node_ground_key (RBT.lookup (shared_nodes s') q)) |\<union>|
    (if (RBT.lookup (shared_goals s) q = None) = (RBT.lookup (shared_goals s') q = None) then {||}
     else classes_carried q s s' (Suc (length q)))"

definition classes_touched :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> 's list list" where
  "classes_touched q s s' = q # concat (map (\<lambda>i. sorted_list_of_fset (tree_bucket (shared_goal_calls s') i))
    (sorted_list_of_fset (classes_keys q s s')))"

lemma classes_touched_member:
  "p \<in> set (classes_touched q s s') \<longleftrightarrow> p = q \<or> (\<exists>i. i |\<in>| classes_keys q s s' \<and> p |\<in>| tree_bucket (shared_goal_calls s') i)"
  by (auto simp: classes_touched_def sorted_list_of_fset.rep_eq)

lemma changed_refs_intro: "k \<noteq> k' \<Longrightarrow> k = Some (d,i) \<or> k' = Some (d,i) \<Longrightarrow> i |\<in>| changed_refs k k'"
  by (auto simp: changed_refs_def key_refs_def)

lemma classes_keys_goal:
  assumes "goal_ground_key (RBT.lookup (shared_goals s) q) \<noteq> goal_ground_key (RBT.lookup (shared_goals s') q)"
    and "goal_ground_key (RBT.lookup (shared_goals s) q) = Some (d,i) \<or>
      goal_ground_key (RBT.lookup (shared_goals s') q) = Some (d,i)"
  shows "i |\<in>| classes_keys q s s'"
  using changed_refs_intro[OF assms] unfolding classes_keys_def by simp

lemma classes_keys_node:
  assumes "node_ground_key (RBT.lookup (shared_nodes s) q) \<noteq> node_ground_key (RBT.lookup (shared_nodes s') q)"
    and "node_ground_key (RBT.lookup (shared_nodes s) q) = Some (d,i) \<or>
      node_ground_key (RBT.lookup (shared_nodes s') q) = Some (d,i)"
  shows "i |\<in>| classes_keys q s s'"
  using changed_refs_intro[OF assms] unfolding classes_keys_def by simp

lemma classes_keys_prefix:
  assumes s: "shared_state_formed \<kappa> P s" and s': "shared_state_formed \<kappa> P s'"
    and pre: "take (length p) q = p"
    and pres: "(RBT.lookup (shared_goals s) q = None) \<noteq> (RBT.lookup (shared_goals s') q = None)"
    and flip: "(tree_count (shared_open s) p = 0) \<noteq> (tree_count (shared_open s') p = 0)"
    and key: "node_ground_key (RBT.lookup (shared_nodes s') p) = Some (d,i)"
  shows "i |\<in>| classes_keys q s s'"
proof -
  have lp: "length p \<le> length q" using pre by (metis length_take min.cobounded1)
  have fl: "(tree_count (shared_open s) (take j q) = 0) \<noteq> (tree_count (shared_open s') (take j q) = 0)"
    if j: "length p \<le> j" "j \<le> length q" for j
  proof -
    have sub: "take (length p) q' = p" if "take j q' = take j q" for q'
    proof -
      have "take (length p) q' = take (length p) (take j q')" using j(1) by (simp add: min_absorb1)
      also have "\<dots> = take (length p) (take j q)" using that by simp
      also have "\<dots> = p" using j(1) pre by (simp add: min_absorb1)
      finally show ?thesis .
    qed
    have lj: "length (take j q) = j" using j(2) by simp
    note z = shared_open_zero[OF s, of p] shared_open_zero[OF s', of p]
      shared_open_zero[OF s, of "take j q", unfolded lj] shared_open_zero[OF s', of "take j q", unfolded lj]
    show ?thesis
    proof (cases "RBT.lookup (shared_goals s) q = None")
      case True
      have in': "RBT.lookup (shared_goals s') q \<noteq> None" using pres True by simp
      have no: "\<not> (\<exists>q'. RBT.lookup (shared_goals s) q' \<noteq> None \<and> take (length p) q' = p)"
        using flip z(1) z(2) in' pre by blast
      have a: "\<not> (\<exists>q'. RBT.lookup (shared_goals s) q' \<noteq> None \<and> take j q' = take j q)" using no sub by blast
      have b: "\<exists>q'. RBT.lookup (shared_goals s') q' \<noteq> None \<and> take j q' = take j q" using in' by blast
      show ?thesis using a b z(3) z(4) by simp
    next
      case False
      have no: "\<not> (\<exists>q'. RBT.lookup (shared_goals s') q' \<noteq> None \<and> take (length p) q' = p)"
        using flip z(1) z(2) False pre by blast
      have a: "\<not> (\<exists>q'. RBT.lookup (shared_goals s') q' \<noteq> None \<and> take j q' = take j q)" using no sub by blast
      have b: "\<exists>q'. RBT.lookup (shared_goals s) q' \<noteq> None \<and> take j q' = take j q" using False by blast
      show ?thesis using a b z(3) z(4) by simp
    qed
  qed
  have mem: "i |\<in>| classes_carried q s s' (Suc (length q))"
  proof (rule classes_carried_member[OF fl _ lp])
    show "i |\<in>| key_refs (node_ground_key (RBT.lookup (shared_nodes s') (take (length p) q)))"
      unfolding pre key key_refs_def by simp
  qed
  show ?thesis unfolding classes_keys_def if_not_P[OF pres] using mem by simp
qed

lemmas classes_keys_intro = classes_keys_goal classes_keys_node classes_keys_prefix

text \<open>
  A goal at a position the step does not touch keeps its tests: its call is ground and collapsed, so it is one reference.
  The tests read the nodes and the pending goals making that call by their positions, and the solvedness of those nodes
  (@{thm [source] goal_tests_frame}); at a position the ground key of a formed entry says whether it makes the call
  (@{thm [source] goal_ground_key_pending}, @{thm [source] node_ground_key_nodes}). A goal or a node making the call at the
  step's position changes its key, and a node making it at a prefix of the step's position changes its solvedness, only
  where the reference is among the keys the touched positions include (@{thm [source] classes_keys_intro}).
\<close>

lemma classes_frame:
  assumes r: "search_formed \<kappa> P r" and r': "search_formed \<kappa> P r'"
    and ext: "table_extends (search_table r) (search_table r')"
    and goals: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals (search_state r')) p = RBT.lookup (shared_goals (search_state r)) p"
    and nodes: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state r')) p = RBT.lookup (shared_nodes (search_state r)) p"
    and at: "RBT.lookup (shared_goals (search_state r)) p = Some h"
    and out: "p \<notin> set (classes_touched q (search_state r) (search_state r'))"
  shows "kept_candidate (search_table r') h \<longleftrightarrow> kept_candidate (search_table r) h"
    and "kept_settled (search_table r') (search_project r') h \<longleftrightarrow> kept_settled (search_table r) (search_project r) h"
    and "kept_single (search_table r') (search_project r') h \<longleftrightarrow> kept_single (search_table r) (search_project r) h"
proof -
  let ?s = "search_state r" and ?s' = "search_state r'" and ?T = "search_table r" and ?T' = "search_table r'"
  let ?st = "search_project r" and ?st' = "search_project r'"
  have s: "shared_state_formed \<kappa> P ?s" and s': "shared_state_formed \<kappa> P ?s'" using search_formedD(1) r r' by blast+
  have tf: "table_formed ?T" and tf': "table_formed ?T'" using shared_entries_formed(4) s s' by blast+
  have pq: "p \<noteq> q" using out by (simp add: classes_touched_member)
  have at': "RBT.lookup (shared_goals ?s') p = Some h" using goals[OF pq] at by simp
  have hf: "goal_entry_formed P ?T p h" by (rule shared_entries_formed(1)[OF s at])
  have proj: "shared_goal_project ?T' (shared_entry_goal h) = shared_goal_project ?T (shared_entry_goal h)"
    using goal_entry_extends[OF tf hf ext] by simp
  let ?g = "shared_goal_project ?T (shared_entry_goal h)"
  have tests: "(finite_pruned ?st' ?g \<longleftrightarrow> finite_pruned ?st ?g) \<and> (finite_reusable ?st' ?g \<longleftrightarrow> finite_reusable ?st ?g) \<and>
      (finite_goal_waits ?st' ?g \<longleftrightarrow> finite_goal_waits ?st ?g)"
  proof (cases ?g)
    case (Resolution_Material_Goal q0 rr M)
    then show ?thesis by (simp add: finite_pruned_def finite_reusable_def finite_goal_waits_def)
  next
    case (Resolution_Call_Goal q0 rr d pc)
    show ?thesis
    proof (cases "finite_pattern_variables pc = {||}")
      case False
      then show ?thesis using Resolution_Call_Goal by (simp add: finite_pruned_def finite_reusable_def finite_goal_waits_def)
    next
      case True
      obtain gp where hg: "shared_entry_goal h = Shared_Call_Goal q0 rr d gp" and gpp: "shared_pattern_project ?T gp = pc"
        using Resolution_Call_Goal by (cases "shared_entry_goal h") auto
      have gpf: "shared_pattern_formed ?T gp" "shared_collapsed gp" using hf hg by (simp_all add: goal_entry_formed_def)
      have gv: "shared_pattern_variables gp = {||}" using goal_entry_variables[OF hf] hg gpp True by simp
      then obtain i where gi: "gp = Shared_Ground i" using shared_collapsed_ground[OF gpf(2)] by blast
      have "shared_recorded_at ?s' p" using s' by (simp add: shared_state_formed_def)
      then have rec: "p |\<in>| tree_bucket (shared_goal_calls ?s') i" using at' hg gi by (simp add: shared_recorded_at_def)
      have ik: "i |\<notin>| classes_keys q ?s ?s'" using out rec by (auto simp: classes_touched_member)
      have gf: "shared_pattern_formed ?T (Shared_Ground i)" "shared_collapsed (Shared_Ground i)"
          "shared_pattern_variables (Shared_Ground i) = {||}"
        and gr: "shared_pattern_project ?T (Shared_Ground i) = pc"
        using gpf gv gpp gi by simp_all
      have gf': "shared_pattern_formed ?T' (Shared_Ground i)" by (rule shared_pattern_extends(1)[OF tf gf(1) ext])
      have gr': "shared_pattern_project ?T' (Shared_Ground i) = pc"
        using shared_pattern_extends(2)[OF tf gf(1) ext] gr by (rule trans)
      note Gk = goal_ground_key_pending[OF s gf gr] and Gk' = goal_ground_key_pending[OF s' gf' gf(2,3) gr']
      note Nk = node_ground_key_nodes[OF s gf gr] and Nk' = node_ground_key_nodes[OF s' gf' gf(2,3) gr']
      have gq: "goal_ground_key (RBT.lookup (shared_goals ?s') q) = Some (d,i) \<longleftrightarrow>
          goal_ground_key (RBT.lookup (shared_goals ?s) q) = Some (d,i)"
      proof (cases "goal_ground_key (RBT.lookup (shared_goals ?s) q) = goal_ground_key (RBT.lookup (shared_goals ?s') q)")
        case True
        then show ?thesis by simp
      next
        case False
        have "goal_ground_key (RBT.lookup (shared_goals ?s) q) \<noteq> Some (d,i) \<and>
            goal_ground_key (RBT.lookup (shared_goals ?s') q) \<noteq> Some (d,i)"
          using classes_keys_goal[OF False] ik by blast
        then show ?thesis by simp
      qed
      have nq: "node_ground_key (RBT.lookup (shared_nodes ?s') q) = Some (d,i) \<longleftrightarrow>
          node_ground_key (RBT.lookup (shared_nodes ?s) q) = Some (d,i)"
      proof (cases "node_ground_key (RBT.lookup (shared_nodes ?s) q) = node_ground_key (RBT.lookup (shared_nodes ?s') q)")
        case True
        then show ?thesis by simp
      next
        case False
        have "node_ground_key (RBT.lookup (shared_nodes ?s) q) \<noteq> Some (d,i) \<and>
            node_ground_key (RBT.lookup (shared_nodes ?s') q) \<noteq> Some (d,i)"
          using classes_keys_node[OF False] ik by blast
        then show ?thesis by simp
      qed
      have G: "(\<exists>r'. Resolution_Call_Goal q' r' d pc |\<in>| resolution_pending ?st') \<longleftrightarrow>
          (\<exists>r'. Resolution_Call_Goal q' r' d pc |\<in>| resolution_pending ?st)" for q'
        unfolding Gk Gk' using gq goals[of q'] by (cases "q' = q") auto
      have N: "(\<exists>nd. nd |\<in>| resolution_nodes ?st' \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
            resolution_node_call nd = pc) \<longleftrightarrow>
          (\<exists>nd. nd |\<in>| resolution_nodes ?st \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
            resolution_node_call nd = pc)" for q'
        unfolding Nk Nk' using nq nodes[of q'] by (cases "q' = q") auto
      have S: "fBex (resolution_pending ?st') (\<lambda>g. take (length q') (resolution_goal_position g) = q') \<longleftrightarrow>
          fBex (resolution_pending ?st) (\<lambda>g. take (length q') (resolution_goal_position g) = q')"
        if n: "\<exists>nd. nd |\<in>| resolution_nodes ?st \<and> resolution_node_position nd = q' \<and> resolution_node_site nd = d \<and>
          resolution_node_call nd = pc" for q'
      proof -
        have k0: "node_ground_key (RBT.lookup (shared_nodes ?s) q') = Some (d,i)" using n Nk by blast
        have k: "node_ground_key (RBT.lookup (shared_nodes ?s') q') = Some (d,i)"
          using k0 nq nodes[of q'] by (cases "q' = q") auto
        have u: "(\<exists>p2. RBT.lookup (shared_goals ?s') p2 \<noteq> None \<and> take (length q') p2 = q') \<longleftrightarrow>
            (\<exists>p2. RBT.lookup (shared_goals ?s) p2 \<noteq> None \<and> take (length q') p2 = q')"
        proof (cases "take (length q') q = q' \<and>
            (RBT.lookup (shared_goals ?s) q = None) \<noteq> (RBT.lookup (shared_goals ?s') q = None)")
          case True
          have "(tree_count (shared_open ?s) q' = 0) = (tree_count (shared_open ?s') q' = 0)"
            using classes_keys_prefix[OF s s' conjunct1[OF True] conjunct2[OF True] _ k] ik by blast
          note c = this
          have flipped: "\<And>c c' A A'. c = c' \<Longrightarrow> c = (\<not> A) \<Longrightarrow> c' = (\<not> A') \<Longrightarrow> A' = A" by blast
          show ?thesis by (rule flipped[OF c shared_open_zero[OF s] shared_open_zero[OF s']])
        next
          case False
          have "RBT.lookup (shared_goals ?s') p2 \<noteq> None \<longleftrightarrow> RBT.lookup (shared_goals ?s) p2 \<noteq> None"
            if "take (length q') p2 = q'" for p2
            using False goals[of p2] that by (cases "p2 = q") auto
          then show ?thesis by blast
        qed
        show ?thesis unfolding shared_pending_under[OF s] shared_pending_under[OF s'] by (rule u)
      qed
      have fr: "(finite_pruned ?st' (Resolution_Call_Goal q0 rr d pc) \<longleftrightarrow> finite_pruned ?st (Resolution_Call_Goal q0 rr d pc)) \<and>
          (finite_reusable ?st' (Resolution_Call_Goal q0 rr d pc) \<longleftrightarrow> finite_reusable ?st (Resolution_Call_Goal q0 rr d pc)) \<and>
          (finite_goal_waits ?st' (Resolution_Call_Goal q0 rr d pc) \<longleftrightarrow> finite_goal_waits ?st (Resolution_Call_Goal q0 rr d pc))"
        by (intro conjI goal_tests_frame[OF N S G])
      show ?thesis unfolding Resolution_Call_Goal by (rule fr)
    qed
  qed
  show "kept_candidate ?T' h \<longleftrightarrow> kept_candidate ?T h" using proj by (simp add: kept_candidate_def)
  show "kept_settled ?T' ?st' h \<longleftrightarrow> kept_settled ?T ?st h"
    using proj tests by (simp add: kept_settled_def kept_candidate_def goal_settled_def)
  show "kept_single ?T' ?st' h \<longleftrightarrow> kept_single ?T ?st h"
    using proj tests by (simp add: kept_single_def kept_candidate_def goal_single_def)
qed

lemma classes_step:
  assumes r: "search_formed \<kappa> P r" and r': "search_formed \<kappa> P r'"
    and ext: "table_extends (search_table r) (search_table r')"
    and goals: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals (search_state r')) p = RBT.lookup (shared_goals (search_state r)) p"
    and nodes: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes (search_state r')) p = RBT.lookup (shared_nodes (search_state r)) p"
    and K: "classes_formed (search_state r) K"
  shows "classes_formed (search_state r')
    (classes_update (classes_touched q (search_state r) (search_state r')) (search_state r') K)"
proof (rule classes_update_formed[OF r'])
  fix p assume out: "p \<notin> set (classes_touched q (search_state r) (search_state r'))"
  have pq: "p \<noteq> q" using out by (simp add: classes_touched_member)
  show "RBT.lookup (class_candidates K) p = class_value (kept_candidate (search_table r')) (shared_goals (search_state r')) p \<and>
      RBT.lookup (class_settled K) p =
        class_value (kept_settled (search_table r') (search_project r')) (shared_goals (search_state r')) p \<and>
      RBT.lookup (class_single K) p =
        class_value (kept_single (search_table r') (search_project r')) (shared_goals (search_state r')) p"
  proof (cases "RBT.lookup (shared_goals (search_state r)) p")
    case None
    then show ?thesis using K goals[OF pq] unfolding classes_formed_def by (simp add: class_value_def)
  next
    case (Some h)
    note f = classes_frame[OF r r' ext goals nodes Some out]
    show ?thesis using K goals[OF pq] Some f unfolding classes_formed_def by (simp add: class_value_def)
  qed
qed

text \<open>A step that extends the table and keeps the goals, the pending goals and the nodes keeps the classes formed.\<close>

lemma classes_formed_extends:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and ext: "table_extends (search_table r) (search_table r')"
    and g: "shared_goals (search_state r') = shared_goals (search_state r)"
    and pd: "resolution_pending (search_project r') = resolution_pending (search_project r)"
    and nd: "resolution_nodes (search_project r') = resolution_nodes (search_project r)"
    and c: "search_classes r' = search_classes r"
  shows "search_classes_formed r'"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF r] .
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have t: "goal_settled n (search_project r') x = goal_settled n (search_project r) x"
    "goal_single n (search_project r') x = goal_single n (search_project r) x" for n x
    by (cases x; simp add: goal_settled_def goal_single_def finite_pruned_def finite_reusable_def finite_goal_waits_def
        finite_solved_node_def pd nd)+
  have v: "kept_candidate (search_table r') h = kept_candidate (search_table r) h \<and>
      kept_settled (search_table r') (search_project r') h = kept_settled (search_table r) (search_project r) h \<and>
      kept_single (search_table r') (search_project r') h = kept_single (search_table r) (search_project r) h"
    if "RBT.lookup (shared_goals (search_state r)) p = Some h" for p h
    using goal_entry_extends[OF tf shared_entries_formed(1)[OF s that] ext] t
    by (simp add: kept_candidate_def kept_settled_def kept_single_def)
  have cv: "class_value (kept_candidate (search_table r')) (shared_goals (search_state r)) p =
        class_value (kept_candidate (search_table r)) (shared_goals (search_state r)) p \<and>
      class_value (kept_settled (search_table r') (search_project r')) (shared_goals (search_state r)) p =
        class_value (kept_settled (search_table r) (search_project r)) (shared_goals (search_state r)) p \<and>
      class_value (kept_single (search_table r') (search_project r')) (shared_goals (search_state r)) p =
        class_value (kept_single (search_table r) (search_project r)) (shared_goals (search_state r)) p" for p
  proof (cases "RBT.lookup (shared_goals (search_state r)) p")
    case None
    then show ?thesis by (simp add: class_value_def)
  next
    case (Some h)
    then show ?thesis using v[OF Some] by (simp add: class_value_def)
  qed
  show ?thesis using K g c cv unfolding classes_formed_def by simp
qed

section \<open>Steps over the shared search state\<close>

text \<open>
  Every step changes the goal at one position through (a)'s operations, and moves that position between the buckets
  of the registered positions of the goal it leaves and of the goal it enters, as F2b2 (c) moves it. The table only
  extends, so every kept value stays the value at its node.
\<close>

text \<open>
  The class of the goals the table closes is written where a goal changes: at the step's own position (task 876).
\<close>

definition closed_put :: "'s list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> (nat,'d fset) rbt \<Rightarrow>
    ('s list, ('a,'s,'d,'c) shared_goal_entry) rbt \<Rightarrow> ('s list, ('a,'s,'d,'c) shared_goal_entry) rbt" where
  "closed_put q s E t = (case RBT.lookup (shared_goals s) q of None \<Rightarrow> class_drop q t
    | Some h \<Rightarrow> class_put (shared_goal_closes E (shared_entry_goal h)) q h t)"

lemma closed_put_lookup:
  "RBT.lookup (closed_put q s E t) p = (if p = q then (case RBT.lookup (shared_goals s) q of None \<Rightarrow> None
    | Some h \<Rightarrow> if shared_goal_closes E (shared_entry_goal h) then Some h else None) else RBT.lookup t p)"
  by (simp add: closed_put_def split: option.split)

lemma closed_put_fold:
  "RBT.lookup (fold (\<lambda>p t. closed_put p s E t) ps t0) p = (if p \<in> set ps then (case RBT.lookup (shared_goals s) p of
      None \<Rightarrow> None | Some h \<Rightarrow> if shared_goal_closes E (shared_entry_goal h) then Some h else None) else RBT.lookup t0 p)"
  by (induction ps arbitrary: t0) (auto simp: closed_put_lookup)

definition search_update :: "'s list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_update q s' r = r\<lparr>search_state := s', search_registered := tree_move q
    (option_registered (RBT.lookup (shared_goals (search_state r)) q)) (option_registered (RBT.lookup (shared_goals s') q))
    (search_registered r), search_classes := classes_update (classes_touched q (search_state r) s') s' (search_classes r),
    search_closed := closed_put q s' (search_index r) (search_closed r)\<rparr>"

lemma search_closing_update:
  assumes r: "search_formed \<kappa> P r"
    and ext: "table_extends (search_table r) (shared_state_table s')"
    and same: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals (search_state r)) p"
  shows "search_closing_formed (search_update q s' r)"
proof -
  have c: "search_closing_formed r" by (rule search_formed_closing[OF r])
  have I: "calls_indexed (shared_state_table s') (search_index r) (set (search_calls r))"
    by (rule calls_indexed_extends[OF _ ext]) (use c in \<open>simp add: search_closing_formed_def\<close>)
  have cl: "RBT.lookup (search_closed r) p = (case RBT.lookup (shared_goals (search_state r)) p of None \<Rightarrow> None
      | Some h \<Rightarrow> if search_closes r h then Some h else None)" for p
    using c by (simp add: search_closing_formed_def)
  show ?thesis
    unfolding search_closing_formed_def
  proof (intro conjI allI)
    show "calls_indexed (search_table (search_update q s' r)) (search_index (search_update q s' r))
        (set (search_calls (search_update q s' r)))" using I by (simp add: search_update_def)
    fix p
    show "RBT.lookup (search_closed (search_update q s' r)) p =
        (case RBT.lookup (shared_goals (search_state (search_update q s' r))) p of None \<Rightarrow> None
         | Some h \<Rightarrow> if search_closes (search_update q s' r) h then Some h else None)"
      using cl[of p] same[of p] by (simp add: search_update_def closed_put_lookup search_closes_def split: option.split)
  qed
qed

lemma search_closing_same:
  assumes c: "search_closing_formed r" and ext: "table_extends (search_table r) (search_table r')"
    and f: "search_calls r' = search_calls r" "search_index r' = search_index r" "search_closed r' = search_closed r"
    and g: "\<And>p. RBT.lookup (shared_goals (search_state r')) p = RBT.lookup (shared_goals (search_state r)) p"
  shows "search_closing_formed r'"
proof -
  have I: "calls_indexed (search_table r) (search_index r) (set (search_calls r))"
    and C: "\<And>p. RBT.lookup (search_closed r) p = (case RBT.lookup (shared_goals (search_state r)) p of None \<Rightarrow> None
      | Some h \<Rightarrow> if search_closes r h then Some h else None)"
    using c by (simp_all add: search_closing_formed_def)
  have e: "search_closes r' = search_closes r" by (simp add: fun_eq_iff search_closes_def f)
  show ?thesis unfolding search_closing_formed_def f g e using calls_indexed_extends[OF I ext] C by simp
qed

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
  proof -
    have "search_values_formed \<kappa> P (search_update q s' r) =
        search_values_formed \<kappa> P (r\<lparr>search_state := s', search_registered := search_registered r\<rparr>)"
      by (simp add: search_values_formed_def search_update_def)
    then show ?thesis using search_values_extends[OF v tf ext, where t = "search_registered r"] by simp
  qed
  have cf: "search_closing_formed (search_update q s' r)" by (rule search_closing_update[OF r ext same])
  show ?thesis using s' rf vf cf by (simp add: search_formed_def search_update_def)
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
  "search_put_node q hn r = (let s' = shared_put_node q hn (search_state r) in
    r\<lparr>search_state := s', search_classes := classes_update (classes_touched q (search_state r) s') s' (search_classes r)\<rparr>)"

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
    using reg g by (simp add: search_registered_formed_def search_put_node_def Let_def)
  have tb: "search_table (search_put_node q hn r) = search_table r" using t by (simp add: search_put_node_def Let_def)
  have vv: "search_values (search_put_node q hn r) = search_values r" by (simp add: search_put_node_def Let_def)
  have vf: "search_values_formed \<kappa> P (search_put_node q hn r)" using v unfolding search_values_formed_def tb vv .
  have cf: "search_closing_formed (search_put_node q hn r)"
    by (rule search_closing_same[OF search_formed_closing[OF r]]) (simp_all add: tb t g search_put_node_def Let_def)
  show "search_formed \<kappa> P (search_put_node q hn r)" using s' rf vf cf by (simp add: search_formed_def search_put_node_def Let_def)
  show "search_state (search_put_node q hn r) = shared_put_node q hn (search_state r)" by (simp add: search_put_node_def Let_def)
qed

subsection \<open>The classes kept by the steps\<close>

text \<open>
  Each step that changes the goal or the node at one position updates the classes at the goals it touches
  (@{thm [source] classes_step}), and keeps them formed whenever it leaves the search formed.
\<close>

lemma search_update_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and r': "search_formed \<kappa> P (search_update q s' r)"
    and ext: "table_extends (search_table r) (shared_state_table s')"
    and goals: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals (search_state r)) p"
    and nodes: "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes s') p = RBT.lookup (shared_nodes (search_state r)) p"
  shows "search_classes_formed (search_update q s' r)"
proof -
  have "classes_formed (search_state (search_update q s' r)) (classes_update
      (classes_touched q (search_state r) (search_state (search_update q s' r))) (search_state (search_update q s' r))
      (search_classes r))"
    by (rule classes_step[OF r r' _ _ _ K]) (use ext goals nodes in simp_all)
  then show ?thesis by (simp add: search_update_def)
qed

lemma search_put_goal_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and r': "search_formed \<kappa> P (search_put_goal q h r)"
  shows "search_classes_formed (search_put_goal q h r)"
  unfolding search_put_goal_def
  by (rule search_update_classes[OF r K r'[unfolded search_put_goal_def]]) (simp_all add: shared_put_goal_def)

lemma search_remove_goal_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
  shows "search_classes_formed (search_remove_goal q r)"
  unfolding search_remove_goal_def
  by (rule search_update_classes[OF r K search_remove_goal(1)[OF r at, unfolded search_remove_goal_def]])
    (simp_all add: shared_remove_goal_def)

lemma search_put_node_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and r': "search_formed \<kappa> P (search_put_node q hn r)"
  shows "search_classes_formed (search_put_node q hn r)"
proof -
  have e: "search_state (search_put_node q hn r) = shared_put_node q hn (search_state r)"
    by (simp add: search_put_node_def Let_def)
  have "classes_formed (search_state (search_put_node q hn r)) (classes_update (classes_touched q (search_state r)
      (search_state (search_put_node q hn r))) (search_state (search_put_node q hn r)) (search_classes r))"
    by (rule classes_step[OF r r' _ _ _ K]) (simp_all add: e shared_put_node_def)
  then show ?thesis by (simp add: search_put_node_def Let_def)
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

lemma search_substitute_at_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and r': "search_formed \<kappa> P (search_substitute_at P \<sigma> D q r)"
    and ext: "table_extends (search_table r) (search_table (search_substitute_at P \<sigma> D q r))"
  shows "search_classes_formed (search_substitute_at P \<sigma> D q r)"
  unfolding search_substitute_at_def
  by (rule search_update_classes[OF r K r'[unfolded search_substitute_at_def]])
    (use ext in \<open>simp_all add: search_substitute_at_def shared_substitute_at_def shared_reshare_def Let_def\<close>)

lemma search_substitute_fold_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r" and tf0: "table_formed T0"
    and ext0: "table_extends T0 (search_table r)"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_classes_formed (fold (search_substitute_at P \<sigma> D) qs r)"
  using r K ext0
proof (induction qs arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  let ?r1 = "search_substitute_at P \<sigma> D q r"
  have tfr: "table_formed (search_table r)" using shared_entries_formed(4)[OF search_formedD(1)[OF Cons.prems(1)]] .
  have \<sigma>fr: "shared_pattern_formed (search_table r) (\<sigma> a)" for a using shared_pattern_extends(1)[OF tf0 \<sigma>f Cons.prems(3)] .
  have f0: "search_formed \<kappa> P ?r1 \<and> table_extends T0 (search_table ?r1)"
    using search_substitute_fold[OF Cons.prems(1) tf0 Cons.prems(3) \<sigma>f \<sigma>c out, where qs = "[q]"] by simp
  have f1: "table_extends (search_table r) (search_table ?r1)"
    using search_substitute_fold[OF Cons.prems(1) tfr table_extends_refl \<sigma>fr \<sigma>c out, where qs = "[q]"] by simp
  have k1: "search_classes_formed ?r1"
    by (rule search_substitute_at_classes[OF Cons.prems(1) Cons.prems(2) conjunct1[OF f0] f1])
  show ?case using Cons.IH[OF conjunct1[OF f0] k1 conjunct2[OF f0]] by simp
qed

lemma search_substitute_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and \<sigma>f: "\<And>a. shared_pattern_formed (search_table r) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "search_classes_formed (search_substitute P \<sigma> D r)"
  unfolding search_substitute_def
  by (rule search_substitute_fold_classes[OF r K _ table_extends_refl \<sigma>f \<sigma>c out])
    (rule shared_entries_formed(4)[OF search_formedD(1)[OF r]])

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
  have cf: "search_closing_formed (search_reshare G r)"
    by (rule search_closing_same[OF search_formed_closing[OF r]])
      (use k(2) tb in \<open>simp_all add: search_reshare_def shared_reshare_def\<close>)
  show "search_formed \<kappa> P (search_reshare G r)"
    using e(1) rf vf cf by (simp add: search_formed_def search_reshare_def)
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

text \<open>
  The substitution's value at a bound variable is its pattern read against the shared state, a walk of the bound
  pattern. It is tabulated once per bound variable: the graph of the values over the bound variables, read at each
  occurrence by the variable's fibre, which is the value itself (@{text fset_graph_lookup}), so no statement changes.
\<close>

lemma search_reshare_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_classes_formed (search_reshare G r)"
  by (rule classes_formed_extends[OF r K]) (use search_reshare[OF r, where G = G] in \<open>simp_all add: search_reshare_def\<close>)

lemma search_substitute_plain_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<tau> a = Finite_Variable a"
  shows "search_classes_formed (search_substitute_plain P \<tau> D r)"
proof -
  let ?r1 = "search_reshare (plain_grounds \<tau> D) r"
  note r1 = search_reshare[OF r, where G = "plain_grounds \<tau> D"]
  let ?x = "shared_sharing (search_state ?r1)"
  have xf: "share_state_formed ?x" using shared_entries_formed(3)[OF search_formedD(1)[OF r1(1)]] .
  have rep: "keyed_state_represents ?x (search_table ?r1)" and tf1: "table_formed (search_table ?r1)"
    using share_state_formed_table[OF xf] by simp_all
  have held: "table_holds (search_table ?r1) t" if "t |\<in>| pattern_grounds (\<tau> a)" for a t
  proof (cases "a |\<in>| D")
    case True
    then have "t |\<in>| plain_grounds \<tau> D" using that by (auto simp: plain_grounds_def ffUnion.rep_eq fimage.rep_eq)
    then show ?thesis by (rule r1(4))
  next
    case False
    then show ?thesis using that out by simp
  qed
  have ex: "shared_pattern_formed (search_table ?r1) (keyed_pattern_at ?x (\<tau> a)) \<and>
      shared_collapsed (keyed_pattern_at ?x (\<tau> a))" for a
  proof -
    have "\<And>t. t |\<in>| pattern_grounds (\<tau> a) \<Longrightarrow> table_holds (search_table ?r1) t" by (rule held)
    then show ?thesis using keyed_pattern_at_exact[OF rep tf1, of "\<tau> a"] by blast
  qed
  have k1: "search_classes_formed ?r1" by (rule search_reshare_classes[OF r K])
  show ?thesis unfolding search_substitute_plain_def Let_def
    by (rule search_substitute_classes[OF r1(1) k1]) (use ex out in auto)
qed

lemma fset_graph_lookup:
  "(case finite_singleton_option (fimage snd (ffilter (\<lambda>z. fst z = a) (fimage (\<lambda>a. (a, g a)) D))) of
      Some p \<Rightarrow> p | None \<Rightarrow> g a) = g a"
proof (cases "a |\<in>| D")
  case True
  then have "fimage snd (ffilter (\<lambda>z. fst z = a) (fimage (\<lambda>a. (a, g a)) D)) = {|g a|}"
    by (auto simp: fset_eq_iff fimage_iff intro!: image_eqI[where x = "(a, g a)"])
  then show ?thesis by simp
next
  case False
  then have e: "fimage snd (ffilter (\<lambda>z. fst z = a) (fimage (\<lambda>a. (a, g a)) D)) = {||}"
    by (auto simp: fset_eq_iff fimage_iff)
  have "finite_singleton_option (fimage snd (ffilter (\<lambda>z. fst z = a) (fimage (\<lambda>a. (a, g a)) D))) = None"
    unfolding e by (metis finite_singleton_option_some finsert_not_fempty option.exhaust)
  then show ?thesis by simp
qed

lemma search_substitute_plain_code [code]:
  "search_substitute_plain P \<tau> D r = (let r1 = search_reshare (plain_grounds \<tau> D) r;
      x = shared_sharing (search_state r1); tab = fimage (\<lambda>a. (a, keyed_pattern_at x (\<tau> a))) D in
    search_substitute P (\<lambda>a. case finite_singleton_option (fimage snd (ffilter (\<lambda>z. fst z = a) tab)) of
      Some p \<Rightarrow> p | None \<Rightarrow> keyed_pattern_at x (\<tau> a)) D r1)"
proof -
  let ?x = "shared_sharing (search_state (search_reshare (plain_grounds \<tau> D) r))"
  have tab: "(\<lambda>a. case finite_singleton_option (fimage snd (ffilter (\<lambda>z. fst z = a)
      (fimage (\<lambda>a. (a, keyed_pattern_at ?x (\<tau> a))) D))) of Some p \<Rightarrow> p | None \<Rightarrow> keyed_pattern_at ?x (\<tau> a)) =
    (\<lambda>a. keyed_pattern_at ?x (\<tau> a))"
    by (rule ext, rule fset_graph_lookup)
  show ?thesis unfolding search_substitute_plain_def Let_def by (simp only: tab)
qed

subsection \<open>A shared unifier substituted, its bindings collapsed\<close>

text \<open>
  A unifier computed over the shared state binds variables to shared patterns, references into the table among them.
  Its bindings are collapsed through the keyed constructor, a node whose parts became ground made a reference, and
  substituted as they are: no binding is decoded, shared again or walked below a reference.
\<close>

lemma shared_bindings_extends:
  assumes tf: "table_formed T" and ext: "table_extends T T'" and s: "shared_bindings_formed T s"
  shows "shared_bindings_formed T' s \<and> shared_bindings_project T' s = shared_bindings_project T s"
  using s
proof (induction s)
  case (Cons z s)
  then show ?case by (cases z) (simp add: shared_pattern_extends[OF tf _ ext])
qed simp

fun keyed_collapse_bindings ::
    "('a \<times> 'a shared_pattern) list \<Rightarrow> share_state \<Rightarrow> ('a \<times> 'a shared_pattern) list \<times> share_state" where
  "keyed_collapse_bindings [] x = ([], x)"
| "keyed_collapse_bindings ((a,p) # s) x = (case keyed_share_collapse p x of (p', x1) \<Rightarrow>
    (case keyed_collapse_bindings s x1 of (s', x2) \<Rightarrow> ((a,p') # s', x2)))"

lemma keyed_collapse_bindings:
  "share_state_formed x \<Longrightarrow> shared_bindings_formed (share_state_table x) s \<Longrightarrow>
    share_state_formed (snd (keyed_collapse_bindings s x)) \<and>
    table_extends (share_state_table x) (share_state_table (snd (keyed_collapse_bindings s x))) \<and>
    shared_bindings_formed (share_state_table (snd (keyed_collapse_bindings s x))) (fst (keyed_collapse_bindings s x)) \<and>
    shared_bindings_project (share_state_table (snd (keyed_collapse_bindings s x))) (fst (keyed_collapse_bindings s x)) =
      shared_bindings_project (share_state_table x) s \<and>
    (\<forall>z\<in>set (fst (keyed_collapse_bindings s x)). shared_collapsed (snd z))"
proof (induction s arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons z s)
  obtain a p where z: "z = (a,p)" by (cases z)
  obtain p' x1 where k1: "keyed_share_collapse p x = (p', x1)" by (cases "keyed_share_collapse p x")
  obtain s' x2 where k2: "keyed_collapse_bindings s x1 = (s', x2)" by (cases "keyed_collapse_bindings s x1")
  have fp: "shared_pattern_formed (share_state_table x) p" and fs: "shared_bindings_formed (share_state_table x) s"
    using Cons.prems(2) z by simp_all
  note c = share_state_collapse[OF Cons.prems(1) fp]
  have x1: "share_state_formed x1" and fp': "shared_pattern_formed (share_state_table x1) p'"
    and pp': "shared_pattern_project (share_state_table x1) p' = shared_pattern_project (share_state_table x) p"
    and cp': "shared_collapsed p'" and e1: "table_extends (share_state_table x) (share_state_table x1)"
    using c k1 by simp_all
  have tf: "table_formed (share_state_table x)" using share_state_formed_table(1)[OF Cons.prems(1)] .
  have tf1: "table_formed (share_state_table x1)" using share_state_formed_table(1)[OF x1] .
  note b1 = shared_bindings_extends[OF tf e1 fs]
  note IH = Cons.IH[OF x1 conjunct1[OF b1]]
  have x2: "share_state_formed x2" and e2: "table_extends (share_state_table x1) (share_state_table x2)"
    and fs': "shared_bindings_formed (share_state_table x2) s'"
    and ps': "shared_bindings_project (share_state_table x2) s' = shared_bindings_project (share_state_table x1) s"
    and cs': "\<forall>z\<in>set s'. shared_collapsed (snd z)" using IH k2 by simp_all
  note p2 = shared_pattern_extends[OF tf1 fp' e2]
  show ?case using x2 table_extends_trans[OF e1 e2] fs' ps' cs' p2 pp' cp' b1 by (simp add: z k1 k2)
qed

definition search_share :: "share_state \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_share x r = r\<lparr>search_state := shared_reshare x (search_state r)\<rparr>"

lemma search_share:
  assumes r: "search_formed \<kappa> P r" and x: "share_state_formed x"
    and ext: "table_extends (search_table r) (share_state_table x)"
  shows "search_formed \<kappa> P (search_share x r)" and "search_project (search_share x r) = search_project r"
    and "search_table (search_share x r) = share_state_table x"
    and "shared_goals (search_state (search_share x r)) = shared_goals (search_state r)"
    and "shared_nodes (search_state (search_share x r)) = shared_nodes (search_state r)"
proof -
  have s: "shared_state_formed \<kappa> P (search_state r)" and reg: "search_registered_formed r" and v: "search_values_formed \<kappa> P r"
    using search_formedD[OF r] by simp_all
  note e = shared_reshare[OF s x ext]
  show "search_table (search_share x r) = share_state_table x" by (simp add: search_share_def shared_reshare_def)
  show "shared_goals (search_state (search_share x r)) = shared_goals (search_state r)"
    "shared_nodes (search_state (search_share x r)) = shared_nodes (search_state r)"
    by (simp_all add: search_share_def shared_reshare_def)
  show "search_project (search_share x r) = search_project r" using e(2) by (simp add: search_share_def)
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have vf: "search_values_formed \<kappa> P (r\<lparr>search_state := shared_reshare x (search_state r), search_registered := search_registered r\<rparr>)"
    by (rule search_values_extends[OF v tf]) (simp add: shared_reshare_def ext)
  have rf: "search_registered_formed (search_share x r)"
    using reg by (simp add: search_registered_formed_def search_share_def shared_reshare_def)
  have cf: "search_closing_formed (search_share x r)"
    by (rule search_closing_same[OF search_formed_closing[OF r]])
      (use ext in \<open>simp_all add: search_share_def shared_reshare_def\<close>)
  show "search_formed \<kappa> P (search_share x r)"
    using e(1) rf vf cf by (simp add: search_formed_def search_share_def)
qed

definition search_bind :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_bind P s r = (case keyed_collapse_bindings s (shared_sharing (search_state r)) of (s', x) \<Rightarrow>
    search_substitute P (shared_binding_substitution s') (shared_binding_domain s') (search_share x r))"

lemma search_share_classes:
  assumes r: "search_formed \<kappa> P r" and x: "share_state_formed x"
    and ext: "table_extends (search_table r) (share_state_table x)" and K: "search_classes_formed r"
  shows "search_classes_formed (search_share x r)"
  by (rule classes_formed_extends[OF r K]) (use search_share[OF r x ext] ext in \<open>simp_all add: search_share_def\<close>)

text \<open>
  Binding shares the unifier's bindings collapsed against the search's sharing state and substitutes them at their
  holders; its parts are stated once, for the search's formation and its classes.
\<close>

lemma search_bind_parts:
  assumes r: "search_formed \<kappa> P r" and sf: "shared_bindings_formed (search_table r) s"
  shows "\<exists>s' x. search_bind P s r = search_substitute P (shared_binding_substitution s') (shared_binding_domain s')
      (search_share x r) \<and> share_state_formed x \<and> table_extends (search_table r) (share_state_table x) \<and>
    shared_bindings_formed (share_state_table x) s' \<and>
    shared_bindings_project (share_state_table x) s' = shared_bindings_project (search_table r) s \<and>
    (\<forall>a. shared_pattern_formed (share_state_table x) (shared_binding_substitution s' a)) \<and>
    (\<forall>a. shared_collapsed (shared_binding_substitution s' a)) \<and>
    (\<forall>a. a |\<notin>| shared_binding_domain s' \<longrightarrow> shared_binding_substitution s' a = Shared_Variable a)"
proof -
  let ?x = "shared_sharing (search_state r)"
  have st: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have x: "share_state_formed ?x" using shared_entries_formed(3)[OF st] .
  obtain s' x' where k: "keyed_collapse_bindings s ?x = (s', x')" by (cases "keyed_collapse_bindings s ?x")
  have c: "share_state_formed x' \<and> table_extends (share_state_table ?x) (share_state_table x') \<and>
      shared_bindings_formed (share_state_table x') s' \<and>
      shared_bindings_project (share_state_table x') s' = shared_bindings_project (share_state_table ?x) s \<and>
      (\<forall>z\<in>set s'. shared_collapsed (snd z))"
    using keyed_collapse_bindings[OF x sf] k by simp
  have \<sigma>f: "shared_pattern_formed (share_state_table x') (shared_binding_substitution s' a)" for a
    using shared_binding_substitution_formed[of "share_state_table x'" s'] c by simp
  have cs: "\<forall>z\<in>set s'. shared_collapsed (snd z)" using c by simp
  have \<sigma>c: "shared_collapsed (shared_binding_substitution s' a)" for a
  proof (cases "map_of s' a")
    case (Some p)
    then have "(a,p) \<in> set s'" by (rule map_of_SomeD)
    then show ?thesis using cs Some by (force simp: shared_binding_substitution_def)
  qed (simp add: shared_binding_substitution_def)
  have out: "\<And>a. a |\<notin>| shared_binding_domain s' \<Longrightarrow> shared_binding_substitution s' a = Shared_Variable a"
    by (rule shared_binding_substitution_outside)
  have eq: "search_bind P s r = search_substitute P (shared_binding_substitution s') (shared_binding_domain s')
      (search_share x' r)"
    by (simp add: search_bind_def k)
  show ?thesis by (rule exI[where x = s'], rule exI[where x = x'], use eq c \<sigma>f \<sigma>c out in simp)
qed

theorem search_bind:
  assumes r: "search_formed \<kappa> P r" and sf: "shared_bindings_formed (search_table r) s"
  shows "search_formed \<kappa> P (search_bind P s r)"
    and "search_project (search_bind P s r) =
      resolution_state_substitute (finite_binding_substitution (shared_bindings_project (search_table r) s)) (search_project r)"
    and "table_extends (search_table r) (search_table (search_bind P s r))"
proof -
  obtain s' x where eq: "search_bind P s r = search_substitute P (shared_binding_substitution s') (shared_binding_domain s')
      (search_share x r)"
    and x: "share_state_formed x" and ext: "table_extends (search_table r) (share_state_table x)"
    and bf: "shared_bindings_formed (share_state_table x) s'"
    and bp: "shared_bindings_project (share_state_table x) s' = shared_bindings_project (search_table r) s"
    and \<sigma>f0: "\<forall>a. shared_pattern_formed (share_state_table x) (shared_binding_substitution s' a)"
    and \<sigma>c0: "\<forall>a. shared_collapsed (shared_binding_substitution s' a)"
    and out0: "\<forall>a. a |\<notin>| shared_binding_domain s' \<longrightarrow> shared_binding_substitution s' a = Shared_Variable a"
    using search_bind_parts[OF r sf] by (elim exE conjE) (rule that; assumption)
  note \<sigma>f = \<sigma>f0[rule_format] and \<sigma>c = \<sigma>c0[rule_format] and out = out0[rule_format]
  note h = search_share[OF r x ext]
  let ?r1 = "search_share x r"
  have \<sigma>f': "shared_pattern_formed (search_table ?r1) (shared_binding_substitution s' a)" for a using \<sigma>f h(3) by simp
  note k2 = search_substitute[OF h(1) \<sigma>f' \<sigma>c out]
  show "search_formed \<kappa> P (search_bind P s r)" using k2(1) eq by simp
  have e2: "table_extends (share_state_table x)
      (search_table (search_substitute P (shared_binding_substitution s') (shared_binding_domain s') ?r1))"
    using k2(2) h(3) by simp
  show "table_extends (search_table r) (search_table (search_bind P s r))"
    using table_extends_trans[OF ext e2] eq by simp
  have "(\<lambda>a. shared_pattern_project (search_table ?r1) (shared_binding_substitution s' a)) =
      finite_binding_substitution (shared_bindings_project (search_table r) s)"
    using bf bp h(3) by (simp add: fun_eq_iff shared_binding_substitution_project)
  then show "search_project (search_bind P s r) =
      resolution_state_substitute (finite_binding_substitution (shared_bindings_project (search_table r) s)) (search_project r)"
    using k2(3) h(2) eq by simp
qed

lemma search_bind_classes:
  assumes r: "search_formed \<kappa> P r" and sf: "shared_bindings_formed (search_table r) s" and K: "search_classes_formed r"
  shows "search_classes_formed (search_bind P s r)"
proof -
  obtain s' x where eq: "search_bind P s r = search_substitute P (shared_binding_substitution s') (shared_binding_domain s')
      (search_share x r)"
    and x: "share_state_formed x" and ext: "table_extends (search_table r) (share_state_table x)"
    and bf: "shared_bindings_formed (share_state_table x) s'"
    and bp: "shared_bindings_project (share_state_table x) s' = shared_bindings_project (search_table r) s"
    and \<sigma>f0: "\<forall>a. shared_pattern_formed (share_state_table x) (shared_binding_substitution s' a)"
    and \<sigma>c0: "\<forall>a. shared_collapsed (shared_binding_substitution s' a)"
    and out0: "\<forall>a. a |\<notin>| shared_binding_domain s' \<longrightarrow> shared_binding_substitution s' a = Shared_Variable a"
    using search_bind_parts[OF r sf] by (elim exE conjE) (rule that; assumption)
  note \<sigma>f = \<sigma>f0[rule_format] and \<sigma>c = \<sigma>c0[rule_format] and out = out0[rule_format]
  note h = search_share[OF r x ext]
  have \<sigma>f': "shared_pattern_formed (search_table (search_share x r)) (shared_binding_substitution s' a)" for a
    using \<sigma>f h(3) by simp
  show ?thesis unfolding eq by (rule search_substitute_classes[OF h(1) search_share_classes[OF r x ext K] \<sigma>f' \<sigma>c out])
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
  by (simp add: search_ready_def search_goal_holders_def access_ready_def access_goal_holders_def shared_access_def state_access_def state_access_over_def Let_def)

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
  have cf: "search_closing_formed (r\<lparr>search_state := ?s\<lparr>shared_unconstructed := Z\<rparr>, search_values := W\<rparr>)"
    by (rule search_closing_same[OF search_formed_closing[OF r]]) simp_all
  show ?thesis using e sf vf rf pj cf by (simp add: search_formed_def)
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

lemma search_refresh_at_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_classes_formed (search_refresh_at \<kappa> P p r)"
proof (rule classes_formed_extends[OF r K])
  show "table_extends (search_table r) (search_table (search_refresh_at \<kappa> P p r))"
    by (simp add: search_refresh_at_def Let_def split: option.split)
  show "shared_goals (search_state (search_refresh_at \<kappa> P p r)) = shared_goals (search_state r)"
    by (simp add: search_refresh_at_def Let_def split: option.split)
  show "resolution_pending (search_project (search_refresh_at \<kappa> P p r)) = resolution_pending (search_project r)"
    using search_refresh_at[OF r, of p] by simp
  show "resolution_nodes (search_project (search_refresh_at \<kappa> P p r)) = resolution_nodes (search_project r)"
    using search_refresh_at[OF r, of p] by simp
  show "search_classes (search_refresh_at \<kappa> P p r) = search_classes r"
    by (simp add: search_refresh_at_def Let_def split: option.split)
qed

lemma search_refresh_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_classes_formed (search_refresh \<kappa> P r)"
proof -
  have "search_formed \<kappa> P (fold (search_refresh_at \<kappa> P) ps t) \<and> search_classes_formed (fold (search_refresh_at \<kappa> P) ps t)"
    if "search_formed \<kappa> P t" "search_classes_formed t" for ps t
    using that
  proof (induction ps arbitrary: t)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    have "search_formed \<kappa> P (search_refresh_at \<kappa> P p t)" using search_refresh_at[OF Cons.prems(1)] by simp
    moreover have "search_classes_formed (search_refresh_at \<kappa> P p t)" by (rule search_refresh_at_classes[OF Cons.prems])
    ultimately show ?case using Cons.IH by simp
  qed
  then show ?thesis unfolding search_refresh_def using r K by blast
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

lemma search_closing_witnesses:
  "search_closing_formed (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) \<longleftrightarrow> search_closing_formed r"
proof -
  have "search_closes (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) = search_closes r"
    by (simp add: fun_eq_iff search_closes_def)
  then show ?thesis by (simp add: search_closing_formed_def split: option.split)
qed

lemma search_witnesses_update:
  "search_formed \<kappa> P (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) \<longleftrightarrow> search_formed \<kappa> P r"
  "search_project (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>) =
    Resolution_State (resolution_pending (search_project r)) (resolution_nodes (search_project r)) W"
  using search_closing_witnesses[where r=r and W=W]
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

lemma search_witnesses_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_classes_formed (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>)"
  by (rule classes_formed_extends[OF r K]) (simp_all add: shared_state_project_fields)

lemma search_construct_classes:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_classes_formed (search_construct \<kappa> P r hn)"
proof -
  have k1: "\<And>W. search_classes_formed (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>)"
    by (rule search_witnesses_classes[OF r K])
  have f1: "\<And>W. search_formed \<kappa> P (r\<lparr>search_state := (search_state r)\<lparr>shared_witnesses := W\<rparr>\<rparr>)"
    by (rule search_witnesses_update(1)[THEN iffD2, OF r])
  let ?q = "shared_derivation_position (shared_entry_node hn)" and ?C = "access_constructed (shared_access \<kappa> P r) hn"
  have out: "(case z of ((q',b),a) \<Rightarrow> if b \<and> q' = ?q \<and> a |\<in>| ?C then
      (case search_value \<kappa> P r (shared_entry_node hn) a of Some v \<Rightarrow> finite_exact_term_pattern v | None \<Rightarrow> Finite_Variable z)
      else Finite_Variable z) = Finite_Variable z"
    if "z |\<notin>| fimage (\<lambda>a. ((?q,True),a)) ?C" for z
  proof -
    obtain q' b a where zz: "z = ((q',b),a)" by (cases z) auto
    have "\<not> (b \<and> q' = ?q \<and> a |\<in>| ?C)"
    proof
      assume "b \<and> q' = ?q \<and> a |\<in>| ?C"
      then have "z |\<in>| fimage (\<lambda>a. ((?q,True),a)) ?C" using zz fimageI[of a ?C "\<lambda>a. ((?q,True),a)"] by simp
      then show False using that by simp
    qed
    then show ?thesis using zz by auto
  qed
  show ?thesis unfolding search_construct_def Let_def
    by (rule search_substitute_plain_classes[OF f1 k1], rule out, assumption)
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

text \<open>
  A formed program's clauses have distinct sockets, and a call's initial state is placeable: the shared branch of the
  search's code equation is taken at every call of a formed program (review 772, follow-up 2).
\<close>

lemma finite_system_formed_sockets_distinct: "finite_system_formed P \<Longrightarrow> clause_sockets_distinct P"
  unfolding finite_system_formed_def clause_sockets_distinct_def finite_schema_formed_def by (auto split: prod.splits)

lemma finite_initial_state_placeable: "search_placeable (finite_initial_state d t)"
  by (auto simp: search_placeable_def finite_initial_state_def resolution_positions_distinct_def)

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
  A call's plain alternative, one of R3's read at the goal's projection, places its clause and substitutes its unifier,
  shared first and collapsed; a material goal's removes the goal and substitutes its solution's unifier. Each projects
  to R3's alternative state. The search's own successors take the same placement with the shared unifier's
  alternatives instead (@{text search_call_successors}, @{text search_solution_successors} below).
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

text \<open>
  A clause is placed at a call goal's position: the goal removed, the ground terms of the clause's premises and node
  shared, the premises placed at their positions and the node at the goal's. The call state of a plain alternative
  substitutes its unifier, shared first, into the placed state.
\<close>

lemma search_place_goals_classes:
  assumes t: "search_formed \<kappa> P t" and K: "search_classes_formed t" and d: "distinct (map fst rows)"
    and free: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> RBT.lookup (shared_goals (search_state t)) q = None"
    and pos: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> resolution_goal_position g = q"
    and held: "\<And>q g u. (q,g) \<in> set rows \<Longrightarrow> u |\<in>| goal_grounds g \<Longrightarrow> table_holds (search_table t) u"
  shows "search_classes_formed (search_place_goals P rows t)"
  using t K d free pos held
proof (induction rows arbitrary: t)
  case Nil
  then show ?case by (simp add: search_place_goals_def)
next
  case (Cons z rows)
  obtain q g where z: "z = (q,g)" by (cases z)
  let ?h = "Shared_Goal_Entry (shared_goal_of (shared_sharing (search_state t)) g) (finite_goal_alternatives P g)"
  let ?t1 = "search_put_goal q ?h t"
  have one: "search_place_goals P [(q,g)] t = ?t1" by (simp add: search_place_goals_def)
  have "search_formed \<kappa> P (search_place_goals P [(q,g)] t)"
  proof (rule conjunct1[OF search_place_goals[OF Cons.prems(1)]])
    show "distinct (map fst [(q,g)])" by simp
    show "RBT.lookup (shared_goals (search_state t)) q' = None" if "(q',g') \<in> set [(q,g)]" for q' g'
      using that Cons.prems(4)[of q g] z by simp
    show "resolution_goal_position g' = q'" if "(q',g') \<in> set [(q,g)]" for q' g'
      using that Cons.prems(5)[of q g] z by simp
    show "table_holds (search_table t) u" if "(q',g') \<in> set [(q,g)]" "u |\<in>| goal_grounds g'" for q' g' u
      using that Cons.prems(6)[of q g u] z by simp
  qed
  then have f1: "search_formed \<kappa> P ?t1" using one by simp
  have k1: "search_classes_formed ?t1" by (rule search_put_goal_classes[OF Cons.prems(1,2) f1])
  have st1: "search_state ?t1 = shared_put_goal q ?h (search_state t)" by (simp add: search_put_goal_def)
  have tb: "search_table ?t1 = search_table t" using st1 by (simp add: shared_put_goal_def)
  have qn: "q \<notin> fst ` set rows" using Cons.prems(3) z by simp
  have IH: "search_classes_formed (search_place_goals P rows ?t1)"
  proof (rule Cons.IH[OF f1 k1])
    show "distinct (map fst rows)" using Cons.prems(3) by simp
    show "RBT.lookup (shared_goals (search_state ?t1)) q' = None" if "(q',g') \<in> set rows" for q' g'
    proof -
      have "q' \<noteq> q" using that qn by force
      then show ?thesis using Cons.prems(4)[of q' g'] that st1 by (simp add: shared_put_goal_def)
    qed
    show "resolution_goal_position g' = q'" if "(q',g') \<in> set rows" for q' g' using Cons.prems(5)[of q' g'] that by simp
    show "table_holds (search_table ?t1) u" if "(q',g') \<in> set rows" "u |\<in>| goal_grounds g'" for q' g' u
      using Cons.prems(6)[of q' g' u] that tb by simp
  qed
  have "search_place_goals P (z # rows) t = search_place_goals P rows ?t1" by (simp add: search_place_goals_def z)
  then show ?case using IH by simp
qed

definition search_call_place :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_call_place P r q d c S = (let G = finite_clause_goals q d c S; nd = finite_clause_node q d c S;
      r1 = search_reshare (ffUnion (fimage goal_grounds G) |\<union>| node_grounds nd) (search_remove_goal q r);
      r2 = search_place_goals P (finite_functional_rows (fimage (\<lambda>g. (resolution_goal_position g, g)) G)) r1 in
    search_put_node q (enter_node (shared_derivation_of (shared_sharing (search_state r2)) nd)) r2)"

definition search_call_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> ('d \<times> 'c \<times> 's) option \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
    'a finite_term_pattern \<times> 'c \<times> ('a,'s,'d) finite_factor_schema \<times>
      (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable finite_term_pattern) list \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_call_state P r q rr d p z = (case z of (i,c,S,u) \<Rightarrow>
    search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) (search_call_place P r q d c S))"

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

theorem search_call_place_classed:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_goal_project (search_table r) (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
    and cl: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "search_formed \<kappa> P (search_call_place P r q d c S)"
    and "search_project (search_call_place P r q d c S) = Resolution_State
      (finite_clause_goals q d c S |\<union>| (resolution_pending (search_project r) |-| {|Resolution_Call_Goal q rr d p|}))
      (finsert (finite_clause_node q d c S) (resolution_nodes (search_project r))) (resolution_witnesses (search_project r))"
    and "search_placeable (search_project (search_call_place P r q d c S))"
    and "table_extends (search_table r) (search_table (search_call_place P r q d c S))"
    and "search_classes_formed r \<Longrightarrow> search_classes_formed (search_call_place P r q d c S)"
proof -
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
  have e: "search_call_place P r q d c S = ?r3" by (simp add: search_call_place_def Let_def)
  show "search_classes_formed r \<Longrightarrow> search_classes_formed (search_call_place P r q d c S)"
  proof -
    assume K: "search_classes_formed r"
    have k0: "search_classes_formed ?r0" by (rule search_remove_goal_classes[OF r K at])
    have k1: "search_classes_formed ?r1" by (rule search_reshare_classes[OF r0(1) k0])
    have k2: "search_classes_formed ?r2" by (rule search_place_goals_classes[OF r1(1) k1 rd rfree rpos rheld])
    have k3: "search_classes_formed ?r3" by (rule search_put_node_classes[OF conjunct1[OF r2] k2 r3(1)])
    then show ?thesis using e by simp
  qed
  show "search_formed \<kappa> P (search_call_place P r q d c S)" using r3(1) e by simp
  show "search_project (search_call_place P r q d c S) =
      Resolution_State (?G |\<union>| (resolution_pending ?st |-| {|?g|})) (finsert ?nd (resolution_nodes ?st)) (resolution_witnesses ?st)"
    using p3 e by simp
  show "search_placeable (search_project (search_call_place P r q d c S))"
    using search_placeable_call[OF pl gin f1 f2 dj, where c = c and W = "resolution_witnesses ?st"] p3 e by simp
  have t0: "search_table ?r0 = search_table r" using r0(2) by (simp add: shared_remove_goal_def shared_replace_def)
  have t3: "search_table ?r3 = search_table ?r1" using r3(2) x2 by (simp add: shared_put_node_def)
  show "table_extends (search_table r) (search_table (search_call_place P r q d c S))" using r1(3) t0 t3 e by simp
qed

theorem search_call_place:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_goal_project (search_table r) (shared_entry_goal h) = Resolution_Call_Goal q rr d p"
    and cl: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "search_formed \<kappa> P (search_call_place P r q d c S)"
    and "search_project (search_call_place P r q d c S) = Resolution_State
      (finite_clause_goals q d c S |\<union>| (resolution_pending (search_project r) |-| {|Resolution_Call_Goal q rr d p|}))
      (finsert (finite_clause_node q d c S) (resolution_nodes (search_project r))) (resolution_witnesses (search_project r))"
    and "search_placeable (search_project (search_call_place P r q d c S))"
    and "table_extends (search_table r) (search_table (search_call_place P r q d c S))"
  by (rule search_call_place_classed[OF r pl sock at g cl])+

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
  note pc = search_call_place[OF r pl sock at g cl]
  have out: "\<And>a. a |\<notin>| fset_of_list (map fst u) \<Longrightarrow> finite_binding_substitution u a = Finite_Variable a"
    by (rule finite_binding_substitution_outside)
  note k = search_substitute_plain[where \<tau> = "finite_binding_substitution u" and D = "fset_of_list (map fst u)",
    OF pc(1) out]
  have e: "search_call_state P r q rr d p z =
      search_substitute_plain P (finite_binding_substitution u) (fset_of_list (map fst u)) (search_call_place P r q d c S)"
    by (simp add: search_call_state_def zz)
  show "search_formed \<kappa> P (search_call_state P r q rr d p z)" using k(1) e by simp
  show "search_project (search_call_state P r q rr d p z) = finite_call_alternative_state (search_project r) q rr d p z"
    using k(2) e pc(2) by (simp add: finite_call_alternative_state_def zz)
  show "search_placeable (search_project (search_call_state P r q rr d p z))"
    using k(2) e pc(3) search_placeable_substitute by simp
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

subsection \<open>The alternatives computed by the shared unifier\<close>

text \<open>
  A call goal's alternatives are computed on its shared pattern: the ground terms of the definition's renamed
  interfaces and clause heads are shared first, and each clause is unified by F2a's unifier (@{const shared_unify_pairs})
  against the goal's pattern as it stands, so a variable is bound to the reference of the goal's ground subterm, never
  to its decoded copy. A material goal's solutions are unified likewise: its shared fields against the solution's
  instances, shared first. Each shared alternative projects to R3's (@{thm [source] shared_unify_pairs_exact}), and its
  state is the placed clause, or the goal removed, with the shared unifier bound (@{const search_bind}).
\<close>

text \<open>
  The successors of a call goal take the bind as a parameter (task 903, D1b): each alternative the shared unifier gives
  is placed as today and its bindings handed to the bind, which may give any state. The theorem is stated once over the
  bind: where every alternative's bound state is invariant and presents R3's alternative state of a state the caller
  names, the successors present R3's successors of that state. Today's successors are the instance at
  @{text search_bind}, the state being the search's own projection.
\<close>

definition search_call_successors_with :: "((('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> 'r) \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable shared_pattern \<Rightarrow> 'r fset" where
  "search_call_successors_with \<beta> P r q d gp = (let r0 = search_reshare (search_call_grounds P q d) r in
    fimage (\<lambda>(i,c,S,s). \<beta> s (search_call_place P r0 q d c S))
      (shared_call_alternatives P (shared_sharing (search_state r0)) q d gp))"

theorem search_call_successors_with:
  assumes r: "search_formed \<kappa> P r" and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Call_Goal q rr d gp"
    and step: "\<And>i c S s. (i,c,S,s) |\<in>| shared_call_alternatives P
        (shared_sharing (search_state (search_reshare (search_call_grounds P q d) r))) q d gp \<Longrightarrow>
      ((d,c),S) |\<in>| finite_system_clauses P \<Longrightarrow>
      shared_bindings_formed (search_table (search_reshare (search_call_grounds P q d) r)) s \<Longrightarrow>
      F (\<beta> s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) \<and>
      proj (\<beta> s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) =
        finite_call_alternative_state st q rr d (shared_pattern_project (search_table r) gp)
          (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q d) r)) s)"
  shows "fimage proj (search_call_successors_with \<beta> P r q d gp) =
      fimage (finite_call_alternative_state st q rr d (shared_pattern_project (search_table r) gp))
        (finite_call_alternative_set P q d (shared_pattern_project (search_table r) gp))"
    and "s' |\<in>| search_call_successors_with \<beta> P r q d gp \<Longrightarrow> F s'"
proof -
  let ?p = "shared_pattern_project (search_table r) gp"
  let ?r0 = "search_reshare (search_call_grounds P q d) r"
  let ?x = "shared_sharing (search_state ?r0)"
  let ?G = "\<lambda>(i,c,S,s). \<beta> s (search_call_place P ?r0 q d c S)"
  let ?f = "\<lambda>(i,c,S,s). (i,c,S,shared_bindings_project (share_state_table ?x) s)"
  note h0 = search_reshare[where G = "search_call_grounds P q d", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gpf: "shared_pattern_formed (search_table r) gp"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gp0 = shared_pattern_extends[OF tf gpf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have gpx: "shared_pattern_formed (share_state_table ?x) gp" "shared_pattern_project (share_state_table ?x) gp = ?p"
    using gp0 by simp_all
  have held: "\<forall>t. t |\<in>| search_call_grounds P q d \<longrightarrow> table_holds (share_state_table ?x) t" using h0(4) by simp
  note A = shared_call_alternatives_project[OF x0 gpx(1) held]
  have each: "F (?G z) \<and> proj (?G z) = finite_call_alternative_state st q rr d ?p (?f z)"
    if z: "z |\<in>| shared_call_alternatives P ?x q d gp" for z
  proof -
    obtain i c S s where zz: "z = (i,c,S,s)" and cl: "((d,c),S) |\<in>| finite_system_clauses P"
      and sf: "shared_bindings_formed (share_state_table ?x) s" using A(2)[OF z] by blast
    show ?thesis using step[OF z[unfolded zz] cl sf] zz by simp
  qed
  have eq: "search_call_successors_with \<beta> P r q d gp = fimage ?G (shared_call_alternatives P ?x q d gp)"
    by (simp add: search_call_successors_with_def Let_def)
  have m: "fimage proj (fimage ?G (shared_call_alternatives P ?x q d gp)) =
      fimage (finite_call_alternative_state st q rr d ?p) (fimage ?f (shared_call_alternatives P ?x q d gp))"
    unfolding fset.map_comp comp_def by (rule fset.map_cong0) (use each in blast)
  note A1 = A(1)[unfolded gpx(2)]
  show "fimage proj (search_call_successors_with \<beta> P r q d gp) =
      fimage (finite_call_alternative_state st q rr d ?p) (finite_call_alternative_set P q d ?p)"
    unfolding eq m A1 by (rule refl)
  show "F s'" if ms: "s' |\<in>| search_call_successors_with \<beta> P r q d gp"
  proof -
    obtain z where z: "z |\<in>| shared_call_alternatives P ?x q d gp" and sz: "s' = ?G z"
      using ms eq by (auto simp: fimage_iff)
    show ?thesis unfolding sz using each[OF z] by blast
  qed
qed

text \<open>At the bind of the shared search, each alternative's bound state is formed and presents R3's alternative state.\<close>

lemma search_bind_call_alternative:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Call_Goal q rr d gp"
    and cl: "((d,c),S) |\<in>| finite_system_clauses P"
    and sf: "shared_bindings_formed (search_table (search_reshare (search_call_grounds P q d) r)) s"
  shows "(search_formed \<kappa> P (search_bind P s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) \<and>
      search_placeable (search_project (search_bind P s
        (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)))) \<and>
    search_project (search_bind P s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) =
      finite_call_alternative_state (search_project r) q rr d (shared_pattern_project (search_table r) gp)
        (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q d) r)) s)"
proof -
  let ?p = "shared_pattern_project (search_table r) gp" and ?st = "search_project r"
  let ?r0 = "search_reshare (search_call_grounds P q d) r"
  let ?T0 = "search_table (search_reshare (search_call_grounds P q d) r)"
  note h0 = search_reshare[where G = "search_call_grounds P q d", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gpf: "shared_pattern_formed (search_table r) gp"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gp0 = shared_pattern_extends[OF tf gpf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have tf0: "table_formed ?T0" using shared_entries_formed(4)[OF s0] .
  have at0: "RBT.lookup (shared_goals (search_state ?r0)) q = Some h" using h0(5) at by simp
  have pl0: "search_placeable (search_project ?r0)" using h0(2) pl by simp
  have g0: "shared_goal_project ?T0 (shared_entry_goal h) = Resolution_Call_Goal q rr d ?p" using g gp0 by simp
  note pc = search_call_place[OF h0(1) pl0 sock at0 g0 cl]
  note sb = shared_bindings_extends[OF tf0 pc(4) sf]
  note b = search_bind[OF pc(1) conjunct1[OF sb]]
  have pr: "search_project (search_bind P s (search_call_place P ?r0 q d c S)) =
      finite_call_alternative_state ?st q rr d ?p (i,c,S,shared_bindings_project ?T0 s)"
    using b(2) pc(2) sb h0(2) by (simp add: finite_call_alternative_state_def)
  have pb: "search_placeable (search_project (search_bind P s (search_call_place P ?r0 q d c S)))"
    using b(2) pc(3) search_placeable_substitute by simp
  show ?thesis using b(1) pr pb by simp
qed

definition search_call_successors :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable shared_pattern \<Rightarrow> ('a,'s,'d,'c) shared_search fset" where
  "search_call_successors P r q d gp = search_call_successors_with (search_bind P) P r q d gp"

theorem search_call_successors_classed:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Call_Goal q rr d gp"
  shows "fimage search_project (search_call_successors P r q d gp) =
      fimage (finite_call_alternative_state (search_project r) q rr d (shared_pattern_project (search_table r) gp))
        (finite_call_alternative_set P q d (shared_pattern_project (search_table r) gp))"
    and "s' |\<in>| search_call_successors P r q d gp \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
    and "s' |\<in>| search_call_successors P r q d gp \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
proof -
  let ?p = "shared_pattern_project (search_table r) gp" and ?st = "search_project r"
  let ?r0 = "search_reshare (search_call_grounds P q d) r"
  let ?x = "shared_sharing (search_state ?r0)" and ?T0 = "search_table ?r0"
  let ?F = "\<lambda>(i,c,S,s). search_bind P s (search_call_place P ?r0 q d c S)"
  let ?f = "\<lambda>(i,c,S,s). (i,c,S,shared_bindings_project (share_state_table ?x) s)"
  note h0 = search_reshare[where G = "search_call_grounds P q d", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gpf: "shared_pattern_formed (search_table r) gp"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gp0 = shared_pattern_extends[OF tf gpf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have tf0: "table_formed ?T0" using shared_entries_formed(4)[OF s0] .
  have gpx: "shared_pattern_formed (share_state_table ?x) gp" "shared_pattern_project (share_state_table ?x) gp = ?p"
    using gp0 by simp_all
  have held: "\<forall>t. t |\<in>| search_call_grounds P q d \<longrightarrow> table_holds (share_state_table ?x) t" using h0(4) by simp
  note A = shared_call_alternatives_project[OF x0 gpx(1) held]
  have at0: "RBT.lookup (shared_goals (search_state ?r0)) q = Some h" using h0(5) at by simp
  have pl0: "search_placeable (search_project ?r0)" using h0(2) pl by simp
  have g0: "shared_goal_project ?T0 (shared_entry_goal h) = Resolution_Call_Goal q rr d ?p" using g gp0 by simp
  have eq: "search_call_successors P r q d gp = fimage ?F (shared_call_alternatives P ?x q d gp)"
    by (simp add: search_call_successors_def search_call_successors_with_def Let_def)
  show "s' |\<in>| search_call_successors P r q d gp \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
  proof -
    assume s': "s' |\<in>| search_call_successors P r q d gp" and K: "search_classes_formed r"
    obtain z where z: "z |\<in>| shared_call_alternatives P ?x q d gp" and e: "s' = ?F z" using s' eq by auto
    obtain i c S s where zz: "z = (i,c,S,s)" and cl: "((d,c),S) |\<in>| finite_system_clauses P"
      and sf: "shared_bindings_formed (share_state_table ?x) s" using A(2)[OF z] by blast
    note pc = search_call_place_classed[OF h0(1) pl0 sock at0 g0 cl]
    have sf0: "shared_bindings_formed ?T0 s" using sf by simp
    note sb = shared_bindings_extends[OF tf0 pc(4) sf0]
    have k0: "search_classes_formed ?r0" by (rule search_reshare_classes[OF r K])
    have "search_classes_formed (search_bind P s (search_call_place P ?r0 q d c S))"
      by (rule search_bind_classes[OF pc(1) conjunct1[OF sb] pc(5)[OF k0]])
    then show ?thesis using e zz by simp
  qed
  show "fimage search_project (search_call_successors P r q d gp) =
      fimage (finite_call_alternative_state ?st q rr d ?p) (finite_call_alternative_set P q d ?p)"
    unfolding search_call_successors_def
    by (rule search_call_successors_with(1)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')",
      OF r at g]) (rule search_bind_call_alternative[OF r pl sock at g]; assumption)
  show "search_formed \<kappa> P s' \<and> search_placeable (search_project s')" if ms: "s' |\<in>| search_call_successors P r q d gp"
    by (rule search_call_successors_with(2)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
      and proj = search_project and st = ?st, OF r at g _ ms[unfolded search_call_successors_def]])
      (rule search_bind_call_alternative[OF r pl sock at g]; assumption)
qed

definition shared_material_pairs :: "share_state \<Rightarrow> 'a shared_material \<Rightarrow> 'a finite_pattern_pairs \<Rightarrow> 'a shared_pattern_pairs" where
  "shared_material_pairs x gM E = zip [shared_material_source gM, shared_material_atoms gM, shared_material_edges gM,
    shared_material_counts gM, shared_material_functions gM] (map (\<lambda>e. keyed_pattern_at x (snd e)) E)"

definition solution_grounds :: "('a \<times> finite_factor_term) fset fset \<Rightarrow> 'a finite_material_pattern \<Rightarrow> finite_factor_term fset" where
  "solution_grounds Ws M = ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E. ffUnion (fset_of_list (map (\<lambda>e. pattern_grounds (snd e)) E)))
    (finite_material_instance_pairs W M))) Ws)"

definition shared_solution_alternatives :: "share_state \<Rightarrow> 'a shared_material \<Rightarrow> 'a finite_material_pattern \<Rightarrow>
    ('a \<times> finite_factor_term) fset fset \<Rightarrow> ('a finite_pattern_pairs \<times> ('a \<times> 'a shared_pattern) list) fset" where
  "shared_solution_alternatives x gM M Ws = (let T = share_state_table x in ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E.
      case shared_unify_pairs T (shared_material_pairs x gM E) of None \<Rightarrow> {||} | Some s \<Rightarrow> {|(E,s)|})
    (finite_material_instance_pairs W M))) Ws))"

theorem search_call_successors:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Call_Goal q rr d gp"
  shows "fimage search_project (search_call_successors P r q d gp) =
      fimage (finite_call_alternative_state (search_project r) q rr d (shared_pattern_project (search_table r) gp))
        (finite_call_alternative_set P q d (shared_pattern_project (search_table r) gp))"
    and "s' |\<in>| search_call_successors P r q d gp \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
  by (rule search_call_successors_classed[OF r pl sock at g])+

lemma shared_solution_alternatives_member:
  "z |\<in>| shared_solution_alternatives x gM M Ws \<longleftrightarrow> (\<exists>W E s. z = (E,s) \<and> W |\<in>| Ws \<and>
    E |\<in>| finite_material_instance_pairs W M \<and> shared_unify_pairs (share_state_table x) (shared_material_pairs x gM E) = Some s)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then show ?r unfolding shared_solution_alternatives_def Let_def
    by (auto simp: ffUnion.rep_eq fimage.rep_eq split: option.splits)
next
  assume ?r
  then show ?l unfolding shared_solution_alternatives_def Let_def by (force simp: ffUnion.rep_eq fimage.rep_eq)
qed

lemma finite_solution_alternatives_member:
  "z |\<in>| finite_solution_alternatives M Ws \<longleftrightarrow> (\<exists>W E u. z = (E,u) \<and> W |\<in>| Ws \<and>
    E |\<in>| finite_material_instance_pairs W M \<and> finite_unify_pairs E = Some u)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then show ?r unfolding finite_solution_alternatives_def by (auto simp: ffUnion.rep_eq fimage.rep_eq split: option.splits)
next
  assume ?r
  then show ?l unfolding finite_solution_alternatives_def by (force simp: ffUnion.rep_eq fimage.rep_eq)
qed

lemma material_instance_pairs_shape:
  assumes "E |\<in>| finite_material_instance_pairs W M"
  shows "\<exists>a b c e f. E = [(finite_material_source M, finite_exact_term_pattern a),
    (finite_material_atoms M, finite_exact_term_pattern b), (finite_material_edges M, finite_exact_term_pattern c),
    (finite_material_counts M, finite_exact_term_pattern e), (finite_material_functions M, finite_exact_term_pattern f)]"
  using assms unfolding finite_material_instance_pairs_def by (auto simp: ffUnion.rep_eq fimage.rep_eq)

lemma shared_material_pairs_exact:
  assumes x: "share_state_formed x" and gM: "shared_material_formed (share_state_table x) gM"
    and E: "E |\<in>| finite_material_instance_pairs W (shared_material_project (share_state_table x) gM)"
    and held: "\<And>t. t |\<in>| ffUnion (fset_of_list (map (\<lambda>e. pattern_grounds (snd e)) E)) \<Longrightarrow> table_holds (share_state_table x) t"
  shows "shared_pairs_formed (share_state_table x) (shared_material_pairs x gM E) \<and>
    shared_pairs_project (share_state_table x) (shared_material_pairs x gM E) = E"
proof -
  let ?T = "share_state_table x"
  have rep: "keyed_state_represents x ?T" and tf: "table_formed ?T" using share_state_formed_table[OF x] by simp_all
  obtain a b c e f where Ee: "E = [(finite_material_source (shared_material_project ?T gM), finite_exact_term_pattern a),
      (finite_material_atoms (shared_material_project ?T gM), finite_exact_term_pattern b),
      (finite_material_edges (shared_material_project ?T gM), finite_exact_term_pattern c),
      (finite_material_counts (shared_material_project ?T gM), finite_exact_term_pattern e),
      (finite_material_functions (shared_material_project ?T gM), finite_exact_term_pattern f)]"
    using material_instance_pairs_shape[OF E] by blast
  have k: "shared_pattern_formed ?T (keyed_pattern_at x (finite_exact_term_pattern v :: 'a finite_term_pattern)) \<and>
      shared_pattern_project ?T (keyed_pattern_at x (finite_exact_term_pattern v :: 'a finite_term_pattern)) =
        finite_exact_term_pattern v"
    if v: "v \<in> {a,b,c,e,f}" for v
  proof -
    have "\<And>t. t |\<in>| pattern_grounds (finite_exact_term_pattern v :: 'a finite_term_pattern) \<Longrightarrow> table_holds ?T t"
    proof -
      fix t assume t: "t |\<in>| pattern_grounds (finite_exact_term_pattern v :: 'a finite_term_pattern)"
      have "t |\<in>| ffUnion (fset_of_list (map (\<lambda>e. pattern_grounds (snd e)) E))" using v t by (auto simp: Ee ffUnion.rep_eq)
      then show "table_holds ?T t" by (rule held)
    qed
    from keyed_pattern_at_exact[OF rep tf, where p = "finite_exact_term_pattern v", OF this] show ?thesis by blast
  qed
  show ?thesis using k[of a] k[of b] k[of c] k[of e] k[of f] gM
    by (simp add: Ee shared_material_pairs_def shared_material_formed_def shared_material_project_def)
qed

lemma shared_solution_alternatives_project:
  assumes x: "share_state_formed x" and gM: "shared_material_formed (share_state_table x) gM"
    and held: "\<forall>t. t |\<in>| solution_grounds Ws (shared_material_project (share_state_table x) gM) \<longrightarrow>
      table_holds (share_state_table x) t"
  shows "fimage (\<lambda>(E,s). (E, shared_bindings_project (share_state_table x) s))
      (shared_solution_alternatives x gM (shared_material_project (share_state_table x) gM) Ws) =
    finite_solution_alternatives (shared_material_project (share_state_table x) gM) Ws"
    and "z |\<in>| shared_solution_alternatives x gM (shared_material_project (share_state_table x) gM) Ws \<Longrightarrow>
      \<exists>E s. z = (E,s) \<and> shared_bindings_formed (share_state_table x) s"
proof -
  let ?T = "share_state_table x" and ?M = "shared_material_project (share_state_table x) gM"
  let ?f = "\<lambda>(E,s). (E, shared_bindings_project ?T s)"
  have tf: "table_formed ?T" using share_state_formed_table(1)[OF x] .
  have pairs: "shared_pairs_formed ?T (shared_material_pairs x gM E) \<and> shared_pairs_project ?T (shared_material_pairs x gM E) = E"
    if "W |\<in>| Ws" "E |\<in>| finite_material_instance_pairs W ?M" for W E
  proof (rule shared_material_pairs_exact[OF x gM that(2)])
    fix t assume "t |\<in>| ffUnion (fset_of_list (map (\<lambda>e. pattern_grounds (snd e)) E))"
    then have "t |\<in>| solution_grounds Ws ?M" using that by (force simp: solution_grounds_def ffUnion.rep_eq fimage.rep_eq)
    then show "table_holds ?T t" using held by blast
  qed
  note un = shared_unify_pairs_exact[OF tf]
  show "fimage ?f (shared_solution_alternatives x gM ?M Ws) = finite_solution_alternatives ?M Ws"
  proof (rule fset_eqI)
    fix z
    show "z |\<in>| fimage ?f (shared_solution_alternatives x gM ?M Ws) \<longleftrightarrow> z |\<in>| finite_solution_alternatives ?M Ws"
    proof
      assume "z |\<in>| fimage ?f (shared_solution_alternatives x gM ?M Ws)"
      then obtain y where y: "y |\<in>| shared_solution_alternatives x gM ?M Ws" and zy: "z = ?f y" by (auto simp: fimage_iff)
      then obtain W E s where yy: "y = (E,s)" and ww: "W |\<in>| Ws" and ee: "E |\<in>| finite_material_instance_pairs W ?M"
        and us: "shared_unify_pairs ?T (shared_material_pairs x gM E) = Some s"
        by (auto simp: shared_solution_alternatives_member)
      have "finite_unify_pairs E = Some (shared_bindings_project ?T s)"
        using un[OF conjunct1[OF pairs[OF ww ee]]] conjunct2[OF pairs[OF ww ee]] us by simp
      then show "z |\<in>| finite_solution_alternatives ?M Ws" using yy zy ww ee by (auto simp: finite_solution_alternatives_member)
    next
      assume "z |\<in>| finite_solution_alternatives ?M Ws"
      then obtain W E u where zz: "z = (E,u)" and ww: "W |\<in>| Ws" and ee: "E |\<in>| finite_material_instance_pairs W ?M"
        and uu: "finite_unify_pairs E = Some u" by (auto simp: finite_solution_alternatives_member)
      have "map_option (shared_bindings_project ?T) (shared_unify_pairs ?T (shared_material_pairs x gM E)) = Some u"
        using un[OF conjunct1[OF pairs[OF ww ee]]] conjunct2[OF pairs[OF ww ee]] uu by simp
      then obtain s where us: "shared_unify_pairs ?T (shared_material_pairs x gM E) = Some s"
        and su: "shared_bindings_project ?T s = u" by auto
      have m: "(E,s) |\<in>| shared_solution_alternatives x gM ?M Ws" using ww ee us
        by (auto simp: shared_solution_alternatives_member)
      show "z |\<in>| fimage ?f (shared_solution_alternatives x gM ?M Ws)" using fimageI[OF m, of ?f] zz su by simp
    qed
  qed
  show "\<exists>E s. z = (E,s) \<and> shared_bindings_formed ?T s" if mz: "z |\<in>| shared_solution_alternatives x gM ?M Ws"
  proof -
    obtain W E s where zz: "z = (E,s)" and ww: "W |\<in>| Ws" and ee: "E |\<in>| finite_material_instance_pairs W ?M"
      and us: "shared_unify_pairs ?T (shared_material_pairs x gM E) = Some s"
      using mz unfolding shared_solution_alternatives_member by blast
    show ?thesis using un[OF conjunct1[OF pairs[OF ww ee]]] us zz by blast
  qed
qed

text \<open>The successors of a material goal over the bind, stated once as the call goal's are.\<close>

definition search_solution_successors_with :: "((('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> 'r) \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> ('s,'a) resolution_variable shared_material \<Rightarrow> ('s,'a) resolution_variable finite_material_pattern \<Rightarrow>
    (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow> 'r fset" where
  "search_solution_successors_with \<beta> P r q gM M Ws = (let r0 = search_reshare (solution_grounds Ws M) r in
    fimage (\<lambda>(E,s). \<beta> s (search_remove_goal q r0)) (shared_solution_alternatives (shared_sharing (search_state r0)) gM M Ws))"

theorem search_solution_successors_with:
  assumes r: "search_formed \<kappa> P r" and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
    and step: "\<And>E s. (E,s) |\<in>| shared_solution_alternatives
        (shared_sharing (search_state (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)))
        gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow> shared_bindings_formed
        (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s \<Longrightarrow>
      F (\<beta> s (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) \<and>
      proj (\<beta> s (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) =
        finite_material_alternative_state st q rr (shared_material_project (search_table r) gM)
          (E, shared_bindings_project
            (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s)"
  shows "fimage proj (search_solution_successors_with \<beta> P r q gM (shared_material_project (search_table r) gM) Ws) =
      fimage (finite_material_alternative_state st q rr (shared_material_project (search_table r) gM))
        (finite_solution_alternatives (shared_material_project (search_table r) gM) Ws)"
    and "s' |\<in>| search_solution_successors_with \<beta> P r q gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow> F s'"
proof -
  let ?M = "shared_material_project (search_table r) gM"
  let ?r0 = "search_reshare (solution_grounds Ws ?M) r"
  let ?x = "shared_sharing (search_state ?r0)"
  let ?G = "\<lambda>(E,s). \<beta> s (search_remove_goal q ?r0)"
  let ?f = "\<lambda>(E,s). (E, shared_bindings_project (share_state_table ?x) s)"
  note h0 = search_reshare[where G = "solution_grounds Ws ?M", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gf: "shared_material_formed (search_table r) gM"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gM0 = shared_material_extends[OF tf gf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have gMx: "shared_material_formed (share_state_table ?x) gM" "shared_material_project (share_state_table ?x) gM = ?M"
    using gM0 by simp_all
  have held: "\<forall>t. t |\<in>| solution_grounds Ws (shared_material_project (share_state_table ?x) gM) \<longrightarrow>
      table_holds (share_state_table ?x) t" using h0(4) gMx(2) by simp
  note A = shared_solution_alternatives_project[OF x0 gMx(1) held]
  note A2 = A(2)[unfolded gMx(2)]
  have each: "F (?G z) \<and> proj (?G z) = finite_material_alternative_state st q rr ?M (?f z)"
    if z: "z |\<in>| shared_solution_alternatives ?x gM ?M Ws" for z
  proof -
    obtain E s where zz: "z = (E,s)" and sf: "shared_bindings_formed (share_state_table ?x) s" using A2[OF z] by blast
    show ?thesis using step[OF z[unfolded zz] sf] zz by simp
  qed
  have eq: "search_solution_successors_with \<beta> P r q gM ?M Ws = fimage ?G (shared_solution_alternatives ?x gM ?M Ws)"
    by (simp add: search_solution_successors_with_def Let_def)
  have m: "fimage proj (fimage ?G (shared_solution_alternatives ?x gM ?M Ws)) =
      fimage (finite_material_alternative_state st q rr ?M) (fimage ?f (shared_solution_alternatives ?x gM ?M Ws))"
    unfolding fset.map_comp comp_def by (rule fset.map_cong0) (use each in blast)
  note A1 = A(1)[unfolded gMx(2)]
  show "fimage proj (search_solution_successors_with \<beta> P r q gM ?M Ws) =
      fimage (finite_material_alternative_state st q rr ?M) (finite_solution_alternatives ?M Ws)"
    unfolding eq m A1 by (rule refl)
  show "F s'" if ms: "s' |\<in>| search_solution_successors_with \<beta> P r q gM ?M Ws"
  proof -
    obtain z where z: "z |\<in>| shared_solution_alternatives ?x gM ?M Ws" and sz: "s' = ?G z"
      using ms eq by (auto simp: fimage_iff)
    show ?thesis unfolding sz using each[OF z] by blast
  qed
qed

lemma search_bind_solution_alternative:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
    and sf: "shared_bindings_formed
      (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s"
  shows "(search_formed \<kappa> P (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) \<and>
      search_placeable (search_project (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))))) \<and>
    search_project (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) =
      finite_material_alternative_state (search_project r) q rr (shared_material_project (search_table r) gM)
        (E, shared_bindings_project
          (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s)"
proof -
  let ?M = "shared_material_project (search_table r) gM" and ?st = "search_project r"
  let ?r0 = "search_reshare (solution_grounds Ws ?M) r"
  let ?T0 = "search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)"
  note h0 = search_reshare[where G = "solution_grounds Ws ?M", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gf: "shared_material_formed (search_table r) gM"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gM0 = shared_material_extends[OF tf gf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have at0: "RBT.lookup (shared_goals (search_state ?r0)) q = Some h" using h0(5) at by simp
  have g0: "shared_goal_project ?T0 (shared_entry_goal h) = Resolution_Material_Goal q rr ?M" using g gM0 by simp
  note r0 = search_remove_goal[OF h0(1) at0]
  note sr0 = shared_remove_goal[OF s0 at0]
  have p0: "search_project (search_remove_goal q ?r0) = Resolution_State
      (resolution_pending ?st |-| {|Resolution_Material_Goal q rr ?M|}) (resolution_nodes ?st) (resolution_witnesses ?st)"
    using sr0(2-4) r0(2) g0 h0(2) by (cases "search_project (search_remove_goal q ?r0)") simp
  have trm: "search_table (search_remove_goal q ?r0) = ?T0" using r0(2) by (simp add: shared_remove_goal_def shared_replace_def)
  have plr: "search_placeable (search_project (search_remove_goal q ?r0))" using search_placeable_fewer[OF pl] p0 by simp
  have sf0: "shared_bindings_formed (search_table (search_remove_goal q ?r0)) s" using sf trm by simp
  note b = search_bind[OF r0(1) sf0]
  have pr: "search_project (search_bind P s (search_remove_goal q ?r0)) =
      finite_material_alternative_state ?st q rr ?M (E, shared_bindings_project ?T0 s)"
    using b(2) p0 trm by (simp add: finite_material_alternative_state_def)
  have pb: "search_placeable (search_project (search_bind P s (search_remove_goal q ?r0)))"
    using b(2) plr search_placeable_substitute by simp
  show ?thesis using b(1) pr pb by simp
qed

definition search_solution_successors :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    's list \<Rightarrow> ('s,'a) resolution_variable shared_material \<Rightarrow> ('s,'a) resolution_variable finite_material_pattern \<Rightarrow>
    (('s,'a) resolution_variable \<times> finite_factor_term) fset fset \<Rightarrow> ('a,'s,'d,'c) shared_search fset" where
  "search_solution_successors P r q gM M Ws = search_solution_successors_with (search_bind P) P r q gM M Ws"

theorem search_solution_successors_classed:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
  shows "fimage search_project (search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws) =
      fimage (finite_material_alternative_state (search_project r) q rr (shared_material_project (search_table r) gM))
        (finite_solution_alternatives (shared_material_project (search_table r) gM) Ws)"
    and "s' |\<in>| search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow>
      search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
    and "s' |\<in>| search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow>
      search_classes_formed r \<Longrightarrow> search_classes_formed s'"
proof -
  let ?M = "shared_material_project (search_table r) gM" and ?st = "search_project r"
  let ?r0 = "search_reshare (solution_grounds Ws ?M) r"
  let ?x = "shared_sharing (search_state ?r0)" and ?T0 = "search_table ?r0"
  let ?F = "\<lambda>(E,s). search_bind P s (search_remove_goal q ?r0)"
  let ?f = "\<lambda>(E,s). (E, shared_bindings_project (share_state_table ?x) s)"
  note h0 = search_reshare[where G = "solution_grounds Ws ?M", OF r]
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD[OF r] by simp
  have tf: "table_formed (search_table r)" using shared_entries_formed(4)[OF s] .
  have gf: "shared_material_formed (search_table r) gM"
    using shared_entries_formed(1)[OF s at] g by (simp add: goal_entry_formed_def)
  note gM0 = shared_material_extends[OF tf gf h0(3)]
  have s0: "shared_state_formed \<kappa> P (search_state ?r0)" using search_formedD[OF h0(1)] by simp
  have x0: "share_state_formed ?x" using shared_entries_formed(3)[OF s0] .
  have gMx: "shared_material_formed (share_state_table ?x) gM" "shared_material_project (share_state_table ?x) gM = ?M"
    using gM0 by simp_all
  have held: "\<forall>t. t |\<in>| solution_grounds Ws (shared_material_project (share_state_table ?x) gM) \<longrightarrow>
      table_holds (share_state_table ?x) t" using h0(4) gMx(2) by simp
  note A = shared_solution_alternatives_project[OF x0 gMx(1) held]
  note A2 = A(2)[unfolded gMx(2)]
  have at0: "RBT.lookup (shared_goals (search_state ?r0)) q = Some h" using h0(5) at by simp
  have g0: "shared_goal_project ?T0 (shared_entry_goal h) = Resolution_Material_Goal q rr ?M" using g gM0 by simp
  note r0 = search_remove_goal[OF h0(1) at0]
  note sr0 = shared_remove_goal[OF s0 at0]
  have p0: "search_project (search_remove_goal q ?r0) = Resolution_State
      (resolution_pending ?st |-| {|Resolution_Material_Goal q rr ?M|}) (resolution_nodes ?st) (resolution_witnesses ?st)"
    using sr0(2-4) r0(2) g0 h0(2) by (cases "search_project (search_remove_goal q ?r0)") simp
  have trm: "search_table (search_remove_goal q ?r0) = ?T0" using r0(2) by (simp add: shared_remove_goal_def shared_replace_def)
  have plr: "search_placeable (search_project (search_remove_goal q ?r0))" using search_placeable_fewer[OF pl] p0 by simp
  show "s' |\<in>| search_solution_successors P r q gM ?M Ws \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
  proof -
    assume s': "s' |\<in>| search_solution_successors P r q gM ?M Ws" and K: "search_classes_formed r"
    obtain z where z: "z |\<in>| shared_solution_alternatives ?x gM ?M Ws" and e: "s' = ?F z"
      using s' by (auto simp: search_solution_successors_def search_solution_successors_with_def Let_def)
    obtain E s where zz: "z = (E,s)" and sf: "shared_bindings_formed (share_state_table ?x) s" using A2[OF z] by blast
    have k0: "search_classes_formed ?r0" by (rule search_reshare_classes[OF r K])
    have kr: "search_classes_formed (search_remove_goal q ?r0)" by (rule search_remove_goal_classes[OF h0(1) k0 at0])
    have sfr: "shared_bindings_formed (search_table (search_remove_goal q ?r0)) s" using sf trm by simp
    have "search_classes_formed (search_bind P s (search_remove_goal q ?r0))" by (rule search_bind_classes[OF r0(1) sfr kr])
    then show ?thesis using e zz by simp
  qed
  show "fimage search_project (search_solution_successors P r q gM ?M Ws) =
      fimage (finite_material_alternative_state ?st q rr ?M) (finite_solution_alternatives ?M Ws)"
    unfolding search_solution_successors_def
    by (rule search_solution_successors_with(1)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')",
      OF r at g]) (rule search_bind_solution_alternative[OF r pl at g]; assumption)
  show "search_formed \<kappa> P s' \<and> search_placeable (search_project s')" if ms: "s' |\<in>| search_solution_successors P r q gM ?M Ws"
    by (rule search_solution_successors_with(2)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
      and proj = search_project and st = ?st, OF r at g _ ms[unfolded search_solution_successors_def]])
      (rule search_bind_solution_alternative[OF r pl at g]; assumption)
qed

subsection \<open>The successors\<close>

text \<open>
  A goal is read as it stands in the shared state: a call is closed by a reusable node or expanded by the shared
  unifier's alternatives, and a material goal by its solutions' shared alternatives; only the material pattern is read
  plain, as the material resolution reads it.
\<close>

text \<open>
  The successors over an access, a wrapping of the closed goal's state and a bind at the goal's position (task 903,
  D1b), stated once: where the access's reuse test is R3's, the closed state and every alternative's bound state are
  invariant and present R3's states of a state the caller names, the successors present R3's successors of that
  state. Today's successors are the instance at the search's access, no wrapping and @{text search_bind}.
\<close>

definition search_successors_with :: "(('a,'s,'d,'c) shared_goal_entry,'n,'k,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search \<Rightarrow> 'r) \<Rightarrow>
    ('s list \<Rightarrow> (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable shared_pattern) list \<Rightarrow>
      ('a,'s,'d,'c) shared_search \<Rightarrow> 'r) \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> 'r fset" where
  "search_successors_with V \<rho> \<beta> P r h = (case shared_entry_goal h of
      Shared_Call_Goal q rr d gp \<Rightarrow> if access_reusable V h then {|\<rho> (search_remove_goal q r)|}
        else search_call_successors_with (\<beta> q) P r q d gp
    | Shared_Material_Goal q rr gM \<Rightarrow> (let M = shared_material_project (search_table r) gM in
        case finite_material_resolution M of Material_Waits \<Rightarrow> {||}
        | Material_Solutions Ws \<Rightarrow> search_solution_successors_with (\<beta> q) P r q gM M Ws))"

theorem search_successors_with:
  assumes r: "search_formed \<kappa> P r"
    and at: "RBT.lookup (shared_goals (search_state r)) (shared_goal_position (shared_entry_goal h)) = Some h"
    and reuse: "\<And>q rr d gp. shared_entry_goal h = Shared_Call_Goal q rr d gp \<Longrightarrow>
      access_reusable V h \<longleftrightarrow> finite_reusable st (Resolution_Call_Goal q rr d (shared_pattern_project (search_table r) gp))"
    and closed: "\<And>q rr d gp. shared_entry_goal h = Shared_Call_Goal q rr d gp \<Longrightarrow> access_reusable V h \<Longrightarrow>
      F (\<rho> (search_remove_goal q r)) \<and>
      proj (\<rho> (search_remove_goal q r)) = finite_goal_closed st (Resolution_Call_Goal q rr d (shared_pattern_project (search_table r) gp))"
    and call: "\<And>q rr d gp i c S s. shared_entry_goal h = Shared_Call_Goal q rr d gp \<Longrightarrow>
      (i,c,S,s) |\<in>| shared_call_alternatives P
        (shared_sharing (search_state (search_reshare (search_call_grounds P q d) r))) q d gp \<Longrightarrow>
      ((d,c),S) |\<in>| finite_system_clauses P \<Longrightarrow>
      shared_bindings_formed (search_table (search_reshare (search_call_grounds P q d) r)) s \<Longrightarrow>
      F (\<beta> q s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) \<and>
      proj (\<beta> q s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) =
        finite_call_alternative_state st q rr d (shared_pattern_project (search_table r) gp)
          (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q d) r)) s)"
    and material: "\<And>q rr gM Ws E s. shared_entry_goal h = Shared_Material_Goal q rr gM \<Longrightarrow>
      (E,s) |\<in>| shared_solution_alternatives
        (shared_sharing (search_state (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)))
        gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow>
      shared_bindings_formed
        (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s \<Longrightarrow>
      F (\<beta> q s (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) \<and>
      proj (\<beta> q s (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r))) =
        finite_material_alternative_state st q rr (shared_material_project (search_table r) gM)
          (E, shared_bindings_project
            (search_table (search_reshare (solution_grounds Ws (shared_material_project (search_table r) gM)) r)) s)"
  shows "fimage proj (search_successors_with V \<rho> \<beta> P r h) =
      finite_goal_successors P st (shared_goal_project (search_table r) (shared_entry_goal h))"
    and "s' |\<in>| search_successors_with V \<rho> \<beta> P r h \<Longrightarrow> F s'"
proof -
  let ?T = "search_table r"
  show "fimage proj (search_successors_with V \<rho> \<beta> P r h) =
      finite_goal_successors P st (shared_goal_project ?T (shared_entry_goal h))"
  proof (cases "shared_entry_goal h")
    case (Shared_Call_Goal q rr d gp)
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Call_Goal by simp
    have C1: "fimage proj (search_call_successors_with (\<beta> q) P r q d gp) =
        fimage (finite_call_alternative_state st q rr d (shared_pattern_project ?T gp))
          (finite_call_alternative_set P q d (shared_pattern_project ?T gp))"
      by (rule search_call_successors_with(1)[where F = F, OF r atq Shared_Call_Goal])
        (rule call[OF Shared_Call_Goal]; assumption)
    show ?thesis
    proof (cases "access_reusable V h")
      case True
      then show ?thesis using reuse[OF Shared_Call_Goal] closed[OF Shared_Call_Goal True] Shared_Call_Goal
        by (simp add: search_successors_with_def)
    next
      case False
      then show ?thesis using reuse[OF Shared_Call_Goal] C1 Shared_Call_Goal
        by (simp add: search_successors_with_def finite_call_successors_alternatives)
    qed
  next
    case (Shared_Material_Goal q rr gM)
    let ?M = "shared_material_project ?T gM"
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Material_Goal by simp
    have e: "fimage proj (search_successors_with V \<rho> \<beta> P r h) =
        fimage (finite_material_alternative_state st q rr ?M) (finite_material_alternative_set ?M)"
    proof (cases "finite_material_resolution ?M")
      case Material_Waits
      then show ?thesis by (simp add: search_successors_with_def Shared_Material_Goal Let_def finite_material_alternative_set_def)
    next
      case (Material_Solutions Ws)
      have D1: "fimage proj (search_solution_successors_with (\<beta> q) P r q gM ?M Ws) =
          fimage (finite_material_alternative_state st q rr ?M) (finite_solution_alternatives ?M Ws)"
        by (rule search_solution_successors_with(1)[where F = F, OF r atq Shared_Material_Goal])
          (rule material[OF Shared_Material_Goal]; assumption)
      show ?thesis using Material_Solutions D1
        by (simp add: search_successors_with_def Shared_Material_Goal Let_def finite_material_alternative_set_def)
    qed
    then show ?thesis by (simp add: Shared_Material_Goal finite_material_successors_alternatives)
  qed
  show "F s'" if s': "s' |\<in>| search_successors_with V \<rho> \<beta> P r h"
  proof (cases "shared_entry_goal h")
    case (Shared_Call_Goal q rr d gp)
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Call_Goal by simp
    show ?thesis
    proof (cases "access_reusable V h")
      case True
      then have "s' = \<rho> (search_remove_goal q r)" using s' Shared_Call_Goal by (simp add: search_successors_with_def)
      then show ?thesis using closed[OF Shared_Call_Goal True] by simp
    next
      case False
      then have "s' |\<in>| search_call_successors_with (\<beta> q) P r q d gp" using s' Shared_Call_Goal
        by (simp add: search_successors_with_def)
      note m = this
      show ?thesis
        by (rule search_call_successors_with(2)[where F = F and proj = proj and st = st, OF r atq Shared_Call_Goal _ m])
          (rule call[OF Shared_Call_Goal]; assumption)
    qed
  next
    case (Shared_Material_Goal q rr gM)
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Material_Goal by simp
    obtain Ws where m: "s' |\<in>| search_solution_successors_with (\<beta> q) P r q gM (shared_material_project ?T gM) Ws"
      using s' Shared_Material_Goal by (auto simp: search_successors_with_def Let_def split: finite_material_outcome.splits)
    show ?thesis
      by (rule search_solution_successors_with(2)[where F = F and proj = proj and st = st, OF r atq Shared_Material_Goal _ m])
        (rule material[OF Shared_Material_Goal]; assumption)
  qed
qed

definition search_successors :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) shared_search fset" where
  "search_successors \<kappa> P r h = search_successors_with (shared_access \<kappa> P r) id (\<lambda>q. search_bind P) P r h"

lemma search_successors_cases:
  "search_successors \<kappa> P r h = (case shared_entry_goal h of
      Shared_Call_Goal q rr d gp \<Rightarrow> if access_reusable (shared_access \<kappa> P r) h then {|search_remove_goal q r|}
        else search_call_successors P r q d gp
    | Shared_Material_Goal q rr gM \<Rightarrow> (let M = shared_material_project (search_table r) gM in
        case finite_material_resolution M of Material_Waits \<Rightarrow> {||}
        | Material_Solutions Ws \<Rightarrow> search_solution_successors P r q gM M Ws))"
  unfolding search_successors_def search_successors_with_def search_call_successors_def search_solution_successors_def id_def
  by (rule refl)

theorem search_solution_successors:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)"
    and at: "RBT.lookup (shared_goals (search_state r)) q = Some h"
    and g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
  shows "fimage search_project (search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws) =
      fimage (finite_material_alternative_state (search_project r) q rr (shared_material_project (search_table r) gM))
        (finite_solution_alternatives (shared_material_project (search_table r) gM) Ws)"
    and "s' |\<in>| search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws \<Longrightarrow>
      search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
  by (rule search_solution_successors_classed[OF r pl at g])+

theorem search_successors_classed:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
  shows "fimage search_project (search_successors \<kappa> P r h) =
      finite_goal_successors P (search_project r) (access_goal (shared_access \<kappa> P r) h)"
    and "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
    and "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
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
  show "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
  proof -
    assume s': "s' |\<in>| search_successors \<kappa> P r h" and K: "search_classes_formed r"
    show ?thesis
    proof (cases "shared_entry_goal h")
      case (Shared_Call_Goal q rr d gp)
      have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Call_Goal by simp
      show ?thesis
      proof (cases "access_reusable (shared_access \<kappa> P r) h")
        case True
        then have "s' = search_remove_goal q r" using s' Shared_Call_Goal by (simp add: search_successors_cases)
        then show ?thesis using search_remove_goal_classes[OF r K atq] by simp
      next
        case False
        then have "s' |\<in>| search_call_successors P r q d gp" using s' Shared_Call_Goal by (simp add: search_successors_cases)
        then show ?thesis using search_call_successors_classed(3)[OF r pl sock atq Shared_Call_Goal] K by blast
      qed
    next
      case (Shared_Material_Goal q rr gM)
      have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at Shared_Material_Goal by simp
      obtain Ws where "s' |\<in>| search_solution_successors P r q gM (shared_material_project (search_table r) gM) Ws"
        using s' Shared_Material_Goal
        by (auto simp: search_successors_cases Let_def split: finite_material_outcome.splits)
      then show ?thesis using search_solution_successors_classed(3)[OF r pl atq Shared_Material_Goal] K by blast
    qed
  qed
  have reuse: "access_reusable (shared_access \<kappa> P r) h \<longleftrightarrow>
      finite_reusable ?st (Resolution_Call_Goal q rr d (shared_pattern_project ?T gp))"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr d gp" for q rr d gp
    using reusable[OF h] g by (simp add: shared_access_simps)
  have closed_id: "(search_formed \<kappa> P (id (search_remove_goal q r)) \<and> search_placeable (search_project (id (search_remove_goal q r)))) \<and>
      search_project (id (search_remove_goal q r)) =
        finite_goal_closed ?st (Resolution_Call_Goal q rr d (shared_pattern_project ?T gp))"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr d gp" and "access_reusable (shared_access \<kappa> P r) h" for q rr d gp
  proof -
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at g by simp
    have gq: "shared_goal_project ?T (shared_entry_goal h) = Resolution_Call_Goal q rr d (shared_pattern_project ?T gp)"
      using g by simp
    show ?thesis using closed_ok[OF atq gq] closed[OF atq gq] by simp
  qed
  have call: "(search_formed \<kappa> P (search_bind P s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) \<and>
      search_placeable (search_project (search_bind P s
        (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)))) \<and>
    search_project (search_bind P s (search_call_place P (search_reshare (search_call_grounds P q d) r) q d c S)) =
      finite_call_alternative_state ?st q rr d (shared_pattern_project ?T gp)
        (i,c,S,shared_bindings_project (search_table (search_reshare (search_call_grounds P q d) r)) s)"
    if g: "shared_entry_goal h = Shared_Call_Goal q rr d gp" and cl: "((d,c),S) |\<in>| finite_system_clauses P"
      and sf: "shared_bindings_formed (search_table (search_reshare (search_call_grounds P q d) r)) s" for q rr d gp i c S s
  proof -
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at g by simp
    show ?thesis by (rule search_bind_call_alternative[OF r pl sock atq g cl sf])
  qed
  have mat: "(search_formed \<kappa> P (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) r))) \<and>
      search_placeable (search_project (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) r))))) \<and>
    search_project (search_bind P s
        (search_remove_goal q (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) r))) =
      finite_material_alternative_state ?st q rr (shared_material_project ?T gM)
        (E, shared_bindings_project (search_table (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) r)) s)"
    if g: "shared_entry_goal h = Shared_Material_Goal q rr gM"
      and sf: "shared_bindings_formed (search_table (search_reshare (solution_grounds Ws (shared_material_project ?T gM)) r)) s"
    for q rr gM Ws E s
  proof -
    have atq: "RBT.lookup (shared_goals (search_state r)) q = Some h" using at g by simp
    show ?thesis by (rule search_bind_solution_alternative[OF r pl atq g sf])
  qed
  have W1: "fimage search_project (search_successors_with (shared_access \<kappa> P r) id (\<lambda>q. search_bind P) P r h) =
      finite_goal_successors P ?st (shared_goal_project ?T (shared_entry_goal h))"
    by (rule search_successors_with(1)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')",
      OF r at]) ((rule reuse; assumption), (rule closed_id; assumption), (rule call; assumption), (rule mat; assumption))
  show "fimage search_project (search_successors \<kappa> P r h) = finite_goal_successors P ?st (access_goal (shared_access \<kappa> P r) h)"
    using W1 by (simp add: search_successors_def shared_access_simps)
  show "search_formed \<kappa> P s' \<and> search_placeable (search_project s')" if s': "s' |\<in>| search_successors \<kappa> P r h"
    by (rule search_successors_with(2)[where F = "\<lambda>s'. search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
      and proj = search_project and st = ?st, OF r at _ _ _ _ s'[unfolded search_successors_def]])
      ((rule reuse; assumption), (rule closed_id; assumption), (rule call; assumption), (rule mat; assumption))
qed

theorem search_successors:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
  shows "fimage search_project (search_successors \<kappa> P r h) =
      finite_goal_successors P (search_project r) (access_goal (shared_access \<kappa> P r) h)"
    and "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s')"
  by (rule search_successors_classed[OF r pl sock h])+

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
      (RBT.entries (shared_goals s)) RBT.empty, search_values = RBT.empty,
     search_classes = classes_update (map fst (RBT.entries (shared_goals s))) s empty_classes,
     search_calls = [], search_index = RBT.empty, search_closed = RBT.empty\<rparr>)"

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
  have cf: "search_closing_formed (search_of P st)"
    by (simp add: search_closing_formed_def calls_indexed_def search_closes_def search_of_def Let_def split: option.split)
  show "search_formed \<kappa> P (search_of P st)" using s rf vf cf by (simp add: search_formed_def search_of_def Let_def)
  show "search_project (search_of P st) = st" using p by (simp add: search_of_def Let_def)
qed

lemma search_of_classes:
  assumes d: "resolution_positions_distinct st"
  shows "search_classes_formed (search_of P st)"
proof -
  have none: "RBT.lookup t p = None" if "p \<notin> set (map fst (RBT.entries t))" for t :: "('x::linorder,'y) rbt" and p
    using that by (cases "RBT.lookup t p") (force simp: RBT.lookup_in_tree)+
  have "classes_formed (search_state (search_of P st))
      (classes_update (map fst (RBT.entries (shared_goals (search_state (search_of P st))))) (search_state (search_of P st))
        empty_classes)"
    by (rule classes_update_formed[OF search_of(1)[OF d]]) (simp add: none empty_classes_def class_value_def)
  then show ?thesis by (simp add: search_of_def Let_def)
qed

definition shared_representation :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) resolution_representation" where
  "shared_representation \<kappa> P = \<lparr>rep_access = shared_access \<kappa> P, rep_empty = (\<lambda>r. RBT.is_empty (shared_goals (search_state r))),
    rep_project = (\<lambda>r. search_project r), rep_refresh = search_refresh \<kappa> P, rep_construct = search_construct \<kappa> P,
    rep_successors = search_successors \<kappa> P\<rparr>"

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
  then show ?thesis using search_of(2)[OF d] by (simp add: finite_resolution_search_def finite_resolution_search_in_def shared_representation_def)
qed

text \<open>
  R3's search is computed over the shared state where R3's search keeps one goal and one node at a position, and over
  F2b1's indexed state elsewhere; the two coincide with R3's, so the equation holds at every input, at the search's
  general type.
\<close>

section \<open>The selection over the kept classes\<close>

text \<open>
  The selection reads the kept classes (task 865): the first settled goal, else the goals the priority names among the
  candidates, else the first single goal, each first in the order of positions and outside the goals held back, and only
  then the waiting rule over every goal not held back (@{thm [source] access_goal_choice_classes}). The goals held back
  are found through the registered index: only a registered position whose node leaves a registered variable free can
  hold a goal back, and a goal holding such a variable is in that position's bucket (@{text search_held}). The
  construction nodes are read as the access reads them. At every formed search with formed classes the selection is
  the access's (@{text search_select}), at every priority.
\<close>

definition search_held_over :: "(('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry, nat, 'a, 's, 'd, 'c)
    search_access \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset" where
  "search_held_over V r = ffUnion (fimage (\<lambda>p.
      if fBex (access_nodes_at V p) (\<lambda>n. access_free V n \<noteq> {||})
      then ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (ffUnion (fimage (access_goals_at V) (tree_bucket (search_registered r) p)))
      else {||}) (fset_of_list (map fst (RBT.entries (search_registered r)))))"

text \<open>The goals held back are read over the search's access, so a selection that holds it reads them over it once.\<close>

definition search_held :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset" where
  "search_held \<kappa> P r = search_held_over (shared_access \<kappa> P r) r"

text \<open>
  The goals held back read of the nodes only what the access they are read over reads of them: over an access that
  reads the search's goals, positions and indexes as the search's own access does, whatever it reads of the nodes, they
  are the goals the access holds back (task 903: the deferred search reads its nodes through a store). The search's own
  access is the instance at its own node fields.
\<close>

lemma access_node_fields_self:
  "V\<lparr>access_node := access_node V, access_free := access_free V, access_value_none := access_value_none V,
    access_call_variables := access_call_variables V\<rparr> = V"
  by (cases V) simp

lemma search_held_over_nodes:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  shows "search_held_over V r = ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
proof (rule fset_eqI)
  let ?G = "shared_goals (search_state r)"
  have reg: "search_registered_formed r" using search_formedD(2)[OF r] .
  fix h
  show "h |\<in>| search_held_over V r \<longleftrightarrow> h |\<in>| ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
  proof
    assume "h |\<in>| search_held_over V r"
    then obtain p where "h |\<in>| ffilter (\<lambda>h. access_holdable V h \<and> access_held V h)
        (ffUnion (fimage (access_goals_at V) (tree_bucket (search_registered r) p)))"
      by (auto simp: search_held_over_def Let_def ffUnion.rep_eq fimage.rep_eq split: if_splits)
    then show "h |\<in>| ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
      by (auto simp: V_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq shared_access_simps tree_values_member
          option_fset_def split: option.splits)
  next
    assume "h |\<in>| ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
    then have hg: "h |\<in>| access_goals V" and ho: "access_holdable V h" and hh: "access_held V h"
      by (simp_all add: ffilter.rep_eq)
    obtain x where x: "x |\<in>| access_variables V h" "snd (fst x)"
      and nx: "fBex (access_nodes_at V (fst (fst x))) (\<lambda>n. snd x |\<in>| access_free V n)"
      using hh by (auto simp: access_held_def)
    obtain q where q: "RBT.lookup ?G q = Some h" using hg by (auto simp: V_def shared_access_simps tree_values_member)
    have "fst (fst x) |\<in>| shared_goal_registered h"
      using x by (cases x) (auto simp: V_def shared_goal_registered_member shared_access_simps)
    then have qb: "q |\<in>| tree_bucket (search_registered r) (fst (fst x))" using reg q by (simp add: search_registered_formed_def)
    then have key: "fst (fst x) \<in> set (map fst (RBT.entries (search_registered r)))"
      by (cases "RBT.lookup (search_registered r) (fst (fst x))") (force simp: tree_bucket_def RBT.lookup_in_tree)+
    have ne: "fBex (access_nodes_at V (fst (fst x))) (\<lambda>n. access_free V n \<noteq> {||})" using nx by blast
    have "h |\<in>| ffilter (\<lambda>h. access_holdable V h \<and> access_held V h)
        (ffUnion (fimage (access_goals_at V) (tree_bucket (search_registered r) (fst (fst x)))))"
      using qb q ho hh by (force simp: V_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq shared_access_simps)
    then show "h |\<in>| search_held_over V r"
      using key ne by (force simp: search_held_over_def Let_def ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq)
  qed
qed

lemma search_held:
  assumes r: "search_formed \<kappa> P r"
  shows "search_held \<kappa> P r = ffilter (\<lambda>h. access_holdable (shared_access \<kappa> P r) h \<and> access_held (shared_access \<kappa> P r) h)
    (access_goals (shared_access \<kappa> P r))"
  using search_held_over_nodes[OF r, where N = "access_node (shared_access \<kappa> P r)" and Fr = "access_free (shared_access \<kappa> P r)"
      and VN = "access_value_none (shared_access \<kappa> P r)" and C = "access_call_variables (shared_access \<kappa> P r)"]
  by (simp only: access_node_fields_self search_held_def)

definition class_first :: "'e fset \<Rightarrow> ('k::linorder,'e) rbt \<Rightarrow> 'e fset" where
  "class_first H t = (case find (\<lambda>h. h |\<notin>| H) (map snd (RBT.entries t)) of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})"

lemma finite_position_less_list: "finite_position_less p q \<longleftrightarrow> p < q"
  by (simp add: finite_position_less_def list_less_def)

lemma class_tree_member:
  assumes t: "\<And>p. RBT.lookup t p = class_value Q G p"
  shows "h \<in> set (map snd (RBT.entries t)) \<longleftrightarrow> h |\<in>| tree_values G \<and> Q h"
proof -
  have "h \<in> set (map snd (RBT.entries t)) \<longleftrightarrow> (\<exists>p. RBT.lookup t p = Some h)" by (force simp: RBT.lookup_in_tree)
  also have "\<dots> \<longleftrightarrow> (\<exists>p. RBT.lookup G p = Some h \<and> Q h)" using t by (auto simp: class_value_def split: option.splits)
  also have "\<dots> \<longleftrightarrow> h |\<in>| tree_values G \<and> Q h" by (auto simp: tree_values_member)
  finally show ?thesis .
qed

text \<open>A class's tree lists its goals in the order of their positions, so its first goal outside a set is read at once.\<close>

lemma class_first:
  assumes t: "\<And>p. RBT.lookup t p = class_value Q G p" and pos: "\<And>p h. RBT.lookup G p = Some h \<Longrightarrow> pos h = p"
  shows "positioned_first pos (ffilter Q (tree_values G |-| H)) = class_first H t"
    and "class_first H t = {||} \<longleftrightarrow> ffilter Q (tree_values G |-| H) = {||}"
proof -
  let ?E = "RBT.entries t"
  have E: "map (\<lambda>z. pos (snd z)) ?E = map fst ?E"
  proof (rule map_cong[OF refl])
    fix z assume z: "z \<in> set ?E"
    obtain k v where zz: "z = (k,v)" by (cases z)
    have "RBT.lookup t k = Some v" using z zz by (simp add: RBT.lookup_in_tree)
    then have "RBT.lookup G k = Some v" using t[of k] by (auto simp: class_value_def split: option.splits if_splits)
    then show "pos (snd z) = fst z" using pos zz by simp
  qed
  have so: "sorted_wrt (<) (map fst ?E)" using RBT.sorted_entries[of t] RBT.distinct_entries[of t] by (simp add: strict_sorted_iff)
  have "sorted_wrt (<) (map (\<lambda>z. pos (snd z)) ?E)" unfolding E by (rule so)
  then have sw: "sorted_wrt (\<lambda>x y. finite_position_less (pos x) (pos y)) (map snd ?E)"
    by (simp add: sorted_wrt_map finite_position_less_list)
  have f: "fset_of_list (filter (\<lambda>h. h |\<notin>| H) (map snd ?E)) = ffilter Q (tree_values G |-| H)"
    by (rule fset_eqI) (use class_tree_member[OF t] in \<open>auto simp: fset_of_list.rep_eq ffilter.rep_eq\<close>)
  show "positioned_first pos (ffilter Q (tree_values G |-| H)) = class_first H t"
    using positioned_first_sorted[OF sw, of "\<lambda>h. h |\<notin>| H"] f by (simp add: class_first_def)
  have "class_first H t = {||} \<longleftrightarrow> find (\<lambda>h. h |\<notin>| H) (map snd ?E) = None"
    by (cases "find (\<lambda>h. h |\<notin>| H) (map snd ?E)") (simp_all add: class_first_def)
  also have "\<dots> \<longleftrightarrow> fset_of_list (filter (\<lambda>h. h |\<notin>| H) (map snd ?E)) = {||}"
    by (auto simp: find_None_iff fset_eq_iff fset_of_list.rep_eq)
  also have "\<dots> \<longleftrightarrow> ffilter Q (tree_values G |-| H) = {||}" by (simp only: f)
  finally show "class_first H t = {||} \<longleftrightarrow> ffilter Q (tree_values G |-| H) = {||}" .
qed

text \<open>
  A class's first goal outside a set is read along the tree, left to right, stopping at the first: the class is not
  listed.
\<close>

fun rbt_first_value :: "('e \<Rightarrow> bool) \<Rightarrow> ('k,'e) RBT_Impl.rbt \<Rightarrow> 'e option" where
  "rbt_first_value Q RBT_Impl.Empty = None"
| "rbt_first_value Q (RBT_Impl.Branch c l k v r) = (case rbt_first_value Q l of Some h \<Rightarrow> Some h
    | None \<Rightarrow> if Q v then Some v else rbt_first_value Q r)"

lemma rbt_first_value_find: "rbt_first_value Q t = find Q (map snd (RBT_Impl.entries t))"
proof -
  have app: "find Q (xs @ ys) = (case find Q xs of None \<Rightarrow> find Q ys | Some x \<Rightarrow> Some x)" for xs ys
    by (induction xs) auto
  show ?thesis by (induction t) (simp_all add: app split: option.split)
qed

lemma class_first_code [code]:
  "class_first H t = (case rbt_first_value (\<lambda>h. h |\<notin>| H) (RBT.impl_of t) of None \<Rightarrow> {||} | Some h \<Rightarrow> {|h|})"
  by (simp add: class_first_def rbt_first_value_find RBT.entries.rep_eq)

text \<open>
  The kept selection at a priority given as a class of the candidates (task 871, moved here by task 891): the
  construction nodes as the access reads them, then the first settled goal, the goals the class names among the
  candidates, the first single goal and the waiting rule over every goal not held back, the goals held back read over
  the access it is given (@{text search_held_over}), so that the access is built once. The plain selection is its
  instance at the class a test's filter makes (@{text search_select}); the committed route's selection at the whole
  focus is too (@{text Factor_Shared_Commitments}).
\<close>

definition kept_select_by :: "(('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "kept_select_by pc r V = (let N = access_construction_nodes V in
    if N \<noteq> {||} then Access_Construction (access_first_nodes V N)
    else let H = search_held_over V r; K = search_classes r; c0 = class_first H (class_settled K);
      S = (if c0 \<noteq> {||} then c0 else
        let cp = pc (fset_of_list (map snd (RBT.entries (class_candidates K))) |-| H) in
        if cp \<noteq> {||} then access_first_goals V cp else
        let c1 = class_first H (class_single K) in
        if c1 \<noteq> {||} then c1 else access_waiting_selection V (access_goals V |-| H)) in
      if S = {||} then Access_None else Access_Goals S)"

definition search_select :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "search_select \<kappa> P rp r = kept_select_by (ffilter rp) r (shared_access \<kappa> P r)"

text \<open>
  The kept selection reads the classes, the goals held back and the access: over an access differing from the search's
  own only in what it reads of the nodes it is that access's selection (task 903), the search's own selection its
  instance.
\<close>

text \<open>
  The first class at a table (task 876): the settled goals and the goals the table closes, each kept as a class by
  position; the first of the two is the first of their union. The kept selection at the empty closed class is
  today's (@{text kept_select_by_in_empty}).
\<close>

lemma positioned_first_least:
  fixes pos :: "'x \<Rightarrow> 's::linorder list"
  shows "h |\<in>| positioned_first pos A \<longleftrightarrow> h |\<in>| A \<and> fBall A (\<lambda>h'. pos h \<le> pos h')"
  by (auto simp: positioned_first_def ffilter.rep_eq finite_position_less_list not_less)

lemma positioned_first_exists:
  fixes pos :: "'x \<Rightarrow> 's::linorder list"
  assumes y: "y |\<in>| A"
  shows "\<exists>m. m |\<in>| positioned_first pos A \<and> pos m \<le> pos y"
proof -
  have fin: "finite (pos ` fset A)" by simp
  have ne: "pos ` fset A \<noteq> {}" using y by auto
  obtain m where m: "m |\<in>| A" "pos m = Min (pos ` fset A)" using Min_in[OF fin ne] by auto
  have le: "pos m \<le> pos h'" if "h' |\<in>| A" for h' using m(2) Min_le[OF fin, of "pos h'"] that by auto
  show ?thesis using m(1) le le[OF y] by (auto simp: positioned_first_least)
qed

lemma positioned_first_empty_iff:
  fixes pos :: "'x \<Rightarrow> 's::linorder list"
  shows "positioned_first pos A = {||} \<longleftrightarrow> A = {||}"
proof
  assume e: "positioned_first pos A = {||}"
  have "\<not> y |\<in>| A" for y
  proof
    assume "y |\<in>| A"
    then obtain m where "m |\<in>| positioned_first pos A" using positioned_first_exists[of y A pos] by blast
    then show False using e by simp
  qed
  then show "A = {||}" by (simp add: fset_eq_iff)
qed (auto simp: positioned_first_def fset_eq_iff ffilter.rep_eq)

lemma positioned_first_union:
  fixes pos :: "'x \<Rightarrow> 's::linorder list"
  shows "positioned_first pos (positioned_first pos A |\<union>| positioned_first pos B) = positioned_first pos (A |\<union>| B)"
proof (rule fset_eqI)
  fix h
  show "h |\<in>| positioned_first pos (positioned_first pos A |\<union>| positioned_first pos B) \<longleftrightarrow>
      h |\<in>| positioned_first pos (A |\<union>| B)"
  proof
    assume h: "h |\<in>| positioned_first pos (positioned_first pos A |\<union>| positioned_first pos B)"
    then have hm: "h |\<in>| positioned_first pos A |\<union>| positioned_first pos B"
      and low: "\<And>m. m |\<in>| positioned_first pos A |\<union>| positioned_first pos B \<Longrightarrow> pos h \<le> pos m"
      by (auto simp: positioned_first_least)
    have "pos h \<le> pos y" if y: "y |\<in>| A |\<union>| B" for y
    proof -
      obtain m where m: "m |\<in>| positioned_first pos A |\<union>| positioned_first pos B" "pos m \<le> pos y"
        using y positioned_first_exists[of y A pos] positioned_first_exists[of y B pos] by auto
      show ?thesis by (rule order_trans[OF low[OF m(1)] m(2)])
    qed
    then show "h |\<in>| positioned_first pos (A |\<union>| B)" using hm by (auto simp: positioned_first_least)
  next
    assume "h |\<in>| positioned_first pos (A |\<union>| B)"
    then have hm: "h |\<in>| A |\<union>| B" and low: "\<And>y. y |\<in>| A |\<union>| B \<Longrightarrow> pos h \<le> pos y"
      by (auto simp: positioned_first_least)
    have "h |\<in>| positioned_first pos A |\<union>| positioned_first pos B"
      using hm low by (auto simp: positioned_first_least)
    moreover have "pos h \<le> pos m" if "m |\<in>| positioned_first pos A |\<union>| positioned_first pos B" for m
      using that low by (auto simp: positioned_first_least)
    ultimately show "h |\<in>| positioned_first pos (positioned_first pos A |\<union>| positioned_first pos B)"
      by (auto simp: positioned_first_least)
  qed
qed

definition kept_select_by_in :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry fset \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry fset) \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry,('a,'s,'d,'c) shared_node_entry,nat,'a,'s,'d,'c) search_access \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "kept_select_by_in Z pc r V = (let N = access_construction_nodes V in
    if N \<noteq> {||} then Access_Construction (access_first_nodes V N)
    else let H = search_held_over V r; K = search_classes r;
      c0 = access_first_goals V (class_first H (class_settled K) |\<union>| class_first H Z);
      S = (if c0 \<noteq> {||} then c0 else
        let cp = pc (fset_of_list (map snd (RBT.entries (class_candidates K))) |-| H) in
        if cp \<noteq> {||} then access_first_goals V cp else
        let c1 = class_first H (class_single K) in
        if c1 \<noteq> {||} then c1 else access_waiting_selection V (access_goals V |-| H)) in
      if S = {||} then Access_None else Access_Goals S)"

lemma kept_select_by_in_empty: "kept_select_by_in RBT.empty pc r V = kept_select_by pc r V"
proof -
  have f: "access_first_goals V (class_first H t) = class_first H t" for H t
    by (cases "find (\<lambda>h. h |\<notin>| H) (map snd (RBT.entries t))")
      (auto simp: class_first_def access_first_goals_def positioned_first_def ffilter.rep_eq fset_eq_iff
        finite_position_less_list)
  have e: "class_first H RBT.empty = {||}" for H by (simp add: class_first_code RBT.empty.rep_eq)
  show ?thesis by (simp add: kept_select_by_in_def kept_select_by_def e f Let_def)
qed

theorem kept_select_over_in:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
    and Z: "\<And>p. RBT.lookup Z p = class_value E (shared_goals (search_state r)) p"
    and EC: "\<And>h. E h \<Longrightarrow> shared_goal_is_call (shared_entry_goal h)"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  shows "kept_select_by_in Z (ffilter rp) r V = access_select_in E rp V"
proof -
  let ?V = V and ?s = "search_state r" and ?K = "search_classes r"
  let ?G = "shared_goals ?s" and ?H = "search_held_over V r"
  have s: "shared_state_formed \<kappa> P ?s" using search_formedD(1)[OF r] .
  have goals: "access_goals ?V = tree_values ?G" by (simp add: V_def shared_access_simps)
  have pos: "access_goal_position ?V h = p" if "RBT.lookup ?G p = Some h" for p h
    using shared_goal_lookup_position[OF s that] by (simp add: V_def shared_access_simps)
  have held: "?H = ffilter (\<lambda>h. access_holdable V h \<and> access_held V h) (access_goals V)"
    unfolding V_def by (rule search_held_over_nodes[OF r])
  have A: "ffilter (\<lambda>h. \<not> (access_holdable ?V h \<and> access_held ?V h)) (access_goals ?V) = access_goals ?V |-| ?H"
    unfolding held by (rule fset_eqI) (auto simp: ffilter.rep_eq)
  have tst: "access_candidate ?V h = access_candidate (state_access ?s) h \<and>
      access_settled ?V h = access_settled (state_access ?s) h \<and> access_single ?V h = access_single (state_access ?s) h" for h
    by (simp add: V_def shared_access_def Let_def access_candidate_def access_settled_def access_single_def
      access_pruned_def access_pruned_among_def access_reusable_def access_waits_def access_ground_def)
  have kk: "RBT.lookup (class_candidates ?K) p = class_value (access_candidate ?V) ?G p \<and>
      RBT.lookup (class_settled ?K) p = class_value (\<lambda>h. access_candidate ?V h \<and> access_settled ?V h) ?G p \<and>
      RBT.lookup (class_single ?K) p = class_value (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) ?G p" for p
  proof (cases "RBT.lookup ?G p")
    case None
    then show ?thesis using K by (simp add: classes_formed_def class_value_def)
  next
    case (Some h)
    then show ?thesis using K kept_tests[OF r Some] tst[of h] by (simp add: classes_formed_def class_value_def)
  qed
  have tc: "\<And>p. RBT.lookup (class_candidates ?K) p = class_value (access_candidate ?V) ?G p" using kk by simp
  have t0: "\<And>p. RBT.lookup (class_settled ?K) p = class_value (\<lambda>h. access_candidate ?V h \<and> access_settled ?V h) ?G p"
    using kk by simp
  have t1: "\<And>p. RBT.lookup (class_single ?K) p = class_value (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) ?G p"
    using kk by simp
  note c0 = class_first[OF t0 pos, where H = "search_held_over V r"]
    and c1 = class_first[OF t1 pos, where H = "search_held_over V r"]
    and cz = class_first[OF Z pos, where H = "search_held_over V r"]
  have e0: "class_first ?H (class_settled ?K) =
      access_first_goals ?V (ffilter (\<lambda>h. access_candidate ?V h \<and> access_settled ?V h) (access_goals ?V |-| ?H))"
    using c0(1) goals by (simp add: access_first_goals_def)
  have ez: "class_first ?H Z = access_first_goals ?V (ffilter E (access_goals ?V |-| ?H))"
    using cz(1) goals by (simp add: access_first_goals_def)
  have e1: "class_first ?H (class_single ?K) =
      access_first_goals ?V (ffilter (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) (access_goals ?V |-| ?H))"
    using c1(1) goals by (simp add: access_first_goals_def)
  have n1: "access_first_goals ?V (ffilter (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) (access_goals ?V |-| ?H)) = {||}
      \<longleftrightarrow> ffilter (\<lambda>h. access_candidate ?V h \<and> access_single ?V h) (access_goals ?V |-| ?H) = {||}"
    using c1 goals by (simp add: access_first_goals_def)
  have cand: "access_candidate ?V h" if "E h" for h
    using EC[OF that] by (simp add: V_def access_candidate_def shared_access_simps)
  have un: "ffilter (\<lambda>h. access_candidate ?V h \<and> (access_settled ?V h \<or> E h)) (access_goals ?V |-| ?H) =
      ffilter (\<lambda>h. access_candidate ?V h \<and> access_settled ?V h) (access_goals ?V |-| ?H) |\<union>| ffilter E (access_goals ?V |-| ?H)"
    using cand by (auto simp: ffilter.rep_eq)
  have u0: "access_first_goals ?V (class_first ?H (class_settled ?K) |\<union>| class_first ?H Z) =
      access_first_goals ?V (ffilter (\<lambda>h. access_candidate ?V h \<and> (access_settled ?V h \<or> E h)) (access_goals ?V |-| ?H))"
    unfolding e0 ez un access_first_goals_def by (rule positioned_first_union)
  have fe: "access_first_goals ?V X = {||} \<longleftrightarrow> X = {||}" for X
    unfolding access_first_goals_def by (rule positioned_first_empty_iff)
  have ecp: "fset_of_list (map snd (RBT.entries (class_candidates ?K))) |-| ?H =
      ffilter (access_candidate ?V) (access_goals ?V |-| ?H)"
    by (rule fset_eqI) (use class_tree_member[OF tc] in \<open>auto simp: fset_of_list.rep_eq ffilter.rep_eq goals\<close>)
  have ch: "access_goal_choice_in E rp ?V (access_goals ?V |-| ?H) =
      (if access_first_goals ?V (class_first ?H (class_settled ?K) |\<union>| class_first ?H Z) \<noteq> {||}
         then access_first_goals ?V (class_first ?H (class_settled ?K) |\<union>| class_first ?H Z)
       else if ffilter rp (ffilter (access_candidate ?V) (access_goals ?V |-| ?H)) \<noteq> {||}
         then access_first_goals ?V (ffilter rp (ffilter (access_candidate ?V) (access_goals ?V |-| ?H)))
       else if class_first ?H (class_single ?K) \<noteq> {||} then class_first ?H (class_single ?K)
       else access_waiting_selection ?V (access_goals ?V |-| ?H))"
    by (simp only: access_goal_choice_classes_in Let_def u0 fe e1 n1)
  show ?thesis by (simp only: kept_select_by_in_def access_select_in_def Let_def A ecp ch)
qed

theorem kept_select_over:
  fixes N :: "('a,'s::linorder,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) resolution_node"
    and Fr :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a fset"
    and VN :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> 'a \<Rightarrow> bool"
    and C :: "('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('s,'a) resolution_variable fset"
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  defines "V \<equiv> (shared_access \<kappa> P r)\<lparr>access_node := N, access_free := Fr, access_value_none := VN,
    access_call_variables := C\<rparr>"
  shows "kept_select_by (ffilter rp) r V = access_select rp V"
proof -
  have Z: "\<And>p. RBT.lookup RBT.empty p = class_value (\<lambda>h. False) (shared_goals (search_state r)) p"
    by (simp add: class_value_def split: option.split)
  have "kept_select_by_in RBT.empty (ffilter rp) r V = access_select_in (\<lambda>h. False) rp V"
    unfolding V_def by (rule kept_select_over_in[OF r K Z]) simp
  then show ?thesis by (simp only: kept_select_by_in_empty access_select_in_empty)
qed


theorem search_select:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_select \<kappa> P rp r = access_select rp (shared_access \<kappa> P r)"
  using kept_select_over[OF r K, where N = "access_node (shared_access \<kappa> P r)" and Fr = "access_free (shared_access \<kappa> P r)"
      and VN = "access_value_none (shared_access \<kappa> P r)" and C = "access_call_variables (shared_access \<kappa> P r)" and rp = rp]
  by (simp only: access_node_fields_self search_select_def)

theorem shared_kept_search:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
  shows "selected_search (shared_representation \<kappa> P) (search_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of P st) =
      finite_resolution_search \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "shared_representation \<kappa> P"
  let ?F = "\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r) \<and> search_classes_formed r"
  have "selected_search ?R (search_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of P st) =
      represented_search ?R (\<lambda>r h. False) \<kappa> P n (search_of P st)"
  proof (rule selected_search[where F = ?F])
    show "?F (search_of P st)" using search_of[OF d] search_of_classes[OF d] pl by simp
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s)"
      using search_refresh[OF conjunct1[OF f]] search_refresh_classes[of \<kappa> P s] by (simp add: shared_representation_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (shared_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "shared_access \<kappa> P s"] m by (auto simp: shared_representation_def)
    note c = search_construct[OF conjunct1[OF f] n]
    have "search_placeable (search_project (search_construct \<kappa> P s m))"
      unfolding c(2) finite_construction_step_def Let_def
      by (rule search_placeable_substitute, rule search_placeable_witnesses[OF conjunct1[OF conjunct2[OF f]]])
    then show "?F (rep_construct ?R s m)"
      using c(1) search_construct_classes[of \<kappa> P s m] f by (simp add: shared_representation_def)
  next
    fix s h s' assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)" and s': "s' |\<in>| rep_successors ?R s h"
    have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" and s'': "s' |\<in>| search_successors \<kappa> P s h"
      using h s' by (simp_all add: shared_representation_def)
    show "?F s'" using search_successors_classed(2,3)[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] sock h' s''] f
      by simp
  next
    fix s assume f: "?F s"
    show "search_select \<kappa> P (\<lambda>h. False) s = access_select ((\<lambda>r h. False) s) (rep_access ?R s)"
      using search_select[OF conjunct1[OF f] conjunct2[OF conjunct2[OF f]]] by (simp add: shared_representation_def)
  qed
  also have "\<dots> = finite_resolution_search \<kappa> P n st" by (rule shared_search[OF sock pl])
  finally show ?thesis .
qed

text \<open>
  The search over the kept classes is R3's search where R3's search keeps one goal and one node at a position, and
  F2b1's indexed search computes it elsewhere; the equation holds at every input, at the search's general type.
\<close>

declare finite_resolution_search_code [code del]

lemma finite_resolution_search_shared_code [code]:
  "finite_resolution_search \<kappa> P n st = (if clause_sockets_distinct P \<and> search_placeable st
    then selected_search (shared_representation \<kappa> P) (search_select \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of P st)
    else indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st))"
  using shared_kept_search[of P st \<kappa> n] finite_resolution_search_code[of \<kappa> P n st] by simp

export_code finite_resolution_search checking SML

section \<open>The search at a table of certified calls\<close>

text \<open>
  Build GT3 of DECISIONS.md, task 495's entry, the section "The given's calls are decided once" (task 876): the table
  in F2's shared representation. The table's calls are shared into the search's term table once, where the search is
  made (@{text search_of_in}), and indexed by reference; every step keeps the index and the calls as they are, and
  the term table only extends, so the index stays formed (@{const search_closing_formed}, a clause of
  @{const search_formed}). A ground call goal the index closes has one successor, the goal removed; the selection
  reads the table's closing test among the kept classes. The search at a table is R3's at a table, by
  @{thm [source] represented_search_in}; today's search is its instance at the empty table.
\<close>

subsection \<open>The steps keep the table's calls and index\<close>

definition search_frame :: "('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('d \<times> finite_factor_term) list \<times> (nat,'d fset) rbt" where
  "search_frame r = (search_calls r, search_index r)"

lemma fold_value_kept: "(\<And>x t. g (f x t) = g t) \<Longrightarrow> g (fold f xs t) = g t"
  by (induction xs arbitrary: t) simp_all

lemma search_frame_steps [simp]:
  "search_frame (search_update q s' r) = search_frame r"
  "search_frame (search_put_goal q h r) = search_frame r"
  "search_frame (search_remove_goal q r) = search_frame r"
  "search_frame (search_put_node q hn r) = search_frame r"
  "search_frame (search_reshare G r) = search_frame r"
  "search_frame (search_share x r) = search_frame r"
  "search_frame (search_substitute_at P \<sigma> D q r) = search_frame r"
  "search_frame (r\<lparr>search_state := s'\<rparr>) = search_frame r"
  by (simp_all add: search_frame_def search_update_def search_put_goal_def search_remove_goal_def search_put_node_def
    search_reshare_def search_share_def search_substitute_at_def Let_def)

lemma search_frame_folds [simp]:
  "search_frame (search_substitute P \<sigma> D r) = search_frame r"
  "search_frame (search_place_goals P rows r) = search_frame r"
  "search_frame (search_refresh \<kappa> P r) = search_frame r"
proof -
  show "search_frame (search_substitute P \<sigma> D r) = search_frame r"
    unfolding search_substitute_def by (rule fold_value_kept) simp
  show "search_frame (search_place_goals P rows r) = search_frame r"
    unfolding search_place_goals_def by (rule fold_value_kept) simp
  have "search_frame (search_refresh_at \<kappa> P p t) = search_frame t" for p t
    by (simp add: search_refresh_at_def search_frame_def Let_def split: option.split)
  then show "search_frame (search_refresh \<kappa> P r) = search_frame r"
    unfolding search_refresh_def by (rule fold_value_kept)
qed

lemma search_frame_composed [simp]:
  "search_frame (search_substitute_plain P \<tau> D r) = search_frame r"
  "search_frame (search_bind P s r) = search_frame r"
  "search_frame (search_call_place P r q d c S) = search_frame r"
  "search_frame (search_construct \<kappa> P r hn) = search_frame r"
  by (simp_all add: search_substitute_plain_def search_bind_def search_call_place_def search_construct_def Let_def
    split: prod.split)

lemma search_successors_with_frame:
  assumes s': "s' |\<in>| search_successors_with V \<rho> \<beta> P r h"
    and closed: "\<And>q. g (\<rho> (search_remove_goal q r)) = search_frame r"
    and bind: "\<And>q s x. search_frame x = search_frame r \<Longrightarrow> g (\<beta> q s x) = search_frame r"
  shows "g s' = search_frame r"
proof (cases "shared_entry_goal h")
  case (Shared_Call_Goal q rr d gp)
  then show ?thesis using s'
    by (auto simp: search_successors_with_def search_call_successors_with_def Let_def closed bind split: if_splits)
next
  case (Shared_Material_Goal q rr gM)
  show ?thesis
  proof (cases "finite_material_resolution (shared_material_project (search_table r) gM)")
    case Material_Waits
    then show ?thesis using s' Shared_Material_Goal by (simp add: search_successors_with_def)
  next
    case (Material_Solutions Ws)
    then show ?thesis using s' Shared_Material_Goal
      by (auto simp: search_successors_with_def search_solution_successors_with_def Let_def bind)
  qed
qed

lemma search_successors_frame: "s' |\<in>| search_successors \<kappa> P r h \<Longrightarrow> search_frame s' = search_frame r"
  unfolding search_successors_def by (erule search_successors_with_frame) simp_all

subsection \<open>The table's calls shared and indexed once\<close>

text \<open>
  Each call's term is shared into the term table through the keyed sharing, and its site added to the bucket of the
  reference it receives: the bucket tree's update at that key (@{text bucket_tree_updates}). The index is built once,
  where the search at a table is made.
\<close>

fun index_calls :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<Rightarrow> (nat,'d fset) rbt \<Rightarrow> share_state \<times> (nat,'d fset) rbt" where
  "index_calls [] x E = (x,E)"
| "index_calls (z#C) x E = (case keyed_share_term (snd z) x of (i,x') \<Rightarrow> index_calls C x' (tree_bucket_add E i (fst z)))"

lemma index_calls:
  assumes x: "share_state_formed x" and I: "calls_indexed (share_state_table x) E D"
  shows "share_state_formed (fst (index_calls C x E)) \<and>
    table_extends (share_state_table x) (share_state_table (fst (index_calls C x E))) \<and>
    calls_indexed (share_state_table (fst (index_calls C x E))) (snd (index_calls C x E)) (D \<union> set C)"
  using x I
proof (induction C arbitrary: x E D)
  case Nil
  then show ?case by simp
next
  case (Cons z C)
  obtain d t where z: "z = (d,t)" by (cases z)
  obtain i x' where k: "keyed_share_term t x = (i,x')" by (cases "keyed_share_term t x")
  let ?T = "share_state_table x"
  have rep: "keyed_state_represents x ?T" and tf: "table_formed ?T" using Cons.prems(1) by (simp_all add: share_state_formed_def)
  note ke = keyed_share_term_exact[OF rep, of t]
  have i: "i = fst (share_term t ?T)" and rep': "keyed_state_represents x' (snd (share_term t ?T))" using ke k by simp_all
  note se = share_term_exact[OF tf, of t]
  have T': "share_state_table x' = snd (share_term t ?T)" by (rule share_state_table_represents[OF rep'])
  have x': "share_state_formed x'" using rep' se T' by (simp add: share_state_formed_def)
  have ext: "table_extends ?T (share_state_table x')" unfolding table_extends_def T' by (blast intro: share_term_preserves)
  have ref: "reference_term (share_state_table x') i = Some t" using se T' i by simp
  have I0: "calls_indexed (share_state_table x') E D" by (rule calls_indexed_extends[OF Cons.prems(2) ext])
  have I': "calls_indexed (share_state_table x') (tree_bucket_add E i d) (insert (d,t) D)"
    unfolding calls_indexed_def
  proof (intro conjI allI impI)
    fix d' t' assume m: "(d',t') \<in> insert (d,t) D"
    show "\<exists>j. reference_term (share_state_table x') j = Some t' \<and> d' |\<in>| tree_bucket (tree_bucket_add E i d) j"
    proof (cases "(d',t') = (d,t)")
      case True
      then show ?thesis using ref by (intro exI[of _ i]) (simp add: bucket_tree_updates.updated)
    next
      case False
      then have "(d',t') \<in> D" using m by auto
      then obtain j where "reference_term (share_state_table x') j = Some t'" "d' |\<in>| tree_bucket E j"
        using I0 unfolding calls_indexed_def by blast
      then show ?thesis by (intro exI[of _ j]) (auto simp: bucket_tree_updates.updated)
    qed
  next
    fix j d' assume b: "d' |\<in>| tree_bucket (tree_bucket_add E i d) j"
    show "\<exists>t'. reference_term (share_state_table x') j = Some t' \<and> (d',t') \<in> insert (d,t) D"
    proof (cases "j = i \<and> d' = d")
      case True
      then show ?thesis using ref by (intro exI[of _ t]) simp
    next
      case False
      then have "d' |\<in>| tree_bucket E j" using b by (auto simp: bucket_tree_updates.updated split: if_splits)
      then obtain t' where "reference_term (share_state_table x') j = Some t'" "(d',t') \<in> D"
        using I0 unfolding calls_indexed_def by blast
      then show ?thesis by (intro exI[of _ t']) simp
    qed
  qed
  note IH = Cons.IH[OF x' I']
  have e: "index_calls (z#C) x E = index_calls C x' (tree_bucket_add E i d)" by (simp add: z k)
  have s: "insert (d,t) D \<union> set C = D \<union> set (z#C)" by (auto simp: z)
  show ?case unfolding e using IH table_extends_trans[OF ext] s by auto
qed

text \<open>
  The index built from the empty one is the bucket tree (@{const bucket_tree}) of the rows pairing each call's
  reference with its site, so its buckets are the index notion's (@{text bucket_tree_index}).
\<close>

fun index_rows :: "('d \<times> finite_factor_term) list \<Rightarrow> share_state \<Rightarrow> (nat \<times> 'd) list" where
  "index_rows [] x = []"
| "index_rows (z#C) x = (case keyed_share_term (snd z) x of (i,x') \<Rightarrow> (i, fst z) # index_rows C x')"

lemma index_calls_rows:
  "snd (index_calls C x E) = fold (\<lambda>z T. tree_bucket_add T (fst z) (snd z)) (index_rows C x) E"
  by (induction C arbitrary: x E) (simp_all split: prod.split)

lemma index_calls_bucket_tree:
  "snd (index_calls C x RBT.empty) = bucket_tree (index_rows C x)"
  by (simp add: index_calls_rows bucket_tree_def)

lemma index_calls_buckets:
  "d |\<in>| tree_bucket (snd (index_calls C x RBT.empty)) i \<longleftrightarrow> (i,d) \<in> set (index_rows C x)"
  using bucket_tree_index.represents[where c = "index_rows C x" and k = i and v = d] by (simp add: index_calls_bucket_tree)

definition search_attach :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    ('a,'s,'d,'c) shared_search" where
  "search_attach C r = (case index_calls C (shared_sharing (search_state r)) RBT.empty of (x,E) \<Rightarrow>
    let r1 = (search_share x r)\<lparr>search_calls := C, search_index := E\<rparr> in
    r1\<lparr>search_closed := fold (\<lambda>p t. closed_put p (search_state r1) E t) (RBT.keys (shared_goals (search_state r1)))
      RBT.empty\<rparr>)"

lemma search_attach:
  assumes r: "search_formed \<kappa> P r"
  shows "search_formed \<kappa> P (search_attach C r)" and "search_project (search_attach C r) = search_project r"
    and "search_calls (search_attach C r) = C"
    and "table_extends (search_table r) (search_table (search_attach C r))"
    and "shared_goals (search_state (search_attach C r)) = shared_goals (search_state r)"
    and "shared_nodes (search_state (search_attach C r)) = shared_nodes (search_state r)"
    and "search_classes_formed r \<Longrightarrow> search_classes_formed (search_attach C r)"
proof -
  obtain x E where ic: "index_calls C (shared_sharing (search_state r)) RBT.empty = (x,E)"
    by (cases "index_calls C (shared_sharing (search_state r)) RBT.empty")
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF r] .
  have x0: "share_state_formed (shared_sharing (search_state r))" by (rule shared_entries_formed(3)[OF s])
  have I0: "calls_indexed (share_state_table (shared_sharing (search_state r))) RBT.empty {}"
    by (simp add: calls_indexed_def)
  note ix = index_calls[OF x0 I0, of C]
  have xf: "share_state_formed x" and ext: "table_extends (search_table r) (share_state_table x)"
    and I: "calls_indexed (share_state_table x) E (set C)" using ix ic by simp_all
  note sh = search_share[OF r xf ext]
  let ?r1 = "(search_share x r)\<lparr>search_calls := C, search_index := E\<rparr>"
  define K where "K = fold (\<lambda>p t. closed_put p (search_state ?r1) E t) (RBT.keys (shared_goals (search_state ?r1))) RBT.empty"
  have a: "search_attach C r = ?r1\<lparr>search_closed := K\<rparr>" by (simp add: search_attach_def ic K_def Let_def)
  have Kl: "RBT.lookup K p = (case RBT.lookup (shared_goals (search_state r)) p of None \<Rightarrow> None
      | Some h \<Rightarrow> if shared_goal_closes E (shared_entry_goal h) then Some h else None)" for p
  proof -
    have keys: "p \<in> set (RBT.keys (shared_goals (search_state r))) \<longleftrightarrow> RBT.lookup (shared_goals (search_state r)) p \<noteq> None"
      using RBT.lookup_keys[of "shared_goals (search_state r)"] by (auto simp: dom_def)
    show ?thesis using keys unfolding K_def closed_put_fold by (auto simp: sh(4) split: option.split)
  qed
  have sf: "search_formed \<kappa> P (search_share x r)" by (rule sh(1))
  have three: "shared_state_formed \<kappa> P (search_state (search_attach C r)) \<and> search_registered_formed (search_attach C r) \<and>
      search_values_formed \<kappa> P (search_attach C r)"
  proof -
    have e1: "search_state (search_attach C r) = search_state (search_share x r)"
      "search_registered (search_attach C r) = search_registered (search_share x r)"
      "search_values (search_attach C r) = search_values (search_share x r)" by (simp_all add: a)
    have "search_registered_formed (search_attach C r) = search_registered_formed (search_share x r)"
      "search_values_formed \<kappa> P (search_attach C r) = search_values_formed \<kappa> P (search_share x r)"
      by (simp_all only: search_registered_formed_def search_values_formed_def e1)
    then show ?thesis using search_formedD[OF sf] e1(1) by simp
  qed
  have cl: "search_closing_formed (search_attach C r)"
    unfolding search_closing_formed_def
  proof (intro conjI allI)
    show "calls_indexed (search_table (search_attach C r)) (search_index (search_attach C r)) (set (search_calls (search_attach C r)))"
      using I sh(3) by (simp add: a)
    fix p
    show "RBT.lookup (search_closed (search_attach C r)) p = (case RBT.lookup (shared_goals (search_state (search_attach C r))) p of
        None \<Rightarrow> None | Some h \<Rightarrow> if search_closes (search_attach C r) h then Some h else None)"
      using Kl[of p] sh(4) by (simp add: a search_closes_def split: option.split)
  qed
  show "search_formed \<kappa> P (search_attach C r)" using three cl by (simp add: search_formed_def)
  show "search_project (search_attach C r) = search_project r" using sh(2) by (simp add: a)
  show "search_calls (search_attach C r) = C" by (simp add: a)
  show "table_extends (search_table r) (search_table (search_attach C r))" using ext sh(3) by (simp add: a)
  show "shared_goals (search_state (search_attach C r)) = shared_goals (search_state r)" using sh(4) by (simp add: a)
  show "shared_nodes (search_state (search_attach C r)) = shared_nodes (search_state r)" using sh(5) by (simp add: a)
  show "search_classes_formed r \<Longrightarrow> search_classes_formed (search_attach C r)"
    using search_share_classes[OF r xf ext] by (simp add: a)
qed

definition search_of_in :: "('d \<times> finite_factor_term) list \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) shared_search" where
  "search_of_in C P st = search_attach C (search_of P st)"

lemma search_of_in:
  assumes d: "resolution_positions_distinct st"
  shows "search_formed \<kappa> P (search_of_in C P st)" and "search_project (search_of_in C P st) = st"
    and "search_calls (search_of_in C P st) = C" and "search_classes_formed (search_of_in C P st)"
  using search_attach[OF search_of(1)[OF d]] search_of(2)[OF d] search_of_classes[OF d] by (simp_all add: search_of_in_def)

subsection \<open>A goal the table closes has one successor\<close>

lemma finite_goal_successors_in_open:
  "\<not> finite_table_closes \<Theta> g \<Longrightarrow> finite_goal_successors_in \<Theta> P st g = finite_goal_successors P st g"
  by (cases g) simp_all

definition search_successors_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_search \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) shared_search fset" where
  "search_successors_in \<kappa> P r h = (if search_closes r h then {|search_remove_goal (shared_goal_position (shared_entry_goal h)) r|}
    else search_successors \<kappa> P r h)"

theorem search_successors_in:
  assumes r: "search_formed \<kappa> P r" and pl: "search_placeable (search_project r)" and sock: "clause_sockets_distinct P"
    and h: "h |\<in>| access_goals (shared_access \<kappa> P r)"
    and D: "\<And>d t. (d,t) \<in> set (search_calls r) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "fimage search_project (search_successors_in \<kappa> P r h) =
      finite_goal_successors_in \<Theta> P (search_project r) (access_goal (shared_access \<kappa> P r) h)"
    and "s' |\<in>| search_successors_in \<kappa> P r h \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s') \<and>
      search_frame s' = search_frame r"
    and "s' |\<in>| search_successors_in \<kappa> P r h \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
proof -
  let ?V = "shared_access \<kappa> P r" let ?g = "access_goal ?V h" let ?q = "shared_goal_position (shared_entry_goal h)"
  have s: "shared_state_formed \<kappa> P (search_state r)" using search_formedD(1)[OF r] .
  obtain p where p: "RBT.lookup (shared_goals (search_state r)) p = Some h"
    using h by (auto simp: shared_access_simps tree_values_member)
  have at: "RBT.lookup (shared_goals (search_state r)) ?q = Some h" using p shared_goal_lookup_position[OF s p] by simp
  have cl: "search_closes r h \<longleftrightarrow> finite_table_closes \<Theta> ?g" by (rule search_closes_table[OF r h D])
  note rm = search_remove_goal[OF r at] and sr = shared_remove_goal[OF s at]
  have proj: "search_project (search_remove_goal ?q r) = finite_goal_closed (search_project r) ?g"
  proof -
    have "search_project (search_remove_goal ?q r) = Resolution_State
        (resolution_pending (search_project r) |-| {|?g|}) (resolution_nodes (search_project r))
        (resolution_witnesses (search_project r))"
      by (rule resolution_state.expand) (simp_all add: rm(2) sr(2,3,4) shared_access_simps)
    then show ?thesis by (simp add: finite_goal_closed_def)
  qed
  show "fimage search_project (search_successors_in \<kappa> P r h) = finite_goal_successors_in \<Theta> P (search_project r) ?g"
  proof (cases "search_closes r h")
    case True
    then have tc: "finite_table_closes \<Theta> ?g" using cl by simp
    then obtain q' rr d p' where g: "?g = Resolution_Call_Goal q' rr d p'"
      by (cases ?g) (simp_all add: finite_table_closes_def)
    have "finite_goal_successors_in \<Theta> P (search_project r) ?g = {|finite_goal_closed (search_project r) ?g|}"
      using tc g by simp
    then show ?thesis using True proj by (simp add: search_successors_in_def)
  next
    case False
    then have nc: "\<not> finite_table_closes \<Theta> ?g" using cl by simp
    have "fimage search_project (search_successors_in \<kappa> P r h) = fimage search_project (search_successors \<kappa> P r h)"
      using False by (simp add: search_successors_in_def)
    also have "\<dots> = finite_goal_successors P (search_project r) ?g" by (rule search_successors(1)[OF r pl sock h])
    also have "\<dots> = finite_goal_successors_in \<Theta> P (search_project r) ?g"
      by (rule finite_goal_successors_in_open[OF nc, symmetric])
    finally show ?thesis .
  qed
  show "s' |\<in>| search_successors_in \<kappa> P r h \<Longrightarrow> search_formed \<kappa> P s' \<and> search_placeable (search_project s') \<and>
      search_frame s' = search_frame r"
  proof -
    assume s': "s' |\<in>| search_successors_in \<kappa> P r h"
    show ?thesis
    proof (cases "search_closes r h")
      case True
      then have e: "s' = search_remove_goal ?q r" using s' by (simp add: search_successors_in_def)
      have "search_placeable (finite_goal_closed (search_project r) ?g)"
        unfolding finite_goal_closed_def by (rule search_placeable_fewer[OF pl])
      then show ?thesis using rm(1) proj by (simp add: e)
    next
      case False
      then have "s' |\<in>| search_successors \<kappa> P r h" using s' by (simp add: search_successors_in_def)
      then show ?thesis using search_successors(2)[OF r pl sock h] search_successors_frame by blast
    qed
  qed
  show "s' |\<in>| search_successors_in \<kappa> P r h \<Longrightarrow> search_classes_formed r \<Longrightarrow> search_classes_formed s'"
    using search_remove_goal_classes[OF r _ at] search_successors_classed(3)[OF r pl sock h]
    by (auto simp: search_successors_in_def split: if_splits)
qed

definition shared_representation_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s::linorder,'d,'c) shared_search, ('a,'s,'d,'c) shared_goal_entry, ('a,'s,'d,'c) shared_node_entry,
      nat, 'a, 's, 'd, 'c) resolution_representation" where
  "shared_representation_in \<kappa> P = (shared_representation \<kappa> P)\<lparr>rep_successors := search_successors_in \<kappa> P\<rparr>"

lemma shared_representation_in_fields [simp]:
  "rep_access (shared_representation_in \<kappa> P) = shared_access \<kappa> P"
  "rep_empty (shared_representation_in \<kappa> P) = (\<lambda>r. RBT.is_empty (shared_goals (search_state r)))"
  "rep_project (shared_representation_in \<kappa> P) = search_project"
  "rep_refresh (shared_representation_in \<kappa> P) = search_refresh \<kappa> P"
  "rep_construct (shared_representation_in \<kappa> P) = search_construct \<kappa> P"
  "rep_successors (shared_representation_in \<kappa> P) = search_successors_in \<kappa> P"
  by (simp_all add: shared_representation_in_def shared_representation_def)

theorem shared_search_in:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and D: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "represented_search_in (shared_representation_in \<kappa> P) search_closes (\<lambda>r h. False) \<kappa> P n (search_of_in C P st) =
      finite_resolution_search_in \<Theta> \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "shared_representation_in \<kappa> P"
  let ?F = "\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r) \<and> search_calls r = C"
  have DC: "\<And>r d t. ?F r \<Longrightarrow> (d,t) \<in> set (search_calls r) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
    using D by simp
  have "represented_search_in ?R search_closes (\<lambda>r h. False) \<kappa> P n (search_of_in C P st) =
      finite_resolution_search_by_in \<Theta> (finite_resolution_select_in \<Theta> (\<lambda>st g. False) \<kappa> P) \<kappa> P n
        (rep_project ?R (search_of_in C P st))"
  proof (rule represented_search_in[where F = ?F])
    show "?F (search_of_in C P st)" using search_of_in[OF d] pl by simp
  next
    fix s assume f: "?F s"
    then show "access_formed \<kappa> P (rep_access ?R s) (rep_project ?R s)" using shared_access_formed[OF conjunct1[OF f]] by simp
  next
    fix s assume f: "?F s"
    have "resolution_pending (search_project s) = fimage (\<lambda>h. shared_goal_project (search_table s) (shared_entry_goal h))
        (tree_values (shared_goals (search_state s)))" by (simp add: shared_state_project_fields)
    then show "rep_empty ?R s \<longleftrightarrow> resolution_pending (rep_project ?R s) = {||}" by (simp add: rbt_empty_values)
  next
    fix s assume f: "?F s"
    have fr: "search_frame (search_refresh \<kappa> P s) = search_frame s" by simp
    then show "?F (rep_refresh ?R s) \<and> rep_project ?R (rep_refresh ?R s) = rep_project ?R s"
      using search_refresh[OF conjunct1[OF f]] f by (simp add: search_frame_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (shared_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "shared_access \<kappa> P s"] m by auto
    note c = search_construct[OF conjunct1[OF f] n]
    have "search_placeable (search_project (search_construct \<kappa> P s m))"
      unfolding c(2) finite_construction_step_def Let_def
      by (rule search_placeable_substitute, rule search_placeable_witnesses[OF conjunct1[OF conjunct2[OF f]]])
    moreover have "search_calls (search_construct \<kappa> P s m) = search_calls s"
      using search_frame_composed(4)[of \<kappa> P s m] by (simp add: search_frame_def)
    ultimately show "?F (rep_construct ?R s m) \<and>
        rep_project ?R (rep_construct ?R s m) = finite_construction_step \<kappa> P (rep_project ?R s) (access_node (rep_access ?R s) m)"
      using c f by simp
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" using h by simp
    note sc = search_successors_in[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] sock h' DC[OF f]]
    show "fimage (rep_project ?R) (rep_successors ?R s h) =
        finite_goal_successors_in \<Theta> P (rep_project ?R s) (access_goal (rep_access ?R s) h) \<and>
        (\<forall>s'. s' |\<in>| rep_successors ?R s h \<longrightarrow> ?F s')"
      using sc(1) sc(2) f by (auto simp: search_frame_def)
  next
    fix s h assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)"
    have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" using h by simp
    show "search_closes s h \<longleftrightarrow> finite_table_closes \<Theta> (access_goal (rep_access ?R s) h)"
      using search_closes_table[OF conjunct1[OF f] h' DC[OF f]] by simp
  next
    fix s h show "False \<longleftrightarrow> False" by simp
  qed
  then show ?thesis using search_of_in(2)[OF d] by (simp add: finite_resolution_search_in_def)
qed

subsection \<open>The closing among the kept classes\<close>

definition search_select_in :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool) \<Rightarrow> ('a,'s::linorder,'d,'c) shared_search \<Rightarrow>
    (('a,'s,'d,'c) shared_node_entry, ('a,'s,'d,'c) shared_goal_entry) access_selection" where
  "search_select_in \<kappa> P rp r = kept_select_by_in (search_closed r) (ffilter rp) r (shared_access \<kappa> P r)"

lemma search_closed_class:
  assumes r: "search_formed \<kappa> P r"
  shows "RBT.lookup (search_closed r) p = class_value (search_closes r) (shared_goals (search_state r)) p"
  using search_formed_closing[OF r] by (simp add: search_closing_formed_def class_value_def)

theorem search_select_in:
  assumes r: "search_formed \<kappa> P r" and K: "search_classes_formed r"
  shows "search_select_in \<kappa> P rp r = access_select_in (search_closes r) rp (shared_access \<kappa> P r)"
  using kept_select_over_in[OF r K search_closed_class[OF r] search_closes_call, where N = "access_node (shared_access \<kappa> P r)"
      and Fr = "access_free (shared_access \<kappa> P r)" and VN = "access_value_none (shared_access \<kappa> P r)"
      and C = "access_call_variables (shared_access \<kappa> P r)" and rp = rp]
  by (simp only: access_node_fields_self search_select_in_def)

theorem shared_kept_search_in:
  assumes sock: "clause_sockets_distinct P" and pl: "search_placeable st"
    and D: "\<And>d t. (d,t) \<in> set C \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
  shows "selected_search (shared_representation_in \<kappa> P) (search_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of_in C P st) =
      finite_resolution_search_in \<Theta> \<kappa> P n st"
proof -
  have d: "resolution_positions_distinct st" using pl by (simp add: search_placeable_def)
  let ?R = "shared_representation_in \<kappa> P"
  let ?F = "\<lambda>r. search_formed \<kappa> P r \<and> search_placeable (search_project r) \<and> search_classes_formed r \<and> search_calls r = C"
  have DC: "\<And>r d t. ?F r \<Longrightarrow> (d,t) \<in> set (search_calls r) \<longleftrightarrow> resolution_table_lookup \<Theta> (d,t) \<noteq> None"
    using D by simp
  have "selected_search ?R (search_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n (search_of_in C P st) =
      represented_search_in ?R search_closes (\<lambda>r h. False) \<kappa> P n (search_of_in C P st)"
  proof (rule selected_search_in[where F = ?F])
    show "?F (search_of_in C P st)" using search_of_in[OF d] pl by simp
  next
    fix s assume f: "?F s"
    then show "?F (rep_refresh ?R s)"
      using search_refresh[OF conjunct1[OF f]] search_refresh_classes[of \<kappa> P s] search_frame_folds(3)[of \<kappa> P s]
      by (simp add: search_frame_def)
  next
    fix s m assume f: "?F s" and m: "m |\<in>| access_construction_nodes (rep_access ?R s)"
    obtain q0 where n: "m |\<in>| access_nodes_at (shared_access \<kappa> P s) q0"
      using access_construction_nodes_at[of m "shared_access \<kappa> P s"] m by auto
    note c = search_construct[OF conjunct1[OF f] n]
    have "search_placeable (search_project (search_construct \<kappa> P s m))"
      unfolding c(2) finite_construction_step_def Let_def
      by (rule search_placeable_substitute, rule search_placeable_witnesses[OF conjunct1[OF conjunct2[OF f]]])
    then show "?F (rep_construct ?R s m)"
      using c(1) search_construct_classes[of \<kappa> P s m] search_frame_composed(4)[of \<kappa> P s m] f
      by (simp add: search_frame_def)
  next
    fix s h s' assume f: "?F s" and h: "h |\<in>| access_goals (rep_access ?R s)" and s': "s' |\<in>| rep_successors ?R s h"
    have h': "h |\<in>| access_goals (shared_access \<kappa> P s)" and s'': "s' |\<in>| search_successors_in \<kappa> P s h"
      using h s' by simp_all
    note sc = search_successors_in[OF conjunct1[OF f] conjunct1[OF conjunct2[OF f]] sock h' DC[OF f]]
    show "?F s'" using sc(2)[OF s''] sc(3)[OF s''] f by (simp add: search_frame_def)
  next
    fix s assume f: "?F s"
    show "search_select_in \<kappa> P (\<lambda>h. False) s = access_select_in (search_closes s) ((\<lambda>r h. False) s) (rep_access ?R s)"
      using search_select_in[OF conjunct1[OF f] conjunct1[OF conjunct2[OF conjunct2[OF f]]]] by simp
  qed
  also have "\<dots> = finite_resolution_search_in \<Theta> \<kappa> P n st" by (rule shared_search_in[OF sock pl D])
  finally show ?thesis .
qed

subsection \<open>The listed table and the search's code at a table\<close>

text \<open>
  A finite table is the list of its entries, its lookup that of the list (@{const map_of}); its calls are the list's
  keys. The search at a listed table is computed over the shared search at the table, which reads the calls alone.
\<close>

definition listed_table :: "(('d \<times> finite_factor_term) \<times> ('a,'s,'c) finite_schema_proof) list \<Rightarrow> ('a,'s,'d,'c) resolution_table" where
  "listed_table es = Resolution_Table (map_of es)"

lemma listed_table_calls: "(d,t) \<in> set (map fst es) \<longleftrightarrow> resolution_table_lookup (listed_table es) (d,t) \<noteq> None"
  by (auto simp: listed_table_def map_of_eq_None_iff)

lemma listed_table_empty: "listed_table [] = resolution_empty_table"
  by (simp add: listed_table_def)

lemma listed_table_calls_set: "finite_table_calls (listed_table es) = set (map fst es)"
  by (auto simp: finite_table_calls_def listed_table_def map_of_eq_None_iff)

text \<open>A listed table of distinct calls is valid exactly when the checker accepts each of its entries at its call.\<close>

lemma listed_table_valid:
  assumes "distinct (map fst es)"
  shows "finite_table_valid P (listed_table es) \<longleftrightarrow> (\<forall>((d,t),c) \<in> set es. finite_checks_schema_proof P c d t)"
  using assms by (auto simp: finite_table_valid_def listed_table_def dest: map_of_SomeD intro: map_of_is_SomeI)

definition finite_resolution_search_listed ::
    "(('d \<times> finite_factor_term) \<times> ('a,'s,'c) finite_schema_proof) list \<Rightarrow> ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow>
      ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_resolution_search_listed es \<kappa> P n st = finite_resolution_search_in (listed_table es) \<kappa> P n st"

lemma finite_resolution_search_listed_empty: "finite_resolution_search_listed [] \<kappa> P n st = finite_resolution_search \<kappa> P n st"
  by (simp add: finite_resolution_search_listed_def listed_table_empty finite_resolution_search_def)

text \<open>
  The search at a listed table reads its calls alone (review 844's follow-up, carried from R3's search,
  @{thm [source] finite_resolution_search_in_calls}): it is the search at every table holding the same calls, a table
  of true calls whose certificates the checker does not accept among them, and two lists of the same calls search alike.
\<close>

theorem finite_resolution_search_listed_calls:
  assumes "finite_table_calls \<Theta> = set (map fst es)"
  shows "finite_resolution_search_listed es \<kappa> P n st = finite_resolution_search_in \<Theta> \<kappa> P n st"
  using finite_resolution_search_in_calls[of "listed_table es" \<Theta> \<kappa> P] assms listed_table_calls_set[of es]
  by (simp add: finite_resolution_search_listed_def)

corollary finite_resolution_search_listed_same_calls:
  assumes "set (map fst es) = set (map fst es')"
  shows "finite_resolution_search_listed es \<kappa> P n st = finite_resolution_search_listed es' \<kappa> P n st"
  using finite_resolution_search_listed_calls[of "listed_table es'" es] assms listed_table_calls_set[of es']
  by (simp add: finite_resolution_search_listed_def)

lemma finite_resolution_search_listed_shared_code [code]:
  "finite_resolution_search_listed es \<kappa> P n st = (if clause_sockets_distinct P \<and> search_placeable st
    then selected_search (shared_representation_in \<kappa> P) (search_select_in \<kappa> P (\<lambda>h. False)) \<kappa> P n
      (search_of_in (map fst es) P st)
    else finite_resolution_search_by_in (listed_table es) (finite_resolution_select_in (listed_table es) (\<lambda>st g. False) \<kappa> P)
      \<kappa> P n st)"
  using shared_kept_search_in[OF _ _ listed_table_calls, of P st \<kappa> n]
  by (simp add: finite_resolution_search_listed_def finite_resolution_search_in_def split: if_split)

export_code finite_resolution_search_listed checking SML

end
