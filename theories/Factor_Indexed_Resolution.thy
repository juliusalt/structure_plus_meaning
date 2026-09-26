theory Factor_Indexed_Resolution
  imports Factor_Resolution_Acceptance Tree_Map_Indexes Ordered_Finite_Terms
begin

section \<open>A tree of finite sets by key\<close>

text \<open>
  Build F2b1 of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size" (divided at q130).
  R3's search (@{const finite_resolution_search}) keeps its pending goals and its nodes as finite sets and substitutes
  each step's unifier into all of them. The indexed state keeps R3's own patterns, holds the goals and the nodes by
  position in red-black trees, caches every goal's and node's variables, and indexes from the position part of each
  variable to the positions of the goals and nodes holding a variable there, so a step visits only the holders of the
  variables it binds. Its projection forgets the trees, the caches and the indexes, and every indexed step projects to
  R3's step; the indexed search is therefore R3's search, and enters as its code equation.

  A bucket tree is a red-black tree from keys to nonempty finite sets; a key the tree does not hold has the empty
  bucket.
\<close>

definition tree_bucket :: "('k::linorder,'v fset) rbt \<Rightarrow> 'k \<Rightarrow> 'v fset" where
  "tree_bucket t q = (case RBT.lookup t q of None \<Rightarrow> {||} | Some G \<Rightarrow> G)"

definition tree_buckets :: "('k::linorder,'v fset) rbt \<Rightarrow> 'v fset" where
  "tree_buckets t = ffUnion (fset_of_list (map snd (RBT.entries t)))"

definition tree_buckets_ex :: "('k::linorder,'v fset) rbt \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> bool" where
  "tree_buckets_ex t F \<longleftrightarrow> list_ex (\<lambda>z. fBex (snd z) F) (RBT.entries t)"

definition tree_bucket_put :: "('k::linorder,'v fset) rbt \<Rightarrow> 'k \<Rightarrow> 'v fset \<Rightarrow> ('k,'v fset) rbt" where
  "tree_bucket_put t q G = (if G = {||} then RBT.delete q t else RBT.insert q G t)"

definition tree_buckets_nonempty :: "('k::linorder,'v fset) rbt \<Rightarrow> bool" where
  "tree_buckets_nonempty t \<longleftrightarrow> (\<forall>q. RBT.lookup t q \<noteq> Some {||})"

definition tree_buckets_formed :: "('k::linorder,'v fset) rbt \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> bool" where
  "tree_buckets_formed t F \<longleftrightarrow> tree_buckets_nonempty t \<and> (\<forall>q x. x |\<in>| tree_bucket t q \<longrightarrow> F q x)"

lemma tree_buckets_member: "x |\<in>| tree_buckets t \<longleftrightarrow> (\<exists>q. x |\<in>| tree_bucket t q)"
proof
  assume "x |\<in>| tree_buckets t"
  then obtain z where z: "z \<in> set (RBT.entries t)" "x |\<in>| snd z"
    by (auto simp: tree_buckets_def ffUnion.rep_eq fset_of_list.rep_eq)
  then have "RBT.lookup t (fst z) = Some (snd z)" by (simp add: RBT.lookup_in_tree)
  then show "\<exists>q. x |\<in>| tree_bucket t q" using z(2) by (intro exI[of _ "fst z"]) (simp add: tree_bucket_def)
next
  assume "\<exists>q. x |\<in>| tree_bucket t q"
  then obtain q G where "RBT.lookup t q = Some G" "x |\<in>| G" by (auto simp: tree_bucket_def split: option.splits)
  then have "(q, G) \<in> set (RBT.entries t)" "x |\<in>| G" by (simp_all add: RBT.lookup_in_tree)
  then show "x |\<in>| tree_buckets t" by (force simp: tree_buckets_def ffUnion.rep_eq fset_of_list.rep_eq)
qed

lemma tree_buckets_ex: "tree_buckets_ex t F \<longleftrightarrow> fBex (tree_buckets t) F"
proof -
  have "tree_buckets_ex t F \<longleftrightarrow> (\<exists>z\<in>set (RBT.entries t). \<exists>x. x |\<in>| snd z \<and> F x)"
    by (auto simp: tree_buckets_ex_def list_ex_iff)
  also have "\<dots> \<longleftrightarrow> (\<exists>x. x |\<in>| tree_buckets t \<and> F x)"
    by (auto simp: tree_buckets_def ffUnion.rep_eq fset_of_list.rep_eq)
  finally show ?thesis by auto
qed

lemma tree_bucket_put [simp]: "tree_bucket (tree_bucket_put t q G) p = (if p = q then G else tree_bucket t p)"
  by (simp add: tree_bucket_def tree_bucket_put_def)

lemma tree_bucket_insert [simp]: "tree_bucket (RBT.insert q G t) p = (if p = q then G else tree_bucket t p)"
  by (simp add: tree_bucket_def)

lemma tree_bucket_delete [simp]: "tree_bucket (RBT.delete q t) p = (if p = q then {||} else tree_bucket t p)"
  by (simp add: tree_bucket_def)

lemma tree_bucket_empty [simp]: "tree_bucket RBT.empty q = {||}"
  by (simp add: tree_bucket_def)

lemma tree_buckets_empty [simp]: "tree_buckets RBT.empty = {||}"
  by (simp add: fset_eq_iff tree_buckets_member)

lemma tree_buckets_formed_empty [simp]: "tree_buckets_formed RBT.empty F"
  by (simp add: tree_buckets_formed_def tree_buckets_nonempty_def)

lemma tree_buckets_formed_bucket: "tree_buckets_formed t F \<Longrightarrow> x |\<in>| tree_bucket t q \<Longrightarrow> F q x"
  by (simp add: tree_buckets_formed_def)

lemma tree_buckets_nonempty_put: "tree_buckets_nonempty t \<Longrightarrow> tree_buckets_nonempty (tree_bucket_put t q G)"
  by (simp add: tree_buckets_nonempty_def tree_bucket_put_def)

lemma tree_buckets_formed_put:
  assumes "tree_buckets_formed t F" "\<And>x. x |\<in>| G \<Longrightarrow> F q x"
  shows "tree_buckets_formed (tree_bucket_put t q G) F"
  using assms tree_buckets_nonempty_put[of t q G] by (auto simp: tree_buckets_formed_def)

lemma tree_buckets_is_empty:
  assumes formed: "tree_buckets_formed t F"
  shows "RBT.is_empty t \<longleftrightarrow> tree_buckets t = {||}"
proof
  assume "RBT.is_empty t"
  then have "t = RBT.empty" by simp
  then show "tree_buckets t = {||}" by simp
next
  assume none: "tree_buckets t = {||}"
  have "RBT.lookup t q = None" for q
  proof (cases "RBT.lookup t q")
    case (Some G)
    then have "G \<noteq> {||}" using formed by (auto simp: tree_buckets_formed_def tree_buckets_nonempty_def)
    then obtain x where x: "x |\<in>| G" by (metis all_not_fin_conv)
    then have "x |\<in>| tree_bucket t q" using Some by (simp add: tree_bucket_def)
    then have "x |\<in>| tree_buckets t" by (auto simp: tree_buckets_member)
    then show ?thesis using none by simp
  qed simp
  then have "RBT.lookup t = Map.empty" by (intro ext) simp
  then have "t = RBT.empty" by (simp only: RBT.lookup_empty_empty)
  then show "RBT.is_empty t" by simp
qed

text \<open>
  A key's own set grows by an element at each key of a finite set of keys; the keys are visited in their order.
\<close>

definition tree_add :: "'q \<Rightarrow> 'k::linorder fset \<Rightarrow> ('k,'q fset) rbt \<Rightarrow> ('k,'q fset) rbt" where
  "tree_add q K h = fold (\<lambda>p h. RBT.insert p (finsert q (tree_bucket h p)) h) (sorted_list_of_fset K) h"

lemma tree_add_fold:
  "tree_bucket (fold (\<lambda>p h. RBT.insert p (finsert q (tree_bucket h p)) h) ps h) p' =
    (if p' \<in> set ps then finsert q (tree_bucket h p') else tree_bucket h p')"
  by (induction ps arbitrary: h) auto

lemma tree_add [simp]:
  "tree_bucket (tree_add q K h) p = (if p |\<in>| K then finsert q (tree_bucket h p) else tree_bucket h p)"
  by (simp add: tree_add_def tree_add_fold)

subsection \<open>A bucket tree is an index of its rows\<close>

text \<open>
  A list of rows is the carrier of the relation it states; a bucket tree built from it by one insertion per row
  is its index, searched by the bucket at a key and keyed by the identity. Inserting one row is the notion's update:
  it adds the value at its key and keeps every other key. The holder index of the resolver's state is this index at
  positions: its rows pair the position part of a variable with the position of a goal or node holding a variable
  there, and @{const tree_add} is the update at each key of a set (the lemma tree_add_updates below).
\<close>

definition tree_bucket_add :: "('k::linorder,'q fset) rbt \<Rightarrow> 'k \<Rightarrow> 'q \<Rightarrow> ('k,'q fset) rbt" where
  "tree_bucket_add T p q = RBT.insert p (finsert q (tree_bucket T p)) T"

definition bucket_tree :: "('k::linorder \<times> 'q) list \<Rightarrow> ('k,'q fset) rbt" where
  "bucket_tree rows = fold (\<lambda>z T. tree_bucket_add T (fst z) (snd z)) rows RBT.empty"

lemma bucket_tree_fold:
  "q |\<in>| tree_bucket (fold (\<lambda>z T. tree_bucket_add T (fst z) (snd z)) rows T) p \<longleftrightarrow>
    (p,q) \<in> set rows \<or> q |\<in>| tree_bucket T p"
proof (induction rows arbitrary: T)
  case (Cons z rows)
  obtain a b where z: "z = (a,b)" by (cases z)
  show ?case unfolding z using Cons.IH[of "tree_bucket_add T a b"] by (simp add: tree_bucket_add_def) blast
qed simp

lemma bucket_tree_carrier_index:
  "carrier_index (\<lambda>rows p q. (p,q)\<in>set rows) (\<lambda>_. True) (UNIV::'k::linorder set) id bucket_tree
    (\<lambda>T p q. q |\<in>| tree_bucket T p)"
proof (rule carrier_index.intro)
  show "inj_on id (UNIV::'k set)" by simp
  fix rows :: "('k\<times>'q) list" and k :: 'k and v :: 'q
  show "v |\<in>| tree_bucket (bucket_tree rows) k \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v)\<in>set rows)"
    by (simp add: bucket_tree_def bucket_tree_fold)
qed

interpretation bucket_tree_index:
  carrier_index "\<lambda>rows p q. (p,q)\<in>set rows" "\<lambda>_. True" "UNIV::'k::linorder set" id bucket_tree
    "\<lambda>T p q. q |\<in>| tree_bucket T p"
  by (rule bucket_tree_carrier_index)

interpretation bucket_tree_updates:
  updated_carrier_index "\<lambda>rows p q. (p,q)\<in>set rows" "\<lambda>_. True" "UNIV::'k::linorder set" id bucket_tree
    "\<lambda>T p q. q |\<in>| tree_bucket T p" tree_bucket_add "\<lambda>u f v. v=u \<or> f v"
proof (rule updated_carrier_index.intro[OF bucket_tree_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "('k,'q fset) rbt" and k k' :: 'k and u v :: 'q
  show "v |\<in>| tree_bucket (tree_bucket_add T k u) k' \<longleftrightarrow> (if k'=k then v=u \<or> v |\<in>| tree_bucket T k else v |\<in>| tree_bucket T k')"
    by (simp add: tree_bucket_add_def)
qed

lemma tree_add_updates: "tree_add q K h = fold (\<lambda>p T. tree_bucket_add T p q) (sorted_list_of_fset K) h"
  by (simp add: tree_add_def tree_bucket_add_def)

lemma ffUnion_fimage_member: "y |\<in>| G \<Longrightarrow> x |\<in>| f y \<Longrightarrow> x |\<in>| ffUnion (fimage f G)"
  by (force simp: ffUnion.rep_eq fimage.rep_eq)

text \<open>
  The holder index is keyed by the position part of a variable (@{typ "('s,'a) resolution_variable"}): keyed by
  positions alone, never by the variables' own type, so it stands at the search's general type. It is a superset
  index: every holder is found, and a position found is read through the caches at it.
\<close>

definition variable_positions :: "('s,'a) resolution_variable fset \<Rightarrow> 's list fset" where
  "variable_positions V = fimage (\<lambda>x. fst (fst x)) V"

lemma variable_positions_member: "x |\<in>| V \<Longrightarrow> fst (fst x) |\<in>| variable_positions V"
  by (force simp: variable_positions_def fimage.rep_eq)

subsection \<open>Counts by prefix\<close>

definition tree_count :: "('k::linorder,nat) rbt \<Rightarrow> 'k \<Rightarrow> nat" where
  "tree_count t k = (case RBT.lookup t k of None \<Rightarrow> 0 | Some n \<Rightarrow> n)"

definition tree_count_adjust :: "(nat \<Rightarrow> nat) \<Rightarrow> 'k::linorder list \<Rightarrow> ('k,nat) rbt \<Rightarrow> ('k,nat) rbt" where
  "tree_count_adjust f ps t = fold (\<lambda>p t. RBT.insert p (f (tree_count t p)) t) ps t"

lemma tree_count_adjust:
  "distinct ps \<Longrightarrow> tree_count (tree_count_adjust f ps t) p = (if p \<in> set ps then f (tree_count t p) else tree_count t p)"
  unfolding tree_count_adjust_def by (induction ps arbitrary: t) (auto simp: tree_count_def)

lemma tree_count_empty [simp]: "tree_count RBT.empty p = 0"
  by (simp add: tree_count_def)

definition position_prefixes :: "'s list \<Rightarrow> 's list list" where
  "position_prefixes q = map (\<lambda>i. take i q) [0..<Suc (length q)]"

lemma position_prefixes_member: "p \<in> set (position_prefixes q) \<longleftrightarrow> take (length p) q = p"
proof
  assume "p \<in> set (position_prefixes q)"
  then have "p \<in> (\<lambda>i. take i q) ` set [0..<Suc (length q)]" by (simp add: position_prefixes_def)
  then obtain i where "p = take i q" "i \<in> set [0..<Suc (length q)]" by (rule imageE)
  then show "take (length p) q = p" by (simp add: min_def)
next
  assume a: "take (length p) q = p"
  have "length (take (length p) q) = length p" using a by simp
  then have le: "length p \<le> length q" by (simp add: min_def split: if_splits)
  have "p = (\<lambda>i. take i q) (length p)" using a by simp
  moreover have "length p \<in> set [0..<Suc (length q)]" using le by auto
  ultimately show "p \<in> set (position_prefixes q)" unfolding position_prefixes_def by (metis image_eqI set_map)
qed

lemma position_prefixes_distinct: "distinct (position_prefixes q)"
proof -
  have "inj_on (\<lambda>i. take i q) (set [0..<Suc (length q)])"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> set [0..<Suc (length q)]" and j: "j \<in> set [0..<Suc (length q)]"
      and e: "take i q = take j q"
    have "length (take i q) = i" "length (take j q) = j" using i j by (auto simp: min_def)
    then show "i = j" using e by metis
  qed
  then show ?thesis unfolding position_prefixes_def by (simp add: distinct_map)
qed

definition tree_keys_under :: "('s::linorder list,'v) rbt \<Rightarrow> 's list \<Rightarrow> 's list set" where
  "tree_keys_under t p = {q. RBT.lookup t q \<noteq> None \<and> take (length p) q = p}"

lemma tree_keys_under_finite: "finite (tree_keys_under t p)"
  by (rule finite_subset[of _ "dom (RBT.lookup t)"]) (auto simp: tree_keys_under_def)

definition tree_bucket_count_put :: "('s::linorder list,'v fset) rbt \<Rightarrow> ('s list,nat) rbt \<Rightarrow> 's list \<Rightarrow> 'v fset \<Rightarrow>
    ('s list,nat) rbt" where
  "tree_bucket_count_put t c q G = (if (RBT.lookup t q = None) = (G = {||}) then c
    else tree_count_adjust (if G = {||} then (\<lambda>n. n - 1) else Suc) (position_prefixes q) c)"

lemma tree_bucket_count_put:
  assumes counts: "\<And>p. tree_count c p = card (tree_keys_under t p)"
  shows "tree_count (tree_bucket_count_put t c q G) p = card (tree_keys_under (tree_bucket_put t q G) p)"
proof -
  have keys: "tree_keys_under (tree_bucket_put t q G) p =
      (if take (length p) q = p then (if G = {||} then tree_keys_under t p - {q} else insert q (tree_keys_under t p))
       else tree_keys_under t p)"
    by (auto simp: tree_keys_under_def tree_bucket_put_def split: if_splits)
  have fin: "finite (tree_keys_under t p)" by (rule tree_keys_under_finite)
  have mem: "q \<in> tree_keys_under t p \<longleftrightarrow> RBT.lookup t q \<noteq> None \<and> take (length p) q = p"
    by (simp add: tree_keys_under_def)
  show ?thesis
    using counts[of p] fin mem
    by (auto simp: keys tree_bucket_count_put_def tree_count_adjust[OF position_prefixes_distinct]
        position_prefixes_member card_insert_if card_Diff_singleton_if split: if_splits)
qed

lemma tree_keys_under_empty:
  assumes "tree_buckets_nonempty t"
  shows "tree_keys_under t p = {} \<longleftrightarrow> \<not> (\<exists>q x. x |\<in>| tree_bucket t q \<and> take (length p) q = p)"
proof -
  have "RBT.lookup t q \<noteq> None \<longleftrightarrow> (\<exists>x. x |\<in>| tree_bucket t q)" for q
  proof (cases "RBT.lookup t q")
    case (Some G)
    then have "G \<noteq> {||}" using assms by (auto simp: tree_buckets_nonempty_def)
    then show ?thesis using Some by (auto simp: tree_bucket_def fset_eq_iff)
  qed (simp add: tree_bucket_def)
  then show ?thesis by (auto simp: tree_keys_under_def)
qed

section \<open>Goals and nodes with their caches\<close>

datatype ('a,'s,'d,'c) indexed_goal = Indexed_Goal
  (indexed_goal_value: "('a,'s,'d,'c) resolution_goal")
  (indexed_goal_variables: "('s,'a) resolution_variable fset")
  (indexed_goal_alternatives: nat)

definition index_goal :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal" where
  "index_goal P g = Indexed_Goal g (resolution_goal_variables g) (finite_goal_alternatives P g)"

lemma index_goal_fields [simp]:
  "indexed_goal_value (index_goal P g) = g"
  "indexed_goal_variables (index_goal P g) = resolution_goal_variables g"
  "indexed_goal_alternatives (index_goal P g) = finite_goal_alternatives P g"
  by (simp_all add: index_goal_def)

definition resolution_node_variables :: "('a,'s,'d,'c) resolution_node \<Rightarrow> ('s,'a) resolution_variable fset" where
  "resolution_node_variables nd = finite_pattern_variables (resolution_node_call nd) |\<union>|
    ffUnion (fimage (\<lambda>z. finite_pattern_variables (snd z)) (resolution_node_bindings nd))"

datatype ('a,'s,'d,'c) indexed_node = Indexed_Node
  (indexed_node_value: "('a,'s,'d,'c) resolution_node")
  (indexed_node_variables: "('s,'a) resolution_variable fset")

definition index_node :: "('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) indexed_node" where
  "index_node nd = Indexed_Node nd (resolution_node_variables nd)"

lemma index_node_fields [simp]:
  "indexed_node_value (index_node nd) = nd"
  "indexed_node_variables (index_node nd) = resolution_node_variables nd"
  by (simp_all add: index_node_def)

definition indexed_node_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) indexed_node \<Rightarrow> bool" where
  "indexed_node_formed \<kappa> P hn \<longleftrightarrow> indexed_node_variables hn = resolution_node_variables (indexed_node_value hn)"

lemma index_node_formed [simp]: "indexed_node_formed \<kappa> P (index_node nd)"
  by (simp add: indexed_node_formed_def)

subsection \<open>The keys of ground calls\<close>

text \<open>
  A ground call is keyed by the term it presents (@{typ ordered_factor_term}), so the solved nodes that close it and
  the pending goals it waits on are found by one search, and never by the types of sites or variables.
\<close>

definition resolution_call_key :: "'v finite_term_pattern \<Rightarrow> ordered_factor_term" where
  "resolution_call_key p = Ordered_Factor_Term (finite_residual_term p)"

definition goal_call_keys :: "('a,'s,'d,'c) indexed_goal fset \<Rightarrow> ordered_factor_term fset" where
  "goal_call_keys G = ffUnion (fimage (\<lambda>hg. case indexed_goal_value hg of
      Resolution_Call_Goal q r d p \<Rightarrow> if indexed_goal_variables hg = {||} then {|resolution_call_key p|} else {||}
    | Resolution_Material_Goal q r M \<Rightarrow> {||}) G)"

definition node_call_keys :: "('a,'s,'d,'c) indexed_node fset \<Rightarrow> ordered_factor_term fset" where
  "node_call_keys N = ffUnion (fimage (\<lambda>hn.
      if finite_pattern_variables (resolution_node_call (indexed_node_value hn)) = {||}
      then {|resolution_call_key (resolution_node_call (indexed_node_value hn))|} else {||}) N)"

lemma goal_call_keys_member:
  assumes "hg |\<in>| G" "indexed_goal_value hg = Resolution_Call_Goal q r d p" "indexed_goal_variables hg = {||}"
  shows "resolution_call_key p |\<in>| goal_call_keys G"
  unfolding goal_call_keys_def by (rule ffUnion_fimage_member[OF assms(1)]) (simp add: assms(2,3))

lemma node_call_keys_member:
  assumes "hn |\<in>| N" "finite_pattern_variables (resolution_node_call (indexed_node_value hn)) = {||}"
  shows "resolution_call_key (resolution_node_call (indexed_node_value hn)) |\<in>| node_call_keys N"
  unfolding node_call_keys_def by (rule ffUnion_fimage_member[OF assms(1)]) (simp add: assms(2))

section \<open>The indexed state and its projection\<close>

text \<open>
  The state holds the goals and the nodes by position, the construction's witnesses, the holder index (from the
  position part of a variable to the positions of its holders), the count of goal positions at or under each
  position (a node is solved when its count is zero), and the positions of the nodes and of the pending goals whose
  call is ground, by the key of that call.
\<close>

text \<open>
  A set of indexed states is computed, so its trees need an executable equality: HOL's equality on the tree
  typedef, which compares the trees it wraps (@{thm [source] RBT.impl_of_inject}). No statement changes with it.
\<close>

instantiation RBT.rbt :: ("{linorder,equal}", equal) equal
begin
definition equal_rbt :: "('a,'b) RBT.rbt \<Rightarrow> ('a,'b) RBT.rbt \<Rightarrow> bool" where
  "equal_rbt t u \<longleftrightarrow> RBT.impl_of t = RBT.impl_of u"
instance by standard (simp add: equal_rbt_def RBT.impl_of_inject)
end

lemma equal_rbt_code [code]: "HOL.equal t u \<longleftrightarrow> RBT.impl_of t = RBT.impl_of u"
  by (simp add: equal_eq equal_rbt_def RBT.impl_of_inject)

declare [[typedef_overloaded]]

record ('a,'s::linorder,'d,'c) indexed_state =
  indexed_goals :: "('s list, ('a,'s,'d,'c) indexed_goal fset) rbt"
  indexed_nodes :: "('s list, ('a,'s,'d,'c) indexed_node fset) rbt"
  indexed_witnesses :: "(('s,'a) resolution_variable \<times> finite_factor_term) fset"
  indexed_holders :: "('s list, 's list fset) rbt"
  indexed_open :: "('s list, nat) rbt"
  indexed_goal_calls :: "(ordered_factor_term, 's list fset) rbt"
  indexed_node_calls :: "(ordered_factor_term, 's list fset) rbt"
  indexed_unconstructed :: "('s list, 'a fset) rbt"

definition indexed_pending :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "indexed_pending r = fimage indexed_goal_value (tree_buckets (indexed_goals r))"

definition indexed_node_set :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "indexed_node_set r = fimage indexed_node_value (tree_buckets (indexed_nodes r))"

definition indexed_project :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "indexed_project r = Resolution_State (indexed_pending r) (indexed_node_set r) (indexed_witnesses r)"

lemma indexed_project_fields [simp]:
  "resolution_pending (indexed_project r) = indexed_pending r"
  "resolution_nodes (indexed_project r) = indexed_node_set r"
  "resolution_witnesses (indexed_project r) = indexed_witnesses r"
  by (simp_all add: indexed_project_def)

lemma indexed_pending_member:
  "g |\<in>| indexed_pending r \<longleftrightarrow> (\<exists>q hg. hg |\<in>| tree_bucket (indexed_goals r) q \<and> indexed_goal_value hg = g)"
  by (force simp: indexed_pending_def tree_buckets_member fimage.rep_eq)

lemma indexed_node_set_member:
  "nd |\<in>| indexed_node_set r \<longleftrightarrow> (\<exists>q hn. hn |\<in>| tree_bucket (indexed_nodes r) q \<and> indexed_node_value hn = nd)"
  by (force simp: indexed_node_set_def tree_buckets_member fimage.rep_eq)

subsection \<open>Formation\<close>

text \<open>
  An indexed state is formed when every goal and node is its own index at its own position, every node's kept values
  are the registered values at it, every goal and node is recorded in the holder index and, where its call is ground,
  in the index of calls, and the counts are the numbers of goal positions at or under each position. Its constructors
  establish it and its steps keep it; nothing checks it.
\<close>

definition indexed_goal_formed_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_goal_formed_at P q hg \<longleftrightarrow>
    index_goal P (indexed_goal_value hg) = hg \<and> resolution_goal_position (indexed_goal_value hg) = q"

definition indexed_node_formed_at :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) indexed_node \<Rightarrow> bool" where
  "indexed_node_formed_at \<kappa> P q hn \<longleftrightarrow>
    indexed_node_formed \<kappa> P hn \<and> resolution_node_position (indexed_node_value hn) = q"

definition indexed_recorded_at :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> 's list \<Rightarrow> bool" where
  "indexed_recorded_at r q \<longleftrightarrow>
    (\<forall>hg x. hg |\<in>| tree_bucket (indexed_goals r) q \<longrightarrow> x |\<in>| indexed_goal_variables hg \<longrightarrow>
      q |\<in>| tree_bucket (indexed_holders r) (fst (fst x))) \<and>
    (\<forall>hn x. hn |\<in>| tree_bucket (indexed_nodes r) q \<longrightarrow> x |\<in>| indexed_node_variables hn \<longrightarrow>
      q |\<in>| tree_bucket (indexed_holders r) (fst (fst x))) \<and>
    (\<forall>k. k |\<in>| goal_call_keys (tree_bucket (indexed_goals r) q) \<longrightarrow> q |\<in>| tree_bucket (indexed_goal_calls r) k) \<and>
    (\<forall>k. k |\<in>| node_call_keys (tree_bucket (indexed_nodes r) q) \<longrightarrow> q |\<in>| tree_bucket (indexed_node_calls r) k)"

definition indexed_open_formed :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> bool" where
  "indexed_open_formed r \<longleftrightarrow> (\<forall>p. tree_count (indexed_open r) p = card (tree_keys_under (indexed_goals r) p))"

text \<open>
  F4: a registered variable whose construction returned nothing at every node of a position is kept at that
  position, so the selection does not ask the construction again; a position whose nodes change drops what it
  kept.
\<close>

definition indexed_unconstructed_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> bool" where
  "indexed_unconstructed_formed \<kappa> P r \<longleftrightarrow> (\<forall>q a hn. a |\<in>| tree_bucket (indexed_unconstructed r) q \<longrightarrow>
    hn |\<in>| tree_bucket (indexed_nodes r) q \<longrightarrow> finite_registered_value \<kappa> P (indexed_node_value hn) a = None)"

definition indexed_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> bool" where
  "indexed_formed \<kappa> P r \<longleftrightarrow> tree_buckets_formed (indexed_goals r) (indexed_goal_formed_at P) \<and>
    tree_buckets_formed (indexed_nodes r) (indexed_node_formed_at \<kappa> P) \<and>
    (\<forall>q. indexed_recorded_at r q) \<and> indexed_open_formed r \<and> indexed_unconstructed_formed \<kappa> P r"

lemma indexed_goal_at:
  assumes "indexed_formed \<kappa> P r" "hg |\<in>| tree_bucket (indexed_goals r) q"
  shows "index_goal P (indexed_goal_value hg) = hg" "resolution_goal_position (indexed_goal_value hg) = q"
  using tree_buckets_formed_bucket[of "indexed_goals r" _ hg q] assms
  unfolding indexed_formed_def indexed_goal_formed_at_def by blast+

lemma indexed_goal_variables_at:
  assumes "indexed_formed \<kappa> P r" "hg |\<in>| tree_bucket (indexed_goals r) q"
  shows "indexed_goal_variables hg = resolution_goal_variables (indexed_goal_value hg)"
    "indexed_goal_alternatives hg = finite_goal_alternatives P (indexed_goal_value hg)"
  using index_goal_fields(2,3)[of P "indexed_goal_value hg"] indexed_goal_at(1)[OF assms] by simp_all

lemma indexed_node_at:
  assumes "indexed_formed \<kappa> P r" "hn |\<in>| tree_bucket (indexed_nodes r) q"
  shows "indexed_node_formed \<kappa> P hn" "resolution_node_position (indexed_node_value hn) = q"
  using tree_buckets_formed_bucket[of "indexed_nodes r" _ hn q] assms
  unfolding indexed_formed_def indexed_node_formed_at_def by blast+

lemma indexed_recorded:
  assumes "indexed_formed \<kappa> P r"
  shows "hg |\<in>| tree_bucket (indexed_goals r) q \<Longrightarrow> x |\<in>| indexed_goal_variables hg \<Longrightarrow>
      q |\<in>| tree_bucket (indexed_holders r) (fst (fst x))"
    and "hn |\<in>| tree_bucket (indexed_nodes r) q \<Longrightarrow> x |\<in>| indexed_node_variables hn \<Longrightarrow>
      q |\<in>| tree_bucket (indexed_holders r) (fst (fst x))"
    and "k |\<in>| goal_call_keys (tree_bucket (indexed_goals r) q) \<Longrightarrow> q |\<in>| tree_bucket (indexed_goal_calls r) k"
    and "k |\<in>| node_call_keys (tree_bucket (indexed_nodes r) q) \<Longrightarrow> q |\<in>| tree_bucket (indexed_node_calls r) k"
  using assms unfolding indexed_formed_def indexed_recorded_at_def by blast+

text \<open>A goal of a formed state is determined by its value, and stands in the bucket of its position.\<close>

lemma indexed_goal_unique:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q"
    and hg': "hg' |\<in>| tree_bucket (indexed_goals r) q'" and same: "indexed_goal_value hg = indexed_goal_value hg'"
  shows "hg = hg'" "q = q'"
proof -
  show "hg = hg'" using indexed_goal_at(1)[OF r hg] indexed_goal_at(1)[OF r hg'] same by metis
  show "q = q'" using indexed_goal_at(2)[OF r hg] indexed_goal_at(2)[OF r hg'] same by simp
qed

lemma indexed_solved_count:
  assumes r: "indexed_formed \<kappa> P r"
  shows "tree_count (indexed_open r) p = 0 \<longleftrightarrow>
    \<not> fBex (indexed_pending r) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
proof -
  have c: "tree_count (indexed_open r) p = card (tree_keys_under (indexed_goals r) p)"
    using r by (simp add: indexed_formed_def indexed_open_formed_def)
  have ne: "tree_buckets_nonempty (indexed_goals r)" using r by (simp add: indexed_formed_def tree_buckets_formed_def)
  have "tree_count (indexed_open r) p = 0 \<longleftrightarrow> tree_keys_under (indexed_goals r) p = {}"
    by (simp add: c card_0_eq[OF tree_keys_under_finite])
  also have "\<dots> \<longleftrightarrow> \<not> (\<exists>q hg. hg |\<in>| tree_bucket (indexed_goals r) q \<and> take (length p) q = p)"
    by (rule tree_keys_under_empty[OF ne])
  also have "\<dots> \<longleftrightarrow> \<not> fBex (indexed_pending r) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
  proof -
    have "(\<exists>q hg. hg |\<in>| tree_bucket (indexed_goals r) q \<and> take (length p) q = p) \<longleftrightarrow>
        fBex (indexed_pending r) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
    proof
      assume "\<exists>q hg. hg |\<in>| tree_bucket (indexed_goals r) q \<and> take (length p) q = p"
      then obtain q hg where hg: "hg |\<in>| tree_bucket (indexed_goals r) q" "take (length p) q = p" by blast
      have "indexed_goal_value hg |\<in>| indexed_pending r" using hg(1) by (auto simp: indexed_pending_member)
      then show "fBex (indexed_pending r) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
        using hg(2) indexed_goal_at(2)[OF r hg(1)] by auto
    next
      assume "fBex (indexed_pending r) (\<lambda>g. take (length p) (resolution_goal_position g) = p)"
      then obtain g where g: "g |\<in>| indexed_pending r" "take (length p) (resolution_goal_position g) = p" by auto
      then obtain q hg where hg: "hg |\<in>| tree_bucket (indexed_goals r) q" "indexed_goal_value hg = g"
        by (auto simp: indexed_pending_member)
      then show "\<exists>q hg. hg |\<in>| tree_bucket (indexed_goals r) q \<and> take (length p) q = p"
        using g(2) indexed_goal_at(2)[OF r hg(1)] by auto
    qed
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

section \<open>Substitution leaves alone what it does not bind\<close>

lemma finite_pattern_substitute_outside:
  "(\<And>x. x |\<in>| finite_pattern_variables p \<Longrightarrow> \<sigma> x = Finite_Variable x) \<Longrightarrow> finite_pattern_substitute \<sigma> p = p"
  using finite_pattern_substitute_cong[of p \<sigma> Finite_Variable] by simp

lemma finite_material_substitute_outside:
  assumes "\<And>x. x |\<in>| finite_material_variables M \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "finite_material_pattern_substitute \<sigma> M = M"
proof -
  have field: "finite_pattern_substitute \<sigma> p = p"
    if "\<And>x. x |\<in>| finite_pattern_variables p \<Longrightarrow> x |\<in>| finite_material_variables M" for p
    using that assms by (intro finite_pattern_substitute_outside) blast
  have "finite_pattern_substitute \<sigma> (finite_material_source M) = finite_material_source M"
    "finite_pattern_substitute \<sigma> (finite_material_atoms M) = finite_material_atoms M"
    "finite_pattern_substitute \<sigma> (finite_material_edges M) = finite_material_edges M"
    "finite_pattern_substitute \<sigma> (finite_material_counts M) = finite_material_counts M"
    "finite_pattern_substitute \<sigma> (finite_material_functions M) = finite_material_functions M"
    by (auto intro!: field simp: finite_material_variables_def)
  then show ?thesis by (simp add: finite_material_pattern_substitute_def)
qed

lemma resolution_goal_substitute_outside:
  assumes "\<And>x. x |\<in>| resolution_goal_variables g \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "resolution_goal_substitute \<sigma> g = g"
proof (cases g)
  case (Resolution_Call_Goal q r d p)
  have "finite_pattern_substitute \<sigma> p = p"
    by (rule finite_pattern_substitute_outside) (use assms in \<open>simp add: Resolution_Call_Goal\<close>)
  then show ?thesis by (simp add: Resolution_Call_Goal)
next
  case (Resolution_Material_Goal q r M)
  have "finite_material_pattern_substitute \<sigma> M = M"
    by (rule finite_material_substitute_outside) (use assms in \<open>simp add: Resolution_Material_Goal\<close>)
  then show ?thesis by (simp add: Resolution_Material_Goal)
qed

lemma fimage_fixed:
  assumes "\<And>z. z |\<in>| B \<Longrightarrow> f z = z"
  shows "fimage f B = B"
proof -
  have "f ` fset B = fset B" using assms by (force intro: rev_image_eqI)
  then show ?thesis by (metis fimage.rep_eq fset_inject)
qed

lemma resolution_node_substitute_outside:
  assumes out: "\<And>x. x |\<in>| resolution_node_variables nd \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "resolution_node_substitute \<sigma> nd = nd"
proof (cases nd)
  case (Resolution_Node q d c S p B)
  have call: "finite_pattern_substitute \<sigma> p = p"
    by (rule finite_pattern_substitute_outside) (use out in \<open>simp add: Resolution_Node resolution_node_variables_def\<close>)
  have bind: "fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) B = B"
  proof (rule fimage_fixed)
    fix z assume z: "z |\<in>| B"
    obtain a x where zx: "z = (a,x)" by (cases z)
    have "finite_pattern_substitute \<sigma> x = x"
    proof (rule finite_pattern_substitute_outside)
      fix y assume "y |\<in>| finite_pattern_variables x"
      then have "y |\<in>| resolution_node_variables nd" using z zx
        by (force simp: Resolution_Node resolution_node_variables_def ffUnion.rep_eq fimage.rep_eq)
      then show "\<sigma> y = Finite_Variable y" by (rule out)
    qed
    then show "(\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) z = z" by (simp add: zx)
  qed
  show ?thesis using call bind by (simp add: Resolution_Node)
qed

lemmas resolution_substitute_positions [simp] =
  resolution_goal_substitute_fields resolution_node_substitute_fields

lemma fimage_cong_on: "(\<And>x. x |\<in>| A \<Longrightarrow> f x = g x) \<Longrightarrow> fimage f A = fimage g A"
  by (force simp: fset_eq_iff fimage.rep_eq)

lemma tree_buckets_map:
  assumes "\<And>p. tree_bucket t' p = fimage f (tree_bucket t p)"
  shows "tree_buckets t' = fimage f (tree_buckets t)"
  using assms by (force simp: fset_eq_iff tree_buckets_member fimage.rep_eq)

section \<open>Replacing the goals and nodes at a position\<close>

text \<open>
  Every change of the state is one operation: the goals and the nodes at one position are replaced, the count of goal
  positions is adjusted along the position's prefixes where the position's bucket appears or disappears, and every
  variable and ground call of the new buckets is recorded in the indexes. The indexes are superset indexes: an entry is
  never removed, and a search reads the buckets it finds.
\<close>

definition indexed_record_at :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_record_at q r = r\<lparr>
    indexed_holders := tree_add q (variable_positions (ffUnion (fimage indexed_goal_variables (tree_bucket (indexed_goals r) q)) |\<union>|
      ffUnion (fimage indexed_node_variables (tree_bucket (indexed_nodes r) q)))) (indexed_holders r),
    indexed_goal_calls := tree_add q (goal_call_keys (tree_bucket (indexed_goals r) q)) (indexed_goal_calls r),
    indexed_node_calls := tree_add q (node_call_keys (tree_bucket (indexed_nodes r) q)) (indexed_node_calls r)\<rparr>"

definition indexed_replace :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset \<Rightarrow> ('a,'s,'d,'c) indexed_node fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_replace q G N r = indexed_record_at q (r\<lparr>indexed_goals := tree_bucket_put (indexed_goals r) q G,
    indexed_nodes := tree_bucket_put (indexed_nodes r) q N,
    indexed_open := tree_bucket_count_put (indexed_goals r) (indexed_open r) q G,
    indexed_unconstructed := RBT.delete q (indexed_unconstructed r)\<rparr>)"

lemma indexed_record_at_fields [simp]:
  "indexed_goals (indexed_record_at q r) = indexed_goals r" "indexed_nodes (indexed_record_at q r) = indexed_nodes r"
  "indexed_witnesses (indexed_record_at q r) = indexed_witnesses r" "indexed_open (indexed_record_at q r) = indexed_open r"
  "indexed_unconstructed (indexed_record_at q r) = indexed_unconstructed r"
  by (simp_all add: indexed_record_at_def)

lemma indexed_record_at_recorded: "indexed_recorded_at (indexed_record_at q r) q"
  unfolding indexed_recorded_at_def
proof (intro conjI allI impI)
  fix hg x assume hg: "hg |\<in>| tree_bucket (indexed_goals (indexed_record_at q r)) q" and x: "x |\<in>| indexed_goal_variables hg"
  have "x |\<in>| ffUnion (fimage indexed_goal_variables (tree_bucket (indexed_goals r) q)) |\<union>|
      ffUnion (fimage indexed_node_variables (tree_bucket (indexed_nodes r) q))"
    using ffUnion_fimage_member[of hg "tree_bucket (indexed_goals r) q" x indexed_goal_variables] hg x by simp
  then have "fst (fst x) |\<in>| variable_positions (ffUnion (fimage indexed_goal_variables (tree_bucket (indexed_goals r) q)) |\<union>|
      ffUnion (fimage indexed_node_variables (tree_bucket (indexed_nodes r) q)))"
    by (rule variable_positions_member)
  then show "q |\<in>| tree_bucket (indexed_holders (indexed_record_at q r)) (fst (fst x))"
    by (simp add: indexed_record_at_def)
next
  fix hn x assume hn: "hn |\<in>| tree_bucket (indexed_nodes (indexed_record_at q r)) q" and x: "x |\<in>| indexed_node_variables hn"
  have "x |\<in>| ffUnion (fimage indexed_goal_variables (tree_bucket (indexed_goals r) q)) |\<union>|
      ffUnion (fimage indexed_node_variables (tree_bucket (indexed_nodes r) q))"
    using ffUnion_fimage_member[of hn "tree_bucket (indexed_nodes r) q" x indexed_node_variables] hn x by simp
  then have "fst (fst x) |\<in>| variable_positions (ffUnion (fimage indexed_goal_variables (tree_bucket (indexed_goals r) q)) |\<union>|
      ffUnion (fimage indexed_node_variables (tree_bucket (indexed_nodes r) q)))"
    by (rule variable_positions_member)
  then show "q |\<in>| tree_bucket (indexed_holders (indexed_record_at q r)) (fst (fst x))"
    by (simp add: indexed_record_at_def)
next
  fix k assume "k |\<in>| goal_call_keys (tree_bucket (indexed_goals (indexed_record_at q r)) q)"
  then show "q |\<in>| tree_bucket (indexed_goal_calls (indexed_record_at q r)) k" by (simp add: indexed_record_at_def)
next
  fix k assume "k |\<in>| node_call_keys (tree_bucket (indexed_nodes (indexed_record_at q r)) q)"
  then show "q |\<in>| tree_bucket (indexed_node_calls (indexed_record_at q r)) k" by (simp add: indexed_record_at_def)
qed

lemma indexed_replace_fields [simp]:
  "tree_bucket (indexed_goals (indexed_replace q G N r)) p = (if p = q then G else tree_bucket (indexed_goals r) p)"
  "tree_bucket (indexed_nodes (indexed_replace q G N r)) p = (if p = q then N else tree_bucket (indexed_nodes r) p)"
  "indexed_witnesses (indexed_replace q G N r) = indexed_witnesses r"
  "tree_bucket (indexed_unconstructed (indexed_replace q G N r)) p =
    (if p = q then {||} else tree_bucket (indexed_unconstructed r) p)"
  by (simp_all add: indexed_replace_def indexed_record_at_def)

theorem indexed_replace_formed:
  assumes r: "indexed_formed \<kappa> P r" and G: "\<And>hg. hg |\<in>| G \<Longrightarrow> indexed_goal_formed_at P q hg"
    and N: "\<And>hn. hn |\<in>| N \<Longrightarrow> indexed_node_formed_at \<kappa> P q hn"
  shows "indexed_formed \<kappa> P (indexed_replace q G N r)"
proof -
  let ?r = "indexed_replace q G N r"
  have goals: "tree_buckets_formed (indexed_goals ?r) (indexed_goal_formed_at P)"
    using r G by (auto simp: indexed_replace_def indexed_record_at_def indexed_formed_def intro!: tree_buckets_formed_put)
  have nodes: "tree_buckets_formed (indexed_nodes ?r) (indexed_node_formed_at \<kappa> P)"
    using r N by (auto simp: indexed_replace_def indexed_record_at_def indexed_formed_def intro!: tree_buckets_formed_put)
  have counts: "tree_count (indexed_open r) p = card (tree_keys_under (indexed_goals r) p)" for p
    using r by (simp add: indexed_formed_def indexed_open_formed_def)
  have opened: "indexed_open_formed ?r"
    using tree_bucket_count_put[OF counts]
    by (simp add: indexed_open_formed_def indexed_replace_def indexed_record_at_def)
  have recorded: "indexed_recorded_at ?r p" for p
  proof (cases "p = q")
    case True
    show ?thesis unfolding True indexed_replace_def by (rule indexed_record_at_recorded)
  next
    case False
    have old: "indexed_recorded_at r p" using r by (simp add: indexed_formed_def)
    show ?thesis using old False
      by (simp add: indexed_recorded_at_def indexed_replace_def indexed_record_at_def)
  qed
  have unconstructed: "indexed_unconstructed_formed \<kappa> P ?r"
    unfolding indexed_unconstructed_formed_def
  proof (intro allI impI)
    fix p a hn assume a: "a |\<in>| tree_bucket (indexed_unconstructed ?r) p" and hn: "hn |\<in>| tree_bucket (indexed_nodes ?r) p"
    have "p \<noteq> q" using a by (auto split: if_splits)
    then have "a |\<in>| tree_bucket (indexed_unconstructed r) p" "hn |\<in>| tree_bucket (indexed_nodes r) p"
      using a hn by simp_all
    then show "finite_registered_value \<kappa> P (indexed_node_value hn) a = None"
      using r by (simp add: indexed_formed_def indexed_unconstructed_formed_def)
  qed
  show ?thesis using goals nodes opened recorded unconstructed by (simp add: indexed_formed_def)
qed

lemma indexed_replace_same_nodes:
  "indexed_node_set (indexed_replace q G (tree_bucket (indexed_nodes r) q) r) = indexed_node_set r"
proof -
  have "tree_buckets (indexed_nodes (indexed_replace q G (tree_bucket (indexed_nodes r) q) r)) =
      fimage id (tree_buckets (indexed_nodes r))"
    by (rule tree_buckets_map) simp
  then show ?thesis by (simp add: indexed_node_set_def)
qed

lemma indexed_replace_same_goals:
  "indexed_pending (indexed_replace q (tree_bucket (indexed_goals r) q) N r) = indexed_pending r"
proof -
  have "tree_buckets (indexed_goals (indexed_replace q (tree_bucket (indexed_goals r) q) N r)) =
      fimage id (tree_buckets (indexed_goals r))"
    by (rule tree_buckets_map) simp
  then show ?thesis by (simp add: indexed_pending_def)
qed

lemma indexed_replace_pending:
  "g |\<in>| indexed_pending (indexed_replace q G N r) \<longleftrightarrow>
    (\<exists>p hg. p \<noteq> q \<and> hg |\<in>| tree_bucket (indexed_goals r) p \<and> indexed_goal_value hg = g) \<or>
    g |\<in>| fimage indexed_goal_value G"
  by (auto simp: indexed_pending_member fimage.rep_eq split: if_splits)

lemma indexed_replace_node_set:
  "nd |\<in>| indexed_node_set (indexed_replace q G N r) \<longleftrightarrow>
    (\<exists>p hn. p \<noteq> q \<and> hn |\<in>| tree_bucket (indexed_nodes r) p \<and> indexed_node_value hn = nd) \<or>
    nd |\<in>| fimage indexed_node_value N"
  by (auto simp: indexed_node_set_member fimage.rep_eq split: if_splits)

subsection \<open>Placing and removing goals and nodes\<close>

definition indexed_put_goals :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_put_goals q G r = indexed_replace q (tree_bucket (indexed_goals r) q |\<union>| G) (tree_bucket (indexed_nodes r) q) r"

definition indexed_put_nodes :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_node fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_put_nodes q N r = indexed_replace q (tree_bucket (indexed_goals r) q) (tree_bucket (indexed_nodes r) q |\<union>| N) r"

definition indexed_remove_goal :: "('a,'s::linorder,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) indexed_state \<Rightarrow>
    ('a,'s,'d,'c) indexed_state" where
  "indexed_remove_goal g r = (let q = resolution_goal_position g in indexed_replace q
    (ffilter (\<lambda>hg. indexed_goal_value hg \<noteq> g) (tree_bucket (indexed_goals r) q)) (tree_bucket (indexed_nodes r) q) r)"

lemma indexed_put_goals:
  assumes r: "indexed_formed \<kappa> P r" and G: "\<And>hg. hg |\<in>| G \<Longrightarrow> indexed_goal_formed_at P q hg"
  shows "indexed_formed \<kappa> P (indexed_put_goals q G r)"
    "indexed_pending (indexed_put_goals q G r) = indexed_pending r |\<union>| fimage indexed_goal_value G"
    "indexed_node_set (indexed_put_goals q G r) = indexed_node_set r"
    "indexed_witnesses (indexed_put_goals q G r) = indexed_witnesses r"
proof -
  show "indexed_formed \<kappa> P (indexed_put_goals q G r)"
    unfolding indexed_put_goals_def
    by (rule indexed_replace_formed[OF r]) (use G indexed_goal_at[OF r] indexed_node_at[OF r] in
      \<open>auto simp: indexed_goal_formed_at_def indexed_node_formed_at_def\<close>)
  show "indexed_pending (indexed_put_goals q G r) = indexed_pending r |\<union>| fimage indexed_goal_value G"
    unfolding indexed_put_goals_def fset_eq_iff indexed_replace_pending
    by (auto simp: indexed_pending_member fimage.rep_eq)
  show "indexed_node_set (indexed_put_goals q G r) = indexed_node_set r"
    unfolding indexed_put_goals_def by (rule indexed_replace_same_nodes)
  show "indexed_witnesses (indexed_put_goals q G r) = indexed_witnesses r" by (simp add: indexed_put_goals_def)
qed

lemma indexed_put_nodes:
  assumes r: "indexed_formed \<kappa> P r" and N: "\<And>hn. hn |\<in>| N \<Longrightarrow> indexed_node_formed_at \<kappa> P q hn"
  shows "indexed_formed \<kappa> P (indexed_put_nodes q N r)"
    "indexed_node_set (indexed_put_nodes q N r) = indexed_node_set r |\<union>| fimage indexed_node_value N"
    "indexed_pending (indexed_put_nodes q N r) = indexed_pending r"
    "indexed_witnesses (indexed_put_nodes q N r) = indexed_witnesses r"
proof -
  show "indexed_formed \<kappa> P (indexed_put_nodes q N r)"
    unfolding indexed_put_nodes_def
    by (rule indexed_replace_formed[OF r]) (use N indexed_goal_at[OF r] indexed_node_at[OF r] in
      \<open>auto simp: indexed_goal_formed_at_def indexed_node_formed_at_def\<close>)
  show "indexed_node_set (indexed_put_nodes q N r) = indexed_node_set r |\<union>| fimage indexed_node_value N"
    unfolding indexed_put_nodes_def fset_eq_iff indexed_replace_node_set
    by (auto simp: indexed_node_set_member fimage.rep_eq)
  show "indexed_pending (indexed_put_nodes q N r) = indexed_pending r"
    unfolding indexed_put_nodes_def by (rule indexed_replace_same_goals)
  show "indexed_witnesses (indexed_put_nodes q N r) = indexed_witnesses r" by (simp add: indexed_put_nodes_def)
qed

lemma indexed_remove_goal:
  assumes r: "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_remove_goal g r)"
    "indexed_pending (indexed_remove_goal g r) = indexed_pending r |-| {|g|}"
    "indexed_node_set (indexed_remove_goal g r) = indexed_node_set r"
    "indexed_witnesses (indexed_remove_goal g r) = indexed_witnesses r"
proof -
  let ?q = "resolution_goal_position g"
  show "indexed_formed \<kappa> P (indexed_remove_goal g r)"
    unfolding indexed_remove_goal_def Let_def
    by (rule indexed_replace_formed[OF r]) (use indexed_goal_at[OF r] indexed_node_at[OF r] in
      \<open>auto simp: indexed_goal_formed_at_def indexed_node_formed_at_def\<close>)
  show "indexed_node_set (indexed_remove_goal g r) = indexed_node_set r"
    unfolding indexed_remove_goal_def Let_def by (rule indexed_replace_same_nodes)
  show "indexed_witnesses (indexed_remove_goal g r) = indexed_witnesses r"
    by (simp add: indexed_remove_goal_def Let_def)
  have "g' |\<in>| indexed_pending (indexed_remove_goal g r) \<longleftrightarrow> g' |\<in>| indexed_pending r \<and> g' \<noteq> g" for g'
  proof
    assume "g' |\<in>| indexed_pending (indexed_remove_goal g r)"
    then obtain p hg where hg: "hg |\<in>| tree_bucket (indexed_goals (indexed_remove_goal g r)) p" "indexed_goal_value hg = g'"
      by (auto simp: indexed_pending_member)
    then have old: "hg |\<in>| tree_bucket (indexed_goals r) p"
      by (auto simp: indexed_remove_goal_def Let_def ffilter.rep_eq split: if_splits)
    have "g' \<noteq> g"
    proof
      assume e: "g' = g"
      then have "p = ?q" using indexed_goal_at(2)[OF r old] hg(2) by simp
      then show False using hg e by (simp add: indexed_remove_goal_def Let_def ffilter.rep_eq)
    qed
    then show "g' |\<in>| indexed_pending r \<and> g' \<noteq> g" using old hg(2) by (auto simp: indexed_pending_member)
  next
    assume a: "g' |\<in>| indexed_pending r \<and> g' \<noteq> g"
    then obtain p hg where hg: "hg |\<in>| tree_bucket (indexed_goals r) p" "indexed_goal_value hg = g'"
      by (auto simp: indexed_pending_member)
    then have "hg |\<in>| tree_bucket (indexed_goals (indexed_remove_goal g r)) p"
      using a by (auto simp: indexed_remove_goal_def Let_def ffilter.rep_eq)
    then show "g' |\<in>| indexed_pending (indexed_remove_goal g r)" using hg(2) by (auto simp: indexed_pending_member)
  qed
  then show "indexed_pending (indexed_remove_goal g r) = indexed_pending r |-| {|g|}" by (auto simp: fset_eq_iff)
qed

subsection \<open>Adding the goals and nodes of an abstract set\<close>

definition indexed_goals_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset \<Rightarrow>
    's list \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_goals_at P A q = fimage (index_goal P) (ffilter (\<lambda>g. resolution_goal_position g = q) A)"

definition indexed_nodes_at :: "('a,'s,'d,'c) resolution_node fset \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) indexed_node fset" where
  "indexed_nodes_at N q = fimage index_node (ffilter (\<lambda>nd. resolution_node_position nd = q) N)"

definition indexed_add_goals :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_goal fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_add_goals P A r = fold (\<lambda>q. indexed_put_goals q (indexed_goals_at P A q))
    (sorted_list_of_fset (fimage resolution_goal_position A)) r"

definition indexed_add_nodes :: "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_add_nodes N r = fold (\<lambda>q. indexed_put_nodes q (indexed_nodes_at N q))
    (sorted_list_of_fset (fimage resolution_node_position N)) r"

lemma indexed_goals_at_formed: "hg |\<in>| indexed_goals_at P A q \<Longrightarrow> indexed_goal_formed_at P q hg"
  by (auto simp: indexed_goals_at_def indexed_goal_formed_at_def fimage.rep_eq)

lemma indexed_nodes_at_formed: "hn |\<in>| indexed_nodes_at N q \<Longrightarrow> indexed_node_formed_at \<kappa> P q hn"
  by (auto simp: indexed_nodes_at_def indexed_node_formed_at_def fimage.rep_eq)

lemma indexed_goals_at_values: "fimage indexed_goal_value (indexed_goals_at P A q) = ffilter (\<lambda>g. resolution_goal_position g = q) A"
  by (simp add: indexed_goals_at_def fset.map_comp comp_def)

lemma indexed_nodes_at_values: "fimage indexed_node_value (indexed_nodes_at N q) = ffilter (\<lambda>nd. resolution_node_position nd = q) N"
  by (simp add: indexed_nodes_at_def fset.map_comp comp_def)

lemma indexed_add_goals_fold:
  "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (fold (\<lambda>q. indexed_put_goals q (indexed_goals_at P A q)) ps r) \<and>
    indexed_pending (fold (\<lambda>q. indexed_put_goals q (indexed_goals_at P A q)) ps r) =
      indexed_pending r |\<union>| ffilter (\<lambda>g. resolution_goal_position g \<in> set ps) A \<and>
    indexed_node_set (fold (\<lambda>q. indexed_put_goals q (indexed_goals_at P A q)) ps r) = indexed_node_set r \<and>
    indexed_witnesses (fold (\<lambda>q. indexed_put_goals q (indexed_goals_at P A q)) ps r) = indexed_witnesses r"
proof (induction ps arbitrary: r)
  case Nil
  then show ?case by (simp add: fset_eq_iff)
next
  case (Cons q ps)
  let ?r = "indexed_put_goals q (indexed_goals_at P A q) r"
  have f: "indexed_formed \<kappa> P ?r" by (rule indexed_put_goals(1)[OF Cons.prems]) (rule indexed_goals_at_formed)
  have p: "indexed_pending ?r = indexed_pending r |\<union>| ffilter (\<lambda>g. resolution_goal_position g = q) A"
    by (simp add: indexed_put_goals(2)[OF Cons.prems indexed_goals_at_formed] indexed_goals_at_values)
  have o: "indexed_node_set ?r = indexed_node_set r" "indexed_witnesses ?r = indexed_witnesses r"
    by (simp_all add: indexed_put_goals(3,4)[OF Cons.prems indexed_goals_at_formed])
  show ?case using Cons.IH[OF f] p o by (auto simp: fset_eq_iff)
qed

lemma indexed_add_nodes_fold:
  "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (fold (\<lambda>q. indexed_put_nodes q (indexed_nodes_at N q)) ps r) \<and>
    indexed_node_set (fold (\<lambda>q. indexed_put_nodes q (indexed_nodes_at N q)) ps r) =
      indexed_node_set r |\<union>| ffilter (\<lambda>nd. resolution_node_position nd \<in> set ps) N \<and>
    indexed_pending (fold (\<lambda>q. indexed_put_nodes q (indexed_nodes_at N q)) ps r) = indexed_pending r \<and>
    indexed_witnesses (fold (\<lambda>q. indexed_put_nodes q (indexed_nodes_at N q)) ps r) = indexed_witnesses r"
proof (induction ps arbitrary: r)
  case Nil
  then show ?case by (simp add: fset_eq_iff)
next
  case (Cons q ps)
  let ?r = "indexed_put_nodes q (indexed_nodes_at N q) r"
  have f: "indexed_formed \<kappa> P ?r" by (rule indexed_put_nodes(1)[OF Cons.prems]) (rule indexed_nodes_at_formed)
  have p: "indexed_node_set ?r = indexed_node_set r |\<union>| ffilter (\<lambda>nd. resolution_node_position nd = q) N"
    by (simp add: indexed_put_nodes(2)[OF Cons.prems indexed_nodes_at_formed] indexed_nodes_at_values)
  have o: "indexed_pending ?r = indexed_pending r" "indexed_witnesses ?r = indexed_witnesses r"
    by (simp_all add: indexed_put_nodes(3,4)[OF Cons.prems indexed_nodes_at_formed])
  show ?case using Cons.IH[OF f] p o by (auto simp: fset_eq_iff)
qed

lemma indexed_add_goals:
  assumes "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_add_goals P A r)" "indexed_pending (indexed_add_goals P A r) = indexed_pending r |\<union>| A"
    "indexed_node_set (indexed_add_goals P A r) = indexed_node_set r"
    "indexed_witnesses (indexed_add_goals P A r) = indexed_witnesses r"
proof -
  have "ffilter (\<lambda>g. resolution_goal_position g \<in> set (sorted_list_of_fset (fimage resolution_goal_position A))) A = A"
    by (force simp: fset_eq_iff fimage.rep_eq)
  then show "indexed_formed \<kappa> P (indexed_add_goals P A r)" "indexed_pending (indexed_add_goals P A r) = indexed_pending r |\<union>| A"
    "indexed_node_set (indexed_add_goals P A r) = indexed_node_set r"
    "indexed_witnesses (indexed_add_goals P A r) = indexed_witnesses r"
    using indexed_add_goals_fold[OF assms, of A "sorted_list_of_fset (fimage resolution_goal_position A)"]
    by (simp_all add: indexed_add_goals_def)
qed

lemma indexed_add_nodes:
  assumes "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_add_nodes N r)" "indexed_node_set (indexed_add_nodes N r) = indexed_node_set r |\<union>| N"
    "indexed_pending (indexed_add_nodes N r) = indexed_pending r"
    "indexed_witnesses (indexed_add_nodes N r) = indexed_witnesses r"
proof -
  have "ffilter (\<lambda>nd. resolution_node_position nd \<in> set (sorted_list_of_fset (fimage resolution_node_position N))) N = N"
    by (force simp: fset_eq_iff fimage.rep_eq)
  then show "indexed_formed \<kappa> P (indexed_add_nodes N r)" "indexed_node_set (indexed_add_nodes N r) = indexed_node_set r |\<union>| N"
    "indexed_pending (indexed_add_nodes N r) = indexed_pending r"
    "indexed_witnesses (indexed_add_nodes N r) = indexed_witnesses r"
    using indexed_add_nodes_fold[OF assms, where N=N and ps="sorted_list_of_fset (fimage resolution_node_position N)"]
    by (simp_all add: indexed_add_nodes_def)
qed

subsection \<open>The indexed state of an abstract state\<close>

definition indexed_empty :: "(('s,'a) resolution_variable \<times> finite_factor_term) fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) indexed_state" where
  "indexed_empty W = \<lparr>indexed_goals = RBT.empty, indexed_nodes = RBT.empty, indexed_witnesses = W,
    indexed_holders = RBT.empty, indexed_open = RBT.empty, indexed_goal_calls = RBT.empty,
    indexed_node_calls = RBT.empty, indexed_unconstructed = RBT.empty\<rparr>"

lemma indexed_empty:
  "indexed_formed \<kappa> P (indexed_empty W)" "indexed_pending (indexed_empty W) = {||}"
  "indexed_node_set (indexed_empty W) = {||}" "indexed_witnesses (indexed_empty W) = W"
  by (simp_all add: indexed_empty_def indexed_formed_def indexed_recorded_at_def indexed_open_formed_def
      tree_keys_under_def indexed_pending_def indexed_node_set_def goal_call_keys_def node_call_keys_def
      indexed_unconstructed_formed_def)

definition index_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) indexed_state" where
  "index_state P st = indexed_add_goals P (resolution_pending st)
    (indexed_add_nodes (resolution_nodes st) (indexed_empty (resolution_witnesses st)))"

theorem index_state:
  "indexed_formed \<kappa> P (index_state P st)" "indexed_project (index_state P st) = st"
proof -
  have n: "indexed_formed \<kappa> P (indexed_add_nodes (resolution_nodes st) (indexed_empty (resolution_witnesses st)))"
    by (rule indexed_add_nodes(1)[OF indexed_empty(1)])
  show "indexed_formed \<kappa> P (index_state P st)" unfolding index_state_def by (rule indexed_add_goals(1)[OF n])
  have "indexed_pending (index_state P st) = resolution_pending st"
    "indexed_node_set (index_state P st) = resolution_nodes st"
    "indexed_witnesses (index_state P st) = resolution_witnesses st"
    unfolding index_state_def
    by (simp_all add: indexed_add_goals(2-4)[OF n] indexed_add_nodes(2-4)[OF indexed_empty(1)[of \<kappa> P]]
      indexed_empty(2-4))
  then show "indexed_project (index_state P st) = st" by (cases st) (simp add: indexed_project_def)
qed

subsection \<open>Substitution at the holders of the variables it binds\<close>

definition indexed_goal_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> ('a,'s,'d,'c) indexed_goal" where
  "indexed_goal_substitute P \<sigma> D hg = (if indexed_goal_variables hg |\<inter>| D = {||} then hg
    else index_goal P (resolution_goal_substitute \<sigma> (indexed_goal_value hg)))"

definition indexed_node_substitute ::
    "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) indexed_node \<Rightarrow> ('a,'s,'d,'c) indexed_node" where
  "indexed_node_substitute \<sigma> D hn = (if indexed_node_variables hn |\<inter>| D = {||} then hn
    else index_node (resolution_node_substitute \<sigma> (indexed_node_value hn)))"

lemma indexed_goal_substitute_formed_at:
  "indexed_goal_formed_at P q hg \<Longrightarrow> indexed_goal_formed_at P q (indexed_goal_substitute P \<sigma> D hg)"
  by (auto simp: indexed_goal_formed_at_def indexed_goal_substitute_def)

lemma indexed_node_substitute_formed_at:
  "indexed_node_formed_at \<kappa> P q hn \<Longrightarrow> indexed_node_formed_at \<kappa> P q (indexed_node_substitute \<sigma> D hn)"
  by (auto simp: indexed_node_formed_at_def indexed_node_substitute_def)

definition indexed_substitute_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> 's::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_substitute_at P \<sigma> D q r = indexed_replace q (fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) q))
    (fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) q)) r"

definition indexed_substitute_positions :: "('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> 's list fset" where
  "indexed_substitute_positions D r = ffUnion (fimage (tree_bucket (indexed_holders r)) (variable_positions D))"

definition indexed_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_substitute P \<sigma> D r =
    fold (indexed_substitute_at P \<sigma> D) (sorted_list_of_fset (indexed_substitute_positions D r)) r"

lemma indexed_substitute_fold:
  assumes "distinct ps"
  shows "tree_bucket (indexed_goals (fold (indexed_substitute_at P \<sigma> D) ps r)) p = (if p \<in> set ps
      then fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) p) else tree_bucket (indexed_goals r) p)"
    and "tree_bucket (indexed_nodes (fold (indexed_substitute_at P \<sigma> D) ps r)) p = (if p \<in> set ps
      then fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) p) else tree_bucket (indexed_nodes r) p)"
    and "indexed_witnesses (fold (indexed_substitute_at P \<sigma> D) ps r) = indexed_witnesses r"
  using assms by (induction ps arbitrary: r) (auto simp: indexed_substitute_at_def)

lemma indexed_substitute_fold_formed:
  "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (fold (indexed_substitute_at P \<sigma> D) ps r)"
proof (induction ps arbitrary: r)
  case (Cons q ps)
  have "indexed_formed \<kappa> P (indexed_substitute_at P \<sigma> D q r)"
    unfolding indexed_substitute_at_def
  proof (rule indexed_replace_formed[OF Cons.prems])
    fix hg assume "hg |\<in>| fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) q)"
    then obtain hg0 where hg0: "hg0 |\<in>| tree_bucket (indexed_goals r) q" "hg = indexed_goal_substitute P \<sigma> D hg0"
      by (auto simp: fimage.rep_eq)
    have "indexed_goal_formed_at P q hg0"
      using indexed_goal_at[OF Cons.prems hg0(1)] by (simp add: indexed_goal_formed_at_def)
    then show "indexed_goal_formed_at P q hg" unfolding hg0(2) by (rule indexed_goal_substitute_formed_at)
  next
    fix hn assume "hn |\<in>| fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) q)"
    then obtain hn0 where hn0: "hn0 |\<in>| tree_bucket (indexed_nodes r) q" "hn = indexed_node_substitute \<sigma> D hn0"
      by (auto simp: fimage.rep_eq)
    have "indexed_node_formed_at \<kappa> P q hn0"
      using indexed_node_at[OF Cons.prems hn0(1)] by (simp add: indexed_node_formed_at_def)
    then show "indexed_node_formed_at \<kappa> P q hn" unfolding hn0(2) by (rule indexed_node_substitute_formed_at)
  qed
  then show ?case by (simp add: Cons.IH)
qed simp

text \<open>
  A bucket the holder index does not find for the bound variables holds no goal or node holding one of them, so the
  substitution is, at every position, the substitution of every goal and node there.
\<close>

lemma indexed_substitute_unvisited:
  assumes r: "indexed_formed \<kappa> P r" and p: "p |\<notin>| indexed_substitute_positions D r"
  shows "hg |\<in>| tree_bucket (indexed_goals r) p \<Longrightarrow> indexed_goal_variables hg |\<inter>| D = {||}"
    and "hn |\<in>| tree_bucket (indexed_nodes r) p \<Longrightarrow> indexed_node_variables hn |\<inter>| D = {||}"
proof -
  have outside: "p |\<notin>| tree_bucket (indexed_holders r) (fst (fst x))" if "x |\<in>| D" for x
  proof
    assume "p |\<in>| tree_bucket (indexed_holders r) (fst (fst x))"
    then have "p |\<in>| indexed_substitute_positions D r"
      using ffUnion_fimage_member[OF variable_positions_member[OF that]]
      by (simp add: indexed_substitute_positions_def)
    then show False using p by simp
  qed
  show "indexed_goal_variables hg |\<inter>| D = {||}" if "hg |\<in>| tree_bucket (indexed_goals r) p"
    unfolding fset_eq_iff finter_iff fempty_iff using outside indexed_recorded(1)[OF r that] by blast
  show "indexed_node_variables hn |\<inter>| D = {||}" if "hn |\<in>| tree_bucket (indexed_nodes r) p"
    unfolding fset_eq_iff finter_iff fempty_iff using outside indexed_recorded(2)[OF r that] by blast
qed

lemma indexed_substitute_buckets:
  assumes r: "indexed_formed \<kappa> P r"
  shows "tree_bucket (indexed_goals (indexed_substitute P \<sigma> D r)) p =
      fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) p)"
    and "tree_bucket (indexed_nodes (indexed_substitute P \<sigma> D r)) p =
      fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) p)"
proof -
  let ?Q = "indexed_substitute_positions D r"
  have d: "distinct (sorted_list_of_fset ?Q)" by simp
  note fold = indexed_substitute_fold(1)[OF d, where r=r and p=p and P=P and \<sigma>=\<sigma> and D=D]
  note fold' = indexed_substitute_fold(2)[OF d, where r=r and p=p and P=P and \<sigma>=\<sigma> and D=D]
  show "tree_bucket (indexed_goals (indexed_substitute P \<sigma> D r)) p =
      fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) p)"
  proof (cases "p |\<in>| ?Q")
    case True
    then show ?thesis using fold by (simp add: indexed_substitute_def)
  next
    case False
    have "fimage (indexed_goal_substitute P \<sigma> D) (tree_bucket (indexed_goals r) p) = tree_bucket (indexed_goals r) p"
      by (rule fimage_fixed) (simp add: indexed_goal_substitute_def indexed_substitute_unvisited(1)[OF r False])
    then show ?thesis using False fold by (simp add: indexed_substitute_def)
  qed
  show "tree_bucket (indexed_nodes (indexed_substitute P \<sigma> D r)) p =
      fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) p)"
  proof (cases "p |\<in>| ?Q")
    case True
    then show ?thesis using fold' by (simp add: indexed_substitute_def)
  next
    case False
    have "fimage (indexed_node_substitute \<sigma> D) (tree_bucket (indexed_nodes r) p) = tree_bucket (indexed_nodes r) p"
      by (rule fimage_fixed) (simp add: indexed_node_substitute_def indexed_substitute_unvisited(2)[OF r False])
    then show ?thesis using False fold' by (simp add: indexed_substitute_def)
  qed
qed

lemma indexed_goal_substitute_value:
  assumes vars: "indexed_goal_variables hg = resolution_goal_variables (indexed_goal_value hg)"
    and out: "\<And>x. x |\<notin>| D \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "indexed_goal_value (indexed_goal_substitute P \<sigma> D hg) = resolution_goal_substitute \<sigma> (indexed_goal_value hg)"
proof (cases "indexed_goal_variables hg |\<inter>| D = {||}")
  case True
  have "resolution_goal_substitute \<sigma> (indexed_goal_value hg) = indexed_goal_value hg"
  proof (rule resolution_goal_substitute_outside)
    fix x assume "x |\<in>| resolution_goal_variables (indexed_goal_value hg)"
    then have "x |\<in>| indexed_goal_variables hg" using vars by simp
    then have "x |\<notin>| D" using True by (metis finter_iff fempty_iff)
    then show "\<sigma> x = Finite_Variable x" by (rule out)
  qed
  then show ?thesis using True by (simp add: indexed_goal_substitute_def)
qed (simp add: indexed_goal_substitute_def)

lemma indexed_node_substitute_value:
  assumes vars: "indexed_node_variables hn = resolution_node_variables (indexed_node_value hn)"
    and out: "\<And>x. x |\<notin>| D \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "indexed_node_value (indexed_node_substitute \<sigma> D hn) = resolution_node_substitute \<sigma> (indexed_node_value hn)"
proof (cases "indexed_node_variables hn |\<inter>| D = {||}")
  case True
  have "resolution_node_substitute \<sigma> (indexed_node_value hn) = indexed_node_value hn"
  proof (rule resolution_node_substitute_outside)
    fix x assume "x |\<in>| resolution_node_variables (indexed_node_value hn)"
    then have "x |\<in>| indexed_node_variables hn" using vars by simp
    then have "x |\<notin>| D" using True by (metis finter_iff fempty_iff)
    then show "\<sigma> x = Finite_Variable x" by (rule out)
  qed
  then show ?thesis using True by (simp add: indexed_node_substitute_def)
qed (simp add: indexed_node_substitute_def)

theorem indexed_substitute:
  assumes r: "indexed_formed \<kappa> P r" and out: "\<And>x. x |\<notin>| D \<Longrightarrow> \<sigma> x = Finite_Variable x"
  shows "indexed_formed \<kappa> P (indexed_substitute P \<sigma> D r)"
    and "indexed_project (indexed_substitute P \<sigma> D r) = resolution_state_substitute \<sigma> (indexed_project r)"
proof -
  let ?r = "indexed_substitute P \<sigma> D r"
  show "indexed_formed \<kappa> P ?r" unfolding indexed_substitute_def by (rule indexed_substitute_fold_formed[OF r])
  have pending: "indexed_pending ?r = fimage (resolution_goal_substitute \<sigma>) (indexed_pending r)"
  proof -
    have "indexed_pending ?r = fimage indexed_goal_value (fimage (indexed_goal_substitute P \<sigma> D) (tree_buckets (indexed_goals r)))"
      unfolding indexed_pending_def using tree_buckets_map[OF indexed_substitute_buckets(1)[OF r]] by simp
    also have "\<dots> = fimage (\<lambda>hg. resolution_goal_substitute \<sigma> (indexed_goal_value hg)) (tree_buckets (indexed_goals r))"
      unfolding fset.map_comp comp_def
    proof (rule fimage_cong_on)
      fix hg assume "hg |\<in>| tree_buckets (indexed_goals r)"
      then obtain q where "hg |\<in>| tree_bucket (indexed_goals r) q" by (auto simp: tree_buckets_member)
      then show "indexed_goal_value (indexed_goal_substitute P \<sigma> D hg) = resolution_goal_substitute \<sigma> (indexed_goal_value hg)"
        by (rule indexed_goal_substitute_value[OF indexed_goal_variables_at(1)[OF r] out])
    qed
    finally show ?thesis by (simp add: indexed_pending_def fset.map_comp comp_def)
  qed
  have node_set: "indexed_node_set ?r = fimage (resolution_node_substitute \<sigma>) (indexed_node_set r)"
  proof -
    have "indexed_node_set ?r = fimage indexed_node_value (fimage (indexed_node_substitute \<sigma> D) (tree_buckets (indexed_nodes r)))"
      unfolding indexed_node_set_def using tree_buckets_map[OF indexed_substitute_buckets(2)[OF r]] by simp
    also have "\<dots> = fimage (\<lambda>hn. resolution_node_substitute \<sigma> (indexed_node_value hn)) (tree_buckets (indexed_nodes r))"
      unfolding fset.map_comp comp_def
    proof (rule fimage_cong_on)
      fix hn assume "hn |\<in>| tree_buckets (indexed_nodes r)"
      then obtain q where "hn |\<in>| tree_bucket (indexed_nodes r) q" by (auto simp: tree_buckets_member)
      then have "indexed_node_formed \<kappa> P hn" by (rule indexed_node_at(1)[OF r])
      then have "indexed_node_variables hn = resolution_node_variables (indexed_node_value hn)"
        by (simp add: indexed_node_formed_def)
      then show "indexed_node_value (indexed_node_substitute \<sigma> D hn) = resolution_node_substitute \<sigma> (indexed_node_value hn)"
        by (rule indexed_node_substitute_value[OF _ out])
    qed
    finally show ?thesis by (simp add: indexed_node_set_def fset.map_comp comp_def)
  qed
  have w: "indexed_witnesses ?r = indexed_witnesses r"
    unfolding indexed_substitute_def by (rule indexed_substitute_fold(3)) simp
  show "indexed_project ?r = resolution_state_substitute \<sigma> (indexed_project r)"
    using pending node_set w by (simp add: indexed_project_def resolution_state_substitute_def)
qed

section \<open>The tests R3's selection reads, through the indexes\<close>

text \<open>
  Each test of R3's selection (@{const finite_pruned}, @{const finite_reusable}, @{const finite_goal_waits},
  @{const finite_independent_goal}, @{const finite_held}, @{const finite_registration_ready},
  @{const finite_constructed}) is read here through the indexes and the caches, and is proved equal to R3's test at
  the projection. A ground call is pruned by the nodes at the prefixes of its position; it is closed by reuse or waits
  by the nodes and goals the index of calls finds at its key; a node is solved when the count at its position is zero.
\<close>

lemma indexed_node_in_set: "hn |\<in>| tree_bucket (indexed_nodes r) q \<Longrightarrow> indexed_node_value hn |\<in>| indexed_node_set r"
  by (auto simp: indexed_node_set_member)

lemma indexed_goal_in_pending: "hg |\<in>| tree_bucket (indexed_goals r) q \<Longrightarrow> indexed_goal_value hg |\<in>| indexed_pending r"
  by (auto simp: indexed_pending_member)

lemma indexed_node_set_at:
  assumes r: "indexed_formed \<kappa> P r" and nd: "nd |\<in>| indexed_node_set r"
  obtains hn where "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
proof -
  obtain q hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) q" "indexed_node_value hn = nd"
    using nd by (auto simp: indexed_node_set_member)
  have "q = resolution_node_position nd" using indexed_node_at(2)[OF r hn(1)] hn(2) by simp
  then show thesis using that hn by simp
qed

lemma indexed_pending_at:
  assumes r: "indexed_formed \<kappa> P r" and g: "g |\<in>| indexed_pending r"
  obtains hg where "hg |\<in>| tree_bucket (indexed_goals r) (resolution_goal_position g)" "indexed_goal_value hg = g"
proof -
  obtain q hg where hg: "hg |\<in>| tree_bucket (indexed_goals r) q" "indexed_goal_value hg = g"
    using g by (auto simp: indexed_pending_member)
  have "q = resolution_goal_position g" using indexed_goal_at(2)[OF r hg(1)] hg(2) by simp
  then show thesis using that hg by simp
qed

lemma indexed_solved:
  assumes r: "indexed_formed \<kappa> P r"
  shows "tree_count (indexed_open r) (resolution_node_position nd) = 0 \<longleftrightarrow> finite_solved_node (indexed_project r) nd"
  using indexed_solved_count[OF r, of "resolution_node_position nd"] by (simp add: finite_solved_node_def)

lemma indexed_node_call_found:
  assumes r: "indexed_formed \<kappa> P r" and hn: "hn |\<in>| tree_bucket (indexed_nodes r) q"
    and ground: "finite_pattern_variables (resolution_node_call (indexed_node_value hn)) = {||}"
  shows "q |\<in>| tree_bucket (indexed_node_calls r) (resolution_call_key (resolution_node_call (indexed_node_value hn)))"
  by (rule indexed_recorded(4)[OF r node_call_keys_member[OF hn ground]])

subsection \<open>Pruning, reuse and waiting\<close>

definition indexed_pruned :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_pruned r hg = (case indexed_goal_value hg of
      Resolution_Call_Goal q rr d p \<Rightarrow> indexed_goal_variables hg = {||} \<and>
        list_ex (\<lambda>i. fBex (tree_bucket (indexed_nodes r) (take i q)) (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))
          [0..<length q]
    | Resolution_Material_Goal q rr M \<Rightarrow> False)"

lemma indexed_pruned:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "indexed_pruned r hg \<longleftrightarrow> finite_pruned (indexed_project r) (indexed_goal_value hg)"
proof (cases "indexed_goal_value hg")
  case (Resolution_Call_Goal q rr d p)
  have vars: "indexed_goal_variables hg = finite_pattern_variables p"
    using indexed_goal_variables_at(1)[OF r hg] Resolution_Call_Goal by simp
  have "(\<exists>i\<in>set [0..<length q]. fBex (tree_bucket (indexed_nodes r) (take i q))
        (\<lambda>hn. resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)) \<longleftrightarrow>
      fBex (indexed_node_set r) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
  proof
    assume "\<exists>i\<in>set [0..<length q]. fBex (tree_bucket (indexed_nodes r) (take i q))
        (\<lambda>hn. resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)"
    then obtain i hn where i: "i < length q" and hn: "hn |\<in>| tree_bucket (indexed_nodes r) (take i q)"
      and m: "resolution_node_site (indexed_node_value hn) = d" "resolution_node_call (indexed_node_value hn) = p"
      by auto
    have pos: "resolution_node_position (indexed_node_value hn) = take i q" by (rule indexed_node_at(2)[OF r hn])
    have len: "length (take i q) = i" using i by simp
    show "fBex (indexed_node_set r) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    proof (rule rev_bexI[OF indexed_node_in_set[OF hn]])
      show "length (resolution_node_position (indexed_node_value hn)) < length q \<and>
          take (length (resolution_node_position (indexed_node_value hn))) q = resolution_node_position (indexed_node_value hn) \<and>
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p"
        using pos len i m by simp
    qed
  next
    assume "fBex (indexed_node_set r) (\<lambda>nd. length (resolution_node_position nd) < length q \<and>
        take (length (resolution_node_position nd)) q = resolution_node_position nd \<and>
        resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    then obtain nd where nd: "nd |\<in>| indexed_node_set r" "length (resolution_node_position nd) < length q"
        "take (length (resolution_node_position nd)) q = resolution_node_position nd"
        "resolution_node_site nd = d" "resolution_node_call nd = p" by auto
    obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
      by (rule indexed_node_set_at[OF r nd(1)])
    show "\<exists>i\<in>set [0..<length q]. fBex (tree_bucket (indexed_nodes r) (take i q))
        (\<lambda>hn. resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)"
      using nd hn by (intro bexI[of _ "length (resolution_node_position nd)"]) auto
  qed
  then show ?thesis using vars Resolution_Call_Goal by (simp add: indexed_pruned_def finite_pruned_def list_ex_iff)
qed (simp add: indexed_pruned_def finite_pruned_def)

definition indexed_reusable :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_reusable r hg = (case indexed_goal_value hg of
      Resolution_Call_Goal q rr d p \<Rightarrow> indexed_goal_variables hg = {||} \<and>
        fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
          tree_count (indexed_open r) q' = 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
            resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))
    | Resolution_Material_Goal q rr M \<Rightarrow> False)"

lemma indexed_reusable:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "indexed_reusable r hg \<longleftrightarrow> finite_reusable (indexed_project r) (indexed_goal_value hg)"
proof (cases "indexed_goal_value hg")
  case (Resolution_Call_Goal q rr d p)
  have vars: "indexed_goal_variables hg = finite_pattern_variables p"
    using indexed_goal_variables_at(1)[OF r hg] Resolution_Call_Goal by simp
  have eq: "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' = 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)) \<longleftrightarrow>
      fBex (indexed_node_set r) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node (indexed_project r) nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    if ground: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' = 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))"
    then obtain q' hn where q': "finite_position_left q' q" "tree_count (indexed_open r) q' = 0"
      and hn: "hn |\<in>| tree_bucket (indexed_nodes r) q'"
      and m: "resolution_node_site (indexed_node_value hn) = d" "resolution_node_call (indexed_node_value hn) = p"
      by auto
    have pos: "resolution_node_position (indexed_node_value hn) = q'" by (rule indexed_node_at(2)[OF r hn])
    have "finite_solved_node (indexed_project r) (indexed_node_value hn)"
      using indexed_solved[OF r, of "indexed_node_value hn"] pos q'(2) by simp
    then show "fBex (indexed_node_set r) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node (indexed_project r) nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
      using indexed_node_in_set[OF hn] pos q'(1) m by auto
  next
    assume "fBex (indexed_node_set r) (\<lambda>nd. finite_position_left (resolution_node_position nd) q \<and>
        finite_solved_node (indexed_project r) nd \<and> resolution_node_site nd = d \<and> resolution_node_call nd = p)"
    then obtain nd where nd: "nd |\<in>| indexed_node_set r" "finite_position_left (resolution_node_position nd) q"
        "finite_solved_node (indexed_project r) nd" "resolution_node_site nd = d" "resolution_node_call nd = p" by auto
    obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
      by (rule indexed_node_set_at[OF r nd(1)])
    have found: "resolution_node_position nd |\<in>| tree_bucket (indexed_node_calls r) (resolution_call_key p)"
      using indexed_node_call_found[OF r hn(1)] hn(2) nd(5) ground by simp
    have "tree_count (indexed_open r) (resolution_node_position nd) = 0" using indexed_solved[OF r] nd(3) by simp
    then show "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' = 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))"
      using found nd hn by auto
  qed
  show ?thesis
  proof (cases "finite_pattern_variables p = {||}")
    case True
    then show ?thesis using eq[OF True] vars Resolution_Call_Goal by (simp add: indexed_reusable_def finite_reusable_def)
  next
    case False
    then show ?thesis using vars Resolution_Call_Goal by (simp add: indexed_reusable_def finite_reusable_def)
  qed
qed (simp add: indexed_reusable_def finite_reusable_def)

definition indexed_waits :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_waits r hg = (case indexed_goal_value hg of
      Resolution_Call_Goal q rr d p \<Rightarrow> indexed_goal_variables hg = {||} \<and>
        (fBex (tree_bucket (indexed_goal_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_less q' q \<and>
           fBex (tree_bucket (indexed_goals r) q') (\<lambda>h. case indexed_goal_value h of
             Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p
           | Resolution_Material_Goal q'' r'' M \<Rightarrow> False)) \<or>
         fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
           tree_count (indexed_open r) q' \<noteq> 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
             resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)))
    | Resolution_Material_Goal q rr M \<Rightarrow> False)"

lemma indexed_waits:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "indexed_waits r hg \<longleftrightarrow> finite_goal_waits (indexed_project r) (indexed_goal_value hg)"
proof (cases "indexed_goal_value hg")
  case (Resolution_Call_Goal q rr d p)
  have vars: "indexed_goal_variables hg = finite_pattern_variables p"
    using indexed_goal_variables_at(1)[OF r hg] Resolution_Call_Goal by simp
  have goals: "fBex (tree_bucket (indexed_goal_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (tree_bucket (indexed_goals r) q') (\<lambda>h. case indexed_goal_value h of
          Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p | Resolution_Material_Goal q'' r'' M \<Rightarrow> False)) \<longleftrightarrow>
      fBex (indexed_pending r) (\<lambda>h. case h of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    if ground: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (tree_bucket (indexed_goal_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (tree_bucket (indexed_goals r) q') (\<lambda>h. case indexed_goal_value h of
          Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p | Resolution_Material_Goal q'' r'' M \<Rightarrow> False))"
    then obtain q' h where q': "finite_position_less q' q" and h: "h |\<in>| tree_bucket (indexed_goals r) q'"
      and m: "case indexed_goal_value h of Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p
        | Resolution_Material_Goal q'' r'' M \<Rightarrow> False" by auto
    have pos: "resolution_goal_position (indexed_goal_value h) = q'" by (rule indexed_goal_at(2)[OF r h])
    show "fBex (indexed_pending r) (\<lambda>h. case h of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    proof (rule rev_bexI[OF indexed_goal_in_pending[OF h]])
      show "case indexed_goal_value h of Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
          | Resolution_Material_Goal q' r' M \<Rightarrow> False"
        using pos q' m by (cases "indexed_goal_value h") auto
    qed
  next
    assume "fBex (indexed_pending r) (\<lambda>h. case h of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False)"
    then obtain h' where h': "h' |\<in>| indexed_pending r" and m: "case h' of
          Resolution_Call_Goal q' r' d' p' \<Rightarrow> d' = d \<and> p' = p \<and> finite_position_less q' q
        | Resolution_Material_Goal q' r' M \<Rightarrow> False" by auto
    then obtain q' r' where e: "h' = Resolution_Call_Goal q' r' d p" and less: "finite_position_less q' q"
      by (cases h') auto
    obtain h where h: "h |\<in>| tree_bucket (indexed_goals r) (resolution_goal_position h')" "indexed_goal_value h = h'"
      by (rule indexed_pending_at[OF r h'])
    have "indexed_goal_variables h = {||}" using indexed_goal_variables_at(1)[OF r h(1)] h(2) e ground by simp
    then have "resolution_call_key p |\<in>| goal_call_keys (tree_bucket (indexed_goals r) q')"
      using goal_call_keys_member[of h _ q' r' d p] h e by simp
    then have "q' |\<in>| tree_bucket (indexed_goal_calls r) (resolution_call_key p)" by (rule indexed_recorded(3)[OF r])
    then show "fBex (tree_bucket (indexed_goal_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_less q' q \<and>
        fBex (tree_bucket (indexed_goals r) q') (\<lambda>h. case indexed_goal_value h of
          Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p | Resolution_Material_Goal q'' r'' M \<Rightarrow> False))"
    proof (rule rev_bexI)
      have hq: "h |\<in>| tree_bucket (indexed_goals r) q'" using h(1) e by simp
      have "case indexed_goal_value h of Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p
          | Resolution_Material_Goal q'' r'' M \<Rightarrow> False" using h(2) e by simp
      then show "finite_position_less q' q \<and> fBex (tree_bucket (indexed_goals r) q') (\<lambda>h. case indexed_goal_value h of
          Resolution_Call_Goal q'' r'' d' p' \<Rightarrow> d' = d \<and> p' = p | Resolution_Material_Goal q'' r'' M \<Rightarrow> False)"
        using less hq by blast
    qed
  qed
  have nodes: "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' \<noteq> 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p)) \<longleftrightarrow>
      fBex (indexed_node_set r) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and>
        \<not> finite_solved_node (indexed_project r) nd)"
    if ground: "finite_pattern_variables p = {||}"
  proof
    assume "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' \<noteq> 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))"
    then obtain q' hn where q': "finite_position_left q' q" "tree_count (indexed_open r) q' \<noteq> 0"
      and hn: "hn |\<in>| tree_bucket (indexed_nodes r) q'"
      and m: "resolution_node_site (indexed_node_value hn) = d" "resolution_node_call (indexed_node_value hn) = p"
      by auto
    have pos: "resolution_node_position (indexed_node_value hn) = q'" by (rule indexed_node_at(2)[OF r hn])
    have "\<not> finite_solved_node (indexed_project r) (indexed_node_value hn)"
      using indexed_solved[OF r, of "indexed_node_value hn"] pos q'(2) by simp
    then show "fBex (indexed_node_set r) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and>
        \<not> finite_solved_node (indexed_project r) nd)"
      using indexed_node_in_set[OF hn] pos q'(1) m by auto
  next
    assume "fBex (indexed_node_set r) (\<lambda>nd. resolution_node_site nd = d \<and> resolution_node_call nd = p \<and>
        finite_position_left (resolution_node_position nd) q \<and>
        \<not> finite_solved_node (indexed_project r) nd)"
    then obtain nd where nd: "nd |\<in>| indexed_node_set r" "resolution_node_site nd = d" "resolution_node_call nd = p"
        "finite_position_left (resolution_node_position nd) q"
        "\<not> finite_solved_node (indexed_project r) nd" by auto
    obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
      by (rule indexed_node_set_at[OF r nd(1)])
    have found: "resolution_node_position nd |\<in>| tree_bucket (indexed_node_calls r) (resolution_call_key p)"
      using indexed_node_call_found[OF r hn(1)] hn(2) nd(3) ground by simp
    have "tree_count (indexed_open r) (resolution_node_position nd) \<noteq> 0" using indexed_solved[OF r] nd(5) by simp
    then show "fBex (tree_bucket (indexed_node_calls r) (resolution_call_key p)) (\<lambda>q'. finite_position_left q' q \<and>
        tree_count (indexed_open r) q' \<noteq> 0 \<and> fBex (tree_bucket (indexed_nodes r) q') (\<lambda>hn.
          resolution_node_site (indexed_node_value hn) = d \<and> resolution_node_call (indexed_node_value hn) = p))"
      using found nd hn by auto
  qed
  show ?thesis
  proof (cases "finite_pattern_variables p = {||}")
    case True
    then show ?thesis using goals[OF True] nodes[OF True] vars Resolution_Call_Goal
      by (simp add: indexed_waits_def finite_goal_waits_def)
  next
    case False
    then show ?thesis using vars Resolution_Call_Goal by (simp add: indexed_waits_def finite_goal_waits_def)
  qed
qed (simp add: indexed_waits_def finite_goal_waits_def)

subsection \<open>Independence and holding\<close>

definition indexed_independent :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_independent r hg = (case indexed_goal_value hg of
      Resolution_Call_Goal q rr d p \<Rightarrow> indexed_goal_variables hg \<noteq> {||} \<and>
        fBall (indexed_goal_variables hg) (\<lambda>x. fBall (tree_bucket (indexed_holders r) (fst (fst x)))
          (\<lambda>q'. fBall (tree_bucket (indexed_goals r) q') (\<lambda>h. h = hg \<or> x |\<notin>| indexed_goal_variables h)))
    | Resolution_Material_Goal q rr M \<Rightarrow> False)"

lemma indexed_independent:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "indexed_independent r hg \<longleftrightarrow> finite_independent_goal (indexed_pending r) (indexed_goal_value hg)"
proof (cases "indexed_goal_value hg")
  case (Resolution_Call_Goal q rr d p)
  have vars: "indexed_goal_variables hg = finite_pattern_variables p"
    using indexed_goal_variables_at(1)[OF r hg] Resolution_Call_Goal by simp
  have eq: "fBall (indexed_goal_variables hg) (\<lambda>x. fBall (tree_bucket (indexed_holders r) (fst (fst x)))
          (\<lambda>q'. fBall (tree_bucket (indexed_goals r) q') (\<lambda>h. h = hg \<or> x |\<notin>| indexed_goal_variables h))) \<longleftrightarrow>
      fBall (indexed_pending r) (\<lambda>h. h = indexed_goal_value hg \<or>
        resolution_goal_variables h |\<inter>| resolution_goal_variables (indexed_goal_value hg) = {||})"
  proof
    assume all: "fBall (indexed_goal_variables hg) (\<lambda>x. fBall (tree_bucket (indexed_holders r) (fst (fst x)))
          (\<lambda>q'. fBall (tree_bucket (indexed_goals r) q') (\<lambda>h. h = hg \<or> x |\<notin>| indexed_goal_variables h)))"
    show "fBall (indexed_pending r) (\<lambda>h. h = indexed_goal_value hg \<or>
        resolution_goal_variables h |\<inter>| resolution_goal_variables (indexed_goal_value hg) = {||})"
    proof
      fix h' assume h': "h' \<in> fset (indexed_pending r)"
      obtain h where h: "h |\<in>| tree_bucket (indexed_goals r) (resolution_goal_position h')" "indexed_goal_value h = h'"
        by (rule indexed_pending_at[OF r h'])
      show "h' = indexed_goal_value hg \<or>
          resolution_goal_variables h' |\<inter>| resolution_goal_variables (indexed_goal_value hg) = {||}"
      proof (cases "h' = indexed_goal_value hg")
        case False
        note ne = False
        have "x |\<notin>| resolution_goal_variables h'" if x: "x |\<in>| resolution_goal_variables (indexed_goal_value hg)" for x
        proof
          assume xh: "x |\<in>| resolution_goal_variables h'"
          have xh': "x |\<in>| indexed_goal_variables h" using xh h indexed_goal_variables_at(1)[OF r h(1)] by simp
          have xg: "x |\<in>| indexed_goal_variables hg" using x indexed_goal_variables_at(1)[OF r hg] by simp
          have "resolution_goal_position h' |\<in>| tree_bucket (indexed_holders r) (fst (fst x))"
            by (rule indexed_recorded(1)[OF r h(1) xh'])
          then have "h = hg \<or> x |\<notin>| indexed_goal_variables h" using all xg h(1) by blast
          then show False using ne h(2) xh' by auto
        qed
        then have "resolution_goal_variables h' |\<inter>| resolution_goal_variables (indexed_goal_value hg) = {||}"
          unfolding fset_eq_iff finter_iff fempty_iff by blast
        then show ?thesis by simp
      qed simp
    qed
  next
    assume all: "fBall (indexed_pending r) (\<lambda>h. h = indexed_goal_value hg \<or>
        resolution_goal_variables h |\<inter>| resolution_goal_variables (indexed_goal_value hg) = {||})"
    show "fBall (indexed_goal_variables hg) (\<lambda>x. fBall (tree_bucket (indexed_holders r) (fst (fst x)))
          (\<lambda>q'. fBall (tree_bucket (indexed_goals r) q') (\<lambda>h. h = hg \<or> x |\<notin>| indexed_goal_variables h)))"
    proof (intro ballI)
      fix x q' h assume x: "x \<in> fset (indexed_goal_variables hg)"
        and q': "q' \<in> fset (tree_bucket (indexed_holders r) (fst (fst x)))"
        and h: "h \<in> fset (tree_bucket (indexed_goals r) q')"
      show "h = hg \<or> x |\<notin>| indexed_goal_variables h"
      proof (cases "h = hg")
        case False
        then have ne: "indexed_goal_value h \<noteq> indexed_goal_value hg" using indexed_goal_unique(1)[OF r h hg] by blast
        have "indexed_goal_value h |\<in>| indexed_pending r" by (rule indexed_goal_in_pending[OF h])
        then have dj: "resolution_goal_variables (indexed_goal_value h) |\<inter>|
            resolution_goal_variables (indexed_goal_value hg) = {||}"
          using all ne by blast
        have "x |\<in>| resolution_goal_variables (indexed_goal_value hg)"
          using x indexed_goal_variables_at(1)[OF r hg] by simp
        then have "x |\<notin>| resolution_goal_variables (indexed_goal_value h)" using dj by (metis finter_iff fempty_iff)
        then have "x |\<notin>| indexed_goal_variables h" using indexed_goal_variables_at(1)[OF r h] by simp
        then show ?thesis by simp
      qed simp
    qed
  qed
  then show ?thesis using vars Resolution_Call_Goal by (simp add: indexed_independent_def finite_independent_goal_def)
qed (simp add: indexed_independent_def finite_independent_goal_def)

definition indexed_held :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool" where
  "indexed_held \<kappa> r hg = fBex (indexed_goal_variables hg) (\<lambda>x. snd (fst x) \<and>
    fBex (tree_bucket (indexed_nodes r) (fst (fst x))) (\<lambda>hn. snd x |\<in>| finite_free_registered \<kappa> (indexed_node_value hn)))"

lemma indexed_held:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "indexed_held \<kappa> r hg \<longleftrightarrow> finite_held \<kappa> (indexed_project r) (indexed_goal_value hg)"
proof -
  have vars: "indexed_goal_variables hg = resolution_goal_variables (indexed_goal_value hg)"
    by (rule indexed_goal_variables_at(1)[OF r hg])
  show ?thesis
  proof
    assume "indexed_held \<kappa> r hg"
    then obtain x hn where x: "x |\<in>| indexed_goal_variables hg" "snd (fst x)"
      and hn: "hn |\<in>| tree_bucket (indexed_nodes r) (fst (fst x))"
      and a: "snd x |\<in>| finite_free_registered \<kappa> (indexed_node_value hn)"
      unfolding indexed_held_def by blast
    have pos: "resolution_node_position (indexed_node_value hn) = fst (fst x)" by (rule indexed_node_at(2)[OF r hn])
    have xe: "((resolution_node_position (indexed_node_value hn), True), snd x) = x" using x(2) pos by (cases x) auto
    show "finite_held \<kappa> (indexed_project r) (indexed_goal_value hg)"
      unfolding finite_held_def using indexed_node_in_set[OF hn] a x(1) xe vars by force
  next
    assume "finite_held \<kappa> (indexed_project r) (indexed_goal_value hg)"
    then obtain nd a where nd: "nd |\<in>| indexed_node_set r" and a: "a |\<in>| finite_free_registered \<kappa> nd"
      and x: "((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables (indexed_goal_value hg)"
      by (auto simp: finite_held_def)
    obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
      by (rule indexed_node_set_at[OF r nd])
    show "indexed_held \<kappa> r hg" unfolding indexed_held_def using hn a x vars by force
  qed
qed

subsection \<open>Readiness and construction\<close>

definition indexed_goal_holders :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_goal_holders r x = ffilter (\<lambda>h. x |\<in>| indexed_goal_variables h)
    (ffUnion (fimage (tree_bucket (indexed_goals r)) (tree_bucket (indexed_holders r) (fst (fst x)))))"

lemma indexed_goal_holders_at:
  "h |\<in>| indexed_goal_holders r x \<longleftrightarrow>
    (\<exists>q. q |\<in>| tree_bucket (indexed_holders r) (fst (fst x)) \<and> h |\<in>| tree_bucket (indexed_goals r) q) \<and>
    x |\<in>| indexed_goal_variables h"
  by (auto simp: indexed_goal_holders_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)

lemma indexed_goal_holders:
  assumes r: "indexed_formed \<kappa> P r"
  shows "fimage indexed_goal_value (indexed_goal_holders r x) = finite_goal_holders (indexed_pending r) x"
proof -
  have "g |\<in>| fimage indexed_goal_value (indexed_goal_holders r x) \<longleftrightarrow> g |\<in>| finite_goal_holders (indexed_pending r) x" for g
  proof
    assume "g |\<in>| fimage indexed_goal_value (indexed_goal_holders r x)"
    then obtain h q where h: "h |\<in>| tree_bucket (indexed_goals r) q" "x |\<in>| indexed_goal_variables h" "g = indexed_goal_value h"
      by (auto simp: indexed_goal_holders_at fimage.rep_eq)
    then show "g |\<in>| finite_goal_holders (indexed_pending r) x"
      using indexed_goal_in_pending[OF h(1)] indexed_goal_variables_at(1)[OF r h(1)]
      by (auto simp: finite_goal_holders_def ffilter.rep_eq)
  next
    assume "g |\<in>| finite_goal_holders (indexed_pending r) x"
    then have g: "g |\<in>| indexed_pending r" "x |\<in>| resolution_goal_variables g"
      by (auto simp: finite_goal_holders_def ffilter.rep_eq)
    obtain h where h: "h |\<in>| tree_bucket (indexed_goals r) (resolution_goal_position g)" "indexed_goal_value h = g"
      by (rule indexed_pending_at[OF r g(1)])
    have xh: "x |\<in>| indexed_goal_variables h" using g(2) h indexed_goal_variables_at(1)[OF r h(1)] by simp
    have "resolution_goal_position g |\<in>| tree_bucket (indexed_holders r) (fst (fst x))"
      by (rule indexed_recorded(1)[OF r h(1) xh])
    then have "h |\<in>| indexed_goal_holders r x" using h(1) xh by (auto simp: indexed_goal_holders_at)
    then show "g |\<in>| fimage indexed_goal_value (indexed_goal_holders r x)" using h(2) by (force simp: fimage.rep_eq)
  qed
  then show ?thesis by (auto simp: fset_eq_iff)
qed

definition indexed_ready :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> bool" where
  "indexed_ready r nd a = (let x = ((resolution_node_position nd,True),a); H = indexed_goal_holders r x in
    H \<noteq> {||} \<and> fBall H (\<lambda>h. indexed_goal_variables h |\<subseteq>| {|x|}))"

lemma indexed_ready:
  assumes r: "indexed_formed \<kappa> P r"
  shows "indexed_ready r nd a \<longleftrightarrow> finite_registration_ready (indexed_pending r) nd a"
proof -
  let ?x = "((resolution_node_position nd,True),a)"
  let ?H = "indexed_goal_holders r ?x"
  have H: "finite_goal_holders (indexed_pending r) ?x = fimage indexed_goal_value ?H"
    by (rule indexed_goal_holders[OF r, symmetric])
  have v: "indexed_goal_variables h = resolution_goal_variables (indexed_goal_value h)" if "h |\<in>| ?H" for h
    using that indexed_goal_variables_at(1)[OF r] by (auto simp: indexed_goal_holders_at)
  have e: "fimage indexed_goal_value ?H = {||} \<longleftrightarrow> ?H = {||}" by (auto simp: fset_eq_iff fimage.rep_eq)
  have b: "fBall (fimage indexed_goal_value ?H) (\<lambda>g. resolution_goal_variables g |\<subseteq>| {|?x|}) \<longleftrightarrow>
      fBall ?H (\<lambda>h. indexed_goal_variables h |\<subseteq>| {|?x|})"
    using v by (auto simp: fimage.rep_eq)
  show ?thesis unfolding indexed_ready_def finite_registration_ready_def Let_def H e b by simp
qed

definition indexed_value_none :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> bool" where
  "indexed_value_none \<kappa> P r nd a \<longleftrightarrow> a |\<in>| tree_bucket (indexed_unconstructed r) (resolution_node_position nd) \<or>
    finite_registered_value \<kappa> P nd a = None"

lemma indexed_value_none:
  assumes r: "indexed_formed \<kappa> P r" and nd: "nd |\<in>| indexed_node_set r"
  shows "indexed_value_none \<kappa> P r nd a \<longleftrightarrow> finite_registered_value \<kappa> P nd a = None"
proof -
  obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
    by (rule indexed_node_set_at[OF r nd])
  show ?thesis using r hn by (auto simp: indexed_value_none_def indexed_formed_def indexed_unconstructed_formed_def)
qed

definition indexed_constructed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a fset" where
  "indexed_constructed \<kappa> P r nd = ffilter (\<lambda>a. indexed_ready r nd a \<and> \<not> indexed_value_none \<kappa> P r nd a)
    (finite_free_registered \<kappa> nd)"

lemma indexed_constructed:
  assumes r: "indexed_formed \<kappa> P r" and nd: "nd |\<in>| indexed_node_set r"
  shows "indexed_constructed \<kappa> P r nd = finite_constructed \<kappa> P (indexed_pending r) nd"
  by (auto simp: fset_eq_iff indexed_constructed_def finite_constructed_def ffilter.rep_eq indexed_ready[OF r]
      indexed_value_none[OF r nd])

definition indexed_registered_positions :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> 's list fset" where
  "indexed_registered_positions r = fimage (\<lambda>x. fst (fst x))
    (ffilter (\<lambda>x. snd (fst x)) (ffUnion (fimage indexed_goal_variables (tree_buckets (indexed_goals r)))))"

definition indexed_construction_nodes :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_node fset" where
  "indexed_construction_nodes \<kappa> P r = ffilter (\<lambda>hn. indexed_constructed \<kappa> P r (indexed_node_value hn) \<noteq> {||})
    (ffUnion (fimage (tree_bucket (indexed_nodes r)) (indexed_registered_positions r)))"

lemma indexed_construction_nodes:
  assumes r: "indexed_formed \<kappa> P r"
  shows "fimage indexed_node_value (indexed_construction_nodes \<kappa> P r) =
      ffilter (\<lambda>nd. finite_constructed \<kappa> P (indexed_pending r) nd \<noteq> {||}) (indexed_node_set r)"
    and "hn |\<in>| indexed_construction_nodes \<kappa> P r \<Longrightarrow> \<exists>q. hn |\<in>| tree_bucket (indexed_nodes r) q"
proof -
  have cand: "\<exists>q. hn |\<in>| tree_bucket (indexed_nodes r) q" if "hn |\<in>| indexed_construction_nodes \<kappa> P r" for hn
    using that by (auto simp: indexed_construction_nodes_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)
  then show "hn |\<in>| indexed_construction_nodes \<kappa> P r \<Longrightarrow> \<exists>q. hn |\<in>| tree_bucket (indexed_nodes r) q" .
  have "nd |\<in>| fimage indexed_node_value (indexed_construction_nodes \<kappa> P r) \<longleftrightarrow>
      nd |\<in>| indexed_node_set r \<and> finite_constructed \<kappa> P (indexed_pending r) nd \<noteq> {||}" for nd
  proof
    assume "nd |\<in>| fimage indexed_node_value (indexed_construction_nodes \<kappa> P r)"
    then obtain hn where hn: "hn |\<in>| indexed_construction_nodes \<kappa> P r" "nd = indexed_node_value hn"
      by (auto simp: fimage.rep_eq)
    obtain q where q: "hn |\<in>| tree_bucket (indexed_nodes r) q" using cand[OF hn(1)] by blast
    have "indexed_constructed \<kappa> P r nd \<noteq> {||}" using hn by (auto simp: indexed_construction_nodes_def ffilter.rep_eq)
    then show "nd |\<in>| indexed_node_set r \<and> finite_constructed \<kappa> P (indexed_pending r) nd \<noteq> {||}"
      using indexed_node_in_set[OF q] hn(2) indexed_constructed[OF r] by auto
  next
    assume a: "nd |\<in>| indexed_node_set r \<and> finite_constructed \<kappa> P (indexed_pending r) nd \<noteq> {||}"
    then obtain b where b: "b |\<in>| finite_constructed \<kappa> P (indexed_pending r) nd" by (metis all_not_fin_conv)
    let ?x = "((resolution_node_position nd,True),b)"
    have "finite_goal_holders (indexed_pending r) ?x \<noteq> {||}"
      using b by (auto simp: finite_constructed_def finite_registration_ready_def Let_def ffilter.rep_eq)
    then obtain g where g: "g |\<in>| indexed_pending r" "?x |\<in>| resolution_goal_variables g"
      by (auto simp: finite_goal_holders_def ffilter.rep_eq fset_eq_iff)
    obtain h where h: "h |\<in>| tree_bucket (indexed_goals r) (resolution_goal_position g)" "indexed_goal_value h = g"
      by (rule indexed_pending_at[OF r g(1)])
    have xh: "?x |\<in>| indexed_goal_variables h" using g(2) h indexed_goal_variables_at(1)[OF r h(1)] by simp
    have "?x |\<in>| ffUnion (fimage indexed_goal_variables (tree_buckets (indexed_goals r)))"
      using ffUnion_fimage_member[of h "tree_buckets (indexed_goals r)" ?x indexed_goal_variables] h(1) xh
      by (auto simp: tree_buckets_member)
    then have pos: "resolution_node_position nd |\<in>| indexed_registered_positions r"
      by (force simp: indexed_registered_positions_def fimage.rep_eq ffilter.rep_eq)
    obtain hn where hn: "hn |\<in>| tree_bucket (indexed_nodes r) (resolution_node_position nd)" "indexed_node_value hn = nd"
      by (rule indexed_node_set_at[OF r conjunct1[OF a]])
    have "indexed_constructed \<kappa> P r nd \<noteq> {||}" using a indexed_constructed[OF r] by simp
    then have "hn |\<in>| indexed_construction_nodes \<kappa> P r"
      using hn pos by (force simp: indexed_construction_nodes_def ffilter.rep_eq ffUnion.rep_eq fimage.rep_eq)
    then show "nd |\<in>| fimage indexed_node_value (indexed_construction_nodes \<kappa> P r)" using hn(2) by (force simp: fimage.rep_eq)
  qed
  then show "fimage indexed_node_value (indexed_construction_nodes \<kappa> P r) =
      ffilter (\<lambda>nd. finite_constructed \<kappa> P (indexed_pending r) nd \<noteq> {||}) (indexed_node_set r)"
    by (auto simp: fset_eq_iff ffilter.rep_eq)
qed

subsection \<open>The construction step\<close>

definition indexed_construction_substitution :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a fset \<Rightarrow>
    ('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern" where
  "indexed_construction_substitution \<kappa> P nd C z = (case z of ((q,b),a) \<Rightarrow>
    if b \<and> q = resolution_node_position nd \<and> a |\<in>| C then
      (case finite_registered_value \<kappa> P nd a of Some v \<Rightarrow> finite_exact_term_pattern v | None \<Rightarrow> Finite_Variable z)
    else Finite_Variable z)"

definition indexed_construction_step :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_node \<Rightarrow>
    ('a,'s,'d,'c) indexed_state" where
  "indexed_construction_step \<kappa> P r hn = (let nd = indexed_node_value hn; C = indexed_constructed \<kappa> P r nd in
    indexed_substitute P (indexed_construction_substitution \<kappa> P nd C)
      (fimage (\<lambda>a. ((resolution_node_position nd,True),a)) C)
      (r\<lparr>indexed_witnesses := indexed_witnesses r |\<union>| ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
          Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||}) C)\<rparr>))"

lemma indexed_witnesses_update:
  "indexed_formed \<kappa> P (r\<lparr>indexed_witnesses := W\<rparr>) \<longleftrightarrow> indexed_formed \<kappa> P r"
  "indexed_project (r\<lparr>indexed_witnesses := W\<rparr>) = Resolution_State (indexed_pending r) (indexed_node_set r) W"
  by (simp_all add: indexed_formed_def indexed_recorded_at_def indexed_open_formed_def indexed_unconstructed_formed_def
      indexed_project_def indexed_pending_def indexed_node_set_def)

theorem indexed_construction_step:
  assumes r: "indexed_formed \<kappa> P r" and hn: "hn |\<in>| tree_bucket (indexed_nodes r) q0"
  shows "indexed_formed \<kappa> P (indexed_construction_step \<kappa> P r hn)"
    and "indexed_project (indexed_construction_step \<kappa> P r hn) =
      finite_construction_step \<kappa> P (indexed_project r) (indexed_node_value hn)"
proof -
  let ?nd = "indexed_node_value hn"
  let ?G = "indexed_pending r"
  let ?C = "indexed_constructed \<kappa> P r ?nd"
  have C: "?C = finite_constructed \<kappa> P ?G ?nd" by (rule indexed_constructed[OF r indexed_node_in_set[OF hn]])
  let ?W = "indexed_witnesses r |\<union>| ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P ?nd a of
          Some v \<Rightarrow> {|(((resolution_node_position ?nd,True),a),v)|} | None \<Rightarrow> {||}) ?C)"
  let ?r = "r\<lparr>indexed_witnesses := ?W\<rparr>"
  have fr: "indexed_formed \<kappa> P ?r" using r by (simp add: indexed_witnesses_update)
  have out: "indexed_construction_substitution \<kappa> P ?nd ?C z = Finite_Variable z"
    if "z |\<notin>| fimage (\<lambda>a. ((resolution_node_position ?nd,True),a)) ?C" for z
    using that by (auto simp: indexed_construction_substitution_def fimage.rep_eq split: prod.splits)
  have sub: "indexed_construction_substitution \<kappa> P ?nd (finite_constructed \<kappa> P ?G ?nd) =
      finite_construction_substitution \<kappa> P ?G ?nd"
    by (auto simp: fun_eq_iff indexed_construction_substitution_def finite_construction_substitution_def
        split: prod.splits)
  show "indexed_formed \<kappa> P (indexed_construction_step \<kappa> P r hn)"
    unfolding indexed_construction_step_def Let_def by (rule indexed_substitute(1)[OF fr out])
  have "indexed_project (indexed_construction_step \<kappa> P r hn) =
      resolution_state_substitute (indexed_construction_substitution \<kappa> P ?nd ?C) (indexed_project ?r)"
    unfolding indexed_construction_step_def Let_def by (rule indexed_substitute(2)[OF fr out])
  then show "indexed_project (indexed_construction_step \<kappa> P r hn) =
      finite_construction_step \<kappa> P (indexed_project r) (indexed_node_value hn)"
    by (simp add: indexed_witnesses_update sub C finite_construction_step_def Let_def)
qed

subsection \<open>F4: the constructions that returned nothing are kept\<close>

definition indexed_refresh_at :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_refresh_at \<kappa> P q r = (let N = tree_bucket (indexed_nodes r) q;
      U = ffilter (\<lambda>a. a |\<notin>| tree_bucket (indexed_unconstructed r) q \<and>
          fBall N (\<lambda>hn. finite_registered_value \<kappa> P (indexed_node_value hn) a = None))
        (ffUnion (fimage (\<lambda>hn. ffilter (indexed_ready r (indexed_node_value hn))
          (finite_free_registered \<kappa> (indexed_node_value hn))) N)) in
    if U = {||} then r else r\<lparr>indexed_unconstructed :=
      RBT.insert q (tree_bucket (indexed_unconstructed r) q |\<union>| U) (indexed_unconstructed r)\<rparr>)"

definition indexed_refresh :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_state" where
  "indexed_refresh \<kappa> P r = fold (indexed_refresh_at \<kappa> P) (sorted_list_of_fset (indexed_registered_positions r)) r"

lemma indexed_unconstructed_update:
  assumes r: "indexed_formed \<kappa> P r"
    and U: "\<And>a hn. a |\<in>| U \<Longrightarrow> hn |\<in>| tree_bucket (indexed_nodes r) q \<Longrightarrow>
      finite_registered_value \<kappa> P (indexed_node_value hn) a = None"
  shows "indexed_formed \<kappa> P (r\<lparr>indexed_unconstructed :=
      RBT.insert q (tree_bucket (indexed_unconstructed r) q |\<union>| U) (indexed_unconstructed r)\<rparr>)"
    and "indexed_project (r\<lparr>indexed_unconstructed := t\<rparr>) = indexed_project r"
proof -
  let ?r = "r\<lparr>indexed_unconstructed := RBT.insert q (tree_bucket (indexed_unconstructed r) q |\<union>| U) (indexed_unconstructed r)\<rparr>"
  have u: "indexed_unconstructed_formed \<kappa> P ?r"
    unfolding indexed_unconstructed_formed_def
  proof (intro allI impI)
    fix p a hn assume a: "a |\<in>| tree_bucket (indexed_unconstructed ?r) p" and hn: "hn |\<in>| tree_bucket (indexed_nodes ?r) p"
    show "finite_registered_value \<kappa> P (indexed_node_value hn) a = None"
    proof (cases "p = q \<and> a |\<in>| U")
      case True
      then show ?thesis using U hn by simp
    next
      case False
      then have "a |\<in>| tree_bucket (indexed_unconstructed r) p" using a by (auto split: if_splits)
      then show ?thesis using r hn by (simp add: indexed_formed_def indexed_unconstructed_formed_def)
    qed
  qed
  show "indexed_formed \<kappa> P ?r" using r u by (simp add: indexed_formed_def indexed_recorded_at_def indexed_open_formed_def)
  show "indexed_project (r\<lparr>indexed_unconstructed := t\<rparr>) = indexed_project r"
    by (simp add: indexed_project_def indexed_pending_def indexed_node_set_def)
qed

lemma indexed_refresh_at:
  assumes r: "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_refresh_at \<kappa> P q r) \<and> indexed_project (indexed_refresh_at \<kappa> P q r) = indexed_project r"
proof -
  let ?N = "tree_bucket (indexed_nodes r) q"
  let ?U = "ffilter (\<lambda>a. a |\<notin>| tree_bucket (indexed_unconstructed r) q \<and>
          fBall ?N (\<lambda>hn. finite_registered_value \<kappa> P (indexed_node_value hn) a = None))
        (ffUnion (fimage (\<lambda>hn. ffilter (indexed_ready r (indexed_node_value hn))
          (finite_free_registered \<kappa> (indexed_node_value hn))) ?N))"
  note upd = indexed_unconstructed_update[OF r, where U="?U" and q=q]
  have f: "indexed_formed \<kappa> P (r\<lparr>indexed_unconstructed :=
      RBT.insert q (tree_bucket (indexed_unconstructed r) q |\<union>| ?U) (indexed_unconstructed r)\<rparr>)"
    by (rule upd(1)) (auto simp: ffilter.rep_eq)
  show ?thesis
  proof (cases "?U = {||}")
    case True
    then show ?thesis using r by (simp add: indexed_refresh_at_def Let_def)
  next
    case False
    then show ?thesis using f upd(2) by (simp add: indexed_refresh_at_def Let_def)
  qed
qed

lemma indexed_refresh:
  "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (indexed_refresh \<kappa> P r) \<and> indexed_project (indexed_refresh \<kappa> P r) = indexed_project r"
proof -
  have "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (fold (indexed_refresh_at \<kappa> P) ps r) \<and>
      indexed_project (fold (indexed_refresh_at \<kappa> P) ps r) = indexed_project r" for ps r
  proof (induction ps arbitrary: r)
    case (Cons a ps)
    have s: "indexed_formed \<kappa> P (indexed_refresh_at \<kappa> P a r)"
      "indexed_project (indexed_refresh_at \<kappa> P a r) = indexed_project r"
      using indexed_refresh_at[OF Cons.prems] by simp_all
    show ?case using Cons.IH[OF s(1)] s(2) by simp
  qed simp
  then show "indexed_formed \<kappa> P r \<Longrightarrow> indexed_formed \<kappa> P (indexed_refresh \<kappa> P r) \<and>
      indexed_project (indexed_refresh \<kappa> P r) = indexed_project r"
    by (simp add: indexed_refresh_def)
qed

section \<open>The successors of a goal\<close>

definition indexed_call_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> 's list \<Rightarrow>
    ('d \<times> 'c \<times> 's) option \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
    'a finite_term_pattern \<times> 'c \<times> ('a,'s,'d) finite_factor_schema \<times>
      (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable finite_term_pattern) list \<Rightarrow>
    ('a,'s,'d,'c) indexed_state" where
  "indexed_call_state P r q rr d p z = (case z of (i,c,S,u) \<Rightarrow>
    indexed_substitute P (finite_binding_substitution u) (fset_of_list (map fst u))
      (indexed_put_nodes q {|index_node (finite_clause_node q d c S)|}
        (indexed_add_goals P (finite_clause_goals q d c S) (indexed_remove_goal (Resolution_Call_Goal q rr d p) r))))"

definition indexed_material_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow>
    's list \<Rightarrow> 'd \<times> 'c \<times> 's \<Rightarrow> ('s,'a) resolution_variable finite_material_pattern \<Rightarrow>
    ('s,'a) resolution_variable finite_pattern_pairs \<times>
      (('s,'a) resolution_variable \<times> ('s,'a) resolution_variable finite_term_pattern) list \<Rightarrow>
    ('a,'s,'d,'c) indexed_state" where
  "indexed_material_state P r q rr M z = (case z of (E,u) \<Rightarrow>
    indexed_substitute P (finite_binding_substitution u) (fset_of_list (map fst u))
      (indexed_remove_goal (Resolution_Material_Goal q rr M) r))"

lemma finite_binding_substitution_outside:
  assumes "x |\<notin>| fset_of_list (map fst u)"
  shows "finite_binding_substitution u x = Finite_Variable x"
proof -
  have "map_of u x = None" using assms by (simp add: fset_of_list.rep_eq map_of_eq_None_iff)
  then show ?thesis by (simp add: finite_binding_substitution_def)
qed

lemma indexed_call_state:
  assumes r: "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_call_state P r q rr d p z)"
    and "indexed_project (indexed_call_state P r q rr d p z) = finite_call_alternative_state (indexed_project r) q rr d p z"
proof -
  obtain i c S u where z: "z = (i,c,S,u)" by (cases z)
  let ?g = "Resolution_Call_Goal q rr d p"
  let ?nd = "finite_clause_node q d c S"
  let ?r1 = "indexed_remove_goal ?g r"
  let ?r2 = "indexed_add_goals P (finite_clause_goals q d c S) ?r1"
  let ?r3 = "indexed_put_nodes q {|index_node ?nd|} ?r2"
  note r1 = indexed_remove_goal[OF r, of ?g]
  note r2 = indexed_add_goals[OF r1(1), of "finite_clause_goals q d c S"]
  have at: "indexed_node_formed_at \<kappa> P q (index_node ?nd)"
    by (simp add: indexed_node_formed_at_def finite_clause_node_def)
  have f3: "indexed_formed \<kappa> P ?r3" by (rule indexed_put_nodes(1)[OF r2(1)]) (use at in simp)
  have n3: "indexed_node_set ?r3 = indexed_node_set ?r2 |\<union>| fimage indexed_node_value {|index_node ?nd|}"
    by (rule indexed_put_nodes(2)[OF r2(1)]) (use at in simp)
  have g3: "indexed_pending ?r3 = indexed_pending ?r2" by (rule indexed_put_nodes(3)[OF r2(1)]) (use at in simp)
  have w3: "indexed_witnesses ?r3 = indexed_witnesses ?r2" by (rule indexed_put_nodes(4)[OF r2(1)]) (use at in simp)
  have p3: "indexed_project ?r3 = Resolution_State (finite_clause_goals q d c S |\<union>| (indexed_pending r |-| {|?g|}))
      (finsert ?nd (indexed_node_set r)) (indexed_witnesses r)"
    using n3 g3 w3 r2(2-4) r1(2-4) by (auto simp: indexed_project_def fset_eq_iff)
  have out: "\<And>x. x |\<notin>| fset_of_list (map fst u) \<Longrightarrow> finite_binding_substitution u x = Finite_Variable x"
    by (rule finite_binding_substitution_outside)
  note s = indexed_substitute[where D="fset_of_list (map fst u)", OF f3 out]
  show "indexed_formed \<kappa> P (indexed_call_state P r q rr d p z)"
    using s(1) by (simp add: indexed_call_state_def z)
  show "indexed_project (indexed_call_state P r q rr d p z) = finite_call_alternative_state (indexed_project r) q rr d p z"
    using s(2) p3 by (simp add: indexed_call_state_def z finite_call_alternative_state_def)
qed

lemma indexed_material_state:
  assumes r: "indexed_formed \<kappa> P r"
  shows "indexed_formed \<kappa> P (indexed_material_state P r q rr M z)"
    and "indexed_project (indexed_material_state P r q rr M z) =
      finite_material_alternative_state (indexed_project r) q rr M z"
proof -
  obtain E u where z: "z = (E,u)" by (cases z)
  let ?g = "Resolution_Material_Goal q rr M"
  note r1 = indexed_remove_goal[OF r, of ?g]
  have p1: "indexed_project (indexed_remove_goal ?g r) =
      Resolution_State (indexed_pending r |-| {|?g|}) (indexed_node_set r) (indexed_witnesses r)"
    using r1(2-4) by (simp add: indexed_project_def)
  have out: "\<And>x. x |\<notin>| fset_of_list (map fst u) \<Longrightarrow> finite_binding_substitution u x = Finite_Variable x"
    by (rule finite_binding_substitution_outside)
  note s = indexed_substitute[where D="fset_of_list (map fst u)", OF r1(1) out]
  show "indexed_formed \<kappa> P (indexed_material_state P r q rr M z)"
    using s(1) by (simp add: indexed_material_state_def z)
  show "indexed_project (indexed_material_state P r q rr M z) =
      finite_material_alternative_state (indexed_project r) q rr M z"
    using s(2) p1 by (simp add: indexed_material_state_def z finite_material_alternative_state_def)
qed

definition indexed_goal_successors :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) indexed_state \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal \<Rightarrow> ('a,'s,'d,'c) indexed_state fset" where
  "indexed_goal_successors P r hg = (case indexed_goal_value hg of
      Resolution_Call_Goal q rr d p \<Rightarrow> if indexed_reusable r hg then {|indexed_remove_goal (indexed_goal_value hg) r|}
        else fimage (indexed_call_state P r q rr d p) (finite_call_alternative_set P q d p)
    | Resolution_Material_Goal q rr M \<Rightarrow>
        fimage (indexed_material_state P r q rr M) (finite_material_alternative_set M))"

theorem indexed_goal_successors:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
  shows "fimage indexed_project (indexed_goal_successors P r hg) =
      finite_goal_successors P (indexed_project r) (indexed_goal_value hg)"
    and "s |\<in>| indexed_goal_successors P r hg \<Longrightarrow> indexed_formed \<kappa> P s"
proof -
  have reuse: "indexed_reusable r hg \<longleftrightarrow> finite_reusable (indexed_project r) (indexed_goal_value hg)"
    by (rule indexed_reusable[OF r hg])
  have closed: "indexed_project (indexed_remove_goal g r) = finite_goal_closed (indexed_project r) g" for g
    using indexed_remove_goal(2-4)[OF r, of g] by (simp add: indexed_project_def finite_goal_closed_def)
  show "fimage indexed_project (indexed_goal_successors P r hg) =
      finite_goal_successors P (indexed_project r) (indexed_goal_value hg)"
  proof (cases "indexed_goal_value hg")
    case (Resolution_Call_Goal q rr d p)
    show ?thesis
    proof (cases "indexed_reusable r hg")
      case True
      then show ?thesis using reuse closed Resolution_Call_Goal by (simp add: indexed_goal_successors_def)
    next
      case False
      have "fimage indexed_project (fimage (indexed_call_state P r q rr d p) (finite_call_alternative_set P q d p)) =
          fimage (finite_call_alternative_state (indexed_project r) q rr d p) (finite_call_alternative_set P q d p)"
        unfolding fset.map_comp comp_def by (rule fimage_cong_on) (rule indexed_call_state(2)[OF r])
      then show ?thesis using False reuse Resolution_Call_Goal
        by (simp add: indexed_goal_successors_def finite_call_successors_alternatives)
    qed
  next
    case (Resolution_Material_Goal q rr M)
    have "fimage indexed_project (fimage (indexed_material_state P r q rr M) (finite_material_alternative_set M)) =
        fimage (finite_material_alternative_state (indexed_project r) q rr M) (finite_material_alternative_set M)"
      unfolding fset.map_comp comp_def by (rule fimage_cong_on) (rule indexed_material_state(2)[OF r])
    then show ?thesis using Resolution_Material_Goal
      by (simp add: indexed_goal_successors_def finite_material_successors_alternatives)
  qed
  show "indexed_formed \<kappa> P s" if "s |\<in>| indexed_goal_successors P r hg"
    using that indexed_remove_goal(1)[OF r] indexed_call_state(1)[OF r] indexed_material_state(1)[OF r]
    by (auto simp: indexed_goal_successors_def fimage.rep_eq split: resolution_goal.splits if_splits)
qed

section \<open>The selection\<close>

text \<open>
  The selection reads R3's selection (@{const finite_resolution_select_at}) through the tests above: every class of
  @{const finite_goal_choice} is a filter of indexed goals by a test equal to R3's on the goals of a formed state, the
  alternatives read from each goal's cache, and the constructions from the positions holding registered variables.
  A filter commutes with the image of the goals' values, so the selection projects to R3's.
\<close>

lemma fimage_ffilter_value: "ffilter Q (fimage f X) = fimage f (ffilter (\<lambda>x. Q (f x)) X)"
  by (auto simp: fset_eq_iff fimage.rep_eq ffilter.rep_eq)

lemma ffilter_cong_on: "(\<And>x. x |\<in>| X \<Longrightarrow> F x \<longleftrightarrow> G x) \<Longrightarrow> ffilter F X = ffilter G X"
  by (auto simp: fset_eq_iff ffilter.rep_eq)

lemma fimage_snd_keyed: "fimage snd (ffilter F (fimage (\<lambda>g. (f g,g)) C)) = ffilter (\<lambda>g. F (f g,g)) C"
  by (force simp: fset_eq_iff fimage.rep_eq ffilter.rep_eq)

definition indexed_first_goals :: "('a,'s::linorder,'d,'c) indexed_goal fset \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_first_goals H = ffilter (\<lambda>h. \<not> fBex H (\<lambda>h'. finite_position_less
    (resolution_goal_position (indexed_goal_value h')) (resolution_goal_position (indexed_goal_value h)))) H"

lemma indexed_first_goals:
  "fimage indexed_goal_value (indexed_first_goals H) = finite_first_goals (fimage indexed_goal_value H)"
  "h |\<in>| indexed_first_goals H \<Longrightarrow> h |\<in>| H"
  by (auto simp: indexed_first_goals_def finite_first_goals_def fset_eq_iff fimage.rep_eq ffilter.rep_eq)

definition indexed_first_nodes :: "('a,'s::linorder,'d,'c) indexed_node fset \<Rightarrow> ('a,'s,'d,'c) indexed_node fset" where
  "indexed_first_nodes N = ffilter (\<lambda>hn. \<not> fBex N (\<lambda>m. finite_position_less
    (resolution_node_position (indexed_node_value m)) (resolution_node_position (indexed_node_value hn)))) N"

lemma indexed_first_nodes:
  "fimage indexed_node_value (indexed_first_nodes N) = finite_first_nodes (fimage indexed_node_value N)"
  "hn |\<in>| indexed_first_nodes N \<Longrightarrow> hn |\<in>| N"
  by (auto simp: indexed_first_nodes_def finite_first_nodes_def fset_eq_iff fimage.rep_eq ffilter.rep_eq)

subsection \<open>R3's classes and the waiting rule\<close>

definition indexed_goal_selection :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_goal_selection r A = (let c1 = ffilter (\<lambda>h. finite_ground_call_goal (indexed_goal_value h)) A;
      c2 = ffilter (indexed_independent r) A; c3 = ffilter (\<lambda>h. finite_solvable_material_goal (indexed_goal_value h)) A;
      c4 = ffilter (\<lambda>h. finite_leaf_call_goal (indexed_goal_value h)) A in
    indexed_first_goals (if c1\<noteq>{||} then c1 else if c2\<noteq>{||} then c2 else if c3\<noteq>{||} then c3 else c4))"

lemma indexed_goal_selection_member: "h |\<in>| indexed_goal_selection r A \<Longrightarrow> h |\<in>| A"
  by (auto simp: indexed_goal_selection_def Let_def ffilter.rep_eq dest: indexed_first_goals(2) split: if_splits)

lemma indexed_goal_selection:
  assumes r: "indexed_formed \<kappa> P r" and A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| tree_buckets (indexed_goals r)"
  shows "fimage indexed_goal_value (indexed_goal_selection r A) =
      finite_goal_selection (indexed_pending r) (fimage indexed_goal_value A)"
proof -
  have ind: "ffilter (indexed_independent r) A =
      ffilter (\<lambda>h. finite_independent_goal (indexed_pending r) (indexed_goal_value h)) A"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| A"
    then obtain q where q: "h |\<in>| tree_bucket (indexed_goals r) q" using A by (auto simp: tree_buckets_member)
    show "indexed_independent r h \<longleftrightarrow> finite_independent_goal (indexed_pending r) (indexed_goal_value h)"
      by (rule indexed_independent[OF r q])
  qed
  show "fimage indexed_goal_value (indexed_goal_selection r A) =
      finite_goal_selection (indexed_pending r) (fimage indexed_goal_value A)"
    unfolding indexed_goal_selection_def finite_goal_selection_def Let_def ind
    by (simp add: fimage_ffilter_value indexed_first_goals(1) if_distrib[of "fimage indexed_goal_value"])
qed

definition indexed_waiting_selection :: "('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset \<Rightarrow>
    ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_waiting_selection r A = (let W = indexed_goal_selection r (ffilter (\<lambda>h. \<not> indexed_waits r h) A) in
    if W \<noteq> {||} then W else indexed_goal_selection r A)"

lemma indexed_waiting_selection_member: "h |\<in>| indexed_waiting_selection r A \<Longrightarrow> h |\<in>| A"
  by (auto simp: indexed_waiting_selection_def Let_def ffilter.rep_eq dest: indexed_goal_selection_member split: if_splits)

lemma indexed_waiting_selection:
  assumes r: "indexed_formed \<kappa> P r" and A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| tree_buckets (indexed_goals r)"
  shows "fimage indexed_goal_value (indexed_waiting_selection r A) =
      finite_waiting_selection (indexed_project r) (indexed_pending r) (fimage indexed_goal_value A)"
proof -
  let ?A = "ffilter (\<lambda>h. \<not> finite_goal_waits (indexed_project r) (indexed_goal_value h)) A"
  have w: "ffilter (\<lambda>h. \<not> indexed_waits r h) A = ?A"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| A"
    then obtain q where q: "h |\<in>| tree_bucket (indexed_goals r) q" using A by (auto simp: tree_buckets_member)
    show "(\<not> indexed_waits r h) \<longleftrightarrow> (\<not> finite_goal_waits (indexed_project r) (indexed_goal_value h))"
      using indexed_waits[OF r q] by simp
  qed
  have A': "\<And>h. h |\<in>| ?A \<Longrightarrow> h |\<in>| tree_buckets (indexed_goals r)" using A by (simp add: ffilter.rep_eq)
  note s1 = indexed_goal_selection[where A="ffilter (\<lambda>h. \<not> finite_goal_waits (indexed_project r) (indexed_goal_value h)) A",
      OF r A']
    and s2 = indexed_goal_selection[where A=A, OF r A]
  show "fimage indexed_goal_value (indexed_waiting_selection r A) =
      finite_waiting_selection (indexed_project r) (indexed_pending r) (fimage indexed_goal_value A)"
    unfolding indexed_waiting_selection_def finite_waiting_selection_def Let_def w
    using s1(1)[symmetric] s2(1)[symmetric]
    by (simp add: fimage_ffilter_value if_distrib[of "fimage indexed_goal_value"])
qed

subsection \<open>The choice at a priority\<close>

text \<open>
  The priority is refined to the indexed state: a refined priority holds of an indexed goal exactly where the
  priority holds of its value at the projection.
\<close>

definition indexed_goal_choice :: "(('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool) \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset \<Rightarrow> ('a,'s,'d,'c) indexed_goal fset" where
  "indexed_goal_choice rp r A = (let C = ffilter (\<lambda>h. finite_candidate_goal (indexed_goal_value h)) A;
      c0 = ffilter (\<lambda>h. indexed_goal_alternatives h = 0 \<or> indexed_pruned r h \<or> indexed_reusable r h) C in
    if c0 \<noteq> {||} then indexed_first_goals c0
    else let cp = ffilter (rp r) C in if cp \<noteq> {||} then indexed_first_goals cp
    else let c1 = ffilter (\<lambda>h. indexed_goal_alternatives h = 1 \<and> \<not> indexed_waits r h) C in
      if c1 \<noteq> {||} then indexed_first_goals c1
    else indexed_waiting_selection r A)"

lemma indexed_goal_choice_member: "h |\<in>| indexed_goal_choice rp r A \<Longrightarrow> h |\<in>| A"
  by (auto simp: indexed_goal_choice_def Let_def ffilter.rep_eq
    dest: indexed_first_goals(2) indexed_waiting_selection_member split: if_splits)

lemma indexed_goal_choice:
  assumes r: "indexed_formed \<kappa> P r" and A: "\<And>h. h |\<in>| A \<Longrightarrow> h |\<in>| tree_buckets (indexed_goals r)"
    and rp: "\<And>h. h |\<in>| A \<Longrightarrow> rp r h \<longleftrightarrow> pr (indexed_project r) (indexed_goal_value h)"
  shows "fimage indexed_goal_value (indexed_goal_choice rp r A) =
      finite_goal_choice pr P (indexed_project r) (indexed_pending r) (fimage indexed_goal_value A)"
proof -
  let ?C = "ffilter (\<lambda>h. finite_candidate_goal (indexed_goal_value h)) A"
  have at: "\<And>h. h |\<in>| ?C \<Longrightarrow> \<exists>q. h |\<in>| tree_bucket (indexed_goals r) q"
    using A by (auto simp: tree_buckets_member ffilter.rep_eq)
  have c0: "ffilter (\<lambda>h. indexed_goal_alternatives h = 0 \<or> indexed_pruned r h \<or> indexed_reusable r h) ?C =
      ffilter (\<lambda>h. finite_goal_alternatives P (indexed_goal_value h) = 0 \<or>
        finite_pruned (indexed_project r) (indexed_goal_value h) \<or>
        finite_reusable (indexed_project r) (indexed_goal_value h)) ?C"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| ?C"
    then obtain q where q: "h |\<in>| tree_bucket (indexed_goals r) q" using at by blast
    show "(indexed_goal_alternatives h = 0 \<or> indexed_pruned r h \<or> indexed_reusable r h) \<longleftrightarrow>
        (finite_goal_alternatives P (indexed_goal_value h) = 0 \<or>
        finite_pruned (indexed_project r) (indexed_goal_value h) \<or>
        finite_reusable (indexed_project r) (indexed_goal_value h))"
      using indexed_goal_variables_at(2)[OF r q] indexed_pruned[OF r q] indexed_reusable[OF r q] by simp
  qed
  have cp: "ffilter (rp r) ?C = ffilter (\<lambda>h. pr (indexed_project r) (indexed_goal_value h)) ?C"
    by (rule ffilter_cong_on) (use rp in \<open>auto simp: ffilter.rep_eq\<close>)
  have c1: "ffilter (\<lambda>h. indexed_goal_alternatives h = 1 \<and> \<not> indexed_waits r h) ?C =
      ffilter (\<lambda>h. finite_goal_alternatives P (indexed_goal_value h) = 1 \<and>
        \<not> finite_goal_waits (indexed_project r) (indexed_goal_value h)) ?C"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| ?C"
    then obtain q where q: "h |\<in>| tree_bucket (indexed_goals r) q" using at by blast
    show "(indexed_goal_alternatives h = 1 \<and> \<not> indexed_waits r h) \<longleftrightarrow>
        (finite_goal_alternatives P (indexed_goal_value h) = 1 \<and>
        \<not> finite_goal_waits (indexed_project r) (indexed_goal_value h))"
      using indexed_goal_variables_at(2)[OF r q] indexed_waits[OF r q] by simp
  qed
  note w = indexed_waiting_selection[OF r A]
  show "fimage indexed_goal_value (indexed_goal_choice rp r A) =
      finite_goal_choice pr P (indexed_project r) (indexed_pending r) (fimage indexed_goal_value A)"
    unfolding indexed_goal_choice_def finite_goal_choice_def Let_def fimage_snd_keyed c0 cp c1
    by (simp add: fimage_ffilter_value indexed_first_goals(1) w(1) if_distrib[of "fimage indexed_goal_value"])
qed

subsection \<open>The selection and its projection\<close>

datatype ('a,'s,'d,'c) indexed_selection =
    Indexed_Construction "('a,'s,'d,'c) indexed_node fset"
  | Indexed_Goals "('a,'s,'d,'c) indexed_goal fset"
  | Indexed_None

fun indexed_selection_value :: "('a,'s,'d,'c) indexed_selection \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "indexed_selection_value (Indexed_Construction N) = Select_Construction (fimage indexed_node_value N)"
| "indexed_selection_value (Indexed_Goals G) = Select_Goals (fimage indexed_goal_value G)"
| "indexed_selection_value Indexed_None = Select_None"

definition indexed_select :: "(('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool) \<Rightarrow>
    ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_selection" where
  "indexed_select rp \<kappa> P r = (let N = indexed_construction_nodes \<kappa> P r in
    if N \<noteq> {||} then Indexed_Construction (indexed_first_nodes N)
    else let S = indexed_goal_choice rp r (ffilter (\<lambda>h. \<not> indexed_held \<kappa> r h) (tree_buckets (indexed_goals r))) in
      if S = {||} then Indexed_None else Indexed_Goals S)"

theorem indexed_select:
  assumes r: "indexed_formed \<kappa> P r"
    and rp: "\<And>h. rp r h \<longleftrightarrow> pr (indexed_project r) (indexed_goal_value h)"
  shows "indexed_selection_value (indexed_select rp \<kappa> P r) = finite_resolution_select_at pr \<kappa> P (indexed_project r)"
    and "indexed_select rp \<kappa> P r = Indexed_Construction N \<Longrightarrow> hn |\<in>| N \<Longrightarrow> \<exists>q. hn |\<in>| tree_bucket (indexed_nodes r) q"
    and "indexed_select rp \<kappa> P r = Indexed_Goals G \<Longrightarrow> hg |\<in>| G \<Longrightarrow> \<exists>q. hg |\<in>| tree_bucket (indexed_goals r) q"
proof -
  let ?H = "ffilter (\<lambda>h. \<not> indexed_held \<kappa> r h) (tree_buckets (indexed_goals r))"
  have H: "\<And>h. h |\<in>| ?H \<Longrightarrow> h |\<in>| tree_buckets (indexed_goals r)" by (simp add: ffilter.rep_eq)
  have "?H = ffilter (\<lambda>h. \<not> finite_held \<kappa> (indexed_project r) (indexed_goal_value h)) (tree_buckets (indexed_goals r))"
  proof (rule ffilter_cong_on)
    fix h assume "h |\<in>| tree_buckets (indexed_goals r)"
    then obtain q where q: "h |\<in>| tree_bucket (indexed_goals r) q" by (auto simp: tree_buckets_member)
    show "(\<not> indexed_held \<kappa> r h) \<longleftrightarrow> (\<not> finite_held \<kappa> (indexed_project r) (indexed_goal_value h))"
      using indexed_held[OF r q] by simp
  qed
  then have held: "fimage indexed_goal_value ?H =
      ffilter (\<lambda>g. \<not> finite_held \<kappa> (indexed_project r) g) (indexed_pending r)"
    by (simp add: indexed_pending_def fimage_ffilter_value)
  have rpH: "\<And>h. h |\<in>| ?H \<Longrightarrow> rp r h \<longleftrightarrow> pr (indexed_project r) (indexed_goal_value h)" using rp by simp
  note cn = indexed_construction_nodes[OF r]
    and ch = indexed_goal_choice[where A="ffilter (\<lambda>h. \<not> indexed_held \<kappa> r h) (tree_buckets (indexed_goals r))"
      and rp=rp and pr=pr, OF r H rpH]
  show "indexed_selection_value (indexed_select rp \<kappa> P r) = finite_resolution_select_at pr \<kappa> P (indexed_project r)"
    unfolding indexed_select_def finite_resolution_select_at_def Let_def
    using cn(1)[symmetric] held[symmetric] ch(1)[symmetric]
    by (simp add: indexed_first_nodes(1) if_distrib[of indexed_selection_value])
  show "indexed_select rp \<kappa> P r = Indexed_Construction N \<Longrightarrow> hn |\<in>| N \<Longrightarrow> \<exists>q. hn |\<in>| tree_bucket (indexed_nodes r) q"
    by (auto simp: indexed_select_def Let_def dest: indexed_first_nodes(2) cn(2) split: if_splits)
  show "indexed_select rp \<kappa> P r = Indexed_Goals G \<Longrightarrow> hg |\<in>| G \<Longrightarrow> \<exists>q. hg |\<in>| tree_bucket (indexed_goals r) q"
  proof -
    assume "indexed_select rp \<kappa> P r = Indexed_Goals G" "hg |\<in>| G"
    then have "hg |\<in>| indexed_goal_choice rp r ?H" by (auto simp: indexed_select_def Let_def split: if_splits)
    then have "hg |\<in>| ?H" by (rule indexed_goal_choice_member)
    then show ?thesis using H by (auto simp: tree_buckets_member)
  qed
qed

section \<open>The search\<close>

text \<open>
  The indexed search is R3's search over the indexed state: it refreshes F4's kept constructions before it selects,
  steps through the indexed construction step and the indexed successors, and diagnoses at the projection. By
  induction on the bound over the step theorems it is R3's search at the refined priority, and at the default
  priority it is R3's search itself, which it computes as its code equation.
\<close>

lemma indexed_empty_goals:
  assumes r: "indexed_formed \<kappa> P r"
  shows "RBT.is_empty (indexed_goals r) \<longleftrightarrow> indexed_pending r = {||}"
proof -
  have f: "tree_buckets_formed (indexed_goals r) (indexed_goal_formed_at P)" using r by (simp add: indexed_formed_def)
  show ?thesis using tree_buckets_is_empty[OF f] by (simp add: indexed_pending_def)
qed

definition indexed_goal_outcome :: "(('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow>
    ('a,'s,'d,'c) resolution_outcome" where
  "indexed_goal_outcome rec P r hg = (if indexed_pruned r hg then Resolution_Outcome {||} {||} else
    let S = indexed_goal_successors P r hg in
    if S = {||} then (if indexed_witnesses r = {||} then Resolution_Outcome {||} {||}
      else Resolution_Outcome {||} {|Resolution_Witnessed (indexed_witnesses r) (indexed_goal_value hg)|})
    else finite_outcome_union (fimage rec S))"

lemma indexed_goal_outcome:
  assumes r: "indexed_formed \<kappa> P r" and hg: "hg |\<in>| tree_bucket (indexed_goals r) q0"
    and rec: "\<And>s. indexed_formed \<kappa> P s \<Longrightarrow> recI s = recA (indexed_project s)"
  shows "indexed_goal_outcome recI P r hg = finite_goal_outcome recA P (indexed_project r) (indexed_goal_value hg)"
proof -
  let ?S = "indexed_goal_successors P r hg"
  note sc = indexed_goal_successors[OF r hg]
  have img: "fimage recI ?S = fimage recA (fimage indexed_project ?S)"
    unfolding fset.map_comp comp_def by (rule fimage_cong_on) (simp add: rec sc(2))
  show ?thesis using img sc(1)[symmetric]
    by (simp add: indexed_goal_outcome_def finite_goal_outcome_def Let_def indexed_pruned[OF r hg])
qed

primrec indexed_search :: "(('a,'s::linorder,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) indexed_goal \<Rightarrow> bool) \<Rightarrow>
    ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
    ('a,'s,'d,'c) indexed_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "indexed_search rp \<kappa> P 0 r = (if RBT.is_empty (indexed_goals r) then Resolution_Outcome {|indexed_project r|} {||}
    else Resolution_Outcome {||} {|Resolution_Cut (indexed_pending r)|})"
| "indexed_search rp \<kappa> P (Suc n) r = (if RBT.is_empty (indexed_goals r) then Resolution_Outcome {|indexed_project r|} {||}
    else let r' = indexed_refresh \<kappa> P r in (case indexed_select rp \<kappa> P r' of
      Indexed_Construction N \<Rightarrow>
        finite_outcome_union (fimage (\<lambda>hn. indexed_search rp \<kappa> P n (indexed_construction_step \<kappa> P r' hn)) N)
    | Indexed_Goals G \<Rightarrow> finite_outcome_union (fimage (indexed_goal_outcome (indexed_search rp \<kappa> P n) P r') G)
    | Indexed_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (indexed_pending r')) (finite_unconstructed \<kappa> P (indexed_project r')))))"

theorem indexed_search:
  assumes r: "indexed_formed \<kappa> P r"
    and rp: "\<And>s h. rp s h \<longleftrightarrow> pr (indexed_project s) (indexed_goal_value h)"
  shows "indexed_search rp \<kappa> P n r =
      finite_resolution_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> P n (indexed_project r)"
  using r
proof (induction n arbitrary: r)
  case 0
  then show ?case using indexed_empty_goals[OF 0] by simp
next
  case (Suc n)
  let ?r = "indexed_refresh \<kappa> P r"
  let ?rec = "finite_resolution_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> P n"
  have f: "indexed_formed \<kappa> P ?r" and p: "indexed_project ?r = indexed_project r"
    using indexed_refresh[OF Suc.prems] by simp_all
  have pp: "indexed_pending ?r = indexed_pending r" using p by (metis indexed_project_fields(1))
  have rp': "\<And>h. rp ?r h \<longleftrightarrow> pr (indexed_project ?r) (indexed_goal_value h)" by (rule rp)
  note sel = indexed_select[where rp=rp and pr=pr, OF f rp']
  have rec: "\<And>s. indexed_formed \<kappa> P s \<Longrightarrow> indexed_search rp \<kappa> P n s = ?rec (indexed_project s)"
    by (rule Suc.IH)
  show ?case
  proof (cases "indexed_pending r = {||}")
    case True
    then show ?thesis using indexed_empty_goals[OF Suc.prems] by simp
  next
    case False
    have ne: "\<not> RBT.is_empty (indexed_goals r)" using False indexed_empty_goals[OF Suc.prems] by simp
    show ?thesis
    proof (cases "indexed_select rp \<kappa> P ?r")
      case (Indexed_Construction N)
      have s: "finite_resolution_select_at pr \<kappa> P (indexed_project r) = Select_Construction (fimage indexed_node_value N)"
        using sel(1) Indexed_Construction p by simp
      have "fimage (\<lambda>hn. indexed_search rp \<kappa> P n (indexed_construction_step \<kappa> P ?r hn)) N =
          fimage ?rec (fimage (finite_construction_step \<kappa> P (indexed_project r)) (fimage indexed_node_value N))"
        unfolding fset.map_comp comp_def
      proof (rule fimage_cong_on)
        fix hn assume "hn |\<in>| N"
        then obtain q where q: "hn |\<in>| tree_bucket (indexed_nodes ?r) q" using sel(2)[OF Indexed_Construction] by blast
        show "indexed_search rp \<kappa> P n (indexed_construction_step \<kappa> P ?r hn) =
            ?rec (finite_construction_step \<kappa> P (indexed_project r) (indexed_node_value hn))"
          using rec[OF indexed_construction_step(1)[OF f q]] indexed_construction_step(2)[OF f q] p by simp
      qed
      then show ?thesis using ne False s Indexed_Construction by (simp add: Let_def)
    next
      case (Indexed_Goals G)
      have s: "finite_resolution_select_at pr \<kappa> P (indexed_project r) = Select_Goals (fimage indexed_goal_value G)"
        using sel(1) Indexed_Goals p by simp
      have "fimage (indexed_goal_outcome (indexed_search rp \<kappa> P n) P ?r) G =
          fimage (finite_goal_outcome ?rec P (indexed_project r)) (fimage indexed_goal_value G)"
        unfolding fset.map_comp comp_def
      proof (rule fimage_cong_on)
        fix hg assume "hg |\<in>| G"
        then obtain q where q: "hg |\<in>| tree_bucket (indexed_goals ?r) q" using sel(3)[OF Indexed_Goals] by blast
        show "indexed_goal_outcome (indexed_search rp \<kappa> P n) P ?r hg =
            finite_goal_outcome ?rec P (indexed_project r) (indexed_goal_value hg)"
          using indexed_goal_outcome[where recI="indexed_search rp \<kappa> P n"
            and recA="finite_resolution_search_by (finite_resolution_select_at pr \<kappa> P) \<kappa> P n", OF f q rec] p by simp
      qed
      then show ?thesis using ne False s Indexed_Goals by (simp add: Let_def)
    next
      case Indexed_None
      have s: "finite_resolution_select_at pr \<kappa> P (indexed_project r) = Select_None"
        using sel(1) Indexed_None p by simp
      then show ?thesis using ne False Indexed_None p pp by (simp add: Let_def)
    qed
  qed
qed

text \<open>
  At the default priority the indexed search from the indexed state of an abstract state is R3's search from that
  state, and so its code equation: R3's search is computed over the indexed state, at every type R3's search has.
\<close>

lemma finite_resolution_search_code [code]:
  "finite_resolution_search \<kappa> P n st = indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st)"
proof -
  have "indexed_search (\<lambda>r h. False) \<kappa> P n (index_state P st) =
      finite_resolution_search_by (finite_resolution_select_at (\<lambda>st g. False) \<kappa> P) \<kappa> P n
        (indexed_project (index_state P st))"
    by (rule indexed_search[OF index_state(1)]) simp
  then show ?thesis by (simp add: finite_resolution_search_def index_state(2))
qed

export_code finite_resolution_search checking SML

end
