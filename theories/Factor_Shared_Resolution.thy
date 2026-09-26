theory Factor_Shared_Resolution
  imports Factor_Indexed_Resolution Factor_Shared_Patterns Finite_Functional_Enumeration Finite_Presented_Collections
begin

section \<open>The sharing state a search threads\<close>

text \<open>
  Build F2b2 of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size" (divided at
  q130): R3's search over F2b1's indexed state (@{text Factor_Indexed_Resolution}) with the patterns of its goals
  and nodes over F2a's shared patterns (@{text Factor_Shared_Patterns}). The search threads one sharing state, the
  keyed first-occurrence state of a shared-term table (@{typ share_state}); it is formed when it represents its
  table and the table is formed, and every operation extends the table, every earlier reference decoding as
  before (@{text table_extends}).
\<close>

definition share_state_table :: "share_state \<Rightarrow> shape list" where
  "share_state_table q = rev (snd (snd q))"

definition share_state_formed :: "share_state \<Rightarrow> bool" where
  "share_state_formed q \<longleftrightarrow> keyed_state_represents q (share_state_table q) \<and> table_formed (share_state_table q)"

definition table_extends :: "shape list \<Rightarrow> shape list \<Rightarrow> bool" where
  "table_extends T T' \<longleftrightarrow> (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u)"

lemma table_extends_refl [simp]: "table_extends T T"
  by (simp add: table_extends_def)

lemma table_extends_trans: "table_extends T T' \<Longrightarrow> table_extends T' T'' \<Longrightarrow> table_extends T T''"
  by (simp add: table_extends_def)

lemma share_state_table_represents:
  assumes "keyed_state_represents q T"
  shows "share_state_table q = T"
  using keyed_reference_state_table[of shape_key q T] assms
  by (simp add: keyed_state_represents_def share_state_table_def)

lemma share_state_empty:
  "share_state_formed (RBT.empty,0,[])" "share_state_table (RBT.empty,0,[]) = []"
  by (simp_all add: share_state_formed_def share_state_table_def keyed_state_represents_def
    keyed_reference_state_empty table_formed_empty)

lemma share_state_formed_table:
  "share_state_formed q \<Longrightarrow> table_formed (share_state_table q)"
  "share_state_formed q \<Longrightarrow> keyed_state_represents q (share_state_table q)"
  by (simp_all add: share_state_formed_def)

text \<open>A pattern formed over a formed table stays formed, its projection unchanged, over every extension.\<close>

lemma shared_pattern_extends:
  assumes table: "table_formed T" and formed: "shared_pattern_formed T p" and ext: "table_extends T T'"
  shows "shared_pattern_formed T' p" "shared_pattern_project T' p = shared_pattern_project T p"
proof -
  have "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u" using ext by (simp add: table_extends_def)
  from shared_pattern_extended[OF table formed this]
  show "shared_pattern_formed T' p" "shared_pattern_project T' p = shared_pattern_project T p" by simp_all
qed

subsection \<open>The keyed constructors over a formed state\<close>

lemma share_state_node:
  assumes q: "share_state_formed q"
    and p: "shared_pattern_formed (share_state_table q) p" and r: "shared_pattern_formed (share_state_table q) r"
  shows "share_state_formed (snd (keyed_share_node p r q))"
    and "fst (keyed_share_node p r q) = fst (share_node p r (share_state_table q))"
    and "shared_pattern_formed (share_state_table (snd (keyed_share_node p r q))) (fst (keyed_share_node p r q))"
    and "shared_pattern_project (share_state_table (snd (keyed_share_node p r q))) (fst (keyed_share_node p r q)) =
      Finite_Pattern_Pair (shared_pattern_project (share_state_table q) p) (shared_pattern_project (share_state_table q) r)"
    and "table_extends (share_state_table q) (share_state_table (snd (keyed_share_node p r q)))"
proof -
  let ?T = "share_state_table q"
  have rep: "keyed_state_represents q ?T" and tf: "table_formed ?T" using q by (simp_all add: share_state_formed_def)
  have k1: "fst (keyed_share_node p r q) = fst (share_node p r ?T)"
    and k2: "keyed_state_represents (snd (keyed_share_node p r q)) (snd (share_node p r ?T))"
    using keyed_share_node_exact[OF rep, of p r] by simp_all
  have t: "share_state_table (snd (keyed_share_node p r q)) = snd (share_node p r ?T)"
    using share_state_table_represents[OF k2] .
  note e = share_node_exact[OF tf p r]
  show "fst (keyed_share_node p r q) = fst (share_node p r ?T)" by (fact k1)
  show "share_state_formed (snd (keyed_share_node p r q))" using k2 e t by (simp add: share_state_formed_def)
  show "shared_pattern_formed (share_state_table (snd (keyed_share_node p r q))) (fst (keyed_share_node p r q))"
    using k1 e t by simp
  show "shared_pattern_project (share_state_table (snd (keyed_share_node p r q))) (fst (keyed_share_node p r q)) =
      Finite_Pattern_Pair (shared_pattern_project ?T p) (shared_pattern_project ?T r)"
    using k1 e t by simp
  show "table_extends ?T (share_state_table (snd (keyed_share_node p r q)))" using e t by (simp add: table_extends_def)
qed

lemma share_pattern_collapsed: "shared_collapsed (fst (share_pattern p T))"
proof (induction p arbitrary: T)
  case (Finite_Pattern_Pair p r)
  then show ?case by (simp add: split_def share_node_collapsed)
qed (simp_all add: split_def)

lemma share_state_pattern:
  assumes q: "share_state_formed q"
  shows "share_state_formed (snd (keyed_share_pattern p q))"
    and "shared_pattern_formed (share_state_table (snd (keyed_share_pattern p q))) (fst (keyed_share_pattern p q))"
    and "shared_pattern_project (share_state_table (snd (keyed_share_pattern p q))) (fst (keyed_share_pattern p q)) = p"
    and "shared_collapsed (fst (keyed_share_pattern p q))"
    and "table_extends (share_state_table q) (share_state_table (snd (keyed_share_pattern p q)))"
proof -
  let ?T = "share_state_table q"
  have rep: "keyed_state_represents q ?T" and tf: "table_formed ?T" using q by (simp_all add: share_state_formed_def)
  have k1: "fst (keyed_share_pattern p q) = fst (share_pattern p ?T)"
    and k2: "keyed_state_represents (snd (keyed_share_pattern p q)) (snd (share_pattern p ?T))"
    using keyed_share_pattern_exact[OF rep, of p] by simp_all
  have t: "share_state_table (snd (keyed_share_pattern p q)) = snd (share_pattern p ?T)"
    using share_state_table_represents[OF k2] .
  note e = share_pattern_exact[OF tf, of p]
  show "share_state_formed (snd (keyed_share_pattern p q))" using k2 e t by (simp add: share_state_formed_def)
  show "shared_pattern_formed (share_state_table (snd (keyed_share_pattern p q))) (fst (keyed_share_pattern p q))"
    using k1 e t by simp
  show "shared_pattern_project (share_state_table (snd (keyed_share_pattern p q))) (fst (keyed_share_pattern p q)) = p"
    using k1 e t by simp
  show "shared_collapsed (fst (keyed_share_pattern p q))" using k1 share_pattern_collapsed by simp
  show "table_extends ?T (share_state_table (snd (keyed_share_pattern p q)))" using e t by (simp add: table_extends_def)
qed

lemma share_state_collapse:
  assumes q: "share_state_formed q" and p: "shared_pattern_formed (share_state_table q) p"
  shows "share_state_formed (snd (keyed_share_collapse p q))"
    and "shared_pattern_formed (share_state_table (snd (keyed_share_collapse p q))) (fst (keyed_share_collapse p q))"
    and "shared_pattern_project (share_state_table (snd (keyed_share_collapse p q))) (fst (keyed_share_collapse p q)) =
      shared_pattern_project (share_state_table q) p"
    and "shared_collapsed (fst (keyed_share_collapse p q))"
    and "table_extends (share_state_table q) (share_state_table (snd (keyed_share_collapse p q)))"
proof -
  let ?T = "share_state_table q"
  have rep: "keyed_state_represents q ?T" and tf: "table_formed ?T" using q by (simp_all add: share_state_formed_def)
  have k1: "fst (keyed_share_collapse p q) = fst (share_collapse p ?T)"
    and k2: "keyed_state_represents (snd (keyed_share_collapse p q)) (snd (share_collapse p ?T))"
    using keyed_share_collapse_exact[OF rep, of p] by simp_all
  have t: "share_state_table (snd (keyed_share_collapse p q)) = snd (share_collapse p ?T)"
    using share_state_table_represents[OF k2] .
  note e = share_collapse_exact[OF tf p]
  show "share_state_formed (snd (keyed_share_collapse p q))" using k2 e t by (simp add: share_state_formed_def)
  show "shared_pattern_formed (share_state_table (snd (keyed_share_collapse p q))) (fst (keyed_share_collapse p q))"
    using k1 e t by simp
  show "shared_pattern_project (share_state_table (snd (keyed_share_collapse p q))) (fst (keyed_share_collapse p q)) =
      shared_pattern_project ?T p"
    using k1 e t by simp
  show "shared_collapsed (fst (keyed_share_collapse p q))" using k1 e by simp
  show "table_extends ?T (share_state_table (snd (keyed_share_collapse p q)))" using e t by (simp add: table_extends_def)
qed

subsection \<open>A term the table holds is found without extending it\<close>

text \<open>
  Sharing a term a formed table already holds returns its reference and leaves the table, and the keyed state,
  as they are. A family of patterns is therefore shared by extending the table once by the ground terms the family
  holds, in the order of those terms, and then reading each pattern against the one state: the result does not
  depend on an order of the family, which a finite set does not give.
\<close>

lemma share_term_present:
  assumes tf: "table_formed T"
  shows "reference_term T i = Some t \<Longrightarrow> share_term t T = (i, T)"
proof (induction t arbitrary: i)
  case (Finite_Pair u v)
  obtain j k where read: "value_reference_read T i = Some (Pair_Shape j k)"
    and u: "reference_term T j = Some u" and v: "reference_term T k = Some v"
    using Finite_Pair.prems
  proof (cases rule: reference_term_cases)
    case (leaf l)
    then show ?thesis by (cases l) simp_all
  next
    case (pair j k x y)
    then show ?thesis by (auto intro: that)
  qed
  have "value_reference_index (Pair_Shape j k) T = Some i"
    using value_reference_index_distinct_read[OF _ read] tf by (simp add: table_formed_def)
  with Finite_Pair.IH(1)[OF u] Finite_Pair.IH(2)[OF v] show ?case by (simp add: value_reference_step_def)
next
  case (Finite_Payload v)
  have "reference_term T i = Some (leaf_term (Payload_Leaf v))" using Finite_Payload.prems by simp
  then have "value_reference_read T i = Some (Leaf_Shape (Payload_Leaf v))" by (rule reference_factor_leaf_read)
  then have "value_reference_index (Leaf_Shape (Payload_Leaf v)) T = Some i"
    using tf by (intro value_reference_index_distinct_read) (simp_all add: table_formed_def)
  then show ?case by (simp add: value_reference_step_def)
next
  case (Finite_Target a)
  have "reference_term T i = Some (leaf_term (Target_Leaf a))" using Finite_Target.prems by simp
  then have "value_reference_read T i = Some (Leaf_Shape (Target_Leaf a))" by (rule reference_factor_leaf_read)
  then have "value_reference_index (Leaf_Shape (Target_Leaf a)) T = Some i"
    using tf by (intro value_reference_index_distinct_read) (simp_all add: table_formed_def)
  then show ?case by (simp add: value_reference_step_def)
qed

lemma keyed_share_shape_present:
  assumes rep: "keyed_state_represents q T" and found: "value_reference_index s T = Some i"
  shows "keyed_share_shape s q = (i, q)"
proof -
  obtain M n R where qq: "q = (M,n,R)" by (cases q) auto
  have "RBT.lookup M (shape_key s) = value_reference_index s T"
    using rep by (simp add: qq keyed_state_represents_def keyed_reference_state_def)
  with found show ?thesis by (simp add: qq keyed_share_shape_def keyed_reference_step_def)
qed

lemma keyed_share_term_present:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
  shows "reference_term T i = Some t \<Longrightarrow> keyed_share_term t q = (i, q)"
proof (induction t arbitrary: i)
  case (Finite_Pair u v)
  obtain j k where read: "value_reference_read T i = Some (Pair_Shape j k)"
    and u: "reference_term T j = Some u" and v: "reference_term T k = Some v"
    using Finite_Pair.prems
  proof (cases rule: reference_term_cases)
    case (leaf l)
    then show ?thesis by (cases l) simp_all
  next
    case (pair j k x y)
    then show ?thesis by (auto intro: that)
  qed
  have "value_reference_index (Pair_Shape j k) T = Some i"
    using value_reference_index_distinct_read[OF _ read] tf by (simp add: table_formed_def)
  with Finite_Pair.IH(1)[OF u] Finite_Pair.IH(2)[OF v] keyed_share_shape_present[OF rep] show ?case by simp
next
  case (Finite_Payload v)
  have "reference_term T i = Some (leaf_term (Payload_Leaf v))" using Finite_Payload.prems by simp
  then have "value_reference_read T i = Some (Leaf_Shape (Payload_Leaf v))" by (rule reference_factor_leaf_read)
  then have "value_reference_index (Leaf_Shape (Payload_Leaf v)) T = Some i"
    using tf by (intro value_reference_index_distinct_read) (simp_all add: table_formed_def)
  then show ?case using keyed_share_shape_present[OF rep] by simp
next
  case (Finite_Target a)
  have "reference_term T i = Some (leaf_term (Target_Leaf a))" using Finite_Target.prems by simp
  then have "value_reference_read T i = Some (Leaf_Shape (Target_Leaf a))" by (rule reference_factor_leaf_read)
  then have "value_reference_index (Leaf_Shape (Target_Leaf a)) T = Some i"
    using tf by (intro value_reference_index_distinct_read) (simp_all add: table_formed_def)
  then show ?case using keyed_share_shape_present[OF rep] by simp
qed

text \<open>A term the table holds: some reference decodes to it.\<close>

definition table_holds :: "shape list \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "table_holds T t \<longleftrightarrow> (\<exists>i. reference_term T i = Some t)"

lemma table_holds_extends: "table_holds T t \<Longrightarrow> table_extends T T' \<Longrightarrow> table_holds T' t"
  by (auto simp: table_holds_def table_extends_def)

subsection \<open>The ground terms of a pattern, and a family shared against one state\<close>

text \<open>
  The ground terms of a pattern are its maximal ground subpatterns, as terms. A family of patterns is shared by
  sharing the ground terms of all its members in their order (@{typ ordered_factor_term}) and reading each member
  against the resulting state (@{text keyed_pattern_at}), which holds them all.
\<close>

fun pattern_grounds :: "'v finite_term_pattern \<Rightarrow> finite_factor_term fset" where
  "pattern_grounds (Finite_Variable a) = {||}"
| "pattern_grounds (Finite_Pattern_Target t) = {|Finite_Target t|}"
| "pattern_grounds (Finite_Pattern_Payload v) = {|Finite_Payload v|}"
| "pattern_grounds (Finite_Pattern_Pair p r) =
    (if finite_pattern_variables p = {||} \<and> finite_pattern_variables r = {||}
     then {|finite_residual_term (Finite_Pattern_Pair p r)|} else pattern_grounds p |\<union>| pattern_grounds r)"

fun keyed_pattern_at :: "share_state \<Rightarrow> 'v finite_term_pattern \<Rightarrow> 'v shared_pattern" where
  "keyed_pattern_at q (Finite_Variable a) = Shared_Variable a"
| "keyed_pattern_at q (Finite_Pattern_Target t) = Shared_Ground (fst (keyed_share_term (Finite_Target t) q))"
| "keyed_pattern_at q (Finite_Pattern_Payload v) = Shared_Ground (fst (keyed_share_term (Finite_Payload v) q))"
| "keyed_pattern_at q (Finite_Pattern_Pair p r) =
    (if finite_pattern_variables p = {||} \<and> finite_pattern_variables r = {||}
     then Shared_Ground (fst (keyed_share_term (finite_residual_term (Finite_Pattern_Pair p r)) q))
     else shared_node (keyed_pattern_at q p) (keyed_pattern_at q r))"

lemma finite_exact_residual_ground:
  "finite_pattern_variables p = {||} \<Longrightarrow> finite_exact_term_pattern (finite_residual_term p) = p"
  by (induction p) simp_all


lemma keyed_ground_at:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T" and held: "table_holds T t"
  shows "reference_term T (fst (keyed_share_term t q)) = Some t" "fst (keyed_share_term t q) < length T"
proof -
  obtain i where i: "reference_term T i = Some t" using held by (auto simp: table_holds_def)
  with keyed_share_term_present[OF rep tf i]
  show "reference_term T (fst (keyed_share_term t q)) = Some t" "fst (keyed_share_term t q) < length T"
    by (simp_all add: reference_term_bound)
qed

theorem keyed_pattern_at_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
  shows "(\<And>t. t |\<in>| pattern_grounds p \<Longrightarrow> table_holds T t) \<Longrightarrow>
    shared_pattern_formed T (keyed_pattern_at q p) \<and> shared_pattern_project T (keyed_pattern_at q p) = p \<and>
    shared_collapsed (keyed_pattern_at q p)"
proof (induction p)
  case (Finite_Variable a)
  then show ?case by simp
next
  case (Finite_Pattern_Target a)
  have "table_holds T (Finite_Target a)" using Finite_Pattern_Target.prems by simp
  from keyed_ground_at[OF rep tf this] show ?case by simp
next
  case (Finite_Pattern_Payload v)
  have "table_holds T (Finite_Payload v)" using Finite_Pattern_Payload.prems by simp
  from keyed_ground_at[OF rep tf this] show ?case by simp
next
  case (Finite_Pattern_Pair p r)
  show ?case
  proof (cases "finite_pattern_variables p = {||} \<and> finite_pattern_variables r = {||}")
    case True
    let ?t = "finite_residual_term (Finite_Pattern_Pair p r)"
    have "table_holds T ?t" using Finite_Pattern_Pair.prems True by simp
    note g = keyed_ground_at[OF rep tf this]
    have "finite_exact_term_pattern ?t = Finite_Pattern_Pair p r"
      using finite_exact_residual_ground[of "Finite_Pattern_Pair p r"] True by (simp del: finite_residual_term.simps)
    with g True show ?thesis by (simp del: keyed_share_term.simps finite_residual_term.simps)
  next
    case False
    have ip: "shared_pattern_formed T (keyed_pattern_at q p) \<and> shared_pattern_project T (keyed_pattern_at q p) = p \<and>
        shared_collapsed (keyed_pattern_at q p)"
      using Finite_Pattern_Pair.IH(1) Finite_Pattern_Pair.prems False by (auto split: if_splits)
    have ir: "shared_pattern_formed T (keyed_pattern_at q r) \<and> shared_pattern_project T (keyed_pattern_at q r) = r \<and>
        shared_collapsed (keyed_pattern_at q r)"
      using Finite_Pattern_Pair.IH(2) Finite_Pattern_Pair.prems False by (auto split: if_splits)
    have vars: "shared_pattern_variables (keyed_pattern_at q p) |\<union>| shared_pattern_variables (keyed_pattern_at q r) \<noteq> {||}"
      using ip ir False shared_pattern_variables_project[of T "keyed_pattern_at q p"]
        shared_pattern_variables_project[of T "keyed_pattern_at q r"] by auto
    have eq: "keyed_pattern_at q (Finite_Pattern_Pair p r) = shared_node (keyed_pattern_at q p) (keyed_pattern_at q r)"
      by (simp only: keyed_pattern_at.simps if_not_P[OF False])
    show ?thesis unfolding eq using ip ir vars by (simp add: shared_node_def)
  qed
qed

text \<open>The ground terms of a finite family of patterns, and the state extended by all of them in their order.\<close>

definition keyed_share_grounds :: "finite_factor_term fset \<Rightarrow> share_state \<Rightarrow> share_state" where
  "keyed_share_grounds G q = snd (keyed_share_terms (ordered_finite_terms G) q)"

lemma keyed_share_grounds:
  assumes q: "share_state_formed q"
  shows "share_state_formed (keyed_share_grounds G q)"
    and "table_extends (share_state_table q) (share_state_table (keyed_share_grounds G q))"
    and "t |\<in>| G \<Longrightarrow> table_holds (share_state_table (keyed_share_grounds G q)) t"
proof -
  let ?T = "share_state_table q" and ?ts = "ordered_finite_terms G"
  have rep: "keyed_state_represents q ?T" and tf: "table_formed ?T" using q by (simp_all add: share_state_formed_def)
  have k: "keyed_state_represents (snd (keyed_share_terms ?ts q)) (snd (share_terms ?ts ?T))"
    using keyed_share_terms_exact[OF rep, of ?ts] by simp
  have t: "share_state_table (keyed_share_grounds G q) = snd (share_terms ?ts ?T)"
    using share_state_table_represents[OF k] by (simp add: keyed_share_grounds_def)
  note e = share_terms_exact[OF tf, of ?ts]
  show "share_state_formed (keyed_share_grounds G q)"
    using k t e by (simp add: share_state_formed_def keyed_share_grounds_def)
  show "table_extends ?T (share_state_table (keyed_share_grounds G q))"
    using t share_terms_preserves by (simp add: table_extends_def)
  assume "t |\<in>| G"
  then have "t \<in> set ?ts" by (simp add: ordered_finite_terms_set)
  then obtain n where n: "n < length ?ts" "?ts ! n = t" by (auto simp: in_set_conv_nth)
  have "map (reference_term (snd (share_terms ?ts ?T))) (fst (share_terms ?ts ?T)) = map Some ?ts" using e by simp
  then have "reference_term (snd (share_terms ?ts ?T)) (fst (share_terms ?ts ?T) ! n) = Some t"
    using n by (metis length_map nth_map)
  then show "table_holds (share_state_table (keyed_share_grounds G q)) t" using t by (auto simp: table_holds_def)
qed

subsection \<open>Substitution rebuilding through the keyed constructor\<close>

text \<open>
  Substitution returns a pair whose cached variables it does not bind as it stands, and rebuilds every other pair
  through the keyed first-occurrence constructor, so a pair whose parts became ground is made a reference at once:
  a collapsed pattern substituted by collapsed values stays collapsed, with no separate pass over it.
\<close>

fun keyed_substitute :: "('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow> 'a shared_pattern \<Rightarrow> share_state \<Rightarrow>
    'a shared_pattern \<times> share_state" where
  "keyed_substitute \<sigma> D (Shared_Variable a) q = (\<sigma> a, q)"
| "keyed_substitute \<sigma> D (Shared_Ground i) q = (Shared_Ground i, q)"
| "keyed_substitute \<sigma> D (Shared_Node A p r) q = (if A |\<inter>| D = {||} then (Shared_Node A p r, q) else
    (case keyed_substitute \<sigma> D p q of (p', q1) \<Rightarrow> (case keyed_substitute \<sigma> D r q1 of (r', q2) \<Rightarrow>
      keyed_share_node p' r' q2)))"

theorem keyed_substitute_exact:
  shows "(\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a) \<Longrightarrow>
    share_state_formed q \<Longrightarrow> shared_pattern_formed (share_state_table q) p \<Longrightarrow>
    (\<And>a. shared_pattern_formed (share_state_table q) (\<sigma> a)) \<Longrightarrow>
    share_state_formed (snd (keyed_substitute \<sigma> D p q)) \<and>
    shared_pattern_formed (share_state_table (snd (keyed_substitute \<sigma> D p q))) (fst (keyed_substitute \<sigma> D p q)) \<and>
    shared_pattern_project (share_state_table (snd (keyed_substitute \<sigma> D p q))) (fst (keyed_substitute \<sigma> D p q)) =
      finite_pattern_substitute (\<lambda>a. shared_pattern_project (share_state_table q) (\<sigma> a))
        (shared_pattern_project (share_state_table q) p) \<and>
    table_extends (share_state_table q) (share_state_table (snd (keyed_substitute \<sigma> D p q))) \<and>
    (shared_collapsed p \<longrightarrow> (\<forall>a. shared_collapsed (\<sigma> a)) \<longrightarrow> shared_collapsed (fst (keyed_substitute \<sigma> D p q)))"
proof (induction \<sigma> D p q rule: keyed_substitute.induct)
  case (1 \<sigma> D a q)
  then show ?case by simp
next
  case (2 \<sigma> D i q)
  have "finite_pattern_variables (shared_pattern_project (share_state_table q) (Shared_Ground i)) = {||}"
    by (cases "reference_term (share_state_table q) i") (simp_all add: finite_exact_term_pattern_variables)
  then have "finite_pattern_substitute (\<lambda>a. shared_pattern_project (share_state_table q) (\<sigma> a))
      (shared_pattern_project (share_state_table q) (Shared_Ground i)) = shared_pattern_project (share_state_table q) (Shared_Ground i)"
    by (intro finite_pattern_substitute_outside) auto
  with "2.prems" show ?case by simp
next
  case (3 \<sigma> D A p r q)
  let ?T = "share_state_table q"
  have tf: "table_formed ?T" using "3.prems"(2) by (simp add: share_state_formed_def)
  have pf: "shared_pattern_formed ?T p" and rf: "shared_pattern_formed ?T r"
    and A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables r" using "3.prems"(3) by simp_all
  show ?case
  proof (cases "A |\<inter>| D = {||}")
    case True
    have "\<And>x. x |\<in>| finite_pattern_variables (shared_pattern_project ?T (Shared_Node A p r)) \<Longrightarrow>
        shared_pattern_project ?T (\<sigma> x) = Finite_Variable x"
    proof -
      fix x assume "x |\<in>| finite_pattern_variables (shared_pattern_project ?T (Shared_Node A p r))"
      then have "x |\<in>| A" using shared_pattern_variables_project[OF "3.prems"(3)] by simp
      with True have "x |\<notin>| D" by auto
      then show "shared_pattern_project ?T (\<sigma> x) = Finite_Variable x" using "3.prems"(1)[of x] by simp
    qed
    then have "finite_pattern_substitute (\<lambda>a. shared_pattern_project ?T (\<sigma> a)) (shared_pattern_project ?T (Shared_Node A p r)) =
        shared_pattern_project ?T (Shared_Node A p r)"
      by (rule finite_pattern_substitute_outside)
    with True "3.prems" show ?thesis by simp
  next
    case False
    obtain p' q1 where e1: "keyed_substitute \<sigma> D p q = (p', q1)" by (cases "keyed_substitute \<sigma> D p q") auto
    obtain r' q2 where e2: "keyed_substitute \<sigma> D r q1 = (r', q2)" by (cases "keyed_substitute \<sigma> D r q1") auto
    have ih1: "share_state_formed q1 \<and> shared_pattern_formed (share_state_table q1) p' \<and>
        shared_pattern_project (share_state_table q1) p' =
          finite_pattern_substitute (\<lambda>a. shared_pattern_project ?T (\<sigma> a)) (shared_pattern_project ?T p) \<and>
        table_extends ?T (share_state_table q1) \<and>
        (shared_collapsed p \<longrightarrow> (\<forall>a. shared_collapsed (\<sigma> a)) \<longrightarrow> shared_collapsed p')"
      using "3.IH"(1)[OF False "3.prems"(1) "3.prems"(2) pf "3.prems"(4)] e1 by simp
    let ?T1 = "share_state_table q1"
    have s1: "\<And>a. shared_pattern_formed ?T1 (\<sigma> a)" "\<And>a. shared_pattern_project ?T1 (\<sigma> a) = shared_pattern_project ?T (\<sigma> a)"
      using shared_pattern_extends[OF tf "3.prems"(4)] ih1 by blast+
    have r1: "shared_pattern_formed ?T1 r" "shared_pattern_project ?T1 r = shared_pattern_project ?T r"
      using shared_pattern_extends[OF tf rf] ih1 by blast+
    have ih2: "share_state_formed q2 \<and> shared_pattern_formed (share_state_table q2) r' \<and>
        shared_pattern_project (share_state_table q2) r' =
          finite_pattern_substitute (\<lambda>a. shared_pattern_project ?T1 (\<sigma> a)) (shared_pattern_project ?T1 r) \<and>
        table_extends ?T1 (share_state_table q2) \<and>
        (shared_collapsed r \<longrightarrow> (\<forall>a. shared_collapsed (\<sigma> a)) \<longrightarrow> shared_collapsed r')"
      using "3.IH"(2)[OF False e1[symmetric]] "3.prems"(1) ih1 r1(1) s1(1) e2 by simp
    let ?T2 = "share_state_table q2"
    have tf1: "table_formed ?T1" using ih1 by (simp add: share_state_formed_def)
    have p2: "shared_pattern_formed ?T2 p'" "shared_pattern_project ?T2 p' = shared_pattern_project ?T1 p'"
      using shared_pattern_extends[OF tf1 _ ] ih1 ih2 by blast+
    have q2f: "share_state_formed q2" and r2f: "shared_pattern_formed ?T2 r'" using ih2 by simp_all
    note n = share_state_node[OF q2f p2(1) r2f]
    have res: "keyed_substitute \<sigma> D (Shared_Node A p r) q = keyed_share_node p' r' q2"
      using False e1 e2 by simp
    have col: "shared_collapsed (Shared_Node A p r) \<longrightarrow> (\<forall>a. shared_collapsed (\<sigma> a)) \<longrightarrow>
        shared_collapsed (fst (keyed_share_node p' r' q2))"
    proof (intro impI)
      assume c: "shared_collapsed (Shared_Node A p r)" "\<forall>a. shared_collapsed (\<sigma> a)"
      have "shared_collapsed p'" "shared_collapsed r'" using ih1 ih2 c by simp_all
      then have "shared_collapsed (fst (share_node p' r' ?T2))" by (rule share_node_collapsed)
      then show "shared_collapsed (fst (keyed_share_node p' r' q2))" using n(2) by simp
    qed
    have ext: "table_extends ?T (share_state_table (snd (keyed_share_node p' r' q2)))"
      using ih1 ih2 n(5) by (blast intro: table_extends_trans)
    show ?thesis
      unfolding res
      using n ih1 ih2 p2 s1 r1 col ext by simp
  qed
qed

section \<open>Material patterns, goals and nodes over shared patterns\<close>

text \<open>
  A goal and a node of R3's search (@{typ "('a,'s,'d,'c) resolution_goal"}, @{typ "('a,'s,'d,'c) resolution_node"})
  hold their patterns as shared patterns over the search's table. A call pattern, of a goal and of a node, is kept
  collapsed, so a ground call is a reference and two ground calls are compared as numbers; the patterns of a material
  goal and a node's bindings are kept formed. Each is formed over the table, projects to R3's goal or node, is read
  from R3's against a state that holds its ground terms, and is substituted through the keyed constructor.
\<close>

subsection \<open>Material patterns\<close>

record 'a shared_material =
  shared_material_source :: "'a shared_pattern"
  shared_material_atoms :: "'a shared_pattern"
  shared_material_edges :: "'a shared_pattern"
  shared_material_counts :: "'a shared_pattern"
  shared_material_functions :: "'a shared_pattern"

definition shared_material_variables :: "'a shared_material \<Rightarrow> 'a fset" where
  "shared_material_variables M = shared_pattern_variables (shared_material_source M) |\<union>|
    shared_pattern_variables (shared_material_atoms M) |\<union>| shared_pattern_variables (shared_material_edges M) |\<union>|
    shared_pattern_variables (shared_material_counts M) |\<union>| shared_pattern_variables (shared_material_functions M)"

definition shared_material_formed :: "shape list \<Rightarrow> 'a shared_material \<Rightarrow> bool" where
  "shared_material_formed T M \<longleftrightarrow> shared_pattern_formed T (shared_material_source M) \<and>
    shared_pattern_formed T (shared_material_atoms M) \<and> shared_pattern_formed T (shared_material_edges M) \<and>
    shared_pattern_formed T (shared_material_counts M) \<and> shared_pattern_formed T (shared_material_functions M)"

definition shared_material_project :: "shape list \<Rightarrow> 'a shared_material \<Rightarrow> 'a finite_material_pattern" where
  "shared_material_project T M =
    \<lparr>finite_material_source = shared_pattern_project T (shared_material_source M),
     finite_material_atoms = shared_pattern_project T (shared_material_atoms M),
     finite_material_edges = shared_pattern_project T (shared_material_edges M),
     finite_material_counts = shared_pattern_project T (shared_material_counts M),
     finite_material_functions = shared_pattern_project T (shared_material_functions M)\<rparr>"

definition shared_material_substitute ::
    "('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow> 'a shared_material \<Rightarrow> 'a shared_material" where
  "shared_material_substitute \<sigma> D M =
    \<lparr>shared_material_source = shared_substitute \<sigma> D (shared_material_source M),
     shared_material_atoms = shared_substitute \<sigma> D (shared_material_atoms M),
     shared_material_edges = shared_substitute \<sigma> D (shared_material_edges M),
     shared_material_counts = shared_substitute \<sigma> D (shared_material_counts M),
     shared_material_functions = shared_substitute \<sigma> D (shared_material_functions M)\<rparr>"

definition material_grounds :: "'a finite_material_pattern \<Rightarrow> finite_factor_term fset" where
  "material_grounds M = pattern_grounds (finite_material_source M) |\<union>| pattern_grounds (finite_material_atoms M) |\<union>|
    pattern_grounds (finite_material_edges M) |\<union>| pattern_grounds (finite_material_counts M) |\<union>|
    pattern_grounds (finite_material_functions M)"

definition shared_material_of :: "share_state \<Rightarrow> 'a finite_material_pattern \<Rightarrow> 'a shared_material" where
  "shared_material_of q M =
    \<lparr>shared_material_source = keyed_pattern_at q (finite_material_source M),
     shared_material_atoms = keyed_pattern_at q (finite_material_atoms M),
     shared_material_edges = keyed_pattern_at q (finite_material_edges M),
     shared_material_counts = keyed_pattern_at q (finite_material_counts M),
     shared_material_functions = keyed_pattern_at q (finite_material_functions M)\<rparr>"

lemma shared_material_variables_project:
  "shared_material_formed T M \<Longrightarrow> shared_material_variables M = finite_material_variables (shared_material_project T M)"
  by (simp add: shared_material_formed_def shared_material_variables_def shared_material_project_def
    finite_material_variables_def shared_pattern_variables_project[of T])

lemma shared_material_substitute_project:
  assumes "shared_material_formed T M" and "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_material_project T (shared_material_substitute \<sigma> D M) =
    finite_material_pattern_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_material_project T M)"
  using assms by (simp add: shared_material_formed_def shared_material_project_def shared_material_substitute_def
    finite_material_pattern_substitute_def shared_substitute_project)

lemma shared_material_substitute_formed:
  "shared_material_formed T M \<Longrightarrow> (\<And>a. shared_pattern_formed T (\<sigma> a)) \<Longrightarrow>
    shared_material_formed T (shared_material_substitute \<sigma> D M)"
  by (simp add: shared_material_formed_def shared_material_substitute_def shared_substitute_formed)

lemma shared_material_extends:
  assumes tf: "table_formed T" and M: "shared_material_formed T M" and ext: "table_extends T T'"
  shows "shared_material_formed T' M" "shared_material_project T' M = shared_material_project T M"
proof -
  have f: "shared_pattern_formed T (shared_material_source M)" "shared_pattern_formed T (shared_material_atoms M)"
    "shared_pattern_formed T (shared_material_edges M)" "shared_pattern_formed T (shared_material_counts M)"
    "shared_pattern_formed T (shared_material_functions M)" using M by (simp_all add: shared_material_formed_def)
  note e1 = shared_pattern_extends[OF tf f(1) ext] and e2 = shared_pattern_extends[OF tf f(2) ext]
    and e3 = shared_pattern_extends[OF tf f(3) ext] and e4 = shared_pattern_extends[OF tf f(4) ext]
    and e5 = shared_pattern_extends[OF tf f(5) ext]
  show "shared_material_formed T' M" "shared_material_project T' M = shared_material_project T M"
    using e1 e2 e3 e4 e5 by (simp_all add: shared_material_formed_def shared_material_project_def)
qed

lemma shared_material_of_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
    and held: "\<And>t. t |\<in>| material_grounds M \<Longrightarrow> table_holds T t"
  shows "shared_material_formed T (shared_material_of q M) \<and> shared_material_project T (shared_material_of q M) = M"
proof -
  note k = keyed_pattern_at_exact[OF rep tf]
  have h1: "\<And>t. t |\<in>| pattern_grounds (finite_material_source M) \<Longrightarrow> table_holds T t"
    and h2: "\<And>t. t |\<in>| pattern_grounds (finite_material_atoms M) \<Longrightarrow> table_holds T t"
    and h3: "\<And>t. t |\<in>| pattern_grounds (finite_material_edges M) \<Longrightarrow> table_holds T t"
    and h4: "\<And>t. t |\<in>| pattern_grounds (finite_material_counts M) \<Longrightarrow> table_holds T t"
    and h5: "\<And>t. t |\<in>| pattern_grounds (finite_material_functions M) \<Longrightarrow> table_holds T t"
    using held by (simp_all add: material_grounds_def)
  note s1 = k[where p = "finite_material_source M", OF h1] and s2 = k[where p = "finite_material_atoms M", OF h2]
    and s3 = k[where p = "finite_material_edges M", OF h3] and s4 = k[where p = "finite_material_counts M", OF h4]
    and s5 = k[where p = "finite_material_functions M", OF h5]
  show ?thesis using s1 s2 s3 s4 s5
    by (cases M) (simp add: shared_material_formed_def shared_material_project_def shared_material_of_def)
qed

subsection \<open>Goals\<close>

datatype ('a,'s,'d,'c) shared_goal =
    Shared_Call_Goal "'s list" "('d \<times> 'c \<times> 's) option" 'd "('s,'a) resolution_variable shared_pattern"
  | Shared_Material_Goal "'s list" "'d \<times> 'c \<times> 's" "('s,'a) resolution_variable shared_material"

fun shared_goal_position :: "('a,'s,'d,'c) shared_goal \<Rightarrow> 's list" where
  "shared_goal_position (Shared_Call_Goal q r d p) = q"
| "shared_goal_position (Shared_Material_Goal q r M) = q"

fun shared_goal_variables :: "('a,'s,'d,'c) shared_goal \<Rightarrow> ('s,'a) resolution_variable fset" where
  "shared_goal_variables (Shared_Call_Goal q r d p) = shared_pattern_variables p"
| "shared_goal_variables (Shared_Material_Goal q r M) = shared_material_variables M"

fun shared_goal_formed :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow> bool" where
  "shared_goal_formed T (Shared_Call_Goal q r d p) \<longleftrightarrow> shared_pattern_formed T p \<and> shared_collapsed p"
| "shared_goal_formed T (Shared_Material_Goal q r M) \<longleftrightarrow> shared_material_formed T M"

fun shared_goal_project :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow> ('a,'s,'d,'c) resolution_goal" where
  "shared_goal_project T (Shared_Call_Goal q r d p) = Resolution_Call_Goal q r d (shared_pattern_project T p)"
| "shared_goal_project T (Shared_Material_Goal q r M) = Resolution_Material_Goal q r (shared_material_project T M)"

fun goal_grounds :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> finite_factor_term fset" where
  "goal_grounds (Resolution_Call_Goal q r d p) = pattern_grounds p"
| "goal_grounds (Resolution_Material_Goal q r M) = material_grounds M"

fun shared_goal_of :: "share_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) shared_goal" where
  "shared_goal_of q' (Resolution_Call_Goal q r d p) = Shared_Call_Goal q r d (keyed_pattern_at q' p)"
| "shared_goal_of q' (Resolution_Material_Goal q r M) = Shared_Material_Goal q r (shared_material_of q' M)"

fun shared_goal_substitute :: "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow> share_state \<Rightarrow>
    ('a,'s,'d,'c) shared_goal \<times> share_state" where
  "shared_goal_substitute \<sigma> D (Shared_Call_Goal q r d p) q' =
    (case keyed_substitute \<sigma> D p q' of (p', q'') \<Rightarrow> (Shared_Call_Goal q r d p', q''))"
| "shared_goal_substitute \<sigma> D (Shared_Material_Goal q r M) q' =
    (Shared_Material_Goal q r (shared_material_substitute \<sigma> D M), q')"

lemma shared_goal_project_position [simp]:
  "resolution_goal_position (shared_goal_project T g) = shared_goal_position g"
  by (cases g) simp_all

lemma shared_goal_variables_project:
  "shared_goal_formed T g \<Longrightarrow> shared_goal_variables g = resolution_goal_variables (shared_goal_project T g)"
  by (cases g) (simp_all add: shared_pattern_variables_project[of T] shared_material_variables_project[of T])

lemma shared_goal_extends:
  assumes tf: "table_formed T" and g: "shared_goal_formed T g" and ext: "table_extends T T'"
  shows "shared_goal_formed T' g \<and> shared_goal_project T' g = shared_goal_project T g"
proof (cases g)
  case (Shared_Call_Goal q r d p)
  have "shared_pattern_formed T p" using g Shared_Call_Goal by simp
  note e = shared_pattern_extends[OF tf this ext]
  show ?thesis using e g Shared_Call_Goal by simp
next
  case (Shared_Material_Goal q r M)
  have "shared_material_formed T M" using g Shared_Material_Goal by simp
  note e = shared_material_extends[OF tf this ext]
  show ?thesis using e Shared_Material_Goal by simp
qed

lemma shared_goal_of_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
    and held: "\<And>t. t |\<in>| goal_grounds g \<Longrightarrow> table_holds T t"
  shows "shared_goal_formed T (shared_goal_of q g) \<and> shared_goal_project T (shared_goal_of q g) = g"
proof (cases g)
  case (Resolution_Call_Goal q0 r d p)
  have "\<And>t. t |\<in>| pattern_grounds p \<Longrightarrow> table_holds T t" using held Resolution_Call_Goal by simp
  from keyed_pattern_at_exact[OF rep tf, where p = p, OF this] Resolution_Call_Goal show ?thesis by simp
next
  case (Resolution_Material_Goal q0 r M)
  have "\<And>t. t |\<in>| material_grounds M \<Longrightarrow> table_holds T t" using held Resolution_Material_Goal by simp
  from shared_material_of_exact[OF rep tf, where M = M, OF this] Resolution_Material_Goal show ?thesis by simp
qed

lemma shared_goal_substitute_position [simp]:
  "shared_goal_position (fst (shared_goal_substitute \<sigma> D g q)) = shared_goal_position g"
  by (cases g) (simp_all add: split_def)

theorem shared_goal_substitute_exact:
  assumes q: "share_state_formed q" and g: "shared_goal_formed (share_state_table q) g"
    and \<sigma>: "\<And>a. shared_pattern_formed (share_state_table q) (\<sigma> a)" "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "share_state_formed (snd (shared_goal_substitute \<sigma> D g q)) \<and>
    shared_goal_formed (share_state_table (snd (shared_goal_substitute \<sigma> D g q))) (fst (shared_goal_substitute \<sigma> D g q)) \<and>
    shared_goal_project (share_state_table (snd (shared_goal_substitute \<sigma> D g q))) (fst (shared_goal_substitute \<sigma> D g q)) =
      resolution_goal_substitute (\<lambda>a. shared_pattern_project (share_state_table q) (\<sigma> a))
        (shared_goal_project (share_state_table q) g) \<and>
    table_extends (share_state_table q) (share_state_table (snd (shared_goal_substitute \<sigma> D g q)))"
proof (cases g)
  case (Shared_Call_Goal q0 r d p)
  have "share_state_formed (snd (keyed_substitute \<sigma> D p q)) \<and>
    shared_pattern_formed (share_state_table (snd (keyed_substitute \<sigma> D p q))) (fst (keyed_substitute \<sigma> D p q)) \<and>
    shared_pattern_project (share_state_table (snd (keyed_substitute \<sigma> D p q))) (fst (keyed_substitute \<sigma> D p q)) =
      finite_pattern_substitute (\<lambda>a. shared_pattern_project (share_state_table q) (\<sigma> a))
        (shared_pattern_project (share_state_table q) p) \<and>
    table_extends (share_state_table q) (share_state_table (snd (keyed_substitute \<sigma> D p q))) \<and>
    (shared_collapsed p \<longrightarrow> (\<forall>a. shared_collapsed (\<sigma> a)) \<longrightarrow> shared_collapsed (fst (keyed_substitute \<sigma> D p q)))"
    using keyed_substitute_exact[where \<sigma> = \<sigma> and D = D and p = p, OF out q _ \<sigma>(1)] g Shared_Call_Goal by simp
  with g \<sigma>(2) Shared_Call_Goal show ?thesis by (simp add: split_def)
next
  case (Shared_Material_Goal q0 r M)
  with g q \<sigma>(1) out show ?thesis
    by (simp add: shared_material_substitute_formed shared_material_substitute_project)
qed

subsection \<open>Nodes\<close>

datatype ('a,'s,'d,'c) shared_derivation = Shared_Derivation
  (shared_derivation_position: "'s list") (shared_derivation_site: 'd) (shared_derivation_clause: 'c)
  (shared_derivation_schema: "('a,'s,'d) finite_factor_schema")
  (shared_derivation_call: "('s,'a) resolution_variable shared_pattern")
  (shared_derivation_bindings: "('a \<times> ('s,'a) resolution_variable shared_pattern) fset")

definition shared_derivation_variables :: "('a,'s,'d,'c) shared_derivation \<Rightarrow> ('s,'a) resolution_variable fset" where
  "shared_derivation_variables nd = shared_pattern_variables (shared_derivation_call nd) |\<union>|
    ffUnion (fimage (\<lambda>z. shared_pattern_variables (snd z)) (shared_derivation_bindings nd))"

definition shared_derivation_formed :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> bool" where
  "shared_derivation_formed T nd \<longleftrightarrow> shared_pattern_formed T (shared_derivation_call nd) \<and>
    shared_collapsed (shared_derivation_call nd) \<and> fBall (shared_derivation_bindings nd) (\<lambda>z. shared_pattern_formed T (snd z))"

definition shared_derivation_project :: "shape list \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> ('a,'s,'d,'c) resolution_node" where
  "shared_derivation_project T nd = Resolution_Node (shared_derivation_position nd) (shared_derivation_site nd)
    (shared_derivation_clause nd) (shared_derivation_schema nd) (shared_pattern_project T (shared_derivation_call nd))
    (fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd))"

definition node_grounds :: "('a,'s,'d,'c) resolution_node \<Rightarrow> finite_factor_term fset" where
  "node_grounds nd = pattern_grounds (resolution_node_call nd) |\<union>|
    ffUnion (fimage (\<lambda>z. pattern_grounds (snd z)) (resolution_node_bindings nd))"

definition shared_derivation_of :: "share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) shared_derivation" where
  "shared_derivation_of q nd = Shared_Derivation (resolution_node_position nd) (resolution_node_site nd)
    (resolution_node_clause nd) (resolution_node_schema nd) (keyed_pattern_at q (resolution_node_call nd))
    (fimage (\<lambda>z. (fst z, keyed_pattern_at q (snd z))) (resolution_node_bindings nd))"

definition shared_derivation_substitute :: "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow>
    ('s,'a) resolution_variable fset \<Rightarrow> ('a,'s,'d,'c) shared_derivation \<Rightarrow> share_state \<Rightarrow>
    ('a,'s,'d,'c) shared_derivation \<times> share_state" where
  "shared_derivation_substitute \<sigma> D nd q = (case keyed_substitute \<sigma> D (shared_derivation_call nd) q of (c', q') \<Rightarrow>
    (Shared_Derivation (shared_derivation_position nd) (shared_derivation_site nd) (shared_derivation_clause nd)
      (shared_derivation_schema nd) c' (fimage (\<lambda>z. (fst z, shared_substitute \<sigma> D (snd z))) (shared_derivation_bindings nd)), q'))"

lemma shared_derivation_project_fields [simp]:
  "resolution_node_position (shared_derivation_project T nd) = shared_derivation_position nd"
  "resolution_node_site (shared_derivation_project T nd) = shared_derivation_site nd"
  "resolution_node_clause (shared_derivation_project T nd) = shared_derivation_clause nd"
  "resolution_node_schema (shared_derivation_project T nd) = shared_derivation_schema nd"
  "resolution_node_call (shared_derivation_project T nd) = shared_pattern_project T (shared_derivation_call nd)"
  "resolution_node_bindings (shared_derivation_project T nd) =
    fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd)"
  by (simp_all add: shared_derivation_project_def)

lemma shared_derivation_variables_project:
  assumes "shared_derivation_formed T nd"
  shows "shared_derivation_variables nd = resolution_node_variables (shared_derivation_project T nd)"
proof -
  have "fimage (\<lambda>z. shared_pattern_variables (snd z)) (shared_derivation_bindings nd) =
      fimage (\<lambda>z. finite_pattern_variables (shared_pattern_project T (snd z))) (shared_derivation_bindings nd)"
  proof (rule fimage_cong_on)
    fix z assume "z |\<in>| shared_derivation_bindings nd"
    then have "shared_pattern_formed T (snd z)" using assms by (auto simp: shared_derivation_formed_def)
    then show "shared_pattern_variables (snd z) = finite_pattern_variables (shared_pattern_project T (snd z))"
      by (rule shared_pattern_variables_project)
  qed
  moreover have "shared_pattern_variables (shared_derivation_call nd) =
      finite_pattern_variables (shared_pattern_project T (shared_derivation_call nd))"
    using assms by (intro shared_pattern_variables_project) (simp add: shared_derivation_formed_def)
  ultimately show ?thesis
    by (simp add: shared_derivation_variables_def resolution_node_variables_def fimage_fimage comp_def)
qed

lemma shared_derivation_extends:
  assumes tf: "table_formed T" and nd: "shared_derivation_formed T nd" and ext: "table_extends T T'"
  shows "shared_derivation_formed T' nd" "shared_derivation_project T' nd = shared_derivation_project T nd"
proof -
  have b: "shared_pattern_formed T' (snd z) \<and> shared_pattern_project T' (snd z) = shared_pattern_project T (snd z)"
    if z: "z |\<in>| shared_derivation_bindings nd" for z
  proof -
    have "shared_pattern_formed T (snd z)" using nd z by (auto simp: shared_derivation_formed_def)
    from shared_pattern_extends[OF tf this ext] show ?thesis by simp
  qed
  have "shared_pattern_formed T (shared_derivation_call nd)" using nd by (simp add: shared_derivation_formed_def)
  note c = shared_pattern_extends[OF tf this ext]
  show "shared_derivation_formed T' nd" using nd b c by (simp add: shared_derivation_formed_def)
  have "fimage (\<lambda>z. (fst z, shared_pattern_project T' (snd z))) (shared_derivation_bindings nd) =
      fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (shared_derivation_bindings nd)"
    using b by (intro fimage_cong_on) simp
  with c show "shared_derivation_project T' nd = shared_derivation_project T nd"
    by (simp add: shared_derivation_project_def)
qed

lemma shared_derivation_of_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
    and held: "\<And>t. t |\<in>| node_grounds nd \<Longrightarrow> table_holds T t"
  shows "shared_derivation_formed T (shared_derivation_of q nd) \<and> shared_derivation_project T (shared_derivation_of q nd) = nd"
proof -
  note k = keyed_pattern_at_exact[OF rep tf]
  have "\<And>t. t |\<in>| pattern_grounds (resolution_node_call nd) \<Longrightarrow> table_holds T t"
    using held by (simp add: node_grounds_def)
  note c = k[where p = "resolution_node_call nd", OF this]
  have b: "\<And>z. z |\<in>| resolution_node_bindings nd \<Longrightarrow> shared_pattern_formed T (keyed_pattern_at q (snd z)) \<and>
      shared_pattern_project T (keyed_pattern_at q (snd z)) = snd z"
  proof -
    fix z assume z: "z |\<in>| resolution_node_bindings nd"
    have "\<And>t. t |\<in>| pattern_grounds (snd z) \<Longrightarrow> table_holds T t"
      using held z by (auto simp: node_grounds_def intro: ffUnion_fimage_member)
    then show "shared_pattern_formed T (keyed_pattern_at q (snd z)) \<and>
      shared_pattern_project T (keyed_pattern_at q (snd z)) = snd z" using k[where p = "snd z"] by blast
  qed
  have "fimage (\<lambda>z. (fst z, shared_pattern_project T (snd z))) (fimage (\<lambda>z. (fst z, keyed_pattern_at q (snd z)))
      (resolution_node_bindings nd)) = resolution_node_bindings nd"
    using b by (force simp: fimage_fimage intro: fimage_fixed)
  then show ?thesis using c b
    by (cases nd) (auto simp: shared_derivation_of_def shared_derivation_formed_def shared_derivation_project_def)
qed

lemma shared_derivation_substitute_fields [simp]:
  "shared_derivation_position (fst (shared_derivation_substitute \<sigma> D nd q)) = shared_derivation_position nd"
  "shared_derivation_site (fst (shared_derivation_substitute \<sigma> D nd q)) = shared_derivation_site nd"
  "shared_derivation_clause (fst (shared_derivation_substitute \<sigma> D nd q)) = shared_derivation_clause nd"
  "shared_derivation_schema (fst (shared_derivation_substitute \<sigma> D nd q)) = shared_derivation_schema nd"
  by (simp_all add: shared_derivation_substitute_def split_def)

theorem shared_derivation_substitute_exact:
  assumes q: "share_state_formed q" and nd: "shared_derivation_formed (share_state_table q) nd"
    and \<sigma>: "\<And>a. shared_pattern_formed (share_state_table q) (\<sigma> a)" "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "share_state_formed (snd (shared_derivation_substitute \<sigma> D nd q)) \<and>
    shared_derivation_formed (share_state_table (snd (shared_derivation_substitute \<sigma> D nd q)))
      (fst (shared_derivation_substitute \<sigma> D nd q)) \<and>
    shared_derivation_project (share_state_table (snd (shared_derivation_substitute \<sigma> D nd q)))
      (fst (shared_derivation_substitute \<sigma> D nd q)) =
      resolution_node_substitute (\<lambda>a. shared_pattern_project (share_state_table q) (\<sigma> a))
        (shared_derivation_project (share_state_table q) nd) \<and>
    table_extends (share_state_table q) (share_state_table (snd (shared_derivation_substitute \<sigma> D nd q)))"
proof -
  let ?T = "share_state_table q" and ?c = "shared_derivation_call nd" and ?B = "shared_derivation_bindings nd"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T (\<sigma> a)"
  have tf: "table_formed ?T" using q by (simp add: share_state_formed_def)
  obtain c' q' where e: "keyed_substitute \<sigma> D ?c q = (c', q')" by (cases "keyed_substitute \<sigma> D ?c q") auto
  have k: "share_state_formed q' \<and> shared_pattern_formed (share_state_table q') c' \<and>
      shared_pattern_project (share_state_table q') c' = finite_pattern_substitute ?\<tau> (shared_pattern_project ?T ?c) \<and>
      table_extends ?T (share_state_table q') \<and> shared_collapsed c'"
    using keyed_substitute_exact[where \<sigma> = \<sigma> and D = D and p = "shared_derivation_call nd", OF out q _ \<sigma>(1)] nd \<sigma>(2) e
    by (simp add: shared_derivation_formed_def)
  let ?T' = "share_state_table q'"
  have b: "\<And>z. z |\<in>| ?B \<Longrightarrow> shared_pattern_formed ?T' (shared_substitute \<sigma> D (snd z)) \<and>
      shared_pattern_project ?T' (shared_substitute \<sigma> D (snd z)) = finite_pattern_substitute ?\<tau> (shared_pattern_project ?T (snd z))"
  proof -
    fix z assume z: "z |\<in>| ?B"
    have f: "shared_pattern_formed ?T (shared_substitute \<sigma> D (snd z))"
      using nd z \<sigma>(1) by (auto simp: shared_derivation_formed_def intro: shared_substitute_formed)
    have p: "shared_pattern_project ?T (shared_substitute \<sigma> D (snd z)) = finite_pattern_substitute ?\<tau> (shared_pattern_project ?T (snd z))"
      using nd z out by (auto simp: shared_derivation_formed_def intro: shared_substitute_project)
    from shared_pattern_extends[OF tf f] k p show "shared_pattern_formed ?T' (shared_substitute \<sigma> D (snd z)) \<and>
      shared_pattern_project ?T' (shared_substitute \<sigma> D (snd z)) = finite_pattern_substitute ?\<tau> (shared_pattern_project ?T (snd z))"
      by simp
  qed
  have bs: "fimage (\<lambda>z. (fst z, shared_pattern_project ?T' (snd z))) (fimage (\<lambda>z. (fst z, shared_substitute \<sigma> D (snd z))) ?B) =
      fimage (\<lambda>(a,x). (a, finite_pattern_substitute ?\<tau> x)) (fimage (\<lambda>z. (fst z, shared_pattern_project ?T (snd z))) ?B)"
    using b by (simp add: fimage_fimage) (intro fimage_cong_on, simp)
  have r: "shared_derivation_substitute \<sigma> D nd q = (Shared_Derivation (shared_derivation_position nd) (shared_derivation_site nd)
      (shared_derivation_clause nd) (shared_derivation_schema nd) c' (fimage (\<lambda>z. (fst z, shared_substitute \<sigma> D (snd z))) ?B), q')"
    using e by (simp add: shared_derivation_substitute_def)
  show ?thesis unfolding r using k b bs
    by (cases nd) (auto simp: shared_derivation_formed_def shared_derivation_project_def)
qed

section \<open>The shared state\<close>

text \<open>
  The shared state holds one goal and one node by position, in the order of positions, each with its caches: a goal
  its count of alternatives (its variables are its patterns' caches), a node its variables. It keeps F2b1's indexes
  over them: the holder index from the position part of a variable to the positions holding or having held a variable
  there (a superset index: an entry is never removed), the count of goal positions at or under each position, the
  construction's kept failures, and the positions of the ground calls of goals and of nodes, keyed by the call's
  reference, a number. Beside the sharing state it holds an index of the table by position, equal to the table, so a
  reference is read without walking the list. It is formed when these are what they keep; its projection to R3's state
  decodes every entry and forgets the caches and the indexes.
\<close>

subsection \<open>Entries\<close>

datatype ('a,'s,'d,'c) shared_goal_entry = Shared_Goal_Entry
  (shared_entry_goal: "('a,'s,'d,'c) shared_goal") (shared_entry_alternatives: nat)

datatype ('a,'s,'d,'c) shared_node_entry = Shared_Node_Entry
  (shared_entry_node: "('a,'s,'d,'c) shared_derivation") (shared_entry_variables: "('s,'a) resolution_variable fset")

definition enter_goal :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> shape list \<Rightarrow> ('a,'s,'d,'c) shared_goal \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry" where
  "enter_goal P T g = Shared_Goal_Entry g (finite_goal_alternatives P (shared_goal_project T g))"

definition enter_node :: "('a,'s,'d,'c) shared_derivation \<Rightarrow> ('a,'s,'d,'c) shared_node_entry" where
  "enter_node nd = Shared_Node_Entry nd (shared_derivation_variables nd)"

definition goal_entry_formed :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> shape list \<Rightarrow> 's list \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> bool" where
  "goal_entry_formed P T q h \<longleftrightarrow> shared_goal_formed T (shared_entry_goal h) \<and> shared_goal_position (shared_entry_goal h) = q \<and>
    shared_entry_alternatives h = finite_goal_alternatives P (shared_goal_project T (shared_entry_goal h))"

definition node_entry_formed :: "shape list \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow> bool" where
  "node_entry_formed T q hn \<longleftrightarrow> shared_derivation_formed T (shared_entry_node hn) \<and>
    shared_derivation_position (shared_entry_node hn) = q \<and> shared_entry_variables hn = shared_derivation_variables (shared_entry_node hn)"

lemma enter_goal_formed:
  "shared_goal_formed T g \<Longrightarrow> shared_goal_position g = q \<Longrightarrow> goal_entry_formed P T q (enter_goal P T g)"
  by (simp add: goal_entry_formed_def enter_goal_def)

lemma enter_node_formed:
  "shared_derivation_formed T nd \<Longrightarrow> shared_derivation_position nd = q \<Longrightarrow> node_entry_formed T q (enter_node nd)"
  by (simp add: node_entry_formed_def enter_node_def)

lemma enter_goal_fields [simp]: "shared_entry_goal (enter_goal P T g) = g"
  by (simp add: enter_goal_def)

lemma enter_node_fields [simp]: "shared_entry_node (enter_node nd) = nd"
  by (simp add: enter_node_def)

lemma goal_entry_extends:
  assumes tf: "table_formed T" and h: "goal_entry_formed P T q h" and ext: "table_extends T T'"
  shows "goal_entry_formed P T' q h \<and> shared_goal_project T' (shared_entry_goal h) = shared_goal_project T (shared_entry_goal h)"
proof -
  have "shared_goal_formed T (shared_entry_goal h)" using h by (simp add: goal_entry_formed_def)
  from shared_goal_extends[OF tf this ext] h show ?thesis by (simp add: goal_entry_formed_def)
qed

lemma node_entry_extends:
  assumes tf: "table_formed T" and hn: "node_entry_formed T q hn" and ext: "table_extends T T'"
  shows "node_entry_formed T' q hn \<and>
    shared_derivation_project T' (shared_entry_node hn) = shared_derivation_project T (shared_entry_node hn)"
proof -
  have "shared_derivation_formed T (shared_entry_node hn)" using hn by (simp add: node_entry_formed_def)
  note e = shared_derivation_extends[OF tf this ext]
  show ?thesis using e hn by (simp add: node_entry_formed_def)
qed

lemma goal_entry_variables:
  "goal_entry_formed P T q h \<Longrightarrow>
    shared_goal_variables (shared_entry_goal h) = resolution_goal_variables (shared_goal_project T (shared_entry_goal h))"
  by (simp add: goal_entry_formed_def shared_goal_variables_project)

lemma node_entry_variables:
  "node_entry_formed T q hn \<Longrightarrow>
    shared_entry_variables hn = resolution_node_variables (shared_derivation_project T (shared_entry_node hn))"
  by (simp add: node_entry_formed_def shared_derivation_variables_project)

subsection \<open>Ground calls keyed by their references\<close>

text \<open>A call pattern is collapsed, so a ground call is one reference: its key in the index of ground calls.\<close>

fun shared_call_refs :: "'v shared_pattern \<Rightarrow> nat fset" where
  "shared_call_refs (Shared_Ground i) = {|i|}"
| "shared_call_refs (Shared_Variable a) = {||}"
| "shared_call_refs (Shared_Node A p r) = {||}"

fun shared_goal_call_refs :: "('a,'s,'d,'c) shared_goal \<Rightarrow> nat fset" where
  "shared_goal_call_refs (Shared_Call_Goal q r d p) = shared_call_refs p"
| "shared_goal_call_refs (Shared_Material_Goal q r M) = {||}"

lemma shared_call_refs_formed:
  "shared_pattern_formed T p \<Longrightarrow> i |\<in>| shared_call_refs p \<Longrightarrow> i < length T"
  by (cases p) simp_all

lemma shared_goal_call_refs_formed:
  "shared_goal_formed T g \<Longrightarrow> i |\<in>| shared_goal_call_refs g \<Longrightarrow> i < length T"
  by (cases g) (auto intro: shared_call_refs_formed)

subsection \<open>The table read by position\<close>

text \<open>
  The table is kept reversed in the sharing state. Beside it the state holds a tree from each position of the table to
  the shape there, extended by the positions a step appends: their shapes stand at the front of the reversed table.
  Every position reads there what the table holds (@{text position_index_formed}), and the positions a formed table held
  before an extension read the same shapes after it.
\<close>

definition position_index_formed :: "share_state \<Rightarrow> (nat, shape) rbt \<Rightarrow> bool" where
  "position_index_formed x t \<longleftrightarrow> (\<forall>i. RBT.lookup t i = value_reference_read (share_state_table x) i)"

definition position_index_extend :: "share_state \<Rightarrow> share_state \<Rightarrow> (nat, shape) rbt \<Rightarrow> (nat, shape) rbt" where
  "position_index_extend x x' t = fold (\<lambda>i u. RBT.insert i (snd (snd x') ! (fst (snd x') - Suc i)) u)
    [fst (snd x)..<fst (snd x')] t"

lemma lookup_fold_insert:
  "RBT.lookup (fold (\<lambda>i u. RBT.insert i (f i) u) xs t) j = (if j \<in> set xs then Some (f j) else RBT.lookup t j)"
  by (induction xs arbitrary: t) auto

lemma table_extends_length:
  assumes tf: "table_formed T" and ext: "table_extends T T'"
  shows "length T \<le> length T'"
proof (cases "length T")
  case (Suc n)
  obtain t where "reference_term T n = Some t" using table_formed_decodes[OF tf] Suc by auto
  then have "reference_term T' n = Some t" using ext by (simp add: table_extends_def)
  then show ?thesis using Suc reference_term_bound[of T' n t] by simp
qed simp

lemma extends_read:
  assumes tf: "table_formed T" and tf': "table_formed T'" and ext: "table_extends T T'" and i: "i < length T"
  shows "value_reference_read T' i = value_reference_read T i"
proof -
  obtain u where u: "reference_term T i = Some u" using table_formed_decodes[OF tf i] by auto
  have u': "reference_term T' i = Some u" using ext u by (simp add: table_extends_def)
  from u show ?thesis
  proof (cases rule: reference_term_cases)
    case (leaf l)
    have "reference_term T' i = Some (leaf_term l)" using u' leaf(2) by simp
    then have "value_reference_read T' i = Some (Leaf_Shape l)" by (rule reference_factor_leaf_read)
    with leaf(1) show ?thesis by simp
  next
    case (pair j k x y)
    obtain j' k' where r': "value_reference_read T' i = Some (Pair_Shape j' k')"
      and x': "reference_term T' j' = Some x" and y': "reference_term T' k' = Some y"
      using u'
    proof (cases rule: reference_term_cases)
      case (leaf l)
      then show ?thesis using pair(6) by (cases l) simp_all
    next
      case (pair j'' k'' x'' y'')
      then show ?thesis using \<open>u = Finite_Pair x y\<close> by (auto intro: that)
    qed
    have "reference_term T' j = Some x" "reference_term T' k = Some y"
      using ext pair(4,5) by (simp_all add: table_extends_def)
    then have "j' = j" "k' = k" using reference_term_injective[OF tf'] x' y' by blast+
    with r' pair(1) show ?thesis by simp
  qed
qed

lemma position_index_extend:
  assumes x: "share_state_formed x" and x': "share_state_formed x'"
    and ext: "table_extends (share_state_table x) (share_state_table x')" and t: "position_index_formed x t"
  shows "position_index_formed x' (position_index_extend x x' t)"
  unfolding position_index_formed_def
proof
  fix j
  let ?T = "share_state_table x" and ?T' = "share_state_table x'"
  have n: "fst (snd x) = length ?T" using x
    by (cases x) (simp add: share_state_formed_def keyed_state_represents_def keyed_reference_state_def share_state_table_def)
  have n': "fst (snd x') = length ?T'" and R': "snd (snd x') = rev ?T'" using x'
    by (cases x', simp add: share_state_formed_def keyed_state_represents_def keyed_reference_state_def share_state_table_def)+
  have tf: "table_formed ?T" and tf': "table_formed ?T'" using x x' by (simp_all add: share_state_formed_def)
  have look: "RBT.lookup (position_index_extend x x' t) j =
      (if length ?T \<le> j \<and> j < length ?T' then Some (?T' ! j) else RBT.lookup t j)"
  proof -
    have "RBT.lookup (position_index_extend x x' t) j = (if j \<in> set [fst (snd x)..<fst (snd x')]
        then Some (snd (snd x') ! (fst (snd x') - Suc j)) else RBT.lookup t j)"
      by (simp add: position_index_extend_def lookup_fold_insert)
    moreover have "j < length ?T' \<Longrightarrow> snd (snd x') ! (fst (snd x') - Suc j) = ?T' ! j"
      using R' n' by (simp add: rev_nth)
    ultimately show ?thesis using n n' by auto
  qed
  have old: "RBT.lookup t j = value_reference_read ?T j" using t by (simp add: position_index_formed_def)
  show "RBT.lookup (position_index_extend x x' t) j = value_reference_read ?T' j"
  proof (cases "j < length ?T")
    case True
    then show ?thesis using look old extends_read[OF tf tf' ext True] by simp
  next
    case False
    then show ?thesis using look old by (auto simp: value_reference_read_def)
  qed
qed

subsection \<open>The state, its projection and its formation\<close>

record (overloaded) ('a,'s::linorder,'d,'c) shared_state =
  shared_sharing :: share_state
  shared_positions :: "(nat, shape) rbt"
  shared_goals :: "('s list, ('a,'s,'d,'c) shared_goal_entry) rbt"
  shared_nodes :: "('s list, ('a,'s,'d,'c) shared_node_entry) rbt"
  shared_witnesses :: "(('s,'a) resolution_variable \<times> finite_factor_term) fset"
  shared_holders :: "('s list, 's list fset) rbt"
  shared_open :: "('s list, nat) rbt"
  shared_goal_calls :: "(nat, 's list fset) rbt"
  shared_node_calls :: "(nat, 's list fset) rbt"
  shared_unconstructed :: "('s list, 'a fset) rbt"

abbreviation shared_state_table :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> shape list" where
  "shared_state_table s \<equiv> share_state_table (shared_sharing s)"

definition tree_values :: "('k::linorder, 'v) rbt \<Rightarrow> 'v fset" where
  "tree_values t = fset_of_list (map snd (RBT.entries t))"

lemma tree_values_member: "v |\<in>| tree_values t \<longleftrightarrow> (\<exists>k. RBT.lookup t k = Some v)"
  by (force simp: tree_values_def fset_of_list_elem RBT.lookup_in_tree)

lemma fimage_tree_values_member:
  "x |\<in>| fimage f (tree_values t) \<longleftrightarrow> (\<exists>k v. RBT.lookup t k = Some v \<and> f v = x)"
proof
  assume "x |\<in>| fimage f (tree_values t)"
  then obtain v where v: "v |\<in>| tree_values t" "x = f v" by blast
  then obtain k where "RBT.lookup t k = Some v" by (auto simp: tree_values_member)
  with v show "\<exists>k v. RBT.lookup t k = Some v \<and> f v = x" by blast
next
  assume "\<exists>k v. RBT.lookup t k = Some v \<and> f v = x"
  then obtain k v where kv: "RBT.lookup t k = Some v" "f v = x" by blast
  then have "v |\<in>| tree_values t" by (auto simp: tree_values_member)
  with kv(2) show "x |\<in>| fimage f (tree_values t)" by blast
qed

lemma tree_values_empty [simp]: "tree_values RBT.empty = {||}"
  by (rule fset_eqI) (simp add: tree_values_member)

lemma tree_values_image:
  assumes same: "\<And>p. map_option f (RBT.lookup t p) = map_option g (RBT.lookup t' p)"
  shows "fimage f (tree_values t) = fimage g (tree_values t')"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| fimage f (tree_values t) \<longleftrightarrow> x |\<in>| fimage g (tree_values t')"
    unfolding fimage_tree_values_member
  proof
    assume "\<exists>k v. RBT.lookup t k = Some v \<and> f v = x"
    then obtain k v where kv: "RBT.lookup t k = Some v" "f v = x" by blast
    from same[of k] kv obtain w where "RBT.lookup t' k = Some w" "g w = x" by (cases "RBT.lookup t' k") auto
    then show "\<exists>k v. RBT.lookup t' k = Some v \<and> g v = x" by blast
  next
    assume "\<exists>k v. RBT.lookup t' k = Some v \<and> g v = x"
    then obtain k v where kv: "RBT.lookup t' k = Some v" "g v = x" by blast
    from same[of k] kv obtain w where "RBT.lookup t k = Some w" "f w = x" by (cases "RBT.lookup t k") auto
    then show "\<exists>k v. RBT.lookup t k = Some v \<and> f v = x" by blast
  qed
qed

lemma put_lookup_exists:
  "(\<exists>p v. (if p = q then x else RBT.lookup t p) = Some v \<and> f v = g) \<longleftrightarrow>
    ((\<exists>v. x = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g))"
proof
  assume "\<exists>p v. (if p = q then x else RBT.lookup t p) = Some v \<and> f v = g"
  then obtain p v where pv: "(if p = q then x else RBT.lookup t p) = Some v" "f v = g" by blast
  then show "(\<exists>v. x = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g)"
    by (cases "p = q") auto
next
  assume "(\<exists>v. x = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g)"
  then show "\<exists>p v. (if p = q then x else RBT.lookup t p) = Some v \<and> f v = g"
  proof
    assume "\<exists>v. x = Some v \<and> f v = g"
    then show ?thesis by (intro exI[of _ q]) simp
  next
    assume "\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g"
    then obtain p v where "p \<noteq> q" "RBT.lookup t p = Some v" "f v = g" by blast
    then show ?thesis by (intro exI[of _ p] exI[of _ v]) simp
  qed
qed

definition shared_state_project :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "shared_state_project s = Resolution_State
    (fimage (\<lambda>h. shared_goal_project (shared_state_table s) (shared_entry_goal h)) (tree_values (shared_goals s)))
    (fimage (\<lambda>hn. shared_derivation_project (shared_state_table s) (shared_entry_node hn)) (tree_values (shared_nodes s)))
    (shared_witnesses s)"

lemma shared_state_project_fields:
  "resolution_pending (shared_state_project s) =
    fimage (\<lambda>h. shared_goal_project (shared_state_table s) (shared_entry_goal h)) (tree_values (shared_goals s))"
  "resolution_nodes (shared_state_project s) =
    fimage (\<lambda>hn. shared_derivation_project (shared_state_table s) (shared_entry_node hn)) (tree_values (shared_nodes s))"
  "resolution_witnesses (shared_state_project s) = shared_witnesses s"
  by (simp_all add: shared_state_project_def)

lemma shared_state_project_member:
  "g |\<in>| resolution_pending (shared_state_project s) \<longleftrightarrow>
    (\<exists>q h. RBT.lookup (shared_goals s) q = Some h \<and> shared_goal_project (shared_state_table s) (shared_entry_goal h) = g)"
  "nd |\<in>| resolution_nodes (shared_state_project s) \<longleftrightarrow>
    (\<exists>q hn. RBT.lookup (shared_nodes s) q = Some hn \<and> shared_derivation_project (shared_state_table s) (shared_entry_node hn) = nd)"
  by (simp_all only: shared_state_project_def resolution_state.sel fimage_tree_values_member)

lemma keep_lookup_exists:
  "((\<exists>v. RBT.lookup t q = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g)) \<longleftrightarrow>
    (\<exists>p v. RBT.lookup t p = Some v \<and> f v = g)"
proof
  assume "(\<exists>v. RBT.lookup t q = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g)"
  then show "\<exists>p v. RBT.lookup t p = Some v \<and> f v = g" by blast
next
  assume "\<exists>p v. RBT.lookup t p = Some v \<and> f v = g"
  then obtain p v where pv: "RBT.lookup t p = Some v" "f v = g" by blast
  show "(\<exists>v. RBT.lookup t q = Some v \<and> f v = g) \<or> (\<exists>p v. p \<noteq> q \<and> RBT.lookup t p = Some v \<and> f v = g)"
  proof (cases "p = q")
    case True
    with pv show ?thesis by blast
  next
    case False
    with pv show ?thesis by blast
  qed
qed

definition shared_recorded_at :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> 's list \<Rightarrow> bool" where
  "shared_recorded_at s q \<longleftrightarrow>
    (\<forall>h x. RBT.lookup (shared_goals s) q = Some h \<longrightarrow> x |\<in>| shared_goal_variables (shared_entry_goal h) \<longrightarrow>
      q |\<in>| tree_bucket (shared_holders s) (fst (fst x))) \<and>
    (\<forall>hn x. RBT.lookup (shared_nodes s) q = Some hn \<longrightarrow> x |\<in>| shared_entry_variables hn \<longrightarrow>
      q |\<in>| tree_bucket (shared_holders s) (fst (fst x))) \<and>
    (\<forall>h i. RBT.lookup (shared_goals s) q = Some h \<longrightarrow> i |\<in>| shared_goal_call_refs (shared_entry_goal h) \<longrightarrow>
      q |\<in>| tree_bucket (shared_goal_calls s) i) \<and>
    (\<forall>hn i. RBT.lookup (shared_nodes s) q = Some hn \<longrightarrow> i |\<in>| shared_call_refs (shared_derivation_call (shared_entry_node hn)) \<longrightarrow>
      q |\<in>| tree_bucket (shared_node_calls s) i)"

definition shared_state_formed :: "('a,'s,'d,'c) finite_witness_construction \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> bool" where
  "shared_state_formed \<kappa> P s \<longleftrightarrow> share_state_formed (shared_sharing s) \<and>
    position_index_formed (shared_sharing s) (shared_positions s) \<and>
    (\<forall>q h. RBT.lookup (shared_goals s) q = Some h \<longrightarrow> goal_entry_formed P (shared_state_table s) q h) \<and>
    (\<forall>q hn. RBT.lookup (shared_nodes s) q = Some hn \<longrightarrow> node_entry_formed (shared_state_table s) q hn) \<and>
    (\<forall>i x. x |\<in>| tree_bucket (shared_goal_calls s) i \<longrightarrow> i < length (shared_state_table s)) \<and>
    (\<forall>i x. x |\<in>| tree_bucket (shared_node_calls s) i \<longrightarrow> i < length (shared_state_table s)) \<and>
    (\<forall>q. shared_recorded_at s q) \<and>
    (\<forall>p. tree_count (shared_open s) p = card (tree_keys_under (shared_goals s) p)) \<and>
    (\<forall>q a hn. a |\<in>| tree_bucket (shared_unconstructed s) q \<longrightarrow> RBT.lookup (shared_nodes s) q = Some hn \<longrightarrow>
      finite_registered_value \<kappa> P (shared_derivation_project (shared_state_table s) (shared_entry_node hn)) a = None)"

lemma shared_entries_formed:
  assumes "shared_state_formed \<kappa> P s"
  shows "RBT.lookup (shared_goals s) q = Some h \<Longrightarrow> goal_entry_formed P (shared_state_table s) q h"
    and "RBT.lookup (shared_nodes s) q = Some hn \<Longrightarrow> node_entry_formed (shared_state_table s) q hn"
    and "share_state_formed (shared_sharing s)"
    and "table_formed (shared_state_table s)"
  using assms by (simp_all add: shared_state_formed_def share_state_formed_def)

section \<open>Replacing, placing and removing the entries at a position\<close>

text \<open>
  Every change of the entries is one operation, as in F2b1: the goal and the node at one position are replaced, the
  count of goal positions is adjusted along the position's prefixes where a goal appears or disappears there, and the
  new entries' variables and ground call references are recorded. It keeps the formation.
\<close>

definition option_fset :: "'a option \<Rightarrow> 'a fset" where
  "option_fset x = (case x of None \<Rightarrow> {||} | Some y \<Rightarrow> {|y|})"

lemma option_fset_simps [simp]: "option_fset None = {||}" "option_fset (Some y) = {|y|}"
  by (simp_all add: option_fset_def)

definition tree_option_put :: "('k::linorder,'v) rbt \<Rightarrow> 'k \<Rightarrow> 'v option \<Rightarrow> ('k,'v) rbt" where
  "tree_option_put t q x = (case x of None \<Rightarrow> RBT.delete q t | Some y \<Rightarrow> RBT.insert q y t)"

lemma tree_option_put_lookup [simp]:
  "RBT.lookup (tree_option_put t q x) p = (if p = q then x else RBT.lookup t p)"
  by (cases x) (simp_all add: tree_option_put_def)

definition presence_count_put :: "('s::linorder list, 'v) rbt \<Rightarrow> ('s list, nat) rbt \<Rightarrow> 's list \<Rightarrow> bool \<Rightarrow>
    ('s list, nat) rbt" where
  "presence_count_put t c q b = (if (RBT.lookup t q = None) = (\<not> b) then c
    else tree_count_adjust (if b then Suc else (\<lambda>n. n - 1)) (position_prefixes q) c)"

lemma presence_count_put_formed:
  assumes counts: "\<And>p. tree_count c p = card (tree_keys_under t p)"
  shows "tree_count (presence_count_put t c q (x \<noteq> None)) p = card (tree_keys_under (tree_option_put t q x) p)"
proof -
  let ?t0 = "RBT.map (\<lambda>k v. {|v|}) t"
  have keys: "\<And>p. tree_keys_under ?t0 p = tree_keys_under t p" by (simp add: tree_keys_under_def)
  have c0: "\<And>p. tree_count c p = card (tree_keys_under ?t0 p)" using counts keys by simp
  have eq: "presence_count_put t c q (x \<noteq> None) = tree_bucket_count_put ?t0 c q (option_fset x)"
    by (cases x) (simp_all add: presence_count_put_def tree_bucket_count_put_def)
  have k2: "tree_keys_under (tree_bucket_put ?t0 q (option_fset x)) p = tree_keys_under (tree_option_put t q x) p"
    by (cases x) (auto simp: tree_keys_under_def tree_bucket_put_def)
  show ?thesis using tree_bucket_count_put[where t = ?t0 and c = c, OF c0] eq k2 by simp
qed

definition shared_replace :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry option \<Rightarrow>
    ('a,'s,'d,'c) shared_node_entry option \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_replace q go no s = s\<lparr>shared_goals := tree_option_put (shared_goals s) q go,
    shared_nodes := tree_option_put (shared_nodes s) q no,
    shared_holders := tree_add q (variable_positions
      (case_option {||} (\<lambda>h. shared_goal_variables (shared_entry_goal h)) go |\<union>| case_option {||} shared_entry_variables no))
      (shared_holders s),
    shared_open := presence_count_put (shared_goals s) (shared_open s) q (go \<noteq> None),
    shared_goal_calls := tree_add q (case_option {||} (\<lambda>h. shared_goal_call_refs (shared_entry_goal h)) go) (shared_goal_calls s),
    shared_node_calls := tree_add q (case_option {||} (\<lambda>hn. shared_call_refs (shared_derivation_call (shared_entry_node hn))) no)
      (shared_node_calls s),
    shared_unconstructed := RBT.delete q (shared_unconstructed s)\<rparr>"

lemma shared_replace_fields [simp]:
  "shared_sharing (shared_replace q go no s) = shared_sharing s"
  "shared_positions (shared_replace q go no s) = shared_positions s"
  "shared_witnesses (shared_replace q go no s) = shared_witnesses s"
  "RBT.lookup (shared_goals (shared_replace q go no s)) p = (if p = q then go else RBT.lookup (shared_goals s) p)"
  "RBT.lookup (shared_nodes (shared_replace q go no s)) p = (if p = q then no else RBT.lookup (shared_nodes s) p)"
  by (simp_all add: shared_replace_def)

lemma shared_replace_member:
  "g |\<in>| resolution_pending (shared_state_project (shared_replace q go no s)) \<longleftrightarrow>
    (\<exists>h. go = Some h \<and> shared_goal_project (shared_state_table s) (shared_entry_goal h) = g) \<or>
    (\<exists>p h. p \<noteq> q \<and> RBT.lookup (shared_goals s) p = Some h \<and> shared_goal_project (shared_state_table s) (shared_entry_goal h) = g)"
  "nd |\<in>| resolution_nodes (shared_state_project (shared_replace q go no s)) \<longleftrightarrow>
    (\<exists>hn. no = Some hn \<and> shared_derivation_project (shared_state_table s) (shared_entry_node hn) = nd) \<or>
    (\<exists>p hn. p \<noteq> q \<and> RBT.lookup (shared_nodes s) p = Some hn \<and> shared_derivation_project (shared_state_table s) (shared_entry_node hn) = nd)"
  by (simp_all only: shared_state_project_member shared_replace_fields put_lookup_exists)

theorem shared_replace_formed:
  assumes s: "shared_state_formed \<kappa> P s"
    and go: "\<And>h. go = Some h \<Longrightarrow> goal_entry_formed P (shared_state_table s) q h"
    and no: "\<And>hn. no = Some hn \<Longrightarrow> node_entry_formed (shared_state_table s) q hn"
  shows "shared_state_formed \<kappa> P (shared_replace q go no s)"
proof -
  let ?T = "shared_state_table s" and ?s' = "shared_replace q go no s"
  have rec: "shared_recorded_at ?s' p" for p
  proof (cases "p = q")
    case True
    then show ?thesis by (cases go; cases no) (auto simp: shared_recorded_at_def shared_replace_def variable_positions_member)
  next
    case False
    have "shared_recorded_at s p" using s by (simp add: shared_state_formed_def)
    with False show ?thesis by (auto simp: shared_recorded_at_def shared_replace_def)
  qed
  have gcalls: "i < length ?T" if "x |\<in>| tree_bucket (shared_goal_calls ?s') i" for i x
  proof (cases "i |\<in>| case_option {||} (\<lambda>h. shared_goal_call_refs (shared_entry_goal h)) go")
    case True
    then obtain h where "go = Some h" "i |\<in>| shared_goal_call_refs (shared_entry_goal h)" by (cases go) auto
    then show ?thesis using go shared_goal_call_refs_formed[of ?T] by (auto simp: goal_entry_formed_def)
  next
    case False
    then have "x |\<in>| tree_bucket (shared_goal_calls s) i" using that by (simp add: shared_replace_def)
    then show ?thesis using s by (auto simp: shared_state_formed_def)
  qed
  have ncalls: "i < length ?T" if "x |\<in>| tree_bucket (shared_node_calls ?s') i" for i x
  proof (cases "i |\<in>| case_option {||} (\<lambda>hn. shared_call_refs (shared_derivation_call (shared_entry_node hn))) no")
    case True
    then obtain hn where "no = Some hn" "i |\<in>| shared_call_refs (shared_derivation_call (shared_entry_node hn))" by (cases no) auto
    then show ?thesis using no shared_call_refs_formed[of ?T] by (auto simp: node_entry_formed_def shared_derivation_formed_def)
  next
    case False
    then have "x |\<in>| tree_bucket (shared_node_calls s) i" using that by (simp add: shared_replace_def)
    then show ?thesis using s by (auto simp: shared_state_formed_def)
  qed
  have counts: "tree_count (shared_open ?s') p = card (tree_keys_under (shared_goals ?s') p)" for p
  proof -
    have "\<And>p. tree_count (shared_open s) p = card (tree_keys_under (shared_goals s) p)"
      using s by (simp add: shared_state_formed_def)
    from presence_count_put_formed[OF this, of q go p] show ?thesis by (simp add: shared_replace_def)
  qed
  have unc: "finite_registered_value \<kappa> P (shared_derivation_project ?T (shared_entry_node hn)) a = None"
    if "a |\<in>| tree_bucket (shared_unconstructed ?s') p" "RBT.lookup (shared_nodes ?s') p = Some hn" for p a hn
  proof -
    have "p \<noteq> q" using that(1) by (cases "p = q") (simp_all add: shared_replace_def)
    with that s show ?thesis by (auto simp: shared_replace_def shared_state_formed_def)
  qed
  have gs: "\<And>p h. RBT.lookup (shared_goals ?s') p = Some h \<Longrightarrow> goal_entry_formed P ?T p h"
    using go shared_entries_formed(1)[OF s] by (auto split: if_splits)
  have ns: "\<And>p hn. RBT.lookup (shared_nodes ?s') p = Some hn \<Longrightarrow> node_entry_formed ?T p hn"
    using no shared_entries_formed(2)[OF s] by (auto split: if_splits)
  have c1: "\<forall>i x. x |\<in>| tree_bucket (shared_goal_calls ?s') i \<longrightarrow> i < length (shared_state_table ?s')"
    using gcalls by simp
  have c2: "\<forall>i x. x |\<in>| tree_bucket (shared_node_calls ?s') i \<longrightarrow> i < length (shared_state_table ?s')"
    using ncalls by simp
  have g1: "\<forall>p h. RBT.lookup (shared_goals ?s') p = Some h \<longrightarrow> goal_entry_formed P (shared_state_table ?s') p h"
    using gs by simp
  have n1: "\<forall>p hn. RBT.lookup (shared_nodes ?s') p = Some hn \<longrightarrow> node_entry_formed (shared_state_table ?s') p hn"
    using ns by simp
  have o1: "\<forall>p. tree_count (shared_open ?s') p = card (tree_keys_under (shared_goals ?s') p)" using counts by simp
  have u1: "\<forall>p a hn. a |\<in>| tree_bucket (shared_unconstructed ?s') p \<longrightarrow> RBT.lookup (shared_nodes ?s') p = Some hn \<longrightarrow>
      finite_registered_value \<kappa> P (shared_derivation_project (shared_state_table ?s') (shared_entry_node hn)) a = None"
    using unc by simp
  have sh: "share_state_formed (shared_sharing ?s')" "position_index_formed (shared_sharing ?s') (shared_positions ?s')"
    using s by (simp_all add: shared_state_formed_def)
  show ?thesis unfolding shared_state_formed_def using sh g1 n1 c1 c2 rec o1 u1 by blast
qed

subsection \<open>Placing a goal or a node and removing a goal\<close>

definition shared_put_goal :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow>
    ('a,'s,'d,'c) shared_state" where
  "shared_put_goal q h s = shared_replace q (Some h) (RBT.lookup (shared_nodes s) q) s"

definition shared_put_node :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow>
    ('a,'s,'d,'c) shared_state" where
  "shared_put_node q hn s = shared_replace q (RBT.lookup (shared_goals s) q) (Some hn) s"

definition shared_remove_goal :: "'s::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_remove_goal q s = shared_replace q None (RBT.lookup (shared_nodes s) q) s"

theorem shared_put_goal:
  assumes s: "shared_state_formed \<kappa> P s" and h: "goal_entry_formed P (shared_state_table s) q h"
    and free: "RBT.lookup (shared_goals s) q = None"
  shows "shared_state_formed \<kappa> P (shared_put_goal q h s)"
    and "resolution_pending (shared_state_project (shared_put_goal q h s)) =
      resolution_pending (shared_state_project s) |\<union>| {|shared_goal_project (shared_state_table s) (shared_entry_goal h)|}"
    and "resolution_nodes (shared_state_project (shared_put_goal q h s)) = resolution_nodes (shared_state_project s)"
    and "resolution_witnesses (shared_state_project (shared_put_goal q h s)) = resolution_witnesses (shared_state_project s)"
proof -
  let ?T = "shared_state_table s" and ?s' = "shared_put_goal q h s"
  show "shared_state_formed \<kappa> P ?s'"
    unfolding shared_put_goal_def using s h shared_entries_formed(2)[OF s]
    by (intro shared_replace_formed) simp_all
  have out: "\<And>p v. RBT.lookup (shared_goals s) p = Some v \<Longrightarrow> p \<noteq> q" using free by auto
  show "resolution_pending (shared_state_project ?s') =
      resolution_pending (shared_state_project s) |\<union>| {|shared_goal_project ?T (shared_entry_goal h)|}"
  proof (rule fset_eqI)
    fix g
    have m: "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>h'. Some h = Some h' \<and> shared_goal_project ?T (shared_entry_goal h') = g) \<or>
        (\<exists>p h'. p \<noteq> q \<and> RBT.lookup (shared_goals s) p = Some h' \<and> shared_goal_project ?T (shared_entry_goal h') = g)"
      unfolding shared_put_goal_def by (rule shared_replace_member(1))
    have o: "g |\<in>| resolution_pending (shared_state_project s) \<longleftrightarrow>
        (\<exists>p h'. RBT.lookup (shared_goals s) p = Some h' \<and> shared_goal_project ?T (shared_entry_goal h') = g)"
      by (rule shared_state_project_member(1))
    show "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow>
        g |\<in>| resolution_pending (shared_state_project s) |\<union>| {|shared_goal_project ?T (shared_entry_goal h)|}"
      using m o out by blast
  qed
  show "resolution_nodes (shared_state_project ?s') = resolution_nodes (shared_state_project s)"
  proof (rule fset_eqI)
    fix nd
    have m: "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>hn. RBT.lookup (shared_nodes s) q = Some hn \<and> shared_derivation_project ?T (shared_entry_node hn) = nd) \<or>
        (\<exists>p hn. p \<noteq> q \<and> RBT.lookup (shared_nodes s) p = Some hn \<and> shared_derivation_project ?T (shared_entry_node hn) = nd)"
      unfolding shared_put_goal_def by (rule shared_replace_member(2))
    show "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow> nd |\<in>| resolution_nodes (shared_state_project s)"
      unfolding m keep_lookup_exists by (rule shared_state_project_member(2)[symmetric])
  qed
  show "resolution_witnesses (shared_state_project ?s') = resolution_witnesses (shared_state_project s)"
    by (simp add: shared_state_project_def shared_put_goal_def)
qed

theorem shared_put_node:
  assumes s: "shared_state_formed \<kappa> P s" and hn: "node_entry_formed (shared_state_table s) q hn"
    and free: "RBT.lookup (shared_nodes s) q = None"
  shows "shared_state_formed \<kappa> P (shared_put_node q hn s)"
    and "resolution_pending (shared_state_project (shared_put_node q hn s)) = resolution_pending (shared_state_project s)"
    and "resolution_nodes (shared_state_project (shared_put_node q hn s)) =
      resolution_nodes (shared_state_project s) |\<union>| {|shared_derivation_project (shared_state_table s) (shared_entry_node hn)|}"
    and "resolution_witnesses (shared_state_project (shared_put_node q hn s)) = resolution_witnesses (shared_state_project s)"
proof -
  let ?T = "shared_state_table s" and ?s' = "shared_put_node q hn s"
  show "shared_state_formed \<kappa> P ?s'"
    unfolding shared_put_node_def using s hn shared_entries_formed(1)[OF s]
    by (intro shared_replace_formed) simp_all
  have out: "\<And>p v. RBT.lookup (shared_nodes s) p = Some v \<Longrightarrow> p \<noteq> q" using free by auto
  show "resolution_pending (shared_state_project ?s') = resolution_pending (shared_state_project s)"
  proof (rule fset_eqI)
    fix g
    have m: "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>h. RBT.lookup (shared_goals s) q = Some h \<and> shared_goal_project ?T (shared_entry_goal h) = g) \<or>
        (\<exists>p h. p \<noteq> q \<and> RBT.lookup (shared_goals s) p = Some h \<and> shared_goal_project ?T (shared_entry_goal h) = g)"
      unfolding shared_put_node_def by (rule shared_replace_member(1))
    show "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow> g |\<in>| resolution_pending (shared_state_project s)"
      unfolding m keep_lookup_exists by (rule shared_state_project_member(1)[symmetric])
  qed
  show "resolution_nodes (shared_state_project ?s') =
      resolution_nodes (shared_state_project s) |\<union>| {|shared_derivation_project ?T (shared_entry_node hn)|}"
  proof (rule fset_eqI)
    fix nd
    have m: "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>hn'. Some hn = Some hn' \<and> shared_derivation_project ?T (shared_entry_node hn') = nd) \<or>
        (\<exists>p hn'. p \<noteq> q \<and> RBT.lookup (shared_nodes s) p = Some hn' \<and> shared_derivation_project ?T (shared_entry_node hn') = nd)"
      unfolding shared_put_node_def by (rule shared_replace_member(2))
    have o: "nd |\<in>| resolution_nodes (shared_state_project s) \<longleftrightarrow>
        (\<exists>p hn'. RBT.lookup (shared_nodes s) p = Some hn' \<and> shared_derivation_project ?T (shared_entry_node hn') = nd)"
      by (rule shared_state_project_member(2))
    show "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow>
        nd |\<in>| resolution_nodes (shared_state_project s) |\<union>| {|shared_derivation_project ?T (shared_entry_node hn)|}"
      using m o out by blast
  qed
  show "resolution_witnesses (shared_state_project ?s') = resolution_witnesses (shared_state_project s)"
    by (simp add: shared_state_project_def shared_put_node_def)
qed

theorem shared_remove_goal:
  assumes s: "shared_state_formed \<kappa> P s" and at: "RBT.lookup (shared_goals s) q = Some h"
  shows "shared_state_formed \<kappa> P (shared_remove_goal q s)"
    and "resolution_pending (shared_state_project (shared_remove_goal q s)) =
      resolution_pending (shared_state_project s) |-| {|shared_goal_project (shared_state_table s) (shared_entry_goal h)|}"
    and "resolution_nodes (shared_state_project (shared_remove_goal q s)) = resolution_nodes (shared_state_project s)"
    and "resolution_witnesses (shared_state_project (shared_remove_goal q s)) = resolution_witnesses (shared_state_project s)"
proof -
  let ?T = "shared_state_table s" and ?s' = "shared_remove_goal q s"
  let ?f = "\<lambda>h'. shared_goal_project ?T (shared_entry_goal h')"
  show "shared_state_formed \<kappa> P ?s'"
    unfolding shared_remove_goal_def using s shared_entries_formed(2)[OF s]
    by (intro shared_replace_formed) simp_all
  have pos: "\<And>p v. RBT.lookup (shared_goals s) p = Some v \<Longrightarrow> resolution_goal_position (?f v) = p"
    using shared_entries_formed(1)[OF s] by (simp add: goal_entry_formed_def)
  have other: "p = q" if "RBT.lookup (shared_goals s) p = Some v" "?f v = ?f h" for p v
    using pos[OF that(1)] pos[OF at] that(2) by simp
  show "resolution_pending (shared_state_project ?s') = resolution_pending (shared_state_project s) |-| {|?f h|}"
  proof (rule fset_eqI)
    fix g
    have m: "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>h'. None = Some h' \<and> ?f h' = g) \<or> (\<exists>p h'. p \<noteq> q \<and> RBT.lookup (shared_goals s) p = Some h' \<and> ?f h' = g)"
      unfolding shared_remove_goal_def by (rule shared_replace_member(1))
    have o: "g |\<in>| resolution_pending (shared_state_project s) \<longleftrightarrow>
        (\<exists>p h'. RBT.lookup (shared_goals s) p = Some h' \<and> ?f h' = g)"
      by (rule shared_state_project_member(1))
    show "g |\<in>| resolution_pending (shared_state_project ?s') \<longleftrightarrow> g |\<in>| resolution_pending (shared_state_project s) |-| {|?f h|}"
    proof
      assume "g |\<in>| resolution_pending (shared_state_project ?s')"
      then obtain p h' where p: "p \<noteq> q" "RBT.lookup (shared_goals s) p = Some h'" "?f h' = g" using m by blast
      have "g \<noteq> ?f h" using other[OF p(2)] p by auto
      then show "g |\<in>| resolution_pending (shared_state_project s) |-| {|?f h|}" using o p by blast
    next
      assume "g |\<in>| resolution_pending (shared_state_project s) |-| {|?f h|}"
      then have ne: "g \<noteq> ?f h" and g: "g |\<in>| resolution_pending (shared_state_project s)" by auto
      then obtain p h' where p: "RBT.lookup (shared_goals s) p = Some h'" "?f h' = g" using o by blast
      have "p \<noteq> q" using p at ne by auto
      then show "g |\<in>| resolution_pending (shared_state_project ?s')" using m p by blast
    qed
  qed
  show "resolution_nodes (shared_state_project ?s') = resolution_nodes (shared_state_project s)"
  proof (rule fset_eqI)
    fix nd
    have m: "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow>
        (\<exists>hn. RBT.lookup (shared_nodes s) q = Some hn \<and> shared_derivation_project ?T (shared_entry_node hn) = nd) \<or>
        (\<exists>p hn. p \<noteq> q \<and> RBT.lookup (shared_nodes s) p = Some hn \<and> shared_derivation_project ?T (shared_entry_node hn) = nd)"
      unfolding shared_remove_goal_def by (rule shared_replace_member(2))
    show "nd |\<in>| resolution_nodes (shared_state_project ?s') \<longleftrightarrow> nd |\<in>| resolution_nodes (shared_state_project s)"
      unfolding m keep_lookup_exists by (rule shared_state_project_member(2)[symmetric])
  qed
  show "resolution_witnesses (shared_state_project ?s') = resolution_witnesses (shared_state_project s)"
    by (simp add: shared_state_project_def shared_remove_goal_def)
qed

section \<open>Substitution at the holders of the variables it binds\<close>

text \<open>
  A step extends the table: the state takes the extended sharing state and its positional index, every entry keeping
  its formation and its projection. Substitution visits the positions the holder index finds for the position parts of
  the variables it binds, in their order, and at each rebuilds the goal and the node there through the keyed
  constructor, threading the sharing state; an entry none of whose variables it binds stays as it is. Under collapsed
  bindings a collapsed entry stays collapsed. Its projection is R3's substitution of the projection, as F2b1's is.
\<close>

subsection \<open>Extending the table under a formed state\<close>

definition shared_reshare :: "share_state \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_reshare x s = s\<lparr>shared_sharing := x, shared_positions := position_index_extend (shared_sharing s) x (shared_positions s)\<rparr>"

lemma shared_reshare:
  assumes s: "shared_state_formed \<kappa> P s" and x: "share_state_formed x"
    and ext: "table_extends (shared_state_table s) (share_state_table x)"
  shows "shared_state_formed \<kappa> P (shared_reshare x s)"
    and "shared_state_project (shared_reshare x s) = shared_state_project s"
proof -
  let ?T = "shared_state_table s" and ?T' = "share_state_table x" and ?s' = "shared_reshare x s"
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have le: "length ?T \<le> length ?T'" using table_extends_length[OF tf ext] .
  have ge: "goal_entry_formed P ?T' q h \<and> shared_goal_project ?T' (shared_entry_goal h) = shared_goal_project ?T (shared_entry_goal h)"
    if "RBT.lookup (shared_goals s) q = Some h" for q h
    using goal_entry_extends[OF tf shared_entries_formed(1)[OF s that] ext] .
  have ne: "node_entry_formed ?T' q hn \<and>
      shared_derivation_project ?T' (shared_entry_node hn) = shared_derivation_project ?T (shared_entry_node hn)"
    if "RBT.lookup (shared_nodes s) q = Some hn" for q hn
    using node_entry_extends[OF tf shared_entries_formed(2)[OF s that] ext] .
  have pos: "position_index_formed x (shared_positions ?s')"
    using position_index_extend[OF shared_entries_formed(3)[OF s] x ext] s
    by (simp add: shared_reshare_def shared_state_formed_def)
  have rec: "\<forall>q. shared_recorded_at ?s' q" using s by (simp add: shared_reshare_def shared_recorded_at_def shared_state_formed_def)
  have c1: "\<forall>i y. y |\<in>| tree_bucket (shared_goal_calls ?s') i \<longrightarrow> i < length ?T'"
    using s le unfolding shared_state_formed_def shared_reshare_def by (simp, meson less_le_trans)
  have c2: "\<forall>i y. y |\<in>| tree_bucket (shared_node_calls ?s') i \<longrightarrow> i < length ?T'"
    using s le unfolding shared_state_formed_def shared_reshare_def by (simp, meson less_le_trans)
  have g1: "\<forall>q h. RBT.lookup (shared_goals ?s') q = Some h \<longrightarrow> goal_entry_formed P ?T' q h"
    using ge by (simp add: shared_reshare_def)
  have n1: "\<forall>q hn. RBT.lookup (shared_nodes ?s') q = Some hn \<longrightarrow> node_entry_formed ?T' q hn"
    using ne by (simp add: shared_reshare_def)
  have o1: "\<forall>p. tree_count (shared_open ?s') p = card (tree_keys_under (shared_goals ?s') p)"
    using s by (simp add: shared_reshare_def shared_state_formed_def)
  have u1: "\<forall>q a hn. a |\<in>| tree_bucket (shared_unconstructed ?s') q \<longrightarrow> RBT.lookup (shared_nodes ?s') q = Some hn \<longrightarrow>
      finite_registered_value \<kappa> P (shared_derivation_project ?T' (shared_entry_node hn)) a = None"
    using s ne by (simp add: shared_reshare_def shared_state_formed_def)
  have tbl: "shared_state_table ?s' = ?T'" by (simp add: shared_reshare_def)
  show "shared_state_formed \<kappa> P ?s'"
    unfolding shared_state_formed_def tbl using x pos g1 n1 c1 c2 rec o1 u1 by (simp add: shared_reshare_def)
  have gp: "map_option (\<lambda>h. shared_goal_project ?T' (shared_entry_goal h)) (RBT.lookup (shared_goals s) p) =
      map_option (\<lambda>h. shared_goal_project ?T (shared_entry_goal h)) (RBT.lookup (shared_goals s) p)" for p
    using ge by (cases "RBT.lookup (shared_goals s) p") simp_all
  have np: "map_option (\<lambda>hn. shared_derivation_project ?T' (shared_entry_node hn)) (RBT.lookup (shared_nodes s) p) =
      map_option (\<lambda>hn. shared_derivation_project ?T (shared_entry_node hn)) (RBT.lookup (shared_nodes s) p)" for p
    using ne by (cases "RBT.lookup (shared_nodes s) p") simp_all
  show "shared_state_project ?s' = shared_state_project s"
    unfolding shared_state_project_def tbl
    using tree_values_image[OF gp] tree_values_image[OF np] by (simp add: shared_reshare_def)
qed

subsection \<open>Substituting one goal entry and one node entry\<close>

definition shared_goal_entry_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s,'d,'c) shared_goal_entry \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) shared_goal_entry \<times> share_state" where
  "shared_goal_entry_substitute P \<sigma> D h x = (if shared_goal_variables (shared_entry_goal h) |\<inter>| D = {||} then (h, x)
    else (case shared_goal_substitute \<sigma> D (shared_entry_goal h) x of (g', x') \<Rightarrow> (enter_goal P (share_state_table x') g', x')))"

definition shared_node_entry_substitute ::
    "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s,'d,'c) shared_node_entry \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) shared_node_entry \<times> share_state" where
  "shared_node_entry_substitute \<sigma> D hn x = (if shared_entry_variables hn |\<inter>| D = {||} then (hn, x)
    else (case shared_derivation_substitute \<sigma> D (shared_entry_node hn) x of (n', x') \<Rightarrow> (enter_node n', x')))"

lemma shared_goal_entry_substitute:
  assumes x: "share_state_formed x" and h: "goal_entry_formed P (share_state_table x) q h"
    and \<sigma>f: "\<And>a. shared_pattern_formed (share_state_table x) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "share_state_formed (snd (shared_goal_entry_substitute P \<sigma> D h x)) \<and>
    table_extends (share_state_table x) (share_state_table (snd (shared_goal_entry_substitute P \<sigma> D h x))) \<and>
    goal_entry_formed P (share_state_table (snd (shared_goal_entry_substitute P \<sigma> D h x))) q
      (fst (shared_goal_entry_substitute P \<sigma> D h x)) \<and>
    shared_goal_project (share_state_table (snd (shared_goal_entry_substitute P \<sigma> D h x)))
      (shared_entry_goal (fst (shared_goal_entry_substitute P \<sigma> D h x))) =
      resolution_goal_substitute (\<lambda>a. shared_pattern_project (share_state_table x) (\<sigma> a))
        (shared_goal_project (share_state_table x) (shared_entry_goal h))"
proof (cases "shared_goal_variables (shared_entry_goal h) |\<inter>| D = {||}")
  case True
  let ?g = "shared_goal_project (share_state_table x) (shared_entry_goal h)"
  have "resolution_goal_substitute (\<lambda>a. shared_pattern_project (share_state_table x) (\<sigma> a)) ?g = ?g"
  proof (rule resolution_goal_substitute_outside)
    fix y assume "y |\<in>| resolution_goal_variables ?g"
    then have "y |\<in>| shared_goal_variables (shared_entry_goal h)" using goal_entry_variables[OF h] by simp
    with True have "y |\<notin>| D" by auto
    then show "shared_pattern_project (share_state_table x) (\<sigma> y) = Finite_Variable y" using out by simp
  qed
  with True x h show ?thesis by (simp add: shared_goal_entry_substitute_def)
next
  case False
  let ?g = "shared_entry_goal h"
  obtain g' x' where e: "shared_goal_substitute \<sigma> D ?g x = (g', x')" by (cases "shared_goal_substitute \<sigma> D ?g x") auto
  have gf: "shared_goal_formed (share_state_table x) ?g" using h by (simp add: goal_entry_formed_def)
  note k = shared_goal_substitute_exact[where q = x and g = ?g and \<sigma> = \<sigma> and D = D, OF x gf \<sigma>f \<sigma>c out]
  have pos: "shared_goal_position g' = q" using shared_goal_substitute_position[of \<sigma> D ?g x] e h
    by (simp add: goal_entry_formed_def)
  show ?thesis using False e k pos enter_goal_formed[of "share_state_table x'" g' q P]
    by (simp add: shared_goal_entry_substitute_def)
qed

lemma shared_node_entry_substitute:
  assumes x: "share_state_formed x" and hn: "node_entry_formed (share_state_table x) q hn"
    and \<sigma>f: "\<And>a. shared_pattern_formed (share_state_table x) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "share_state_formed (snd (shared_node_entry_substitute \<sigma> D hn x)) \<and>
    table_extends (share_state_table x) (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x))) \<and>
    node_entry_formed (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x))) q
      (fst (shared_node_entry_substitute \<sigma> D hn x)) \<and>
    shared_derivation_project (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x)))
      (shared_entry_node (fst (shared_node_entry_substitute \<sigma> D hn x))) =
      resolution_node_substitute (\<lambda>a. shared_pattern_project (share_state_table x) (\<sigma> a))
        (shared_derivation_project (share_state_table x) (shared_entry_node hn))"
proof (cases "shared_entry_variables hn |\<inter>| D = {||}")
  case True
  let ?n = "shared_derivation_project (share_state_table x) (shared_entry_node hn)"
  have "resolution_node_substitute (\<lambda>a. shared_pattern_project (share_state_table x) (\<sigma> a)) ?n = ?n"
  proof (rule resolution_node_substitute_outside)
    fix y assume "y |\<in>| resolution_node_variables ?n"
    then have "y |\<in>| shared_entry_variables hn" using node_entry_variables[OF hn] by simp
    with True have "y |\<notin>| D" by auto
    then show "shared_pattern_project (share_state_table x) (\<sigma> y) = Finite_Variable y" using out by simp
  qed
  with True x hn show ?thesis by (simp add: shared_node_entry_substitute_def)
next
  case False
  let ?n = "shared_entry_node hn"
  obtain n' x' where e: "shared_derivation_substitute \<sigma> D ?n x = (n', x')"
    by (cases "shared_derivation_substitute \<sigma> D ?n x") auto
  have nf: "shared_derivation_formed (share_state_table x) ?n" using hn by (simp add: node_entry_formed_def)
  note k = shared_derivation_substitute_exact[where q = x and nd = ?n and \<sigma> = \<sigma> and D = D, OF x nf \<sigma>f \<sigma>c out]
  have pos: "shared_derivation_position n' = q" using shared_derivation_substitute_fields(1)[of \<sigma> D ?n x] e hn
    by (simp add: node_entry_formed_def)
  show ?thesis using False e k pos enter_node_formed[of "share_state_table x'" n' q]
    by (simp add: shared_node_entry_substitute_def)
qed

subsection \<open>Substitution at one position\<close>

definition shared_substitute_at :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    's::linorder list \<Rightarrow> ('a,'s,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_substitute_at P \<sigma> D q s = (let
      gr = map_option (\<lambda>h. shared_goal_entry_substitute P \<sigma> D h (shared_sharing s)) (RBT.lookup (shared_goals s) q);
      x1 = case_option (shared_sharing s) snd gr;
      nr = map_option (\<lambda>hn. shared_node_entry_substitute \<sigma> D hn x1) (RBT.lookup (shared_nodes s) q);
      x2 = case_option x1 snd nr
    in shared_replace q (map_option fst gr) (map_option fst nr) (shared_reshare x2 s))"

lemma shared_substitute_at:
  fixes q
  assumes s: "shared_state_formed \<kappa> P s"
    and \<sigma>f: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  defines "s' \<equiv> shared_substitute_at P \<sigma> D q s"
  shows "shared_state_formed \<kappa> P s'"
    and "table_extends (shared_state_table s) (shared_state_table s')"
    and "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals s) p"
    and "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes s') p = RBT.lookup (shared_nodes s) p"
    and "map_option (\<lambda>h. shared_goal_project (shared_state_table s') (shared_entry_goal h)) (RBT.lookup (shared_goals s') q) =
      map_option (\<lambda>h. resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))
        (shared_goal_project (shared_state_table s) (shared_entry_goal h))) (RBT.lookup (shared_goals s) q)"
    and "map_option (\<lambda>hn. shared_derivation_project (shared_state_table s') (shared_entry_node hn)) (RBT.lookup (shared_nodes s') q) =
      map_option (\<lambda>hn. resolution_node_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))
        (shared_derivation_project (shared_state_table s) (shared_entry_node hn))) (RBT.lookup (shared_nodes s) q)"
    and "shared_witnesses s' = shared_witnesses s"
proof -
  let ?x0 = "shared_sharing s" and ?T0 = "shared_state_table s"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T0 (\<sigma> a)"
  define gr where "gr = map_option (\<lambda>h. shared_goal_entry_substitute P \<sigma> D h ?x0) (RBT.lookup (shared_goals s) q)"
  define x1 where "x1 = case_option ?x0 snd gr"
  define nr where "nr = map_option (\<lambda>hn. shared_node_entry_substitute \<sigma> D hn x1) (RBT.lookup (shared_nodes s) q)"
  define x2 where "x2 = case_option x1 snd nr"
  let ?T1 = "share_state_table x1" and ?T2 = "share_state_table x2"
  have x0: "share_state_formed ?x0" and tf0: "table_formed ?T0" using shared_entries_formed(3,4)[OF s] .
  have g1: "share_state_formed x1 \<and> table_extends ?T0 ?T1 \<and>
      (\<forall>h. map_option fst gr = Some h \<longrightarrow> goal_entry_formed P ?T1 q h) \<and>
      map_option (\<lambda>h. shared_goal_project ?T1 (shared_entry_goal h)) (map_option fst gr) =
        map_option (\<lambda>h. resolution_goal_substitute ?\<tau> (shared_goal_project ?T0 (shared_entry_goal h))) (RBT.lookup (shared_goals s) q)"
  proof (cases "RBT.lookup (shared_goals s) q")
    case None
    then show ?thesis using x0 by (simp add: gr_def x1_def)
  next
    case (Some h)
    have "goal_entry_formed P ?T0 q h" using shared_entries_formed(1)[OF s Some] .
    from shared_goal_entry_substitute[OF x0 this \<sigma>f \<sigma>c out] Some show ?thesis by (simp add: gr_def x1_def)
  qed
  have tf1: "table_formed ?T1" using g1 by (simp add: share_state_formed_def)
  have \<sigma>1: "\<And>a. shared_pattern_formed ?T1 (\<sigma> a)" and \<tau>1: "\<And>a. shared_pattern_project ?T1 (\<sigma> a) = ?\<tau> a"
    using shared_pattern_extends[OF tf0 \<sigma>f] g1 by blast+
  have n1: "share_state_formed x2 \<and> table_extends ?T1 ?T2 \<and>
      (\<forall>hn. map_option fst nr = Some hn \<longrightarrow> node_entry_formed ?T2 q hn) \<and>
      map_option (\<lambda>hn. shared_derivation_project ?T2 (shared_entry_node hn)) (map_option fst nr) =
        map_option (\<lambda>hn. resolution_node_substitute ?\<tau> (shared_derivation_project ?T0 (shared_entry_node hn))) (RBT.lookup (shared_nodes s) q)"
  proof (cases "RBT.lookup (shared_nodes s) q")
    case None
    then show ?thesis using g1 by (simp add: nr_def x2_def)
  next
    case (Some hn)
    have f0: "node_entry_formed ?T0 q hn" using shared_entries_formed(2)[OF s Some] .
    have e1: "node_entry_formed ?T1 q hn \<and>
        shared_derivation_project ?T1 (shared_entry_node hn) = shared_derivation_project ?T0 (shared_entry_node hn)"
      using node_entry_extends[OF tf0 f0] g1 by blast
    have x1f: "share_state_formed x1" using g1 by blast
    have st: "share_state_formed (snd (shared_node_entry_substitute \<sigma> D hn x1)) \<and>
      table_extends ?T1 (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x1))) \<and>
      node_entry_formed (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x1))) q
        (fst (shared_node_entry_substitute \<sigma> D hn x1)) \<and>
      shared_derivation_project (share_state_table (snd (shared_node_entry_substitute \<sigma> D hn x1)))
        (shared_entry_node (fst (shared_node_entry_substitute \<sigma> D hn x1))) =
        resolution_node_substitute (\<lambda>a. shared_pattern_project ?T1 (\<sigma> a))
          (shared_derivation_project ?T1 (shared_entry_node hn))"
      using shared_node_entry_substitute[OF x1f _ \<sigma>1 \<sigma>c out] e1 by blast
    show ?thesis using st e1 Some \<tau>1 by (simp add: nr_def x2_def)
  qed
  have ext02: "table_extends ?T0 ?T2" using g1 n1 table_extends_trans by blast
  have x2f: "share_state_formed x2" using n1 by blast
  let ?sr = "shared_reshare x2 s"
  have srf: "shared_state_formed \<kappa> P ?sr" using shared_reshare(1)[OF s x2f ext02] .
  have tbl: "shared_state_table ?sr = ?T2" by (simp add: shared_reshare_def)
  have e12: "table_extends ?T1 ?T2" using n1 by blast
  have go: "\<And>h. map_option fst gr = Some h \<Longrightarrow> goal_entry_formed P (shared_state_table ?sr) q h"
  proof -
    fix h assume "map_option fst gr = Some h"
    then have hf: "goal_entry_formed P ?T1 q h" using g1 by blast
    from goal_entry_extends[OF tf1 hf e12] tbl show "goal_entry_formed P (shared_state_table ?sr) q h" by simp
  qed
  have no: "\<And>hn. map_option fst nr = Some hn \<Longrightarrow> node_entry_formed (shared_state_table ?sr) q hn"
    using n1 tbl by simp
  have eq: "s' = shared_replace q (map_option fst gr) (map_option fst nr) ?sr"
    unfolding s'_def shared_substitute_at_def Let_def gr_def x1_def nr_def x2_def by (rule refl)
  show "shared_state_formed \<kappa> P s'" unfolding eq using shared_replace_formed[OF srf go no] .
  have tbl': "shared_state_table s' = ?T2" unfolding eq using tbl by simp
  show "table_extends ?T0 (shared_state_table s')" using ext02 tbl' by simp
  show "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_goals s') p = RBT.lookup (shared_goals s) p"
    unfolding eq by (simp add: shared_reshare_def)
  show "\<And>p. p \<noteq> q \<Longrightarrow> RBT.lookup (shared_nodes s') p = RBT.lookup (shared_nodes s) p"
    unfolding eq by (simp add: shared_reshare_def)
  have gq: "map_option (\<lambda>h. shared_goal_project ?T2 (shared_entry_goal h)) (map_option fst gr) =
      map_option (\<lambda>h. shared_goal_project ?T1 (shared_entry_goal h)) (map_option fst gr)"
  proof (cases "map_option fst gr")
    case (Some h)
    then have hf: "goal_entry_formed P ?T1 q h" using g1 by blast
    from goal_entry_extends[OF tf1 hf e12] show ?thesis unfolding Some by simp
  qed simp
  show "map_option (\<lambda>h. shared_goal_project (shared_state_table s') (shared_entry_goal h)) (RBT.lookup (shared_goals s') q) =
      map_option (\<lambda>h. resolution_goal_substitute ?\<tau> (shared_goal_project ?T0 (shared_entry_goal h))) (RBT.lookup (shared_goals s) q)"
  proof -
    have "RBT.lookup (shared_goals s') q = map_option fst gr" unfolding eq by simp
    then show ?thesis using gq g1 tbl' by simp
  qed
  show "map_option (\<lambda>hn. shared_derivation_project (shared_state_table s') (shared_entry_node hn)) (RBT.lookup (shared_nodes s') q) =
      map_option (\<lambda>hn. resolution_node_substitute ?\<tau> (shared_derivation_project ?T0 (shared_entry_node hn))) (RBT.lookup (shared_nodes s) q)"
  proof -
    have "RBT.lookup (shared_nodes s') q = map_option fst nr" unfolding eq by simp
    then show ?thesis using n1 tbl' by simp
  qed
  show "shared_witnesses s' = shared_witnesses s" unfolding eq by (simp add: shared_reshare_def)
qed

subsection \<open>The entries a state presents at a position\<close>

text \<open>
  What a state presents at a position is the goal and the node there, decoded: the projection is the set of what it
  presents, so two states presenting related entries at every position project to related states.
\<close>

definition shared_goal_view :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_goal option" where
  "shared_goal_view s p = map_option (\<lambda>h. shared_goal_project (shared_state_table s) (shared_entry_goal h))
    (RBT.lookup (shared_goals s) p)"

definition shared_node_view :: "('a,'s::linorder,'d,'c) shared_state \<Rightarrow> 's list \<Rightarrow> ('a,'s,'d,'c) resolution_node option" where
  "shared_node_view s p = map_option (\<lambda>hn. shared_derivation_project (shared_state_table s) (shared_entry_node hn))
    (RBT.lookup (shared_nodes s) p)"

lemma shared_state_project_views:
  assumes g: "\<And>p. shared_goal_view s' p = map_option f (shared_goal_view s p)"
    and n: "\<And>p. shared_node_view s' p = map_option k (shared_node_view s p)"
    and w: "shared_witnesses s' = shared_witnesses s"
  shows "shared_state_project s' = Resolution_State (fimage f (resolution_pending (shared_state_project s)))
    (fimage k (resolution_nodes (shared_state_project s))) (resolution_witnesses (shared_state_project s))"
proof -
  have gi: "fimage (\<lambda>h. shared_goal_project (shared_state_table s') (shared_entry_goal h)) (tree_values (shared_goals s')) =
      fimage (\<lambda>h. f (shared_goal_project (shared_state_table s) (shared_entry_goal h))) (tree_values (shared_goals s))"
  proof (rule tree_values_image)
    fix p
    show "map_option (\<lambda>h. shared_goal_project (shared_state_table s') (shared_entry_goal h)) (RBT.lookup (shared_goals s') p) =
        map_option (\<lambda>h. f (shared_goal_project (shared_state_table s) (shared_entry_goal h))) (RBT.lookup (shared_goals s) p)"
      using g[of p] by (simp add: shared_goal_view_def option.map_comp comp_def)
  qed
  have ni: "fimage (\<lambda>hn. shared_derivation_project (shared_state_table s') (shared_entry_node hn)) (tree_values (shared_nodes s')) =
      fimage (\<lambda>hn. k (shared_derivation_project (shared_state_table s) (shared_entry_node hn))) (tree_values (shared_nodes s))"
  proof (rule tree_values_image)
    fix p
    show "map_option (\<lambda>hn. shared_derivation_project (shared_state_table s') (shared_entry_node hn)) (RBT.lookup (shared_nodes s') p) =
        map_option (\<lambda>hn. k (shared_derivation_project (shared_state_table s) (shared_entry_node hn))) (RBT.lookup (shared_nodes s) p)"
      using n[of p] by (simp add: shared_node_view_def option.map_comp comp_def)
  qed
  show ?thesis using gi ni w by (simp add: shared_state_project_def fset.map_comp comp_def)
qed

lemma shared_substitute_at_views:
  assumes s: "shared_state_formed \<kappa> P s"
    and \<sigma>f: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "p \<noteq> q \<Longrightarrow> shared_goal_view (shared_substitute_at P \<sigma> D q s) p = shared_goal_view s p"
    and "p \<noteq> q \<Longrightarrow> shared_node_view (shared_substitute_at P \<sigma> D q s) p = shared_node_view s p"
    and "shared_goal_view (shared_substitute_at P \<sigma> D q s) q =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_goal_view s q)"
    and "shared_node_view (shared_substitute_at P \<sigma> D q s) q =
      map_option (resolution_node_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_node_view s q)"
proof -
  let ?s' = "shared_substitute_at P \<sigma> D q s" and ?T = "shared_state_table s"
  note k = shared_substitute_at[where D = D and q = q, OF s \<sigma>f \<sigma>c out]
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  have ext: "table_extends ?T (shared_state_table ?s')" using k(2) by simp
  have g3: "RBT.lookup (shared_goals ?s') p = RBT.lookup (shared_goals s) p" if "p \<noteq> q"
    using k(3)[where p = p] that by simp
  have n3: "RBT.lookup (shared_nodes ?s') p = RBT.lookup (shared_nodes s) p" if "p \<noteq> q"
    using k(4)[where p = p] that by simp
  show "shared_goal_view ?s' p = shared_goal_view s p" if "p \<noteq> q"
  proof (cases "RBT.lookup (shared_goals s) p")
    case (Some h)
    from goal_entry_extends[OF tf shared_entries_formed(1)[OF s Some] ext] Some g3[OF that] show ?thesis
      by (simp add: shared_goal_view_def)
  next
    case None
    with g3[OF that] show ?thesis by (simp add: shared_goal_view_def)
  qed
  show "shared_node_view ?s' p = shared_node_view s p" if "p \<noteq> q"
  proof (cases "RBT.lookup (shared_nodes s) p")
    case (Some hn)
    from node_entry_extends[OF tf shared_entries_formed(2)[OF s Some] ext] Some n3[OF that] show ?thesis
      by (simp add: shared_node_view_def)
  next
    case None
    with n3[OF that] show ?thesis by (simp add: shared_node_view_def)
  qed
  show "shared_goal_view ?s' q =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project ?T (\<sigma> a))) (shared_goal_view s q)"
    using k(5) by (simp add: shared_goal_view_def option.map_comp comp_def)
  show "shared_node_view ?s' q =
      map_option (resolution_node_substitute (\<lambda>a. shared_pattern_project ?T (\<sigma> a))) (shared_node_view s q)"
    using k(6) by (simp add: shared_node_view_def option.map_comp comp_def)
qed

subsection \<open>Substitution at the holders\<close>

text \<open>
  The positions substitution visits are those the holder index finds for the position parts of the variables it binds.
  An entry at any other position holds none of them, since the index records every variable of every entry, so
  substitution leaves what it presents as it is; the index being a superset, a visited entry may hold none either, and
  substitution at one position leaves such an entry as it is too.
\<close>

definition shared_substitute_positions :: "('s,'a) resolution_variable fset \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow>
    's list fset" where
  "shared_substitute_positions D s = ffUnion (fimage (tree_bucket (shared_holders s)) (variable_positions D))"

definition shared_state_substitute :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow>
    (('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable shared_pattern) \<Rightarrow> ('s,'a) resolution_variable fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_state_substitute P \<sigma> D s =
    fold (shared_substitute_at P \<sigma> D) (sorted_list_of_fset (shared_substitute_positions D s)) s"

lemma shared_substitute_unvisited:
  assumes s: "shared_state_formed \<kappa> P s" and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
    and p: "p |\<notin>| shared_substitute_positions D s"
  shows "shared_goal_view s p =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_goal_view s p)"
    and "shared_node_view s p =
      map_option (resolution_node_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a))) (shared_node_view s p)"
proof -
  let ?T = "shared_state_table s" and ?\<tau> = "\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a)"
  have free: "x |\<notin>| D" if "p |\<in>| tree_bucket (shared_holders s) (fst (fst x))" for x
  proof
    assume "x |\<in>| D"
    then have "fst (fst x) |\<in>| variable_positions D" by (auto simp: variable_positions_def)
    with that p show False by (force simp: shared_substitute_positions_def ffUnion.rep_eq fimage.rep_eq)
  qed
  have rec: "shared_recorded_at s p" using s by (simp add: shared_state_formed_def)
  have \<tau>: "?\<tau> y = Finite_Variable y" if "y |\<notin>| D" for y using out[OF that] by simp
  show "shared_goal_view s p = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view s p)"
  proof (cases "RBT.lookup (shared_goals s) p")
    case (Some h)
    have hf: "goal_entry_formed P ?T p h" using shared_entries_formed(1)[OF s Some] .
    have "resolution_goal_substitute ?\<tau> (shared_goal_project ?T (shared_entry_goal h)) = shared_goal_project ?T (shared_entry_goal h)"
    proof (rule resolution_goal_substitute_outside)
      fix y assume "y |\<in>| resolution_goal_variables (shared_goal_project ?T (shared_entry_goal h))"
      then have "y |\<in>| shared_goal_variables (shared_entry_goal h)" using goal_entry_variables[OF hf] by simp
      then have "p |\<in>| tree_bucket (shared_holders s) (fst (fst y))" using rec Some unfolding shared_recorded_at_def by blast
      then show "?\<tau> y = Finite_Variable y" using \<tau> free by blast
    qed
    with Some show ?thesis by (simp add: shared_goal_view_def)
  qed (simp add: shared_goal_view_def)
  show "shared_node_view s p = map_option (resolution_node_substitute ?\<tau>) (shared_node_view s p)"
  proof (cases "RBT.lookup (shared_nodes s) p")
    case (Some hn)
    have hf: "node_entry_formed ?T p hn" using shared_entries_formed(2)[OF s Some] .
    have "resolution_node_substitute ?\<tau> (shared_derivation_project ?T (shared_entry_node hn)) =
        shared_derivation_project ?T (shared_entry_node hn)"
    proof (rule resolution_node_substitute_outside)
      fix y assume "y |\<in>| resolution_node_variables (shared_derivation_project ?T (shared_entry_node hn))"
      then have "y |\<in>| shared_entry_variables hn" using node_entry_variables[OF hf] by simp
      then have "p |\<in>| tree_bucket (shared_holders s) (fst (fst y))" using rec Some unfolding shared_recorded_at_def by blast
      then show "?\<tau> y = Finite_Variable y" using \<tau> free by blast
    qed
    with Some show ?thesis by (simp add: shared_node_view_def)
  qed (simp add: shared_node_view_def)
qed

lemma shared_substitute_fold:
  assumes t: "shared_state_formed \<kappa> P t" and tf0: "table_formed T0"
    and ext: "table_extends T0 (shared_state_table t)"
    and \<sigma>f: "\<And>a. shared_pattern_formed T0 (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a" and qs: "distinct qs"
    and gin: "\<And>p. p \<in> set qs \<Longrightarrow> shared_goal_view t p = G p"
    and gout: "\<And>p. p \<notin> set qs \<Longrightarrow>
      shared_goal_view t p = map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (G p)"
    and nin: "\<And>p. p \<in> set qs \<Longrightarrow> shared_node_view t p = N p"
    and nout: "\<And>p. p \<notin> set qs \<Longrightarrow>
      shared_node_view t p = map_option (resolution_node_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (N p)"
  shows "shared_state_formed \<kappa> P (fold (shared_substitute_at P \<sigma> D) qs t) \<and>
    table_extends T0 (shared_state_table (fold (shared_substitute_at P \<sigma> D) qs t)) \<and>
    (\<forall>p. shared_goal_view (fold (shared_substitute_at P \<sigma> D) qs t) p =
      map_option (resolution_goal_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (G p)) \<and>
    (\<forall>p. shared_node_view (fold (shared_substitute_at P \<sigma> D) qs t) p =
      map_option (resolution_node_substitute (\<lambda>a. shared_pattern_project T0 (\<sigma> a))) (N p)) \<and>
    shared_witnesses (fold (shared_substitute_at P \<sigma> D) qs t) = shared_witnesses t"
  using assms
proof (induction qs arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  let ?\<tau> = "\<lambda>a. shared_pattern_project T0 (\<sigma> a)" and ?t' = "shared_substitute_at P \<sigma> D q t"
  have \<sigma>t: "\<And>a. shared_pattern_formed (shared_state_table t) (\<sigma> a)"
    using shared_pattern_extends(1)[OF Cons.prems(2) Cons.prems(4) Cons.prems(3)] .
  have \<tau>t: "\<And>a. shared_pattern_project (shared_state_table t) (\<sigma> a) = ?\<tau> a"
    using shared_pattern_extends(2)[OF Cons.prems(2) Cons.prems(4) Cons.prems(3)] .
  note k = shared_substitute_at_views[where D = D and q = q, OF Cons.prems(1) \<sigma>t Cons.prems(5) Cons.prems(6)]
  note f = shared_substitute_at[where D = D and q = q, OF Cons.prems(1) \<sigma>t Cons.prems(5) Cons.prems(6)]
  have f1: "shared_state_formed \<kappa> P ?t'" using f(1) by simp
  have f2: "table_extends (shared_state_table t) (shared_state_table ?t')" using f(2) by simp
  have f7: "shared_witnesses ?t' = shared_witnesses t" using f(7) by simp
  have d: "q \<notin> set qs" "distinct qs" using Cons.prems(7) by simp_all
  have ext': "table_extends T0 (shared_state_table ?t')" using table_extends_trans[OF Cons.prems(3) f2] .
  have gin': "shared_goal_view ?t' p = G p" if "p \<in> set qs" for p
  proof -
    have "p \<noteq> q" using that d by auto
    then show ?thesis using k(1)[where p = p] Cons.prems(8)[of p] that by simp
  qed
  have gout': "shared_goal_view ?t' p = map_option (resolution_goal_substitute ?\<tau>) (G p)" if "p \<notin> set qs" for p
  proof (cases "p = q")
    case True
    then show ?thesis using k(3) Cons.prems(8)[of q] \<tau>t by simp
  next
    case False
    then show ?thesis using k(1)[where p = p] Cons.prems(9)[of p] that by simp
  qed
  have nin': "shared_node_view ?t' p = N p" if "p \<in> set qs" for p
  proof -
    have "p \<noteq> q" using that d by auto
    then show ?thesis using k(2)[where p = p] Cons.prems(10)[of p] that by simp
  qed
  have nout': "shared_node_view ?t' p = map_option (resolution_node_substitute ?\<tau>) (N p)" if "p \<notin> set qs" for p
  proof (cases "p = q")
    case True
    then show ?thesis using k(4) Cons.prems(10)[of q] \<tau>t by simp
  next
    case False
    then show ?thesis using k(2)[where p = p] Cons.prems(11)[of p] that by simp
  qed
  have "shared_state_formed \<kappa> P (fold (shared_substitute_at P \<sigma> D) qs ?t') \<and>
    table_extends T0 (shared_state_table (fold (shared_substitute_at P \<sigma> D) qs ?t')) \<and>
    (\<forall>p. shared_goal_view (fold (shared_substitute_at P \<sigma> D) qs ?t') p = map_option (resolution_goal_substitute ?\<tau>) (G p)) \<and>
    (\<forall>p. shared_node_view (fold (shared_substitute_at P \<sigma> D) qs ?t') p = map_option (resolution_node_substitute ?\<tau>) (N p)) \<and>
    shared_witnesses (fold (shared_substitute_at P \<sigma> D) qs ?t') = shared_witnesses ?t'"
    using Cons.IH[OF f1 Cons.prems(2) ext' Cons.prems(4) Cons.prems(5) Cons.prems(6) d(2) gin' gout' nin' nout'] .
  then show ?case using f7 by simp
qed

theorem shared_state_substitute:
  assumes s: "shared_state_formed \<kappa> P s"
    and \<sigma>f: "\<And>a. shared_pattern_formed (shared_state_table s) (\<sigma> a)" and \<sigma>c: "\<And>a. shared_collapsed (\<sigma> a)"
    and out: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_state_formed \<kappa> P (shared_state_substitute P \<sigma> D s)"
    and "table_extends (shared_state_table s) (shared_state_table (shared_state_substitute P \<sigma> D s))"
    and "shared_state_project (shared_state_substitute P \<sigma> D s) =
      resolution_state_substitute (\<lambda>a. shared_pattern_project (shared_state_table s) (\<sigma> a)) (shared_state_project s)"
proof -
  let ?qs = "sorted_list_of_fset (shared_substitute_positions D s)" and ?T = "shared_state_table s"
  let ?\<tau> = "\<lambda>a. shared_pattern_project ?T (\<sigma> a)"
  have tf: "table_formed ?T" using shared_entries_formed(4)[OF s] .
  note u = shared_substitute_unvisited[where D = D, OF s out]
  have gout: "shared_goal_view s p = map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view s p)"
    if "p \<notin> set ?qs" for p
    using u(1)[where p = p] that by simp
  have nout: "shared_node_view s p = map_option (resolution_node_substitute ?\<tau>) (shared_node_view s p)"
    if "p \<notin> set ?qs" for p
    using u(2)[where p = p] that by simp
  note fold0 = shared_substitute_fold[where D = D, OF s tf table_extends_refl \<sigma>f \<sigma>c out]
  have k: "shared_state_formed \<kappa> P (fold (shared_substitute_at P \<sigma> D) ?qs s) \<and>
    table_extends ?T (shared_state_table (fold (shared_substitute_at P \<sigma> D) ?qs s)) \<and>
    (\<forall>p. shared_goal_view (fold (shared_substitute_at P \<sigma> D) ?qs s) p =
      map_option (resolution_goal_substitute ?\<tau>) (shared_goal_view s p)) \<and>
    (\<forall>p. shared_node_view (fold (shared_substitute_at P \<sigma> D) ?qs s) p =
      map_option (resolution_node_substitute ?\<tau>) (shared_node_view s p)) \<and>
    shared_witnesses (fold (shared_substitute_at P \<sigma> D) ?qs s) = shared_witnesses s"
    by (rule fold0[OF _ _ _ gout _ nout]) simp_all
  have e: "shared_state_substitute P \<sigma> D s = fold (shared_substitute_at P \<sigma> D) ?qs s"
    by (simp add: shared_state_substitute_def)
  show "shared_state_formed \<kappa> P (shared_state_substitute P \<sigma> D s)" using k e by simp
  show "table_extends ?T (shared_state_table (shared_state_substitute P \<sigma> D s))" using k e by simp
  show "shared_state_project (shared_state_substitute P \<sigma> D s) = resolution_state_substitute ?\<tau> (shared_state_project s)"
    unfolding resolution_state_substitute_def
    by (rule shared_state_project_views) (use k e in simp_all)
qed

section \<open>The shared state of an R3 state\<close>

text \<open>
  The shared state of an R3 state shares, once and in their order, the ground terms of all its goals and nodes, and
  places each goal and each node, read against the one resulting state, at its position. R3's search keeps one goal
  and one node per position (@{const resolution_positions_distinct}), so the goals and the nodes are the rows of two
  functional relations from positions, placed in their positions' order. The state it makes is formed, its call
  patterns collapsed, and projects back to the R3 state.
\<close>

definition shared_empty :: "share_state \<Rightarrow> (('s,'a) resolution_variable \<times> finite_factor_term) fset \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_state" where
  "shared_empty x W = \<lparr>shared_sharing = x, shared_positions = position_index_extend (RBT.empty,0,[]) x RBT.empty,
    shared_goals = RBT.empty, shared_nodes = RBT.empty, shared_witnesses = W, shared_holders = RBT.empty,
    shared_open = RBT.empty, shared_goal_calls = RBT.empty, shared_node_calls = RBT.empty,
    shared_unconstructed = RBT.empty\<rparr>"

lemma shared_empty:
  assumes x: "share_state_formed x" and ext: "table_extends [] (share_state_table x)"
  shows "shared_state_formed \<kappa> P (shared_empty x W)"
    and "shared_state_project (shared_empty x W) = Resolution_State {||} {||} W"
    and "RBT.lookup (shared_goals (shared_empty x W)) p = None"
    and "RBT.lookup (shared_nodes (shared_empty x W)) p = None"
    and "shared_sharing (shared_empty x W) = x"
proof -
  have e: "position_index_formed (RBT.empty,0,[]) RBT.empty"
    by (simp add: position_index_formed_def value_reference_read_def share_state_empty)
  have pos: "position_index_formed x (position_index_extend (RBT.empty,0,[]) x RBT.empty)"
    using position_index_extend[OF share_state_empty(1) x _ e] ext share_state_empty(2) by simp
  have sel: "shared_sharing (shared_empty x W) = x"
    "shared_positions (shared_empty x W) = position_index_extend (RBT.empty,0,[]) x RBT.empty"
    "shared_goals (shared_empty x W) = RBT.empty" "shared_nodes (shared_empty x W) = RBT.empty"
    "shared_holders (shared_empty x W) = RBT.empty" "shared_open (shared_empty x W) = RBT.empty"
    "shared_goal_calls (shared_empty x W) = RBT.empty" "shared_node_calls (shared_empty x W) = RBT.empty"
    "shared_unconstructed (shared_empty x W) = RBT.empty"
    by (simp_all add: shared_empty_def)
  have rec: "\<forall>q. shared_recorded_at (shared_empty x W) q" by (simp add: shared_recorded_at_def sel)
  show "shared_state_formed \<kappa> P (shared_empty x W)"
    unfolding shared_state_formed_def using x pos rec
    by (simp add: sel tree_bucket_def tree_count_def tree_keys_under_def)
  show "shared_state_project (shared_empty x W) = Resolution_State {||} {||} W"
    by (simp add: shared_state_project_def shared_empty_def)
  show "RBT.lookup (shared_goals (shared_empty x W)) p = None" "RBT.lookup (shared_nodes (shared_empty x W)) p = None"
    "shared_sharing (shared_empty x W) = x"
    by (simp_all add: shared_empty_def)
qed

definition shared_place_nodes :: "('s list \<times> ('a,'s,'d,'c) resolution_node) list \<Rightarrow> ('a,'s::linorder,'d,'c) shared_state \<Rightarrow>
    ('a,'s,'d,'c) shared_state" where
  "shared_place_nodes rows s =
    fold (\<lambda>(q,nd) t. shared_put_node q (enter_node (shared_derivation_of (shared_sharing t) nd)) t) rows s"

definition shared_place_goals :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('s list \<times> ('a,'s,'d,'c) resolution_goal) list \<Rightarrow>
    ('a,'s::linorder,'d,'c) shared_state \<Rightarrow> ('a,'s,'d,'c) shared_state" where
  "shared_place_goals P rows s =
    fold (\<lambda>(q,g) t. shared_put_goal q (enter_goal P (shared_state_table t) (shared_goal_of (shared_sharing t) g)) t) rows s"

lemma shared_place_nodes:
  assumes t: "shared_state_formed \<kappa> P t" and d: "distinct (map fst rows)"
    and free: "\<And>q nd. (q,nd) \<in> set rows \<Longrightarrow> RBT.lookup (shared_nodes t) q = None"
    and pos: "\<And>q nd. (q,nd) \<in> set rows \<Longrightarrow> resolution_node_position nd = q"
    and held: "\<And>q nd u. (q,nd) \<in> set rows \<Longrightarrow> u |\<in>| node_grounds nd \<Longrightarrow> table_holds (shared_state_table t) u"
  shows "shared_state_formed \<kappa> P (shared_place_nodes rows t) \<and>
    shared_sharing (shared_place_nodes rows t) = shared_sharing t \<and>
    (\<forall>p. RBT.lookup (shared_goals (shared_place_nodes rows t)) p = RBT.lookup (shared_goals t) p) \<and>
    resolution_pending (shared_state_project (shared_place_nodes rows t)) = resolution_pending (shared_state_project t) \<and>
    resolution_nodes (shared_state_project (shared_place_nodes rows t)) =
      resolution_nodes (shared_state_project t) |\<union>| fset_of_list (map snd rows) \<and>
    resolution_witnesses (shared_state_project (shared_place_nodes rows t)) = resolution_witnesses (shared_state_project t)"
  using assms
proof (induction rows arbitrary: t)
  case Nil
  then show ?case by (simp add: shared_place_nodes_def)
next
  case (Cons r rows)
  obtain q nd where r: "r = (q,nd)" by (cases r)
  let ?x = "shared_sharing t" and ?T = "shared_state_table t"
  let ?hn = "enter_node (shared_derivation_of ?x nd)" and ?t' = "shared_put_node q (enter_node (shared_derivation_of ?x nd)) t"
  have xf: "share_state_formed ?x" using shared_entries_formed(3)[OF Cons.prems(1)] .
  have rep: "keyed_state_represents ?x ?T" and tf: "table_formed ?T"
    using share_state_formed_table[OF xf] by simp_all
  have hd: "\<And>u. u |\<in>| node_grounds nd \<Longrightarrow> table_holds ?T u" using Cons.prems(5) r by auto
  have ex: "shared_derivation_formed ?T (shared_derivation_of ?x nd) \<and>
      shared_derivation_project ?T (shared_derivation_of ?x nd) = nd"
    using shared_derivation_of_exact[OF rep tf hd] .
  have pq: "shared_derivation_position (shared_derivation_of ?x nd) = q"
    using Cons.prems(4)[of q nd] r by (simp add: shared_derivation_of_def)
  have hn: "node_entry_formed ?T q ?hn" using enter_node_formed[OF conjunct1[OF ex] pq] .
  have fr: "RBT.lookup (shared_nodes t) q = None" using Cons.prems(3)[of q nd] r by simp
  note put = shared_put_node[OF Cons.prems(1) hn fr]
  have sh: "shared_sharing ?t' = ?x" by (simp add: shared_put_node_def)
  have gl: "\<And>p. RBT.lookup (shared_goals ?t') p = RBT.lookup (shared_goals t) p" by (simp add: shared_put_node_def)
  have d': "distinct (map fst rows)" using Cons.prems(2) by simp
  have nq: "(q,nd') \<notin> set rows" for nd'
  proof
    assume "(q,nd') \<in> set rows"
    then have "q \<in> set (map fst rows)" by force
    with Cons.prems(2) r show False by simp
  qed
  have free': "\<And>q' nd'. (q',nd') \<in> set rows \<Longrightarrow> RBT.lookup (shared_nodes ?t') q' = None"
  proof -
    fix q' nd' assume m: "(q',nd') \<in> set rows"
    then have "q' \<noteq> q" using nq by auto
    then show "RBT.lookup (shared_nodes ?t') q' = None" using Cons.prems(3)[of q' nd'] m by (simp add: shared_put_node_def)
  qed
  have pos': "\<And>q' nd'. (q',nd') \<in> set rows \<Longrightarrow> resolution_node_position nd' = q'" using Cons.prems(4) by auto
  have held': "\<And>q' nd' u. (q',nd') \<in> set rows \<Longrightarrow> u |\<in>| node_grounds nd' \<Longrightarrow> table_holds (shared_state_table ?t') u"
    using Cons.prems(5) sh by auto
  note IH = Cons.IH[OF put(1) d' free' pos' held']
  have unf: "shared_place_nodes (r # rows) t = shared_place_nodes rows ?t'" by (simp add: shared_place_nodes_def r)
  show ?case unfolding unf using IH put(2-4) sh gl ex r by (auto intro!: fset_eqI)
qed

lemma shared_place_goals:
  assumes t: "shared_state_formed \<kappa> P t" and d: "distinct (map fst rows)"
    and free: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> RBT.lookup (shared_goals t) q = None"
    and pos: "\<And>q g. (q,g) \<in> set rows \<Longrightarrow> resolution_goal_position g = q"
    and held: "\<And>q g u. (q,g) \<in> set rows \<Longrightarrow> u |\<in>| goal_grounds g \<Longrightarrow> table_holds (shared_state_table t) u"
  shows "shared_state_formed \<kappa> P (shared_place_goals P rows t) \<and>
    shared_sharing (shared_place_goals P rows t) = shared_sharing t \<and>
    resolution_pending (shared_state_project (shared_place_goals P rows t)) =
      resolution_pending (shared_state_project t) |\<union>| fset_of_list (map snd rows) \<and>
    resolution_nodes (shared_state_project (shared_place_goals P rows t)) = resolution_nodes (shared_state_project t) \<and>
    resolution_witnesses (shared_state_project (shared_place_goals P rows t)) = resolution_witnesses (shared_state_project t)"
  using assms
proof (induction rows arbitrary: t)
  case Nil
  then show ?case by (simp add: shared_place_goals_def)
next
  case (Cons r rows)
  obtain q g where r: "r = (q,g)" by (cases r)
  let ?x = "shared_sharing t" and ?T = "shared_state_table t"
  let ?h = "enter_goal P (shared_state_table t) (shared_goal_of (shared_sharing t) g)"
  let ?t' = "shared_put_goal q (enter_goal P (shared_state_table t) (shared_goal_of (shared_sharing t) g)) t"
  have xf: "share_state_formed ?x" using shared_entries_formed(3)[OF Cons.prems(1)] .
  have rep: "keyed_state_represents ?x ?T" and tf: "table_formed ?T"
    using share_state_formed_table[OF xf] by simp_all
  have hd: "\<And>u. u |\<in>| goal_grounds g \<Longrightarrow> table_holds ?T u" using Cons.prems(5) r by auto
  have ex: "shared_goal_formed ?T (shared_goal_of ?x g) \<and> shared_goal_project ?T (shared_goal_of ?x g) = g"
    using shared_goal_of_exact[OF rep tf hd] .
  have pq: "shared_goal_position (shared_goal_of ?x g) = q"
    using Cons.prems(4)[of q g] r ex shared_goal_project_position[of ?T "shared_goal_of ?x g"] by simp
  have hf: "goal_entry_formed P ?T q ?h" using enter_goal_formed[OF conjunct1[OF ex] pq] .
  have fr: "RBT.lookup (shared_goals t) q = None" using Cons.prems(3)[of q g] r by simp
  note put = shared_put_goal[OF Cons.prems(1) hf fr]
  have sh: "shared_sharing ?t' = ?x" by (simp add: shared_put_goal_def)
  have d': "distinct (map fst rows)" using Cons.prems(2) by simp
  have nq: "(q,g') \<notin> set rows" for g'
  proof
    assume "(q,g') \<in> set rows"
    then have "q \<in> set (map fst rows)" by force
    with Cons.prems(2) r show False by simp
  qed
  have free': "\<And>q' g'. (q',g') \<in> set rows \<Longrightarrow> RBT.lookup (shared_goals ?t') q' = None"
  proof -
    fix q' g' assume m: "(q',g') \<in> set rows"
    then have "q' \<noteq> q" using nq by auto
    then show "RBT.lookup (shared_goals ?t') q' = None" using Cons.prems(3)[of q' g'] m by (simp add: shared_put_goal_def)
  qed
  have pos': "\<And>q' g'. (q',g') \<in> set rows \<Longrightarrow> resolution_goal_position g' = q'" using Cons.prems(4) by auto
  have held': "\<And>q' g' u. (q',g') \<in> set rows \<Longrightarrow> u |\<in>| goal_grounds g' \<Longrightarrow> table_holds (shared_state_table ?t') u"
    using Cons.prems(5) sh by auto
  note IH = Cons.IH[OF put(1) d' free' pos' held']
  have unf: "shared_place_goals P (r # rows) t = shared_place_goals P rows ?t'" by (simp add: shared_place_goals_def r)
  show ?case unfolding unf using IH put(2-4) sh ex r by (auto intro!: fset_eqI)
qed

definition resolution_grounds :: "('a,'s,'d,'c) resolution_state \<Rightarrow> finite_factor_term fset" where
  "resolution_grounds st =
    ffUnion (fimage goal_grounds (resolution_pending st)) |\<union>| ffUnion (fimage node_grounds (resolution_nodes st))"

definition resolution_goal_rows :: "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('s list \<times> ('a,'s,'d,'c) resolution_goal) list" where
  "resolution_goal_rows st = finite_functional_rows (fimage (\<lambda>g. (resolution_goal_position g, g)) (resolution_pending st))"

definition resolution_node_rows :: "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('s list \<times> ('a,'s,'d,'c) resolution_node) list" where
  "resolution_node_rows st = finite_functional_rows (fimage (\<lambda>nd. (resolution_node_position nd, nd)) (resolution_nodes st))"

definition share_resolution_state :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) shared_state" where
  "share_resolution_state P st = shared_place_goals P (resolution_goal_rows st)
    (shared_place_nodes (resolution_node_rows st)
      (shared_empty (keyed_share_grounds (resolution_grounds st) (RBT.empty,0,[])) (resolution_witnesses st)))"

theorem share_resolution_state:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and st :: "('a,'s,'d,'c) resolution_state"
  assumes d: "resolution_positions_distinct st"
  shows "shared_state_formed \<kappa> P (share_resolution_state P st)"
    and "shared_state_project (share_resolution_state P st) = st"
proof -
  let ?x = "keyed_share_grounds (resolution_grounds st) (RBT.empty,0,[])"
  let ?NR = "fimage (\<lambda>nd. (resolution_node_position nd, nd)) (resolution_nodes st)"
  let ?GR = "fimage (\<lambda>g. (resolution_goal_position g, g)) (resolution_pending st)"
  let ?s0 = "shared_empty ?x (resolution_witnesses st) :: ('a,'s,'d,'c) shared_state"
  let ?s1 = "shared_place_nodes (finite_functional_rows ?NR) ?s0"
  note kx = keyed_share_grounds[where G = "resolution_grounds st", OF share_state_empty(1)]
  have xf: "share_state_formed ?x" using kx(1) .
  have ext: "table_extends [] (share_state_table ?x)" using kx(2) share_state_empty(2) by simp
  have hx: "\<And>u. u |\<in>| resolution_grounds st \<Longrightarrow> table_holds (share_state_table ?x) u" using kx(3) .
  have e1: "shared_state_formed \<kappa> P ?s0" by (rule shared_empty(1)[OF xf ext])
  have e2: "shared_state_project ?s0 = Resolution_State {||} {||} (resolution_witnesses st)"
    by (rule shared_empty(2)[OF xf ext])
  have e3: "\<And>p. RBT.lookup (shared_goals ?s0) p = None" and e4: "\<And>p. RBT.lookup (shared_nodes ?s0) p = None"
    and e5: "shared_sharing ?s0 = ?x"
    by (simp_all add: shared_empty_def)
  have nfun: "finite_relation_functional ?NR"
    unfolding finite_relation_functional_def
  proof (intro fBallI impI)
    fix a b assume "a |\<in>| ?NR" "b |\<in>| ?NR" "fst a = fst b"
    then show "snd a = snd b" using d by (auto simp: resolution_positions_distinct_def)
  qed
  have gfun: "finite_relation_functional ?GR"
    unfolding finite_relation_functional_def
  proof (intro fBallI impI)
    fix a b assume "a |\<in>| ?GR" "b |\<in>| ?GR" "fst a = fst b"
    then show "snd a = snd b" using d by (auto simp: resolution_positions_distinct_def)
  qed
  have nrows: "set (finite_functional_rows ?NR) = fset ?NR" using finite_functional_rows_exact[OF nfun] .
  have grows: "set (finite_functional_rows ?GR) = fset ?GR" using finite_functional_rows_exact[OF gfun] .
  have nfree: "\<And>q nd. (q,nd) \<in> set (finite_functional_rows ?NR) \<Longrightarrow> RBT.lookup (shared_nodes ?s0) q = None"
    using e4 by simp
  have npos: "\<And>q nd. (q,nd) \<in> set (finite_functional_rows ?NR) \<Longrightarrow> resolution_node_position nd = q"
    using nrows by auto
  have nheld: "\<And>q nd u. (q,nd) \<in> set (finite_functional_rows ?NR) \<Longrightarrow> u |\<in>| node_grounds nd \<Longrightarrow>
      table_holds (shared_state_table ?s0) u"
  proof -
    fix q nd u assume m: "(q,nd) \<in> set (finite_functional_rows ?NR)" and u: "u |\<in>| node_grounds nd"
    have "nd |\<in>| resolution_nodes st" using m nrows by auto
    then have "u |\<in>| resolution_grounds st" using u by (auto simp: resolution_grounds_def ffUnion.rep_eq fimage.rep_eq)
    then show "table_holds (shared_state_table ?s0) u" using hx e5 by simp
  qed
  have n: "shared_state_formed \<kappa> P ?s1 \<and> shared_sharing ?s1 = shared_sharing ?s0 \<and>
    (\<forall>p. RBT.lookup (shared_goals ?s1) p = RBT.lookup (shared_goals ?s0) p) \<and>
    resolution_pending (shared_state_project ?s1) = resolution_pending (shared_state_project ?s0) \<and>
    resolution_nodes (shared_state_project ?s1) =
      resolution_nodes (shared_state_project ?s0) |\<union>| fset_of_list (map snd (finite_functional_rows ?NR)) \<and>
    resolution_witnesses (shared_state_project ?s1) = resolution_witnesses (shared_state_project ?s0)"
    using shared_place_nodes[OF e1 finite_functional_rows_distinct_keys[OF nfun] nfree npos nheld] .
  have gfree: "\<And>q g. (q,g) \<in> set (finite_functional_rows ?GR) \<Longrightarrow> RBT.lookup (shared_goals ?s1) q = None"
    using n e3 by simp
  have gpos: "\<And>q g. (q,g) \<in> set (finite_functional_rows ?GR) \<Longrightarrow> resolution_goal_position g = q"
    using grows by auto
  have gheld: "\<And>q g u. (q,g) \<in> set (finite_functional_rows ?GR) \<Longrightarrow> u |\<in>| goal_grounds g \<Longrightarrow>
      table_holds (shared_state_table ?s1) u"
  proof -
    fix q g u assume m: "(q,g) \<in> set (finite_functional_rows ?GR)" and u: "u |\<in>| goal_grounds g"
    have "g |\<in>| resolution_pending st" using m grows by auto
    then have "u |\<in>| resolution_grounds st" using u by (auto simp: resolution_grounds_def ffUnion.rep_eq fimage.rep_eq)
    moreover have "shared_sharing ?s1 = ?x" using conjunct1[OF conjunct2[OF n]] e5 by simp
    ultimately show "table_holds (shared_state_table ?s1) u" using hx by simp
  qed
  note g = shared_place_goals[OF conjunct1[OF n] finite_functional_rows_distinct_keys[OF gfun] gfree gpos gheld]
  have eq: "share_resolution_state P st = shared_place_goals P (finite_functional_rows ?GR) ?s1"
    by (simp add: share_resolution_state_def resolution_goal_rows_def resolution_node_rows_def)
  show "shared_state_formed \<kappa> P (share_resolution_state P st)" using g eq by simp
  have nl: "fset_of_list (map snd (finite_functional_rows ?NR)) = resolution_nodes st"
    by (unfold fset_of_list_eq_set) (simp add: nrows fimage.rep_eq image_image)
  have gl: "fset_of_list (map snd (finite_functional_rows ?GR)) = resolution_pending st"
    by (unfold fset_of_list_eq_set) (simp add: grows fimage.rep_eq image_image)
  have p1: "resolution_pending (shared_state_project (share_resolution_state P st)) = resolution_pending st"
    using g n e2 gl eq by simp
  have p2: "resolution_nodes (shared_state_project (share_resolution_state P st)) = resolution_nodes st"
    using g n e2 nl eq by simp
  have p3: "resolution_witnesses (shared_state_project (share_resolution_state P st)) = resolution_witnesses st"
    using g n e2 eq by simp
  show "shared_state_project (share_resolution_state P st) = st"
    using p1 p2 p3 by (cases "shared_state_project (share_resolution_state P st)", cases st) simp
qed

end
