theory Shared_Term_Tables
  imports Keyed_Value_References Tree_Map_Indexes Ordered_Finite_Terms Keyed_Demanded_Sites
    Prefix_Key_Comparisons
begin

section \<open>A term over the shared subterms of a family of terms\<close>

text \<open>
  This is the notion stated in DECISIONS.md, "An evaluation's calls are built over the shared subterms of
  its requests", checked. Given a finite family of terms, its \emph{table} is the first-occurrence table
  of the family's distinct subterms, each held as its \emph{shape}: a payload leaf, a target leaf, or the
  pair of the references of its two components; a \emph{reference} is a shape's position in the table.
  A formed table is subterm-closed (a held pair's components are held, at smaller positions) and holds
  each shape once. A \emph{shared term} over a table is a reference, or a leaf or a pair the table does
  not hold, whose components are shared terms; it is \emph{canonical} when every subterm the table holds
  is present as its reference. \emph{Decoding} reads a shared term as the term it presents; the
  \emph{canonical constructors} build a leaf or a pair and look its shape up in the table's index of
  shapes; the \emph{view} is a shared term's top constructor, read through the table at a reference.

  The contract is four obligations, as the index notion's is: (1) the table presents its family
  (@{text share_term_exact}, @{text share_terms_exact}, @{text share_term_preserves}); (2) two canonical
  shared terms over one formed table are equal exactly when they decode to equal terms
  (@{text shared_canonical_equality}); (3) the canonical constructors return canonical shared terms and
  commute with decoding, and the components of a canonical shared term are canonical
  (@{text shared_leaf_exact}, @{text shared_pair_exact}, @{text shared_canonical_components});
  (4) the view commutes with decoding and keeps canonicity (@{text shared_view_decode},
  @{text shared_view_canonical}). The order on shared terms compares a reference as a number
  (@{text compare_shared_references}); it is a key with the identity as its left inverse
  (@{text shared_call_demanded_sites}), and no subject reads it.

  The notion instantiates what exists. The table is @{text Complete_Value_References}' first-occurrence
  table over shapes: sharing a term is its step (@{const value_reference_step}) at every node, a pair's
  shape naming the references its components have just received, and the build is
  @{text Keyed_Value_References}' keyed step, a lookup of the shape's key in an ordered tree and an
  insertion where it is absent, threaded through the terms' structure, since a run over a fixed list
  cannot supply the references a pair's shape names. That step is stated once, generic in the value and an
  injective key (@{text keyed_reference_step}, @{text keyed_reference_step_exact}): its insertion is the
  index notion's update (@{text tree_map_updates}) at the first-occurrence table (@{text keyed_reference_insert}),
  and the build takes it at the shape key. The index of shapes is a carrier index
  through the red-black tree's instance (@{text shape_carrier_index}); a target leaf's shape is keyed by
  the order of @{text Ordered_Finite_Terms}.

  What it does not claim. Which reference a subterm receives: the first occurrence depends on the order
  of sharing, so no reference is a subject, none is presented, and none is compared across two tables;
  each evaluation builds its own. That structure built during an evaluation is shared: the table is fixed
  at its family, and a node it does not hold stays explicit structure, canonical over the fixed table.
  Anything of cost: the table's build and what it saves are observations of a use.
\<close>

subsection \<open>Leaves and shapes\<close>

datatype factor_leaf = Payload_Leaf octets | Target_Leaf finite_exact_target

fun leaf_term :: "factor_leaf \<Rightarrow> finite_factor_term" where
  "leaf_term (Payload_Leaf v)=Finite_Payload v"
| "leaf_term (Target_Leaf a)=Finite_Target a"

lemma leaf_term_injective: "leaf_term l=leaf_term m \<longleftrightarrow> l=m"
  by (cases l; cases m) simp_all

lemma leaf_term_not_pair: "leaf_term l\<noteq>Finite_Pair x y" "Finite_Pair x y\<noteq>leaf_term l"
  by (cases l; simp)+

datatype shape = Leaf_Shape factor_leaf | Pair_Shape nat nat

type_synonym shape_order_key = "ordered_factor_term option \<times> nat \<times> nat"

fun shape_key :: "shape \<Rightarrow> shape_order_key" where
  "shape_key (Leaf_Shape l)=(Some (Ordered_Factor_Term (leaf_term l)),0,0)"
| "shape_key (Pair_Shape i j)=(None,i,j)"

lemma shape_key_injective: "inj shape_key"
proof (rule injI)
  fix s u assume "shape_key s=shape_key u"
  then show "s=u" by (cases s; cases u) (simp_all add: leaf_term_injective)
qed

subsection \<open>Reading a table\<close>

lemma read_some: "value_reference_read T i=Some s \<longleftrightarrow> i<length T \<and> T!i=s"
  by (simp add: value_reference_read_def)

lemma read_member: "value_reference_read T i=Some s \<Longrightarrow> s\<in>set T"
  by (auto simp: read_some)

lemma read_same_position:
  assumes "distinct T" "value_reference_read T i=Some s" "value_reference_read T j=Some s"
  shows "i=j"
  using assms nth_eq_iff_index_eq[of T i j] by (auto simp: read_some)

definition pair_decoded :: "finite_factor_term option \<Rightarrow> finite_factor_term option \<Rightarrow> finite_factor_term option" where
  "pair_decoded a b=(case a of None \<Rightarrow> None | Some x \<Rightarrow> (case b of None \<Rightarrow> None | Some y \<Rightarrow> Some (Finite_Pair x y)))"

lemma pair_decoded_some:
  "pair_decoded a b=Some t \<longleftrightarrow> (\<exists>x y. a=Some x \<and> b=Some y \<and> t=Finite_Pair x y)"
  by (auto simp: pair_decoded_def split: option.splits)

lemma pair_decoded_some_eq:
  "Some t=pair_decoded a b \<longleftrightarrow> (\<exists>x y. a=Some x \<and> b=Some y \<and> t=Finite_Pair x y)"
  by (auto simp: pair_decoded_def split: option.splits)

function reference_term :: "shape list \<Rightarrow> nat \<Rightarrow> finite_factor_term option" where
  "reference_term T i=(case value_reference_read T i of None \<Rightarrow> None
    | Some (Leaf_Shape l) \<Rightarrow> Some (leaf_term l)
    | Some (Pair_Shape j k) \<Rightarrow> (if j<i \<and> k<i then pair_decoded (reference_term T j) (reference_term T k) else None))"
  by pat_completeness auto
termination by (relation "measure snd") auto

declare reference_term.simps [simp del]

lemma reference_factor_leaf:
  "value_reference_read T i=Some (Leaf_Shape l) \<Longrightarrow> reference_term T i=Some (leaf_term l)"
  by (simp add: reference_term.simps[of T i])

lemma reference_term_pair:
  "value_reference_read T i=Some (Pair_Shape j k) \<Longrightarrow> j<i \<Longrightarrow> k<i \<Longrightarrow>
    reference_term T i=pair_decoded (reference_term T j) (reference_term T k)"
  by (simp add: reference_term.simps[of T i])

lemma reference_term_cases:
  assumes decoded: "reference_term T i=Some t"
  obtains (leaf) l where "value_reference_read T i=Some (Leaf_Shape l)" "t=leaf_term l"
  | (pair) j k x y where "value_reference_read T i=Some (Pair_Shape j k)" "j<i" "k<i"
      "reference_term T j=Some x" "reference_term T k=Some y" "t=Finite_Pair x y"
proof (cases "value_reference_read T i")
  case None
  then show ?thesis using decoded by (simp add: reference_term.simps[of T i])
next
  case (Some s)
  show ?thesis
  proof (cases s)
    case (Leaf_Shape l)
    have "t=leaf_term l" using decoded Some Leaf_Shape by (simp add: reference_term.simps[of T i])
    then show ?thesis using leaf Some Leaf_Shape by blast
  next
    case (Pair_Shape j k)
    have ordered: "j<i \<and> k<i"
      using decoded Some Pair_Shape by (simp add: reference_term.simps[of T i] split: if_splits)
    have "pair_decoded (reference_term T j) (reference_term T k)=Some t"
      using decoded Some Pair_Shape ordered by (simp add: reference_term.simps[of T i])
    then obtain x y where "reference_term T j=Some x" "reference_term T k=Some y" "t=Finite_Pair x y"
      by (auto simp: pair_decoded_some)
    then show ?thesis using pair Some Pair_Shape ordered by blast
  qed
qed

lemma reference_term_bound: "reference_term T i=Some t \<Longrightarrow> i<length T"
  by (erule reference_term_cases) (simp_all add: read_some)

lemma reference_factor_leaf_read:
  assumes "reference_term T i=Some (leaf_term l)"
  shows "value_reference_read T i=Some (Leaf_Shape l)"
  using assms by (cases rule: reference_term_cases) (auto simp: leaf_term_injective leaf_term_not_pair)

text \<open>
  Decoding reads only positions, so whatever keeps every read keeps every decoding: the first-occurrence
  law (@{thm [source] value_reference_step_preserves}) is what a sharing that adds terms consumes.
\<close>

lemma reference_term_preserved:
  assumes reads: "\<And>j s. value_reference_read T j=Some s \<Longrightarrow> value_reference_read T' j=Some s"
  shows "reference_term T i=Some t \<Longrightarrow> reference_term T' i=Some t"
proof (induction t arbitrary: i)
  case (Finite_Pair x y)
  from Finite_Pair.prems show ?case
  proof (cases rule: reference_term_cases)
    case (leaf l)
    then show ?thesis by (simp add: leaf_term_not_pair)
  next
    case (pair j k x' y')
    have xy: "x'=x" "y'=y" using pair(6) by simp_all
    have "reference_term T' j=Some x" using Finite_Pair.IH(1)[of j] pair(4) xy by simp
    moreover have "reference_term T' k=Some y" using Finite_Pair.IH(2)[of k] pair(5) xy by simp
    ultimately show ?thesis using reference_term_pair[OF reads[OF pair(1)] pair(2,3)] by (simp add: pair_decoded_def)
  qed
next
  case (Finite_Payload v)
  have "reference_term T i=Some (leaf_term (Payload_Leaf v))" using Finite_Payload.prems by simp
  then have "value_reference_read T' i=Some (Leaf_Shape (Payload_Leaf v))" by (rule reads[OF reference_factor_leaf_read])
  then show ?case using reference_factor_leaf by fastforce
next
  case (Finite_Target a)
  have "reference_term T i=Some (leaf_term (Target_Leaf a))" using Finite_Target.prems by simp
  then have "value_reference_read T' i=Some (Leaf_Shape (Target_Leaf a))" by (rule reads[OF reference_factor_leaf_read])
  then show ?case using reference_factor_leaf by fastforce
qed

subsection \<open>A formed table: subterm-closed, each shape once\<close>

definition table_formed :: "shape list \<Rightarrow> bool" where
  "table_formed T \<longleftrightarrow> distinct T \<and> (\<forall>i j k. value_reference_read T i=Some (Pair_Shape j k) \<longrightarrow> j<i \<and> k<i)"

lemma table_formed_empty: "table_formed []"
  by (simp add: table_formed_def value_reference_read_def)

lemma table_formed_decodes:
  assumes formed: "table_formed T" and bound: "i<length T"
  shows "\<exists>t. reference_term T i=Some t"
  using bound
proof (induction i rule: less_induct)
  case (less i)
  show ?case
  proof (cases "T!i")
    case (Leaf_Shape l)
    have "value_reference_read T i=Some (Leaf_Shape l)" using less.prems Leaf_Shape by (simp add: read_some)
    then show ?thesis by (auto dest: reference_factor_leaf)
  next
    case (Pair_Shape j k)
    have read: "value_reference_read T i=Some (Pair_Shape j k)" using less.prems Pair_Shape by (simp add: read_some)
    have jk: "j<i" "k<i" using formed read by (auto simp: table_formed_def)
    obtain x where x: "reference_term T j=Some x" using less.IH[OF jk(1)] jk(1) less.prems by auto
    obtain y where y: "reference_term T k=Some y" using less.IH[OF jk(2)] jk(2) less.prems by auto
    show ?thesis using reference_term_pair[OF read jk] x y by (simp add: pair_decoded_def)
  qed
qed

lemma reference_term_injective:
  assumes formed: "table_formed T"
  shows "reference_term T i=Some t \<Longrightarrow> reference_term T j=Some t \<Longrightarrow> i=j"
proof (induction t arbitrary: i j)
  case (Finite_Pair x y)
  from Finite_Pair.prems(1) obtain a b where ri: "value_reference_read T i=Some (Pair_Shape a b)"
      and xa: "reference_term T a=Some x" and yb: "reference_term T b=Some y"
    by (cases rule: reference_term_cases) (auto simp: leaf_term_not_pair)
  from Finite_Pair.prems(2) obtain c d where rj: "value_reference_read T j=Some (Pair_Shape c d)"
      and xc: "reference_term T c=Some x" and yd: "reference_term T d=Some y"
    by (cases rule: reference_term_cases) (auto simp: leaf_term_not_pair)
  have "a=c" by (rule Finite_Pair.IH(1)[OF xa xc])
  moreover have "b=d" by (rule Finite_Pair.IH(2)[OF yb yd])
  moreover have "distinct T" using formed by (simp add: table_formed_def)
  ultimately show ?case using read_same_position[of T i "Pair_Shape a b" j] ri rj by simp
next
  case (Finite_Payload v)
  have "value_reference_read T i=Some (Leaf_Shape (Payload_Leaf v))"
    "value_reference_read T j=Some (Leaf_Shape (Payload_Leaf v))"
    using Finite_Payload.prems reference_factor_leaf_read[of T _ "Payload_Leaf v"] by simp_all
  then show ?case using formed by (metis read_same_position table_formed_def)
next
  case (Finite_Target a)
  have "value_reference_read T i=Some (Leaf_Shape (Target_Leaf a))"
    "value_reference_read T j=Some (Leaf_Shape (Target_Leaf a))"
    using Finite_Target.prems reference_factor_leaf_read[of T _ "Target_Leaf a"] by simp_all
  then show ?case using formed by (metis read_same_position table_formed_def)
qed

subsection \<open>Sharing a family: the first-occurrence table over shapes\<close>

fun share_term :: "finite_factor_term \<Rightarrow> shape list \<Rightarrow> nat \<times> shape list" where
  "share_term (Finite_Pair t u) T=(case share_term t T of (i,T1) \<Rightarrow>
    (case share_term u T1 of (j,T2) \<Rightarrow> value_reference_step (Pair_Shape i j) T2))"
| "share_term (Finite_Payload v) T=value_reference_step (Leaf_Shape (Payload_Leaf v)) T"
| "share_term (Finite_Target a) T=value_reference_step (Leaf_Shape (Target_Leaf a)) T"

fun share_terms :: "finite_factor_term list \<Rightarrow> shape list \<Rightarrow> nat list \<times> shape list" where
  "share_terms [] T=([],T)"
| "share_terms (t#ts) T=(case share_term t T of (i,T1) \<Rightarrow> (case share_terms ts T1 of (is,T2) \<Rightarrow> (i#is,T2)))"

definition shared_table :: "finite_factor_term list \<Rightarrow> shape list" where
  "shared_table ts=snd (share_terms ts [])"

lemma share_term_reads:
  "value_reference_read T j=Some s \<Longrightarrow> value_reference_read (snd (share_term t T)) j=Some s"
proof (induction t arbitrary: T)
  case (Finite_Pair t u)
  obtain i T1 where first: "share_term t T=(i,T1)" by (cases "share_term t T")
  obtain k T2 where second: "share_term u T1=(k,T2)" by (cases "share_term u T1")
  have "value_reference_read T1 j=Some s" using Finite_Pair.IH(1)[OF Finite_Pair.prems] first by simp
  then have "value_reference_read T2 j=Some s" using Finite_Pair.IH(2) second by fastforce
  then show ?case using value_reference_step_preserves by (simp add: first second)
qed (simp_all add: value_reference_step_preserves)

lemma share_terms_reads:
  "value_reference_read T j=Some s \<Longrightarrow> value_reference_read (snd (share_terms ts T)) j=Some s"
proof (induction ts arbitrary: T)
  case (Cons t ts)
  obtain i T1 where first: "share_term t T=(i,T1)" by (cases "share_term t T")
  have "value_reference_read T1 j=Some s" using share_term_reads[OF Cons.prems, of t] first by simp
  then show ?case using Cons.IH by (simp add: first case_prod_unfold)
qed simp

theorem share_term_preserves:
  "reference_term T i=Some u \<Longrightarrow> reference_term (snd (share_term t T)) i=Some u"
  by (rule reference_term_preserved[OF share_term_reads])

theorem share_terms_preserves:
  "reference_term T i=Some u \<Longrightarrow> reference_term (snd (share_terms ts T)) i=Some u"
  by (rule reference_term_preserved[OF share_terms_reads])

lemma share_step_formed:
  assumes formed: "table_formed T" and closed: "\<And>j k. s=Pair_Shape j k \<Longrightarrow> j<length T \<and> k<length T"
  shows "table_formed (snd (value_reference_step s T))"
proof -
  have distinct: "distinct (snd (value_reference_step s T))"
    using value_reference_step_distinct[of T s] formed by (simp add: table_formed_def)
  have closure: "j<i \<and> k<i" if read: "value_reference_read (snd (value_reference_step s T)) i=Some (Pair_Shape j k)" for i j k
  proof (cases "s\<in>set T")
    case True
    then have "snd (value_reference_step s T)=T" by (simp add: value_reference_step_table value_reference_add_def)
    then show ?thesis using formed read by (simp add: table_formed_def)
  next
    case False
    then have appended: "snd (value_reference_step s T)=T@[s]" by (simp add: value_reference_step_table value_reference_add_def)
    show ?thesis
    proof (cases "i<length T")
      case True
      then have "value_reference_read T i=Some (Pair_Shape j k)" using read appended by (simp add: read_some nth_append)
      then show ?thesis using formed by (simp add: table_formed_def)
    next
      case False
      then have "i=length T" "s=Pair_Shape j k" using read appended by (auto simp: read_some nth_append)
      then show ?thesis using closed by simp
    qed
  qed
  show ?thesis using distinct closure by (auto simp: table_formed_def)
qed

lemma share_leaf_exact:
  assumes formed: "table_formed T"
  shows "table_formed (snd (value_reference_step (Leaf_Shape l) T)) \<and>
    reference_term (snd (value_reference_step (Leaf_Shape l) T)) (fst (value_reference_step (Leaf_Shape l) T))=
      Some (leaf_term l)"
proof -
  have "table_formed (snd (value_reference_step (Leaf_Shape l) T))" by (rule share_step_formed[OF formed]) simp
  moreover have "reference_term (snd (value_reference_step (Leaf_Shape l) T)) (fst (value_reference_step (Leaf_Shape l) T))=
      Some (leaf_term l)" by (rule reference_factor_leaf) (rule value_reference_step_exact)
  ultimately show ?thesis by simp
qed

theorem share_term_exact:
  "table_formed T \<Longrightarrow> table_formed (snd (share_term t T)) \<and>
    reference_term (snd (share_term t T)) (fst (share_term t T))=Some t"
proof (induction t arbitrary: T)
  case (Finite_Pair t u)
  obtain i T1 where first: "share_term t T=(i,T1)" by (cases "share_term t T")
  obtain j T2 where second: "share_term u T1=(j,T2)" by (cases "share_term u T1")
  have f1: "table_formed T1" and r1: "reference_term T1 i=Some t"
    using Finite_Pair.IH(1)[OF Finite_Pair.prems] first by simp_all
  have f2: "table_formed T2" and r2: "reference_term T2 j=Some u"
    using Finite_Pair.IH(2)[OF f1] second by simp_all
  have r1': "reference_term T2 i=Some t" using share_term_preserves[OF r1, of u] second by simp
  obtain k T3 where step: "value_reference_step (Pair_Shape i j) T2=(k,T3)"
    by (cases "value_reference_step (Pair_Shape i j) T2")
  have f3: "table_formed T3"
    using share_step_formed[OF f2, of "Pair_Shape i j"] reference_term_bound[OF r1'] reference_term_bound[OF r2] step by simp
  have read: "value_reference_read T3 k=Some (Pair_Shape i j)"
    using value_reference_step_exact[of "Pair_Shape i j" T2] step by simp
  have ordered: "i<k" "j<k" using f3 read by (auto simp: table_formed_def)
  have reads3: "value_reference_read T3 p=Some s'" if "value_reference_read T2 p=Some s'" for p s'
    using value_reference_step_preserves[OF that, of "Pair_Shape i j"] step by simp
  have "reference_term T3 i=Some t" "reference_term T3 j=Some u"
    using reference_term_preserved[OF reads3] r1' r2 by simp_all
  then show ?case using f3 reference_term_pair[OF read ordered] by (simp add: first second step pair_decoded_def)
next
  case (Finite_Payload v)
  then show ?case using share_leaf_exact[OF Finite_Payload.prems, of "Payload_Leaf v"] by simp
next
  case (Finite_Target a)
  then show ?case using share_leaf_exact[OF Finite_Target.prems, of "Target_Leaf a"] by simp
qed

theorem share_terms_exact:
  "table_formed T \<Longrightarrow> table_formed (snd (share_terms ts T)) \<and>
    map (reference_term (snd (share_terms ts T))) (fst (share_terms ts T))=map Some ts"
proof (induction ts arbitrary: T)
  case (Cons t ts)
  obtain i T1 where first: "share_term t T=(i,T1)" by (cases "share_term t T")
  have f1: "table_formed T1" and r1: "reference_term T1 i=Some t"
    using share_term_exact[OF Cons.prems, of t] first by simp_all
  have "reference_term (snd (share_terms ts T1)) i=Some t" by (rule share_terms_preserves[OF r1])
  then show ?case using Cons.IH[OF f1] by (simp add: first case_prod_unfold)
qed simp

theorem shared_table_presents:
  "table_formed (shared_table ts) \<and> map (reference_term (shared_table ts)) (fst (share_terms ts []))=map Some ts"
  using share_terms_exact[OF table_formed_empty, of ts] by (simp add: shared_table_def)

subsection \<open>The index of shapes is a carrier index\<close>

definition shape_rows :: "shape list \<Rightarrow> (shape_order_key\<times>nat) list" where
  "shape_rows T=zip (map shape_key T) [0..<length T]"

lemma shape_rows_member: "(k,i)\<in>set (shape_rows T) \<longleftrightarrow> i<length T \<and> shape_key (T!i)=k"
proof
  assume "(k,i)\<in>set (shape_rows T)"
  then show "i<length T \<and> shape_key (T!i)=k" by (auto simp: shape_rows_def in_set_zip)
next
  assume "i<length T \<and> shape_key (T!i)=k"
  then show "(k,i)\<in>set (shape_rows T)" unfolding shape_rows_def in_set_zip by (intro exI[of _ i]) simp
qed

definition shape_index :: "shape list \<Rightarrow> (shape_order_key,nat) rbt" where
  "shape_index T=RBT.bulkload (shape_rows T)"

lemma shape_carrier_index:
  "carrier_index (\<lambda>T s i. value_reference_read T i=Some s) distinct (UNIV::shape set) shape_key shape_index tree_search"
proof -
  have "carrier_index (\<lambda>T s i. value_reference_read T i=Some s) distinct (UNIV::shape set) shape_key
      (\<lambda>T. RBT.bulkload (shape_rows T)) tree_search"
    apply (rule carrier_index_through_key[OF tree_map_carrier_index])
      apply (simp add: shape_rows_def distinct_map inj_on_subset[OF shape_key_injective subset_UNIV])
     apply (auto simp: shape_rows_member read_some)[1]
    apply (rule shape_key_injective)
    done
  then show ?thesis by (simp only: shape_index_def[abs_def])
qed

interpretation shape_indexes: carrier_index "\<lambda>T s i. value_reference_read T i=Some s" distinct "UNIV::shape set"
  shape_key shape_index tree_search
  by (rule shape_carrier_index)

lemma shape_index_lookup:
  assumes distinct: "distinct T"
  shows "RBT.lookup (shape_index T) (shape_key s)=value_reference_index s T"
proof -
  have found: "RBT.lookup (shape_index T) (shape_key s)=Some i \<longleftrightarrow> value_reference_read T i=Some s" for i
    by (rule shape_indexes.query_search[OF distinct UNIV_I])
  have first: "value_reference_index s T=Some i \<longleftrightarrow> value_reference_read T i=Some s" for i
  proof
    assume "value_reference_index s T=Some i"
    then show "value_reference_read T i=Some s" using value_reference_index_read by (simp add: read_some)
  next
    assume "value_reference_read T i=Some s"
    then show "value_reference_index s T=Some i" by (rule value_reference_index_distinct_read[OF distinct])
  qed
  show ?thesis by (metis found first option.exhaust)
qed

subsection \<open>The build: the keyed step threaded through the terms\<close>

type_synonym share_state = "(shape_order_key,nat) rbt \<times> nat \<times> shape list"

text \<open>
  The keyed first-occurrence step, for any value and injective key: the table is kept reversed with its
  length, and an ordered tree maps the key of every held value to its first position. Inserting an absent
  value's key at the table's length is the index notion's update at the first-occurrence table.
\<close>

definition keyed_reference_step ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a \<Rightarrow> ('k,nat) rbt\<times>nat\<times>'a list \<Rightarrow> nat\<times>(('k,nat) rbt\<times>nat\<times>'a list)" where
  "keyed_reference_step key x q=(case q of (M,n,R) \<Rightarrow> (case RBT.lookup M (key x) of
    Some i \<Rightarrow> (i,q) | None \<Rightarrow> (n,(RBT.insert (key x) n M,Suc n,x#R))))"

definition keyed_reference_state :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,nat) rbt\<times>nat\<times>'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "keyed_reference_state key q T \<longleftrightarrow> (case q of (M,n,R) \<Rightarrow> n=length T \<and> R=rev T \<and>
    (\<forall>y. RBT.lookup M (key y)=value_reference_index y T))"

lemma keyed_reference_insert:
  assumes key: "inj key" and index: "\<And>y. RBT.lookup M (key y)=value_reference_index y T"
    and absent: "value_reference_index x T=None"
  shows "RBT.lookup (RBT.insert (key x) (length T) M) (key y)=value_reference_index y (T@[x])"
proof -
  have "RBT.lookup (RBT.insert (key x) (length T) M) (key y)=Some v \<longleftrightarrow> value_reference_index y (T@[x])=Some v" for v
  proof (cases "y=x")
    case True
    then show ?thesis using tree_map_updates.updated[where i=M and k="key x" and u="length T" and k'="key y" and v=v] absent
      by (simp add: value_reference_index_snoc)
  next
    case False
    then have "key y\<noteq>key x" using key by (auto dest: injD)
    then show ?thesis using tree_map_updates.updated[where i=M and k="key x" and u="length T" and k'="key y" and v=v] index[of y] False
      by (simp add: value_reference_index_snoc split: option.splits)
  qed
  then show ?thesis by (metis option.exhaust)
qed

lemma keyed_reference_step_exact:
  assumes key: "inj key" and rep: "keyed_reference_state key q T"
  shows "fst (keyed_reference_step key x q)=fst (value_reference_step x T) \<and>
    keyed_reference_state key (snd (keyed_reference_step key x q)) (snd (value_reference_step x T))"
proof -
  obtain M n R where q: "q=(M,n,R)" by (cases q) auto
  have n: "n=length T" and R: "R=rev T" and index: "\<And>y. RBT.lookup M (key y)=value_reference_index y T"
    using rep by (simp_all add: q keyed_reference_state_def)
  show ?thesis
  proof (cases "value_reference_index x T")
    case (Some i)
    then show ?thesis using rep index[of x] by (simp add: q keyed_reference_step_def value_reference_step_def)
  next
    case None
    have moved: "RBT.lookup (RBT.insert (key x) n M) (key y)=value_reference_index y (T@[x])" for y
      using keyed_reference_insert[OF key index None] n by simp
    show ?thesis using None index[of x] n R moved
      by (simp add: q keyed_reference_step_def value_reference_step_def keyed_reference_state_def)
  qed
qed

definition keyed_share_shape :: "shape \<Rightarrow> share_state \<Rightarrow> nat \<times> share_state" where
  "keyed_share_shape=keyed_reference_step shape_key"

fun keyed_share_term :: "finite_factor_term \<Rightarrow> share_state \<Rightarrow> nat \<times> share_state" where
  "keyed_share_term (Finite_Pair t u) q=(case keyed_share_term t q of (i,q1) \<Rightarrow>
    (case keyed_share_term u q1 of (j,q2) \<Rightarrow> keyed_share_shape (Pair_Shape i j) q2))"
| "keyed_share_term (Finite_Payload v) q=keyed_share_shape (Leaf_Shape (Payload_Leaf v)) q"
| "keyed_share_term (Finite_Target a) q=keyed_share_shape (Leaf_Shape (Target_Leaf a)) q"

fun keyed_share_terms :: "finite_factor_term list \<Rightarrow> share_state \<Rightarrow> nat list \<times> share_state" where
  "keyed_share_terms [] q=([],q)"
| "keyed_share_terms (t#ts) q=(case keyed_share_term t q of (i,q1) \<Rightarrow>
    (case keyed_share_terms ts q1 of (is,q2) \<Rightarrow> (i#is,q2)))"

definition keyed_state_represents :: "share_state \<Rightarrow> shape list \<Rightarrow> bool" where
  "keyed_state_represents=keyed_reference_state shape_key"

lemma keyed_share_shape_exact:
  assumes rep: "keyed_state_represents q T"
  shows "fst (keyed_share_shape s q)=fst (value_reference_step s T) \<and>
    keyed_state_represents (snd (keyed_share_shape s q)) (snd (value_reference_step s T))"
  using keyed_reference_step_exact[OF shape_key_injective, where q=q and T=T and x=s] rep
  by (simp add: keyed_share_shape_def keyed_state_represents_def keyed_reference_state_def)

lemma keyed_share_term_exact:
  "keyed_state_represents q T \<Longrightarrow> fst (keyed_share_term t q)=fst (share_term t T) \<and>
    keyed_state_represents (snd (keyed_share_term t q)) (snd (share_term t T))"
proof (induction t arbitrary: q T)
  case (Finite_Pair t u)
  obtain i q1 where k1: "keyed_share_term t q=(i,q1)" by (cases "keyed_share_term t q")
  obtain i' T1 where s1: "share_term t T=(i',T1)" by (cases "share_term t T")
  have e1: "i=i'" and r1: "keyed_state_represents q1 T1"
    using Finite_Pair.IH(1)[OF Finite_Pair.prems] k1 s1 by simp_all
  obtain j q2 where k2: "keyed_share_term u q1=(j,q2)" by (cases "keyed_share_term u q1")
  obtain j' T2 where s2: "share_term u T1=(j',T2)" by (cases "share_term u T1")
  have e2: "j=j'" and r2: "keyed_state_represents q2 T2" using Finite_Pair.IH(2)[OF r1] k2 s2 by simp_all
  show ?case using keyed_share_shape_exact[OF r2, of "Pair_Shape i j"] by (simp add: k1 s1 k2 s2 e1 e2)
qed (simp_all add: keyed_share_shape_exact)

lemma keyed_share_terms_exact:
  "keyed_state_represents q T \<Longrightarrow> fst (keyed_share_terms ts q)=fst (share_terms ts T) \<and>
    keyed_state_represents (snd (keyed_share_terms ts q)) (snd (share_terms ts T))"
proof (induction ts arbitrary: q T)
  case (Cons t ts)
  obtain i q1 where k1: "keyed_share_term t q=(i,q1)" by (cases "keyed_share_term t q")
  obtain i' T1 where s1: "share_term t T=(i',T1)" by (cases "share_term t T")
  have e1: "i=i'" and r1: "keyed_state_represents q1 T1"
    using keyed_share_term_exact[OF Cons.prems, of t] k1 s1 by simp_all
  show ?case using Cons.IH[OF r1] by (simp add: k1 s1 e1 case_prod_unfold)
qed simp

definition keyed_shared_family ::
  "finite_factor_term list \<Rightarrow> nat list \<times> shape list \<times> (shape_order_key,nat) rbt" where
  "keyed_shared_family ts=(case keyed_share_terms ts (RBT.empty,0,[]) of (is,(M,n,R)) \<Rightarrow> (is,rev R,M))"

theorem keyed_shared_family_exact:
  assumes built: "keyed_shared_family ts=(is,T,M)"
  shows "(is,T)=share_terms ts [] \<and> (\<forall>s. RBT.lookup M (shape_key s)=value_reference_index s T)"
proof -
  have start: "keyed_state_represents (RBT.empty,0,[]) []" by (simp add: keyed_state_represents_def keyed_reference_state_def)
  obtain is' M' n R where run: "keyed_share_terms ts (RBT.empty,0,[])=(is',(M',n,R))"
    by (cases "keyed_share_terms ts (RBT.empty,0,[])") auto
  have fields: "is=is'" "T=rev R" "M=M'" using built run by (simp_all add: keyed_shared_family_def)
  show ?thesis using keyed_share_terms_exact[OF start, of ts] run fields
    by (cases "share_terms ts []") (simp add: keyed_state_represents_def keyed_reference_state_def)
qed

corollary keyed_shared_family_index:
  assumes built: "keyed_shared_family ts=(is,T,M)"
  shows "RBT.lookup M (shape_key s)=RBT.lookup (shape_index T) (shape_key s)"
proof -
  have "T=shared_table ts" using keyed_shared_family_exact[OF built] by (simp add: shared_table_def prod_eq_iff)
  then have "distinct T" using shared_table_presents[of ts] by (simp add: table_formed_def)
  then show ?thesis using keyed_shared_family_exact[OF built] shape_index_lookup by simp
qed

lemma shared_table_code [code]: "shared_table ts=fst (snd (keyed_shared_family ts))"
  using keyed_shared_family_exact[of ts]
  by (cases "keyed_shared_family ts") (auto simp: shared_table_def prod_eq_iff)

subsection \<open>Shared terms, canonicity and decoding\<close>

datatype shared_term = Shared_Reference nat | Shared_Leaf factor_leaf | Shared_Pair shared_term shared_term

fun shared_decode :: "shape list \<Rightarrow> shared_term \<Rightarrow> finite_factor_term option" where
  "shared_decode T (Shared_Reference i)=reference_term T i"
| "shared_decode T (Shared_Leaf l)=Some (leaf_term l)"
| "shared_decode T (Shared_Pair a b)=pair_decoded (shared_decode T a) (shared_decode T b)"

fun shared_canonical :: "shape list \<Rightarrow> shared_term \<Rightarrow> bool" where
  "shared_canonical T (Shared_Reference i)\<longleftrightarrow>i<length T"
| "shared_canonical T (Shared_Leaf l)\<longleftrightarrow>Leaf_Shape l\<notin>set T"
| "shared_canonical T (Shared_Pair a b)\<longleftrightarrow>shared_canonical T a \<and> shared_canonical T b \<and>
    (\<forall>i j. a=Shared_Reference i \<longrightarrow> b=Shared_Reference j \<longrightarrow> Pair_Shape i j\<notin>set T)"

lemma shared_canonical_components:
  "shared_canonical T (Shared_Pair a b) \<Longrightarrow> shared_canonical T a \<and> shared_canonical T b"
  by simp

lemma canonical_decodes:
  assumes formed: "table_formed T"
  shows "shared_canonical T s \<Longrightarrow> \<exists>t. shared_decode T s=Some t"
proof (induction s)
  case (Shared_Reference i)
  then show ?case using table_formed_decodes[OF formed] by simp
next
  case (Shared_Leaf l)
  then show ?case by simp
next
  case (Shared_Pair a b)
  then show ?case by (auto simp: pair_decoded_def)
qed

text \<open>A canonical shared term whose decoded term the table holds is that term's reference.\<close>

lemma canonical_held:
  assumes formed: "table_formed T"
  shows "shared_canonical T s \<Longrightarrow> shared_decode T s=Some t \<Longrightarrow> reference_term T i=Some t \<Longrightarrow>
    s=Shared_Reference i"
proof (induction s arbitrary: t i)
  case (Shared_Reference i')
  then show ?case using reference_term_injective[OF formed, of i' t i] by simp
next
  case (Shared_Leaf l)
  have "value_reference_read T i=Some (Leaf_Shape l)"
    using Shared_Leaf.prems(2,3) reference_factor_leaf_read by simp
  then have "Leaf_Shape l\<in>set T" by (rule read_member)
  then show ?case using Shared_Leaf.prems(1) by simp
next
  case (Shared_Pair a b)
  obtain x y where ax: "shared_decode T a=Some x" and bx: "shared_decode T b=Some y" and t: "t=Finite_Pair x y"
    using Shared_Pair.prems(2) by (auto simp: pair_decoded_some)
  from Shared_Pair.prems(3)[unfolded t] obtain j k where read: "value_reference_read T i=Some (Pair_Shape j k)"
      and xj: "reference_term T j=Some x" and yk: "reference_term T k=Some y"
    by (cases rule: reference_term_cases) (auto simp: leaf_term_not_pair)
  have "a=Shared_Reference j" using Shared_Pair.IH(1)[where t=x and i=j] Shared_Pair.prems(1) ax xj by simp
  moreover have "b=Shared_Reference k" using Shared_Pair.IH(2)[where t=y and i=k] Shared_Pair.prems(1) bx yk by simp
  moreover have "Pair_Shape j k\<in>set T" using read by (rule read_member)
  ultimately show ?case using Shared_Pair.prems(1) by simp
qed

lemma canonical_reference_equality:
  assumes formed: "table_formed T" and s: "shared_canonical T s" and u: "shared_canonical T u"
    and same: "shared_decode T s=shared_decode T u" and reference: "s=Shared_Reference i"
  shows "u=Shared_Reference i"
proof -
  obtain t where t: "reference_term T i=Some t" using canonical_decodes[OF formed s] reference by auto
  show ?thesis by (rule canonical_held[OF formed u, of t]) (use same reference t in simp_all)
qed

text \<open>Obligation (2): a reference decides equality, and nothing the table holds is walked.\<close>

theorem shared_canonical_equality:
  assumes formed: "table_formed T" and s: "shared_canonical T s" and u: "shared_canonical T u"
  shows "s=u \<longleftrightarrow> shared_decode T s=shared_decode T u"
proof
  assume "s=u"
  then show "shared_decode T s=shared_decode T u" by simp
next
  show "shared_decode T s=shared_decode T u \<Longrightarrow> s=u"
    using s u
  proof (induction s arbitrary: u)
    case (Shared_Reference i)
    show ?case using canonical_reference_equality[OF formed Shared_Reference.prems(2,3,1)] by simp
  next
    case (Shared_Leaf l)
    show ?case
    proof (cases u)
      case (Shared_Reference j)
      show ?thesis using canonical_reference_equality[OF formed Shared_Leaf.prems(3,2)
          Shared_Leaf.prems(1)[symmetric] Shared_Reference] by simp
    next
      case (Shared_Leaf m)
      then show ?thesis using Shared_Leaf.prems(1) by (simp add: leaf_term_injective)
    next
      case (Shared_Pair c d)
      then show ?thesis using Shared_Leaf.prems(1) by (auto simp: pair_decoded_some_eq leaf_term_not_pair)
    qed
  next
    case (Shared_Pair a b)
    note pair_prems=Shared_Pair.prems and pair_IH=Shared_Pair.IH
    show ?case
    proof (cases u)
      case (Shared_Reference j)
      show ?thesis using canonical_reference_equality[OF formed pair_prems(3,2) pair_prems(1)[symmetric] Shared_Reference]
        by simp
    next
      case (Shared_Leaf m)
      then show ?thesis using pair_prems(1) by (auto simp: pair_decoded_some leaf_term_not_pair)
    next
      case (Shared_Pair c d)
      obtain t where t: "shared_decode T (Shared_Pair a b)=Some t" using canonical_decodes[OF formed pair_prems(2)] by auto
      obtain x y where ax: "shared_decode T a=Some x" and bx: "shared_decode T b=Some y" and txy: "t=Finite_Pair x y"
        using t by (auto simp: pair_decoded_some)
      have tu: "shared_decode T (Shared_Pair c d)=Some t" using t pair_prems(1) Shared_Pair by simp
      obtain x' y' where cx: "shared_decode T c=Some x'" and dx: "shared_decode T d=Some y'" and txy': "t=Finite_Pair x' y'"
        using tu by (auto simp: pair_decoded_some)
      have "a=c" using pair_IH(1)[of c] pair_prems(2,3) Shared_Pair ax cx txy txy' by simp
      moreover have "b=d" using pair_IH(2)[of d] pair_prems(2,3) Shared_Pair bx dx txy txy' by simp
      ultimately show ?thesis using Shared_Pair by simp
    qed
  qed
qed

subsection \<open>The canonical constructors\<close>

definition table_find :: "shape list \<Rightarrow> shape \<Rightarrow> nat option" where
  "table_find T s=value_reference_index s T"

definition shared_leaf :: "(shape \<Rightarrow> nat option) \<Rightarrow> factor_leaf \<Rightarrow> shared_term" where
  "shared_leaf look l=(case look (Leaf_Shape l) of Some i \<Rightarrow> Shared_Reference i | None \<Rightarrow> Shared_Leaf l)"

fun shared_pair :: "(shape \<Rightarrow> nat option) \<Rightarrow> shared_term \<Rightarrow> shared_term \<Rightarrow> shared_term" where
  "shared_pair look (Shared_Reference i) (Shared_Reference j)=(case look (Pair_Shape i j) of
    Some k \<Rightarrow> Shared_Reference k | None \<Rightarrow> Shared_Pair (Shared_Reference i) (Shared_Reference j))"
| "shared_pair look a b=Shared_Pair a b"

text \<open>
  The constructors look a shape up through any search; the table's own search is @{const table_find},
  and the built index (@{text keyed_shared_family_find}) is that search.
\<close>

lemma keyed_shared_family_find:
  assumes "keyed_shared_family ts=(is,T,M)"
  shows "(\<lambda>s. RBT.lookup M (shape_key s))=table_find T"
  using keyed_shared_family_exact[OF assms] by (simp add: table_find_def fun_eq_iff)

text \<open>Obligation (3): the constructors are canonical and decode homomorphically.\<close>

theorem shared_leaf_exact:
  assumes formed: "table_formed T"
  shows "shared_canonical T (shared_leaf (table_find T) l) \<and>
    shared_decode T (shared_leaf (table_find T) l)=Some (leaf_term l)"
proof (cases "value_reference_index (Leaf_Shape l) T")
  case None
  have "Leaf_Shape l\<notin>set T" using None value_reference_index_absent[of "Leaf_Shape l" T] by blast
  then show ?thesis using None by (simp add: shared_leaf_def table_find_def)
next
  case (Some i)
  have read: "value_reference_read T i=Some (Leaf_Shape l)"
    using value_reference_index_read[OF Some] by (simp add: read_some)
  show ?thesis using Some reference_factor_leaf[OF read] read by (simp add: shared_leaf_def table_find_def read_some)
qed

theorem shared_pair_exact:
  assumes formed: "table_formed T" and a: "shared_canonical T a" and b: "shared_canonical T b"
  shows "shared_canonical T (shared_pair (table_find T) a b) \<and>
    shared_decode T (shared_pair (table_find T) a b)=shared_decode T (Shared_Pair a b)"
proof (cases "\<exists>i j. a=Shared_Reference i \<and> b=Shared_Reference j")
  case True
  then obtain i j where ai: "a=Shared_Reference i" and bj: "b=Shared_Reference j" by blast
  show ?thesis
  proof (cases "value_reference_index (Pair_Shape i j) T")
    case None
    have "Pair_Shape i j\<notin>set T" using None value_reference_index_absent[of "Pair_Shape i j" T] by blast
    then show ?thesis using None a b by (simp add: ai bj table_find_def)
  next
    case (Some k)
    have read: "value_reference_read T k=Some (Pair_Shape i j)"
      using value_reference_index_read[OF Some] by (simp add: read_some)
    have ordered: "i<k" "j<k" using formed read by (auto simp: table_formed_def)
    show ?thesis using Some reference_term_pair[OF read ordered] read
      by (simp add: ai bj table_find_def read_some)
  qed
next
  case False
  then have "shared_pair (table_find T) a b=Shared_Pair a b"
    by (cases a; cases b) auto
  then show ?thesis using a b False by auto
qed

subsection \<open>The view\<close>

datatype term_view = Leaf_View factor_leaf | Pair_View shared_term shared_term

fun shared_view :: "shape list \<Rightarrow> shared_term \<Rightarrow> term_view option" where
  "shared_view T (Shared_Reference i)=(case value_reference_read T i of None \<Rightarrow> None
    | Some (Leaf_Shape l) \<Rightarrow> Some (Leaf_View l)
    | Some (Pair_Shape j k) \<Rightarrow> Some (Pair_View (Shared_Reference j) (Shared_Reference k)))"
| "shared_view T (Shared_Leaf l)=Some (Leaf_View l)"
| "shared_view T (Shared_Pair a b)=Some (Pair_View a b)"

text \<open>Obligation (4): the view decodes to the top constructor of the decoded term, and keeps canonicity.\<close>

theorem shared_view_decode:
  assumes decoded: "shared_decode T s=Some t"
  shows "(\<exists>l. shared_view T s=Some (Leaf_View l) \<and> t=leaf_term l) \<or>
    (\<exists>a b x y. shared_view T s=Some (Pair_View a b) \<and> shared_decode T a=Some x \<and>
      shared_decode T b=Some y \<and> t=Finite_Pair x y)"
proof (cases s)
  case (Shared_Reference i)
  have "reference_term T i=Some t" using decoded Shared_Reference by simp
  then show ?thesis
  proof (cases rule: reference_term_cases)
    case (leaf l)
    then show ?thesis using Shared_Reference by simp
  next
    case (pair j k x y)
    then show ?thesis using Shared_Reference by simp
  qed
next
  case (Shared_Leaf l)
  then show ?thesis using decoded by simp
next
  case (Shared_Pair a b)
  then show ?thesis using decoded by (auto simp: pair_decoded_some)
qed

theorem shared_view_canonical:
  assumes formed: "table_formed T" and canonical: "shared_canonical T s"
    and view: "shared_view T s=Some (Pair_View a b)"
  shows "shared_canonical T a \<and> shared_canonical T b"
proof (cases s)
  case (Shared_Reference i)
  obtain j k where read: "value_reference_read T i=Some (Pair_Shape j k)"
      and ab: "a=Shared_Reference j" "b=Shared_Reference k"
    using view Shared_Reference by (auto split: option.splits shape.splits)
  have "j<i" "k<i" using formed read by (auto simp: table_formed_def)
  moreover have "i<length T" using read by (simp add: read_some)
  ultimately show ?thesis using ab by simp
next
  case (Shared_Leaf l)
  then show ?thesis using view by simp
next
  case (Shared_Pair c d)
  then show ?thesis using view canonical by simp
qed

subsection \<open>The order: a reference compared as a number\<close>

type_synonym shared_atom = "nat \<times> nat \<times> ordered_factor_term option"

fun shared_head :: "shared_term \<Rightarrow> shared_atom" where
  "shared_head (Shared_Reference i)=(0,i,None)"
| "shared_head (Shared_Leaf l)=(1,0,Some (Ordered_Factor_Term (leaf_term l)))"
| "shared_head (Shared_Pair a b)=(2,0,None)"

fun shared_term_key :: "shared_term \<Rightarrow> shared_atom list" where
  "shared_term_key (Shared_Pair a b)=shared_head (Shared_Pair a b)#shared_term_key a@shared_term_key b"
| "shared_term_key (Shared_Reference i)=[shared_head (Shared_Reference i)]"
| "shared_term_key (Shared_Leaf l)=[shared_head (Shared_Leaf l)]"

text \<open>
  The key is the prefix key of the view that meets a pair's left component first
  (\<open>Prefix_Key_Comparisons\<close>): a node's head, then the keys of its children, a pair's two components and
  no child of a reference or a leaf. Its one-level equations are proved here by cases; that the key is
  prefix-free, and that the comparison below computes its order, are the notion's.
\<close>

fun shared_children :: "shared_term \<Rightarrow> shared_term list" where
  "shared_children (Shared_Pair a b)=[a,b]"
| "shared_children (Shared_Reference i)=[]"
| "shared_children (Shared_Leaf l)=[]"

lemma shared_term_view: "prefix_key shared_head shared_children shared_term_key"
proof (rule prefix_key.intro)
  fix t u
  show "shared_term_key t=shared_head t#concat (map shared_term_key (shared_children t))"
    by (cases t) simp_all
  show "length (shared_children t)=length (shared_children u)" if "shared_head t=shared_head u"
    using that by (cases t; cases u) simp_all
  show "t=u" if "shared_head t=shared_head u" and "shared_children t=shared_children u"
    using that by (cases t; cases u) (simp_all add: leaf_term_injective)
qed

interpretation shared_term_prefix_key: prefix_key shared_head shared_children shared_term_key
  by (rule shared_term_view)

lemma shared_term_key_prefix:
  "shared_term_key s@xs=shared_term_key u@ys \<Longrightarrow> s=u \<and> xs=ys"
  by (rule shared_term_prefix_key.key_prefix)

lemma shared_term_key_injective: "shared_term_key s=shared_term_key u \<longleftrightarrow> s=u"
  by (rule shared_term_prefix_key.key_injective)

instantiation shared_term :: linorder
begin

definition less_eq_shared_term :: "shared_term \<Rightarrow> shared_term \<Rightarrow> bool" where
  "less_eq_shared_term s u \<longleftrightarrow> shared_term_key s\<le>shared_term_key u"

definition less_shared_term :: "shared_term \<Rightarrow> shared_term \<Rightarrow> bool" where
  "less_shared_term s u \<longleftrightarrow> shared_term_key s<shared_term_key u"

instance
  by standard
    (auto simp: less_eq_shared_term_def less_shared_term_def less_le_not_le shared_term_key_injective
      intro: order_trans dest: order_antisym)

end

fun compare_shared_terms :: "shared_term \<Rightarrow> shared_term \<Rightarrow> linear_comparison" where
  "compare_shared_terms (Shared_Pair a b) (Shared_Pair c d)=(case compare_shared_terms a c of
    Linear_Equal \<Rightarrow> compare_shared_terms b d | r \<Rightarrow> r)"
| "compare_shared_terms s u=compare_linear (shared_head s) (shared_head u)"

text \<open>The comparison is the notion's structural comparison at the same view.\<close>

lemma compare_shared_node:
  "compare_shared_terms t u=(case compare_linear (shared_head t) (shared_head u) of
    Linear_Equal \<Rightarrow> compare_listed compare_shared_terms (shared_children t) (shared_children u) | c \<Rightarrow> c)"
  by (cases t; cases u) (auto simp: compare_linear_cases(2) split: linear_comparison.split)

interpretation shared_term_comparison:
  prefix_key_comparison shared_head shared_children shared_term_key compare_shared_terms
  by (rule prefix_key_comparison.intro[OF shared_term_view], rule prefix_key_comparison_axioms.intro,
    rule compare_shared_node)

lemma compare_shared_terms_keys:
  "compare_linear (shared_term_key s@xs) (shared_term_key u@ys)=
    (case compare_shared_terms s u of Linear_Equal \<Rightarrow> compare_linear xs ys | r \<Rightarrow> r)"
  by (rule shared_term_comparison.compare_keys)

theorem compare_shared_terms_linear: "compare_shared_terms s u=compare_linear s u"
proof -
  have keys: "compare_linear s u=compare_linear (shared_term_key s) (shared_term_key u)"
    by (simp add: compare_linear_def less_shared_term_def shared_term_key_injective)
  show ?thesis by (simp only: keys shared_term_comparison.compare_order)
qed

lemma less_shared_term_code [code]: "s<u \<longleftrightarrow> compare_shared_terms s u=Linear_Less"
  by (simp add: compare_shared_terms_linear compare_linear_cases)

lemma less_eq_shared_term_code [code]: "s\<le>u \<longleftrightarrow> compare_shared_terms s u\<noteq>Linear_Greater"
  by (simp add: compare_shared_terms_linear compare_linear_order(1))

theorem compare_shared_references:
  "compare_shared_terms (Shared_Reference i) (Shared_Reference j)=compare_linear i j"
  by (simp add: compare_linear_pair split: linear_comparison.split)

corollary shared_reference_less: "Shared_Reference i<Shared_Reference j \<longleftrightarrow> i<j"
  by (simp only: less_shared_term_code compare_shared_references compare_linear_cases(1))

text \<open>
  The key's contract: a call keyed by its site and a shared term is keyed by itself, the identity its
  left inverse, so the keyed traversal of demanded sites takes it as it takes any such key.
\<close>

theorem shared_call_demanded_sites:
  "keyed_demanded_sites (id::'a::linorder\<times>shared_term\<Rightarrow>_) id read succ roots=finite_demanded_sites read succ roots"
  by (rule keyed_demanded_sites_exact) simp


end
