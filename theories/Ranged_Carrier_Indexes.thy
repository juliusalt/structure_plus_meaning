theory Ranged_Carrier_Indexes
  imports Tree_Map_Indexes "HOL-Library.List_Lexorder"
begin

section \<open>The entries of an index in a range of its key order\<close>

text \<open>
  Task 892 (q157). A carrier indexed by an ordered key is read at a \emph{range} of the key order: the entries whose
  keys lie in it, in the order of their keys. A range is given by its two sides, the keys before it and the keys after
  it (@{text key_range}): a key before the range has only keys before the range below it, a key after it only keys after
  it above it, and a key inside is neither. The sides, not a membership test, are what the operation reads, so that a
  search skips the parts of the index wholly before or after the range. The operation is the notion's: an index read at
  a range finds exactly the pairs its search finds whose keys lie inside, in strictly increasing key order
  (@{text ranged_carrier_index}), and a carrier's content in the range is then the keyed image of what it holds there
  (@{text range_content}, @{text range_query}), stated once for every carrier interpreting it. Its tree instance reads the
  red-black tree left to right and prunes a subtree at a key before or after the range (@{text rbt_range}); a prefix of
  a list key is a range of the lexicographic order (@{text prefix_range}), so the keys under a position are read as
  one range of the positions' tree (@{text tree_prefix}).
\<close>

definition key_range :: "('k::linorder \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> bool" where
  "key_range L R \<longleftrightarrow> (\<forall>k k'. L k \<longrightarrow> k' \<le> k \<longrightarrow> L k') \<and> (\<forall>k k'. R k \<longrightarrow> k \<le> k' \<longrightarrow> R k')"

locale ranged_carrier_index = carrier_index holds formed Q key build search
  for holds :: "'c \<Rightarrow> 'q \<Rightarrow> 'v \<Rightarrow> bool" and formed :: "'c \<Rightarrow> bool" and Q :: "'q set"
    and key :: "'q \<Rightarrow> 'k::linorder" and build :: "'c \<Rightarrow> 'i" and search :: "'i \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes range :: "'i \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) list"
  assumes ranged: "key_range L R \<Longrightarrow> set (range i L R) = {(k,v). search i k v \<and> \<not> L k \<and> \<not> R k}"
    and range_sorted: "key_range L R \<Longrightarrow> sorted_wrt (<) (map fst (range i L R))"
begin

theorem range_content:
  assumes c: "formed c" and LR: "key_range L R"
  shows "set (range (build c) L R) =
    (\<lambda>(q,v). (key q,v)) ` {(q,v). q\<in>Q \<and> holds c q v \<and> \<not> L (key q) \<and> \<not> R (key q)}"
  unfolding ranged[OF LR] represents[OF c] by auto

theorem range_query:
  assumes c: "formed c" and q: "q\<in>Q" and LR: "key_range L R"
  shows "(key q,v) \<in> set (range (build c) L R) \<longleftrightarrow> holds c q v \<and> \<not> L (key q) \<and> \<not> R (key q)"
  unfolding ranged[OF LR] using query_search[OF c q] by auto

theorem range_values:
  assumes c: "formed c" and LR: "key_range L R"
  shows "set (map snd (range (build c) L R)) = {v. \<exists>q\<in>Q. holds c q v \<and> \<not> L (key q) \<and> \<not> R (key q)}"
  unfolding set_map range_content[OF c LR] by force

end

section \<open>The tree read at a range\<close>

fun rbt_range :: "('k::linorder \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k,'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v) list" where
  "rbt_range L R RBT_Impl.Empty = []"
| "rbt_range L R (RBT_Impl.Branch c l k v r) = (if L k then rbt_range L R r else if R k then rbt_range L R l
    else rbt_range L R l @ (k,v) # rbt_range L R r)"

lemma rbt_range_entries:
  assumes sorted: "rbt_sorted t" and LR: "key_range L R"
  shows "rbt_range L R t = filter (\<lambda>(k,v). \<not> L k \<and> \<not> R k) (RBT_Impl.entries t)"
  using sorted
proof (induction t)
  case Empty
  then show ?case by simp
next
  case (Branch c l k v r)
  have sl: "rbt_sorted l" and sr: "rbt_sorted r" using Branch.prems by simp_all
  have lk: "\<And>x y. (x,y) \<in> set (RBT_Impl.entries l) \<Longrightarrow> x < k"
    using Branch.prems by (force simp: rbt_less_prop RBT_Impl.keys_def)
  have kr: "\<And>x y. (x,y) \<in> set (RBT_Impl.entries r) \<Longrightarrow> k < x"
    using Branch.prems by (force simp: rbt_greater_prop RBT_Impl.keys_def)
  have down: "L x \<Longrightarrow> x' \<le> x \<Longrightarrow> L x'" and up: "R x \<Longrightarrow> x \<le> x' \<Longrightarrow> R x'" for x x'
    using LR by (auto simp: key_range_def)
  have fl: "filter (\<lambda>(k,v). \<not> L k \<and> \<not> R k) (RBT_Impl.entries l) = []" if "L k"
    using lk down[OF that] by (force simp: filter_empty_conv)
  have fr: "filter (\<lambda>(k,v). \<not> L k \<and> \<not> R k) (RBT_Impl.entries r) = []" if "R k"
    using kr up[OF that] by (force simp: filter_empty_conv)
  show ?case
  proof (cases "L k")
    case True
    then show ?thesis using fl[OF True] Branch.IH(2)[OF sr] by simp
  next
    case nl: False
    show ?thesis
    proof (cases "R k")
      case True
      then show ?thesis using nl fr[OF True] Branch.IH(1)[OF sl] by simp
    next
      case False
      then show ?thesis using nl Branch.IH(1)[OF sl] Branch.IH(2)[OF sr] by simp
    qed
  qed
qed

definition tree_range :: "('k::linorder,'v) rbt \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'v) list" where
  "tree_range T L R = rbt_range L R (RBT.impl_of T)"

lemma tree_range_entries:
  assumes LR: "key_range L R"
  shows "tree_range T L R = filter (\<lambda>(k,v). \<not> L k \<and> \<not> R k) (RBT.entries T)"
proof -
  have "rbt_sorted (RBT.impl_of T)" using RBT.impl_of[of T] by (simp add: is_rbt_def)
  then show ?thesis by (simp add: tree_range_def rbt_range_entries[OF _ LR] RBT.entries.rep_eq)
qed

interpretation tree_map_ranges:
  ranged_carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>rows. distinct (map fst rows)" "UNIV::'k::linorder set" id
    RBT.bulkload tree_search tree_range
proof (rule ranged_carrier_index.intro[OF tree_map_carrier_index], rule ranged_carrier_index_axioms.intro)
  fix L R :: "'k \<Rightarrow> bool" and T :: "('k,'v) rbt"
  assume LR: "key_range L R"
  show "set (tree_range T L R) = {(k,v). RBT.lookup T k = Some v \<and> \<not> L k \<and> \<not> R k}"
    by (auto simp: tree_range_entries[OF LR] RBT.lookup_in_tree)
  have "sorted_wrt (<) (map fst (RBT.entries T))"
    using RBT.sorted_entries[of T] RBT.distinct_entries[of T] by (simp add: strict_sorted_iff)
  then have "sorted_wrt (\<lambda>x y. fst x < fst y) (RBT.entries T)" by (simp add: sorted_wrt_map)
  then have "sorted_wrt (\<lambda>x y. fst x < fst y) (filter (\<lambda>(k,v). \<not> L k \<and> \<not> R k) (RBT.entries T))"
    by (rule sorted_wrt_filter)
  then show "sorted_wrt (<) (map fst (tree_range T L R))" by (simp add: tree_range_entries[OF LR] sorted_wrt_map)
qed

section \<open>The keys under a prefix are a range\<close>

text \<open>
  In the lexicographic order a list precedes its extensions, and the lists extending a prefix lie between it and every
  list after it that does not extend it: the keys under a prefix are the range whose side before is the keys less than
  the prefix and whose side after is the keys greater than it that do not extend it.
\<close>

definition prefix_below :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "prefix_below f k \<longleftrightarrow> k < f"

definition prefix_above :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "prefix_above f k \<longleftrightarrow> f < k \<and> take (length f) k \<noteq> f"

lemma extension_not_less: "\<not> (f @ z) < (f :: 'a::linorder list)"
  by (induction f) simp_all

lemma prefix_between:
  fixes f :: "'a::linorder list"
  shows "f \<le> k \<Longrightarrow> k \<le> f @ z \<Longrightarrow> take (length f) k = f"
proof (induction f arbitrary: k)
  case Nil
  then show ?case by simp
next
  case (Cons a f)
  from Cons.prems(1) obtain b k' where k: "k = b # k'" by (cases k) simp_all
  have "a < b \<or> a = b \<and> f \<le> k'" and "b < a \<or> b = a \<and> k' \<le> f @ z" using Cons.prems unfolding k by simp_all
  then have "a = b" "f \<le> k'" "k' \<le> f @ z" by auto
  then show ?case using Cons.IH[of k'] k by simp
qed

lemma prefix_range: "key_range (prefix_below f) (prefix_above f)"
proof -
  have below: "k' < f" if "k < f" "k' \<le> k" for k k' :: "'a list" by (rule le_less_trans[OF that(2) that(1)])
  have above: "f < k' \<and> take (length f) k' \<noteq> f"
    if a: "f < k \<and> take (length f) k \<noteq> f" and le: "k \<le> k'" for k k' :: "'a list"
  proof
    show "f < k'" using a le by (blast intro: less_le_trans)
    show "take (length f) k' \<noteq> f"
    proof
      assume t: "take (length f) k' = f"
      have "k' = f @ drop (length f) k'" using t by (metis append_take_drop_id)
      then have "k \<le> f @ drop (length f) k'" using le by simp
      then have "take (length f) k = f" using a by (blast intro: prefix_between less_imp_le)
      then show False using a by simp
    qed
  qed
  show ?thesis unfolding key_range_def prefix_below_def prefix_above_def using below above by blast
qed

lemma prefix_inside: "\<not> prefix_below f k \<and> \<not> prefix_above f k \<longleftrightarrow> take (length f) k = f"
proof
  assume t: "take (length f) k = f"
  have "k = f @ drop (length f) k" using t by (metis append_take_drop_id)
  then have "\<not> k < f" using extension_not_less[of f] by metis
  then show "\<not> prefix_below f k \<and> \<not> prefix_above f k" using t by (simp add: prefix_below_def prefix_above_def)
next
  assume n: "\<not> prefix_below f k \<and> \<not> prefix_above f k"
  then have "f \<le> k" by (simp add: prefix_below_def not_less)
  then show "take (length f) k = f" using n by (cases "f = k") (simp_all add: prefix_above_def order.order_iff_strict)
qed

definition tree_prefix :: "('a::linorder list,'v) rbt \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'v) list" where
  "tree_prefix T f = tree_range T (prefix_below f) (prefix_above f)"

theorem tree_prefix:
  "(k,v) \<in> set (tree_prefix T f) \<longleftrightarrow> RBT.lookup T k = Some v \<and> take (length f) k = f"
  "sorted_wrt (<) (map fst (tree_prefix T f))"
  "v \<in> snd ` set (tree_prefix T f) \<longleftrightarrow> (\<exists>k. RBT.lookup T k = Some v \<and> take (length f) k = f)"
proof -
  have pairs: "(k,v) \<in> set (tree_prefix T f) \<longleftrightarrow> RBT.lookup T k = Some v \<and> take (length f) k = f" for k v
    unfolding tree_prefix_def tree_map_ranges.ranged[OF prefix_range] using prefix_inside[of f k] by simp
  show "(k,v) \<in> set (tree_prefix T f) \<longleftrightarrow> RBT.lookup T k = Some v \<and> take (length f) k = f" by (rule pairs)
  show "sorted_wrt (<) (map fst (tree_prefix T f))"
    unfolding tree_prefix_def by (rule tree_map_ranges.range_sorted[OF prefix_range])
  show "v \<in> snd ` set (tree_prefix T f) \<longleftrightarrow> (\<exists>k. RBT.lookup T k = Some v \<and> take (length f) k = f)"
    by (simp add: snd_eq_Range Range_iff pairs)
qed

end
