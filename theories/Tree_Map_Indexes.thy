theory Tree_Map_Indexes
  imports Carrier_Indexes "HOL-Library.RBT"
begin

section \<open>The red-black tree is an index of its rows\<close>

text \<open>
  A list of rows with distinct keys is the carrier of the partial map it states; its index is the
  red-black tree @{const RBT.bulkload} builds from it, searched by lookup and keyed by the identity. The
  tree's own contract @{thm [source] RBT.lookup_bulkload} discharges the notion's obligation (2) at every
  key, and an insertion is the notion's update: the lookup of an insertion
  (@{thm [source] RBT.lookup_insert}) makes the inserted value the one found at its key and keeps every
  other key. The values are of any type. The instance stands below every theory that indexes by the tree,
  the ordered member tree's own theory among them, so that each of them cites it rather than making the
  lookup's argument again.
\<close>

abbreviation tree_search :: "('k::linorder,'v) rbt \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" where
  "tree_search T k v \<equiv> RBT.lookup T k=Some v"

lemma tree_map_carrier_index:
  "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>rows. distinct (map fst rows)) (UNIV::'k::linorder set) id
    RBT.bulkload tree_search"
proof (rule carrier_index.intro)
  show "inj_on id (UNIV::'k set)" by simp
  fix rows :: "('k\<times>'v) list" and k :: 'k and v :: 'v
  assume distinct: "distinct (map fst rows)"
  show "RBT.lookup (RBT.bulkload rows) k=Some v \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v)\<in>set rows)"
    by (auto simp: RBT.lookup_bulkload intro: map_of_is_SomeI[OF distinct] dest: map_of_SomeD)
qed

interpretation tree_map_index:
  carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>rows. distinct (map fst rows)" "UNIV::'k::linorder set" id
    RBT.bulkload tree_search
  by (rule tree_map_carrier_index)

interpretation tree_map_updates:
  updated_carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>rows. distinct (map fst rows)" "UNIV::'k::linorder set" id
    RBT.bulkload tree_search "\<lambda>T k u. RBT.insert k u T" "\<lambda>u f v. v=u"
proof (rule updated_carrier_index.intro[OF tree_map_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "('k,'v) rbt" and k k' :: 'k and u v :: 'v
  show "RBT.lookup (RBT.insert k u T) k'=Some v \<longleftrightarrow> (if k'=k then v=u else RBT.lookup T k'=Some v)"
    by (cases "k'=k") (auto simp: RBT.lookup_insert)
qed

end
