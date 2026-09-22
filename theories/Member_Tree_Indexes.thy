theory Member_Tree_Indexes
imports Carrier_Indexes Ordered_Member_Trees Keyed_Finite_Sets
begin

section \<open>The red-black tree is an index of its rows, and the member tree and the keyed set are its instances\<close>

text \<open>
  A list of rows with distinct keys is the carrier of the partial map it states; its index is the
  red-black tree @{const RBT.bulkload} builds from it, searched by lookup and keyed by the identity. The
  tree's own contract @{thm [source] RBT.lookup_bulkload} discharges the notion's obligation (2) at every
  key, and an insertion is the notion's update: the lookup of an insertion
  (@{thm [source] RBT.lookup_insert}) makes the inserted value the one found at its key and keeps every
  other key. The values are of any type.

  A finite set of a linearly ordered type is the carrier of the relation of its members to the one
  value of @{typ unit}; its index @{const ordered_member_tree} is the tree of the rows of its canonical
  listing, so it is the tree's instance read through that listing by the notion's
  @{thm [source] carrier_index_through_key}, and its update is the tree's update at unit values. The
  listed set, a list read as the set of its members, is the same carrier read through
  @{const fset_of_list}; a keyed set, a finite set searched by a key with a left inverse, is the member
  tree of its key image. Both are derived by @{thm [source] carrier_index_through_key}, not proved again.
  The positions of a demand (@{text Positioned_Native_Evaluation}) are another instance of the tree,
  with positions as values.
\<close>

abbreviation member_holds :: "'a fset \<Rightarrow> 'a \<Rightarrow> unit \<Rightarrow> bool" where
  "member_holds A q v \<equiv> q |\<in>| A"

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

lemma member_tree_carrier_index:
  "carrier_index member_holds (\<lambda>_. True) (UNIV::'a::linorder set) id ordered_member_tree tree_search"
proof -
  have tree: "ordered_member_tree=(\<lambda>A::'a fset. RBT.bulkload (map (\<lambda>x. (x,())) (sorted_list_of_fset A)))"
    by (rule ext) (simp only: ordered_member_tree_def)
  show ?thesis unfolding tree
  proof (rule carrier_index_through_key[OF tree_map_carrier_index])
    fix A :: "'a fset" and k :: 'a and v :: unit
    show "(k,v)\<in>set (map (\<lambda>x. (x,())) (sorted_list_of_fset A)) \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> q |\<in>| A)"
      by (cases v) auto
  qed (simp_all add: sorted_list_of_fset.rep_eq comp_def)
qed

interpretation member_tree_index:
  carrier_index member_holds "\<lambda>_. True" "UNIV::'a::linorder set" id ordered_member_tree tree_search
  by (rule member_tree_carrier_index)

text \<open>
  The member tree's update is the tree's update at unit values: the update axiom concerns the search
  and the insertion alone, so it is the tree's, instantiated.
\<close>

interpretation member_tree_updates:
  updated_carrier_index member_holds "\<lambda>_. True" "UNIV::'a::linorder set" id ordered_member_tree tree_search
    "\<lambda>T k u. RBT.insert k u T" "\<lambda>u f v. v=u"
proof (rule updated_carrier_index.intro[OF member_tree_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "('a,unit) rbt" and k k' :: 'a and u v :: unit
  show "RBT.lookup (RBT.insert k u T) k'=Some v \<longleftrightarrow> (if k'=k then v=u else RBT.lookup T k'=Some v)"
    by (simp only: tree_map_updates.updated)
qed

text \<open>
  The member tree's query and update forms, as its uses ask them: whether a lookup finds anything.
\<close>

corollary member_tree_lookup: "RBT.lookup (ordered_member_tree A) x\<noteq>None \<longleftrightarrow> x |\<in>| A"
  using member_tree_index.query_search[where c=A and q=x and v="()"] by (cases "RBT.lookup (ordered_member_tree A) x") auto

corollary member_tree_found: "RBT.lookup (ordered_member_tree A) x=Some () \<longleftrightarrow> x |\<in>| A"
  using member_tree_index.query_search[where c=A and q=x and v="()"] by simp

corollary member_tree_absent: "RBT.lookup (ordered_member_tree A) x=None \<longleftrightarrow> x |\<notin>| A"
  using member_tree_lookup[of A x] by blast

corollary member_tree_insert: "RBT.lookup (RBT.insert k () T) k'\<noteq>None \<longleftrightarrow> k'=k \<or> RBT.lookup T k'\<noteq>None"
  using member_tree_updates.updated[where i=T and k=k and u="()" and k'=k' and v="()"]
  by (cases "RBT.lookup T k'") (auto simp del: RBT.lookup_insert)

lemma listed_member_tree_carrier_index:
  "carrier_index (\<lambda>xs q (v::unit). q\<in>set xs) (\<lambda>_. True) (UNIV::'a::linorder set) id
    (\<lambda>xs. ordered_member_tree (fset_of_list xs)) tree_search"
proof (rule carrier_index_through_key[OF member_tree_carrier_index])
  show "inj_on id (UNIV::'a set)" by simp
  fix xs :: "'a list" and k :: 'a and v :: unit
  show "k |\<in>| fset_of_list xs \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> q\<in>set xs)"
    by (simp add: fset_of_list.rep_eq)
qed simp

interpretation listed_member_tree_index:
  carrier_index "\<lambda>xs q (v::unit). q\<in>set xs" "\<lambda>_. True" "UNIV::'a::linorder set" id
    "\<lambda>xs. ordered_member_tree (fset_of_list xs)" tree_search
  by (rule listed_member_tree_carrier_index)

corollary listed_member_lookup: "RBT.lookup (ordered_member_tree (fset_of_list xs)) x\<noteq>None \<longleftrightarrow> x\<in>set xs"
  using listed_member_tree_index.query_search[where c=xs and q=x and v="()"]
  by (cases "RBT.lookup (ordered_member_tree (fset_of_list xs)) x") auto

locale keyed_set_index =
  fixes key :: "'a \<Rightarrow> 'k::linorder" and unkey :: "'k \<Rightarrow> 'a"
  assumes inverse: "\<And>x. unkey (key x)=x"
begin

lemma carrier:
  "carrier_index member_holds (\<lambda>_. True) UNIV key (\<lambda>A. ordered_member_tree (fimage key A)) tree_search"
proof (rule carrier_index_through_key[OF member_tree_carrier_index])
  show "inj_on key UNIV" by (rule distinguishes_by_left_inverse[where unkey=unkey], rule inverse)
  fix A :: "'a fset" and k :: 'k and v :: unit
  show "k |\<in>| fimage key A \<longleftrightarrow> (\<exists>q\<in>UNIV. key q=k \<and> q |\<in>| A)" by auto
qed simp

sublocale carrier_index member_holds "\<lambda>_. True" UNIV key "\<lambda>A. ordered_member_tree (fimage key A)" tree_search
  by (rule carrier)

text \<open>
  The keyed set's own contract @{thm [source] keyed_member_lookup} is the query form of the notion here;
  the uses of the index notion cite this form, the carrier keeping its own since it cannot import its
  instance.
\<close>

corollary member_query: "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> x |\<in>| A"
  using query_search[where c=A and q=x and v="()"] by (cases "RBT.lookup (ordered_member_tree (fimage key A)) (key x)") auto

corollary members_subset:
  "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) \<longleftrightarrow> B |\<subseteq>| A"
proof -
  have "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) \<longleftrightarrow> fBall B (\<lambda>q. q |\<in>| A)"
    by (simp only: member_query)
  then show ?thesis by (auto simp: less_eq_fset.rep_eq)
qed

end

end
