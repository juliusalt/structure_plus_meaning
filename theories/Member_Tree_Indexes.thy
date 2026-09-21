theory Member_Tree_Indexes
imports Carrier_Indexes Ordered_Member_Trees Keyed_Finite_Sets
begin

section \<open>The ordered member tree and the keyed set over it are indexes\<close>

text \<open>
  A finite set of a linearly ordered type is the carrier of the relation of its members to the one
  value of @{typ unit}; its index is @{const ordered_member_tree}, searched by lookup, and the key is
  the identity. The member tree's own contract @{thm [source] ordered_member_tree_some} discharges the
  notion's obligation (2) at every key, and the identity distinguishes every query. The listed set, a
  list read as the set of its members, is the same carrier read through @{const fset_of_list}; a keyed
  set, a finite set searched by a key with a left inverse, is the member tree of its key image. Both
  are derived by the notion's @{thm [source] carrier_index_through_key}, not proved again. An insertion
  into the tree is the notion's update: the lookup of an insertion (@{thm [source] RBT.lookup_insert})
  makes the inserted value the one found at its key and keeps every other key.
\<close>

abbreviation member_holds :: "'a fset \<Rightarrow> 'a \<Rightarrow> unit \<Rightarrow> bool" where
  "member_holds A q v \<equiv> q |\<in>| A"

abbreviation tree_search :: "('k::linorder,'v) rbt \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> bool" where
  "tree_search T k v \<equiv> RBT.lookup T k=Some v"

lemma member_tree_carrier_index:
  "carrier_index member_holds (\<lambda>_. True) (UNIV::'a::linorder set) id ordered_member_tree tree_search"
proof (rule carrier_index.intro)
  show "inj_on id (UNIV::'a set)" by simp
  fix A :: "'a fset" and k :: 'a and v :: unit
  show "RBT.lookup (ordered_member_tree A) k=Some v \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> q |\<in>| A)"
    by (cases v) (simp add: ordered_member_tree_some)
qed

interpretation member_tree_index:
  carrier_index member_holds "\<lambda>_. True" "UNIV::'a::linorder set" id ordered_member_tree tree_search
  by (rule member_tree_carrier_index)

interpretation member_tree_updates:
  updated_carrier_index member_holds "\<lambda>_. True" "UNIV::'a::linorder set" id ordered_member_tree tree_search
    "\<lambda>T k u. RBT.insert k u T" "\<lambda>u f v. v=u"
proof (rule updated_carrier_index.intro[OF member_tree_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "('a,unit) rbt" and k k' :: 'a and u v :: unit
  show "RBT.lookup (RBT.insert k u T) k'=Some v \<longleftrightarrow> (if k'=k then v=u else RBT.lookup T k'=Some v)"
    by (cases "k'=k") (auto simp: RBT.lookup_insert)
qed

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
  The keyed set's own contract @{thm [source] keyed_member_lookup} is the query form of the notion here.
\<close>

corollary member_query: "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> x |\<in>| A"
  using query_search[where c=A and q=x and v="()"] by (cases "RBT.lookup (ordered_member_tree (fimage key A)) (key x)") auto

end

end
