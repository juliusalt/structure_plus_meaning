theory Member_Tree_Indexes
imports Carrier_Indexes Ordered_Member_Trees Keyed_Finite_Sets
begin

section \<open>The member tree and the keyed set are instances of the red-black tree's index\<close>

text \<open>
  The red-black tree is an index of its rows (@{text Tree_Map_Indexes}). A finite set of a linearly ordered type is the carrier of the relation of its members to the one
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
  The member tree's query and update forms, as its uses ask them: whether a lookup finds anything, the
  notion's @{text lookup_found} at unit values.
\<close>

corollary member_tree_lookup: "RBT.lookup (ordered_member_tree A) x\<noteq>None \<longleftrightarrow> x |\<in>| A"
proof -
  have "RBT.lookup (ordered_member_tree A) (id x)\<noteq>None \<longleftrightarrow> (\<exists>v::unit. x |\<in>| A)"
    by (rule member_tree_index.lookup_found[where look=RBT.lookup]) simp_all
  then show ?thesis by simp
qed

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
proof -
  have "RBT.lookup (ordered_member_tree (fset_of_list xs)) (id x)\<noteq>None \<longleftrightarrow> (\<exists>v::unit. x\<in>set xs)"
    by (rule listed_member_tree_index.lookup_found[where look=RBT.lookup]) simp_all
  then show ?thesis by simp
qed

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
  The keyed set's query and inclusion forms are the notion's @{text lookup_found} and
  @{text lookup_queries_found} at unit values; the uses of the keyed set cite these forms.
\<close>

corollary member_query: "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> x |\<in>| A"
proof -
  have "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> (\<exists>v::unit. x |\<in>| A)"
    by (rule lookup_found[where look=RBT.lookup]) simp_all
  then show ?thesis by simp
qed

corollary members_subset:
  "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) \<longleftrightarrow> B |\<subseteq>| A"
proof -
  have "(\<forall>q\<in>fset B. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) \<longleftrightarrow>
      (\<forall>q\<in>fset B. \<exists>v::unit. q |\<in>| A)"
    by (rule lookup_queries_found[where look=RBT.lookup]) simp_all
  then show ?thesis by (auto simp: less_eq_fset.rep_eq)
qed

end

end
