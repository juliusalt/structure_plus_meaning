theory First_Index_Trees
  imports Tree_Map_Indexes Complete_Value_References "HOL-Library.Multiset"
begin

section \<open>A list is indexed by the first positions of its members\<close>

text \<open>
  The index of a list by the first positions of its members is the tree map's index
  (@{thm [source] tree_map_carrier_index}) read through an injective key (@{thm [source] carrier_index_through_key}):
  its carrier relates a member to its first position (@{const value_reference_index}). The tree the code
  builds, the bulkload of the keys zipped with their positions, has that index's lookups, since a bulkload
  keeps the first row at a key; an index whose search agrees with an index's search is an index
  (@{text carrier_index_search_agrees}). A distinct list is recovered in its own order from any distinct
  listing of the members it keeps, by sorting that listing on their first positions
  (@{text first_positions_sort}). The facts are general over lists: a use keys its members and cites them.
\<close>


definition first_index_tree :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> ('k,nat) rbt" where
  "first_index_tree key xs=RBT.bulkload (zip (map key xs) [0..<length xs])"

lemma map_of_first_index:
  assumes key: "inj key"
  shows "map_of (zip (map key xs) [0..<length xs]) (key x)=value_reference_index x xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have upto: "[0..<length (y#ys)]=0#map Suc [0..<length ys]"
    by (simp only: length_Cons map_Suc_upt upt_conv_Cons[OF zero_less_Suc])
  show ?case unfolding upto by (simp add: zip_map2 map_of_map Cons.IH inj_eq[OF key])
qed

lemma first_index_tree_lookup:
  assumes key: "inj key"
  shows "RBT.lookup (first_index_tree key xs) (key x)=value_reference_index x xs"
  by (simp add: first_index_tree_def RBT.lookup_bulkload map_of_first_index[OF key])

lemma first_index_tree_absent:
  assumes "k\<notin>range key"
  shows "RBT.lookup (first_index_tree key xs) k=None"
  using assms by (auto simp: first_index_tree_def RBT.lookup_bulkload map_of_eq_None_iff dest!: set_zip_leftD)

lemma first_index_tree_found:
  assumes key: "inj key"
  shows "RBT.lookup (first_index_tree key xs) (key x)=None \<longleftrightarrow> x\<notin>set xs"
  by (simp add: first_index_tree_lookup[OF key] value_reference_index_absent)

lemma first_index_image:
  "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)) \<longleftrightarrow>
    (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)"
proof
  assume "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))"
  then obtain x where x: "x\<in>set c" "k=key x" "v=the (value_reference_index x c)" by auto
  have "value_reference_index x c=Some v"
    using x value_reference_index_absent[of x c] by (cases "value_reference_index x c") auto
  then show "\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v" using x by auto
next
  assume "\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v"
  then obtain q where q: "k=key q" "value_reference_index q c=Some v" by auto
  have "q\<in>set c" using q(2) value_reference_index_absent[of q c] by auto
  then show "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))"
    using q by (auto simp: image_iff intro!: bexI[where x=q])
qed

text \<open>
  The through instance builds its tree from the remdups of the list; the code's tree, from the positions
  zipped with every key, has the same lookup at every key, so it is the same index.
\<close>

lemma first_index_carrier_index:
  assumes key: "inj key"
  shows "carrier_index (\<lambda>xs x i. value_reference_index x xs=Some i) (\<lambda>_. True) UNIV key
    (first_index_tree key) tree_search"
proof -
  interpret through: carrier_index "\<lambda>xs x i. value_reference_index x xs=Some i" "\<lambda>_. True" UNIV key
    "\<lambda>c. RBT.bulkload (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))" tree_search
  proof (rule carrier_index_through_key[OF tree_map_carrier_index])
    show "distinct (map fst (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)))" for c
      using inj_on_subset[OF key] by (simp add: distinct_map o_def)
    show "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)) \<longleftrightarrow>
        (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)" for c k v
      by (rule first_index_image)
    show "inj_on key UNIV" by (rule key)
  qed
  show ?thesis
  proof (rule carrier_index_search_agrees[OF through.carrier_index_axioms])
    fix c k v
    show "tree_search (first_index_tree key c) k v \<longleftrightarrow>
        tree_search (RBT.bulkload (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))) k v"
    proof (cases "k\<in>range key")
      case True
      then obtain x where k: "k=key x" by auto
      show ?thesis
        using through.query_search[where c=c and q=x and v=v] by (simp add: k first_index_tree_lookup[OF key])
    next
      case False
      then show ?thesis
        using through.unkeyed_search[where c=c and k=k and v=v] by (simp add: first_index_tree_absent)
    qed
  qed
qed

lemma value_reference_index_append_absent:
  "x\<notin>set xs \<Longrightarrow> value_reference_index x (xs@ys)=map_option ((+) (length xs)) (value_reference_index x ys)"
proof (induction xs)
  case Nil
  show ?case by (cases "value_reference_index x ys") simp_all
next
  case (Cons y xs)
  then show ?case by (cases "value_reference_index x ys") simp_all
qed

section \<open>A distinct list is recovered by sorting on first positions\<close>

lemma value_reference_index_nth:
  assumes "distinct xs" "i<length xs"
  shows "value_reference_index (xs!i) xs=Some i"
  by (rule value_reference_index_distinct_read[OF assms(1)]) (simp add: value_reference_read_def assms(2))

lemma first_positions_filter_sorted:
  assumes xs: "distinct xs"
  shows "sorted (map (\<lambda>x. the (value_reference_index x xs)) (filter P xs))"
proof -
  let ?L="filter (\<lambda>i. P (xs!i)) [0..<length xs]"
  have "filter P xs=filter P (map (nth xs) [0..<length xs])" by (simp only: map_nth)
  also have "\<dots>=map (nth xs) ?L" by (simp only: filter_map comp_def)
  finally have split: "filter P xs=map (nth xs) ?L" .
  have mapped: "map (\<lambda>x. the (value_reference_index x xs)) (map (nth xs) ?L)=?L"
    unfolding map_map by (rule map_idI) (simp add: value_reference_index_nth[OF xs])
  show ?thesis unfolding split mapped by (rule sorted_wrt_filter) simp
qed

lemma first_positions_sort:
  assumes xs: "distinct xs" and ys: "distinct ys" and same: "set ys=set (filter P xs)"
  shows "map snd (sort_key fst (map (\<lambda>y. (the (value_reference_index y xs),y)) ys))=filter P xs"
proof -
  let ?p="\<lambda>y. (the (value_reference_index y xs),y)"
  have ms: "mset ys=mset (filter P xs)"
    by (rule iffD1[OF set_eq_iff_mset_eq_distinct[OF ys distinct_filter[OF xs]] same])
  have "sort_key fst (map ?p ys)=map ?p (filter P xs)"
  proof (rule sort_key_inj_key_eq)
    show "mset (map ?p ys)=mset (map ?p (filter P xs))" by (simp only: mset_map ms)
    show "inj_on fst (set (map ?p ys))"
    proof (rule inj_onI)
      fix a b assume a: "a\<in>set (map ?p ys)" and b: "b\<in>set (map ?p ys)" and eq: "fst a=fst b"
      obtain y where y: "y\<in>set ys" "a=?p y" using a by auto
      obtain z where z: "z\<in>set ys" "b=?p z" using b by auto
      have yx: "y\<in>set xs" and zx: "z\<in>set xs" using y(1) z(1) same by auto
      obtain i where i: "value_reference_index y xs=Some i"
        using yx value_reference_index_absent[of y xs] by (cases "value_reference_index y xs") auto
      obtain j where j: "value_reference_index z xs=Some j"
        using zx value_reference_index_absent[of z xs] by (cases "value_reference_index z xs") auto
      have "i=j" using eq y(2) z(2) i j by simp
      then have "y=z" using value_reference_index_read[OF i] value_reference_index_read[OF j] by simp
      then show "a=b" using y(2) z(2) by simp
    qed
    show "sorted (map fst (map ?p (filter P xs)))"
      using first_positions_filter_sorted[OF xs, of P] by (simp add: o_def)
  qed
  then show ?thesis by (simp add: o_def)
qed

end
