theory Binary_Store_Indexes
imports Carrier_Indexes Binary_Path_Stores Binary_Relation_Stores Binary_Nested_Stores
begin

section \<open>The binary stores are indexes updated in place\<close>

text \<open>
  A relation over paths, given by its rows, is the carrier of @{const relation_store}, searched by the
  membership of a value in the bucket at a path and keyed by the path itself; the store's own member
  equation @{thm [source] relation_store_member} discharges the notion's obligation (2) at every key.
  Its insertion is the notion's update, adding one value to one bucket
  (@{thm [source] relation_store_lookup_insert}). A nested store is the same carrier keyed by a pair of
  paths (@{thm [source] nested_relation_store_member}, @{thm [source] nested_relation_lookup_insert}). A
  single-valued path store is its own index, updated by replacement: the lookup of an update is the
  replacing optional value at its path and the old lookup elsewhere (@{thm [source] store_lookup_update}).
  No carrier is changed; these are its statements read as instances.
\<close>

lemma relation_store_carrier_index:
  "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>_. True) UNIV id relation_store
    (\<lambda>T k v. v |\<in>| relation_store_lookup T k)"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by simp
  fix rows :: "(bool list\<times>'v) list" and k v
  show "v |\<in>| relation_store_lookup (relation_store rows) k \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v)\<in>set rows)"
    by (simp add: relation_store_member)
qed

interpretation relation_store_index:
  carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>_. True" UNIV id relation_store
    "\<lambda>T k v. v |\<in>| relation_store_lookup T k"
  by (rule relation_store_carrier_index)

interpretation relation_store_updates:
  updated_carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>_. True" UNIV id relation_store
    "\<lambda>T k v. v |\<in>| relation_store_lookup T k" "\<lambda>T k u. relation_store_insert (k,u) T" "\<lambda>u f v. v=u \<or> f v"
proof (rule updated_carrier_index.intro[OF relation_store_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "'v fset binary_path_store" and k k' :: "bool list" and u v :: 'v
  show "v |\<in>| relation_store_lookup (relation_store_insert (k,u) T) k' \<longleftrightarrow>
      (if k'=k then v=u \<or> v |\<in>| relation_store_lookup T k else v |\<in>| relation_store_lookup T k')"
    by simp
qed

lemma path_store_carrier_index:
  "carrier_index (\<lambda>T q v. store_lookup T q=Some v) (\<lambda>_. True) UNIV id id (\<lambda>T k v. store_lookup T k=Some v)"
  by (rule carrier_index.intro) simp_all

interpretation path_store_updates:
  updated_carrier_index "\<lambda>T q v. store_lookup T q=Some v" "\<lambda>_. True" UNIV id id
    "\<lambda>T k v. store_lookup T k=Some v" store_update "\<lambda>u f v. u=Some v"
proof (rule updated_carrier_index.intro[OF path_store_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "'v binary_path_store" and k k' :: "bool list" and u :: "'v option" and v :: 'v
  show "store_lookup (store_update T k u) k'=Some v \<longleftrightarrow> (if k'=k then u=Some v else store_lookup T k'=Some v)"
    by (cases "k'=k") simp_all
qed

lemma nested_store_carrier_index:
  "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>_. True) UNIV id nested_relation_store
    (\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k))"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by simp
  fix rows :: "((bool list\<times>bool list)\<times>'v) list" and k v
  show "v |\<in>| nested_relation_lookup (nested_relation_store rows) (fst k) (snd k) \<longleftrightarrow>
      (\<exists>q\<in>UNIV. id q=k \<and> (q,v)\<in>set rows)"
    by (cases k) (simp add: nested_relation_store_member)
qed

interpretation nested_store_index:
  carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>_. True" UNIV id nested_relation_store
    "\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k)"
  by (rule nested_store_carrier_index)

interpretation nested_store_updates:
  updated_carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>_. True" UNIV id nested_relation_store
    "\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k)"
    "\<lambda>T k u. nested_relation_insert (fst k) (snd k) u T" "\<lambda>u f v. v=u \<or> f v"
proof (rule updated_carrier_index.intro[OF nested_store_carrier_index], rule updated_carrier_index_axioms.intro)
  fix T :: "'v fset binary_path_store binary_path_store" and k k' :: "bool list\<times>bool list" and u v :: 'v
  show "v |\<in>| nested_relation_lookup (nested_relation_insert (fst k) (snd k) u T) (fst k') (snd k') \<longleftrightarrow>
      (if k'=k then v=u \<or> v |\<in>| nested_relation_lookup T (fst k) (snd k)
        else v |\<in>| nested_relation_lookup T (fst k') (snd k'))"
    by (cases k; cases k') auto
qed

end
