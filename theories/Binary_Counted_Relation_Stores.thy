theory Binary_Counted_Relation_Stores
  imports Binary_Relation_Stores
begin

definition counted_relation_store_insert where
  "counted_relation_store_insert row tree=(case row of (key,value) \<Rightarrow>
    let previous=counted_store_lookup tree key;
      values=(case fst previous of None \<Rightarrow> {||} | Some values \<Rightarrow> values);
      following=counted_store_update tree key (Some (finsert value values))
    in (fst following,snd previous,snd following))"

theorem counted_relation_store_insert_exact:
  "counted_relation_store_insert (key,value) tree=
    (relation_store_insert (key,value) tree,Suc (length key),Suc (length key))"
  by (simp add: counted_relation_store_insert_def counted_store_lookup_exact
    counted_store_update_exact relation_store_insert_def relation_store_lookup_def Let_def)

text \<open>
  Complete relation insertion performs its original bucket lookup and update.
  Both actual traversals are counted, and the resulting store is unchanged by
  instrumentation. Key construction and finite-value operations are separate.
\<close>

end
