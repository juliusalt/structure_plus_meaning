theory Binary_Relation_Stores
  imports Binary_Path_Stores "HOL-Library.FSet"
begin

definition relation_store_lookup where
  "relation_store_lookup tree key=(case store_lookup tree key of None \<Rightarrow> {||} | Some values \<Rightarrow> values)"

definition relation_store_insert where
  "relation_store_insert row tree=(case row of (key,value) \<Rightarrow>
    store_update tree key (Some (finsert value (relation_store_lookup tree key))))"

lemma relation_store_lookup_empty [simp]: "relation_store_lookup Empty_Store key={||}"
  by (simp add: relation_store_lookup_def)

lemma relation_store_lookup_insert [simp]:
  "relation_store_lookup (relation_store_insert (key,value) tree) query=
    (if query=key then finsert value (relation_store_lookup tree query) else relation_store_lookup tree query)"
  by (simp add: relation_store_insert_def relation_store_lookup_def)

fun relation_store where
  "relation_store []=Empty_Store"
| "relation_store (row#rows)=relation_store_insert row (relation_store rows)"

theorem relation_store_member:
  "value |\<in>| relation_store_lookup (relation_store rows) key \<longleftrightarrow> (key,value)\<in>set rows"
  by (induction rows) (auto split: prod.splits if_splits)

lemma relation_store_canonical: "store_canonical (relation_store rows)"
  by (induction rows) (auto simp: relation_store_insert_def intro: store_update_canonical split: prod.splits)

text \<open>
  The index preserves a complete relation, including multiple values at one
  key. Repeated rows do not create repeated set members. Formation and
  single-valuedness are separate conditions and are never assumed by lookup.
\<close>

end
