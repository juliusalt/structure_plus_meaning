theory Binary_Nested_Stores
  imports Binary_Relation_Stores
begin

definition nested_store_at where
  "nested_store_at tree outer=(case store_lookup tree outer of None \<Rightarrow> Empty_Store | Some inner \<Rightarrow> inner)"

definition nested_relation_lookup where
  "nested_relation_lookup tree outer inner=relation_store_lookup (nested_store_at tree outer) inner"

definition nested_relation_insert where
  "nested_relation_insert outer inner value tree=store_update tree outer
    (Some (relation_store_insert (inner,value) (nested_store_at tree outer)))"

lemma nested_relation_lookup_empty [simp]:
  "nested_relation_lookup Empty_Store outer inner={||}"
  by (simp add: nested_relation_lookup_def nested_store_at_def)

lemma nested_relation_lookup_insert [simp]:
  "nested_relation_lookup (nested_relation_insert outer inner value tree) x y=
    (if x=outer \<and> y=inner then finsert value (nested_relation_lookup tree x y)
      else nested_relation_lookup tree x y)"
  by (auto simp: nested_relation_lookup_def nested_relation_insert_def nested_store_at_def)

fun nested_relation_store where
  "nested_relation_store []=Empty_Store"
| "nested_relation_store (((outer,inner),value)#rows)=
    nested_relation_insert outer inner value (nested_relation_store rows)"

theorem nested_relation_store_member:
  "value |\<in>| nested_relation_lookup (nested_relation_store rows) outer inner \<longleftrightarrow>
    ((outer,inner),value)\<in>set rows"
  by (induction rows) (auto split: prod.splits if_splits)

text \<open>
  Two separate keys select the two paths; no concatenation is assumed to
  encode their boundary. Every relation value is retained. Insertion changes
  exactly one bucket and leaves all other outer and inner lookups unchanged.
\<close>

end
