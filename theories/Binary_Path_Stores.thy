theory Binary_Path_Stores
  imports Main
begin

datatype 'a binary_path_store = Empty_Store
  | Store_Node "'a option" "'a binary_path_store" "'a binary_path_store"

fun store_value where
  "store_value Empty_Store=None"
| "store_value (Store_Node value left right)=value"
fun store_left where
  "store_left Empty_Store=Empty_Store"
| "store_left (Store_Node value left right)=left"
fun store_right where
  "store_right Empty_Store=Empty_Store"
| "store_right (Store_Node value left right)=right"

fun compact_store_node where
  "compact_store_node None Empty_Store Empty_Store=Empty_Store"
| "compact_store_node value left right=Store_Node value left right"

lemma compact_store_fields [simp]:
  "store_value (compact_store_node value left right)=value"
  "store_left (compact_store_node value left right)=left"
  "store_right (compact_store_node value left right)=right"
  by (cases "value"; cases "left"; cases "right"; simp)+

fun store_lookup where
  "store_lookup tree []=store_value tree"
| "store_lookup tree (go_right#key)=store_lookup
    (if go_right then store_right tree else store_left tree) key"

lemma store_lookup_empty [simp]: "store_lookup Empty_Store key=None"
  by (induction key) simp_all

fun store_update where
  "store_update tree [] value=compact_store_node value (store_left tree) (store_right tree)"
| "store_update tree (go_right#key) value=(if go_right then
    compact_store_node (store_value tree) (store_left tree) (store_update (store_right tree) key value)
    else compact_store_node (store_value tree) (store_update (store_left tree) key value) (store_right tree))"

theorem store_lookup_update [simp]:
  "store_lookup (store_update tree key value) query=
    (if query=key then value else store_lookup tree query)"
  by (induction key arbitrary: tree query) (case_tac query; auto)+

fun store_canonical where
  "store_canonical Empty_Store=True"
| "store_canonical (Store_Node value left right)=(store_canonical left \<and> store_canonical right \<and>
    (value\<noteq>None \<or> left\<noteq>Empty_Store \<or> right\<noteq>Empty_Store))"

lemma store_canonical_compact:
  "store_canonical left \<Longrightarrow> store_canonical right \<Longrightarrow>
    store_canonical (compact_store_node value left right)"
  by (cases "value"; cases "left"; cases "right") simp_all

lemma store_canonical_children:
  "store_canonical tree \<Longrightarrow> store_canonical (store_left tree)"
  "store_canonical tree \<Longrightarrow> store_canonical (store_right tree)"
  by (cases tree; simp_all)+

theorem store_update_canonical:
  "store_canonical tree \<Longrightarrow> store_canonical (store_update tree key value)"
  by (induction key arbitrary: tree)
    (auto intro: store_canonical_compact store_canonical_children)

fun counted_store_lookup where
  "counted_store_lookup tree []=(store_value tree,1::nat)"
| "counted_store_lookup tree (go_right#key)=(let result=counted_store_lookup
    (if go_right then store_right tree else store_left tree) key in (fst result,Suc (snd result)))"

theorem counted_store_lookup_exact:
  "counted_store_lookup tree key=(store_lookup tree key,Suc (length key))"
  by (induction key arbitrary: tree) (simp_all add: Let_def)

fun counted_store_update where
  "counted_store_update tree [] value=(compact_store_node value (store_left tree) (store_right tree),1::nat)"
| "counted_store_update tree (go_right#key) value=(let result=counted_store_update
    (if go_right then store_right tree else store_left tree) key value in
      (if go_right then compact_store_node (store_value tree) (store_left tree) (fst result)
       else compact_store_node (store_value tree) (fst result) (store_right tree),Suc (snd result)))"

theorem counted_store_update_exact:
  "counted_store_update tree key value=(store_update tree key value,Suc (length key))"
  by (induction key arbitrary: tree) (simp_all add: Let_def)

theorem store_off_path_preserved:
  "query\<noteq>key \<Longrightarrow> store_lookup (store_update tree key value) query=store_lookup tree query"
  by simp

text \<open>
  A read and an update inspect only the requested binary path. Instrumentation
  counts one visited position for the root and each path component; empty
  subtrees retain the same traversal equation. No other branch is traversed.
  Updating a canonical store compacts empty branches and preserves every other
  lookup. Key encoding, value construction and comparison, and physical costs
  are distinct from this explicit structural step count.
\<close>

end
