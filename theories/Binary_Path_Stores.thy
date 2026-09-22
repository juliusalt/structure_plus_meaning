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

lemma path_store_fold_canonical:
  "store_canonical T \<Longrightarrow> store_canonical (fold (\<lambda>(k,v) T. store_update T k (Some v)) rows T)"
  by (induction rows arbitrary: T) (auto simp: split_beta intro: store_update_canonical)

text \<open>A canonical store is determined by its lookups.\<close>

lemma store_canonical_none:
  assumes "store_canonical T" "\<And>q. store_lookup T q=None"
  shows "T=Empty_Store"
  using assms
proof (induction T)
  case Empty_Store
  then show ?case by simp
next
  case (Store_Node v l r)
  have v: "v=None" using Store_Node.prems(2)[of "[]"] by simp
  have l: "l=Empty_Store"
  proof (rule Store_Node.IH(1))
    show "store_canonical l" using Store_Node.prems(1) by simp
    show "store_lookup l q=None" for q using Store_Node.prems(2)[of "False#q"] by simp
  qed
  have r: "r=Empty_Store"
  proof (rule Store_Node.IH(2))
    show "store_canonical r" using Store_Node.prems(1) by simp
    show "store_lookup r q=None" for q using Store_Node.prems(2)[of "True#q"] by simp
  qed
  show ?case using Store_Node.prems(1) v l r by simp
qed

theorem store_canonical_lookup_eq:
  assumes "store_canonical S" "store_canonical T" "\<And>q. store_lookup S q=store_lookup T q"
  shows "S=T"
  using assms
proof (induction S arbitrary: T)
  case Empty_Store
  have "store_lookup T q=None" for q using Empty_Store.prems(3)[of q] by simp
  from store_canonical_none[OF Empty_Store.prems(2) this] show ?case by simp
next
  case (Store_Node v l r)
  note prems=Store_Node.prems and IH=Store_Node.IH
  show ?case
  proof (cases T)
    case Empty_Store
    have "store_lookup (Store_Node v l r) q=None" for q using prems(3)[of q] Empty_Store by simp
    from store_canonical_none[OF prems(1) this] show ?thesis by simp
  next
    case (Store_Node v' l' r')
    have v: "v=v'" using prems(3)[of "[]"] Store_Node by simp
    have l: "l=l'"
    proof (rule IH(1))
      show "store_canonical l" using prems(1) by simp
      show "store_canonical l'" using prems(2) Store_Node by simp
      show "store_lookup l q=store_lookup l' q" for q using prems(3)[of "False#q"] Store_Node by simp
    qed
    have r: "r=r'"
    proof (rule IH(2))
      show "store_canonical r" using prems(1) by simp
      show "store_canonical r'" using prems(2) Store_Node by simp
      show "store_lookup r q=store_lookup r' q" for q using prems(3)[of "True#q"] Store_Node by simp
    qed
    show ?thesis using Store_Node v l r by simp
  qed
qed

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
