theory Binary_Store_Entries
  imports Binary_Nested_Stores
begin

fun binary_store_entries where
  "binary_store_entries Empty_Store=[]"
| "binary_store_entries (Store_Node value left right)=
    (case value of None \<Rightarrow> [] | Some x \<Rightarrow> [([],x)]) @
    map (\<lambda>(key,x). (False#key,x)) (binary_store_entries left) @
    map (\<lambda>(key,x). (True#key,x)) (binary_store_entries right)"

theorem binary_store_entries_exact:
  "(key,x)\<in>set (binary_store_entries tree) \<longleftrightarrow> store_lookup tree key=Some x"
  by (induction tree arbitrary: key) (case_tac key; auto split: option.splits if_splits)+

definition relation_store_entries where
  "relation_store_entries tree=ffUnion (fimage (\<lambda>(key,bucket). fimage (Pair key) bucket)
    (fset_of_list (binary_store_entries tree)))"

theorem relation_store_entries_exact:
  "(key,x) |\<in>| relation_store_entries tree \<longleftrightarrow> x |\<in>| relation_store_lookup tree key"
  apply (cases "store_lookup tree key")
   apply (auto simp: relation_store_entries_def ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq
      binary_store_entries_exact relation_store_lookup_def split: prod.splits)
  subgoal for bucket
    by (rule bexI[where x="(key,bucket)"]) (auto simp: binary_store_entries_exact)
  done

definition nested_relation_entries where
  "nested_relation_entries tree=ffUnion (fimage (\<lambda>(outer,inner).
    fimage (\<lambda>(key,x). ((outer,key),x)) (relation_store_entries inner))
      (fset_of_list (binary_store_entries tree)))"

theorem nested_relation_entries_exact:
  "((outer,inner),x) |\<in>| nested_relation_entries tree \<longleftrightarrow>
    x |\<in>| nested_relation_lookup tree outer inner"
  apply (cases "store_lookup tree outer")
   apply (auto simp: nested_relation_entries_def ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq
      binary_store_entries_exact relation_store_entries_exact nested_relation_lookup_def
      nested_store_at_def split: prod.splits)
  subgoal for child
    by (rule bexI[where x="(outer,child)"])
      (auto simp: binary_store_entries_exact relation_store_entries_exact intro: rev_image_eqI)
  done

end
