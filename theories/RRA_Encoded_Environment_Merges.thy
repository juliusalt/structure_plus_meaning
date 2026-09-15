theory RRA_Encoded_Environment_Merges
  imports RRA_Encoded_Environment_Views
begin

fun encoded_artifact_rows :: "(local_address option\<Rightarrow>bool list)\<Rightarrow>
    (local_address option\<times>finite_exact_artifact) list\<Rightarrow>
    indexed_artifact_environment\<Rightarrow>indexed_artifact_environment" where
  "encoded_artifact_rows use_code [] I=I"
| "encoded_artifact_rows use_code ((u,R)#rows) I=
    encoded_artifact_rows use_code rows (encoded_insert_artifact use_code I u R)"

fun encoded_binding_rows :: "(local_address option\<Rightarrow>bool list)\<Rightarrow>(local_address\<Rightarrow>bool list)\<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>
    indexed_artifact_environment\<Rightarrow>indexed_artifact_environment" where
  "encoded_binding_rows use_code slot_code [] I=I"
| "encoded_binding_rows use_code slot_code (((u,k),v)#rows) I=
    encoded_binding_rows use_code slot_code rows (encoded_insert_binding use_code slot_code I u k v)"

definition encoded_merge_rows where
  "encoded_merge_rows use_code slot_code I A B=
    encoded_binding_rows use_code slot_code B (encoded_artifact_rows use_code A I)"

context environment_key_encoding
begin

lemma artifact_rows_artifacts:
  "R |\<in>| encoded_environment_artifacts use_code (encoded_artifact_rows use_code A I) u \<longleftrightarrow>
    R |\<in>| encoded_environment_artifacts use_code I u \<or> (u,R)\<in>set A"
proof (induction A arbitrary: I)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  obtain v S where row: "a=(v,S)" by (cases a) auto
  show ?case by (simp only: row encoded_artifact_rows.simps Cons.IH insert_artifact_lookups)
    (auto split: if_splits)
qed

lemma artifact_rows_bindings:
  "encoded_environment_bindings use_code slot_code (encoded_artifact_rows use_code A I) u k=
    encoded_environment_bindings use_code slot_code I u k"
proof (induction A arbitrary: I)
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  obtain v S where row: "a=(v,S)" by (cases a) auto
  show ?case by (simp only: row encoded_artifact_rows.simps Cons.IH insert_artifact_lookups)
qed

lemma binding_rows_artifacts:
  "encoded_environment_artifacts use_code (encoded_binding_rows use_code slot_code B I) u=
    encoded_environment_artifacts use_code I u"
proof (induction B arbitrary: I)
  case Nil
  then show ?case by simp
next
  case (Cons b B)
  obtain v k w where row: "b=((v,k),w)" by (cases b) auto
  show ?case by (simp only: row encoded_binding_rows.simps Cons.IH insert_binding_lookups)
qed

lemma binding_rows_bindings:
  "v |\<in>| encoded_environment_bindings use_code slot_code (encoded_binding_rows use_code slot_code B I) u k \<longleftrightarrow>
    v |\<in>| encoded_environment_bindings use_code slot_code I u k \<or> ((u,k),v)\<in>set B"
proof (induction B arbitrary: I)
  case Nil
  then show ?case by simp
next
  case (Cons b B)
  obtain v j w where row: "b=((v,j),w)" by (cases b) auto
  show ?case by (simp only: row encoded_binding_rows.simps Cons.IH insert_binding_lookups)
    (auto split: if_splits)
qed

theorem merge_rows_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_represents use_code slot_code (encoded_merge_rows use_code slot_code I A B)
      (finite_merge_environment E (finite_enumerated_environment A B))"
  by (auto simp: encoded_environment_represents_def environment_lookup_represents_def encoded_merge_rows_def
    artifact_rows_artifacts artifact_rows_bindings binding_rows_artifacts binding_rows_bindings
    finite_merge_environment_def finite_enumerated_environment_def fset_of_list.rep_eq)

end

context environment_key_codec
begin

theorem merge_rows_view:
  "encoded_environment_view use_decode slot_decode (encoded_merge_rows use_code slot_code I A B)=
    finite_merge_environment (encoded_environment_view use_decode slot_decode I) (finite_enumerated_environment A B)"
  by (rule view_representation; rule merge_rows_exact; rule view_exact)

end

text \<open>
  The batch operation inserts complete supplied artifact and binding rows into
  the existing actual index. It traverses those lists and their insertion paths.
  Whole-view equality is proved for every original lookup without scanning the
  old environment during the operation. Formation and conflicting values remain
  separate; raw merge preserves every row on both sides.
\<close>

end
