theory RRA_Indexed_Environments
  imports RRA_Indexed_Artifact_Lookup Binary_Nested_Stores RRA_Finite_Environment_Construction
begin

record indexed_artifact_environment =
  indexed_artifact_store :: "finite_exact_artifact fset binary_path_store"
  indexed_binding_store :: "(local_address option fset binary_path_store) binary_path_store"

definition indexed_environment_artifacts where
  "indexed_environment_artifacts I u=indexed_artifacts_at (indexed_artifact_store I) u"

definition indexed_environment_bindings where
  "indexed_environment_bindings I u k=nested_relation_lookup (indexed_binding_store I)
    (use_binary_path u) (address_binary_path k)"

definition indexed_environment_represents where
  "indexed_environment_represents I E \<longleftrightarrow>
    (\<forall>u R. R |\<in>| indexed_environment_artifacts I u \<longleftrightarrow>
      (u,R) |\<in>| finite_environment_artifacts E) \<and>
    (\<forall>u k v. v |\<in>| indexed_environment_bindings I u k \<longleftrightarrow>
      ((u,k),v) |\<in>| finite_environment_bindings E)"

definition index_environment_rows where
  "index_environment_rows A B=\<lparr>indexed_artifact_store=artifact_relation_store A,
    indexed_binding_store=nested_relation_store
      (map (\<lambda>((u,k),v). ((use_binary_path u,address_binary_path k),v)) B)\<rparr>"

theorem index_environment_rows_exact:
  "indexed_environment_represents (index_environment_rows A B) (finite_enumerated_environment A B)"
  by (auto simp: indexed_environment_represents_def index_environment_rows_def
    indexed_environment_artifacts_def indexed_artifacts_at_def artifact_relation_store_def
    indexed_environment_bindings_def relation_store_member nested_relation_store_member
    finite_enumerated_environment_def fset_of_list.rep_eq; force)

definition indexed_insert_artifact where
  "indexed_insert_artifact I u R=I\<lparr>indexed_artifact_store:=
    relation_store_insert (use_binary_path u,R) (indexed_artifact_store I)\<rparr>"

definition indexed_insert_binding where
  "indexed_insert_binding I u k v=I\<lparr>indexed_binding_store:=
    nested_relation_insert (use_binary_path u) (address_binary_path k) v (indexed_binding_store I)\<rparr>"

lemma indexed_insert_artifact_lookups [simp]:
  "indexed_environment_artifacts (indexed_insert_artifact I u R) v=
    (if v=u then finsert R (indexed_environment_artifacts I v) else indexed_environment_artifacts I v)"
  "indexed_environment_bindings (indexed_insert_artifact I u R) v k=indexed_environment_bindings I v k"
  by (simp_all add: indexed_environment_artifacts_def indexed_insert_artifact_def
    indexed_environment_bindings_def indexed_artifacts_at_def)

lemma indexed_insert_binding_lookups [simp]:
  "indexed_environment_artifacts (indexed_insert_binding I u k v) w=indexed_environment_artifacts I w"
  "indexed_environment_bindings (indexed_insert_binding I u k v) w j=
    (if w=u \<and> j=k then finsert v (indexed_environment_bindings I w j)
     else indexed_environment_bindings I w j)"
  by (simp_all add: indexed_environment_artifacts_def indexed_insert_binding_def
    indexed_environment_bindings_def)

theorem indexed_insert_artifact_exact:
  "indexed_environment_represents I E \<Longrightarrow>
    indexed_environment_represents (indexed_insert_artifact I u R) (finite_add_artifact_use E u R)"
  by (auto simp: indexed_environment_represents_def finite_add_artifact_use_def)

theorem indexed_insert_binding_exact:
  "indexed_environment_represents I E \<Longrightarrow>
    indexed_environment_represents (indexed_insert_binding I u k v) (finite_add_source_bindings E u {|(k,v)|})"
  by (auto simp: indexed_environment_represents_def finite_add_source_bindings_def)

text \<open>
  A complete environment is the independently defined subject. This index
  implements both original finite relations, including conflicting rows on
  arbitrary input. Formation is separate from representation. The update
  equations preserve every original value and binding, not only a selected
  query or a finite sample of observations.
\<close>

end
