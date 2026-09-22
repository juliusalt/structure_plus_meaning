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

text \<open>
  The binding store is the nested store's index read through the pair of a use path and an address path,
  both injective: its member equation is the nested store's
  (@{thm [source] nested_store_carrier_index}) through that key, and its insertion the nested store's update.
\<close>

lemma binding_relation_store_carrier_index:
  "carrier_index (\<lambda>rows q v. (q,v)\<in>set rows) (\<lambda>_. True) UNIV
    (\<lambda>(u,k). (use_binary_path u,address_binary_path k))
    (\<lambda>rows. nested_relation_store (map (\<lambda>((u,k),v). ((use_binary_path u,address_binary_path k),v)) rows))
    (\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k))"
proof (rule carrier_index_through_key[OF nested_store_carrier_index])
  show "inj_on (\<lambda>(u,k). (use_binary_path u,address_binary_path k)) UNIV" by (auto simp: inj_on_def)
qed force+

interpretation binding_relation_index: carrier_index "\<lambda>rows q v. (q,v)\<in>set rows" "\<lambda>_. True" UNIV
    "\<lambda>(u,k). (use_binary_path u,address_binary_path k)"
    "\<lambda>rows. nested_relation_store (map (\<lambda>((u,k),v). ((use_binary_path u,address_binary_path k),v)) rows)"
    "\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k)"
  by (rule binding_relation_store_carrier_index)

theorem index_environment_rows_exact:
  "indexed_environment_represents (index_environment_rows A B) (finite_enumerated_environment A B)"
proof -
  have artifacts: "\<And>u R. R |\<in>| indexed_environment_artifacts (index_environment_rows A B) u \<longleftrightarrow> (u,R)\<in>set A"
    using artifact_relation_index.query_search
    by (simp add: index_environment_rows_def indexed_environment_artifacts_def indexed_artifacts_at_def)
  have bindings: "\<And>u k v. v |\<in>| indexed_environment_bindings (index_environment_rows A B) u k \<longleftrightarrow> ((u,k),v)\<in>set B"
  proof -
    fix u k v
    show "v |\<in>| indexed_environment_bindings (index_environment_rows A B) u k \<longleftrightarrow> ((u,k),v)\<in>set B"
      using binding_relation_index.query_search[where c=B and q="(u,k)" and v=v]
      by (simp add: index_environment_rows_def indexed_environment_bindings_def)
  qed
  show ?thesis
    by (simp add: indexed_environment_represents_def artifacts bindings finite_enumerated_environment_def
      fset_of_list.rep_eq)
qed

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
    indexed_environment_bindings_def indexed_artifacts_insert del: relation_store_lookup_insert)

lemma indexed_insert_binding_lookups [simp]:
  "indexed_environment_artifacts (indexed_insert_binding I u k v) w=indexed_environment_artifacts I w"
  "indexed_environment_bindings (indexed_insert_binding I u k v) w j=
    (if w=u \<and> j=k then finsert v (indexed_environment_bindings I w j)
     else indexed_environment_bindings I w j)"
   apply (simp add: indexed_environment_artifacts_def indexed_insert_binding_def)
  apply (rule fset_eqI)
  using nested_store_updates.updated[where i="indexed_binding_store I"
      and k="(use_binary_path u,address_binary_path k)" and u=v and k'="(use_binary_path w,address_binary_path j)"]
  by (simp add: indexed_environment_bindings_def indexed_insert_binding_def del: nested_relation_lookup_insert)

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
