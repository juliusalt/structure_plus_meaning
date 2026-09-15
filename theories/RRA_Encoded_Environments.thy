theory RRA_Encoded_Environments
  imports RRA_Environment_Lookup_Contracts
begin

definition encoded_environment_artifacts where
  "encoded_environment_artifacts use_code I u=relation_store_lookup (indexed_artifact_store I) (use_code u)"

definition encoded_environment_bindings where
  "encoded_environment_bindings use_code slot_code I u k=
    nested_relation_lookup (indexed_binding_store I) (use_code u) (slot_code k)"

definition encoded_environment_represents where
  "encoded_environment_represents use_code slot_code I E=environment_lookup_represents
    (encoded_environment_artifacts use_code I) (encoded_environment_bindings use_code slot_code I) E"

definition encoded_environment_rows where
  "encoded_environment_rows use_code slot_code A B=\<lparr>
    indexed_artifact_store=relation_store (map (\<lambda>(u,R). (use_code u,R)) A),
    indexed_binding_store=nested_relation_store
      (map (\<lambda>((u,k),v). ((use_code u,slot_code k),v)) B)\<rparr>"

definition encoded_insert_artifact where
  "encoded_insert_artifact use_code I u R=I\<lparr>indexed_artifact_store:=
    relation_store_insert (use_code u,R) (indexed_artifact_store I)\<rparr>"

definition encoded_insert_binding where
  "encoded_insert_binding use_code slot_code I u k v=I\<lparr>indexed_binding_store:=
    nested_relation_insert (use_code u) (slot_code k) v (indexed_binding_store I)\<rparr>"

locale environment_key_encoding =
  fixes use_code :: "local_address option\<Rightarrow>bool list"
    and slot_code :: "local_address\<Rightarrow>bool list"
  assumes use_injective: "inj use_code" and slot_injective: "inj slot_code"
begin

lemma use_code_eq [simp]: "use_code u=use_code v \<longleftrightarrow> u=v"
  using use_injective by (auto simp: inj_on_def)

lemma slot_code_eq [simp]: "slot_code k=slot_code j \<longleftrightarrow> k=j"
  using slot_injective by (auto simp: inj_on_def)

theorem rows_exact:
  "encoded_environment_represents use_code slot_code (encoded_environment_rows use_code slot_code A B)
    (finite_enumerated_environment A B)"
  by (auto simp: encoded_environment_represents_def environment_lookup_represents_def
    encoded_environment_rows_def encoded_environment_artifacts_def encoded_environment_bindings_def
    relation_store_member nested_relation_store_member finite_enumerated_environment_def
    fset_of_list.rep_eq; force)

lemma insert_artifact_lookups [simp]:
  "encoded_environment_artifacts use_code (encoded_insert_artifact use_code I u R) v=
    (if v=u then finsert R (encoded_environment_artifacts use_code I v)
      else encoded_environment_artifacts use_code I v)"
  "encoded_environment_bindings use_code slot_code (encoded_insert_artifact use_code I u R) v k=
    encoded_environment_bindings use_code slot_code I v k"
  by (simp_all add: encoded_environment_artifacts_def encoded_environment_bindings_def encoded_insert_artifact_def)

lemma insert_binding_lookups [simp]:
  "encoded_environment_artifacts use_code (encoded_insert_binding use_code slot_code I u k v) w=
    encoded_environment_artifacts use_code I w"
  "encoded_environment_bindings use_code slot_code (encoded_insert_binding use_code slot_code I u k v) w j=
    (if w=u \<and> j=k then finsert v (encoded_environment_bindings use_code slot_code I w j)
      else encoded_environment_bindings use_code slot_code I w j)"
  by (simp_all add: encoded_environment_artifacts_def encoded_environment_bindings_def encoded_insert_binding_def)

theorem insert_artifact_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_represents use_code slot_code (encoded_insert_artifact use_code I u R)
      (finite_add_artifact_use E u R)"
  by (auto simp: encoded_environment_represents_def environment_lookup_represents_def finite_add_artifact_use_def)

theorem insert_binding_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_represents use_code slot_code (encoded_insert_binding use_code slot_code I u k v)
      (finite_add_source_bindings E u {|(k,v)|})"
  by (auto simp: encoded_environment_represents_def environment_lookup_represents_def finite_add_source_bindings_def)

end

end
