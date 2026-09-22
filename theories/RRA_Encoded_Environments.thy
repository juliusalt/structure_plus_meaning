theory RRA_Encoded_Environments
  imports RRA_Environment_Lookup_Contracts Binary_Store_Indexes
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

text \<open>
  An encoding is an index of each of the environment's two relations: the artifact rows through the use
  code, over the relation store, and the binding rows through the pair of the two codes, over the nested
  store. Both codes are injective, and each store's insertion is the update of its index.
\<close>

lemma artifact_carrier_index:
  "carrier_index (\<lambda>rows (u::local_address option) (R::finite_exact_artifact). (u,R)\<in>set rows) (\<lambda>_. True) UNIV
    use_code (\<lambda>rows. relation_store (map (\<lambda>(u,R). (use_code u,R)) rows))
    (\<lambda>T k R. R |\<in>| relation_store_lookup T k)"
  by (rule carrier_index_through_key[OF relation_store_carrier_index _ _ use_injective]) force+

lemma binding_carrier_index:
  "carrier_index (\<lambda>rows (q::local_address option\<times>local_address) v. (q,v)\<in>set rows)
    (\<lambda>_. True) UNIV (\<lambda>(u,k). (use_code u,slot_code k))
    (\<lambda>rows. nested_relation_store (map (\<lambda>((u,k),v). ((use_code u,slot_code k),v)) rows))
    (\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k))"
proof (rule carrier_index_through_key[OF nested_store_carrier_index])
  show "inj_on (\<lambda>(u,k). (use_code u,slot_code k)) UNIV" by (auto simp: inj_on_def)
qed force+

sublocale artifact_index: updated_carrier_index
    "\<lambda>rows (u::local_address option) (R::finite_exact_artifact). (u,R)\<in>set rows" "\<lambda>_. True" UNIV
    use_code "\<lambda>rows. relation_store (map (\<lambda>(u,R). (use_code u,R)) rows)"
    "\<lambda>T k R. R |\<in>| relation_store_lookup T k" "\<lambda>T k u. relation_store_insert (k,u) T" "\<lambda>u f v. v=u \<or> f v"
  by (rule updated_carrier_index.intro[OF artifact_carrier_index], rule updated_carrier_index_axioms.intro,
    rule relation_store_updates.updated)

sublocale binding_index: updated_carrier_index
    "\<lambda>rows (q::local_address option\<times>local_address) (v::local_address option). (q,v)\<in>set rows" "\<lambda>_. True" UNIV
    "\<lambda>(u,k). (use_code u,slot_code k)"
    "\<lambda>rows. nested_relation_store (map (\<lambda>((u,k),v). ((use_code u,slot_code k),v)) rows)"
    "\<lambda>T k v. v |\<in>| nested_relation_lookup T (fst k) (snd k)"
    "\<lambda>T k u. nested_relation_insert (fst k) (snd k) u T" "\<lambda>u f v. v=u \<or> f v"
  by (rule updated_carrier_index.intro[OF binding_carrier_index], rule updated_carrier_index_axioms.intro,
    rule nested_store_updates.updated)

lemma rows_artifact_lookup:
  "(R::finite_exact_artifact) |\<in>| relation_store_lookup (relation_store (map (\<lambda>(u,R). (use_code u,R)) rows)) (use_code u) \<longleftrightarrow>
    (u,R)\<in>set rows"
  using artifact_index.query_search[where c=rows and q=u and v=R] by simp

lemma rows_binding_lookup:
  "v |\<in>| nested_relation_lookup (nested_relation_store (map (\<lambda>((u,k),v). ((use_code u,slot_code k),v)) rows))
      (use_code u) (slot_code k) \<longleftrightarrow> ((u,k),v)\<in>set rows"
  using carrier_index.query_search[OF binding_carrier_index, where c=rows and q="(u,k)" and v=v] by simp

theorem rows_exact:
  "encoded_environment_represents use_code slot_code (encoded_environment_rows use_code slot_code A B)
    (finite_enumerated_environment A B)"
  by (simp add: encoded_environment_represents_def environment_lookup_represents_def
    encoded_environment_rows_def encoded_environment_artifacts_def encoded_environment_bindings_def
    rows_artifact_lookup rows_binding_lookup finite_enumerated_environment_def fset_of_list.rep_eq)

lemma insert_artifact_lookups [simp]:
  "encoded_environment_artifacts use_code (encoded_insert_artifact use_code I u R) v=
    (if v=u then finsert R (encoded_environment_artifacts use_code I v)
      else encoded_environment_artifacts use_code I v)"
  "encoded_environment_bindings use_code slot_code (encoded_insert_artifact use_code I u R) v k=
    encoded_environment_bindings use_code slot_code I v k"
   apply (rule fset_eqI)
   using artifact_index.updated[where i="indexed_artifact_store I" and k="use_code u" and u=R and k'="use_code v"]
   apply (simp add: encoded_environment_artifacts_def encoded_insert_artifact_def del: relation_store_lookup_insert)
  by (simp add: encoded_environment_bindings_def encoded_insert_artifact_def)

lemma insert_binding_lookups [simp]:
  "encoded_environment_artifacts use_code (encoded_insert_binding use_code slot_code I u k v) w=
    encoded_environment_artifacts use_code I w"
  "encoded_environment_bindings use_code slot_code (encoded_insert_binding use_code slot_code I u k v) w j=
    (if w=u \<and> j=k then finsert v (encoded_environment_bindings use_code slot_code I w j)
      else encoded_environment_bindings use_code slot_code I w j)"
   apply (simp add: encoded_environment_artifacts_def encoded_insert_binding_def)
  apply (rule fset_eqI)
  using binding_index.updated[where i="indexed_binding_store I" and k="(use_code u,slot_code k)" and u=v
      and k'="(use_code w,slot_code j)"]
  by (simp add: encoded_environment_bindings_def encoded_insert_binding_def del: nested_relation_lookup_insert)

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
