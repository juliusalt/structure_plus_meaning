theory RRA_Indexed_Artifact_Lookup
  imports Binary_Store_Indexes RRA_Binary_Use_Paths RRA_Executable_Citations
begin

definition artifact_relation_store where
  "artifact_relation_store rows=relation_store (map (\<lambda>(u,C). (use_binary_path u,C)) rows)"

definition indexed_artifacts_at where
  "indexed_artifacts_at tree u=relation_store_lookup tree (use_binary_path u)"

text \<open>
  The artifact store is the relation store's index read through the use path: its carrier is the list of
  artifact rows, its key the injective path of a use (@{thm [source] use_binary_path_injective}), and its
  member equation is the relation store's (@{thm [source] relation_store_carrier_index}) through that key.
\<close>

lemma artifact_relation_store_carrier_index:
  "carrier_index (\<lambda>rows u C. (u,C)\<in>set rows) (\<lambda>_. True) UNIV use_binary_path artifact_relation_store
    (\<lambda>T k C. C |\<in>| relation_store_lookup T k)"
proof -
  have "carrier_index (\<lambda>rows u C. (u,C)\<in>set rows) (\<lambda>_. True) UNIV use_binary_path
      (\<lambda>rows. relation_store (map (\<lambda>(u,C). (use_binary_path u,C)) rows)) (\<lambda>T k C. C |\<in>| relation_store_lookup T k)"
  proof (rule carrier_index_through_key[OF relation_store_carrier_index])
    show "inj_on use_binary_path UNIV" by (rule inj_onI) simp
  qed force+
  then show ?thesis by (simp only: artifact_relation_store_def[abs_def])
qed

interpretation artifact_relation_index: carrier_index "\<lambda>rows u C. (u,C)\<in>set rows" "\<lambda>_. True" UNIV
    use_binary_path artifact_relation_store "\<lambda>T k C. C |\<in>| relation_store_lookup T k"
  by (rule artifact_relation_store_carrier_index)

theorem indexed_artifacts_at_exact:
  "indexed_artifacts_at (artifact_relation_store rows) u=
    finite_artifacts_at (finite_enumerated_environment rows bindings) u"
proof (rule fset_eqI)
  fix C
  have "C |\<in>| indexed_artifacts_at (artifact_relation_store rows) u \<longleftrightarrow> (u,C)\<in>set rows"
    using artifact_relation_index.query_search[where c=rows and q=u and v=C] by (simp add: indexed_artifacts_at_def)
  then show "C |\<in>| indexed_artifacts_at (artifact_relation_store rows) u \<longleftrightarrow>
      C |\<in>| finite_artifacts_at (finite_enumerated_environment rows bindings) u"
    by (auto simp: finite_artifacts_at_member finite_enumerated_environment_def fset_of_list.rep_eq)
qed

theorem indexed_artifacts_insert:
  "indexed_artifacts_at (relation_store_insert (use_binary_path u,C) tree) v=
    (if v=u then finsert C (indexed_artifacts_at tree v) else indexed_artifacts_at tree v)"
proof (rule fset_eqI)
  fix D
  show "D |\<in>| indexed_artifacts_at (relation_store_insert (use_binary_path u,C) tree) v \<longleftrightarrow>
      D |\<in>| (if v=u then finsert C (indexed_artifacts_at tree v) else indexed_artifacts_at tree v)"
  proof (cases "v=u")
    case True
    then show ?thesis
      using relation_store_updates.update_at[where i=tree and k="use_binary_path u" and u=C and v=D]
      by (simp add: indexed_artifacts_at_def)
  next
    case False
    then have "use_binary_path v\<noteq>use_binary_path u" by simp
    then show ?thesis using relation_store_updates.update_preserves_else[where k'="use_binary_path v"
        and k="use_binary_path u" and i=tree and u=C and v=D] False
      by (simp add: indexed_artifacts_at_def)
  qed
qed

theorem indexed_artifact_lookup_steps:
  "snd (counted_store_lookup tree (use_binary_path u))=Suc (length (use_binary_path u))"
  by (simp only: counted_store_lookup_exact snd_conv)

end
