theory RRA_Indexed_Artifact_Lookup
  imports Binary_Relation_Stores RRA_Binary_Use_Paths RRA_Executable_Citations
begin

definition artifact_relation_store where
  "artifact_relation_store rows=relation_store (map (\<lambda>(u,C). (use_binary_path u,C)) rows)"

definition indexed_artifacts_at where
  "indexed_artifacts_at tree u=relation_store_lookup tree (use_binary_path u)"

theorem indexed_artifacts_at_exact:
  "indexed_artifacts_at (artifact_relation_store rows) u=
    finite_artifacts_at (finite_enumerated_environment rows bindings) u"
  by (auto simp: indexed_artifacts_at_def artifact_relation_store_def relation_store_member
    finite_artifacts_at_member finite_enumerated_environment_def fset_of_list.rep_eq
    intro!: fset_inject[THEN iffD1] set_eqI)

theorem indexed_artifacts_insert:
  "indexed_artifacts_at (relation_store_insert (use_binary_path u,C) tree) v=
    (if v=u then finsert C (indexed_artifacts_at tree v) else indexed_artifacts_at tree v)"
  by (simp add: indexed_artifacts_at_def)

theorem indexed_artifact_lookup_steps:
  "snd (counted_store_lookup tree (use_binary_path u))=Suc (length (use_binary_path u))"
  by (simp only: counted_store_lookup_exact snd_conv)

export_code artifact_relation_store indexed_artifacts_at counted_store_lookup counted_store_update checking SML

end
