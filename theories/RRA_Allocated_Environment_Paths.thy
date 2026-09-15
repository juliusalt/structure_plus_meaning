theory RRA_Allocated_Environment_Paths
  imports RRA_Allocated_Environment_Methods Binary_Counted_Relation_Stores
begin

definition allocated_environment_allocation_path where
  "allocated_environment_allocation_path q R=(let raw=raw_allocated_environment q;
    I=snd raw;u=bounded_environment_next_use raw;key=use_binary_path u;tree=indexed_artifact_store I;
    inserted=counted_relation_store_insert (key,R) tree in
    (key,counted_store_lookup tree key,snd inserted,
      relation_store_lookup (fst inserted) key,
      indexed_environment_view (I\<lparr>indexed_artifact_store:=fst inserted\<rparr>)))"

lemma allocated_environment_counted_insertion:
  "I\<lparr>indexed_artifact_store:=fst (counted_relation_store_insert (use_binary_path u,R)
      (indexed_artifact_store I))\<rparr>=indexed_insert_artifact I u R"
  by (simp add: counted_relation_store_insert_exact indexed_insert_artifact_def)

theorem allocated_environment_next_path_counts:
  "snd (counted_relation_store_insert
      (use_binary_path (bounded_environment_next_use (raw_allocated_environment q)),R)
      (indexed_artifact_store (snd (raw_allocated_environment q))))=
    (fst (raw_allocated_environment q)+3,fst (raw_allocated_environment q)+3)"
  by (simp add: counted_relation_store_insert_exact bounded_environment_next_use_def natural_binary_path_length)

text \<open>
  The path observation inspects the actual next allocation coordinate and the
  actual relation insertion. Its whole resulting environment is the original
  indexed insertion. With the current unary component encoding, each of its
  two traversals visits next_head+3 positions. The fixed None lookup alone
  therefore cannot establish the cost of the next allocation.
\<close>

end
