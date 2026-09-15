theory RRA_Digit_Allocation_Paths
  imports RRA_Digit_Allocation_Methods
begin

definition digit_allocation_case :: "nat\<Rightarrow>digit_allocation_subject" where
  "digit_allocation_case=allocation_case_family empty_digit_allocated load_digit_allocated digit_allocated_allocate"

definition digit_allocation_chain where
  "digit_allocation_chain=allocation_case_chain load_digit_allocated digit_allocated_allocate"

definition digit_allocation_path where
  "digit_allocation_path q R=(let raw=raw_digit_allocated q;I=snd raw;
    u=bounded_environment_next_use raw;key=digit_use_path u;tree=indexed_artifact_store I;
    inserted=counted_relation_store_insert (key,R) tree in
    (key,counted_store_lookup tree key,snd inserted,relation_store_lookup (fst inserted) key,
      encoded_environment_view read_digit_use_path read_digit_address_path
        (I\<lparr>indexed_artifact_store:=fst inserted\<rparr>)))"

lemma digit_allocation_counted_insertion:
  "I\<lparr>indexed_artifact_store:=fst (counted_relation_store_insert (digit_use_path u,R)
      (indexed_artifact_store I))\<rparr>=encoded_insert_artifact digit_use_path I u R"
  by (simp add: counted_relation_store_insert_exact encoded_insert_artifact_def)

theorem digit_allocation_next_path_counts:
  "snd (counted_relation_store_insert
    (digit_use_path (bounded_environment_next_use (raw_digit_allocated q)),R)
    (indexed_artifact_store (snd (raw_digit_allocated q))))=
    (2*length (natural_binary_digits (fst (raw_digit_allocated q)))+3,
      2*length (natural_binary_digits (fst (raw_digit_allocated q)))+3)"
  by (simp add: counted_relation_store_insert_exact bounded_environment_next_use_def digit_address_path_length)

definition digit_allocation_state_report where
  "digit_allocation_state_report q=(let raw=raw_digit_allocated q;I=snd raw in
    (digit_allocated_view q,digit_allocated_next_use q,digit_allocated_artifacts q None,
      counted_store_lookup (indexed_artifact_store I) (digit_use_path None)))"

definition digit_allocation_chain_paths where
  "digit_allocation_chain_paths n=map_option (\<lambda>q. (digit_allocation_state_report q,
    digit_allocation_path q (finite_payload_syntax [9]))) (digit_allocation_chain n)"

definition allocation_case_views where
  "allocation_case_views w=((let X=allocated_update_case w in
    (map_option (\<lambda>q. allocated_environment_view (raw_allocated_environment q)) (fst X),snd X)),
    (let X=digit_allocation_case w in (map_option digit_allocated_view (fst X),snd X)))"

definition allocation_case_views_equal where
  "allocation_case_views_equal w=(fst (allocation_case_views w)=snd (allocation_case_views w))"


definition allocation_original_context where
  "allocation_original_context w=(let X=allocated_update_case w in
    ((map_option (\<lambda>q. allocated_environment_view (raw_allocated_environment q)) (fst X),snd X),
      allocated_update_reference X))"

definition allocation_case_result_pairs where
  "allocation_case_result_pairs w=(let X=allocated_update_case w;Y=digit_allocation_case w in
    map (\<lambda>m. let original=allocated_update_method m X;digit=digit_allocation_method m Y in
      (m,original,digit,original=digit)) [0..<12])"

text \<open>
  Each path report uses an actual typed state produced by the persistent chain,
  its actual stored next head, and both traversals of the original relation
  insertion. The complete resulting environment remains visible. Counts exclude
  key construction, natural arithmetic, finite-value work and whole-view reporting.
\<close>

end
