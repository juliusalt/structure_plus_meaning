theory RRA_Generation_Record_References
  imports RRA_Generation_Record_Construction RRA_Generation_References
begin

context generation_record_construction
begin

theorem predecessor_references:
  "generation_predecessor_references installed record_use [] l p c=
    {(v i,snd (as!i)) | i. i<n}"
proof -
  have rows: "generation_frame_members n=
    {(generation_predecessor_socket n i,generation_predecessor_node i) | i. i\<in>{..<n}}"
    by (auto simp: generation_frame_members_def)
  have locations: "located_at installed record_use (generation_predecessor_node i) (v i) (snd (as!i))"
    if "i\<in>{..<n}" for i using properties(4) that by simp
  show ?thesis using generation_predecessor_references_indexed[OF properties(3) rows locations] by simp
qed

end

end
