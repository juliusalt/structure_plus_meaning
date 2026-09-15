theory RRA_Allocated_Environment_Cases
  imports RRA_Allocated_Environment_Paths
begin

definition allocated_environment_chain where
  "allocated_environment_chain n=foldl (\<lambda>current i. case current of None \<Rightarrow> None
    | Some q \<Rightarrow> allocate_environment_artifact q (finite_payload_syntax [8]))
    (load_allocated_environment [(None,finite_payload_syntax [7])] []) [0..<n]"

definition allocated_update_case :: "nat\<Rightarrow>allocated_update_subject" where
  "allocated_update_case w=(let A=finite_payload_syntax [7];B=finite_payload_syntax [8];
    bad=finite_payload_syntax [256];base=load_allocated_environment [(None,A),(Some [],B)] [] in
    if w=0 then (Some empty_allocated_environment,Allocate_Artifact A)
    else if w=1 then (base,Allocate_Artifact B)
    else if w=2 then (load_allocated_environment [(Some [300],A)] [],Allocate_Artifact B)
    else if w=3 then (allocated_environment_chain 32,Allocate_Artifact A)
    else if w=4 then (allocated_environment_chain 128,Allocate_Artifact B)
    else if w=5 then (Some empty_allocated_environment,Allocate_Artifact bad)
    else if w=6 then (load_allocated_environment [(None,A)] [],Add_Allocated_Binding None [] (Some []))
    else if w=7 then (base,Add_Allocated_Binding None [7] (Some []))
    else if w=8 then (load_allocated_environment [(None,A),(Some [],B)] [((None,[]),Some [])],
      Add_Allocated_Binding None [] (Some []))
    else if w=9 then (base,Add_Allocated_Binding None [] None)
    else if w=10 then (load_allocated_environment [(None,A),(None,B)] [],Allocate_Artifact A)
    else if w=11 then (load_allocated_environment [(None,bad)] [],Allocate_Artifact A)
    else if w=12 then (load_allocated_environment [(Some [],A)] [],Allocate_Artifact B)
    else if w=13 then (load_allocated_environment [(Some (replicate 128 0),A)] [],Allocate_Artifact B)
    else if w=14 then (allocated_environment_chain 2,Add_Allocated_Binding (Some [1]) [] (Some [2]))
    else (base,Add_Allocated_Binding (Some [99]) [] None))"

definition allocated_environment_state_report where
  "allocated_environment_state_report q=(let raw=raw_allocated_environment q;I=snd raw in
    (allocated_environment_view raw,bounded_environment_next_use raw,
      allocated_environment_artifacts q None,
      counted_store_lookup (indexed_artifact_store I) (use_binary_path None)))"

definition allocated_environment_chain_report where
  "allocated_environment_chain_report n=map_option allocated_environment_state_report (allocated_environment_chain n)"

definition allocated_environment_chain_paths where
  "allocated_environment_chain_paths n=map_option (\<lambda>q. (allocated_environment_state_report q,
    allocated_environment_allocation_path q (finite_payload_syntax [9]))) (allocated_environment_chain n)"

theorem allocated_environment_chain_previous:
  "map_option fst (allocated_environment_chain_paths n)=allocated_environment_chain_report n"
  by (simp add: allocated_environment_chain_paths_def allocated_environment_chain_report_def option.map_comp comp_def)

text \<open>
  Actual typed preparation and allocation supply the input states. Larger
  histories extend the same persistent store. Malformed old material leaves
  preparation unavailable; a malformed new artifact rejects an operation on
  an available state. Complete views expose these separate positions.
  The fixed original use is inspected after zero, 32 and 128 allocations.
\<close>

end
