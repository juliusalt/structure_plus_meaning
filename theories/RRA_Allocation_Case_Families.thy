theory RRA_Allocation_Case_Families
  imports RRA_Allocated_Environment_Cases
begin

type_synonym 'q allocation_case_loader =
  "(local_address option\<times>finite_exact_artifact) list\<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>'q option"

definition allocation_case_chain ::
  "'q allocation_case_loader\<Rightarrow>('q\<Rightarrow>finite_exact_artifact\<Rightarrow>'q option)\<Rightarrow>nat\<Rightarrow>'q option" where
  "allocation_case_chain load allocate n=foldl (\<lambda>current i. case current of None \<Rightarrow> None
    | Some q \<Rightarrow> allocate q (finite_payload_syntax [8]))
    (load [(None,finite_payload_syntax [7])] []) [0..<n]"

definition allocation_case_family ::
  "'q\<Rightarrow>'q allocation_case_loader\<Rightarrow>('q\<Rightarrow>finite_exact_artifact\<Rightarrow>'q option)\<Rightarrow>
    nat\<Rightarrow>'q option\<times>allocated_environment_update" where
  "allocation_case_family initial load allocate w=(let A=finite_payload_syntax [7];B=finite_payload_syntax [8];
    bad=finite_payload_syntax [256];base=load [(None,A),(Some [],B)] [] in
    if w=0 then (Some initial,Allocate_Artifact A)
    else if w=1 then (base,Allocate_Artifact B)
    else if w=2 then (load [(Some [300],A)] [],Allocate_Artifact B)
    else if w=3 then (allocation_case_chain load allocate 32,Allocate_Artifact A)
    else if w=4 then (allocation_case_chain load allocate 128,Allocate_Artifact B)
    else if w=5 then (Some initial,Allocate_Artifact bad)
    else if w=6 then (load [(None,A)] [],Add_Allocated_Binding None [] (Some []))
    else if w=7 then (base,Add_Allocated_Binding None [7] (Some []))
    else if w=8 then (load [(None,A),(Some [],B)] [((None,[]),Some [])],Add_Allocated_Binding None [] (Some []))
    else if w=9 then (base,Add_Allocated_Binding None [] None)
    else if w=10 then (load [(None,A),(None,B)] [],Allocate_Artifact A)
    else if w=11 then (load [(None,bad)] [],Allocate_Artifact A)
    else if w=12 then (load [(Some [],A)] [],Allocate_Artifact B)
    else if w=13 then (load [(Some (replicate 128 0),A)] [],Allocate_Artifact B)
    else if w=14 then (allocation_case_chain load allocate 2,Add_Allocated_Binding (Some [1]) [] (Some [2]))
    else (base,Add_Allocated_Binding (Some [99]) [] None))"

lemma original_allocation_chain_instance:
  "allocation_case_chain load_allocated_environment allocate_environment_artifact n=allocated_environment_chain n"
  by (simp only: allocation_case_chain_def allocated_environment_chain_def)

lemma original_allocation_case_instance:
  "allocation_case_family empty_allocated_environment load_allocated_environment allocate_environment_artifact w=
    allocated_update_case w"
  by (simp only: allocation_case_family_def allocated_update_case_def original_allocation_chain_instance)

text \<open>
  The same original source rows and operations instantiate each storage API.
  Chains apply the supplied allocator to each preceding prepared state. The
  old complete case family is recovered for every index, not copied as a table
  of expected outputs or supplied satisfaction values.
\<close>

end
