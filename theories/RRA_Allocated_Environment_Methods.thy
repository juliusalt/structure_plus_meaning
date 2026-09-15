theory RRA_Allocated_Environment_Methods
  imports RRA_Allocated_Environment_References
begin

definition allocated_update_variant where
  "allocated_update_variant (m::nat) q op=(let n=fst q;I=snd q;actual=allocated_environment_update_raw q op in
    if m=2 then map_option (\<lambda>r. (n,snd r)) actual
    else if m=3 then (case op of Allocate_Artifact R \<Rightarrow>
      Some (Suc n,indexed_insert_artifact I (Some [n]) R) | _ \<Rightarrow> actual)
    else if m=4 then map_option (\<lambda>r. (0,snd r)) actual
    else if m=5 then (case op of Allocate_Artifact R \<Rightarrow>
      if finite_exact_formed R then Some (Suc n,indexed_insert_artifact I (Some [n,0]) R) else None
      | _ \<Rightarrow> actual)
    else if m=6 then (case op of Add_Allocated_Binding u k v \<Rightarrow>
      Some (n,indexed_insert_binding I u k v) | _ \<Rightarrow> actual)
    else if m=10 then Some q else if m=11 then None else actual)"

definition allocated_update_method :: "nat\<Rightarrow>allocated_update_subject\<Rightarrow>allocated_update_value fset" where
  "allocated_update_method m X=(if m=7 then {||}
    else if m=8 then finsert None (allocated_update_reference X)
    else case X of (input,op) \<Rightarrow> case input of
      None \<Rightarrow> (if m=9 then {|None|} else {||})
    | Some q \<Rightarrow> {|if m=0 then map_option
        (\<lambda>r. allocated_environment_view (raw_allocated_environment r)) (allocated_environment_update_typed q op)
      else if m=1 then allocated_update_reference_option q op
      else map_option allocated_environment_view (allocated_update_variant m (raw_allocated_environment q) op)|})"

theorem allocated_update_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> allocated_update_method m X=allocated_update_reference X"
  by (cases X) (auto simp: allocated_update_method_def allocated_update_reference_def
    allocated_update_typed_exact split: option.splits)

definition allocated_update_condition where
  "allocated_update_condition f method X=relation_reader_condition (allocated_update_relation X) f (method X)"

definition allocated_update_context where
  "allocated_update_context X=(X,allocated_update_reference X)"

definition allocated_update_assessment where
  "allocated_update_assessment m context=(case context of (X,reference) \<Rightarrow>
    (allocated_update_method m X,reference))"

definition allocated_update_inspect :: "(allocated_update_value fset\<times>allocated_update_value fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "allocated_update_inspect=finite_reader_inspect"

theorem allocated_update_assessment_exact:
  "allocated_update_inspect (allocated_update_assessment m (allocated_update_context X)) f=
    allocated_update_condition f (allocated_update_method m) X"
  by (simp only: allocated_update_inspect_def allocated_update_assessment_def allocated_update_context_def
    case_prod_conv allocated_update_condition_def finite_reader_inspect_exact[OF allocated_update_reference_exact])

end
