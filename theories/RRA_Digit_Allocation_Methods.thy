theory RRA_Digit_Allocation_Methods
  imports RRA_Digit_Allocation_References RRA_Allocation_Case_Families
begin

definition digit_allocation_variant where
  "digit_allocation_variant (m::nat) q op=(let n=fst q;I=snd q;
    actual=encoded_bounded_update digit_use_path digit_address_path q op in
    if m=2 then map_option (\<lambda>r. (n,snd r)) actual
    else if m=3 then (case op of Allocate_Artifact R \<Rightarrow>
      Some (Suc n,encoded_insert_artifact digit_use_path I (Some [n]) R) | _ \<Rightarrow> actual)
    else if m=4 then map_option (\<lambda>r. (0,snd r)) actual
    else if m=5 then (case op of Allocate_Artifact R \<Rightarrow>
      if finite_exact_formed R then Some (Suc n,encoded_insert_artifact digit_use_path I (Some [n,0]) R) else None
      | _ \<Rightarrow> actual)
    else if m=6 then (case op of Add_Allocated_Binding u k v \<Rightarrow>
      Some (n,encoded_insert_binding digit_use_path digit_address_path I u k v) | _ \<Rightarrow> actual)
    else if m=10 then Some q else if m=11 then None else actual)"

definition digit_allocation_method :: "nat\<Rightarrow>digit_allocation_subject\<Rightarrow>allocated_update_value fset" where
  "digit_allocation_method m X=(if m=7 then {||}
    else if m=8 then finsert None (digit_allocation_reference X)
    else case X of (input,op) \<Rightarrow> case input of
      None \<Rightarrow> (if m=9 then {|None|} else {||})
    | Some q \<Rightarrow> {|if m=0 then map_option digit_allocated_view (digit_allocated_update q op)
      else if m=1 then finite_allocation_reference (digit_allocated_view q) op
      else map_option (encoded_bounded_view read_digit_use_path read_digit_address_path)
        (digit_allocation_variant m (raw_digit_allocated q) op)|})"

theorem digit_allocation_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> digit_allocation_method m X=digit_allocation_reference X"
  by (cases X) (auto simp: digit_allocation_method_def digit_allocation_reference_def
    digit_allocation_typed_exact split: option.splits)

definition digit_allocation_condition where
  "digit_allocation_condition f method X=relation_reader_condition (digit_allocation_relation X) f (method X)"

definition digit_allocation_context where
  "digit_allocation_context X=(X,digit_allocation_reference X)"

definition digit_allocation_assessment where
  "digit_allocation_assessment m context=(case context of (X,reference) \<Rightarrow>
    (digit_allocation_method m X,reference))"

definition digit_allocation_inspect :: "(allocated_update_value fset\<times>allocated_update_value fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "digit_allocation_inspect=finite_reader_inspect"

theorem digit_allocation_assessment_exact:
  "digit_allocation_inspect (digit_allocation_assessment m (digit_allocation_context X)) f=
    digit_allocation_condition f (digit_allocation_method m) X"
  by (simp only: digit_allocation_inspect_def digit_allocation_assessment_def digit_allocation_context_def
    case_prod_conv digit_allocation_condition_def finite_reader_inspect_exact[OF digit_allocation_reference_exact])

end
