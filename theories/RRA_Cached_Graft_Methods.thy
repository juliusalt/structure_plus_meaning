theory RRA_Cached_Graft_Methods
  imports RRA_Cached_Graft_References RRA_Graft_Case_Families
begin

definition cached_graft_variant where
  "cached_graft_variant (m::nat) q u A B=(let n=fst q;I=snd q;h=prefix_use_map [n] u;
    F=finite_enumerated_environment A B;artifacts=encoded_environment_artifacts digit_use_path I;
    bindings=encoded_environment_bindings digit_use_path digit_address_path I;
    ready=(if m=3 then finite_environment_formed F \<and> lookup_shared_graft_artifact artifacts u F
      else if m=4 then finite_environment_formed F \<and> lookup_boundary_bindings_compatible bindings h u F
      else if m=9 then True else lookup_graft_ready artifacts bindings h u F);
    chosen=(if m=11 then finite_compact_use_map
      (finite_environment_uses (encoded_environment_view read_digit_use_path read_digit_address_path I)) u else h);
    imported_bindings=(if m=5 then [] else B);
    following=encoded_graft_rows digit_use_path digit_address_path I chosen A imported_bindings;
    head=(if m=2 then n else if m=6 then 0 else if m=12 then n+2 else Suc n)
    in if m=10 then None else if m=13 then Some q else if ready then Some (head,following) else None)"

definition cached_graft_method :: "nat\<Rightarrow>cached_graft_subject\<Rightarrow>cached_graft_value fset" where
  "cached_graft_method m X=(if m=8 then {||} else case X of (input,u,A,B) \<Rightarrow>
    case input of None \<Rightarrow> (if m=7 then {|None|} else {||})
    | Some q \<Rightarrow> {|if m=0 then map_option digit_allocated_view (digit_allocated_graft q u A B)
      else if m=1 then finite_bounded_graft_reference (digit_allocated_view q) u (finite_enumerated_environment A B)
      else map_option (encoded_bounded_view read_digit_use_path read_digit_address_path)
        (cached_graft_variant m (raw_digit_allocated q) u A B)|})"

theorem cached_graft_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> cached_graft_method m X=cached_graft_reference X"
  by (cases X) (auto simp: cached_graft_method_def cached_graft_reference_def digit_graft_reference_exact split: option.splits)

definition cached_graft_condition where
  "cached_graft_condition f method X=relation_reader_condition (cached_graft_relation X) f (method X)"

definition cached_graft_context where
  "cached_graft_context X=(X,cached_graft_reference X)"

definition cached_graft_assessment where
  "cached_graft_assessment m context=(case context of (X,reference) \<Rightarrow> (cached_graft_method m X,reference))"

definition cached_graft_inspect :: "(cached_graft_value fset\<times>cached_graft_value fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "cached_graft_inspect=finite_reader_inspect"

theorem cached_graft_assessment_exact:
  "cached_graft_inspect (cached_graft_assessment m (cached_graft_context X)) f=cached_graft_condition f (cached_graft_method m) X"
  by (simp only: cached_graft_inspect_def cached_graft_assessment_def cached_graft_context_def case_prod_conv
    cached_graft_condition_def finite_reader_inspect_exact[OF cached_graft_reference_exact])

end
