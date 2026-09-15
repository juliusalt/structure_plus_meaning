theory RRA_Digit_Generation_Methods
  imports RRA_Digit_Generation_References
begin

definition digit_generation_unguarded where
  "digit_generation_unguarded q l p c rows=Option.bind
    (keyed_option_map (digit_generation_anchor q) (map fst rows)) (\<lambda>anchors.
      map_option (\<lambda>following. (following,digit_allocated_next_use q,finite_generation_record_core l p c rows))
        (digit_generation_installation q l p c anchors))"

definition digit_generation_variant_key :: "nat\<Rightarrow>nat" where
  "digit_generation_variant_key m=(if m\<in>{1,2,13} then m else 0)"

definition digit_generation_variant where
  "digit_generation_variant (m::nat) X=(if m=1 then digit_generation_reference X
    else if m=0 then digit_generation_typed X else
    case X of (input,l,p,c,rows) \<Rightarrow> finite_prepared_results (\<lambda>q.
      if m=2 then map_option (\<lambda>(F,u,G). ((Suc (Suc (fst (digit_allocated_view q))),F),u,G))
        (finite_construct_generation_record (snd (digit_allocated_view q)) l p c rows)
      else map_option digit_generation_result_view (digit_generation_unguarded q l p c rows)) input)"

definition digit_generation_changed_result :: "nat\<Rightarrow>digit_generation_subject\<Rightarrow>
    bounded_generation_result\<Rightarrow>bounded_generation_result" where
  "digit_generation_changed_result m X result=(case X of (input,l,p,c,rows) \<Rightarrow>
    case input of None \<Rightarrow> result | Some q \<Rightarrow>
    let n=fst (digit_allocated_view q);E=snd (digit_allocated_view q) in
    case result of ((next_head,F),u,G) \<Rightarrow>
      ((if m=9 then n else if m=10 then Suc n else if m=15 then n else next_head,
        if m=3 then F\<lparr>finite_environment_bindings:={||}\<rparr>
        else if m=4 then F\<lparr>finite_environment_bindings:=
          ffilter (\<lambda>((v,k),w). v\<noteq>u \<or>
            k\<notin>generation_predecessor_slot ` {..<length rows}) (finite_environment_bindings F)\<rparr>
        else if m=5 then F\<lparr>finite_environment_artifacts:=
          ffilter (\<lambda>(v,R). v\<noteq>None) (finite_environment_artifacts F),
          finite_environment_bindings:=ffilter (\<lambda>((v,k),w). v\<noteq>None \<and> w\<noteq>None)
            (finite_environment_bindings F)\<rparr>
        else if m=6 then F\<lparr>finite_environment_artifacts:=
          ffilter (\<lambda>(v,R). n\<le>use_word_head v) (finite_environment_artifacts F),
          finite_environment_bindings:=ffilter (\<lambda>((v,k),w). n\<le>use_word_head v)
            (finite_environment_bindings F)\<rparr>
        else if m=15 then E else F),
       if m=8 then None else u,
       if m=7 then Generation l {||} p c
       else if m=16 then Generation l (generation_predecessors G) (Finite_Whole (finite_payload_syntax [77])) c else G))"

definition digit_generation_mutation :: "nat\<Rightarrow>digit_generation_subject\<Rightarrow>
    bounded_generation_value fset\<Rightarrow>bounded_generation_value fset" where
  "digit_generation_mutation m X results=(if m=12 then {||}
    else if m=14 \<and> fst X=None then {|None|}
    else if m=11 then fimage (\<lambda>result. None) results
    else if m\<in>{3,4,5,6,7,8,9,10,15,16} then
      fimage (map_option (digit_generation_changed_result m X)) results else results)"

definition digit_generation_method where
  "digit_generation_method m X=digit_generation_mutation m X
    (digit_generation_variant (digit_generation_variant_key m) X)"

theorem digit_generation_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> digit_generation_method m X=digit_generation_reference X"
  by (auto simp: digit_generation_method_def digit_generation_mutation_def digit_generation_variant_key_def
    digit_generation_variant_def digit_generation_typed_exact)

definition digit_generation_context where
  "digit_generation_context X=(X,digit_generation_reference X,
    map (\<lambda>k. (k,digit_generation_variant k X)) [0,1,2,13])"

definition digit_generation_prepared where
  "digit_generation_prepared m X variants=digit_generation_mutation m X
    (case map_of variants (digit_generation_variant_key m) of None \<Rightarrow> {||} | Some result \<Rightarrow> result)"

lemma digit_generation_prepared_exact:
  "digit_generation_prepared m X (map (\<lambda>k. (k,digit_generation_variant k X)) [0,1,2,13])=
    digit_generation_method m X"
proof -
  have key: "digit_generation_variant_key m\<in>set [0,1,2,13]"
    by (auto simp: digit_generation_variant_key_def)
  show ?thesis by (simp only: digit_generation_prepared_def mapped_function_lookup key
    if_True option.case digit_generation_method_def)
qed

definition digit_generation_assessment where
  "digit_generation_assessment m context=(case context of (X,reference,variants) \<Rightarrow>
    let result=digit_generation_prepared m X variants in
    (result,reference,fimage (\<lambda>value. (value,digit_generation_original_assessment X value)) result))"

definition digit_generation_inspect ::
  "(bounded_generation_value fset\<times>bounded_generation_value fset\<times>'a)\<Rightarrow>nat\<Rightarrow>bool" where
  "digit_generation_inspect assessment f=(case assessment of (result,reference,original) \<Rightarrow>
    finite_reader_inspect (result,reference) f)"

definition digit_generation_condition where
  "digit_generation_condition f method X=relation_reader_condition (digit_generation_relation X) f (method X)"

theorem digit_generation_assessment_exact:
  "digit_generation_inspect (digit_generation_assessment m (digit_generation_context X)) f=
    digit_generation_condition f (digit_generation_method m) X"
  by (simp only: digit_generation_inspect_def digit_generation_assessment_def digit_generation_context_def
    Let_def case_prod_conv digit_generation_prepared_exact digit_generation_condition_def
    finite_reader_inspect_exact[OF digit_generation_reference_exact])

text \<open>
  Whole results expose changed material, bindings, generation values, result
  uses and reservation heads. An actual readiness-bypassing implementation is
  distinct from forced reported truth values. Original generation assessments
  accompany every result, keeping complete operation equality separate from
  broader generation validity and alternative fresh embeddings.
\<close>

end
