theory Factor_Digit_Replay_Methods
  imports Factor_Digit_Replay_Variants Finite_Relation_Reader_Assessments
begin

definition digit_replay_context where
  "digit_replay_context X=(X,digit_replay_reference X,
    map (\<lambda>k. (k,digit_replay_variant k X)) [0,1,2,3,4,5,6])"

definition digit_replay_prepared where
  "digit_replay_prepared m X variants=digit_replay_mutation m X
    (case map_of variants (digit_replay_variant_key m) of None \<Rightarrow> {||} | Some result \<Rightarrow> result)"

lemma digit_replay_prepared_exact:
  "digit_replay_prepared m X (map (\<lambda>k. (k,digit_replay_variant k X)) [0,1,2,3,4,5,6])=
    digit_replay_method m X"
proof -
  have key: "digit_replay_variant_key m\<in>set [0,1,2,3,4,5,6]"
    by (auto simp: digit_replay_variant_key_def)
  show ?thesis by (simp only: digit_replay_prepared_def mapped_function_lookup key
    if_True option.case digit_replay_method_def)
qed

definition digit_replay_assessment where
  "digit_replay_assessment m context=(case context of (X,reference,variants) \<Rightarrow>
    let result=digit_replay_prepared m X variants in
    (result,reference,fimage (\<lambda>value. (value,digit_replay_cause_report X value)) result))"

definition digit_replay_inspect ::
  "(bounded_replay_value fset\<times>bounded_replay_value fset\<times>'a)\<Rightarrow>nat\<Rightarrow>bool" where
  "digit_replay_inspect assessment f=(case assessment of (result,reference,causes) \<Rightarrow>
    finite_reader_inspect (result,reference) f)"

definition digit_replay_condition where
  "digit_replay_condition f method X=relation_reader_condition (digit_replay_relation X) f (method X)"

theorem digit_replay_assessment_exact:
  "digit_replay_inspect (digit_replay_assessment m (digit_replay_context X)) f=
    digit_replay_condition f (digit_replay_method m) X"
  by (simp only: digit_replay_inspect_def digit_replay_assessment_def digit_replay_context_def
    Let_def case_prod_conv digit_replay_prepared_exact digit_replay_condition_def
    finite_reader_inspect_exact[OF digit_replay_reference_exact])

end
