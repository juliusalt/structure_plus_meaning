theory Factor_Shared_Replay_Construction
  imports Factor_Nested_Replay_Identity
begin

declare digit_replay_reference_def[code del]

lemma digit_replay_reference_typed_code [code]:
  "digit_replay_reference X=digit_replay_typed X"
  by (rule digit_replay_typed_exact[symmetric])

declare digit_replay_context_def[code del]

lemma digit_replay_context_shared_code [code]:
  "digit_replay_context X=(let result=digit_replay_typed X in
    (X,result,(0,result)#(1,result)#map (\<lambda>k. (k,digit_replay_variant k X)) [2,3,4,5,6]))"
  by (simp add: digit_replay_context_def digit_replay_variant_def Let_def digit_replay_typed_exact)

definition digit_replay_prepared_reference where
  "digit_replay_prepared_reference prepared=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>(X,reference,variants). reference) input)) prepared"

lemma digit_replay_prepared_reference_exact:
  "digit_replay_prepared_reference (digit_replay_family_prepare subjects)=
    digit_replay_family_reference subjects"
  by (simp add: digit_replay_prepared_reference_def digit_replay_family_prepare_def
      digit_replay_family_reference_def digit_replay_context_def fimage_fimage
      option.map_comp comp_def case_prod_unfold)

declare digit_replay_family_context_def[code del]

lemma digit_replay_family_context_shared_code [code]:
  "digit_replay_family_context subjects=(let prepared=digit_replay_family_prepare subjects in
    (subjects,literal_replay_covered literal_replay_seed,prepared,digit_replay_prepared_reference prepared))"
  by (simp only: digit_replay_family_context_def Let_def digit_replay_prepared_reference_exact)

definition digit_replay_assessed_results where
  "digit_replay_assessed_results causes=fimage (\<lambda>(key,input). (key,map_option fst input)) causes"

lemma digit_replay_assessed_results_exact:
  "digit_replay_family_change m (digit_replay_assessed_results
      (fimage (\<lambda>(key,input). (key,map_option (digit_replay_assessment m) input)) prepared))=
    digit_replay_family_prepared m prepared"
  by (simp add: digit_replay_assessed_results_def digit_replay_family_prepared_def
      digit_replay_assessment_def fimage_fimage option.map_comp comp_def case_prod_unfold Let_def)

declare digit_replay_family_assessment_def[code del]

lemma digit_replay_family_assessment_shared_code [code]:
  "digit_replay_family_assessment m context=(case context of (subjects,covered,prepared,reference) \<Rightarrow>
    let causes=fimage (\<lambda>(key,input). (key,map_option (digit_replay_assessment m) input)) prepared
    in (digit_replay_family_change m (digit_replay_assessed_results causes),reference,covered,causes))"
  by (cases "context")
    (simp add: digit_replay_family_assessment_def Let_def digit_replay_assessed_results_exact
      split: prod.splits)

text \<open>The established complete projection equation supplies the bounded
  reference from the actual digit operation. One result accompanies both
  original methods, and complete prepared contexts and assessment reports
  supply their own reference and result projections. Every original variant,
  changed value, cause report and whole-family change remains present.\<close>

end
