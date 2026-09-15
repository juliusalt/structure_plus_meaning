theory RRA_Digit_Generation_References
  imports RRA_Digit_Generation_Construction RRA_Generation_Record_Assessment Finite_Prepared_Results
    Finite_Relation_Reader_Assessments
begin

type_synonym digit_generation_subject =
  "digit_allocated_environment option\<times>finite_exact_target\<times>finite_exact_target\<times>finite_exact_target\<times>
    (local_address option definition_site\<times>finite_generation) list"
type_synonym bounded_generation_result =
  "(nat\<times>local_address option finite_artifact_environment)\<times>local_address option\<times>finite_generation"
type_synonym bounded_generation_value = "bounded_generation_result option"

definition digit_generation_result_view where
  "digit_generation_result_view result=(case result of (following,u,G) \<Rightarrow> (digit_allocated_view following,u,G))"

definition digit_generation_original_subject :: "digit_generation_subject\<Rightarrow>generation_record_problem option" where
  "digit_generation_original_subject X=(case X of (input,l,p,c,rows) \<Rightarrow>
    map_option (\<lambda>q. (snd (digit_allocated_view q),l,p,c,rows)) input)"

definition bounded_generation_record_result :: "bounded_generation_value\<Rightarrow>generation_record_result option" where
  "bounded_generation_record_result result=map_option (\<lambda>((n,F),u,G). (F,u,G)) result"

definition digit_generation_relation :: "digit_generation_subject\<Rightarrow>bounded_generation_value\<Rightarrow>bool" where
  "digit_generation_relation X result=(case X of (input,l,p,c,rows) \<Rightarrow>
    \<exists>q. input=Some q \<and> result=finite_construct_bounded_generation (digit_allocated_view q) l p c rows)"

definition digit_generation_reference where
  "digit_generation_reference X=(case X of (input,l,p,c,rows) \<Rightarrow>
    finite_prepared_results (\<lambda>q. finite_construct_bounded_generation (digit_allocated_view q) l p c rows) input)"

theorem digit_generation_reference_exact:
  "result |\<in>| digit_generation_reference X \<longleftrightarrow> digit_generation_relation X result"
  by (simp only: digit_generation_reference_def digit_generation_relation_def
    case_prod_unfold finite_prepared_results_exact)

definition digit_generation_typed where
  "digit_generation_typed X=(case X of (input,l,p,c,rows) \<Rightarrow>
    finite_prepared_results (\<lambda>q. map_option digit_generation_result_view
      (digit_construct_generation q l p c rows)) input)"

lemma digit_generation_typed_exact:
  "digit_generation_typed X=digit_generation_reference X"
proof -
  have each: "map_option digit_generation_result_view (digit_construct_generation q l p c rows)=
    finite_construct_bounded_generation (digit_allocated_view q) l p c rows" for q l p c rows
    using digit_construct_generation_projection[of q l p c rows]
    by (simp only: digit_generation_result_view_def[abs_def])
  show ?thesis by (simp only: digit_generation_typed_def digit_generation_reference_def case_prod_unfold each)
qed

definition digit_generation_original_assessment where
  "digit_generation_original_assessment X result=map_option (\<lambda>original.
    generation_record_assessment original (bounded_generation_record_result result)) (digit_generation_original_subject X)"

definition digit_generation_original_condition where
  "digit_generation_original_condition X result f=(case digit_generation_original_subject X of
    None \<Rightarrow> False | Some original \<Rightarrow>
      generation_record_condition f (\<lambda>input. bounded_generation_record_result result) original)"

definition digit_generation_original_inspect where
  "digit_generation_original_inspect assessment f=(case assessment of None \<Rightarrow> False
    | Some A \<Rightarrow> generation_record_inspect A f)"

theorem digit_generation_original_assessment_exact:
  "digit_generation_original_inspect (digit_generation_original_assessment X result) f=
    digit_generation_original_condition X result f"
proof -
  have each: "generation_record_inspect
      (generation_record_assessment original (bounded_generation_record_result result)) f=
    generation_record_condition f (\<lambda>input. bounded_generation_record_result result) original" for original
    by (rule generation_record_assessment_exact[where method="\<lambda>input. bounded_generation_record_result result"])
  show ?thesis by (cases "digit_generation_original_subject X")
    (simp_all add: digit_generation_original_inspect_def digit_generation_original_assessment_def
      digit_generation_original_condition_def each)
qed

definition generation_record_condition_scope :: "nat list" where
  "generation_record_condition_scope=[0..<9]"

lemma generation_record_condition_outside_scope:
  "f\<notin>set generation_record_condition_scope \<Longrightarrow> \<not>generation_record_condition f method X"
  by (auto simp: generation_record_condition_scope_def generation_record_condition_def)

text \<open>
  The independently established bounded constructor determines the complete
  operation result, including its explicit reservation policy. The separate
  original generation assessment retains fields, recursive validity, old
  material and exact predecessor references. An alternative fresh allocation
  can preserve generation meaning while differing from this complete operation.
\<close>

end
