theory Prepared_Digit_Cause_Assessments
 imports Parallel_Computed_Preparation
   Factor_Constructed_Cause_Cache
   Factor_Shared_Replay_Construction
   Parallel_Assessment_Execution
begin

declare digit_replay_constructed_cause_code[code del]
  digit_replay_cause_report_shared_code[code]

definition cause_report_from_scopes where
  "cause_report_from_scopes scopes X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    (finite_check_generation G E gu gr,generation_payload G=Finite_Whole R,
      fimage (certified_cause_judgment_report X) (scopes (generation_cause G))))"

lemma cause_report_from_scopes_exact:
  "cause_report_from_scopes target_judgment_scopes X=certified_cause_report X"
  by (cases X) (simp add: cause_report_from_scopes_def certified_cause_report_def
      certified_cause_core_scopes_def split: finite_exact_target.splits)

definition digit_cause_report_from_scopes where
  "digit_cause_report_from_scopes scopes X value=map_option (\<lambda>Y.
    let report=cause_report_from_scopes scopes Y in (Y,report,certified_cause_decide 0 report))
      (digit_replay_cause_subject X value)"

lemma digit_cause_report_from_scopes_exact:
  "digit_cause_report_from_scopes target_judgment_scopes X value=digit_replay_cause_report X value"
  by (simp only: digit_cause_report_from_scopes_def cause_report_from_scopes_exact
      digit_replay_cause_report_shared_code)

definition digit_prepared_result where
  "digit_prepared_result P m=(case P of (X,reference,variants) \<Rightarrow> digit_replay_prepared m X variants)"

definition digit_prepare_result_functions where
  "digit_prepare_result_functions ms prepared=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>P. (P,parallel_computed_function (digit_prepared_result P) ms)) input)) prepared"

definition digit_ready_cause_targets where
  "digit_ready_cause_targets ms ready=ffUnion (fimage (\<lambda>(key,input).
    case input of None \<Rightarrow> {||} | Some (P,results) \<Rightarrow>
      ffUnion (fimage (\<lambda>m. ffUnion (fimage (\<lambda>value. case value of None \<Rightarrow> {||}
        | Some (a,u,G,J,C) \<Rightarrow> {|generation_cause G|}) (results m))) (fset_of_list ms))) ready)"

definition digit_assessment_from_results where
  "digit_assessment_from_results scopes m entry=(case entry of ((X,reference,variants),results) \<Rightarrow>
    let result=results m in (result,reference,
      fimage (\<lambda>value. (value,digit_cause_report_from_scopes scopes X value)) result))"

lemma digit_assessment_from_results_exact:
  "digit_assessment_from_results target_judgment_scopes m
      (P,parallel_computed_function (digit_prepared_result P) ms)=digit_replay_assessment m P"
  by (cases P) (simp add: digit_assessment_from_results_def digit_prepared_result_def
      parallel_computed_function_exact digit_replay_assessment_def digit_cause_report_from_scopes_exact)

definition digit_prepare_cause_assessments where
  "digit_prepare_cause_assessments ms context=(case context of (subjects,covered,prepared,reference) \<Rightarrow>
    let ready=digit_prepare_result_functions ms prepared;
        scopes=finite_computed_function target_judgment_scopes (digit_ready_cause_targets ms ready)
    in (\<lambda>m. let causes=fimage (\<lambda>(key,input).
          (key,map_option (digit_assessment_from_results scopes m) input)) ready
       in (digit_replay_family_change m (digit_replay_assessed_results causes),reference,covered,causes)))"

theorem digit_prepare_cause_assessments_exact:
  "digit_prepare_cause_assessments ms context m=digit_replay_family_assessment m context"
  by (cases "context") (simp add: digit_prepare_cause_assessments_def digit_prepare_result_functions_def
      finite_computed_function_exact digit_assessment_from_results_exact
      digit_replay_family_assessment_shared_code fimage_fimage option.map_comp comp_def case_prod_unfold Let_def)

text \<open>
  Each actual prepared subject carries its own result function; no equality
  operation is required on the opaque digit store or on function values.
  All requested methods first produce their actual complete results. Cause keys
  are then read from those actual generations. Every distinct target receives
  the original complete scope computation, independently of the other targets;
  no guessed source quotation or supplied scope flag is used. Every generation,
  payload, original cause subject, policy reading and verdict is still assessed.
  The exact equation holds for arbitrary contexts and unprepared method indices,
  so changed or unavailable inputs retain the original operation and refusal.
\<close>
end
