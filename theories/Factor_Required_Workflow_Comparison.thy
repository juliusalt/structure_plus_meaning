theory Factor_Required_Workflow_Comparison
  imports Factor_Required_Workflow_Cases Factor_Workflow_Comparison
begin

definition required_workflow_reference where
  "required_workflow_reference X=(case X of (R,problem) \<Rightarrow>
    map_option (\<lambda>W. workflow_reference_paths (development_workflow_stages W) problem [])
      (compile_development_workflow R))"

definition required_workflow_paths where
  "required_workflow_paths result=(case result of None \<Rightarrow> [] | Some execution \<Rightarrow> workflow_completed_paths execution)"

definition required_workflow_trace_valid where
  "required_workflow_trace_valid X actual=(case X of (R,problem) \<Rightarrow>
    (case actual of None \<Rightarrow> compile_development_workflow R=None
      | Some execution \<Rightarrow> admit_required_development_workflow R problem execution\<noteq>None))"

definition required_workflow_assessment where
  "required_workflow_assessment X actual=(required_workflow_paths actual,
    case_option [] id (required_workflow_reference X),required_workflow_trace_valid X actual)"

definition required_workflow_condition :: "nat \<Rightarrow>
    (required_workflow_subject \<Rightarrow> native_workflow_execution option) \<Rightarrow> required_workflow_subject \<Rightarrow> bool" where
  "required_workflow_condition f method X=(let paths=required_workflow_paths (method X);
    reference=case_option [] id (required_workflow_reference X) in
    if f=0 then set paths\<subseteq>set reference else if f=1 then set reference\<subseteq>set paths
    else if f=2 then paths=reference else if f=3 then required_workflow_trace_valid X (method X) else False)"

lemma required_workflow_assessment_exact:
  "workflow_inspect (required_workflow_assessment X (method X)) f=required_workflow_condition f method X"
  by (auto simp: workflow_inspect_def required_workflow_assessment_def required_workflow_condition_def Let_def list_all_iff)

definition required_workflow_quality where
  "required_workflow_quality m w f=workflow_inspect (required_workflow_assessment (required_workflow_problem_at w)
    (required_workflow_method m (required_workflow_problem_at w))) f"

lemma required_workflow_quality_exact:
  "required_workflow_quality m w f=required_workflow_condition f (required_workflow_method m) (required_workflow_problem_at w)"
  by (simp only: required_workflow_quality_def required_workflow_assessment_exact)

interpretation required_workflow: finite_subject_investigation "[0,1,2,3,4,5,6]" "[0,1,2,3]" ws
    required_workflow_method required_workflow_condition required_workflow_problem_at required_workflow_quality for ws
  by (unfold_locales) (rule required_workflow_quality_exact)

definition required_workflow_investigation where
  "required_workflow_investigation ws selected=investigation_basis [0,1,2,3,4,5,6] [0,1,2,3] selected
    (subject_investigation_observations [0,1,2,3,4,5,6] [0,1,2,3] ws required_workflow_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6] [0,1,2,3] ws required_workflow_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm required_workflow_investigation_def},
   equation = @{thm required_workflow.observations_derived},
   formation = @{thm required_workflow.maps_formed},
   observation = @{thm required_workflow.observation_at_subject},
   comparison = @{thm required_workflow.comparison_at_subject}}\<close>

definition required_workflow_context where
  "required_workflow_context w=(let X=required_workflow_problem_at w in (X,required_workflow_method 0 X))"

definition required_workflow_prepared where
  "required_workflow_prepared m X original=(if m=0 then original
    else if m=4 then map_option workflow_without_certificates original
    else if m=5 then map_option workflow_altered_inputs original else required_workflow_method m X)"

lemma required_workflow_prepared_exact:
  "required_workflow_prepared m X (required_workflow_method 0 X)=required_workflow_method m X"
  by (cases X) (auto simp: required_workflow_prepared_def required_workflow_method_def Let_def split: if_splits)

definition required_workflow_cell where
  "required_workflow_cell m C=(case C of (X,original) \<Rightarrow>
    let actual=required_workflow_prepared m X original in (actual,required_workflow_assessment X actual))"

lemma required_workflow_cell_at:
  "required_workflow_cell m (required_workflow_context w)=
    (required_workflow_method m (required_workflow_problem_at w),
      required_workflow_assessment (required_workflow_problem_at w) (required_workflow_method m (required_workflow_problem_at w)))"
  by (simp only: required_workflow_cell_def required_workflow_context_def Let_def case_prod_conv required_workflow_prepared_exact)

definition required_workflow_packet where
  "required_workflow_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6] ws required_workflow_context required_workflow_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6] [0,1,2,3] ws table
      (\<lambda>(actual,assessment). workflow_inspect assessment)
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1,2,3]
      (fst comparison) (fst (snd comparison))) selections))"

export_code required_workflow_packet checking SML

end
