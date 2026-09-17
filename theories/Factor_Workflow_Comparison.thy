theory Factor_Workflow_Comparison
  imports Factor_Workflow_Cases Finite_Assessment_Reports
begin

definition workflow_condition :: "nat \<Rightarrow>
    (development_workflow_protocol \<times> finite_factor_term \<Rightarrow> native_workflow_execution) \<Rightarrow>
    development_workflow_protocol \<times> finite_factor_term \<Rightarrow> bool" where
  "workflow_condition f method X=(case X of (W,problem) \<Rightarrow>
    let actual=method X; paths=workflow_completed_paths actual;
      reference=workflow_reference_paths (development_workflow_stages W) problem [] in
    if f=0 then set paths\<subseteq>set reference else if f=1 then set reference\<subseteq>set paths
    else if f=2 then paths=reference else if f=3 then
      workflow_trace_valid (development_workflow_stages W) problem [] actual else False)"

definition workflow_assessment where
  "workflow_assessment X actual=(case X of (W,problem) \<Rightarrow>
    (workflow_completed_paths actual,workflow_reference_paths (development_workflow_stages W) problem [],
      workflow_trace_valid (development_workflow_stages W) problem [] actual))"

definition workflow_inspect where
  "workflow_inspect report (f::nat)=(case report of (paths,reference,valid) \<Rightarrow>
    if f=0 then list_all (\<lambda>path. path\<in>set reference) paths
    else if f=1 then list_all (\<lambda>path. path\<in>set paths) reference
    else if f=2 then paths=reference else if f=3 then valid else False)"

theorem workflow_assessment_exact:
  "workflow_inspect (workflow_assessment X (method X)) f=workflow_condition f method X"
  by (cases X) (auto simp: workflow_inspect_def workflow_assessment_def workflow_condition_def
    Let_def list_all_iff)

definition workflow_quality where
  "workflow_quality m w f=workflow_inspect
    (workflow_assessment (workflow_problem_at w) (workflow_method m (workflow_problem_at w))) f"

lemma workflow_quality_exact:
  "workflow_quality m w f=workflow_condition f (workflow_method m) (workflow_problem_at w)"
  by (simp only: workflow_quality_def workflow_assessment_exact)

interpretation native_workflow: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]"
    "[0,1,2,3]" ws workflow_method workflow_condition workflow_problem_at workflow_quality for ws
  by (unfold_locales) (rule workflow_quality_exact)

definition workflow_investigation where
  "workflow_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws workflow_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws workflow_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm workflow_investigation_def},
   equation = @{thm native_workflow.observations_derived},
   formation = @{thm native_workflow.maps_formed},
   observation = @{thm native_workflow.observation_at_subject},
   comparison = @{thm native_workflow.comparison_at_subject}}\<close>

definition workflow_context where
  "workflow_context w=(let X=workflow_problem_at w in (X,workflow_method 0 X))"

definition workflow_prepared where
  "workflow_prepared m X original=(if m=0 then original
    else if m=5 then workflow_without_certificates original
    else if m=6 then workflow_first_branches original
    else if m=7 then workflow_altered_inputs original else workflow_method m X)"

lemma workflow_prepared_exact:
  "workflow_prepared m X (workflow_method 0 X)=workflow_method m X"
  by (cases X) (auto simp: workflow_prepared_def workflow_method_def Let_def split: if_splits)

definition workflow_cell where
  "workflow_cell m C=(case C of (X,original) \<Rightarrow>
    let actual=workflow_prepared m X original in
    (actual,workflow_assessment X actual))"

lemma workflow_cell_at:
  "workflow_cell m (workflow_context w)=
    (workflow_method m (workflow_problem_at w),
      workflow_assessment (workflow_problem_at w) (workflow_method m (workflow_problem_at w)))"
  by (simp only: workflow_cell_def workflow_context_def Let_def case_prod_conv workflow_prepared_exact)

definition workflow_packet where
  "workflow_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws workflow_context workflow_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws table
      (\<lambda>(actual,assessment). workflow_inspect assessment)
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3]
      (fst comparison) (fst (snd comparison))) selections))"

text \<open>
  Every observation is derived from the complete original workflow source and
  actual candidate execution. Ordered complete output comparison remains
  separate from full source, input, evidence and branch admission. Empty
  results cannot hide an omitted required stage or an altered original input.
  The registered equation concerns this whole-constructor question; it does
  not supply the missing full development-stage meaning contracts.
\<close>

end
