theory Factor_Workflow_Expanded_Comparison
  imports Factor_Workflow_Input_Scope
begin

definition required_workflow_scope_problem :: "required_workflow_subject list \<Rightarrow> nat \<Rightarrow>
    required_workflow_subject" where
  "required_workflow_scope_problem X w=(if w<length X then X!w else required_workflow_problem_at w)"

definition required_workflow_scope_quality where
  "required_workflow_scope_quality X m w f=workflow_inspect (required_workflow_assessment
    (required_workflow_scope_problem X w) (required_workflow_method m (required_workflow_scope_problem X w))) f"

interpretation required_workflow_scope: finite_subject_investigation "[0,1,2,3,4,5,6]" "[0,1,2,3]" ws
    required_workflow_method required_workflow_condition "required_workflow_scope_problem X"
    "required_workflow_scope_quality X" for ws X
  by (unfold_locales) (simp only: required_workflow_scope_quality_def required_workflow_assessment_exact)

definition required_workflow_scope_investigation where
  "required_workflow_scope_investigation X ws selected=investigation_basis [0,1,2,3,4,5,6] [0,1,2,3] selected
    (subject_investigation_observations [0,1,2,3,4,5,6] [0,1,2,3] ws (required_workflow_scope_quality X))
    (subject_investigation_relation [0,1,2,3,4,5,6] [0,1,2,3] ws (required_workflow_scope_quality X))"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm required_workflow_scope_investigation_def},
   equation = @{thm required_workflow_scope.observations_derived},
   formation = @{thm required_workflow_scope.maps_formed},
   observation = @{thm required_workflow_scope.observation_at_subject},
   comparison = @{thm required_workflow_scope.comparison_at_subject}}\<close>

definition required_workflow_scope_packet where
  "required_workflow_scope_packet X ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6] ws
      (\<lambda>w. let subject=required_workflow_scope_problem X w in (subject,required_workflow_method 0 subject))
      required_workflow_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6] [0,1,2,3] ws table
      (\<lambda>(actual,assessment). workflow_inspect assessment)
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1,2,3]
      (fst comparison) (fst (snd comparison))) selections))"

definition expanded_workflow_indices where
  "expanded_workflow_indices=map_option (\<lambda>X. [0..<length X]) selected_workflow_input_scope"

definition expanded_workflow_packet where
  "expanded_workflow_packet ws selections=map_option (\<lambda>X. required_workflow_scope_packet X ws selections)
    selected_workflow_input_scope"

text \<open>
  The scope is the unique result of the native coverage comparison. Missing or
  ambiguous adequacy prevents this complete comparison from being constructed.
  Every source, original goal, execution and certificate uses that actual scope.
\<close>

end
