theory Factor_Required_Workflow_Cases
  imports Factor_Workflow_Requirements Factor_Workflow_Cases
begin

definition workflow_required_identity :: native_workflow_requirement where
  "workflow_required_identity=\<lparr>requirement_source=finite_guard_source False,
    requirement_source_use=None,requirement_source_root=[0],
    requirement_goals=[Existing_Admission (None,[Suc 0])],requirement_candidates=Workflow_Input\<rparr>"

definition workflow_repeated_requirements :: "native_workflow_requirement \<Rightarrow> required_development_workflow" where
  "workflow_repeated_requirements R=\<lparr>required_problem_formation=R,required_requirement_reasoning=R,
    required_candidate_construction=R,required_evidence_observation=R,required_independent_criticism=R,
    required_comparison_revision=R,required_construction_validation=R,required_reconstruction_retention=R\<rparr>"

definition workflow_require_stage :: "native_workflow_stage \<Rightarrow> native_workflow_requirement" where
  "workflow_require_stage S=\<lparr>requirement_source=workflow_source S,requirement_source_use=workflow_source_use S,
    requirement_source_root=workflow_source_root S,requirement_goals=[Existing_Admission (workflow_entry S)],
    requirement_candidates=workflow_outputs S\<rparr>"

definition workflow_generated_requirements :: "nat \<Rightarrow> required_development_workflow" where
  "workflow_generated_requirements copies=(let R=workflow_repeated_requirements workflow_required_identity in
    case workflow_generating_stage True copies of None \<Rightarrow>
      R\<lparr>required_candidate_construction:=workflow_required_identity\<lparr>requirement_source_root:=[255]\<rparr>\<rparr>
    | Some S \<Rightarrow> R\<lparr>required_candidate_construction:=workflow_require_stage S\<rparr>)"

type_synonym required_workflow_subject = "required_development_workflow\<times>finite_factor_term"

definition required_workflow_case_inputs :: "required_workflow_subject list" where
  "required_workflow_case_inputs=(let R=workflow_repeated_requirements workflow_required_identity;
    refused=workflow_required_identity\<lparr>requirement_candidates:=Workflow_Values [Finite_Payload []]\<rparr>;
    missing=workflow_required_identity\<lparr>requirement_source_root:=[255]\<rparr>;
    repeated=workflow_required_identity\<lparr>requirement_goals:=[Existing_Admission (None,[Suc 0]),
      Existing_Admission (None,[Suc 0])]\<rparr> in
    [(R,Finite_Payload []),(R\<lparr>required_independent_criticism:=refused\<rparr>,Finite_Payload []),
      (R\<lparr>required_independent_criticism:=missing\<rparr>,Finite_Payload []),
      (workflow_generated_requirements 1,Finite_Payload []),(workflow_generated_requirements 2,Finite_Payload []),
      (R\<lparr>required_independent_criticism:=repeated\<rparr>,Finite_Payload [1,2])])"

definition required_workflow_problem_at :: "nat \<Rightarrow> required_workflow_subject" where
  "required_workflow_problem_at w=(if w<length required_workflow_case_inputs then required_workflow_case_inputs!w
    else (workflow_repeated_requirements workflow_required_identity,Finite_Payload []))"

definition required_workflow_method :: "nat \<Rightarrow> required_workflow_subject \<Rightarrow> native_workflow_execution option" where
  "required_workflow_method m X=(case X of (R,problem) \<Rightarrow>
    if m=1 then construct_required_development_workflow (R\<lparr>required_independent_criticism:=
      (required_independent_criticism R)\<lparr>requirement_goals:=[]\<rparr>\<rparr>) problem
    else if m=2 then map_option (\<lambda>W. let stages=development_workflow_stages W in
      execute_workflow (take 4 stages@drop 5 stages) problem []) (compile_development_workflow R)
    else if m=3 then Some (Workflow_Finished [])
    else if m=6 then construct_required_development_workflow R (Finite_Pair problem problem)
    else let original=construct_required_development_workflow R problem in
      if m=4 then map_option workflow_without_certificates original
      else if m=5 then map_option workflow_altered_inputs original else original)"

text \<open>
  These original subjects contain every native source and goal occurrence.
  Cases require complete input transfer, include a refused original native
  requirement, lack a critical source, generate new values, preserve repeated
  rule results and repeat an original requirement occurrence. Alternatives
  weaken the original goal family, skip its position, fabricate completion,
  remove evidence or change the original input. These are compiler and gate
  experiments; they do not identify input transfer with real development roles.
\<close>

end
