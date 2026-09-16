theory Factor_Workflow_Cases
  imports Factor_Workflow_Admission Factor_Requirement_Source_Examples Factor_Finite_Source_Entry_Installation
    Factor_Finite_View_Installation
begin

definition workflow_guard_stage where
  "workflow_guard_stage b scope=\<lparr>workflow_source=finite_guard_source b,
    workflow_source_use=None,workflow_source_root=[0],workflow_entry=(None,[Suc 0]),workflow_outputs=scope\<rparr>"

definition workflow_repeated_protocol where
  "workflow_repeated_protocol S=\<lparr>problem_formation_stage=S,requirement_reasoning_stage=S,
    candidate_construction_stage=S,evidence_observation_stage=S,independent_criticism_stage=S,
    comparison_revision_stage=S,construction_validation_stage=S,reconstruction_retention_stage=S\<rparr>"

definition workflow_original_protocol where
  "workflow_original_protocol=workflow_repeated_protocol (workflow_guard_stage False Workflow_Input)"

definition workflow_generation_rule ::
  "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "workflow_generation_rule=\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable [0])
      (Finite_Pattern_Pair (Finite_Variable [0]) (Finite_Variable [0])),
    finite_schema_premises={|([0],(None,[Suc 0]),Finite_Variable [0])|},finite_schema_materials={||}\<rparr>"

definition workflow_generating_stage :: "bool \<Rightarrow> nat \<Rightarrow> native_workflow_stage option" where
  "workflow_generating_stage b copies=(let E=finite_guard_source b; P=finite_guard_source_program b;
      e=(Some [],[]); Q=finite_add_view_definition P e (Finite_Variable [])
        (fset_of_list (map (\<lambda>n. ([n],workflow_generation_rule)) [0..<copies])) in
    map_option (\<lambda>(d,F,u). \<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],
      workflow_entry=d,workflow_outputs=Workflow_Generated d\<rparr>)
      (finite_install_source_entry E None [0] Q e))"

definition workflow_generation_case where
  "workflow_generation_case b copies=(case workflow_generating_stage b copies of None \<Rightarrow>
      (workflow_original_protocol\<lparr>candidate_construction_stage:=
        (workflow_guard_stage False Workflow_Input)\<lparr>workflow_entry:=(None,[255])\<rparr>\<rparr>,Finite_Payload [])
    | Some S \<Rightarrow> (workflow_original_protocol\<lparr>candidate_construction_stage:=S\<rparr>,Finite_Payload []))"

definition workflow_case_inputs where
  "workflow_case_inputs=(let W=workflow_original_protocol;
    missing=(workflow_guard_stage False Workflow_Input)\<lparr>workflow_entry:=(None,[255])\<rparr>;
    refused=workflow_guard_stage False (Workflow_Values [Finite_Payload []]);
    choices=workflow_guard_stage True (Workflow_Values [Finite_Payload [],Finite_Payload [1],Finite_Payload []]);
    empty=workflow_guard_stage False (Workflow_Values []) in
    [(W,Finite_Payload []),(W,Finite_Payload [256]),
      (W\<lparr>independent_criticism_stage:=missing\<rparr>,Finite_Payload []),
      (W\<lparr>independent_criticism_stage:=refused\<rparr>,Finite_Payload []),
      (W\<lparr>candidate_construction_stage:=choices\<rparr>,Finite_Payload []),
      (W\<lparr>problem_formation_stage:=empty\<rparr>,Finite_Payload []),
      (W,Finite_Payload [3,4]),workflow_generation_case True 1,
      workflow_generation_case False 1,workflow_generation_case True 2])"

definition workflow_problem_at where
  "workflow_problem_at w=(if w<length workflow_case_inputs then workflow_case_inputs!w
    else (workflow_original_protocol,Finite_Payload []))"

fun workflow_without_certificates where
  "workflow_without_certificates (Workflow_Finished ys)=Workflow_Finished ys"
| "workflow_without_certificates (Workflow_Unavailable S input)=Workflow_Unavailable S input"
| "workflow_without_certificates (Workflow_Executed S input (P,D,A,T,ys) children)=
    Workflow_Executed S input (P,D,A,{||},ys)
      (map (\<lambda>(y,child). (y,workflow_without_certificates child)) children)"

fun workflow_first_branches where
  "workflow_first_branches (Workflow_Finished ys)=Workflow_Finished ys"
| "workflow_first_branches (Workflow_Unavailable S input)=Workflow_Unavailable S input"
| "workflow_first_branches (Workflow_Executed S input result children)=
    Workflow_Executed S input result
      (take 1 (map (\<lambda>(y,child). (y,workflow_first_branches child)) children))"

fun workflow_altered_inputs where
  "workflow_altered_inputs (Workflow_Finished ys)=Workflow_Finished ys"
| "workflow_altered_inputs (Workflow_Unavailable S input)=Workflow_Unavailable S (Finite_Payload [])"
| "workflow_altered_inputs (Workflow_Executed S input result children)=
    Workflow_Executed S (Finite_Payload []) result
      (map (\<lambda>(y,child). (y,workflow_altered_inputs child)) children)"

definition workflow_method :: "nat \<Rightarrow> development_workflow_protocol \<times> finite_factor_term \<Rightarrow>
    native_workflow_execution" where
  "workflow_method m X=(case X of (W,problem) \<Rightarrow>
    let stages=development_workflow_stages W in
    if m=1 then execute_workflow (take 4 stages@drop 5 stages) problem []
    else if m=2 then execute_workflow (take 7 stages) problem []
    else if m=3 then Workflow_Finished []
    else if m=4 then construct_development_workflow W (Finite_Pair problem problem)
    else if m=8 then construct_development_workflow
      (W\<lparr>candidate_construction_stage:=(candidate_construction_stage W)
        \<lparr>workflow_outputs:=Workflow_Input\<rparr>\<rparr>) problem
    else if m=9 then construct_development_workflow
      (W\<lparr>candidate_construction_stage:=(candidate_construction_stage W)
        \<lparr>workflow_outputs:=Workflow_Values [Finite_Payload []]\<rparr>\<rparr>) problem
    else let result=construct_development_workflow W problem in
      if m=5 then workflow_without_certificates result
      else if m=6 then workflow_first_branches result
      else if m=7 then workflow_altered_inputs result else result)"

lemma workflow_original_method:
  "workflow_method 0 (W,problem)=construct_development_workflow W problem"
  by (simp add: workflow_method_def Let_def)

text \<open>
  These are complete native-source experiments for the whole workflow
  constructor and admission mechanism. The unchanged source artifacts have
  independently proved equality or formed-term meanings. A missing actual
  entry, an unsatisfied actual call, an empty scope, invalid literal input,
  multiple output branches and repeated outputs remain separate cases.

  Controls omit required positions, substitute the original problem, remove
  actual certificates, lose branches or alter the actual recorded inputs.
  None supplies a satisfaction table. These source experiments do not claim
  that identity transfer implements problem selection or independent criticism
  for the repository's complete development requirements.

  Three further complete source constructions generate a newly paired output
  from actual accepted premises, refuse that premise under a different source,
  and retain two distinct rule applications with the same output. The controls
  also replace this generated scope with input copying or a fixed value. Every
  constructed source and placed entry remain in the actual workflow subject.
\<close>

end
