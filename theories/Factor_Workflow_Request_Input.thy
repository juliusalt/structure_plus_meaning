theory Factor_Workflow_Request_Input
  imports Factor_Workflow_Requirements
begin

definition workflow_requirement_input :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site admission_goal list \<Rightarrow> workflow_output_scope \<Rightarrow>
    native_workflow_requirement" where
  "workflow_requirement_input E u r gs candidates=\<lparr>requirement_source=E,requirement_source_use=u,
    requirement_source_root=r,requirement_goals=gs,requirement_candidates=candidates\<rparr>"

fun workflow_requirements_input :: "native_workflow_requirement list \<Rightarrow> required_development_workflow option" where
  "workflow_requirements_input [a,b,c,d,e,f,g,h]=Some \<lparr>required_problem_formation=a,
    required_requirement_reasoning=b,required_candidate_construction=c,required_evidence_observation=d,
    required_independent_criticism=e,required_comparison_revision=f,required_construction_validation=g,
    required_reconstruction_retention=h\<rparr>"
| "workflow_requirements_input _=None"

lemma workflow_requirements_input_exact:
  "workflow_requirements_input specs=Some R \<longleftrightarrow> development_workflow_requirements R=specs"
  by (cases specs rule: workflow_requirements_input.cases; cases R)
    (auto simp: development_workflow_requirements_def)

definition execute_workflow_request where
  "execute_workflow_request specs problem=(case workflow_requirements_input specs of None \<Rightarrow> None
    | Some R \<Rightarrow> construct_required_development_workflow R problem)"

definition admit_workflow_request where
  "admit_workflow_request specs problem execution=(case workflow_requirements_input specs of None \<Rightarrow> None
    | Some R \<Rightarrow> admit_required_development_workflow R problem execution)"

theorem admitted_workflow_request_originals:
  assumes admitted: "admit_workflow_request specs problem execution=Some paths"
    and path: "ys\<in>set paths"
  shows "length specs=8"
    "i<8 \<Longrightarrow> workflow_requirement_holds (specs!i)
      (workflow_stage_input problem (take i ys)) (ys!i)"
proof -
  obtain R where parsed: "workflow_requirements_input specs=Some R"
    and checked: "admit_required_development_workflow R problem execution=Some paths"
    using admitted by (auto simp: admit_workflow_request_def split: option.splits)
  have same: "development_workflow_requirements R=specs"
    using parsed by (simp only: workflow_requirements_input_exact)
  show "length specs=8" by (simp only: same[symmetric] development_workflow_requirements_def; simp)
  show "i<8 \<Longrightarrow> workflow_requirement_holds (specs!i)
    (workflow_stage_input problem (take i ys)) (ys!i)"
    using admitted_compiled_workflow_requirements[OF checked path] by (simp only: same)
qed

definition workflow_request_packet where
  "workflow_request_packet specs problem=(let parsed=workflow_requirements_input specs;
    compiled=(case parsed of None \<Rightarrow> None | Some R \<Rightarrow> compile_development_workflow R);
    execution=map_option (\<lambda>W. construct_development_workflow W problem) compiled;
    admitted=(case execution of None \<Rightarrow> None | Some trace \<Rightarrow> admit_workflow_request specs problem trace)
    in (specs,problem,compiled,execution,admitted))"

lemma workflow_request_packet_execution:
  "fst (snd (snd (snd (workflow_request_packet specs problem))))=execute_workflow_request specs problem"
  by (auto simp: workflow_request_packet_def execute_workflow_request_def construct_required_development_workflow_def
    Let_def split: option.splits)

text \<open>
  The request contains complete original requirement values and the actual
  problem. Its native reader requires exactly all eight positions and retains
  every source, goal occurrence and candidate scope. Compilation, execution and
  admission consume those same values. Input encoding supplies no truth table,
  certificate, callback or permission flag.
\<close>

export_code workflow_requirement_input workflow_requirements_input execute_workflow_request
  admit_workflow_request workflow_request_packet checking SML

end
