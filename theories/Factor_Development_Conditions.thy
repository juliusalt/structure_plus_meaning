theory Factor_Development_Conditions
  imports Factor_Workflow_Requirements Factor_Executable_Environment_Values_Base
begin

record native_development_condition =
  condition_source :: "local_address option finite_artifact_environment"
  condition_source_use :: "local_address option"
  condition_source_root :: local_address
  condition_goals :: "local_address option definition_site admission_goal list"

definition development_condition_requirement ::
    "native_development_condition \<Rightarrow> finite_factor_term list \<Rightarrow> native_workflow_requirement" where
  "development_condition_requirement C ys=\<lparr>requirement_source=condition_source C,
    requirement_source_use=condition_source_use C,requirement_source_root=condition_source_root C,
    requirement_goals=condition_goals C,requirement_candidates=Workflow_Values ys\<rparr>"

definition development_condition_holds ::
    "native_development_condition \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "development_condition_holds C x y=workflow_requirement_holds (development_condition_requirement C []) x y"

type_synonym native_condition_execution = "native_workflow_stage\<times>native_workflow_stage_result"

definition execute_development_condition ::
    "native_development_condition \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow> native_condition_execution option" where
  "execute_development_condition C x ys=(case compile_workflow_requirement (development_condition_requirement C ys) of
    None \<Rightarrow> None | Some S \<Rightarrow> map_option (Pair S) (evaluate_workflow_stage S x))"

definition development_condition_evidence ::
    "native_development_condition \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow> native_condition_execution \<Rightarrow> bool" where
  "development_condition_evidence C x ys execution=(case execution of (S,result) \<Rightarrow>
    compile_workflow_requirement (development_condition_requirement C ys)=Some S \<and>
    workflow_stage_evidence S x result)"

definition development_condition_outputs :: "native_condition_execution \<Rightarrow> finite_factor_term list" where
  "development_condition_outputs execution=(case execution of (S,P,D,A,T,ys) \<Rightarrow> ys)"

lemma compiled_requirement_candidate_scope:
  "compile_workflow_requirement R=Some S \<Longrightarrow> workflow_outputs S=requirement_candidates R"
  by (auto simp: compile_workflow_requirement_def split: option.splits prod.splits)

lemma execute_development_condition_evidence:
  "execute_development_condition C x ys=Some execution \<Longrightarrow>
    development_condition_evidence C x ys execution"
  using evaluate_workflow_stage_evidence
  by (auto simp: execute_development_condition_def development_condition_evidence_def
    split: option.splits)

theorem development_condition_evidence_exact:
  assumes valid: "development_condition_evidence C x ys execution"
  shows "y\<in>set (development_condition_outputs execution) \<longleftrightarrow>
    y\<in>set ys \<and> development_condition_holds C x y"
proof -
  obtain S P D A T zs where shape: "execution=(S,P,D,A,T,zs)" by (cases execution) auto
  have compiled: "compile_workflow_requirement (development_condition_requirement C ys)=Some S"
    and evidence: "workflow_stage_evidence S x (P,D,A,T,zs)"
    using valid by (simp_all add: development_condition_evidence_def shape)
  have reference: "workflow_stage_reference S x=Some zs"
    by (rule workflow_stage_evidence_reference[OF evidence])
  have exact: "set zs={y. workflow_stage_relation S x y}"
    by (rule workflow_stage_reference_exact[OF reference])
  have scope: "workflow_outputs S=Workflow_Values ys"
    using compiled_requirement_candidate_scope[OF compiled]
    by (simp only: development_condition_requirement_def native_workflow_requirement.select_convs)
  show ?thesis
    by (simp add: development_condition_outputs_def shape exact compiled_workflow_requirement_exact[OF compiled]
      workflow_scope_values_def workflow_scope_result_def scope development_condition_holds_def
      workflow_requirement_holds_def development_condition_requirement_def)
qed

definition development_site_value where
  "development_site_value d=the (finite_self_contained_term (site_data_term (fst d) (snd d)))"

lemma development_site_value_decode [simp]:
  "decode_finite_term (development_site_value d)=site_data_term (fst d) (snd d)"
  by (simp only: development_site_value_def; rule decode_finite_self_contained_term) simp

fun development_goal_value where
  "development_goal_value (Existing_Admission d)=Finite_Pair (Finite_Payload [0]) (development_site_value d)"
| "development_goal_value (Paired_Admission p q)=Finite_Pair (Finite_Payload [1])
    (Finite_Pair (development_goal_value p) (development_goal_value q))"
| "development_goal_value (Collected_Admission p)=Finite_Pair (Finite_Payload [2]) (development_goal_value p)"

lemma development_goal_value_decode:
  "decode_finite_term (development_goal_value g)=admission_goal_value_with
    (\<lambda>d. site_data_term (fst d) (snd d)) g"
  by (induction g) simp_all

definition development_condition_value ::
    "native_development_condition \<Rightarrow> finite_factor_term" where
  "development_condition_value C=finite_data_sequence [finite_environment_value (condition_source C),
    development_site_value (condition_source_use C,condition_source_root C),
    finite_data_sequence (map development_goal_value (condition_goals C))]"

text \<open>
  Original conditions are complete native source-and-goal subjects. Their
  compiled guards are generated by the existing planner. Observation consumes
  the original input and every candidate occurrence; evidence inspection reads
  the source, demand, complete answers and every original proof. Its equation
  refers to original native meaning, not a supplied satisfaction table.
  The value view composes the established environment, coordinate and goal
  presentations for subsequent native criticism.
\<close>

end
