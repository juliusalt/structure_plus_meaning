theory Factor_Workflow_Protocol
  imports Factor_Workflow_Execution
begin

record development_workflow_protocol =
  problem_formation_stage :: native_workflow_stage
  requirement_reasoning_stage :: native_workflow_stage
  candidate_construction_stage :: native_workflow_stage
  evidence_observation_stage :: native_workflow_stage
  independent_criticism_stage :: native_workflow_stage
  comparison_revision_stage :: native_workflow_stage
  construction_validation_stage :: native_workflow_stage
  reconstruction_retention_stage :: native_workflow_stage

definition development_workflow_stages :: "development_workflow_protocol \<Rightarrow> native_workflow_stage list" where
  "development_workflow_stages W=[problem_formation_stage W,requirement_reasoning_stage W,
    candidate_construction_stage W,evidence_observation_stage W,independent_criticism_stage W,
    comparison_revision_stage W,construction_validation_stage W,reconstruction_retention_stage W]"

definition construct_development_workflow :: "development_workflow_protocol \<Rightarrow> finite_factor_term \<Rightarrow>
    native_workflow_execution" where
  "construct_development_workflow W problem=execute_workflow (development_workflow_stages W) problem []"

definition development_workflow_results :: "development_workflow_protocol \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term list list" where
  "development_workflow_results W problem=workflow_completed_paths (construct_development_workflow W problem)"

theorem development_workflow_all_stages:
  assumes result: "path\<in>set (development_workflow_results W problem)"
  shows "length path=8"
    "i<8 \<Longrightarrow> workflow_stage_relation (development_workflow_stages W!i)
      (workflow_stage_input problem (take i path)) (path!i)"
proof -
  have whole: "workflow_path_holds (development_workflow_stages W) problem [] path"
    by (rule execute_workflow_complete_path)
      (use result in \<open>simp only: development_workflow_results_def construct_development_workflow_def\<close>)
  show "length path=8" using workflow_path_length[OF whole]
    by (simp add: development_workflow_stages_def)
  show "i<8 \<Longrightarrow> workflow_stage_relation (development_workflow_stages W!i)
      (workflow_stage_input problem (take i path)) (path!i)"
    using completed_workflow_at_stage[OF whole] by (simp add: development_workflow_stages_def)
qed

locale development_workflow_contract =
  fixes W :: development_workflow_protocol
    and required :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow>
      finite_factor_term \<Rightarrow> bool"
  assumes complete_stage_meanings: "\<And>i problem prior value. i<8 \<Longrightarrow> length prior=i \<Longrightarrow>
    workflow_stage_relation (development_workflow_stages W!i)
      (workflow_stage_input problem prior) value \<longleftrightarrow> required i problem prior value"
begin

theorem every_required_transition:
  assumes result: "path\<in>set (development_workflow_results W problem)" and index: "i<8"
  shows "required i problem (take i path) (path!i)"
proof -
  have length: "length path=8" by (rule development_workflow_all_stages(1)[OF result])
  have meaning: "workflow_stage_relation (development_workflow_stages W!i)
      (workflow_stage_input problem (take i path)) (path!i)"
    by (rule development_workflow_all_stages(2)[OF result index])
  have prefix: "length (take i path)=i" using length index by simp
  show ?thesis using meaning complete_stage_meanings[OF index prefix] by blast
qed

corollary failed_requirement_prevents_completion:
  assumes "i<8" "\<not>required i problem (take i path) (path!i)"
  shows "path\<notin>set (development_workflow_results W problem)"
  using every_required_transition assms by blast

end

definition workflow_reconstruction_boundary :: "development_workflow_protocol \<Rightarrow> finite_factor_term \<Rightarrow>
    development_workflow_protocol \<times> finite_factor_term" where
  "workflow_reconstruction_boundary W problem=(W,problem)"

definition reconstruct_development_workflow :: "development_workflow_protocol \<times> finite_factor_term \<Rightarrow>
    native_workflow_execution" where
  "reconstruct_development_workflow boundary=(case boundary of (W,problem) \<Rightarrow>
    construct_development_workflow W problem)"

lemma workflow_reconstructed:
  "reconstruct_development_workflow (workflow_reconstruction_boundary W problem)=
    construct_development_workflow W problem"
  by (simp only: reconstruct_development_workflow_def workflow_reconstruction_boundary_def case_prod_conv)

text \<open>
  The full workflow has fixed required positions, shared original subjects and
  computed predecessor results. The constructor cannot omit an entire phase.
  One retained local source-and-input boundary reconstructs every branch,
  observation and native certificate; an accumulated process history is not
  an argument of that computation.

  Position names do not establish meaning. The independent complete-stage
  equations are mandatory premises, including problem adequacy, constructive
  scope, independent criticism and the actual retention condition. An arbitrary
  program record is not an instance of those equations. This compiler's own
  construction and those remaining instances must enter the same process;
  this conditional contract does not declare the six conditions settled.
\<close>

export_code construct_development_workflow development_workflow_results
  workflow_reconstruction_boundary reconstruct_development_workflow checking SML

end
