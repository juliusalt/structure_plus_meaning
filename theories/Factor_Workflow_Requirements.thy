theory Factor_Workflow_Requirements
  imports Factor_Workflow_Admission Factor_Finite_Native_Requirements
begin

record native_workflow_requirement =
  requirement_source :: "local_address option finite_artifact_environment"
  requirement_source_use :: "local_address option"
  requirement_source_root :: local_address
  requirement_goals :: "local_address option definition_site admission_goal list"
  requirement_candidates :: workflow_output_scope

definition workflow_requirement_holds :: "native_workflow_requirement \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "workflow_requirement_holds R input output \<longleftrightarrow>
    (\<exists>P. native_package_at (decode_finite_environment (requirement_source R))
      (requirement_source_use R) (requirement_source_root R) (decode_finite_system P) \<and>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) (requirement_goals R)
        (Pair_Term (decode_finite_term input) (decode_finite_term output)))"

definition compile_workflow_requirement :: "native_workflow_requirement \<Rightarrow> native_workflow_stage option" where
  "compile_workflow_requirement R=map_option (\<lambda>(d,F,u).
    \<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
      workflow_outputs=requirement_candidates R\<rparr>)
    (finite_construct_source_requirements (requirement_source R) (requirement_source_use R)
      (requirement_source_root R) (requirement_goals R))"

theorem compiled_workflow_requirement_exact:
  assumes compiled: "compile_workflow_requirement R=Some S"
  shows "workflow_stage_relation S input output \<longleftrightarrow>
    output\<in>set (workflow_scope_values S input) \<and> workflow_requirement_holds R input output"
proof -
  obtain d F u where constructed: "finite_construct_source_requirements (requirement_source R)
      (requirement_source_use R) (requirement_source_root R) (requirement_goals R)=Some (d,F,u)"
    and stage: "S=\<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
      workflow_outputs=requirement_candidates R\<rparr>"
    using compiled by (auto simp: compile_workflow_requirement_def split: option.splits prod.splits)
  obtain P T where original: "native_package_at (decode_finite_environment (requirement_source R))
      (requirement_source_use R) (requirement_source_root R) (decode_finite_system P)"
    and target: "native_package_at (decode_finite_environment F) u [] T"
    and entry: "d\<in>system_definitions T"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) (requirement_goals R) t"
    using finite_construct_source_requirements_correct[OF constructed] by blast
  have unique_original: "N=P" if "native_package_at (decode_finite_environment (requirement_source R))
      (requirement_source_use R) (requirement_source_root R) (decode_finite_system N)" for N
    using native_package_unique[OF that original] by simp
  have unique_target: "decode_finite_system N=T"
    if "native_package_at (decode_finite_environment F) u [] (decode_finite_system N)" for N
    by (rule native_package_unique[OF that target])
  have available: "finite_native_source F u []\<noteq>None"
    using target by (simp only: finite_native_source_absent; blast)
  obtain N where native: "native_package_at (decode_finite_environment F) u [] (decode_finite_system N)"
    using available by (cases "finite_native_source F u []")
      (auto simp only: finite_native_source_correct)
  have target_value: "decode_finite_system N=T" by (rule unique_target[OF native])
  have required: "workflow_requirement_holds R input output \<longleftrightarrow>
    admission_requirements_hold (positive_meaning (decode_finite_system P)) (requirement_goals R)
      (Pair_Term (decode_finite_term input) (decode_finite_term output))"
  proof
    assume holds: "workflow_requirement_holds R input output"
    obtain L where source: "native_package_at (decode_finite_environment (requirement_source R))
        (requirement_source_use R) (requirement_source_root R) (decode_finite_system L)"
      and goals: "admission_requirements_hold (positive_meaning (decode_finite_system L)) (requirement_goals R)
        (Pair_Term (decode_finite_term input) (decode_finite_term output))"
      using holds by (simp only: workflow_requirement_holds_def; blast)
    have equal: "L=P" by (rule unique_original[OF source])
    show "admission_requirements_hold (positive_meaning (decode_finite_system P)) (requirement_goals R)
      (Pair_Term (decode_finite_term input) (decode_finite_term output))"
      using goals by (simp only: equal)
  next
    assume goals: "admission_requirements_hold (positive_meaning (decode_finite_system P)) (requirement_goals R)
      (Pair_Term (decode_finite_term input) (decode_finite_term output))"
    show "workflow_requirement_holds R input output"
      unfolding workflow_requirement_holds_def
      by (rule exI[of _ P], rule conjI[OF original goals])
  qed
  have relation: "workflow_stage_relation S input output \<longleftrightarrow>
    output\<in>set (workflow_scope_values S input) \<and>
    (d,Pair_Term (decode_finite_term input) (decode_finite_term output))\<in>positive_meaning T"
  proof
    assume holds: "workflow_stage_relation S input output"
    obtain L where actual: "native_package_at (decode_finite_environment F) u [] (decode_finite_system L)"
      and positive: "(d,Pair_Term (decode_finite_term input) (decode_finite_term output))
        \<in>positive_meaning (decode_finite_system L)"
      and selected: "output\<in>set (workflow_scope_values S input)"
      using holds by (auto simp: workflow_stage_relation_def stage)
    show "output\<in>set (workflow_scope_values S input) \<and>
      (d,Pair_Term (decode_finite_term input) (decode_finite_term output))\<in>positive_meaning T"
      using positive selected by (simp only: unique_target[OF actual])
  next
    assume holds: "output\<in>set (workflow_scope_values S input) \<and>
      (d,Pair_Term (decode_finite_term input) (decode_finite_term output))\<in>positive_meaning T"
    have witnessed: "\<exists>L. native_package_at (decode_finite_environment F) u [] (decode_finite_system L) \<and>
      d\<in>system_definitions (decode_finite_system L) \<and>
      (d,Pair_Term (decode_finite_term input) (decode_finite_term output))\<in>positive_meaning (decode_finite_system L)"
      by (rule exI[of _ N]) (use native entry holds in \<open>simp only: target_value; blast\<close>)
    show "workflow_stage_relation S input output"
      using holds witnessed by (simp only: workflow_stage_relation_def stage native_workflow_stage.select_convs; blast)
  qed
  show ?thesis using relation required meaning by blast
qed

record required_development_workflow =
  required_problem_formation :: native_workflow_requirement
  required_requirement_reasoning :: native_workflow_requirement
  required_candidate_construction :: native_workflow_requirement
  required_evidence_observation :: native_workflow_requirement
  required_independent_criticism :: native_workflow_requirement
  required_comparison_revision :: native_workflow_requirement
  required_construction_validation :: native_workflow_requirement
  required_reconstruction_retention :: native_workflow_requirement

definition development_workflow_requirements :: "required_development_workflow \<Rightarrow> native_workflow_requirement list" where
  "development_workflow_requirements R=[required_problem_formation R,required_requirement_reasoning R,
    required_candidate_construction R,required_evidence_observation R,required_independent_criticism R,
    required_comparison_revision R,required_construction_validation R,required_reconstruction_retention R]"

definition compile_development_workflow :: "required_development_workflow \<Rightarrow> development_workflow_protocol option" where
  "compile_development_workflow R=(case compile_workflow_requirement (required_problem_formation R) of
    None \<Rightarrow> None | Some a \<Rightarrow> (case compile_workflow_requirement (required_requirement_reasoning R) of
    None \<Rightarrow> None | Some b \<Rightarrow> (case compile_workflow_requirement (required_candidate_construction R) of
    None \<Rightarrow> None | Some c \<Rightarrow> (case compile_workflow_requirement (required_evidence_observation R) of
    None \<Rightarrow> None | Some d \<Rightarrow> (case compile_workflow_requirement (required_independent_criticism R) of
    None \<Rightarrow> None | Some e \<Rightarrow> (case compile_workflow_requirement (required_comparison_revision R) of
    None \<Rightarrow> None | Some f \<Rightarrow> (case compile_workflow_requirement (required_construction_validation R) of
    None \<Rightarrow> None | Some g \<Rightarrow> (case compile_workflow_requirement (required_reconstruction_retention R) of
    None \<Rightarrow> None | Some h \<Rightarrow> Some \<lparr>problem_formation_stage=a,requirement_reasoning_stage=b,
      candidate_construction_stage=c,evidence_observation_stage=d,independent_criticism_stage=e,
      comparison_revision_stage=f,construction_validation_stage=g,reconstruction_retention_stage=h\<rparr>))))))))"

lemma compile_development_workflow_stages:
  assumes compiled: "compile_development_workflow R=Some W"
  shows "list_all2 (\<lambda>r s. compile_workflow_requirement r=Some s)
    (development_workflow_requirements R) (development_workflow_stages W)"
  using compiled by (auto simp: compile_development_workflow_def development_workflow_requirements_def
    development_workflow_stages_def split: option.splits)

definition construct_required_development_workflow where
  "construct_required_development_workflow R problem=map_option
    (\<lambda>W. construct_development_workflow W problem) (compile_development_workflow R)"

definition admit_required_development_workflow where
  "admit_required_development_workflow R problem execution=(case compile_development_workflow R of
    None \<Rightarrow> None | Some W \<Rightarrow> admit_development_workflow W problem execution)"

theorem admitted_compiled_workflow_requirements:
  assumes admitted: "admit_required_development_workflow R problem execution=Some paths"
    and path: "ys\<in>set paths" and position: "i<8"
  shows "workflow_requirement_holds (development_workflow_requirements R!i)
    (workflow_stage_input problem (take i ys)) (ys!i)"
proof -
  obtain W where compiled: "compile_development_workflow R=Some W"
    and checked: "admit_development_workflow W problem execution=Some paths"
    using admitted by (auto simp: admit_required_development_workflow_def split: option.splits)
  have result: "ys\<in>set (development_workflow_results W problem)"
    using path admitted_workflow_complete_results[OF checked] by simp
  have relation: "workflow_stage_relation (development_workflow_stages W!i)
      (workflow_stage_input problem (take i ys)) (ys!i)"
    by (rule development_workflow_all_stages(2)[OF result position])
  have bound: "i<length (development_workflow_requirements R)"
    using position by (simp add: development_workflow_requirements_def)
  have stage: "compile_workflow_requirement (development_workflow_requirements R!i)=
      Some (development_workflow_stages W!i)"
    using list_all2_nthD[OF compile_development_workflow_stages[OF compiled] bound] .
  show ?thesis using relation compiled_workflow_requirement_exact[OF stage] by blast
qed

corollary failed_original_requirement_prevents_workflow_admission:
  assumes admitted: "admit_required_development_workflow R problem execution=Some paths"
    and position: "i<8"
    and failed: "\<not>workflow_requirement_holds (development_workflow_requirements R!i)
      (workflow_stage_input problem (take i ys)) (ys!i)"
  shows "ys\<notin>set paths"
  using admitted_compiled_workflow_requirements[OF admitted _ position] failed by blast

definition required_workflow_boundary where
  "required_workflow_boundary R problem=(R,problem)"

definition reconstruct_required_workflow where
  "reconstruct_required_workflow boundary=(case boundary of (R,problem) \<Rightarrow>
    construct_required_development_workflow R problem)"

lemma required_workflow_reconstructed:
  "reconstruct_required_workflow (required_workflow_boundary R problem)=
    construct_required_development_workflow R problem"
  by (simp only: required_workflow_boundary_def reconstruct_required_workflow_def case_prod_conv)

text \<open>
  The original requirements are complete native source-and-goal subjects.
  Compilation constructs every required occurrence and guard at every fixed
  workflow position. Submission receives those original requirements and
  derives the whole protocol itself. An independently supplied permissive
  protocol cannot authorize a result. All completed paths satisfy all original
  native goals; failure to compile any position prevents submission.

  The local boundary reconstructs the compiled source, complete executions and
  certificates. Adequacy of the original goal family for the development role,
  candidate-generation scope and the native representation of each real
  development problem remain separate obligations. Slot names establish none
  of those meanings.
\<close>

end
