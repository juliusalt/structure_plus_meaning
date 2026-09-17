theory Finite_Presented_Workflows
  imports Finite_Viewed_Values Finite_Presented_Native_Certificates Factor_Workflow_Execution
    Factor_Workflow_Requirements Factor_Workflow_Protocol Factor_Development_Cycle
begin

section \<open>Answered native demands\<close>

definition finite_native_answered_demand_value where
  "finite_native_answered_demand_value evidence=finite_pair_presentation finite_native_system_value
    (finite_pair_presentation (finite_collection_presentation finite_call_value)
      (finite_pair_presentation (finite_collection_presentation finite_call_value) evidence))"

lemma finite_native_answered_demand_value_injective [intro]:
  "inj evidence \<Longrightarrow> inj (finite_native_answered_demand_value evidence)"
  unfolding finite_native_answered_demand_value_def
  by (intro finite_pair_presentation_injective finite_native_system_value_injective
      finite_collection_presentation_injective finite_call_value_injective)

definition finite_workflow_stage_result_value :: "native_workflow_stage_result \<Rightarrow> finite_factor_term" where
  "finite_workflow_stage_result_value=finite_native_answered_demand_value
    (finite_pair_presentation (finite_collection_presentation finite_history_certificate_value)
      (finite_sequence_presentation id))"

lemma finite_workflow_stage_result_value_injective [intro]: "inj finite_workflow_stage_result_value"
  unfolding finite_workflow_stage_result_value_def
  by (intro finite_native_answered_demand_value_injective finite_pair_presentation_injective
      finite_collection_presentation_injective finite_history_certificate_value_injective
      finite_sequence_presentation_injective inj_on_id)

definition native_development_application_view ::
  "native_development_application \<Rightarrow> native_history_application" where
  "native_development_application_view a=(case a of ((d,c),rest) \<Rightarrow> (d,c,rest))"

lemma native_development_application_view_injective [intro]: "inj native_development_application_view"
  by (rule injI) (auto simp: native_development_application_view_def split: prod.splits)

definition finite_native_generation_value :: "native_development_generation \<Rightarrow> finite_factor_term" where
  "finite_native_generation_value=finite_native_answered_demand_value (finite_sequence_presentation
    (finite_viewed_value finite_native_application_value native_development_application_view))"

lemma finite_native_generation_value_injective [intro]: "inj finite_native_generation_value"
  unfolding finite_native_generation_value_def
  by (intro finite_native_answered_demand_value_injective finite_sequence_presentation_injective
      finite_viewed_value_injective finite_native_application_value_injective
      native_development_application_view_injective)

section \<open>Workflow stages, requirements, protocols and executions\<close>

fun finite_workflow_output_scope_value :: "workflow_output_scope \<Rightarrow> finite_factor_term" where
  "finite_workflow_output_scope_value Workflow_Input=Finite_Payload [0]"
| "finite_workflow_output_scope_value (Workflow_Values ys)=
    Finite_Pair (Finite_Payload [1]) (finite_sequence_presentation id ys)"
| "finite_workflow_output_scope_value (Workflow_Generated d)=Finite_Pair (Finite_Payload [2]) (finite_site_data d)"

lemma finite_workflow_output_scope_value_injective [intro]: "inj finite_workflow_output_scope_value"
proof (rule injI)
  fix x y assume "finite_workflow_output_scope_value x=finite_workflow_output_scope_value y"
  then show "x=y"
    by (cases x; cases y) (simp_all add: inj_eq[OF finite_sequence_presentation_injective[OF inj_on_id]]
      inj_eq[OF finite_site_data_injective])
qed

definition native_workflow_stage_view :: "native_workflow_stage \<Rightarrow> _" where
  "native_workflow_stage_view S=(workflow_source S,workflow_source_use S,workflow_source_root S,
    workflow_entry S,workflow_outputs S)"

lemma native_workflow_stage_view_injective [intro]: "inj native_workflow_stage_view"
proof (rule injI)
  fix x y :: native_workflow_stage
  assume same: "native_workflow_stage_view x=native_workflow_stage_view y"
  show "x=y" by (rule native_workflow_stage.equality; use same in \<open>simp add: native_workflow_stage_view_def\<close>)
qed

definition finite_workflow_stage_value where
  "finite_workflow_stage_value=finite_viewed_value (finite_native_source_problem_value
    (finite_pair_presentation finite_site_data finite_workflow_output_scope_value)) native_workflow_stage_view"

lemma finite_workflow_stage_value_injective [intro]: "inj finite_workflow_stage_value"
  unfolding finite_workflow_stage_value_def
  by (intro finite_viewed_value_injective finite_native_source_problem_value_injective
      finite_pair_presentation_injective finite_site_data_injective finite_workflow_output_scope_value_injective
      native_workflow_stage_view_injective)

definition native_workflow_requirement_view :: "native_workflow_requirement \<Rightarrow> _" where
  "native_workflow_requirement_view R=(requirement_source R,requirement_source_use R,requirement_source_root R,
    requirement_goals R,requirement_candidates R)"

lemma native_workflow_requirement_view_injective [intro]: "inj native_workflow_requirement_view"
proof (rule injI)
  fix x y :: native_workflow_requirement
  assume same: "native_workflow_requirement_view x=native_workflow_requirement_view y"
  show "x=y" by (rule native_workflow_requirement.equality; use same in \<open>simp add: native_workflow_requirement_view_def\<close>)
qed

definition finite_workflow_requirement_value where
  "finite_workflow_requirement_value=finite_viewed_value (finite_native_source_problem_value
    (finite_pair_presentation (finite_sequence_presentation (finite_goal_value finite_site_data))
      finite_workflow_output_scope_value)) native_workflow_requirement_view"

lemma finite_workflow_requirement_value_injective [intro]: "inj finite_workflow_requirement_value"
  unfolding finite_workflow_requirement_value_def
  by (intro finite_viewed_value_injective finite_native_source_problem_value_injective
      finite_pair_presentation_injective finite_sequence_presentation_injective finite_goal_value_injective
      finite_site_data_injective finite_workflow_output_scope_value_injective native_workflow_requirement_view_injective)

lemma development_workflow_requirements_injective [intro]: "inj development_workflow_requirements"
proof (rule injI)
  fix x y :: required_development_workflow
  assume same: "development_workflow_requirements x=development_workflow_requirements y"
  show "x=y" by (rule required_development_workflow.equality; use same in \<open>simp add: development_workflow_requirements_def\<close>)
qed

definition finite_required_workflow_value where
  "finite_required_workflow_value=finite_viewed_value (finite_sequence_presentation finite_workflow_requirement_value)
    development_workflow_requirements"

lemma finite_required_workflow_value_injective [intro]: "inj finite_required_workflow_value"
  unfolding finite_required_workflow_value_def
  by (intro finite_viewed_value_injective finite_sequence_presentation_injective
      finite_workflow_requirement_value_injective development_workflow_requirements_injective)

lemma development_workflow_stages_injective [intro]: "inj development_workflow_stages"
proof (rule injI)
  fix x y :: development_workflow_protocol
  assume same: "development_workflow_stages x=development_workflow_stages y"
  show "x=y" by (rule development_workflow_protocol.equality; use same in \<open>simp add: development_workflow_stages_def\<close>)
qed

definition finite_workflow_protocol_value where
  "finite_workflow_protocol_value=finite_viewed_value (finite_sequence_presentation finite_workflow_stage_value)
    development_workflow_stages"

lemma finite_workflow_protocol_value_injective [intro]: "inj finite_workflow_protocol_value"
  unfolding finite_workflow_protocol_value_def
  by (intro finite_viewed_value_injective finite_sequence_presentation_injective
      finite_workflow_stage_value_injective development_workflow_stages_injective)

fun finite_workflow_execution_value :: "native_workflow_execution \<Rightarrow> finite_factor_term" where
  "finite_workflow_execution_value (Workflow_Finished ys)=
    Finite_Pair (Finite_Payload [0]) (finite_sequence_presentation id ys)"
| "finite_workflow_execution_value (Workflow_Unavailable S x)=
    Finite_Pair (Finite_Payload [1]) (finite_pair_presentation finite_workflow_stage_value id (S,x))"
| "finite_workflow_execution_value (Workflow_Executed S x result children)=
    Finite_Pair (Finite_Payload [2]) (finite_pair_presentation finite_workflow_stage_value
      (finite_pair_presentation id (finite_pair_presentation finite_workflow_stage_result_value
        (finite_sequence_presentation (finite_pair_presentation id id))))
      (S,x,result,map (\<lambda>(y,child). (y,finite_workflow_execution_value child)) children))"

lemma finite_workflow_execution_value_injective [intro]: "inj finite_workflow_execution_value"
proof (rule injI)
  have stage: "inj (finite_pair_presentation finite_workflow_stage_value id)"
    by (intro finite_pair_presentation_injective finite_workflow_stage_value_injective inj_on_id)
  have executed: "inj (finite_pair_presentation finite_workflow_stage_value
      (finite_pair_presentation id (finite_pair_presentation finite_workflow_stage_result_value
        (finite_sequence_presentation (finite_pair_presentation id id)))))"
    by (intro finite_pair_presentation_injective finite_workflow_stage_value_injective inj_on_id
        finite_workflow_stage_result_value_injective finite_sequence_presentation_injective)
  fix a b show "finite_workflow_execution_value a=finite_workflow_execution_value b \<Longrightarrow> a=b"
  proof (induction a arbitrary: b)
    case (Workflow_Finished ys)
    then show ?case
      by (cases b) (simp_all add: inj_eq[OF finite_sequence_presentation_injective[OF inj_on_id]])
  next
    case (Workflow_Unavailable S x)
    then show ?case by (cases b) (simp_all add: inj_eq[OF stage] inj_eq[OF finite_workflow_stage_value_injective])
  next
    case (Workflow_Executed S x result children)
    show ?case
    proof (cases b)
      case (Workflow_Executed S' x' result' children')
      have same: "S=S'" "x=x'" "result=result'"
        and rows: "map (\<lambda>(y,child). (y,finite_workflow_execution_value child)) children=
          map (\<lambda>(y,child). (y,finite_workflow_execution_value child)) children'"
        using Workflow_Executed.prems Workflow_Executed
        by (simp_all add: inj_eq[OF executed] inj_eq[OF finite_workflow_stage_value_injective]
          inj_eq[OF finite_workflow_stage_result_value_injective]
          inj_eq[OF finite_sequence_presentation_injective[OF finite_pair_presentation_injective[OF inj_on_id inj_on_id]]])
      have "children=children'"
        by (rule map_injective_at_left[OF rows])
          (use Workflow_Executed.IH in \<open>auto split: prod.splits\<close>)
      then show ?thesis using same Workflow_Executed by simp
    qed (use Workflow_Executed.prems in simp_all)
  qed
qed

section \<open>Development conditions, questions and reports\<close>

definition native_development_condition_view :: "native_development_condition \<Rightarrow> _" where
  "native_development_condition_view C=(condition_source C,condition_source_use C,condition_source_root C,
    condition_goals C)"

lemma native_development_condition_view_injective [intro]: "inj native_development_condition_view"
proof (rule injI)
  fix x y :: native_development_condition
  assume same: "native_development_condition_view x=native_development_condition_view y"
  show "x=y" by (rule native_development_condition.equality; use same in \<open>simp add: native_development_condition_view_def\<close>)
qed

definition finite_development_condition_value where
  "finite_development_condition_value=finite_viewed_value (finite_native_source_problem_value
    (finite_sequence_presentation (finite_goal_value finite_site_data))) native_development_condition_view"

lemma finite_development_condition_value_injective [intro]: "inj finite_development_condition_value"
  unfolding finite_development_condition_value_def
  by (intro finite_viewed_value_injective finite_native_source_problem_value_injective
      finite_sequence_presentation_injective finite_goal_value_injective finite_site_data_injective
      native_development_condition_view_injective)

definition finite_condition_execution_value :: "native_condition_execution \<Rightarrow> finite_factor_term" where
  "finite_condition_execution_value=finite_pair_presentation finite_workflow_stage_value finite_workflow_stage_result_value"

lemma finite_condition_execution_value_injective [intro]: "inj finite_condition_execution_value"
  unfolding finite_condition_execution_value_def
  by (intro finite_pair_presentation_injective finite_workflow_stage_value_injective
      finite_workflow_stage_result_value_injective)

definition native_development_question_view :: "native_development_question \<Rightarrow> _" where
  "native_development_question_view Q=(development_source Q,development_source_use Q,development_source_root Q,
    development_generator_entry Q,development_problem Q,development_conditions Q,development_scope_criticism Q,
    development_selected_facets Q)"

lemma native_development_question_view_injective [intro]: "inj native_development_question_view"
proof (rule injI)
  fix x y :: native_development_question
  assume same: "native_development_question_view x=native_development_question_view y"
  show "x=y" by (rule native_development_question.equality; use same in \<open>simp add: native_development_question_view_def\<close>)
qed

definition finite_development_question_value where
  "finite_development_question_value=finite_viewed_value (finite_native_source_problem_value
    (finite_pair_presentation finite_site_data (finite_pair_presentation id
      (finite_pair_presentation (finite_sequence_presentation finite_development_condition_value)
        (finite_pair_presentation finite_development_condition_value finite_index_sequence_value)))))
    native_development_question_view"

lemma finite_development_question_value_injective [intro]: "inj finite_development_question_value"
  unfolding finite_development_question_value_def
  by (intro finite_viewed_value_injective finite_native_source_problem_value_injective
      finite_pair_presentation_injective finite_site_data_injective inj_on_id finite_sequence_presentation_injective
      finite_development_condition_value_injective finite_index_values_injective
      native_development_question_view_injective)

definition native_development_report_view :: "native_development_report \<Rightarrow> _" where
  "native_development_report_view report=(development_generation report,development_compiled_conditions report,
    development_observed_conditions report,development_scope_review report,development_comparison report,
    development_revision report)"

lemma native_development_report_view_injective [intro]: "inj native_development_report_view"
proof (rule injI)
  fix x y :: native_development_report
  assume same: "native_development_report_view x=native_development_report_view y"
  show "x=y" by (rule native_development_report.equality; use same in \<open>simp add: native_development_report_view_def\<close>)
qed

definition finite_development_report_value where
  "finite_development_report_value=finite_viewed_value (finite_pair_presentation
    (finite_option_presentation finite_native_generation_value)
    (finite_pair_presentation (finite_option_presentation (finite_sequence_presentation
        (finite_option_presentation finite_workflow_stage_value)))
      (finite_pair_presentation (finite_option_presentation (finite_sequence_presentation
          (finite_option_presentation finite_condition_execution_value)))
        (finite_pair_presentation (finite_option_presentation finite_condition_execution_value)
          (finite_pair_presentation (finite_option_presentation finite_investigation_comparison_value)
            (finite_option_presentation finite_investigation_cycle_value))))))
    native_development_report_view"

lemma finite_development_report_value_injective [intro]: "inj finite_development_report_value"
  unfolding finite_development_report_value_def
  by (intro finite_viewed_value_injective finite_pair_presentation_injective finite_option_presentation_injective
      finite_native_generation_value_injective finite_sequence_presentation_injective
      finite_workflow_stage_value_injective finite_condition_execution_value_injective
      finite_investigation_values_injective native_development_report_view_injective)

definition finite_development_decision_value :: "finite_factor_term list option \<Rightarrow> finite_factor_term" where
  "finite_development_decision_value=finite_option_presentation (finite_sequence_presentation id)"

lemma finite_development_decision_value_injective [intro]: "inj finite_development_decision_value"
  unfolding finite_development_decision_value_def
  by (intro finite_option_presentation_injective finite_sequence_presentation_injective inj_on_id)

text \<open>
  An answered demand keeps a native system with its demand, answers and
  evidence; stage results and generations specialize it with certificates and
  outputs or generated applications. Development applications are native
  applications in another nesting and are presented through that view. Records
  are presented through the view of all their fields: workflow stages,
  requirements and development conditions specialize native source problems,
  required workflows and protocols are the ordered lists of their eight roles,
  and development questions and reports keep every field through the
  presentations of its notion. An execution keeps its stage, input, result and
  every child execution. No presentation computes an observation of its subject.
\<close>

end
