theory Native_Workflow_Execution_Base
  imports Factor_Workflow_Execution_Sharing Factor_Workflow_Expanded_Comparison Factor_Workflow_Request_Batch Parallel_Assessment_Execution
begin

definition workflow_input_scope_indices :: "nat list" where
  "workflow_input_scope_indices=[0]"

definition workflow_indices :: "nat list" where
  "workflow_indices=[0..<length workflow_case_inputs]"

definition required_workflow_indices :: "nat list" where
  "required_workflow_indices=[0..<length required_workflow_case_inputs]"

definition native_workflow_inspect ::
  "finite_factor_term list list \<times> finite_factor_term list list \<times> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "native_workflow_inspect report f=workflow_inspect report f"

end
