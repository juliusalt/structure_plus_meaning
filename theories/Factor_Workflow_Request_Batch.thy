theory Factor_Workflow_Request_Batch
  imports Factor_Workflow_Request_Input "HOL-Library.Parallel"
begin

definition workflow_request_batch where
  "workflow_request_batch inputs=Parallel.map (\<lambda>(i,(specs,problem)).
    (i,workflow_request_packet specs problem)) (zip [0..<length inputs] inputs)"

theorem workflow_request_batch_at:
  assumes "i<length inputs"
  shows "workflow_request_batch inputs!i=(i,case inputs!i of (specs,problem) \<Rightarrow>
    workflow_request_packet specs problem)"
  using assms by (simp add: workflow_request_batch_def split_def)

lemma workflow_request_batch_indices:
  "map fst (workflow_request_batch inputs)=[0..<length inputs]"
  by (simp add: workflow_request_batch_def split_def comp_def)

text \<open>
  Each request is independent. The existing parallel-list contract preserves
  the complete input order and its ordinal correspondence. Every workflow's
  stages retain their own prerequisite order, original requirements and native
  admission. Parallel scheduling introduces no shared semantic state.
\<close>

end
