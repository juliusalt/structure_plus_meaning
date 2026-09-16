theory Native_Development_Execution_Base
  imports Factor_Constructed_Development_Execution Native_Workflow_Execution_Base
begin

definition native_development_indices :: "nat list" where
  "native_development_indices=[0..<length development_case_inputs]"

definition native_development_batch :: "native_development_question list \<Rightarrow>
    (nat\<times>native_development_question\<times>native_development_report\<times>finite_factor_term list option) list" where
  "native_development_batch qs=Parallel.map (\<lambda>(i,Q). (i,native_development_packet Q)) (zip [0..<length qs] qs)"

lemma native_development_batch_at:
  "i<length qs \<Longrightarrow> native_development_batch qs!i=(i,native_development_packet (qs!i))"
  by (simp add: native_development_batch_def Parallel.map_def)

end
