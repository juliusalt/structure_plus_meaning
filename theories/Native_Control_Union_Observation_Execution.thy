theory Native_Control_Union_Observation_Execution
  imports Native_Control_Syntax_Candidate
begin

lemma left_projection_union_exact:
  "A=A |\<union>| B \<longleftrightarrow> B |\<subseteq>| A"
  by auto

declare union_observation_def[code del]

lemma union_observation_original_code [code]:
  "union_observation Original_Union pairs=True"
  by (simp add: union_observation_def list_all_iff split_def)

lemma union_observation_enumerated_code [code]:
  "union_observation Enumerated_Union pairs=True"
  by (simp add: union_observation_def enumerated_union_exact list_all_iff split_def)

lemma union_observation_left_code [code]:
  "union_observation Left_Projection pairs=list_all (\<lambda>(A,B). B |\<subseteq>| A) pairs"
  by (simp add: union_observation_def left_projection_union_exact split_def)

text \<open>These are proved equations of the original observer on every complete
  operand list. The two exact producers use their universal result equations;
  the incorrect control still examines the actual operands. No supplied truth
  table or profiling result enters the observation. The original context,
  subject construction, question, native criticism and complete report remain.\<close>

export_code union_execution_question union_execution_value context_execution_summary
  native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Union_Review file_prefix "native_control_union_review"

end
