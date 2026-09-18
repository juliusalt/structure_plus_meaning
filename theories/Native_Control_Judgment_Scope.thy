theory Native_Control_Judgment_Scope
  imports Native_Control_Judgment_Review Native_Control_Union_Observation_Execution
    Native_Control_Syntax_Execution
begin

text \<open>The first actual judgment question exposed a producer tie: a producer
  retaining only the first admissible result agrees on a singleton outcome. The
  preceding actual seed-union question has two independently proved admissible
  refinements. Both original problems therefore form this prospective scope;
  the new judgment request still receives its own original admission.\<close>

definition judgment_steering_questions :: "unit \<Rightarrow> native_development_question list" where
  "judgment_steering_questions ignored=(case union_execution_question () of None \<Rightarrow> []
    | Some U \<Rightarrow> (case judgment_bridge_question () of None \<Rightarrow> [] | Some J \<Rightarrow> [U,J]))"

lemma judgment_steering_original_inputs:
  assumes "union_execution_question ()=Some U" "judgment_bridge_question ()=Some J"
  shows "judgment_steering_questions ()=[U,J]"
  using assms by (simp only: judgment_steering_questions_def option.simps)

lemma judgment_steering_chosen_at_both:
  assumes first_question: "union_execution_question ()=Some U"
    and second_question: "judgment_bridge_question ()=Some J"
    and chosen: "development_steering_choice
      (snd (snd (development_steering_packet (judgment_steering_questions ()))))=Some m"
    and facet: "f\<in>set development_facets"
  shows "development_producer_condition f (development_producer m) U"
    "development_producer_condition f (development_producer m) J"
  by (rule development_chosen_producer_conditions[OF chosen facet];
    simp only: judgment_steering_original_inputs[OF first_question second_question] set_simps; simp)+

export_code judgment_steering_questions judgment_bridge_question judgment_bridge_value
  judgment_bridge_receive judgment_bridge_receive_summary judgment_bridge_receiving_value
  judgment_bridge_evaluation judgment_bridge_evaluation_summary
  context_execution_summary native_steered_development finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Judgment file_prefix "native_control_judgment"

end
