theory Native_Control_Context_Execution
  imports Native_Development_Steering Native_Control_Context_Contract Native_Control_Seed_Subject
begin


definition context_execution_changed :: isabelle_context where
  "context_execution_changed=(map (\<lambda>s. if s=STR ''HOL.eq'' then STR ''HOL.eq.moved'' else s)
    (fst development_seed_context),snd development_seed_context)"

definition context_execution_questions :: "unit \<Rightarrow> native_development_question list" where
  "context_execution_questions ignored=
    context_input_questions development_seed_context context_execution_changed"

definition context_execution_data where
  "context_execution_data=finite_pair_presentation isabelle_context_data
    (finite_pair_presentation isabelle_context_data
      (finite_steered_development_value finite_development_question_value))"

lemma context_execution_data_injective: "inj context_execution_data"
  unfolding context_execution_data_def
  by (intro finite_pair_presentation_injective isabelle_context_data_injective
    finite_development_values_injective finite_development_question_value_injective)

definition context_execution_value where
  "context_execution_value run=context_execution_data
    (development_seed_context,context_execution_changed,run)"

definition context_execution_summary where
  "context_execution_summary run=(
    fst (snd (snd run)),
    map (\<lambda>(w,original,cells). (w,map (\<lambda>(m,result,assessment).
      (m,assessment)) cells)) (fst (snd (fst (snd run)))),
    map_option (map (\<lambda>(m,Q,report,claim,accepted).
      (m,claim,accepted,development_comparison report,development_revision report)))
      (snd (snd (snd run))))"

definition context_execution_membership :: "unit \<Rightarrow> isabelle_acceptance_assessment" where
  "context_execution_membership ignored=isabelle_demand_acceptance (snd development_seed_context)
    (development_seed_demands development_seed_context)"

definition context_execution_membership_summary where
  "context_execution_membership_summary result=(let demands=development_seed_demands development_seed_context in
    map_option (\<lambda>(accepted,refused). map (\<lambda>i. (i,demands!i |\<in>| accepted,
      demands!i |\<in>| refused)) [0..<length demands]) result)"

text \<open>The report uses the existing proved presentation and execution closure.
  The value carries both original contexts and the complete native result. Its
  injective presentation, not a diagnostic projection or digest, determines that
  result. Membership is a separate unchanged operation and remains independently
  executable. None of these exports adds a checked-context provenance judgment.\<close>

export_code context_execution_questions context_execution_value context_execution_summary
  context_execution_membership context_execution_membership_summary
  development_seed_context development_seed_roots development_seed_demands
  isabelle_acceptance_source finite_native_source finite_native_program_evaluation
  isabelle_demand_acceptance isabelle_entity_data
  native_steered_development native_development_packet
  finite_term_shared_word_fold integer_of_nat nat_of_integer
  in Eval module_name Native_Control_Context file_prefix "native_control_context"

end
