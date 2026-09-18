theory Native_Control_Receiving_Controls
  imports Native_Control_Receiving_Review
begin

definition receiving_review_scopes where
  "receiving_review_scopes = [
    (receiving_programs,receiving_facets),
    (rev receiving_programs,receiving_facets),
    (receiving_programs @ receiving_programs,receiving_facets),
    (receiving_programs,[Complete_Optional_View,Original_Source_Reader]),
    (receiving_programs,[Complete_Optional_View,No_Repeated_Reader]),
    (receiving_programs,[Original_Source_Reader,No_Repeated_Reader]),
    ([(Force_Optional,Always_Available)],receiving_facets),
    ([],receiving_facets)]"

definition receiving_scope_question where
  "receiving_scope_question scope = (case scope of (programs,facets) \<Rightarrow>
    faceted_native_question programs facets optional_view_observation)"

definition receiving_scope_choice where
  "receiving_scope_choice scope report = native_admitted_choice (fst scope)
    (receiving_scope_question scope) report"

lemma receiving_original_scope:
  "receiving_scope_question (receiving_programs,receiving_facets) = receiving_refinement_question ()"
  by (simp only: receiving_scope_question_def receiving_refinement_question_def prod.case)

lemma receiving_absent_choice:
  "receiving_scope_choice scope absent_development_report = None"
  by (simp only: receiving_scope_choice_def absent_native_choice)

export_code receiving_review_scopes receiving_scope_question receiving_scope_choice
  receiving_refinement_choice receiving_programs receiving_facets optional_view_observation
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Receiving_Controls file_prefix "native_control_receiving_controls"

text \<open>Reversal and repeated occurrences retain every concrete program.
  Each facet-omission scope leaves an independently specified distinction out
  of its question, making any remaining alternative explicit. The original
  complete question remains the only receiving-refinement admission. Refused
  and ambiguous diagnostic scopes cannot authorize its omission.\<close>

end
