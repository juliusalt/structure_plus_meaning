theory History_Stage_Operations
  imports Factor_Constructed_History_Investigation
begin

definition history_stage_context where
  "history_stage_context subjects=constructed_history.make_context subjects"

definition history_stage_assessment where
  "history_stage_assessment m context=constructed_history.assessment m context"

lemma history_stage_observation_exact:
  "digit_history_question_inspect (history_stage_assessment m
      (history_stage_context subjects)) f=
    digit_history_question_condition f (constructed_history_family_method m) subjects"
  by (simp only: history_stage_assessment_def history_stage_context_def
      constructed_history.assessment_exact constructed_history_family_method_def)

text \<open>Monomorphic export names expose the existing complete context and
  assessment operations for physical stage measurements. Their observations
  remain the original independently stated history condition.\<close>

end
