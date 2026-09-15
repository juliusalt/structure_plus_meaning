theory Factor_Digit_History_Result_Candidates
  imports Factor_Digit_History_Investigation
begin

definition digit_history_produced_family where
  "digit_history_produced_family produce subjects=fimage (\<lambda>(key,input).
    (key,map_option produce input)) subjects"

locale digit_history_result_candidates =
  fixes producers :: "(digit_history_subject\<Rightarrow>digit_history_result option) list"
begin

definition additional_results where
  "additional_results subjects=map (\<lambda>produce. digit_history_produced_family produce subjects) producers"

definition family_method where
  "family_method (m::nat) subjects=(if m<length producers then
    digit_history_produced_family (producers!m) subjects
    else digit_history_family_method (m-length producers) subjects)"

definition make_context where
  "make_context subjects=(digit_history_question_context subjects,additional_results subjects)"

definition assessment where
  "assessment (m::nat) prepared=(case prepared of ((covered,(subjects,old,reference)),additional) \<Rightarrow>
    if m<length additional then (covered,(additional!m,reference))
    else digit_history_question_assessment (m-length additional) (covered,(subjects,old,reference)))"

theorem assessment_exact:
  "digit_history_question_inspect (assessment m (make_context subjects)) f=
    digit_history_question_condition f (family_method m) subjects"
proof (cases "m<length producers")
  case True
  have direct: "assessment m (make_context subjects)=(digit_history_covered,
    (digit_history_produced_family (producers!m) subjects,digit_history_family_reference subjects))"
    by (simp add: assessment_def make_context_def additional_results_def digit_history_question_context_def
      digit_history_context_def Let_def True digit_history_prepared_reference_exact)
  show ?thesis by (simp only: direct digit_history_question_inspect_def fst_conv snd_conv
    digit_history_inspect_def finite_reader_inspect_exact[OF refl]
    digit_history_question_condition_def digit_history_family_condition_def
    family_method_def True if_True digit_history_covered_exact)
next
  case False
  have previous: "assessment m (make_context subjects)=
    digit_history_question_assessment (m-length producers) (digit_history_question_context subjects)"
    by (simp add: assessment_def make_context_def additional_results_def digit_history_question_context_def
      digit_history_context_def Let_def False)
  show ?thesis by (simp only: previous digit_history_question_assessment_exact
    family_method_def[abs_def] False if_False)
qed

definition methods :: "nat list" where
  "methods=[0..<length producers+19]"

definition packet where
  "packet ws selections=(let table=context_assessment_table methods ws
      (\<lambda>w. make_context (digit_history_case w)) assessment;
    compared=context_assessment_investigation methods [0,1] ws table digit_history_question_inspect
    in (table,compared,map (investigation_cycle_report methods [0,1]
      (fst compared) (fst (snd compared))) selections))"

end

declare digit_history_result_candidates.additional_results_def[code]
  digit_history_result_candidates.family_method_def[code]
  digit_history_result_candidates.make_context_def[code]
  digit_history_result_candidates.assessment_def[code]
  digit_history_result_candidates.methods_def[code]
  digit_history_result_candidates.packet_def[code]

text \<open>
  Actual additional producers accompany every complete original history
  method. Their results are computed once per subject and assessed against the
  original complete reference family. No correctness assumption is imposed on
  an added producer: the same contract supports proposed refinements and
  deliberate omitted-check controls. The native observation remains the
  independently established original transition condition.
\<close>

end
