theory Factor_Known_History_Investigation
  imports Factor_Digit_History_Known_Generation Factor_Digit_History_Investigation
begin

fun known_history_apply where
  "known_history_apply (q,History_Step l rows E pu pr au ar root R)=
    digit_history_known_step q l rows E pu pr au ar root R"

lemma known_history_apply_exact:
  "known_history_apply X=digit_history_apply X"
  by (cases X; cases "snd X") (simp add: digit_history_known_step_exact)

definition known_history_family_result where
  "known_history_family_result subjects=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>X. map_option digit_history_view (known_history_apply X)) input)) subjects"

lemma known_history_family_result_exact:
  "known_history_family_result subjects=digit_history_family_reference subjects"
  by (simp only: known_history_family_result_def digit_history_family_reference_def
    known_history_apply_exact digit_history_apply_exact)

definition known_history_family_method where
  "known_history_family_method (m::nat) subjects=(if m=0 then known_history_family_result subjects
    else digit_history_family_method (m-1) subjects)"

lemma known_history_family_method_original:
  "known_history_family_method m subjects=digit_history_family_method (if m=0 then 0 else m-1) subjects"
proof -
  have original: "digit_history_family_method 0 subjects=digit_history_family_reference subjects"
    by (rule digit_history_correct_methods) simp
  show ?thesis by (simp only: known_history_family_method_def known_history_family_result_exact;
    cases "m=0"; simp add: original)
qed

definition known_history_context where
  "known_history_context subjects=(digit_history_question_context subjects,known_history_family_result subjects)"

definition known_history_assessment where
  "known_history_assessment (m::nat) context=(case context of ((covered,(subjects,prepared,reference)),known) \<Rightarrow>
    if m=0 then (covered,(known,reference))
    else digit_history_question_assessment (m-1) (covered,(subjects,prepared,reference)))"

lemma known_history_assessment_original:
  "known_history_assessment m (known_history_context subjects)=
    digit_history_question_assessment (if m=0 then 0 else m-1) (digit_history_question_context subjects)"
proof -
  have original: "digit_history_prepared_family_method 0 (digit_history_family_prepare subjects)=
    digit_history_family_reference subjects"
    using digit_history_correct_methods[of 0 subjects]
    by (simp only: digit_history_family_method_def; simp)
  show ?thesis by (cases "m=0")
    (simp_all add: known_history_assessment_def known_history_context_def
      digit_history_question_context_def digit_history_context_def Let_def
      digit_history_question_assessment_def digit_history_assessment_def
      known_history_family_result_exact original)
qed

theorem known_history_assessment_exact:
  "digit_history_question_inspect (known_history_assessment m (known_history_context subjects)) f=
    digit_history_question_condition f (known_history_family_method m) subjects"
  by (simp only: known_history_assessment_original digit_history_question_assessment_exact
    known_history_family_method_original[abs_def])

definition known_history_quality where
  "known_history_quality m w f=digit_history_question_inspect
    (known_history_assessment m (known_history_context (digit_history_case w))) f"

lemma known_history_quality_exact:
  "known_history_quality m w f=digit_history_question_condition f (known_history_family_method m) (digit_history_case w)"
  by (simp only: known_history_quality_def known_history_assessment_exact)

interpretation known_history: finite_subject_investigation
    "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]" "[0,1]" ws
    known_history_family_method digit_history_question_condition digit_history_case known_history_quality for ws
  by (unfold_locales) (rule known_history_quality_exact)

definition known_history_investigation where
  "known_history_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] [0,1] ws known_history_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] [0,1] ws known_history_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm known_history_investigation_def},
   equation = @{thm known_history.observations_derived},
   formation = @{thm known_history.maps_formed},
   observation = @{thm known_history.observation_at_subject},
   comparison = @{thm known_history.comparison_at_subject}}\<close>

definition known_history_packet where
  "known_history_packet ws selections=(let table=context_assessment_table
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] ws
      (\<lambda>w. known_history_context (digit_history_case w)) known_history_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] [0,1] ws
      table digit_history_question_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] [0,1]
      (fst compared) (fst (snd compared))) selections))"

text \<open>
  The complete original sixteen subjects and nineteen methods remain present.
  The new constructor-backed step occupies method zero; each old method keeps
  its complete operation at the successor index. The actual closed history
  supplies the predecessor premise. Original transition coverage, full result
  conditions, all omitted-check controls and every revision remain unchanged.
\<close>

end
