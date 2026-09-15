theory Factor_Quoted_History_Investigation
  imports Factor_Digit_History_Policy_Construction Factor_Digit_History_Result_Candidates
    Factor_Quoted_Policy_Attempts
begin

fun quoted_history_apply where
  "quoted_history_apply (q,History_Step l rows E pu pr au ar root R)=
    digit_history_policy_step q l rows E pu pr au ar root R"

definition quoted_history_result where
  "quoted_history_result X=map_option digit_history_view (quoted_history_apply X)"

lemma quoted_history_result_exact:
  "quoted_history_result X=digit_history_reference_option X"
  by (cases X; cases "snd X")
    (simp add: quoted_history_result_def digit_history_policy_step_exact digit_history_apply_exact[symmetric])

definition quoted_history_attempt_only where
  "quoted_history_attempt_only q l rows E pu pr au ar root R=quoted_policy_attempt digit_construct_generation
    (history_header_policy (digit_history_header q)) (history_header_policy_use (digit_history_header q))
    (history_header_entry (digit_history_header q)) (digit_history_material q) l rows E pu pr au ar R"

fun quoted_history_without_replay where
  "quoted_history_without_replay (q,History_Step l rows E pu pr au ar root R)=
    map_option digit_history_state_view (digit_history_step_using quoted_history_attempt_only
      (raw_digit_required_history q) l rows E pu pr au ar root R)"

interpretation quoted_history: digit_history_result_candidates
  "[quoted_history_result,quoted_history_without_replay]" .

lemma quoted_history_methods:
  "quoted_history.methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]"
  by (simp add: quoted_history.methods_def upt_conv_Cons)

definition quoted_history_family_method where
  "quoted_history_family_method=quoted_history.family_method"

definition quoted_history_quality where
  "quoted_history_quality m w f=digit_history_question_inspect
    (quoted_history.assessment m (quoted_history.make_context (digit_history_case w))) f"

lemma quoted_history_quality_exact:
  "quoted_history_quality m w f=digit_history_question_condition f (quoted_history_family_method m) (digit_history_case w)"
  by (simp only: quoted_history_quality_def quoted_history.assessment_exact quoted_history_family_method_def)

interpretation quoted_history_compare: finite_subject_investigation
    "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]" "[0,1]" ws
    quoted_history_family_method digit_history_question_condition digit_history_case quoted_history_quality for ws
  by (unfold_locales) (rule quoted_history_quality_exact)

definition quoted_history_investigation where
  "quoted_history_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] [0,1] ws quoted_history_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20] [0,1] ws quoted_history_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm quoted_history_investigation_def},
   equation = @{thm quoted_history_compare.observations_derived},
   formation = @{thm quoted_history_compare.maps_formed},
   observation = @{thm quoted_history_compare.observation_at_subject},
   comparison = @{thm quoted_history_compare.comparison_at_subject}}\<close>

definition quoted_history_packet where
  "quoted_history_packet=quoted_history.packet"

text \<open>
  The generic additional-producer framework keeps every original history
  method and its exact result condition. The refined closed step and the
  actual policy-aligned attempt without replay supply two new structural
  subjects. The latter remains a raw candidate result; it cannot construct an
  admitted closed history merely by satisfying package or policy alignment.
\<close>

end
