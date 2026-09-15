theory Factor_Constructed_History_Investigation
  imports Factor_Digit_History_Constructed_Steps Factor_Known_History_Investigation
    Factor_Quoted_History_Investigation
begin

fun constructed_history_apply where
  "constructed_history_apply (q,History_Step l rows E pu pr au ar root R)=
    digit_history_constructed_step q l rows E pu pr au ar root R"

definition constructed_history_result where
  "constructed_history_result X=map_option digit_history_view (constructed_history_apply X)"

lemma constructed_history_result_exact:
  "constructed_history_result X=digit_history_reference_option X"
  by (cases X; cases "snd X")
    (simp add: constructed_history_result_def digit_history_constructed_step_exact digit_history_apply_exact[symmetric])

definition known_predecessor_history_result where
  "known_predecessor_history_result X=map_option digit_history_view (known_history_apply X)"

fun constructed_history_without_membership where
  "constructed_history_without_membership (q,History_Step l rows E pu pr au ar root R)=
    map_option (\<lambda>(A,u,G). digit_history_state_view
      (digit_history_append_state (raw_digit_required_history q) A u G))
      (digit_history_constructed_attempt (raw_digit_required_history q) l rows E pu pr au ar root R)"

interpretation constructed_history: digit_history_result_candidates
  "[constructed_history_result,known_predecessor_history_result,quoted_history_result,
    constructed_history_without_membership]" .

lemma constructed_history_methods:
  "constructed_history.methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]"
  by (simp add: constructed_history.methods_def upt_conv_Cons)

definition constructed_history_family_method where
  "constructed_history_family_method=constructed_history.family_method"

definition constructed_history_quality where
  "constructed_history_quality m w f=digit_history_question_inspect
    (constructed_history.assessment m (constructed_history.make_context (digit_history_case w))) f"

lemma constructed_history_quality_exact:
  "constructed_history_quality m w f=
    digit_history_question_condition f (constructed_history_family_method m) (digit_history_case w)"
  by (simp only: constructed_history_quality_def constructed_history.assessment_exact
    constructed_history_family_method_def)

interpretation constructed_history_compare: finite_subject_investigation
    "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]" "[0,1]" ws
    constructed_history_family_method digit_history_question_condition digit_history_case
    constructed_history_quality for ws
  by (unfold_locales) (rule constructed_history_quality_exact)

definition constructed_history_investigation where
  "constructed_history_investigation ws selected=investigation_basis
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
      [0,1] ws constructed_history_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
      [0,1] ws constructed_history_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm constructed_history_investigation_def},
   equation = @{thm constructed_history_compare.observations_derived},
   formation = @{thm constructed_history_compare.maps_formed},
   observation = @{thm constructed_history_compare.observation_at_subject},
   comparison = @{thm constructed_history_compare.comparison_at_subject}}\<close>

definition constructed_history_packet where
  "constructed_history_packet=constructed_history.packet"

text \<open>
  The composite operation, both preceding refinements and an actual omitted
  membership control instantiate the existing additional-producer framework.
  All nineteen original methods, sixteen original subjects, complete reference
  results and coverage requirements remain present. No producer correctness
  assumption supplies an observation. The omitted guard produces only raw
  candidate results, never an admitted closed history.
\<close>

end
