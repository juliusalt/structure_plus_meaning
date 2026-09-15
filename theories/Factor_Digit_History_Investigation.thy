theory Factor_Digit_History_Investigation
  imports Factor_Digit_History_Cases Finite_Optional_Relation_Predicates
begin

definition digit_history_covered where
  "digit_history_covered=fBex (digit_history_case 0) (\<lambda>(key,input).
    case input of None \<Rightarrow> False | Some X \<Rightarrow> digit_history_reference_option X\<noteq>None)"

lemma digit_history_covered_exact:
  "digit_history_covered \<longleftrightarrow>
    (\<exists>key X following. (key,Some X) |\<in>| digit_history_case 0 \<and> digit_history_transition X following)"
  by (simp only: digit_history_covered_def finite_optional_relation_exists not_None_eq digit_history_reference_exact; blast)

definition digit_history_question_condition where
  "digit_history_question_condition f method subjects=(
    (\<exists>key X following. (key,Some X) |\<in>| digit_history_case 0 \<and> digit_history_transition X following) \<and>
    digit_history_family_condition f method subjects)"

definition digit_history_question_context where
  "digit_history_question_context subjects=(digit_history_covered,digit_history_context subjects)"

definition digit_history_question_assessment where
  "digit_history_question_assessment m context=(fst context,digit_history_assessment m (snd context))"

definition digit_history_question_inspect where
  "digit_history_question_inspect assessment f=(fst assessment \<and> digit_history_inspect (snd assessment) f)"

lemma digit_history_question_assessment_exact:
  "digit_history_question_inspect
      (digit_history_question_assessment m (digit_history_question_context subjects)) f=
    digit_history_question_condition f (digit_history_family_method m) subjects"
  by (simp only: digit_history_question_inspect_def digit_history_question_assessment_def digit_history_question_context_def
    fst_conv snd_conv digit_history_assessment_exact digit_history_covered_exact digit_history_question_condition_def)

definition digit_history_quality where
  "digit_history_quality m w f=digit_history_question_inspect
    (digit_history_question_assessment m (digit_history_question_context (digit_history_case w))) f"

lemma digit_history_quality_exact:
  "digit_history_quality m w f=digit_history_question_condition f (digit_history_family_method m) (digit_history_case w)"
  by (simp only: digit_history_quality_def digit_history_question_assessment_exact)

interpretation digit_history: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]" "[0,1]" ws
    digit_history_family_method digit_history_question_condition digit_history_case digit_history_quality for ws
  by (unfold_locales) (rule digit_history_quality_exact)

definition digit_history_investigation where
  "digit_history_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] [0,1] ws digit_history_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] [0,1] ws digit_history_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm digit_history_investigation_def},
   equation = @{thm digit_history.observations_derived},
   formation = @{thm digit_history.maps_formed},
   observation = @{thm digit_history.observation_at_subject},
   comparison = @{thm digit_history.comparison_at_subject}}\<close>

definition digit_history_packet where
  "digit_history_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws
      (\<lambda>w. digit_history_question_context (digit_history_case w)) digit_history_question_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] [0,1] ws table digit_history_question_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition digit_history_source_scope :: "nat list\<Rightarrow>nat list" where
  "digit_history_source_scope ws=ws"

definition digit_history_source_cases where
  "digit_history_source_cases ws=map (\<lambda>w.
    (w,required_history_case (digit_history_source_index w),bounded_history_case w)) ws"

text \<open>
  Coverage requires an actual successful original bounded history transition.
  Missing fixtures cannot establish adequacy. Every candidate observation is
  derived from complete actual inputs and results under the registered original
  transition and whole-family contracts.
\<close>

end
