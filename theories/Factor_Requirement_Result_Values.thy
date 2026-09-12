theory Factor_Requirement_Result_Values
  imports Factor_Requirement_Plan_Realization Factor_Executable_Data_Values
begin

lemma admission_goal_value_self_contained [simp]:
  "self_contained_term (admission_goal_value g)"
  by (induction g) auto

fun admission_sequence_value :: "admission_goal list \<Rightarrow> nat \<Rightarrow>
    nat list\<times>(nat\<times>admission_instruction list) \<Rightarrow> factor_term" where
  "admission_sequence_value gs n (ds,k,cs)=
    admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs))"

lemma admission_sequence_value_formed [simp]: "term_formed (admission_sequence_value gs n plan)"
  by (cases plan; cases "snd plan") (auto simp: data_list_term_formed octets_formed_def)

lemma admission_sequence_value_self_contained [simp]: "self_contained_term (admission_sequence_value gs n plan)"
  by (cases plan; cases "snd plan") (auto simp: data_list_term_self_contained)

definition finite_admission_sequence_value where
  "finite_admission_sequence_value gs n plan=the (finite_self_contained_term (admission_sequence_value gs n plan))"

lemma decode_finite_admission_sequence_value [simp]:
  "decode_finite_term (finite_admission_sequence_value gs n plan)=admission_sequence_value gs n plan"
  unfolding finite_admission_sequence_value_def
  by (rule decode_finite_self_contained_term) simp

export_code admission_sequence_value finite_admission_sequence_value checking SML

end
