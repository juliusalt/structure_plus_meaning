theory Finite_Requirement_Artifact_Admission
  imports Factor_Requirement_Artifact_Admission Factor_Finite_Complete_Quotation
    Factor_Finite_Data_Syntax Factor_Requirement_Result_Values
begin

definition finite_requirement_artifact_admitted ::
  "nat set \<Rightarrow> admission_goal list \<Rightarrow> nat \<Rightarrow> finite_exact_artifact \<Rightarrow> bool" where
  "finite_requirement_artifact_admitted D gs n C=(case checked_admission_sequence D gs n of
    None \<Rightarrow> False | Some plan \<Rightarrow>
      finite_complete_data_roots C (finite_admission_sequence_value gs n plan)\<noteq>{||})"

lemma finite_complete_data_roots_nonempty:
  "finite_complete_data_roots C t\<noteq>{||} \<longleftrightarrow>
    (\<exists>r. complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t))"
proof -
  have nonempty: "A\<noteq>{||} \<longleftrightarrow> (\<exists>a. a |\<in>| A)" for A :: "local_address fset"
    by (transfer) blast
  show ?thesis by (simp only: nonempty finite_complete_data_roots_exact)
qed

theorem finite_requirement_artifact_correct:
  "finite_requirement_artifact_admitted D gs n C \<longleftrightarrow>
    requirement_artifact_admitted D gs n (decode_finite_object C)"
  by (cases "checked_admission_sequence D gs n")
    (auto simp: finite_requirement_artifact_admitted_def requirement_artifact_admitted_def
      finite_complete_data_roots_nonempty split: prod.splits)

theorem finite_requirement_artifact_native:
  assumes "finite D"
  shows "finite_requirement_artifact_admitted D gs n C \<longleftrightarrow>
    (369,Target_Term (Whole_Artifact (decode_finite_object C)))
      \<in>positive_meaning (requirement_artifact_system D gs n)"
  by (simp only: finite_requirement_artifact_correct requirement_artifact_at_literal[OF assms])

theorem finite_requirement_artifact_original_source:
  assumes "schema_system_formed P"
  shows "finite_requirement_artifact_admitted (system_definitions P) gs n C \<longleftrightarrow>
    (369,Target_Term (Whole_Artifact (decode_finite_object C)))
      \<in>positive_meaning (requirement_artifact_system (system_definitions P) gs n)"
  by (rule finite_requirement_artifact_native[OF system_definitions_finite[OF assms]])

definition finite_requirement_candidate ::
  "admission_goal list \<Rightarrow> nat \<Rightarrow> nat list\<times>(nat\<times>admission_instruction list)
    \<Rightarrow> finite_exact_artifact" where
  "finite_requirement_candidate gs n plan=the (finite_data_syntax (admission_sequence_value gs n plan))"

lemma finite_requirement_candidate_built:
  "finite_data_syntax (admission_sequence_value gs n plan)=Some (finite_requirement_candidate gs n plan)"
  unfolding finite_requirement_candidate_def
  using finite_data_syntax_domain[of "admission_sequence_value gs n plan"]
  by (cases "finite_data_syntax (admission_sequence_value gs n plan)") auto

lemma finite_requirement_candidate_quote:
  "complete_data_quoted_at (decode_finite_object (finite_requirement_candidate gs n plan)) []
    (admission_sequence_value gs n plan)"
  by (rule finite_data_syntax_complete_quotation[OF admission_sequence_value_formed
    finite_requirement_candidate_built])

theorem finite_requirement_candidate_exact:
  assumes "finite D"
  shows "finite_requirement_artifact_admitted D gs n (finite_requirement_candidate hs m plan) \<longleftrightarrow>
    hs=gs \<and> m=n \<and> checked_admission_sequence D gs n=Some plan"
proof -
  obtain ds k cs where plan: "plan=(ds,k,cs)" by (cases plan) auto
  have quoted: "complete_data_quoted_at (decode_finite_object (finite_requirement_candidate hs m plan)) []
      (admission_plan_argument (data_list_term (map admission_goal_value hs)) (admission_counter m)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"
    using finite_requirement_candidate_quote[where gs=hs and n=m and plan=plan] by (simp only: plan admission_sequence_value.simps)
  have decision: "requirement_artifact_admitted D gs n
      (decode_finite_object (finite_requirement_candidate hs m plan)) \<longleftrightarrow>
      hs=gs \<and> m=n \<and> checked_admission_sequence D gs n=Some (ds,k,cs)"
    by (rule requirement_artifact_on_complete_body[OF assms quoted])
  show ?thesis using decision by (simp only: finite_requirement_artifact_correct plan)
qed

export_code finite_requirement_artifact_admitted finite_requirement_candidate checking SML

text \<open>
  The expected body is generated from the original request by the checked
  constructor. The candidate is a complete independent finite artifact. The
  existing quotation reader compares that artifact's actual whole body with
  the generated expectation. Its all-input equation is the native artifact
  admission predicate, with the complete original program domain when used
  for a source program.
\<close>

end
