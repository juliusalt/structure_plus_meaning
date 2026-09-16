theory Finite_Presented_Assessments
  imports Finite_Presented_Investigations
begin

definition assessment_truth_rows ::
  "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow>
    (nat\<times>'c\<times>(nat\<times>'a) list) list \<Rightarrow>
    (nat\<times>(nat\<times>(nat\<times>bool) list) list) list" where
  "assessment_truth_rows inspect fs table=map (\<lambda>(w,C,cells).
    (w,map (\<lambda>(m,A). (m,map (\<lambda>f. (f,inspect A f)) fs)) cells)) table"

lemma assessment_truth_rows_at:
  assumes "i<length table" "table!i=(w,C,cells)"
  shows "assessment_truth_rows inspect fs table!i=
    (w,map (\<lambda>(m,A). (m,map (\<lambda>f. (f,inspect A f)) fs)) cells)"
  using assms by (simp add: assessment_truth_rows_def)

definition finite_assessment_truth_value where
  "finite_assessment_truth_value=finite_sequence_presentation
    (finite_pair_presentation finite_natural_data
      (finite_sequence_presentation (finite_pair_presentation finite_natural_data
        (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_boolean_data)))))"

lemma finite_assessment_truth_value_injective [intro]: "inj finite_assessment_truth_value"
  unfolding finite_assessment_truth_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
      finite_natural_data_injective finite_boolean_data_injective)

text \<open>
  Every truth value is computed by the given inspection operation on the actual
  assessment in the original table. Subject, candidate and facet occurrences
  retain their order and multiplicity. A condition claim additionally requires
  that inspector's original-subject equation; this generic table supplies no
  satisfaction premise or semantic authority of its own.
\<close>

end
