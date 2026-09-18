theory Faceted_Native_Questions
  imports Native_Control_Admitted_Selection
begin

definition faceted_native_question where
  "faceted_native_question subjects facets observe = finite_development_question
    (map finite_development_index [0..<length subjects])
    (map (\<lambda>f. filtered_development_indices subjects (\<lambda>s. observe s f)) facets)"

theorem faceted_native_admission:
  assumes question: "faceted_native_question subjects facets observe = Some Q"
    and admission: "native_development_admission Q report = Some accepted"
    and selected: "finite_development_index i \<in> set accepted"
    and facet: "f \<in> set facets"
  shows "i < length subjects \<and> observe (subjects!i) f"
proof -
  have "finite_development_index i \<in>
      set (filtered_development_indices subjects (\<lambda>s. observe s f))"
    by (rule finite_development_original_conditions[OF
      question[unfolded faceted_native_question_def] admission selected])
      (use facet in auto)
  then show ?thesis by (simp only: filtered_development_indices_exact)
qed

theorem faceted_native_choice:
  assumes chosen: "native_admitted_choice subjects
    (faceted_native_question subjects facets observe) report = Some subject"
    and facet: "f \<in> set facets"
  shows "observe subject f"
  by (rule native_admitted_choice_fields[OF chosen])
    (use faceted_native_admission[OF _ _ _ facet] in blast)

end
