theory Native_Control_Context_Selection
  imports Native_Control_Context_Contract Finite_Term_Words
begin

lemma changed_context_input_facet:
  assumes same_entities: "snd C=snd D" and different_contexts: "C\<noteq>D"
  shows "context_input_facet C D=[finite_development_index 1]"
  using assms
  by (simp add: context_input_facet_def context_input_projections_def
    context_input_observation_def inj_eq[OF isabelle_context_data_injective]
    upt_conv_Cons)

theorem admitted_changed_context_input:
  assumes same_entities: "snd C=snd D" and different_contexts: "C\<noteq>D"
    and question: "context_input_question C D=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
  shows "set accepted\<subseteq>{finite_development_index 1}"
proof
  fix v assume selected: "v\<in>set accepted"
  have "v\<in>set (context_input_facet C D)"
    by (rule finite_development_original_conditions[OF
      question[unfolded context_input_question_def] admission selected]) simp
  then show "v\<in>{finite_development_index 1}"
    by (simp only: changed_context_input_facet[OF same_entities different_contexts]) simp
qed

text \<open>Generated occurrence coordinates are not input projection indices.
  The admitted value is mapped by its exact presentation, independently of where
  native generation places it. This theorem still states no provenance or truth
  judgment and does not strengthen the original two-context condition.\<close>

value [code] "map (\<lambda>i. (i,finite_term_shared_word_fold
  (\<lambda>xs b. xs@[b]) (finite_development_index i) [])) [0,1]"

end
