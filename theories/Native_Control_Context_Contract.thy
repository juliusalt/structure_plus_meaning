theory Native_Control_Context_Contract
  imports Isabelle_Acceptance Factor_Steered_Development
begin

section \<open>A reused input must preserve every distinction its consumer requires\<close>

lemma two_subject_factorization:
  "(\<exists>recover. recover (project x)=observe x \<and>
      recover (project y)=observe y) \<longleftrightarrow>
    (project x=project y \<longrightarrow> observe x=observe y)"
proof
  assume "\<exists>recover. recover (project x)=observe x \<and>
      recover (project y)=observe y"
  then show "project x=project y \<longrightarrow> observe x=observe y" by metis
next
  assume preserves: "project x=project y \<longrightarrow> observe x=observe y"
  show "\<exists>recover. recover (project x)=observe x \<and>
      recover (project y)=observe y"
    by (rule exI[of _ "\<lambda>z. if z=project x then observe x else observe y"])
      (use preserves in auto)
qed

datatype context_input_projection = Entity_Input | Context_Input

fun context_input_value :: "context_input_projection \<Rightarrow> isabelle_context \<Rightarrow> finite_factor_term" where
  "context_input_value Entity_Input C=finite_sequence_presentation isabelle_entity_data (snd C)"
| "context_input_value Context_Input C=isabelle_context_data C"

definition context_input_condition ::
    "context_input_projection \<Rightarrow> isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> bool" where
  "context_input_condition projection C D \<longleftrightarrow>
    (\<exists>recover. recover (context_input_value projection C)=C \<and>
      recover (context_input_value projection D)=D)"

definition context_input_observation where
  "context_input_observation projection C D=
    (context_input_value projection C\<noteq>context_input_value projection D \<or> C=D)"

theorem context_input_observation_exact:
  "context_input_observation projection C D=context_input_condition projection C D"
  using two_subject_factorization[where project="context_input_value projection"
    and x=C and y=D and observe=id]
  by (simp add: context_input_observation_def context_input_condition_def)

lemma complete_context_input_preserves:
  "context_input_condition Context_Input C D"
  using two_subject_factorization[where project="context_input_value Context_Input"
    and x=C and y=D and observe=id]
  by (simp add: context_input_condition_def inj_eq[OF isabelle_context_data_injective])

lemma entity_input_loses_context:
  assumes "snd C=snd D" "C\<noteq>D"
  shows "\<not> context_input_condition Entity_Input C D"
  using assms by (simp add: context_input_condition_def two_subject_factorization)

lemma entity_acceptance_ignores_table:
  "isabelle_demand_acceptance (snd (names,es)) demands=
    isabelle_demand_acceptance (snd (other_names,es)) demands"
  by simp

definition context_input_projections where
  "context_input_projections=[Entity_Input,Context_Input]"

definition context_input_values where
  "context_input_values=map finite_development_index [0..<length context_input_projections]"

definition context_input_facet where
  "context_input_facet C D=map finite_development_index
    (filter (\<lambda>i. context_input_observation (context_input_projections!i) C D)
      [0..<length context_input_projections])"

lemma context_input_facet_exact:
  assumes "i<length context_input_projections"
  shows "finite_development_index i\<in>set (context_input_facet C D) \<longleftrightarrow>
    context_input_condition (context_input_projections!i) C D"
  using assms by (auto simp: context_input_facet_def context_input_observation_exact)

definition context_input_question where
  "context_input_question C D=finite_development_question context_input_values [context_input_facet C D]"

theorem context_input_admission_original_condition:
  assumes question: "context_input_question C D=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and chosen: "finite_development_index i\<in>set accepted"
    and index: "i<length context_input_projections"
  shows "context_input_condition (context_input_projections!i) C D"
proof -
  have member: "finite_development_index i\<in>set (context_input_facet C D)"
    by (rule finite_development_original_conditions[OF
      question[unfolded context_input_question_def] admission chosen]) simp
  show ?thesis using member by (simp only: context_input_facet_exact[OF index])
qed

definition context_input_questions where
  "context_input_questions C D=List.map_filter id
    [context_input_question C C,context_input_question C D]"

definition context_input_review where
  "context_input_review C D=(C,D,context_input_projections,
    map (\<lambda>p. (context_input_observation p C C,context_input_observation p C D))
      context_input_projections,
    map native_development_packet (context_input_questions C D),
    native_steered_development (context_input_questions C D) (context_input_questions C D))"

text \<open>
  This bootstrap investigation has one independently stated requirement: the input
  must retain the exact context distinction needed by the receiving judgment. Its
  candidates are actual existing presentation operations. The facet is computed
  from their values and its equation is proved above; no satisfaction table is an
  input. The complete original contexts are retained by context_input_review.
  The repeated self-pair permits both projections; the changed-context pair can
  distinguish them. Neither observation establishes provenance, the truth of an
  encoded proposition, a refinement request, or the adequacy of this scope for
  any condition beyond exact recovery of these two contexts.
\<close>

end
