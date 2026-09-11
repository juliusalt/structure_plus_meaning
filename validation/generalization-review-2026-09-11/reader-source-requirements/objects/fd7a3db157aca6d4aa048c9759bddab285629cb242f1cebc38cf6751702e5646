theory Factor_Reader_Source_Requirements
  imports Factor_Source_Shape_Requirements Factor_Inference_Specialization_Clauses
begin

section \<open>The node request retains its necessary environment source\<close>

lemma proof_node_reading_environment:
  assumes admitted: "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system"
  shows "\<exists>E. environment_value_presents E e"
  using proof_node_reading_sound[OF admitted]
  by (simp only: factor_term.inject) blast

theorem proof_node_reading_source_requirement:
  assumes "(94,term_quotation_argument e u r n i k)\<in>positive_meaning proof_node_reading_system"
  shows "environment_outer_shape e"
  using proof_node_reading_environment[OF assms] environment_presentation_outer_shape by blast

lemma inference_specialization_environment:
  assumes admitted: "(350,inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
    \<in>positive_meaning inference_specialization_system"
  shows "\<exists>E. environment_value_presents E e"
proof -
  obtain bs where node: "(94,term_quotation_argument e nu nr
      (data_list_term [Pair_Term du c,bs,ds]) ni nk)\<in>positive_meaning proof_node_reading_system"
    using admitted by (simp only: inference_specialization_at_arguments inference_specialization_calls_def) blast
  show ?thesis by (rule proof_node_reading_environment[OF node])
qed

theorem inference_specialization_source_requirement:
  assumes "(350,inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
    \<in>positive_meaning inference_specialization_system"
  shows "environment_outer_shape e"
  using inference_specialization_environment[OF assms] environment_presentation_outer_shape by blast

corollary inference_specialization_source_obstruction:
  assumes "\<not>finite_environment_outer_shape e"
  shows "(350,inference_specialization_argument (decode_finite_term e) pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
    \<notin>positive_meaning inference_specialization_system"
  using assms inference_specialization_source_requirement
  by (auto simp only: finite_environment_outer_shape_exact)

text \<open>
  These requirements apply to every choice of the remaining source, node,
  report, and support fields. A payload marker in the environment position
  cannot be repaired by a deeper search or additional true native premises.
  Its request must remain outside native admission. Replacing a marker with
  a pair still requires the complete environment and reader contracts.
\<close>

end
