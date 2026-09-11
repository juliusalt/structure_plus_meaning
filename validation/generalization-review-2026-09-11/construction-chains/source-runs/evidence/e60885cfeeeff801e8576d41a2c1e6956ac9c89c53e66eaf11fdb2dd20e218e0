theory Factor_Binding_Observation_Recovery
  imports Factor_Binding_Observation_Contracts Factor_Paired_List_Relations
begin

section \<open>The two complete row observations determine their common input\<close>

lemma binding_observation_rows_determine:
  assumes first: "binding_observation_row True u a x" "binding_observation_row False u a y"
    and second: "binding_observation_row True u b x" "binding_observation_row False u b y"
  shows "a=b"
  using assms by (auto simp: binding_observation_row_def)

theorem binding_observation_input_unique:
  assumes first: "(347,binding_observation_argument u a x y)\<in>positive_meaning binding_observation_program"
    and second: "(347,binding_observation_argument u b x y)\<in>positive_meaning binding_observation_program"
  shows "a=b"
proof -
  obtain as xs ys where left: "a=data_list_term as" "x=data_list_term xs" "y=data_list_term ys"
    "list_all2 (binding_observation_row True u) as xs"
    "list_all2 (binding_observation_row False u) as ys"
    using first by (simp only: binding_observation_exact binding_observation_result_def factor_term.inject) blast
  obtain bs where right: "b=data_list_term bs"
    "list_all2 (binding_observation_row True u) bs xs"
    "list_all2 (binding_observation_row False u) bs ys"
    using second by (simp only: binding_observation_exact binding_observation_result_def
      factor_term.inject left(2,3) data_list_term_injective) blast
  have same: "as=bs"
    by (rule paired_list_relations_determine[OF binding_observation_rows_determine left(4,5) right(2,3)])
  show ?thesis by (simp only: left(1) right(1) same)
qed

theorem binding_observation_at_pattern_rows:
  assumes owner_formed: "term_formed (use_data_term u)"
    and source: "\<forall>a\<in>set As. octets_formed a \<and> pattern_formed (s a)"
    and variables: "\<forall>a\<in>set As. \<forall>b\<in>pattern_variables (s a). octets_formed b"
  shows "(347,binding_observation_argument (use_data_term u) bs
      (binding_rows_term (map (\<lambda>a. (a,evaluate_pattern Payload_Term (s a))) As))
      (binding_rows_term (map (\<lambda>a. (a,evaluate_pattern
        (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) (s a))) As)))
      \<in>positive_meaning binding_observation_program \<longleftrightarrow>
    bs=positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)"
  using binding_observation_pattern_rows[OF assms] binding_observation_input_unique
  by blast

text \<open>
  This inverse keeps the original row order. It uses observations of supplied
  actual patterns; it does not assert that arbitrary paired values are pattern
  observations. The surrounding record reader supplies that missing source.
\<close>

end
