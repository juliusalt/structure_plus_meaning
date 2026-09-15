theory RRA_Selected_Generation_Predecessors
  imports RRA_Finite_Generation_Construction
begin

context finite_generation_record_construction
begin

abbreviation decoded_anchors where "decoded_anchors\<equiv>map (map_prod decode_finite_object id) as"
abbreviation decoded_predecessor where "decoded_predecessor\<equiv>\<lambda>i. decode_finite_generation (snd (rows!i))"

lemma selected_generation_coordinate:
  assumes index: "i<length anchors"
  shows "(v i,snd (decoded_anchors!i))=fst (rows!i)"
  using at[OF index] index by (simp add: map_map comp_def map_prod_def split_def)

lemma selected_generation_injective:
  "inj_on decoded_predecessor {..<length decoded_anchors}"
proof -
  have different: "distinct (map snd rows)" using ready by (simp only: finite_generation_record_ready_def; blast)
  have decoded: "distinct (map decode_finite_generation (map snd rows))"
    using different by (auto simp: distinct_map inj_on_def)
  have indexed: "inj_on (\<lambda>i. (map decode_finite_generation (map snd rows))!i) {..<length rows}"
    by (rule inj_on_nth[OF decoded]) simp
  show ?thesis using indexed by (auto simp: inj_on_def lengths)
qed

lemma selected_generation_readings:
  "\<forall>i<length decoded_anchors.
    generation_at (decode_finite_environment E) (v i) (snd (decoded_anchors!i)) (decoded_predecessor i)"
proof (intro allI impI)
  fix i assume index: "i<length decoded_anchors"
  have bound: "i<length anchors" and original: "i<length rows" using index lengths by simp_all
  have checked: "finite_check_generation (snd (rows!i)) E (fst (fst (rows!i))) (snd (fst (rows!i)))"
    using ready nth_mem[OF original]
    by (cases "rows!i") (auto simp: finite_generation_record_ready_def list_all_iff)
  show "generation_at (decode_finite_environment E) (v i) (snd (decoded_anchors!i)) (decoded_predecessor i)"
    using checked at[OF bound] bound original
    by (simp add: finite_check_generation_exact map_map comp_def map_prod_def split_def)
qed

lemma selected_generation_values:
  "decoded_predecessor ` {..<length decoded_anchors}=
    fset (fimage decode_finite_generation (fset_of_list (map snd rows)))"
  by (auto simp: lengths fimage.rep_eq fset_of_list.rep_eq set_conv_nth)

lemma selected_generation_sites:
  "{(v i,snd (decoded_anchors!i)) | i. i<length decoded_anchors}=set (map fst rows)"
  by (simp only: length_map lengths set_conv_nth;
    simp only: selected_generation_coordinate[unfolded lengths] nth_map cong: rev_conj_cong)

end

text \<open>
  The existing complete readiness and queried-anchor contract supplies one
  injective decoded predecessor assignment, its exact readings and its original
  sites. Later installations instantiate these facts without redoing the
  list-to-family or cited-coordinate argument.
\<close>

end
