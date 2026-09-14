theory RRA_Finite_Generation_Reference_Construction
  imports RRA_Finite_Generation_Construction RRA_Finite_Generation_References
    RRA_Generation_Record_References
begin

context finite_generation_record_construction
begin

theorem original_references:
  "finite_generation_predecessor_references F u [] l p c=fset_of_list (map fst rows)"
proof -
  let ?as="map (map_prod decode_finite_object id) as"
  have coordinate: "(v i,snd (?as!i))=fst (rows!i)" if "i<length rows" for i
  proof -
    have bound: "i<length anchors" using that lengths by simp
    show ?thesis using at[OF bound] bound
      by (simp add: map_map comp_def map_prod_def split_def)
  qed
  have shape: "generation_predecessor_references (decode_finite_environment F) u []
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)=
    {(v i,snd (?as!i)) | i. i<length ?as}"
    using native.predecessor_references by (simp only: environment record_use)
  have sites: "{(v i,snd (?as!i)) | i. i<length ?as}=set (map fst rows)"
    by (simp only: length_map lengths set_conv_nth;
      simp only: coordinate nth_map cong: rev_conj_cong)
  show ?thesis by (simp only: fset_inject[symmetric] finite_generation_predecessor_references_correct
    shape sites fset_of_list.rep_eq)
qed

end

theorem finite_construct_generation_record_original_references:
  assumes result: "finite_construct_generation_record E l p c rows=Some (F,u,G)"
  shows "finite_generation_predecessor_references F u [] l p c=fset_of_list (map fst rows)"
proof -
  have ready: "finite_generation_record_ready E l p c rows"
    by (rule finite_construct_generation_record_correct(1)[OF result])
  obtain anchors where queried: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
    and body: "finite_generation_record_body E l p c rows anchors=(F,u,G)"
    using result ready by (auto simp: finite_construct_generation_record_def split: option.splits)
  interpret construction: finite_generation_record_construction E l p c rows anchors
    by (rule finite_generation_record_construction.intro[OF ready queried])
  show ?thesis using construction.original_references body
    by (auto simp: finite_generation_record_body_def)
qed

end
