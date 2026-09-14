theory RRA_Finite_Generation_Encoding
  imports RRA_Generation_Record_Construction RRA_Finite_Syntax_Construction
    RRA_Finite_Environment_Construction
begin

definition finite_generation_predecessor_frame where
  "finite_generation_predecessor_frame as=finite_family_wrapper
    (finite_syntax_forest (map (\<lambda>(R,a). finite_literal_syntax (Finite_Anchor R a)) as)) []
    (fset_of_list (zip (family_ports (length as)) (map (\<lambda>i. syntax_branch i []) [0..<length as])))"

definition finite_generation_record_frame where
  "finite_generation_record_frame l p c as=finite_record_wrapper
    (finite_syntax_forest [finite_literal_syntax l,finite_generation_predecessor_frame as,
      finite_literal_syntax p,finite_literal_syntax c]) [] (family_ports 4)
    (map (\<lambda>i. syntax_branch i []) [0..<4])"

lemma finite_generation_record_frame_exact:
  "decode_finite_object (finite_generation_record_frame l p c as)=
    generation_record_frame (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)
      (map (map_prod decode_finite_object id) as)"
  by (simp add: finite_generation_record_frame_def finite_generation_predecessor_frame_def
    generation_record_frame_def map_map comp_def map_prod_def split_def fset_of_list.rep_eq
    eval_nat_numeral external_occurrence_syntax_def)

definition finite_generation_record_use where
  "finite_generation_record_use E=finite_fresh_use_map (finite_environment_uses E) None (Some [])"

lemma finite_generation_record_use_exact:
  "finite_generation_record_use E=generation_record_use (decode_finite_environment E)"
  by (simp only: finite_generation_record_use_def finite_fresh_use_map_exact
    finite_environment_uses_correct generation_record_use_def)

definition finite_generation_record_predecessor_environment where
  "finite_generation_record_predecessor_environment E l p c as v=(let
    u=finite_generation_record_use E; R=finite_generation_record_frame l p c as
    in finite_add_source_bindings (finite_add_artifact_use E u R) u
      (fimage (\<lambda>i. (generation_predecessor_slot i,v i)) (fset_of_list [0..<length as])))"

lemma finite_generation_record_predecessor_environment_exact:
  "decode_finite_environment (finite_generation_record_predecessor_environment E l p c as v)=
    generation_record_predecessor_environment (decode_finite_environment E)
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)
      (map (map_prod decode_finite_object id) as) v"
  by (simp add: finite_generation_record_predecessor_environment_def
    generation_record_predecessor_environment_def finite_generation_record_use_exact
    finite_generation_record_frame_exact Let_def fimage.rep_eq fset_of_list.rep_eq atLeast0LessThan)

definition finite_generation_record_environment where
  "finite_generation_record_environment E l p c as v=(let
    F=finite_generation_record_predecessor_environment E l p c as v;
    u=finite_generation_record_use E; R=finite_generation_record_frame l p c as
    in finite_graft_environment F u (finite_literal_environment R
      {|(syntax_branch 0 [4],finite_target_artifact l),(syntax_branch 2 [4],finite_target_artifact p),
        (syntax_branch 3 [4],finite_target_artifact c)|}))"

theorem finite_generation_record_environment_exact:
  "decode_finite_environment (finite_generation_record_environment E l p c as v)=
    generation_record_environment (decode_finite_environment E)
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)
      (map (map_prod decode_finite_object id) as) v"
  by (simp add: finite_generation_record_environment_def generation_record_environment_def
    finite_generation_record_predecessor_environment_exact finite_generation_record_use_exact
    finite_generation_record_frame_exact Let_def map_relation_values_def)

export_code finite_generation_record_frame finite_generation_record_use
  finite_generation_record_environment checking SML

text \<open>
  The executable frame and environment decode to the complete existing RRA
  construction. Each predecessor slot targets the supplied existing use;
  the locus, payload and cause keep their full literal targets. The equality
  retains every artifact and binding. Original formation and anchor premises
  are required before using the constructor's recovery theorem.
\<close>

end
