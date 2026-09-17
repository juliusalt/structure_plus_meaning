theory RRA_Finite_Embedded_Generation_Records
  imports RRA_Embedded_Generation_Records RRA_Finite_Generation_Encoding RRA_Finite_Embedded_Grafts
begin

definition finite_generation_record_literals where
  "finite_generation_record_literals l p c=
    {|(syntax_branch 0 [4],finite_target_artifact l),(syntax_branch 2 [4],finite_target_artifact p),
      (syntax_branch 3 [4],finite_target_artifact c)|}"

lemma finite_generation_record_literals_exact:
  "map_relation_values decode_finite_object (fset (finite_generation_record_literals l p c))=
    generation_record_literals (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)"
  by (simp add: finite_generation_record_literals_def generation_record_literals_def map_relation_values_def)

definition finite_fresh_generation_predecessor_environment where
  "finite_fresh_generation_predecessor_environment E u l p c as v=
    finite_add_source_bindings (finite_add_artifact_use E u (finite_generation_record_frame l p c as)) u
      (fimage (\<lambda>i. (generation_predecessor_slot i,v i)) (fset_of_list [0..<length as]))"

lemma finite_fresh_generation_predecessor_exact:
  "decode_finite_environment (finite_fresh_generation_predecessor_environment E u l p c as v)=
    fresh_generation_predecessor_environment (decode_finite_environment E) u
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)
      (map (map_prod decode_finite_object id) as) v"
  by (simp add: finite_fresh_generation_predecessor_environment_def
    fresh_generation_predecessor_environment_def finite_generation_record_frame_exact
    fimage.rep_eq fset_of_list.rep_eq atLeast0LessThan)

definition finite_embedded_generation_record_environment where
  "finite_embedded_generation_record_environment h E u l p c as v=
    finite_embedded_graft h (finite_fresh_generation_predecessor_environment E u l p c as v)
      (finite_literal_environment (finite_generation_record_frame l p c as)
        (finite_generation_record_literals l p c))"

theorem finite_embedded_generation_record_exact:
  "decode_finite_environment (finite_embedded_generation_record_environment h E u l p c as v)=
    embedded_generation_record_environment h (decode_finite_environment E) u
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)
      (map (map_prod decode_finite_object id) as) v"
  by (simp add: finite_embedded_generation_record_environment_def embedded_generation_record_environment_def
    finite_embedded_graft_exact finite_fresh_generation_predecessor_exact
    finite_generation_record_frame_exact finite_generation_record_literals_exact)

lemma finite_original_predecessor_instance:
  "finite_generation_record_predecessor_environment E l p c as v=
    finite_fresh_generation_predecessor_environment E (finite_generation_record_use E) l p c as v"
  by (simp only: finite_generation_record_predecessor_environment_def
    finite_fresh_generation_predecessor_environment_def Let_def)

theorem finite_original_embedded_generation_instance:
  "finite_generation_record_environment E l p c as v=
    finite_embedded_generation_record_environment
      (finite_fresh_use_map (finite_environment_uses
        (finite_fresh_generation_predecessor_environment E (finite_generation_record_use E) l p c as v))
        (finite_generation_record_use E))
      E (finite_generation_record_use E) l p c as v"
  by (simp only: finite_generation_record_environment_def finite_original_predecessor_instance
    finite_embedded_generation_record_environment_def finite_generation_record_literals_def
    Let_def finite_original_graft_instance)

text \<open>
  The finite operations preserve the entire original environment and supplied
  embedding, with no restriction to a selected set of observable fields.
  The existing finite constructor is an equal explicit instance. Validity,
  readiness and generation recovery require their separately proved premises.
\<close>

end
