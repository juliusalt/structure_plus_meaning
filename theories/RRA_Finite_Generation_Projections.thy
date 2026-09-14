theory RRA_Finite_Generation_Projections
  imports RRA_Finite_Generations Finite_Set_Composition
begin

lemma decode_finite_generation_inj: "inj decode_finite_generation"
  by (simp add: inj_def)

lemma decode_finite_generation_selectors:
  "generation_locus (decode_finite_generation G)=decode_finite_target (generation_locus G)"
  "generation_predecessors (decode_finite_generation G)=fimage decode_finite_generation (generation_predecessors G)"
  "generation_payload (decode_finite_generation G)=decode_finite_target (generation_payload G)"
  "generation_cause (decode_finite_generation G)=decode_finite_target (generation_cause G)"
  by (cases G; simp add: decode_finite_generation_node)+

end
