theory Generation_Identity_Maps
  imports Generation_Structures
begin

lemma generation_identity_map_injective:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "map_generation_structure encode G=map_generation_structure encode H \<longleftrightarrow> G=H"
proof -
  have injective: "inj encode" by (auto simp: inj_def each)
  have recover: "map_generation_structure (inv encode) (map_generation_structure encode X)=X" for X
    by (simp add: generation_structure.map_comp comp_def inv_f_f[OF injective]
        generation_structure.map_ident)
  show ?thesis using recover[of G] recover[of H] by metis
qed

text \<open>An injective target representation preserves the entire recursive
  generation and every predecessor. The argument is independent of a chosen
  target carrier and requires no formation or cause-validity assumption.\<close>

end
