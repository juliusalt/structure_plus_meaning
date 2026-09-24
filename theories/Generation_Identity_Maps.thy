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

text \<open>
  A representation need not be injective everywhere: two generations are equal exactly when their
  maps are, as soon as the map is injective on the targets that occur in the two, and a map injective
  on a set of targets is injective on every family of generations whose targets lie in that set.
\<close>

lemma generation_identity_map_injective_on:
  assumes each: "inj_on encode (set_generation_structure G\<union>set_generation_structure H)"
  shows "map_generation_structure encode G=map_generation_structure encode H \<longleftrightarrow> G=H"
proof -
  let ?A="set_generation_structure G\<union>set_generation_structure H"
  have recover: "map_generation_structure (inv_into ?A encode) (map_generation_structure encode X)=X"
    if within: "set_generation_structure X\<subseteq>?A" for X
  proof -
    have "map_generation_structure (inv_into ?A encode) (map_generation_structure encode X)=
        map_generation_structure (inv_into ?A encode \<circ> encode) X"
      by (simp add: generation_structure.map_comp)
    also have "\<dots>=map_generation_structure id X"
    proof (rule generation_structure.map_cong0)
      fix z
      assume "z\<in>set_generation_structure X"
      then have "z\<in>?A" using within by blast
      then show "(inv_into ?A encode \<circ> encode) z=id z" by (simp add: inv_into_f_f[OF each])
    qed
    also have "\<dots>=X" by (simp add: generation_structure.map_id)
    finally show ?thesis .
  qed
  have "map_generation_structure (inv_into ?A encode) (map_generation_structure encode G)=G"
    by (rule recover) blast
  moreover have "map_generation_structure (inv_into ?A encode) (map_generation_structure encode H)=H"
    by (rule recover) blast
  ultimately show ?thesis by metis
qed

lemma generation_identity_map_inj_on:
  assumes each: "inj_on encode K" and within: "\<And>G. G\<in>X \<Longrightarrow> set_generation_structure G\<subseteq>K"
  shows "inj_on (map_generation_structure encode) X"
proof (rule inj_onI)
  fix G H
  assume "G\<in>X" "H\<in>X" and same: "map_generation_structure encode G=map_generation_structure encode H"
  then have "inj_on encode (set_generation_structure G\<union>set_generation_structure H)"
    using each within by (blast intro: inj_on_subset)
  then show "G=H" using same generation_identity_map_injective_on by blast
qed

text \<open>An injective target representation preserves the entire recursive
  generation and every predecessor. The argument is independent of a chosen
  target carrier and requires no formation or cause-validity assumption.\<close>

end
