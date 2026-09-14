theory Indexed_Value_Images
  imports Bootstrap_Relations
begin

definition indexed_pair_map where
  "indexed_pair_map f z=(case z of (k,v) \<Rightarrow> (k,f k v))"

lemma indexed_pair_map_pair [simp]:
  "indexed_pair_map f (k,v)=(k,f k v)"
  by (simp only: indexed_pair_map_def case_prod_conv)

definition indexed_value_image where
  "indexed_value_image f R=indexed_pair_map f ` R"

lemma indexed_value_image_member:
  "(k,w)\<in>indexed_value_image f R \<longleftrightarrow> (\<exists>v. (k,v)\<in>R \<and> w=f k v)"
  by (auto simp: indexed_value_image_def indexed_pair_map_def)

lemma indexed_value_image_domain:
  "rel_dom (indexed_value_image f R)=rel_dom R"
  by (auto simp: rel_dom_def indexed_value_image_member)

lemma indexed_value_image_functional:
  assumes "single_valued R"
  shows "single_valued (indexed_value_image f R)"
  using assms by (auto simp: single_valued_def indexed_value_image_member)

lemma indexed_pair_map_injective:
  assumes fibres: "\<And>k. inj_on (f k) {v. (k,v)\<in>A}"
  shows "inj_on (indexed_pair_map f) A"
  using fibres by (auto simp: inj_on_def indexed_pair_map_def; blast)

lemma rel_value_key_image:
  assumes functional: "single_valued R" and injective: "inj_on f (rel_dom R)"
    and key: "k\<in>rel_dom R"
  shows "rel_value (map_prod f id ` R) (f k)=rel_value R k"
proof -
  obtain v where row: "(k,v)\<in>R" using key by (auto simp: rel_dom_def)
  have original: "rel_value R k=v" by (rule rel_value_eq[OF functional row])
  have mapped: "(f k,v)\<in>map_prod f id ` R"
    by (rule rev_image_eqI[OF row]) simp
  have rows: "single_valued (map_prod f id ` R)"
    using single_valued_pair_image[OF functional injective, where g=id] by (simp only: map_prod_def)
  show ?thesis by (simp only: original; rule rel_value_eq[OF rows mapped])
qed

lemma key_image_inverse:
  assumes "inj f"
  shows "map_prod (inv f) id ` (map_prod f id ` R)=R"
  by (simp add: image_image map_prod_def case_prod_unfold inv_f_f[OF assms])

text \<open>
  The original key remains present when its value is transformed in that key's
  context. Complete image membership and domain equations require no
  injectivity. Functional rows remain functional. Injectivity of the complete
  pair map follows from injectivity on each actual key fibre.
\<close>

end
