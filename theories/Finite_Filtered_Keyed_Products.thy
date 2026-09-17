theory Finite_Filtered_Keyed_Products
  imports Finite_Relation_Conflicts
begin

definition finite_filtered_keyed_product where
  "finite_filtered_keyed_product condition R S=ffUnion (fimage (\<lambda>(k,a).
    fimage (\<lambda>(l,b). (k,a,b)) (ffilter (\<lambda>(l,b). l=k \<and> condition a b) S)) R)"

theorem finite_filtered_keyed_product_member:
  "(k,a,b) |\<in>| finite_filtered_keyed_product condition R S \<longleftrightarrow>
    (k,a) |\<in>| R \<and> (k,b) |\<in>| S \<and> condition a b"
  by (simp only: finite_filtered_keyed_product_def finite_union_image_member
    finite_image_member ffmember_filter split_paired_Ex case_prod_conv prod.inject; blast)

theorem finite_filtered_keyed_product_exact:
  "finite_filtered_keyed_product condition R S=
    ffilter (\<lambda>(k,a,b). condition a b) (finite_keyed_product R S)"
  by (rule fset_inject[THEN iffD1], rule set_eqI)
    (auto simp: finite_filtered_keyed_product_member finite_keyed_product_member split: prod.splits)

declare finite_relation_conflicts_def[code del]

lemma finite_relation_conflicts_filtered_code [code]:
  "finite_relation_conflicts R=finite_filtered_keyed_product (\<lambda>a b. a\<noteq>b) R R"
  by (simp only: finite_filtered_keyed_product_exact finite_relation_conflicts_def)

text \<open>The original condition is applied before constructing the corresponding
  keyed product value. Complete conflict witnesses remain exactly the original
  relation, including both orientations and every common key. In particular,
  diagonal values that will be discarded do not enter an intermediate finite
  relation and its duplicate checks. This is a whole-result equation, not a
  bound, functionality assumption, or restriction of the observation scope.\<close>

end
