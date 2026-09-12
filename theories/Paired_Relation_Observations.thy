theory Paired_Relation_Observations
  imports Bootstrap_Relations
begin

section \<open>Two observations of one functional reference retain the same value\<close>

lemma paired_observations_prefixed_injective:
  assumes "inj (\<lambda>v. (f v,g v))"
  shows "inj (\<lambda>q. (map_prod id f q,map_prod id g q))"
  using assms by (auto simp: inj_def map_prod_def split: prod.splits; blast)

lemma single_valued_paired_observations:
  assumes "single_valued R"
  shows "(k,(x,y))\<in>map_relation_values (\<lambda>v. (f v,g v)) R \<longleftrightarrow>
    (k,x)\<in>map_relation_values f R \<and> (k,y)\<in>map_relation_values g R"
  using assms by (auto simp: single_valued_def; blast)

theorem functional_reference_observations_exact:
  assumes reference: "single_valued S" and determining: "inj (\<lambda>v. (f v,g v))"
  shows "(map_relation_values f R=map_relation_values f S \<and>
      map_relation_values g R=map_relation_values g S) \<longleftrightarrow> R=S"
proof
  assume observations: "map_relation_values f R=map_relation_values f S \<and>
    map_relation_values g R=map_relation_values g S"
  have lower: "R\<subseteq>S"
  proof
    fix z assume row: "z\<in>R"
    obtain k v where shape: "z=(k,v)" by (cases z)
    have mapped: "(k,f v)\<in>map_relation_values f R"
      "(k,g v)\<in>map_relation_values g R"
      using row by (auto simp: shape)
    have first: "(k,f v)\<in>map_relation_values f S"
      and second: "(k,g v)\<in>map_relation_values g S"
      using mapped by (simp_all only: conjunct1[OF observations] conjunct2[OF observations])
    have pair: "(k,(f v,g v))\<in>map_relation_values (\<lambda>w. (f w,g w)) S"
      using first second by (simp only: single_valued_paired_observations[OF reference])
    obtain w where actual: "(k,w)\<in>S" "(f v,g v)=(f w,g w)"
      using pair by auto
    have same: "v=w" by (rule injD[OF determining actual(2)])
    show "z\<in>S" using actual(1) by (simp only: shape same)
  qed
  have upper: "S\<subseteq>R"
  proof
    fix z assume row: "z\<in>S"
    obtain k v where shape: "z=(k,v)" by (cases z)
    have mapped: "(k,f v)\<in>map_relation_values f S"
      using row by (auto simp: shape)
    have first: "(k,f v)\<in>map_relation_values f R"
      using mapped by (simp only: conjunct1[OF observations])
    obtain w where actual: "(k,w)\<in>R" using first by auto
    have selected: "(k,w)\<in>S" by (rule subsetD[OF lower actual])
    have same: "w=v" by (rule single_valued_outputs[OF reference selected]) (use row shape in simp)
    show "z\<in>R" using actual by (simp only: shape same)
  qed
  show "R=S" using lower upper by blast
next
  assume "R=S"
  then show "map_relation_values f R=map_relation_values f S \<and>
    map_relation_values g R=map_relation_values g S" by simp
qed

text \<open>
  Only the reference relation must be functional. Complete equality of both
  observed relations forces each candidate row to carry the reference's same
  value and also forces coverage of every reference key. The joint observation
  must be injective; separate observation equality is insufficient otherwise.
\<close>

end
