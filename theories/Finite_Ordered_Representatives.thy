theory Finite_Ordered_Representatives
  imports Finite_Functional_Enumeration Finite_Set_Composition
begin

definition finite_relation_key_fibre :: "('k\<times>'v) fset\<Rightarrow>'v\<Rightarrow>'k fset" where
  "finite_relation_key_fibre R v=fimage fst (ffilter (\<lambda>(k,w). w=v) R)"

lemma finite_relation_key_fibre_member:
  "k |\<in>| finite_relation_key_fibre R v \<longleftrightarrow> (k,v) |\<in>| R"
  by (simp only: finite_relation_key_fibre_def finite_first_projection_member) auto

definition finite_relation_least_key :: "('k::linorder\<times>'v) fset\<Rightarrow>'v\<Rightarrow>'k option" where
  "finite_relation_least_key R v=(let K=finite_relation_key_fibre R v in
    if K={||} then None else Some (fMin K))"

theorem finite_relation_least_key_some:
  "finite_relation_least_key R v=Some k \<longleftrightarrow>
    (k,v) |\<in>| R \<and> (\<forall>j. (j,v) |\<in>| R \<longrightarrow> k\<le>j)"
proof
  let ?K = "finite_relation_key_fibre R v"
  assume selected: "finite_relation_least_key R v=Some k"
  have nonempty: "?K\<noteq>{||}" and least: "k=fMin ?K"
    using selected by (auto simp: finite_relation_least_key_def Let_def split: if_splits)
  have member: "k |\<in>| ?K" by (simp only: least; rule fMin_in[OF nonempty])
  have minimal: "k\<le>j" if "j |\<in>| ?K" for j
    by (simp only: least; rule fMin_le[OF that])
  show "(k,v) |\<in>| R \<and> (\<forall>j. (j,v) |\<in>| R \<longrightarrow> k\<le>j)"
    using member minimal by (simp only: finite_relation_key_fibre_member; blast)
next
  let ?K = "finite_relation_key_fibre R v"
  assume properties: "(k,v) |\<in>| R \<and> (\<forall>j. (j,v) |\<in>| R \<longrightarrow> k\<le>j)"
  have member: "k |\<in>| ?K"
    using properties by (simp only: finite_relation_key_fibre_member; blast)
  have nonempty: "?K\<noteq>{||}" using member by auto
  have least: "fMin ?K=k"
    by (rule fMin_eqI[OF _ member]) (use properties in \<open>simp only: finite_relation_key_fibre_member; blast\<close>)
  show "finite_relation_least_key R v=Some k"
    by (simp only: finite_relation_least_key_def Let_def nonempty if_False least)
qed

lemma finite_relation_least_key_member:
  "finite_relation_least_key R v=Some k \<Longrightarrow> (k,v) |\<in>| R"
  by (simp only: finite_relation_least_key_some; blast)

theorem finite_relation_least_key_domain:
  "(\<exists>k. finite_relation_least_key R v=Some k) \<longleftrightarrow> v |\<in>| fimage snd R"
proof
  assume "\<exists>k. finite_relation_least_key R v=Some k"
  then obtain k where selected: "finite_relation_least_key R v=Some k" by blast
  have member: "(k,v) |\<in>| R" by (rule finite_relation_least_key_member[OF selected])
  show "v |\<in>| fimage snd R" using member by (simp only: finite_second_projection_member; blast)
next
  assume "v |\<in>| fimage snd R"
  then obtain k where member: "(k,v) |\<in>| R"
    by (simp only: finite_second_projection_member; blast)
  have fibre: "k |\<in>| finite_relation_key_fibre R v"
    by (simp only: finite_relation_key_fibre_member; rule member)
  have nonempty: "finite_relation_key_fibre R v\<noteq>{||}"
    using fibre by auto
  show "\<exists>k. finite_relation_least_key R v=Some k"
    by (simp only: finite_relation_least_key_def Let_def nonempty if_False; blast)
qed

theorem finite_relation_representatives_distinct:
  assumes functional: "finite_relation_functional R"
    and left: "finite_relation_least_key R v=Some k"
    and right: "finite_relation_least_key R w=Some k"
  shows "v=w"
proof -
  have original: "single_valued (fset R)"
    using functional by (simp only: finite_relation_functional_correct)
  show ?thesis by (rule single_valued_outputs[OF original
    finite_relation_least_key_member[OF left] finite_relation_least_key_member[OF right]])
qed

definition finite_representative_map where
  "finite_representative_map R=ffUnion (fimage (\<lambda>v.
    case finite_relation_least_key R v of None \<Rightarrow> {||} | Some k \<Rightarrow> {|(v,k)|}) (fimage snd R))"

lemma finite_representative_map_member:
  "(v,k) |\<in>| finite_representative_map R \<longleftrightarrow> finite_relation_least_key R v=Some k"
proof -
  have covered: "v |\<in>| fimage snd R" if "finite_relation_least_key R v=Some k" for v k
    using that finite_relation_least_key_domain[of R v] by blast
  have singleton: "(v,k) |\<in>| (case z of None \<Rightarrow> {||} | Some j \<Rightarrow> {|(x,j)|}) \<longleftrightarrow>
    v=x \<and> z=Some k" for z x
    by (cases z) auto
  show ?thesis
    by (simp only: finite_representative_map_def finite_union_image_member singleton;
      use covered in blast)
qed

lemma finite_representative_map_domain:
  "fimage fst (finite_representative_map R)=fimage snd R"
  by (rule fset_inject[THEN iffD1], rule set_eqI)
    (simp only: finite_first_projection_member finite_representative_map_member finite_relation_least_key_domain)

lemma finite_representative_map_functional:
  "finite_relation_functional (finite_representative_map R)"
  by (auto simp: finite_relation_functional_correct single_valued_def finite_representative_map_member)

theorem finite_representative_map_injective:
  assumes "finite_relation_functional R"
  shows "single_valued ((fset (finite_representative_map R))\<inverse>)"
  by (auto simp: single_valued_def finite_representative_map_member
    intro: finite_relation_representatives_distinct[OF assms])

text \<open>
  The least label comes from the actual complete fibre. Missing values return
  None. Only labels require an order; values need no imposed ordering.
  Functional label rows make the chosen representatives of distinct values
  distinct, even when several original labels share one value.
\<close>

end
