theory Finite_Functional_Selections
  imports Finite_Compatible_Unions Bootstrap_Finite_Closure
begin

definition finite_functional_selections where
  "finite_functional_selections K R=ffilter (\<lambda>B. fimage fst B=K)
    (finite_compatible_unions (fimage (\<lambda>r. {|r|}) R))"

lemma finite_singleton_parts_complete:
  "B |\<in>| finite_compatible_unions (fimage (\<lambda>r. {|r|}) R) \<longleftrightarrow>
    finite_relation_functional B \<and> B |\<subseteq>| R"
proof
  assume member: "B |\<in>| finite_compatible_unions (fimage (\<lambda>r. {|r|}) R)"
  have functional: "finite_relation_functional B"
    using member by (simp only: finite_compatible_union_member; blast)
  have included: "B |\<subseteq>| R"
    using finite_compatible_union_origin[OF member]
    by (auto simp: fsubset_iff)
  show "finite_relation_functional B \<and> B |\<subseteq>| R" using functional included by blast
next
  assume parts: "finite_relation_functional B \<and> B |\<subseteq>| R"
  have included: "fimage (\<lambda>r. {|r|}) B |\<subseteq>| fimage (\<lambda>r. {|r|}) R"
    using parts by (intro fimage_mono; blast)
  have union: "ffUnion (fimage (\<lambda>r. {|r|}) B)=B"
    by (rule fset_inject[THEN iffD1]) (auto simp: ffUnion_membership)
  show "B |\<in>| finite_compatible_unions (fimage (\<lambda>r. {|r|}) R)"
    using parts included union by (simp only: finite_compatible_union_member; blast)
qed

theorem finite_functional_selection_exact:
  "B |\<in>| finite_functional_selections K R \<longleftrightarrow>
    B |\<subseteq>| R \<and> finite_relation_functional B \<and> fimage fst B=K"
  by (auto simp: finite_functional_selections_def finite_singleton_parts_complete)

theorem finite_functional_selection_domain:
  "finite_functional_selections K R\<noteq>{||} \<longleftrightarrow> K |\<subseteq>| fimage fst R"
proof
  assume nonempty: "finite_functional_selections K R\<noteq>{||}"
  then obtain B where selected: "B |\<in>| finite_functional_selections K R" by auto
  have parts: "B |\<subseteq>| R \<and> finite_relation_functional B \<and> fimage fst B=K"
    using selected by (simp only: finite_functional_selection_exact)
  have included: "B |\<subseteq>| R" using parts by blast
  have domain: "fimage fst B=K" using parts by blast
  show "K |\<subseteq>| fimage fst R" using fimage_mono[OF included, of fst] by (simp only: domain)
next
  assume covered: "K |\<subseteq>| fimage fst R"
  have available: "\<exists>b. (a,b) |\<in>| R" if "a |\<in>| K" for a
  proof -
    have key: "a |\<in>| fimage fst R" by (rule fsubsetD[OF covered that])
    show ?thesis using key by (simp only: finite_first_projection_member)
  qed
  let ?choose="\<lambda>a. SOME b. (a,b) |\<in>| R"
  let ?B="fimage (\<lambda>a. (a,?choose a)) K"
  have chosen: "(a,?choose a) |\<in>| R" if "a |\<in>| K" for a
    by (rule someI_ex[OF available[OF that]])
  have included: "?B |\<subseteq>| R" using chosen by auto
  have functional: "finite_relation_functional ?B"
    by (auto simp: finite_relation_functional_correct single_valued_def)
  have domain: "fimage fst ?B=K" by (simp add: fimage_fimage comp_def)
  have selected: "?B |\<in>| finite_functional_selections K R"
    using included functional domain by (simp only: finite_functional_selection_exact; blast)
  show "finite_functional_selections K R\<noteq>{||}" using selected by auto
qed

definition finite_family_images where
  "finite_family_images H T=finite_functional_selections (fimage fst H) (finite_edge_compose H T)"

theorem finite_family_image_exact:
  "B |\<in>| finite_family_images H T \<longleftrightarrow>
    finite_relation_functional B \<and> fimage fst B=fimage fst H \<and>
    (\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>q. (s,q) |\<in>| H \<and> (q,p) |\<in>| T))"
  by (auto simp: finite_family_images_def finite_functional_selection_exact
    fsubset_iff finite_edge_compose_member)

theorem finite_family_images_total:
  assumes support: "fimage snd H |\<subseteq>| fimage fst T"
  shows "finite_family_images H T\<noteq>{||}"
proof -
  have covered: "fimage fst H |\<subseteq>| fimage fst (finite_edge_compose H T)"
  proof (rule fsubsetI)
    fix s assume member: "s |\<in>| fimage fst H"
    obtain q where required: "(s,q) |\<in>| H"
      using member by (simp only: finite_first_projection_member; blast)
    have requested: "q |\<in>| fimage snd H"
      using required by (simp only: finite_second_projection_member; blast)
    have available: "q |\<in>| fimage fst T" by (rule fsubsetD[OF support requested])
    obtain p where actual: "(q,p) |\<in>| T"
      using available by (simp only: finite_first_projection_member; blast)
    have joined: "(s,p) |\<in>| finite_edge_compose H T"
      using required actual by (simp only: finite_edge_compose_member; blast)
    show "s |\<in>| fimage fst (finite_edge_compose H T)"
      using joined by (simp only: finite_first_projection_member; blast)
  qed
  show ?thesis by (simp only: finite_family_images_def finite_functional_selection_domain; rule covered)
qed

text \<open>
  The operation constructs every complete functional selection from the actual
  finite relation. Its required domain is independent of the available rows.
  Missing keys cannot disappear from that domain. The implementation reuses
  compatible finite assembly; the choice in the coverage proof is not an
  executable selector or an additional supplied witness.
\<close>

end
