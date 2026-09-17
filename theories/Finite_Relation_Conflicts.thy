theory Finite_Relation_Conflicts
  imports Finite_Keyed_Products RRA_Finite_Artifacts
begin

definition relation_conflicts :: "('k\<times>'v) set\<Rightarrow>('k\<times>'v\<times>'v) set" where
  "relation_conflicts R={(k,a,b). (k,a)\<in>R \<and> (k,b)\<in>R \<and> a\<noteq>b}"

definition finite_relation_conflicts :: "('k\<times>'v) fset\<Rightarrow>('k\<times>'v\<times>'v) fset" where
  "finite_relation_conflicts R=ffilter (\<lambda>(k,a,b). a\<noteq>b) (finite_keyed_product R R)"

lemma finite_relation_conflicts_member:
  "(k,a,b) |\<in>| finite_relation_conflicts R \<longleftrightarrow>
    (k,a) |\<in>| R \<and> (k,b) |\<in>| R \<and> a\<noteq>b"
  by (auto simp: finite_relation_conflicts_def finite_keyed_product_member)

theorem finite_relation_conflicts_exact:
  "fset (finite_relation_conflicts R)=relation_conflicts (fset R)"
  by (auto simp: set_eq_iff split_paired_All finite_relation_conflicts_member relation_conflicts_def)

lemma relation_conflicts_empty:
  "relation_conflicts R={} \<longleftrightarrow> single_valued R"
  by (auto simp: relation_conflicts_def single_valued_def)

lemma finite_relation_conflicts_empty:
  "finite_relation_conflicts R={||} \<longleftrightarrow> finite_relation_functional R"
  by (simp add: fset_inject[symmetric] finite_relation_conflicts_exact
    relation_conflicts_empty finite_relation_functional_correct)

definition finite_projection_conflicts where
  "finite_projection_conflicts key A=finite_relation_conflicts (fimage (\<lambda>a. (key a,a)) A)"

lemma finite_projection_conflicts_member:
  "(k,a,b) |\<in>| finite_projection_conflicts key A \<longleftrightarrow>
    a |\<in>| A \<and> b |\<in>| A \<and> key a=k \<and> key b=k \<and> a\<noteq>b"
  by (auto simp: finite_projection_conflicts_def finite_relation_conflicts_member
    fimage.rep_eq image_iff)

theorem finite_projection_conflicts_empty:
  "finite_projection_conflicts key A={||} \<longleftrightarrow> inj_on key (fset A)"
  by (auto simp: finite_projection_conflicts_def finite_relation_conflicts_empty
    finite_relation_functional_correct single_valued_def inj_on_def fimage.rep_eq)

lemma finite_projection_conflicts_nonempty:
  "finite_projection_conflicts key A\<noteq>{||} \<longleftrightarrow>
    (\<exists>a\<in>fset A. \<exists>b\<in>fset A. a\<noteq>b \<and> key a=key b)"
  by (auto simp: finite_projection_conflicts_empty inj_on_def)

lemma finite_relation_shared_keys:
  "finite_projection_conflicts snd R\<noteq>{||} \<longleftrightarrow>
    (\<exists>k l v. k\<noteq>l \<and> (k,v) |\<in>| R \<and> (l,v) |\<in>| R)"
proof
  assume "finite_projection_conflicts snd R\<noteq>{||}"
  then obtain a b where members: "a |\<in>| R" "b |\<in>| R" "a\<noteq>b" "snd a=snd b"
    by (simp only: finite_projection_conflicts_nonempty; blast)
  show "\<exists>k l v. k\<noteq>l \<and> (k,v) |\<in>| R \<and> (l,v) |\<in>| R"
    by (rule exI[of _ "fst a"], rule exI[of _ "fst b"], rule exI[of _ "snd a"])
      (use members in \<open>cases a; cases b; auto\<close>)
next
  assume "\<exists>k l v. k\<noteq>l \<and> (k,v) |\<in>| R \<and> (l,v) |\<in>| R"
  then obtain k l v where members: "k\<noteq>l" "(k,v) |\<in>| R" "(l,v) |\<in>| R" by blast
  show "finite_projection_conflicts snd R\<noteq>{||}"
    unfolding finite_projection_conflicts_nonempty
    by (rule bexI[of _ "(k,v)"], rule bexI[of _ "(l,v)"])
      (use members in auto)
qed

text \<open>
  Conflicts retain the common key and both unequal original values. They are
  computed from the complete relation. Projecting an original finite family
  supplies every pair that a proposed identity would merge. Empty conflicts
  mean precisely functionality or injectivity at the respective full boundary.
\<close>

end
