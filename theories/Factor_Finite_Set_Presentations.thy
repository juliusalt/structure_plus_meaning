theory Factor_Finite_Set_Presentations
  imports Factor_Presentation_Classes "HOL-Library.FSet"
begin

section \<open>Collection constraints retain every represented member\<close>

lemma data_collection_presents_constrain:
  "data_collection_presents (\<lambda>a p. D a \<and> R a p) S t \<longleftrightarrow>
    (\<forall>a\<in>S. D a) \<and> data_collection_presents R S t"
proof -
  have rows: "list_all2 (\<lambda>a p. D a \<and> R a p) xs ps \<longleftrightarrow>
      (\<forall>a\<in>set xs. D a) \<and> list_all2 R xs ps" for xs ps
    by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)
  show ?thesis by (auto simp: data_collection_presents_def rows)
qed

lemma list_all2_presentation_constraint:
  "list_all2 (\<lambda>a p. R a p \<and> Q p) xs ps \<longleftrightarrow>
    list_all2 R xs ps \<and> (\<forall>p\<in>set ps. Q p)"
  by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)

lemma data_collection_presents_presentation_constraint:
  "data_collection_presents (\<lambda>a p. R a p \<and> Q p) A (data_list_term ps) \<longleftrightarrow>
    data_collection_presents R A (data_list_term ps) \<and> (\<forall>p\<in>set ps. Q p)"
  by (auto simp: data_collection_presents_def list_all2_presentation_constraint data_list_term_injective)

section \<open>Finite sets use the existing complete collection presentations\<close>

abbreviation data_fset_presents ::
  "('a\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow> 'a fset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "data_fset_presents R S t \<equiv> data_collection_presents R (fset S) t"

theorem data_fset_presentation_class:
  assumes source: "presentation_class R D A"
  shows "presentation_class (data_fset_presents R)
    (\<lambda>S. \<forall>a\<in>fset S. D a) (presented_predicate (data_sequence_presents R) distinct)"
proof -
  have collection: "presentation_class (data_collection_presents R)
      (\<lambda>S. finite S \<and> (\<forall>a\<in>S. D a))
      (presented_predicate (data_sequence_presents R) distinct)"
    by (rule data_collection_presentation_class[OF source])
  have inverse: "Abs_fset (fset S)=S" for S :: "'a fset"
    by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)
  have image: "presentation_class
      (\<lambda>S t. \<exists>X. data_collection_presents R X t \<and> Abs_fset X=S)
      (\<lambda>S. \<forall>a\<in>fset S. D a)
      (presented_predicate (data_sequence_presents R) distinct)"
  proof (rule presentation_class_image[OF collection])
    fix X assume "finite X \<and> (\<forall>a\<in>X. D a)"
    then show "\<forall>a\<in>fset (Abs_fset X). D a" by (simp add: Abs_fset_inverse)
  next
    fix S assume domain: "\<forall>a\<in>fset S. D a"
    show "\<exists>X. (finite X \<and> (\<forall>a\<in>X. D a)) \<and> Abs_fset X=S"
      by (rule exI[of _ "fset S"]) (use domain inverse in simp)
  qed
  have reading: "(\<lambda>S t. \<exists>X. data_collection_presents R X t \<and> Abs_fset X=S)=data_fset_presents R"
  proof (intro ext)
    fix S t
    show "(\<exists>X. data_collection_presents R X t \<and> Abs_fset X=S) \<longleftrightarrow> data_fset_presents R S t"
    proof
      assume "\<exists>X. data_collection_presents R X t \<and> Abs_fset X=S"
      then obtain X where read: "data_collection_presents R X t" and same: "Abs_fset X=S" by blast
      have finite: "finite X" by (rule data_collection_presents_finite[OF read])
      have fields: "fset S=X" using finite by (simp add: same[symmetric] Abs_fset_inverse)
      show "data_fset_presents R S t" using read fields by simp
    next
      assume "data_fset_presents R S t"
      then show "\<exists>X. data_collection_presents R X t \<and> Abs_fset X=S"
        by (rule_tac x="fset S" in exI) (simp add: inverse)
    qed
  qed
  show ?thesis using image by (simp only: reading)
qed

text \<open>
  The finite-set type changes the subject coordinates, not the stored list.
  The covered image rule proves this change on the independently specified
  domain of all finite sets of allowed elements. Every member still occurs
  exactly once, in every complete order and with every allowed presentation.
  No list order becomes part of finite-set identity, and no occurrence in a
  sequence is silently discarded.
\<close>

end
