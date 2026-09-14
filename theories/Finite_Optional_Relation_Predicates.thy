theory Finite_Optional_Relation_Predicates
  imports "HOL-Library.FSet"
begin

lemma finite_optional_relation_exists:
  "fBex R (\<lambda>(k,X). case X of None \<Rightarrow> False | Some x \<Rightarrow> P x) \<longleftrightarrow>
    (\<exists>k x. (k,Some x) |\<in>| R \<and> P x)"
  by (simp add: Bex_def split_paired_Ex split_option_ex)

lemma finite_optional_relation_all:
  "fBall R (\<lambda>(k,X). case X of None \<Rightarrow> False | Some x \<Rightarrow> P x) \<longleftrightarrow>
    (\<forall>k X. (k,X) |\<in>| R \<longrightarrow> (\<exists>x. X=Some x \<and> P x))"
  by (simp add: Ball_def split_paired_All split_option_all split_option_ex)

end
