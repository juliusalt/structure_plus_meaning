theory Factor_Data_Term_Presentations
  imports Factor_List_Set_Presentations
begin

section \<open>Complete data terms and finite sets use the general class constructions\<close>

abbreviation data_term_boundary :: "factor_term \<Rightarrow> bool" where
  "data_term_boundary t \<equiv> term_formed t \<and> self_contained_term t"

abbreviation data_term_presents :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "data_term_presents x p \<equiv> data_term_boundary x \<and> p=x"

abbreviation data_finite_set_presents where
  "data_finite_set_presents \<equiv> data_list_fset_presents data_term_presents"

abbreviation data_finite_set_domain where
  "data_finite_set_domain S \<equiv> \<forall>x\<in>fset S. data_term_boundary x"

lemma data_term_class:
  "presentation_class data_term_presents data_term_boundary data_term_boundary"
  by (unfold_locales) auto

lemma data_finite_set_class:
  "presentation_class data_finite_set_presents data_finite_set_domain
    (\<lambda>p. \<exists>xs. data_elements xs \<and> p=data_list_term xs)"
  by (rule data_list_fset_presentation_class[OF data_term_class])

lemma data_finite_set_at_list:
  "data_finite_set_presents S (data_list_term xs) \<longleftrightarrow>
    data_elements xs \<and> fset_of_list xs=S"
  by (rule data_list_fset_presents_identity)

lemma data_finite_set_fields:
  "data_finite_set_presents S p \<longleftrightarrow>
    (\<exists>xs. data_elements xs \<and> fset_of_list xs=S \<and> p=data_list_term xs)"
  using data_list_fset_presents_function[where D=data_term_boundary and f=id and S=S and t=p]
  by simp

lemma data_finite_set_presented_data:
  assumes "data_finite_set_presents S p"
  shows "data_term_boundary p"
proof -
  obtain xs where fields: "data_elements xs" "p=data_list_term xs"
    using assms by (simp only: data_finite_set_fields) blast
  show ?thesis using fields by (auto simp: data_list_term_formed data_list_term_self_contained)
qed

section \<open>Pairs and finite relations retain both complete data fields\<close>

abbreviation data_pair_term where
  "data_pair_term z \<equiv> case z of (x,y) \<Rightarrow> Pair_Term x y"

abbreviation data_pair_presents where
  "data_pair_presents \<equiv> factor_pair_presents data_term_presents data_term_presents"

abbreviation data_pair_domain where
  "data_pair_domain z \<equiv> case z of (x,y) \<Rightarrow> data_elements [x,y]"

abbreviation data_pair_finite_set_presents where
  "data_pair_finite_set_presents \<equiv> data_list_fset_presents data_pair_presents"

abbreviation data_pair_finite_set_domain where
  "data_pair_finite_set_domain S \<equiv> \<forall>(x,y)\<in>fset S. data_elements [x,y]"

lemma data_pair_class:
  "presentation_class data_pair_presents data_pair_domain (\<lambda>p. \<exists>z. data_pair_presents z p)"
proof -
  have domain: "(\<lambda>z. data_term_boundary (fst z) \<and> data_term_boundary (snd z))=data_pair_domain"
    by (rule ext) (auto split: prod.splits)
  show ?thesis using presentation_class.recovered_admission[OF factor_pair_class[OF data_term_class data_term_class]]
    by (simp only: domain)
qed

lemma data_pair_graph:
  "data_pair_presents=(\<lambda>z p. data_pair_domain z \<and> p=data_pair_term z)"
  by (intro ext) (auto simp: factor_pair_presents_def split: prod.splits)

lemma data_pair_finite_set_class:
  "presentation_class data_pair_finite_set_presents data_pair_finite_set_domain
    (\<lambda>p. \<exists>S. data_pair_finite_set_presents S p)"
proof -
  have source: "presentation_class data_pair_finite_set_presents data_pair_finite_set_domain
      (\<lambda>p. \<exists>xs. (\<forall>x\<in>set xs. \<exists>z. data_pair_presents z x) \<and> p=data_list_term xs)"
    by (rule data_list_fset_presentation_class[OF data_pair_class])
  show ?thesis by (rule presentation_class.recovered_admission[OF source])
qed

lemma data_pair_finite_set_fields:
  "data_pair_finite_set_presents S p \<longleftrightarrow>
    (\<exists>xs. (\<forall>(x,y)\<in>set xs. data_elements [x,y]) \<and> fset_of_list xs=S \<and>
      p=data_list_term (map data_pair_term xs))"
  by (simp only: data_pair_graph data_list_fset_presents_function)

lemma data_pair_finite_set_presented_data:
  assumes "data_pair_finite_set_presents S p"
  shows "data_term_boundary p"
  using assms by (simp only: data_pair_finite_set_fields)
    (auto simp: data_list_term_formed data_list_term_self_contained split: prod.splits)

text \<open>
  A data term is formed and has no external target. Its identity presentation
  is a local choice of class; the finite-set construction admits every list
  displaying its members, in every order and with arbitrary repetition.
  Observation data, facets, and values consume these same general
  boundaries. A finite pair set also presents a finite data relation without
  requiring functionality or restricting its endpoints to a separate scope.
\<close>

end
