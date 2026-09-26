theory Factor_Bag_Presentations
  imports Factor_Presentation_Transport
begin

section \<open>A bag retains every subject and its multiplicity\<close>

definition data_bag_presents ::
  "('a \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "data_bag_presents read M t \<longleftrightarrow>
    (\<exists>xs. data_sequence_presents read xs t \<and> mset xs=M)"

theorem data_bag_presentation_class:
  assumes source: "presentation_class read D A"
  shows "presentation_class (data_bag_presents read) (\<lambda>M. \<forall>a\<in>set_mset M. D a)
    (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. A p) \<and> t=data_list_term ps)"
proof -
  have sequences: "presentation_class (data_sequence_presents read) (\<lambda>xs. \<forall>a\<in>set xs. D a)
      (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. A p) \<and> t=data_list_term ps)"
    by (rule data_sequence_presentation_class[OF source])
  have image: "presentation_class (\<lambda>M t. \<exists>xs. data_sequence_presents read xs t \<and> mset xs=M)
      (\<lambda>M. \<forall>a\<in>set_mset M. D a)
      (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. A p) \<and> t=data_list_term ps)"
  proof (rule presentation_class_image[OF sequences])
    fix xs assume "\<forall>a\<in>set xs. D a"
    then show "\<forall>a\<in>set_mset (mset xs). D a" by simp
  next
    fix M assume domain: "\<forall>a\<in>set_mset M. D a"
    obtain xs where enumeration: "mset xs=M" using ex_mset by blast
    show "\<exists>xs. (\<forall>a\<in>set xs. D a) \<and> mset xs=M"
      by (rule exI[of _ xs]) (use enumeration domain in auto)
  qed
  show ?thesis using image by (simp only: presentation_class_def data_bag_presents_def)
qed

theorem data_bag_presentation_change:
  assumes "presentation_class R D A" "presentation_class S D B"
  shows "presentation_change (data_bag_presents R) (\<lambda>M. \<forall>a\<in>set_mset M. D a)
    (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. A p) \<and> t=data_list_term ps)
    (data_bag_presents S) (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. B p) \<and> t=data_list_term ps)"
  by (rule presentation_change.intro)
    (rule data_bag_presentation_class[OF assms(1)], rule data_bag_presentation_class[OF assms(2)])

section \<open>Two presentations of one bag, in list form\<close>

text \<open>
  A bag presented by a function of its members is a listing of their images. A bag presented by its members
  themselves, where a domain restricts them, is a listing of the members; two such presentations correspond exactly
  when they list the same members with the same multiplicities. Stated once here: the bags of terms and of complete
  data values are its instances, and a use of either reads it in list form.
\<close>

lemma data_bag_function:
  "data_bag_presents (\<lambda>a t. t = f a) N t \<longleftrightarrow> (\<exists>xs. mset xs = N \<and> t = data_list_term (map f xs))"
  by (auto simp: data_bag_presents_def data_sequence_presents_def list_all2_function)

theorem data_bag_restricted_transport:
  "presentation_transport (data_bag_presents (\<lambda>a t. t = a \<and> D a)) (data_bag_presents (\<lambda>a t. t = a \<and> D a)) t t'
    \<longleftrightarrow> (\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> (\<forall>a\<in>set xs. D a) \<and> (\<forall>a\<in>set xs'. D a) \<and>
      mset xs = mset xs')"
proof
  assume "presentation_transport (data_bag_presents (\<lambda>a t. t = a \<and> D a)) (data_bag_presents (\<lambda>a t. t = a \<and> D a)) t t'"
  then obtain N xs ps xs' ps' where l: "list_all2 (\<lambda>a t. t = a \<and> D a) xs ps" and tp: "t = data_list_term ps"
      and m: "mset xs = N" and l': "list_all2 (\<lambda>a t. t = a \<and> D a) xs' ps'" and tp': "t' = data_list_term ps'"
      and m': "mset xs' = N"
    unfolding presentation_transport_def data_bag_presents_def data_sequence_presents_def by blast
  have "ps = xs \<and> (\<forall>a\<in>set xs. D a)" "ps' = xs' \<and> (\<forall>a\<in>set xs'. D a)"
    using l l' unfolding list_all2_function_restricted[of id D, simplified] by blast+
  then show "\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> (\<forall>a\<in>set xs. D a) \<and> (\<forall>a\<in>set xs'. D a) \<and>
      mset xs = mset xs'"
    using tp tp' m m' by (intro exI[of _ xs] exI[of _ xs']) auto
next
  assume "\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> (\<forall>a\<in>set xs. D a) \<and> (\<forall>a\<in>set xs'. D a) \<and>
      mset xs = mset xs'"
  then obtain xs xs' where r: "t = data_list_term xs" "t' = data_list_term xs'" "\<forall>a\<in>set xs. D a" "\<forall>a\<in>set xs'. D a"
      "mset xs = mset xs'" by blast
  have "list_all2 (\<lambda>a t. t = a \<and> D a) xs xs" "list_all2 (\<lambda>a t. t = a \<and> D a) xs' xs'"
    using r(3,4) by (simp_all add: list_all2_function_restricted[of id D, simplified])
  then show "presentation_transport (data_bag_presents (\<lambda>a t. t = a \<and> D a)) (data_bag_presents (\<lambda>a t. t = a \<and> D a)) t t'"
    unfolding presentation_transport_def data_bag_presents_def data_sequence_presents_def using r(1,2,5) by blast
qed

abbreviation term_bag_presents :: "factor_term multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_bag_presents \<equiv> data_bag_presents (\<lambda>a t. t = a)"

lemma term_bag_presents_terms: "term_bag_presents N t \<longleftrightarrow> (\<exists>ys. mset ys = N \<and> t = data_list_term ys)"
  using data_bag_function[of "\<lambda>a. a"] by simp

lemma term_bag_presentation_class:
  "presentation_class term_bag_presents (\<lambda>_. True) (\<lambda>t. \<exists>N. term_bag_presents N t)"
  using presentation_class.recovered_admission[OF data_bag_presentation_class[OF identity_presentation_class]] by simp

abbreviation term_bag_transport :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_bag_transport \<equiv> presentation_transport term_bag_presents term_bag_presents"

lemma term_bag_transport_iff:
  "term_bag_transport t t' \<longleftrightarrow> (\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> mset xs = mset xs')"
  using data_bag_restricted_transport[of "\<lambda>_. True" t t'] by simp

lemma term_bag_transport_lists:
  "term_bag_transport (data_list_term xs) (data_list_term ys) \<longleftrightarrow> mset xs = mset ys"
  by (auto simp: term_bag_transport_iff data_list_term_injective)

lemma term_bag_transport_sym: "symp term_bag_transport"
  unfolding symp_def term_bag_transport_iff by metis

section \<open>Existing ordinary list admission covers exactly bags of complete data\<close>

definition data_bag_value_presents :: "factor_term multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "data_bag_value_presents M t \<longleftrightarrow>
    (\<exists>xs. data_elements xs \<and> mset xs=M \<and> t=data_list_term xs)"

lemma data_bag_value_restricted:
  "data_bag_value_presents = data_bag_presents (\<lambda>a t. t = a \<and> term_formed a \<and> self_contained_term a)"
  by (intro ext) (unfold data_bag_value_presents_def data_bag_presents_def data_sequence_presents_def
    list_all2_function_restricted[of id "\<lambda>a. term_formed a \<and> self_contained_term a", simplified], auto)

theorem data_bag_value_presentation_class:
  "presentation_class data_bag_value_presents
    (\<lambda>M. \<forall>a\<in>set_mset M. term_formed a \<and> self_contained_term a)
    (\<lambda>t. (4,t)\<in>positive_meaning bag_comparison_system)"
proof -
  let ?D="\<lambda>a. term_formed a \<and> self_contained_term a"
  let ?read="\<lambda>a p. p=a \<and> ?D a"
  have elements: "presentation_class ?read ?D ?D"
    by (unfold_locales) auto
  have bag: "presentation_class (data_bag_presents ?read) (\<lambda>M. \<forall>a\<in>set_mset M. ?D a)
      (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. ?D p) \<and> t=data_list_term ps)"
    by (rule data_bag_presentation_class[OF elements])
  have reads: "data_bag_presents ?read=data_bag_value_presents"
    by (rule data_bag_value_restricted[symmetric])
  have admission: "(\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. ?D p) \<and> t=data_list_term ps)=
      (\<lambda>t. (4,t)\<in>positive_meaning bag_comparison_system)"
    by (rule ext) (auto simp: data_list_exact)
  show ?thesis using bag by (simp only: reads admission)
qed

interpretation data_bag_presentations: presentation_class data_bag_value_presents
  "\<lambda>M. \<forall>a\<in>set_mset M. term_formed a \<and> self_contained_term a"
  "\<lambda>t. (4,t)\<in>positive_meaning bag_comparison_system"
  by (rule data_bag_value_presentation_class)

theorem data_bag_identity_presented:
  "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system \<longleftrightarrow>
    presented_relation data_bag_value_presents data_bag_value_presents (=) p q"
proof
  assume holds: "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system"
  obtain xs ys where parts: "p=data_list_term xs" "q=data_list_term ys"
    "data_elements xs" "data_elements ys" "mset xs=mset ys"
    using holds by (auto simp only: bag_comparison_exact factor_term.inject)
  have first: "data_bag_value_presents (mset xs) p" and second: "data_bag_value_presents (mset ys) q"
    using parts unfolding data_bag_value_presents_def by blast+
  show "presented_relation data_bag_value_presents data_bag_value_presents (=) p q"
    using first second parts(5) unfolding presented_relation_def by blast
next
  assume "presented_relation data_bag_value_presents data_bag_value_presents (=) p q"
  then obtain M where readings: "data_bag_value_presents M p" "data_bag_value_presents M q"
    unfolding presented_relation_def by blast
  obtain xs where first: "data_elements xs" "mset xs=M" "p=data_list_term xs"
    using readings(1) unfolding data_bag_value_presents_def by blast
  obtain ys where second: "data_elements ys" "mset ys=M" "q=data_list_term ys"
    using readings(2) unfolding data_bag_value_presents_def by blast
  have same: "mset xs=mset ys" using first(2) second(2) by simp
  show "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system"
    using bag_comparison_complete[OF first(1) second(1) same]
    by (simp only: first(3) second(3))
qed

interpretation data_bag_identity_contract: presented_relation_contract
  data_bag_value_presents "\<lambda>M. \<forall>a\<in>set_mset M. term_formed a \<and> self_contained_term a"
    "\<lambda>t. (4,t)\<in>positive_meaning bag_comparison_system"
  data_bag_value_presents "\<lambda>M. \<forall>a\<in>set_mset M. term_formed a \<and> self_contained_term a"
    "\<lambda>t. (4,t)\<in>positive_meaning bag_comparison_system"
  "(=)" "\<lambda>p q. (6,Pair_Term p q)\<in>positive_meaning bag_comparison_system"
  by (unfold_locales)
    (use data_bag_presentations.presentation_class_axioms data_bag_identity_presented in
      \<open>auto simp: presentation_class_def\<close>)

text \<open>
  Two presentations of one bag of complete data values are two listings of complete data with the same members and
  multiplicities: the list form of the class's transport, the restricted transport at its domain.
\<close>

theorem data_bag_value_transport:
  "presentation_transport data_bag_value_presents data_bag_value_presents t t' \<longleftrightarrow>
    (\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> data_elements xs \<and> data_elements xs' \<and>
      mset xs = mset xs')"
  unfolding data_bag_value_restricted by (rule data_bag_restricted_transport)

corollary data_bag_value_transport_lists:
  "presentation_transport data_bag_value_presents data_bag_value_presents (data_list_term xs) (data_list_term ys)
    \<longleftrightarrow> data_elements xs \<and> data_elements ys \<and> mset xs = mset ys"
  by (auto simp: data_bag_value_transport data_list_term_injective)

text \<open>
  A finite multiset is the independent subject. Complete sequences present
  all its members with their multiplicities, and the covered image rule
  forgets only enumeration order. No distinctness constraint or conversion
  to a membership set enters this class. Every permitted member presentation
  and every enumeration remains available.

  Complete data bags instantiate the generic class. The existing ordinary
  list reader supplies their exact admission, and the existing counted
  comparison supplies the local identity contract. Later artifact and
  collection operations can use these exported facts without defining bag
  meaning from their particular application.
\<close>

end
