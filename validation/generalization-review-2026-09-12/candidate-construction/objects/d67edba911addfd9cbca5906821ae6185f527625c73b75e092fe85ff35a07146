theory Factor_Generation_Admission
  imports Factor_Generation_Equations
begin

section \<open>Finite subterm bounds support the joint proof\<close>

lemma generation_bounded_collections:
  assumes admission: "\<And>t. term_height t<n \<Longrightarrow>
      (139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (\<exists>G. generation_value_presents G t)"
    and comparison: "\<And>G H p q. generation_value_presents G p \<Longrightarrow> generation_value_presents H q \<Longrightarrow>
      term_height p<n \<Longrightarrow> term_height q<n \<Longrightarrow>
      (141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
    and bound: "\<forall>p\<in>set ps. term_height p<n"
  shows "(143,data_list_term ps)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>A. data_collection_presents generation_value_presents A (data_list_term ps))"
proof -
  let ?R="\<lambda>G p. generation_value_presents G p \<and> term_height p<n"
  have compare: "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
    if "?R G p" "?R H q" for G H p q
    using comparison that by blast
  show ?thesis
  proof
    assume admitted: "(143,data_list_term ps)\<in>positive_meaning generation_value_system"
    have members: "\<forall>p\<in>set ps. (139,p)\<in>positive_meaning generation_value_system"
      and separated: "sorted_wrt (\<lambda>p q. (141,Pair_Term p q)\<in>positive_meaning generation_value_system) ps"
      using generation_collections.collection_lists[of ps] admitted by blast+
    have sources: "\<forall>p\<in>set ps. \<exists>G. ?R G p" using members admission bound by blast
    obtain xs where reading: "list_all2 ?R xs ps" using sources list_all2_exists_left by blast
    have distinct: "distinct xs"
      using generation_collections.presented_separation[OF reading compare] separated by blast
    have plain: "list_all2 generation_value_presents xs ps"
      using reading by (simp only: list_all2_presentation_constraint)
    show "\<exists>A. data_collection_presents generation_value_presents A (data_list_term ps)"
      by (rule exI[of _ "set xs"]) (use distinct plain in \<open>auto simp: data_collection_presents_def\<close>)
  next
    assume "\<exists>A. data_collection_presents generation_value_presents A (data_list_term ps)"
    then obtain xs where parts: "distinct xs" "list_all2 generation_value_presents xs ps"
      by (auto simp: data_collection_presents_def data_list_term_injective)
    have reading: "list_all2 ?R xs ps"
      using parts(2) bound by (simp only: list_all2_presentation_constraint)
    have members: "\<forall>p\<in>set ps. (139,p)\<in>positive_meaning generation_value_system"
      using list_all2_members[OF parts(2)] admission bound by blast
    have separated: "sorted_wrt (\<lambda>p q. (141,Pair_Term p q)\<in>positive_meaning generation_value_system) ps"
      using generation_collections.presented_separation[OF reading compare] parts(1) by blast
    show "(143,data_list_term ps)\<in>positive_meaning generation_value_system"
      by (rule generation_collections.collection_complete[OF members separated])
  qed
qed

lemma generation_value_bounded_contracts:
  "(\<forall>t. term_height t<n \<longrightarrow>
      ((139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (\<exists>G. generation_value_presents G t))) \<and>
    (\<forall>G H p q. generation_value_presents G p \<longrightarrow> generation_value_presents H q \<longrightarrow>
      term_height p<n \<longrightarrow> term_height q<n \<longrightarrow>
      ((140,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G=H) \<and>
      ((141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H))"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have old_admission: "(139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (\<exists>G. generation_value_presents G t)" if "term_height t<n" for t
    using Suc.IH that by blast
  have old_identity: "(140,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G=H"
    if "generation_value_presents G p" "generation_value_presents H q" "term_height p<n" "term_height q<n" for G H p q
    using Suc.IH that by blast
  have old_difference: "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
    if "generation_value_presents G p" "generation_value_presents H q" "term_height p<n" "term_height q<n" for G H p q
    using Suc.IH that by blast
  have collections: "(143,data_list_term ps)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (\<exists>A. data_collection_presents generation_value_presents A (data_list_term ps))"
    if "\<forall>p\<in>set ps. term_height p<n" for ps
    by (rule generation_bounded_collections[OF old_admission old_difference that])
  have admission: "(139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (\<exists>G. generation_value_presents G t)" if bound: "term_height t<Suc n" for t
  proof
    assume admitted: "(139,t)\<in>positive_meaning generation_value_system"
    obtain a b c d l p q where fields: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
      "target_value_presents l a" "(143,b)\<in>positive_meaning generation_value_system"
      "target_value_presents p c" "target_value_presents q d"
      using admitted by (simp only: generation_admission_fields) blast
    obtain ps where represented: "b=data_list_term ps"
      using generation_collections.collection_sound[OF fields(3)] by blast
    have shape: "t=Pair_Term a (Pair_Term (data_list_term ps) (Pair_Term c d))"
      using fields(1) represented by simp
    have smaller: "\<forall>x\<in>set ps. term_height x<n"
    proof (intro ballI)
      fix x assume member: "x\<in>set ps"
      have "term_height x<term_height t" by (rule generation_predecessor_term_height[OF shape member])
      then show "term_height x<n" using bound by arith
    qed
    obtain A where reading: "data_collection_presents generation_value_presents A b"
      using collections[OF smaller] fields(3) by (simp only: represented) blast
    have finite: "finite A" by (rule data_collection_presents_finite[OF reading])
    have restored: "fset (Abs_fset A)=A" by (rule Abs_fset_inverse) (use finite in simp)
    have predecessors: "data_collection_presents generation_value_presents (fset (Abs_fset A)) b"
      using reading by (simp only: restored)
    have presented: "generation_value_presents (Generation l (Abs_fset A) p q) t"
      using generation_value_presents.generation[OF fields(2) predecessors fields(4,5)] fields(1) by simp
    show "\<exists>G. generation_value_presents G t" using presented by blast
  next
    assume "\<exists>G. generation_value_presents G t"
    then obtain l P p q a b c d where fields: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
      "target_value_presents l a" "data_collection_presents generation_value_presents (fset P) b"
      "target_value_presents p c" "target_value_presents q d"
      by (auto elim: generation_value_presents.cases)
    obtain ps where represented: "b=data_list_term ps"
      using fields(3) unfolding data_collection_presents_def by blast
    have shape: "t=Pair_Term a (Pair_Term (data_list_term ps) (Pair_Term c d))"
      using fields(1) represented by simp
    have smaller: "\<forall>x\<in>set ps. term_height x<n"
    proof (intro ballI)
      fix x assume member: "x\<in>set ps"
      have "term_height x<term_height t" by (rule generation_predecessor_term_height[OF shape member])
      then show "term_height x<n" using bound by arith
    qed
    have predecessors: "(143,b)\<in>positive_meaning generation_value_system"
      using collections[OF smaller] fields(3) by (simp only: represented) blast
    show "(139,t)\<in>positive_meaning generation_value_system"
      using fields(1,2,4,5) predecessors by (simp only: generation_admission_fields) blast
  qed
  have comparison:
    "((140,Pair_Term t u)\<in>positive_meaning generation_value_system \<longleftrightarrow> G=H) \<and>
      ((141,Pair_Term t u)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H)"
    if left: "generation_value_presents G t" and right: "generation_value_presents H u"
      and bounds: "term_height t<Suc n" "term_height u<Suc n" for G H t u
  proof -
    obtain l P p q where core: "G=Generation l P p q" by (cases G) auto
    obtain l' Q p' q' where other: "H=Generation l' Q p' q'" by (cases H) auto
    obtain a b c d where first: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
      "target_value_presents l a" "data_collection_presents generation_value_presents (fset P) b"
      "target_value_presents p c" "target_value_presents q d"
      using left by (simp only: core generation_value_presents_cases) blast
    obtain e f g h where second: "u=Pair_Term e (Pair_Term f (Pair_Term g h))"
      "target_value_presents l' e" "data_collection_presents generation_value_presents (fset Q) f"
      "target_value_presents p' g" "target_value_presents q' h"
      using right by (simp only: other generation_value_presents_cases) blast
    obtain ps where bp: "b=data_list_term ps" using first(3) unfolding data_collection_presents_def by blast
    obtain qs where bq: "f=data_list_term qs" using second(3) unfolding data_collection_presents_def by blast
    have shape_t: "t=Pair_Term a (Pair_Term (data_list_term ps) (Pair_Term c d))"
      and shape_u: "u=Pair_Term e (Pair_Term (data_list_term qs) (Pair_Term g h))"
      using first(1) second(1) bp bq by simp_all
    have small_left: "\<forall>x\<in>set ps. term_height x<n"
    proof (intro ballI)
      fix x assume member: "x\<in>set ps"
      have "term_height x<term_height t" by (rule generation_predecessor_term_height[OF shape_t member])
      then show "term_height x<n" using bounds(1) by arith
    qed
    have small_right: "\<forall>x\<in>set qs. term_height x<n"
    proof (intro ballI)
      fix x assume member: "x\<in>set qs"
      have "term_height x<term_height u" by (rule generation_predecessor_term_height[OF shape_u member])
      then show "term_height x<n" using bounds(2) by arith
    qed
    let ?R="\<lambda>G p. generation_value_presents G p \<and> term_height p<n"
    have left_read: "data_collection_presents ?R (fset P) b"
      using first(3) small_left by (simp only: bp data_collection_presents_presentation_constraint)
    have right_read: "data_collection_presents ?R (fset Q) f"
      using second(3) small_right by (simp only: bq data_collection_presents_presentation_constraint)
    have equal: "(140,Pair_Term x y)\<in>positive_meaning generation_value_system \<longleftrightarrow> A=B"
      if "?R A x" "?R B y" for A B x y
      using old_identity that by blast
    have unequal: "(141,Pair_Term x y)\<in>positive_meaning generation_value_system \<longleftrightarrow> A\<noteq>B"
      if "?R A x" "?R B y" for A B x y
      using old_difference that by blast
    have predecessor_identity: "(145,Pair_Term b f)\<in>positive_meaning generation_value_system \<longleftrightarrow> P=Q"
      using generation_bags.comparison_collections[OF left_read right_read equal] by (simp add: fset_inject)
    have predecessor_difference: "(146,Pair_Term b f)\<in>positive_meaning generation_value_system \<longleftrightarrow> P\<noteq>Q"
      using generation_bags.difference_collections[OF left_read right_read equal unequal] by (simp add: fset_inject)
    have admitted:
      "(139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system"
      "(139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system"
      using admission[OF bounds(1)] admission[OF bounds(2)] left right first(1) second(1) by blast+
    have equal_targets:
      "(135,Pair_Term a e)\<in>positive_meaning generation_value_system \<longleftrightarrow> l=l'"
      "(135,Pair_Term c g)\<in>positive_meaning generation_value_system \<longleftrightarrow> p=p'"
      "(135,Pair_Term d h)\<in>positive_meaning generation_value_system \<longleftrightarrow> q=q'"
      using target_identity_contract.at[OF first(2) second(2)] target_identity_contract.at[OF first(4) second(4)]
        target_identity_contract.at[OF first(5) second(5)] by (simp_all only: generation_value_components)
    have unequal_targets:
      "(136,Pair_Term a e)\<in>positive_meaning generation_value_system \<longleftrightarrow> l\<noteq>l'"
      "(136,Pair_Term c g)\<in>positive_meaning generation_value_system \<longleftrightarrow> p\<noteq>p'"
      "(136,Pair_Term d h)\<in>positive_meaning generation_value_system \<longleftrightarrow> q\<noteq>q'"
      using target_difference_contract.at[OF first(2) second(2)] target_difference_contract.at[OF first(4) second(4)]
        target_difference_contract.at[OF first(5) second(5)] by (simp_all only: generation_value_components)
    show ?thesis by (simp only: first(1) second(1) core other generation_identity_fields generation_difference_fields
      admitted equal_targets unequal_targets predecessor_identity predecessor_difference generation_core.inject; blast)
  qed
  show ?case using admission comparison by blast
qed

section \<open>Every finite generation presentation is admitted and compared exactly\<close>

theorem generation_admission_exact:
  "(139,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> (\<exists>G. generation_value_presents G t)"
  using generation_value_bounded_contracts[of "Suc (term_height t)"] by auto

theorem generation_identity_on_values:
  assumes "generation_value_presents G p" "generation_value_presents H q"
  shows "(140,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G=H"
  using generation_value_bounded_contracts[of "Suc (max (term_height p) (term_height q))"] assms by auto

theorem generation_difference_on_values:
  assumes "generation_value_presents G p" "generation_value_presents H q"
  shows "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
  using generation_value_bounded_contracts[of "Suc (max (term_height p) (term_height q))"] assms by auto

text \<open>
  Admission and both comparisons are proved together. At each bound, the
  predecessor presentations lie strictly below their enclosing value. Their
  established comparison contracts admit exactly a finite set of distinct
  cores. The four admitted fields then recover the parent core. Comparisons
  at that bound use the newly established admission and the smaller-core
  comparison equations through the generic bag theorems.

  Every finite term lies below a bound. The resulting equations cover every
  term and every presentation of every formed core. Bounds and their temporary
  presentation constraints occur only in the proof. They select neither an
  operative depth limit nor a stored field, enumeration, or representative.
  The cause remains a recorded target; these value operations do not judge
  whether its account is valid.
\<close>

end
