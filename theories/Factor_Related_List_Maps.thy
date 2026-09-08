theory Factor_Related_List_Maps
  imports Factor_Related_Lists Factor_Presentation_Classes Presentation_Contract_Constructions
begin

section \<open>The sequence encoding preserves the general relation lifting\<close>

lemma data_sequence_relation_lifting:
  "presented_relation (data_sequence_presents R) (data_sequence_presents S) (list_all2 L) p q \<longleftrightarrow>
    (\<exists>ps qs. p=data_list_term ps \<and> q=data_list_term qs \<and>
      list_all2 (presented_relation R S L) ps qs)"
proof -
  have first: "data_sequence_presents R=composed_presentation (list_all2 R) (\<lambda>ps t. t=data_list_term ps)"
    by (intro ext) (simp add: data_sequence_presents_def composed_presentation_def)
  have second: "data_sequence_presents S=composed_presentation (list_all2 S) (\<lambda>qs t. t=data_list_term qs)"
    by (intro ext) (simp add: data_sequence_presents_def composed_presentation_def)
  show ?thesis by (simp only: first second presented_relation_change presented_relation_lists; blast)
qed

section \<open>The existing traversal exports complete lifted contracts\<close>

context related_list_profile
begin

theorem presented_contract:
  assumes formed: "term_formed a"
    and element: "presented_relation_contract R D A S E B L (related a)"
  shows "presented_relation_contract (data_sequence_presents R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
    (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. A x) \<and> p=data_list_term ps)
    (data_sequence_presents S) (\<lambda>ys. \<forall>y\<in>set ys. E y)
    (\<lambda>q. \<exists>qs. (\<forall>y\<in>set qs. B y) \<and> q=data_list_term qs)
    (list_all2 L) (\<lambda>p q. (list_site,context_relation_argument a p q)\<in>positive_meaning P)"
proof -
  interpret element: presented_relation_contract R D A S E B L "related a" by (rule element)
  have meaning: "(list_site,context_relation_argument a p q)\<in>positive_meaning P \<longleftrightarrow>
      presented_relation (data_sequence_presents R) (data_sequence_presents S) (list_all2 L) p q" for p q
    using formed by (auto simp: exact data_sequence_relation_lifting element.exact[abs_def])
  show ?thesis using data_sequence_presentation_class[OF element.left.presentation_class_axioms]
    data_sequence_presentation_class[OF element.right.presentation_class_axioms] meaning
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem presented_mapping_contract:
  assumes formed: "term_formed a"
    and element: "presented_function_contract R D A S E B f (related a)"
  shows "presented_function_contract (data_sequence_presents R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
    (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. A x) \<and> p=data_list_term ps)
    (data_sequence_presents S) (\<lambda>ys. \<forall>y\<in>set ys. E y)
    (\<lambda>q. \<exists>qs. (\<forall>y\<in>set qs. B y) \<and> q=data_list_term qs)
    (map f) (\<lambda>p q. (list_site,context_relation_argument a p q)\<in>positive_meaning P)"
proof -
  interpret element: presented_function_contract R D A S E B f "related a" by (rule element)
  have relation: "presented_relation_contract (data_sequence_presents R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
      (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. A x) \<and> p=data_list_term ps)
      (data_sequence_presents S) (\<lambda>ys. \<forall>y\<in>set ys. E y)
      (\<lambda>q. \<exists>qs. (\<forall>y\<in>set qs. B y) \<and> q=data_list_term qs)
      (\<lambda>xs ys. ys=map f xs) (\<lambda>p q. (list_site,context_relation_argument a p q)\<in>positive_meaning P)"
    using presented_contract[OF formed element.presented_relation_contract_axioms]
    by (simp only: list_relation_function[abs_def])
  show ?thesis using relation element.image_boundary
    by (auto simp: presented_function_contract_def presented_function_contract_axioms_def)
qed

corollary presented_mapping_output:
  assumes "term_formed a" "presented_function_contract R D A S E B f (related a)"
    "data_sequence_presents R xs p"
  shows "(list_site,context_relation_argument a p q)\<in>positive_meaning P \<longleftrightarrow>
    data_sequence_presents S (map f xs) q"
  by (rule presented_function_contract.output[OF presented_mapping_contract[OF assms(1,2)] assms(3)])

section \<open>An encoded input can determine its output on its local domain\<close>

theorem encoded_input:
  assumes formed: "term_formed a"
    and element: "\<And>x y. x\<in>set xs \<Longrightarrow> related a (f x) y \<longleftrightarrow> y=g x"
  shows "(list_site,context_relation_argument a (data_list_term (map f xs)) q)\<in>positive_meaning P
    \<longleftrightarrow> q=data_list_term (map g xs)"
proof -
  have correspondence: "list_all2 (related a) (map f xs) ys \<longleftrightarrow> ys=map g xs" for ys
    using element
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    have first: "related a (f x) y \<longleftrightarrow> y=g x" for y
      using Cons.prems by simp
    have rest: "list_all2 (related a) (map f xs) zs \<longleftrightarrow> zs=map g xs" for zs
      by (rule Cons.IH) (use Cons.prems in auto)
    show ?case by (cases ys) (simp_all add: first rest)
  qed
  show ?thesis using formed
    by (auto simp: exact data_list_term_injective correspondence)
qed

end

text \<open>
  The existing two-clause correspondence traversal supplies these contracts.
  The general relation lifting accounts for the whole sequence relation before
  the complete term encoding is applied. The native element callee supplies
  one owned contract. Function graphs then give sequence maps, admitting every
  complete output presentation without requiring an injective function.

  For a fixed encoded input, the local element equations can instead determine
  an exact output term. Both forms preserve order, length, and every repeated
  element. Neither proof revisits the native traversal's recursive semantics.

  The context is formed even for an empty list. This theorem adds no context
  admission premise to the existing clauses. A public operation that needs
  a stronger context boundary must establish it through its own actual calls.
\<close>

end
