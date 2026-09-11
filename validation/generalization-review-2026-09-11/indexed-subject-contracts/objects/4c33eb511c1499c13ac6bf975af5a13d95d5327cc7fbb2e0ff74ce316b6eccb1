theory Factor_Product_Contracts
  imports Factor_Presentation_Transport Presentation_Contract_Constructions
begin

section \<open>Independent relation contracts pass through the pair constructor\<close>

lemma factor_pair_relation_lifting:
  "presented_relation (factor_pair_presents R T) (factor_pair_presents S U)
      (\<lambda>a b. L (fst a) (fst b) \<and> M (snd a) (snd b)) p q \<longleftrightarrow>
    (\<exists>x y z w. p=Pair_Term x y \<and> q=Pair_Term z w \<and>
      presented_relation R S L x z \<and> presented_relation T U M y w)"
  by (auto simp: factor_pair_presents_def presented_relation_def; metis fst_conv snd_conv)


lemma factor_pair_identity_lifting:
  "presented_relation (factor_pair_presents R S) (factor_pair_presents R S) (=) p q \<longleftrightarrow>
    (\<exists>a b c d. p=Pair_Term a b \<and> q=Pair_Term c d \<and>
      presented_relation R R (=) a c \<and> presented_relation S S (=) b d)"
proof -
  have identity: "(\<lambda>x y. fst x=fst y \<and> snd x=snd y)=(=)"
    by (intro ext) (simp only: prod_eq_iff)
  show ?thesis using factor_pair_relation_lifting[where R=R and S=R and T=S and U=S and L="(=)" and M="(=)"]
    by (simp only: identity)
qed

theorem factor_pair_relation_contract:
  assumes first: "presented_relation_contract R D A S E B L run"
    and second: "presented_relation_contract T F C U G K M step"
  shows "presented_relation_contract (factor_pair_presents R T)
    (\<lambda>a. D (fst a) \<and> F (snd a))
    (\<lambda>p. \<exists>x y. p=Pair_Term x y \<and> A x \<and> C y)
    (factor_pair_presents S U) (\<lambda>b. E (fst b) \<and> G (snd b))
    (\<lambda>q. \<exists>z w. q=Pair_Term z w \<and> B z \<and> K w)
    (\<lambda>a b. L (fst a) (fst b) \<and> M (snd a) (snd b))
    (\<lambda>p q. \<exists>x y z w. p=Pair_Term x y \<and> q=Pair_Term z w \<and> run x z \<and> step y w)"
proof -
  interpret first: presented_relation_contract R D A S E B L run by (rule first)
  interpret second: presented_relation_contract T F C U G K M step by (rule second)
  have left: "presentation_class (factor_pair_presents R T)
      (\<lambda>a. D (fst a) \<and> F (snd a))
      (\<lambda>p. \<exists>x y. p=Pair_Term x y \<and> A x \<and> C y)"
    using factor_pair_class[OF first.left.presentation_class_axioms second.left.presentation_class_axioms]
    by (simp only: conj_assoc conj_commute conj_left_commute)
  have right: "presentation_class (factor_pair_presents S U)
      (\<lambda>b. E (fst b) \<and> G (snd b))
      (\<lambda>q. \<exists>z w. q=Pair_Term z w \<and> B z \<and> K w)"
    using factor_pair_class[OF first.right.presentation_class_axioms second.right.presentation_class_axioms]
    by (simp only: conj_assoc conj_commute conj_left_commute)
  show ?thesis using left right
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def
      factor_pair_relation_lifting first.exact second.exact)
qed

theorem factor_pair_function_contract:
  assumes first: "presented_function_contract R D A S E B f run"
    and second: "presented_function_contract T F C U G K g step"
  shows "presented_function_contract (factor_pair_presents R T)
    (\<lambda>a. D (fst a) \<and> F (snd a))
    (\<lambda>p. \<exists>x y. p=Pair_Term x y \<and> A x \<and> C y)
    (factor_pair_presents S U) (\<lambda>b. E (fst b) \<and> G (snd b))
    (\<lambda>q. \<exists>z w. q=Pair_Term z w \<and> B z \<and> K w)
    (map_prod f g)
    (\<lambda>p q. \<exists>x y z w. p=Pair_Term x y \<and> q=Pair_Term z w \<and> run x z \<and> step y w)"
proof -
  interpret first: presented_function_contract R D A S E B f run by (rule first)
  interpret second: presented_function_contract T F C U G K g step by (rule second)
  have graph: "(fst b=f (fst a) \<and> snd b=g (snd a)) \<longleftrightarrow> b=map_prod f g a" for a b
    by (cases a; cases b) auto
  show ?thesis
    using factor_pair_relation_contract[OF first.presented_relation_contract_axioms
      second.presented_relation_contract_axioms] first.image_boundary second.image_boundary
    by (simp only: graph presented_function_contract_def presented_function_contract_axioms_def)
      (auto simp: map_prod_def)
qed

text \<open>
  The pair constructor presents the ordinary product. Its relation lifting
  keeps the two component relations independent, and function graphs supply
  the product map. Each use consumes only the two component contracts; their
  internal presentation and implementation proofs remain local to them.
\<close>

end
