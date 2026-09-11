theory Presentation_Contract_Constructions
  imports Presentation_Contracts
begin

section \<open>Recognizing a contract separates meaning from its admission boundary\<close>

theorem presented_relation_contract_recognition:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
  shows "presented_relation_contract R D A S E B L observe \<longleftrightarrow>
    (\<forall>p q. observe p q \<longrightarrow> A p \<and> B q) \<and>
    rel_fun R (rel_fun S (=)) L observe"
proof
  assume contract: "presented_relation_contract R D A S E B L observe"
  interpret contract: presented_relation_contract R D A S E B L observe by (rule contract)
  show "(\<forall>p q. observe p q \<longrightarrow> A p \<and> B q) \<and>
      rel_fun R (rel_fun S (=)) L observe"
    using contract.boundaries contract.at by (auto simp: rel_fun_def)
next
  assume evidence: "(\<forall>p q. observe p q \<longrightarrow> A p \<and> B q) \<and>
    rel_fun R (rel_fun S (=)) L observe"
  interpret left: presentation_class R D A by (rule left)
  interpret right: presentation_class S E B by (rule right)
  have agreement: "rel_fun R (rel_fun S (=)) L observe" using evidence by blast
  have exact: "observe p q \<longleftrightarrow> presented_relation R S L p q" for p q
  proof
    assume checked: "observe p q"
    have admitted: "A p" "B q" using evidence checked by blast+
    obtain a b where reads: "R a p" "S b q"
      using left.admitted[OF admitted(1)] right.admitted[OF admitted(2)] by blast
    have same: "L a b=observe p q"
      by (rule rel_funD[OF rel_funD[OF agreement reads(1)] reads(2)])
    show "presented_relation R S L p q"
      using reads checked same by (auto simp: presented_relation_def)
  next
    assume presented: "presented_relation R S L p q"
    obtain a b where reads: "R a p" "S b q" and link: "L a b"
      using presented by (auto simp: presented_relation_def)
    have same: "L a b=observe p q"
      by (rule rel_funD[OF rel_funD[OF agreement reads(1)] reads(2)])
    show "observe p q" using same link by simp
  qed
  show "presented_relation_contract R D A S E B L observe"
    using left right exact by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem presented_relation_contract_comparison:
  assumes first: "presented_relation_contract R D A S E B L observe"
    and second: "presented_relation_contract R D A S E B M check"
  shows "(\<forall>p q. observe p q \<longrightarrow> check p q) \<longleftrightarrow>
    (\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> L a b \<longrightarrow> M a b)"
proof -
  interpret first: presented_relation_contract R D A S E B L observe by (rule first)
  interpret second: presented_relation_contract R D A S E B M check by (rule second)
  show ?thesis
  proof
    assume implication: "\<forall>p q. observe p q \<longrightarrow> check p q"
    show "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> L a b \<longrightarrow> M a b"
    proof (intro allI impI)
      fix a b assume domain: "D a" "E b" and link: "L a b"
      obtain p q where reads: "R a p" "S b q"
        using first.left.total[OF domain(1)] first.right.total[OF domain(2)] by blast
      show "M a b" using implication link first.at[OF reads] second.at[OF reads] by blast
    qed
  next
    assume implication: "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> L a b \<longrightarrow> M a b"
    show "\<forall>p q. observe p q \<longrightarrow> check p q"
      using implication first.left.subject_boundary first.right.subject_boundary
      by (auto simp: first.exact second.exact presented_relation_def; blast)
  qed
qed

corollary presented_relation_contract_identification:
  assumes first: "presented_relation_contract R D A S E B L observe"
    and second: "presented_relation_contract R D A S E B M check"
  shows "observe=check \<longleftrightarrow>
    (\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> (L a b \<longleftrightarrow> M a b))"
proof -
  have forward: "(\<forall>p q. observe p q \<longrightarrow> check p q) \<longleftrightarrow>
      (\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> L a b \<longrightarrow> M a b)"
    by (rule presented_relation_contract_comparison[OF first second])
  have backward: "(\<forall>p q. check p q \<longrightarrow> observe p q) \<longleftrightarrow>
      (\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> M a b \<longrightarrow> L a b)"
    by (rule presented_relation_contract_comparison[OF second first])
  show ?thesis
  proof
    assume same: "observe=check"
    have one: "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> L a b \<longrightarrow> M a b"
      using forward by (simp add: same)
    have two: "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> M a b \<longrightarrow> L a b"
      using backward by (simp add: same)
    show "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> (L a b \<longleftrightarrow> M a b)"
      using one two by blast
  next
    assume same: "\<forall>a b. D a \<longrightarrow> E b \<longrightarrow> (L a b \<longleftrightarrow> M a b)"
    have one: "\<forall>p q. observe p q \<longrightarrow> check p q" using forward same by blast
    have two: "\<forall>p q. check p q \<longrightarrow> observe p q" using backward same by blast
    show "observe=check" by (intro ext) (use one two in blast)
  qed
qed


section \<open>Relational constructions lift whole classes of contracts\<close>

lemma presented_relation_composition_form:
  "presented_relation R S L = (conversep R OO L OO S)"
  by (intro ext) (auto simp: presented_relation_def relcompp_apply)

theorem presented_relation_lists:
  "presented_relation (list_all2 R) (list_all2 S) (list_all2 L) ps qs \<longleftrightarrow>
    list_all2 (presented_relation R S L) ps qs"
proof -
  have converse: "conversep (list_all2 R)=list_all2 (conversep R)"
    by (intro ext) (auto simp: list_all2_conv_all_nth)
  show ?thesis by (simp only: presented_relation_composition_form list.rel_compp converse)
qed

theorem presented_relation_contract_lists:
  assumes element: "presented_relation_contract R D A S E B L observe"
  shows "presented_relation_contract (list_all2 R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
    (\<lambda>ps. \<forall>p\<in>set ps. A p)
    (list_all2 S) (\<lambda>ys. \<forall>y\<in>set ys. E y) (\<lambda>qs. \<forall>q\<in>set qs. B q)
    (list_all2 L) (list_all2 observe)"
proof -
  interpret element: presented_relation_contract R D A S E B L observe by (rule element)
  have exact: "list_all2 observe ps qs \<longleftrightarrow>
      presented_relation (list_all2 R) (list_all2 S) (list_all2 L) ps qs" for ps qs
    by (simp only: presented_relation_lists element.exact[abs_def])
  show ?thesis using element.left.lists element.right.lists exact
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem presented_relation_contract_product:
  assumes first: "presented_relation_contract R D A S E B L observe"
    and second: "presented_relation_contract T F C U G K M check"
  shows "presented_relation_contract
    (\<lambda>z p. R (fst z) (fst p) \<and> T (snd z) (snd p))
    (\<lambda>z. D (fst z) \<and> F (snd z)) (\<lambda>p. A (fst p) \<and> C (snd p))
    (\<lambda>z q. S (fst z) (fst q) \<and> U (snd z) (snd q))
    (\<lambda>z. E (fst z) \<and> G (snd z)) (\<lambda>q. B (fst q) \<and> K (snd q))
    (\<lambda>z w. L (fst z) (fst w) \<and> M (snd z) (snd w))
    (\<lambda>p q. observe (fst p) (fst q) \<and> check (snd p) (snd q))"
proof -
  interpret first: presented_relation_contract R D A S E B L observe by (rule first)
  interpret second: presented_relation_contract T F C U G K M check by (rule second)
  have left: "presentation_class (\<lambda>z p. R (fst z) (fst p) \<and> T (snd z) (snd p))
      (\<lambda>z. D (fst z) \<and> F (snd z)) (\<lambda>p. A (fst p) \<and> C (snd p))"
    by (rule presentation_class_product[OF first.left.presentation_class_axioms second.left.presentation_class_axioms])
  have right: "presentation_class (\<lambda>z q. S (fst z) (fst q) \<and> U (snd z) (snd q))
      (\<lambda>z. E (fst z) \<and> G (snd z)) (\<lambda>q. B (fst q) \<and> K (snd q))"
    by (rule presentation_class_product[OF first.right.presentation_class_axioms second.right.presentation_class_axioms])
  show ?thesis unfolding presented_relation_contract_recognition[OF left right]
    using first.boundaries second.boundaries first.at second.at by (auto simp: rel_fun_def)
qed

section \<open>Determined operations inherit the same constructions\<close>

lemma list_relation_function:
  "list_all2 (\<lambda>a b. b=f a) xs ys \<longleftrightarrow> ys=map f xs"
  by (induction xs arbitrary: ys) (auto simp: list_all2_Cons1)

theorem presented_function_contract_lists:
  assumes element: "presented_function_contract R D A S E B f operation"
  shows "presented_function_contract (list_all2 R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
    (\<lambda>ps. \<forall>p\<in>set ps. A p)
    (list_all2 S) (\<lambda>ys. \<forall>y\<in>set ys. E y) (\<lambda>qs. \<forall>q\<in>set qs. B q)
    (map f) (list_all2 operation)"
proof -
  interpret element: presented_function_contract R D A S E B f operation by (rule element)
  have relation: "presented_relation_contract (list_all2 R) (\<lambda>xs. \<forall>x\<in>set xs. D x)
      (\<lambda>ps. \<forall>p\<in>set ps. A p)
      (list_all2 S) (\<lambda>ys. \<forall>y\<in>set ys. E y) (\<lambda>qs. \<forall>q\<in>set qs. B q)
      (\<lambda>xs ys. ys=map f xs) (list_all2 operation)"
    using presented_relation_contract_lists[OF element.presented_relation_contract_axioms]
    by (simp only: list_relation_function[abs_def])
  show ?thesis using relation element.image_boundary
    by (auto simp: presented_function_contract_def presented_function_contract_axioms_def)
qed

theorem presented_function_contract_pair:
  assumes first: "presented_function_contract R D A S E B f run"
    and second: "presented_function_contract R D A T F C g step"
  shows "presented_function_contract R D A
    (\<lambda>z q. S (fst z) (fst q) \<and> T (snd z) (snd q))
    (\<lambda>z. E (fst z) \<and> F (snd z)) (\<lambda>q. B (fst q) \<and> C (snd q))
    (\<lambda>a. (f a,g a)) (\<lambda>p q. run p (fst q) \<and> step p (snd q))"
proof -
  interpret first: presented_function_contract R D A S E B f run by (rule first)
  interpret second: presented_function_contract R D A T F C g step by (rule second)
  have pair: "presentation_class (\<lambda>z q. S (fst z) (fst q) \<and> T (snd z) (snd q))
      (\<lambda>z. E (fst z) \<and> F (snd z)) (\<lambda>q. B (fst q) \<and> C (snd q))"
    by (rule presentation_class_product[OF first.right.presentation_class_axioms second.right.presentation_class_axioms])
  have relation: "presented_relation_contract R D A
      (\<lambda>z q. S (fst z) (fst q) \<and> T (snd z) (snd q))
      (\<lambda>z. E (fst z) \<and> F (snd z)) (\<lambda>q. B (fst q) \<and> C (snd q))
      (\<lambda>a z. z=(f a,g a)) (\<lambda>p q. run p (fst q) \<and> step p (snd q))"
    unfolding presented_relation_contract_recognition[OF first.left.presentation_class_axioms pair]
    using first.boundaries second.boundaries first.at second.at
    by (auto simp: rel_fun_def prod_eq_iff)
  show ?thesis using relation first.image_boundary second.image_boundary
    by (simp add: presented_function_contract_def presented_function_contract_axioms_def)
qed

theorem admitted_agreement_needs_a_boundary:
  "presentation_class (\<lambda>_::unit. \<lambda>p::bool. p) (\<lambda>_. True) id \<and>
    rel_fun (\<lambda>_::unit. \<lambda>p::bool. p) (rel_fun (\<lambda>_::unit. \<lambda>p::bool. p) (=))
      (\<lambda>_ _. True) (\<lambda>_ _. True) \<and>
    \<not>presented_relation_contract (\<lambda>_::unit. \<lambda>p::bool. p) (\<lambda>_. True) id
      (\<lambda>_::unit. \<lambda>p::bool. p) (\<lambda>_. True) id (\<lambda>_ _. True) (\<lambda>_ _. True)"
  by (auto simp: presentation_class_def rel_fun_def presented_relation_contract_def
    presented_relation_contract_axioms_def presented_relation_def)

text \<open>
  A relation between independently fixed subject domains has an exact
  implementation contract precisely when its valid arguments are related
  through the existing higher-order function relation and all successful
  observations stay inside the admitted boundary. The latter condition cannot
  be omitted. Recognition verifies a proposed relationship; it does not select
  the intended subject or infer that meaning from a desired implementation.

  Comparison and identification reduce implications and equalities between
  whole implementations to their independent subject relations. Total coverage
  makes the converse valid, so a subject-level counterexample also prevents
  the corresponding implementation implication. Together with specialization,
  adaptation, and composition, these are reusable criteria for checking and
  comparing proposed decompositions.

  List lifting follows from composition of the standard list relator; product
  lifting combines independent contracts. Functions specialize relations to
  their graphs. Pairing functions reuses one admitted source for both results.
  These rules can be nested: each application uses only its immediate contracts
  and stated domain conditions, regardless of the size of their internal proofs.
  They bound the local rule's obligations, not the number of distinct conditions
  in an arbitrary requirement or the effort of discovering a suitable hierarchy.
\<close>

section \<open>Literal copying has a precise semantic identity boundary\<close>

theorem literal_copy_contract_iff:
  assumes source: "presentation_class R D A"
  shows "presented_function_contract R D A R D A id (\<lambda>p q. A p \<and> q=p) \<longleftrightarrow>
    (\<forall>a p q. R a p \<longrightarrow> R a q \<longrightarrow> p=q)"
proof -
  interpret source: presentation_class R D A by (rule source)
  show ?thesis
  proof
    assume contract: "presented_function_contract R D A R D A id (\<lambda>p q. A p \<and> q=p)"
    interpret copy: presented_function_contract R D A R D A id "\<lambda>p q. A p \<and> q=p" by (rule contract)
    show "\<forall>a p q. R a p \<longrightarrow> R a q \<longrightarrow> p=q"
      using copy.output by auto
  next
    assume unique: "\<forall>a p q. R a p \<longrightarrow> R a q \<longrightarrow> p=q"
    have exact: "(A p \<and> q=p) \<longleftrightarrow> presented_relation R R (\<lambda>a b. b=id a) p q" for p q
      using unique source.admitted source.presentation_boundary
      by (auto simp: presented_relation_def; blast)
    show "presented_function_contract R D A R D A id (\<lambda>p q. A p \<and> q=p)"
      using source exact by (simp add: presented_function_contract_def presented_function_contract_axioms_def
        presented_relation_contract_def presented_relation_contract_axioms_def)
  qed
qed

corollary literal_copy_does_not_represent_all_equivalent_outputs:
  "presentation_class (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>_. True) (\<lambda>_. True) \<and>
    \<not>presented_function_contract (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>_. True) (\<lambda>_. True)
      (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>_. True) (\<lambda>_. True) id (\<lambda>p q. q=p)"
proof -
  have source: "presentation_class (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>_. True) (\<lambda>_. True)"
    by (simp add: presentation_class_def)
  show ?thesis using source literal_copy_contract_iff[OF source]
    by (auto; metis bool.distinct(1))
qed

text \<open>
  Copying preserves an actual presentation. It realizes a complete semantic
  identity contract precisely when each subject has one presentation. This
  criterion applies to stored-value lookup, copied fold seeds, and other
  literal projections. When several forms present the same subject, semantic
  comparison or transport supplies the missing output correspondence.
\<close>

end
