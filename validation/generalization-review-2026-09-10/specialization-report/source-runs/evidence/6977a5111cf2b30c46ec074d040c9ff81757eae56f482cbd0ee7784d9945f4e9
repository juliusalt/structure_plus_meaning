theory Presentation_Contracts
  imports Presentation_Transport
begin

section \<open>An implementation establishes its semantic contract locally\<close>

definition adapted_relation ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'u \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow>
    ('p \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow> 'u \<Rightarrow> 'v \<Rightarrow> bool" where
  "adapted_relation R S U V observe p q \<longleftrightarrow>
    (\<exists>x y. presentation_transport U R p x \<and> observe x y \<and> presentation_transport S V y q)"

locale presented_relation_contract =
  left: presentation_class R D A + right: presentation_class S E B
  for R :: "'a \<Rightarrow> 'p \<Rightarrow> bool" and D A
    and S :: "'b \<Rightarrow> 'q \<Rightarrow> bool" and E B +
  fixes relation :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    and observe :: "'p \<Rightarrow> 'q \<Rightarrow> bool"
  assumes exact: "\<And>p q. observe p q \<longleftrightarrow> presented_relation R S relation p q"
begin

theorem at:
  assumes "R a p" "S b q"
  shows "observe p q \<longleftrightarrow> relation a b"
  by (simp only: exact presented_relation_at[OF left.presentation_class_axioms
      right.presentation_class_axioms assms])

theorem at_source:
  assumes "R a p"
  shows "observe p q \<longleftrightarrow> (\<exists>b. S b q \<and> relation a b)"
  using assms left.recovery by (auto simp: exact presented_relation_def; blast)

lemma boundaries:
  assumes "observe p q"
  shows "A p \<and> B q"
  using assms left.presentation_boundary right.presentation_boundary
  by (auto simp: exact presented_relation_def)

theorem invariance:
  assumes "R a p" "S b q" "R a p'" "S b q'"
  shows "observe p q \<longleftrightarrow> observe p' q'"
  by (simp only: at[OF assms(1,2)] at[OF assms(3,4)])

theorem adaptation_exact:
  assumes other_left: "presentation_class U D X" and other_right: "presentation_class V E Y"
  shows "adapted_relation R S U V observe p q \<longleftrightarrow>
    presented_relation U V relation p q"
proof -
  interpret other_left: presentation_class U D X by (rule other_left)
  interpret other_right: presentation_class V E Y by (rule other_right)
  show ?thesis
  proof
    assume "adapted_relation R S U V observe p q"
    then obtain x y a b where parts: "U a p" "R a x" "observe x y" "S b y" "V b q"
      unfolding adapted_relation_def presentation_transport_def by blast
    have related: "relation a b" using at[OF parts(2,4)] parts(3) by blast
    show "presented_relation U V relation p q"
      using parts(1,5) related unfolding presented_relation_def by blast
  next
    assume "presented_relation U V relation p q"
    then obtain a b where parts: "U a p" "V b q" "relation a b"
      unfolding presented_relation_def by blast
    obtain x where first: "R a x" using left.total[OF other_left.subject_boundary[OF parts(1)]] by blast
    obtain y where second: "S b y" using right.total[OF other_right.subject_boundary[OF parts(2)]] by blast
    have checked: "observe x y" using at[OF first second] parts(3) by blast
    show "adapted_relation R S U V observe p q"
      using parts first second checked unfolding adapted_relation_def presentation_transport_def by blast
  qed
qed

theorem adaptation_contract:
  assumes "presentation_class U D X" "presentation_class V E Y"
  shows "presented_relation_contract U D X V E Y relation (adapted_relation R S U V observe)"
  by (unfold_locales)
    (use assms adaptation_exact[OF assms] in \<open>auto simp: presentation_class_def\<close>)

theorem adaptation_identity:
  "adapted_relation R S R S observe=observe"
  by (intro ext)
    (simp only: adaptation_exact[OF left.presentation_class_axioms right.presentation_class_axioms]
      exact)

theorem adaptation_compose:
  assumes middle_left: "presentation_class U D X" and middle_right: "presentation_class V E Y"
    and last_left: "presentation_class U' D X'" and last_right: "presentation_class V' E Y'"
  shows "adapted_relation U V U' V' (adapted_relation R S U V observe)=
    adapted_relation R S U' V' observe"
proof -
  interpret middle: presented_relation_contract U D X V E Y relation
    "adapted_relation R S U V observe"
    by (rule adaptation_contract[OF middle_left middle_right])
  show ?thesis by (intro ext)
    (simp only: middle.adaptation_exact[OF last_left last_right]
      adaptation_exact[OF last_left last_right])
qed

theorem specialization_contract:
  assumes boundary: "\<And>a. K a \<Longrightarrow> D a"
  shows "presented_relation_contract (\<lambda>a p. K a \<and> R a p) K
    (presented_predicate R K) S E B relation
    (\<lambda>p q. presented_predicate R K p \<and> observe p q)"
proof -
  have specialized: "presentation_class (\<lambda>a p. K a \<and> R a p) K (presented_predicate R K)"
    using presentation_class_subdomain[OF left.presentation_class_axioms boundary]
    by (simp only: presentation_class_def presented_predicate_def conj_commute)
  have meaning: "(presented_predicate R K p \<and> observe p q) \<longleftrightarrow>
      presented_relation (\<lambda>a p. K a \<and> R a p) S relation p q" for p q
    using left.recovery by (auto simp: exact presented_relation_def presented_predicate_def; blast)
  show ?thesis by (unfold_locales)
    (use specialized right.presentation_class_axioms meaning in
      \<open>auto simp: presentation_class_def\<close>)
qed

end

section \<open>Clients compose exported contracts across intermediate classes\<close>

theorem presented_relation_contract_compose:
  assumes first: "presented_relation_contract R D A S E B L f"
    and second: "presented_relation_contract T E C U F K M g"
  shows "presented_relation_contract R D A U F K
    (\<lambda>a c. \<exists>b. E b \<and> L a b \<and> M b c)
    (\<lambda>p r. \<exists>q u. f p q \<and> presentation_transport S T q u \<and> g u r)"
proof -
  interpret first: presented_relation_contract R D A S E B L f by (rule first)
  interpret second: presented_relation_contract T E C U F K M g by (rule second)
  have exact: "(\<exists>q u. f p q \<and> presentation_transport S T q u \<and> g u r) \<longleftrightarrow>
      presented_relation R U (\<lambda>a c. \<exists>b. E b \<and> L a b \<and> M b c) p r" for p r
    by (simp only: first.exact second.exact
      presented_relation_compose_across[OF first.right.presentation_class_axioms
        second.left.presentation_class_axioms])
  show ?thesis by (unfold_locales)
    (use first.left.presentation_class_axioms second.right.presentation_class_axioms exact in
      \<open>auto simp: presentation_class_def\<close>)
qed

section \<open>Instantiation is a map between independently specified domains\<close>

locale presented_function_contract =
  presented_relation_contract R D A S E B "\<lambda>a b. b=f a" operation
  for R :: "'a \<Rightarrow> 'p \<Rightarrow> bool" and D A
    and S :: "'b \<Rightarrow> 'q \<Rightarrow> bool" and E B
    and f :: "'a \<Rightarrow> 'b" and operation +
  assumes image_boundary: "\<And>a. D a \<Longrightarrow> E (f a)"
begin

theorem total:
  assumes "A p"
  shows "\<exists>q. operation p q"
  using left.admitted[OF assms] left.subject_boundary image_boundary right.total
  by (auto simp: exact presented_relation_def; blast)

theorem "output":
  assumes "R a p"
  shows "operation p q \<longleftrightarrow> S (f a) q"
  by (simp only: at_source[OF assms]; simp)

theorem output_equivalence:
  assumes "operation p q" "operation p r"
  shows "presentation_transport S S q r"
  using assms left.recovery
  by (auto simp: exact presented_relation_def presentation_transport_def; blast)

end

theorem presentation_identity_function:
  assumes source: "presentation_class R D A" and target: "presentation_class S D B"
  shows "presented_function_contract R D A S D B id (presentation_transport R S)"
  using source target
  by (simp add: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def
    presentation_transport_def presented_relation_def)

theorem presented_function_contract_compose:
  assumes first: "presented_function_contract R D A S E B f run"
    and second: "presented_function_contract T E C U F K g step"
  shows "presented_function_contract R D A U F K (g \<circ> f)
    (\<lambda>p r. \<exists>q u. run p q \<and> presentation_transport S T q u \<and> step u r)"
proof -
  interpret first: presented_function_contract R D A S E B f run by (rule first)
  interpret second: presented_function_contract T E C U F K g step by (rule second)
  have composed: "(\<exists>q u. run p q \<and> presentation_transport S T q u \<and> step u r) \<longleftrightarrow>
      presented_relation R U (\<lambda>a c. \<exists>b. E b \<and> b=f a \<and> c=g b) p r" for p r
    by (simp only: first.exact second.exact
      presented_relation_compose_across[OF first.right.presentation_class_axioms
        second.left.presentation_class_axioms])
  have exact: "(\<exists>q u. run p q \<and> presentation_transport S T q u \<and> step u r) \<longleftrightarrow>
      presented_relation R U (\<lambda>a c. c=(g \<circ> f) a) p r" for p r
  proof (simp only: composed, rule iffI)
    assume "presented_relation R U (\<lambda>a c. \<exists>b. E b \<and> b=f a \<and> c=g b) p r"
    then show "presented_relation R U (\<lambda>a c. c=(g \<circ> f) a) p r"
      by (auto simp: presented_relation_def)
  next
    assume "presented_relation R U (\<lambda>a c. c=(g \<circ> f) a) p r"
    then obtain a c where parts: "R a p" "U c r" "c=(g \<circ> f) a"
      unfolding presented_relation_def by blast
    have domain: "E (f a)" by (rule first.image_boundary[OF first.left.subject_boundary[OF parts(1)]])
    show "presented_relation R U (\<lambda>a c. \<exists>b. E b \<and> b=f a \<and> c=g b) p r"
      by (unfold presented_relation_def, rule exI[of _ a], rule exI[of _ c])
        (use parts domain in auto)
  qed
  have boundary: "D a \<Longrightarrow> F ((g \<circ> f) a)" for a
    using first.image_boundary second.image_boundary by simp
  show ?thesis using first.left.presentation_class_axioms second.right.presentation_class_axioms exact boundary
    by (simp add: presented_function_contract_def presented_function_contract_axioms_def
      presented_relation_contract_def presented_relation_contract_axioms_def)
qed

section \<open>Intrinsic links belong to the complete joint subject\<close>

theorem presentation_class_linked:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
  shows "presentation_class
    (\<lambda>z p. (R (fst z) (fst p) \<and> S (snd z) (snd p)) \<and> L (fst z) (snd z))
    (\<lambda>z. (D (fst z) \<and> E (snd z)) \<and> L (fst z) (snd z))
    (\<lambda>p. presented_relation R S L (fst p) (snd p))"
proof -
  interpret left: presentation_class R D A by (rule left)
  interpret right: presentation_class S E B by (rule right)
  let ?read="\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p)"
  let ?domain="\<lambda>z. (D (fst z) \<and> E (snd z)) \<and> L (fst z) (snd z)"
  have pairs: "presentation_class ?read (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>p. A (fst p) \<and> B (snd p))"
    by (rule presentation_class_product[OF left right])
  have restricted: "presentation_class (\<lambda>z p. ?domain z \<and> ?read z p) ?domain
      (\<lambda>p. \<exists>z. ?domain z \<and> ?read z p)"
    by (rule presentation_class_subdomain[OF pairs]) simp
  have reading: "(\<lambda>z p. ?domain z \<and> ?read z p)=
      (\<lambda>z p. ?read z p \<and> L (fst z) (snd z))"
    by (intro ext) (use left.subject_boundary right.subject_boundary in blast)
  have admission: "(\<lambda>p. \<exists>z. ?domain z \<and> ?read z p)=
      (\<lambda>p. presented_relation R S L (fst p) (snd p))"
    by (rule ext)
      (use left.subject_boundary right.subject_boundary in
        \<open>auto simp: presented_relation_def; metis fst_conv snd_conv\<close>)
  show ?thesis using restricted by (simp only: reading admission)
qed

theorem presentation_linked_join:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
    and joint: "presentation_class J
      (\<lambda>z. (D (fst z) \<and> E (snd z)) \<and> L (fst z) (snd z)) C"
    and inputs: "R a p" "S b q" "L a b"
  shows "\<exists>w. J (a,b) w \<and>
    presentation_transport
      (\<lambda>z p. (R (fst z) (fst p) \<and> S (snd z) (snd p)) \<and> L (fst z) (snd z))
      J (p,q) w"
proof -
  interpret left: presentation_class R D A by (rule left)
  interpret right: presentation_class S E B by (rule right)
  interpret joint: presentation_class J
    "\<lambda>z. (D (fst z) \<and> E (snd z)) \<and> L (fst z) (snd z)" C by (rule joint)
  have domain: "(D (fst (a,b)) \<and> E (snd (a,b))) \<and> L (fst (a,b)) (snd (a,b))"
    using inputs left.subject_boundary right.subject_boundary by auto
  obtain w where read: "J (a,b) w" using joint.total[OF domain] by blast
  show ?thesis by (rule exI[of _ w])
    (use read inputs in \<open>auto simp: presentation_transport_def; metis fst_conv snd_conv\<close>)
qed

section \<open>Representation observations need an independently justified meaning\<close>

context presentation_class
begin

theorem observation_factorization:
  "(\<exists>P. observe=presented_predicate presents P) \<longleftrightarrow>
    (\<forall>p. observe p \<longrightarrow> admissible p) \<and>
    (\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> (observe p \<longleftrightarrow> observe q))"
proof
  assume "\<exists>P. observe=presented_predicate presents P"
  then obtain P where meaning: "observe=presented_predicate presents P" by blast
  show "(\<forall>p. observe p \<longrightarrow> admissible p) \<and>
    (\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> (observe p \<longleftrightarrow> observe q))"
    using presentation_boundary recovery by (auto simp: meaning presented_predicate_def; blast)
next
  assume conditions: "(\<forall>p. observe p \<longrightarrow> admissible p) \<and>
    (\<forall>a p q. presents a p \<longrightarrow> presents a q \<longrightarrow> (observe p \<longleftrightarrow> observe q))"
  show "\<exists>P. observe=presented_predicate presents P"
  proof (rule exI[of _ "\<lambda>a. \<exists>p. presents a p \<and> observe p"], rule ext)
    fix p
    show "observe p=presented_predicate presents (\<lambda>a. \<exists>q. presents a q \<and> observe q) p"
    proof
      assume holds: "observe p"
      have allowed: "admissible p" using conditions holds by blast
      obtain a where read: "presents a p" using admitted[OF allowed] by blast
      show "presented_predicate presents (\<lambda>a. \<exists>q. presents a q \<and> observe q) p"
        using read holds unfolding presented_predicate_def by blast
    next
      assume "presented_predicate presents (\<lambda>a. \<exists>q. presents a q \<and> observe q) p"
      then obtain a q where parts: "presents a p" "presents a q" "observe q"
        unfolding presented_predicate_def by blast
      show "observe p" using conditions parts by blast
    qed
  qed
qed

end

theorem class_recovery_does_not_supply_semantic_observations:
  "presentation_class (\<lambda>_::unit. \<lambda>_::bool. True) (\<lambda>_. True) (\<lambda>_. True) \<and>
    \<not>(\<exists>P. id=presented_predicate (\<lambda>_::unit. \<lambda>_::bool. True) P)"
  by (auto simp: presentation_class_def presented_predicate_def fun_eq_iff)

text \<open>
  An independently defined notion, or an intrinsically linked group, owns its
  subject domain and semantic relations. Each implementation establishes the
  class and exact relation contract there. Adaptation and composition derive
  meaning transport for clients from those exported contracts. Function
  contracts specialize this rule to an independently stated map: every
  admitted input has outputs, and all outputs recover the same value.

  A linked pair uses its intrinsic relation as part of the complete subject
  domain. Every pair of component presentations of those linked subjects is
  available in the logical product. A separately exact physical joint class
  then supplies a presentation for every such input by its own coverage
  contract. This does not assert literal gluing of the supplied material.
  More general groups can be specified together without a product decomposition.

  The factorization criterion detects observations that depend on a discarded
  presentation feature. It does not define a notion from a client's desired
  test, or prove that the resulting predicate is the intended one. An actual
  source, body, or occurrence remains part of the declared subject whenever
  an intrinsic relation observes it. Coverage and recovery alone do not settle
  that boundary; the counterexample isolates this limitation.
\<close>

end
