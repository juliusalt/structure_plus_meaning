theory Presentation_Equivariance
  imports Presentation_Contracts Presentation_Closure Observation_Invariance "HOL-Library.FSet"
begin

section \<open>A group of renamings acts on a class's subjects\<close>

text \<open>
  A renaming is a permutation of a coordinate type admitted by an admissibility closed under
  identity, composition and inverse; it acts on the subjects of a domain, the identity acting as the
  identity and a composition as the composition of the actions. Non-nominality in the renamed
  coordinates is equivariance under this action, stated once here for any presented relation.
\<close>

locale renaming_action =
  fixes admissible :: "('c \<Rightarrow> 'c) \<Rightarrow> bool"
    and act :: "('c \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'a"
    and domain :: "'a \<Rightarrow> bool"
  assumes admissible_bij: "admissible h \<Longrightarrow> bij h"
    and admissible_id: "admissible id"
    and admissible_comp: "admissible g \<Longrightarrow> admissible h \<Longrightarrow> admissible (g \<circ> h)"
    and admissible_inv: "admissible h \<Longrightarrow> admissible (inv h)"
    and act_domain: "admissible h \<Longrightarrow> domain a \<Longrightarrow> domain (act h a)"
    and act_id: "domain a \<Longrightarrow> act id a = a"
    and act_comp: "admissible g \<Longrightarrow> admissible h \<Longrightarrow> domain a \<Longrightarrow> act (g \<circ> h) a = act g (act h a)"
begin

lemma act_inverse:
  assumes h: "admissible h" and a: "domain a"
  shows "act (inv h) (act h a) = a"
proof -
  have composed: "act (inv h) (act h a) = act (inv h \<circ> h) a"
    by (rule act_comp[OF admissible_inv[OF h] h a, symmetric])
  have "inv h \<circ> h = id"
    using inv_f_f[OF bij_is_inj[OF admissible_bij[OF h]]] by (simp add: fun_eq_iff)
  then show ?thesis using composed act_id[OF a] by simp
qed

lemma act_inverse_right:
  assumes h: "admissible h" and a: "domain a"
  shows "act h (act (inv h) a) = a"
proof -
  have composed: "act h (act (inv h) a) = act (h \<circ> inv h) a"
    by (rule act_comp[OF h admissible_inv[OF h] a, symmetric])
  have "h \<circ> inv h = id"
    using surj_f_inv_f[OF bij_is_surj[OF admissible_bij[OF h]]] by (simp add: fun_eq_iff)
  then show ?thesis using composed act_id[OF a] by simp
qed

lemma act_inject:
  assumes h: "admissible h" and a: "domain a" and b: "domain b"
  shows "act h a = act h b \<longleftrightarrow> a = b"
  by (metis act_inverse[OF h a] act_inverse[OF h b])

theorem act_bij:
  assumes h: "admissible h"
  shows "bij_betw (act h) {a. domain a} {a. domain a}"
  unfolding bij_betw_def
proof
  show "inj_on (act h) {a. domain a}"
    by (rule inj_on_inverseI[where g="act (inv h)"]) (simp add: act_inverse[OF h])
  show "act h ` {a. domain a} = {a. domain a}"
  proof
    show "act h ` {a. domain a} \<subseteq> {a. domain a}" using act_domain[OF h] by blast
    show "{a. domain a} \<subseteq> act h ` {a. domain a}"
    proof
      fix b assume "b \<in> {a. domain a}"
      then have b: "domain b" by simp
      have preimage: "b = act h (act (inv h) b)" by (rule act_inverse_right[OF h b, symmetric])
      have "domain (act (inv h) b)" by (rule act_domain[OF admissible_inv[OF h] b])
      then show "b \<in> act h ` {a. domain a}" using preimage by blast
    qed
  qed
qed

text \<open>Subjects with no renamed coordinate take the trivial action, at the same group.\<close>

lemma trivial_action: "renaming_action admissible (\<lambda>h a. a) E"
  by unfold_locales (simp_all add: admissible_bij admissible_id admissible_comp admissible_inv)

end

theorem permutation_renaming_action: "renaming_action bij (\<lambda>h a. a) D"
  by unfold_locales (auto intro: bij_comp bij_imp_bij_inv)

text \<open>
  Permutations and not injections: an injection of finitely many coordinates is the restriction of a
  permutation, so a renaming of the finitely many coordinates a formed subject holds is one of the
  group's.
\<close>

theorem finite_injection_permutation:
  fixes f :: "'c \<Rightarrow> 'c"
  assumes finite: "finite A" and injective: "inj_on f A"
  shows "\<exists>h. bij h \<and> (\<forall>x\<in>A. h x = f x)"
  using finite injective
proof (induction A rule: finite_induct)
  case empty
  show ?case using bij_id by blast
next
  case (insert x A)
  have smaller: "inj_on f A" using insert.prems by (rule inj_on_subset) auto
  obtain h where h: "bij h" "\<forall>a\<in>A. h a = f a" using insert.IH[OF smaller] by blast
  have fresh: "f x \<notin> f ` A" using insert.prems insert.hyps(2) unfolding inj_on_def by blast
  define s where "s = (\<lambda>w. if w = f x then h x else if w = h x then f x else w)"
  have involution: "s \<circ> s = id" by (auto simp: s_def fun_eq_iff)
  have swap: "bij s" by (rule o_bij[OF involution involution])
  show ?case
  proof (rule exI[of _ "s \<circ> h"], intro conjI ballI)
    show "bij (s \<circ> h)" by (rule bij_comp[OF h(1) swap])
  next
    fix a assume a: "a \<in> insert x A"
    show "(s \<circ> h) a = f a"
    proof (cases "a = x")
      case True
      then show ?thesis by (auto simp: s_def)
    next
      case False
      then have old: "a \<in> A" using a by simp
      have fa: "h a = f a" using h(2) old by blast
      have "h a \<noteq> h x" using False bij_is_inj[OF h(1)] by (auto dest: injD)
      then have other: "f a \<noteq> h x" using fa by simp
      have "f a \<noteq> f x" using fresh old by (metis image_eqI)
      then show ?thesis using fa other by (simp add: s_def)
    qed
  qed
qed

section \<open>Equivariance and the renaming correspondence\<close>

definition renaming_equivariant ::
    "(('c \<Rightarrow> 'c) \<Rightarrow> bool) \<Rightarrow> (('c \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "renaming_equivariant admissible act D P \<longleftrightarrow>
    (\<forall>h a. admissible h \<longrightarrow> D a \<longrightarrow> (P (act h a) \<longleftrightarrow> P a))"

definition renaming_correspondence ::
    "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> (('c \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "renaming_correspondence R act h p q \<longleftrightarrow> (\<exists>a. R a p \<and> R (act h a) q)"

text \<open>
  One renaming acts on all of a relation's arguments: a relation is a predicate on the product of its
  subjects under the product action.
\<close>

definition product_action ::
    "(('c \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (('c \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "product_action actL actR h z = (actL h (fst z), actR h (snd z))"

lemma product_action_pair [simp]: "product_action actL actR h (a,b) = (actL h a, actR h b)"
  by (simp add: product_action_def)

lemma renaming_equivariant_relation:
  "renaming_equivariant admissible (product_action actL actR) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>z. Q (fst z) (snd z)) \<longleftrightarrow>
    (\<forall>h a b. admissible h \<longrightarrow> D a \<longrightarrow> E b \<longrightarrow> (Q (actL h a) (actR h b) \<longleftrightarrow> Q a b))"
  by (auto simp: renaming_equivariant_def product_action_def)

text \<open>
  Task 381's part (b), invariance over presentations, is the identity's correspondence: two
  presentations of one subject (@{const presentation_transport}).
\<close>

lemma renaming_correspondence_id:
  assumes presented: "presentation_class R D A" and action: "renaming_action admissible act D"
  shows "renaming_correspondence R act id p q \<longleftrightarrow> presentation_transport R R p q"
proof
  assume "renaming_correspondence R act id p q"
  then obtain a where p: "R a p" and q: "R (act id a) q" unfolding renaming_correspondence_def by blast
  have "act id a = a"
    by (rule renaming_action.act_id[OF action presentation_class.subject_boundary[OF presented p]])
  then show "presentation_transport R R p q" unfolding presentation_transport_def using p q by auto
next
  assume "presentation_transport R R p q"
  then obtain a where p: "R a p" and q: "R a q" unfolding presentation_transport_def by blast
  have "act id a = a"
    by (rule renaming_action.act_id[OF action presentation_class.subject_boundary[OF presented p]])
  then show "renaming_correspondence R act id p q" unfolding renaming_correspondence_def using p q by auto
qed

text \<open>Invariance along every renaming is invariance along every finite path of renamings.\<close>

lemma renaming_invariance_paths:
  "rel_fun (rtranclp (\<lambda>p q. \<exists>h. admissible h \<and> renaming_correspondence R act h p q)) (=) observe observe \<longleftrightarrow>
    (\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe)"
  by (simp only: observation_invariance_closure) (auto simp: rel_fun_def)

section \<open>The notion's contract\<close>

text \<open>
  An observation exact to a presented predicate is invariant along every admissible renaming
  correspondence exactly when the predicate is equivariant on the class's domain; the converse uses
  the class's totality, every subject and every renaming of it being presented.
\<close>

theorem presented_observation_renaming:
  assumes presented: "presentation_class R D A" and action: "renaming_action admissible act D"
    and exact: "\<And>z p. R z p \<Longrightarrow> observe p \<longleftrightarrow> P z"
  shows "(\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe) \<longleftrightarrow>
    renaming_equivariant admissible act D P"
proof
  assume invariant: "\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe"
  show "renaming_equivariant admissible act D P"
    unfolding renaming_equivariant_def
  proof (intro allI impI)
    fix h a assume h: "admissible h" and a: "D a"
    obtain p where p: "R a p" using presentation_class.total[OF presented a] by blast
    have moved: "D (act h a)" by (rule renaming_action.act_domain[OF action h a])
    obtain q where q: "R (act h a) q" using presentation_class.total[OF presented moved] by blast
    have corr: "renaming_correspondence R act h p q" unfolding renaming_correspondence_def using p q by blast
    have same: "observe p = observe q" using invariant h corr by (auto simp: rel_fun_def)
    have left: "observe p \<longleftrightarrow> P a" by (rule exact[OF p])
    have right: "observe q \<longleftrightarrow> P (act h a)" by (rule exact[OF q])
    show "P (act h a) \<longleftrightarrow> P a" using same left right by simp
  qed
next
  assume equivariant: "renaming_equivariant admissible act D P"
  show "\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe"
  proof (intro allI impI)
    fix h assume h: "admissible h"
    show "rel_fun (renaming_correspondence R act h) (=) observe observe"
      unfolding rel_fun_def
    proof (intro allI impI)
      fix p q assume "renaming_correspondence R act h p q"
      then obtain a where p: "R a p" and q: "R (act h a) q" unfolding renaming_correspondence_def by blast
      have a: "D a" by (rule presentation_class.subject_boundary[OF presented p])
      have moved: "P (act h a) \<longleftrightarrow> P a" using equivariant h a unfolding renaming_equivariant_def by blast
      have left: "observe p \<longleftrightarrow> P a" by (rule exact[OF p])
      have right: "observe q \<longleftrightarrow> P (act h a)" by (rule exact[OF q])
      show "observe p = observe q" using moved left right by simp
    qed
  qed
qed

theorem presented_predicate_renaming:
  assumes presented: "presentation_class R D A" and action: "renaming_action admissible act D"
    and exact: "\<And>p. observe p \<longleftrightarrow> presented_predicate R P p"
  shows "(\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe) \<longleftrightarrow>
    renaming_equivariant admissible act D P"
proof (rule presented_observation_renaming[OF presented action])
  fix z p assume z: "R z p"
  show "observe p \<longleftrightarrow> P z"
    using exact[of p] presentation_class.predicate_at[OF presented z, where property=P] by simp
qed

section \<open>Constructions\<close>

subsection \<open>Products: one renaming acts on both components\<close>

theorem renaming_action_product:
  assumes left: "renaming_action admissible actL D" and right: "renaming_action admissible actR E"
  shows "renaming_action admissible (product_action actL actR) (\<lambda>z. D (fst z) \<and> E (snd z))"
proof -
  interpret l: renaming_action admissible actL D by (rule left)
  interpret r: renaming_action admissible actR E by (rule right)
  show ?thesis
    by unfold_locales (auto simp: product_action_def l.admissible_bij l.admissible_id l.admissible_comp
        l.admissible_inv l.act_domain r.act_domain l.act_id r.act_id l.act_comp r.act_comp)
qed

text \<open>A presented relation is its predicate on the product class, one renaming acting on both arguments.\<close>

theorem presented_relation_contract_renaming:
  assumes contract: "presented_relation_contract R D A S E B relation observe"
    and left: "renaming_action admissible actL D" and right: "renaming_action admissible actR E"
  shows "(\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence
      (\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p)) (product_action actL actR) h) (=)
      (\<lambda>p. observe (fst p) (snd p)) (\<lambda>p. observe (fst p) (snd p))) \<longleftrightarrow>
    renaming_equivariant admissible (product_action actL actR) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>z. relation (fst z) (snd z))"
proof -
  have classes: "presentation_class R D A" "presentation_class S E B"
    using contract unfolding presented_relation_contract_def by blast+
  have exact: "observe p q \<longleftrightarrow> presented_relation R S relation p q" for p q
    by (rule presented_relation_contract.exact[OF contract])
  have lifted: "observe (fst x) (snd x) \<longleftrightarrow> presented_predicate
      (\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p)) (\<lambda>z. relation (fst z) (snd z)) x" for x
    by (cases x) (auto simp: exact presented_predicate_def presented_relation_def)
  show ?thesis
    by (rule presented_predicate_renaming[OF presentation_class_product[OF classes]
        renaming_action_product[OF left right] lifted])
qed

text \<open>A presented function is its graph relation.\<close>

corollary presented_function_contract_renaming:
  assumes contract: "presented_function_contract R D A S E B f operation"
    and left: "renaming_action admissible actL D" and right: "renaming_action admissible actR E"
  shows "(\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence
      (\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p)) (product_action actL actR) h) (=)
      (\<lambda>p. operation (fst p) (snd p)) (\<lambda>p. operation (fst p) (snd p))) \<longleftrightarrow>
    renaming_equivariant admissible (product_action actL actR) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>z. snd z = f (fst z))"
proof -
  have relation: "presented_relation_contract R D A S E B (\<lambda>a b. b = f a) operation"
    using contract unfolding presented_function_contract_def by blast
  show ?thesis using presented_relation_contract_renaming[OF relation left right] by simp
qed

text \<open>A graph is equivariant exactly when the function commutes with the renamings.\<close>

theorem renaming_equivariant_graph:
  assumes left: "renaming_action admissible actL D" and right: "renaming_action admissible actR E"
    and image: "\<And>a. D a \<Longrightarrow> E (f a)"
  shows "renaming_equivariant admissible (product_action actL actR) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>z. snd z = f (fst z)) \<longleftrightarrow> (\<forall>h a. admissible h \<longrightarrow> D a \<longrightarrow> f (actL h a) = actR h (f a))"
proof -
  interpret r: renaming_action admissible actR E by (rule right)
  have graph: "(\<forall>h a b. admissible h \<longrightarrow> D a \<longrightarrow> E b \<longrightarrow> (actR h b = f (actL h a) \<longleftrightarrow> b = f a)) \<longleftrightarrow>
      (\<forall>h a. admissible h \<longrightarrow> D a \<longrightarrow> f (actL h a) = actR h (f a))"
  proof
    assume all: "\<forall>h a b. admissible h \<longrightarrow> D a \<longrightarrow> E b \<longrightarrow> (actR h b = f (actL h a) \<longleftrightarrow> b = f a)"
    show "\<forall>h a. admissible h \<longrightarrow> D a \<longrightarrow> f (actL h a) = actR h (f a)"
      using all image by fastforce
  next
    assume commutes: "\<forall>h a. admissible h \<longrightarrow> D a \<longrightarrow> f (actL h a) = actR h (f a)"
    show "\<forall>h a b. admissible h \<longrightarrow> D a \<longrightarrow> E b \<longrightarrow> (actR h b = f (actL h a) \<longleftrightarrow> b = f a)"
    proof (intro allI impI)
      fix h a b assume h: "admissible h" and a: "D a" and b: "E b"
      show "actR h b = f (actL h a) \<longleftrightarrow> b = f a"
        using commutes h a r.act_inject[OF h b image[OF a]] by simp
    qed
  qed
  show ?thesis
    by (simp only: renaming_equivariant_relation[where Q="\<lambda>a b. b = f a"] graph)
qed

subsection \<open>Lists and finite collections\<close>

theorem renaming_action_lists:
  assumes action: "renaming_action admissible act D"
  shows "renaming_action admissible (\<lambda>h. map (act h)) (\<lambda>xs. \<forall>a\<in>set xs. D a)"
proof -
  interpret renaming_action admissible act D by (rule action)
  show ?thesis
    by unfold_locales (auto simp: admissible_bij admissible_id admissible_comp admissible_inv
        act_domain act_id act_comp cong: map_cong)
qed

theorem renaming_action_sets:
  assumes action: "renaming_action admissible act D"
  shows "renaming_action admissible (\<lambda>h. image (act h)) (\<lambda>X. finite X \<and> (\<forall>a\<in>X. D a))"
proof -
  interpret renaming_action admissible act D by (rule action)
  show ?thesis
    by unfold_locales (auto simp: admissible_bij admissible_id admissible_comp admissible_inv
        act_domain act_id act_comp cong: image_cong)
qed

theorem renaming_action_fsets:
  assumes action: "renaming_action admissible act D"
  shows "renaming_action admissible (\<lambda>h. fimage (act h)) (\<lambda>X. \<forall>a\<in>fset X. D a)"
proof -
  interpret renaming_action admissible act D by (rule action)
  show ?thesis
    by unfold_locales (auto simp: fset_inject[symmetric] fimage.rep_eq admissible_bij admissible_id
        admissible_comp admissible_inv act_domain act_id act_comp cong: image_cong)
qed

subsection \<open>Subdomains closed under the action\<close>

theorem renaming_action_subdomain:
  assumes action: "renaming_action admissible act D"
    and inside: "\<And>a. K a \<Longrightarrow> D a" and closed: "\<And>h a. admissible h \<Longrightarrow> K a \<Longrightarrow> K (act h a)"
  shows "renaming_action admissible act K"
proof -
  interpret renaming_action admissible act D by (rule action)
  show ?thesis
    by unfold_locales (simp_all add: admissible_bij admissible_id admissible_comp admissible_inv
        closed inside act_id act_comp)
qed

lemma renaming_subdomain_equivariant:
  assumes action: "renaming_action admissible act D"
    and closed: "\<And>h a. admissible h \<Longrightarrow> K a \<Longrightarrow> K (act h a)"
  shows "renaming_equivariant admissible act D K"
proof -
  interpret renaming_action admissible act D by (rule action)
  show ?thesis
    unfolding renaming_equivariant_def
  proof (intro allI impI iffI)
    fix h a assume h: "admissible h" and a: "D a" and moved: "K (act h a)"
    have "K (act (inv h) (act h a))" by (rule closed[OF admissible_inv[OF h] moved])
    then show "K a" by (simp only: act_inverse[OF h a])
  next
    fix h a assume h: "admissible h" and "D a" and unmoved: "K a"
    show "K (act h a)" by (rule closed[OF h unmoved])
  qed
qed

subsection \<open>Composed presentations\<close>

text \<open>
  A composed presentation reads its subject through the intermediate class's presentation, so its
  renaming correspondence is the intermediate class's, carried by the second presentation; its
  contract is the notion's at the composed class (@{thm [source] presentation_class_compose_on}).
\<close>

lemma renaming_correspondence_composed:
  "renaming_correspondence (composed_presentation R S) act h q r \<longleftrightarrow>
    (\<exists>p u. renaming_correspondence R act h p u \<and> S p q \<and> S u r)"
  by (auto simp: renaming_correspondence_def composed_presentation_def)

corollary composed_presentation_renaming:
  assumes first: "presentation_class R D A" and second: "presentation_class S E B"
    and covered: "\<And>p. A p \<Longrightarrow> E p" and action: "renaming_action admissible act D"
    and exact: "\<And>q. observe q \<longleftrightarrow> presented_predicate (composed_presentation R S) P q"
  shows "(\<forall>h. admissible h \<longrightarrow>
      rel_fun (renaming_correspondence (composed_presentation R S) act h) (=) observe observe) \<longleftrightarrow>
    renaming_equivariant admissible act D P"
  by (rule presented_predicate_renaming[OF presentation_class_compose_on[OF first second covered]
      action exact])

subsection \<open>Relation composition through an intermediate domain\<close>

theorem renaming_equivariant_relation_compose:
  assumes middle: "renaming_action admissible actE E"
    and first: "renaming_equivariant admissible (product_action actD actE) (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>z. L (fst z) (snd z))"
    and second: "renaming_equivariant admissible (product_action actE actF) (\<lambda>z. E (fst z) \<and> F (snd z))
      (\<lambda>z. M (fst z) (snd z))"
  shows "renaming_equivariant admissible (product_action actD actF) (\<lambda>z. D (fst z) \<and> F (snd z))
    (\<lambda>z. \<exists>b. E b \<and> L (fst z) b \<and> M b (snd z))"
proof -
  interpret m: renaming_action admissible actE E by (rule middle)
  have l: "L (actD h a) (actE h b) \<longleftrightarrow> L a b" if "admissible h" "D a" "E b" for h a b
    using first that unfolding renaming_equivariant_relation by blast
  have r: "M (actE h b) (actF h c) \<longleftrightarrow> M b c" if "admissible h" "E b" "F c" for h b c
    using second that unfolding renaming_equivariant_relation by blast
  have key: "(\<exists>b. E b \<and> L (actD h a) b \<and> M b (actF h c)) \<longleftrightarrow> (\<exists>b. E b \<and> L a b \<and> M b c)"
    if h: "admissible h" and a: "D a" and c: "F c" for h a c
  proof
    assume "\<exists>b. E b \<and> L (actD h a) b \<and> M b (actF h c)"
    then obtain u where u: "E u" "L (actD h a) u" "M u (actF h c)" by blast
    have b: "E (actE (inv h) u)" by (rule m.act_domain[OF m.admissible_inv[OF h] u(1)])
    have moved: "actE h (actE (inv h) u) = u" by (rule m.act_inverse_right[OF h u(1)])
    have "L a (actE (inv h) u)" using l[OF h a b] u(2) moved by simp
    moreover have "M (actE (inv h) u) c" using r[OF h b c] u(3) moved by simp
    ultimately show "\<exists>b. E b \<and> L a b \<and> M b c" using b by blast
  next
    assume "\<exists>b. E b \<and> L a b \<and> M b c"
    then obtain b where b: "E b" "L a b" "M b c" by blast
    have "E (actE h b)" by (rule m.act_domain[OF h b(1)])
    then show "\<exists>b. E b \<and> L (actD h a) b \<and> M b (actF h c)"
      using l[OF h a b(1)] r[OF h b(1) c] b by blast
  qed
  show ?thesis
    unfolding renaming_equivariant_relation[where Q="\<lambda>a c. \<exists>b. E b \<and> L a b \<and> M b c"]
    using key by blast
qed

subsection \<open>Conjunction, alternatives and complement\<close>

lemma renaming_equivariant_conj:
  "renaming_equivariant admissible act D P \<Longrightarrow> renaming_equivariant admissible act D Q \<Longrightarrow>
    renaming_equivariant admissible act D (\<lambda>a. P a \<and> Q a)"
  by (simp add: renaming_equivariant_def)

lemma renaming_equivariant_disj:
  "renaming_equivariant admissible act D P \<Longrightarrow> renaming_equivariant admissible act D Q \<Longrightarrow>
    renaming_equivariant admissible act D (\<lambda>a. P a \<or> Q a)"
  by (simp add: renaming_equivariant_def)

lemma renaming_equivariant_not:
  "renaming_equivariant admissible act D P \<Longrightarrow> renaming_equivariant admissible act D (\<lambda>a. \<not> P a)"
  by (simp add: renaming_equivariant_def)

corollary presented_conjunction_renaming:
  assumes presented: "presentation_class R D A" and action: "renaming_action admissible act D"
    and P: "renaming_equivariant admissible act D P" and Q: "renaming_equivariant admissible act D Q"
  shows "\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=)
    (\<lambda>p. presented_predicate R P p \<and> presented_predicate R Q p)
    (\<lambda>p. presented_predicate R P p \<and> presented_predicate R Q p)"
proof -
  have exact: "(presented_predicate R P p \<and> presented_predicate R Q p) \<longleftrightarrow>
      presented_predicate R (\<lambda>a. P a \<and> Q a) p" for p
    by (simp only: presentation_class.predicate_conjunction[OF presented])
  show ?thesis
    using presented_predicate_renaming[OF presented action exact] renaming_equivariant_conj[OF P Q] by blast
qed

corollary presented_alternatives_renaming:
  assumes presented: "presentation_class R D A" and action: "renaming_action admissible act D"
    and P: "renaming_equivariant admissible act D P" and Q: "renaming_equivariant admissible act D Q"
  shows "\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=)
    (\<lambda>p. presented_predicate R P p \<or> presented_predicate R Q p)
    (\<lambda>p. presented_predicate R P p \<or> presented_predicate R Q p)"
proof -
  have exact: "(presented_predicate R P p \<or> presented_predicate R Q p) \<longleftrightarrow>
      presented_predicate R (\<lambda>a. P a \<or> Q a) p" for p
    by (simp only: presented_predicate_alternatives)
  show ?thesis
    using presented_predicate_renaming[OF presented action exact] renaming_equivariant_disj[OF P Q] by blast
qed

subsection \<open>Least fixed points\<close>

text \<open>
  A monotone operator on subsets of the domain that commutes with every admissible renaming has a least
  fixed point every renaming fixes: @{thm [source] presented_least_fixed_point_on} at the presentation
  relation of the renaming's graph, as @{text Factor_System_Relocation.renamed_system_positive_meaning}
  relocates a program's meaning. A recursive definition's equivariance is thereby a local obligation of
  its rules, the commutation of one consequence step.
\<close>

theorem renaming_equivariant_lfp:
  assumes action: "renaming_action admissible act D"
    and monotone: "mono F" and boundary: "\<And>X. X \<subseteq> {a. D a} \<Longrightarrow> F X \<subseteq> {a. D a}"
    and commutes: "\<And>h X. admissible h \<Longrightarrow> X \<subseteq> {a. D a} \<Longrightarrow> F (act h ` X) = act h ` F X"
  shows "lfp F \<subseteq> {a. D a}" and "\<And>h. admissible h \<Longrightarrow> act h ` lfp F = lfp F"
    and "renaming_equivariant admissible act D (\<lambda>a. a \<in> lfp F)"
proof -
  interpret renaming_action admissible act D by (rule action)
  show inside: "lfp F \<subseteq> {a. D a}" by (rule lfp_lowerbound) (rule boundary[OF order_refl])
  have fixed: "act h ` lfp F = lfp F" if h: "admissible h" for h
  proof -
    have lift: "presented_set (\<lambda>a b. b = act h a) X = act h ` X" for X
      by (auto simp: presented_set_def)
    have "lfp F = presented_set (\<lambda>a b. b = act h a) (lfp F)"
    proof (rule presented_least_fixed_point_on[where D="{a. D a}", OF monotone monotone])
      fix X assume "X \<subseteq> {a. D a}"
      then show "F X \<subseteq> {a. D a}" by (rule boundary)
    next
      fix X assume support: "X \<subseteq> {a. D a}"
      have "F (act h ` X) = act h ` F X" by (rule commutes[OF h support])
      then show "F (presented_set (\<lambda>a b. b = act h a) X) = presented_set (\<lambda>a b. b = act h a) (F X)"
        by (simp only: lift)
    qed
    then have "lfp F = act h ` lfp F" by (simp only: lift)
    then show ?thesis by (rule sym)
  qed
  show "\<And>h. admissible h \<Longrightarrow> act h ` lfp F = lfp F" by (rule fixed)
  show "renaming_equivariant admissible act D (\<lambda>a. a \<in> lfp F)"
    unfolding renaming_equivariant_def
  proof (intro allI impI iffI)
    fix h a assume h: "admissible h" and a: "D a" and moved: "act h a \<in> lfp F"
    have "act h a \<in> act h ` lfp F" using moved fixed[OF h] by simp
    then obtain b where b: "b \<in> lfp F" "act h a = act h b" by blast
    have "D b" using inside b(1) by blast
    then have "a = b" using act_inject[OF h a] b(2) by blast
    then show "a \<in> lfp F" using b(1) by simp
  next
    fix h a assume h: "admissible h" and "D a" and unmoved: "a \<in> lfp F"
    have "act h a \<in> act h ` lfp F" using unmoved by (rule imageI)
    then show "act h a \<in> lfp F" using fixed[OF h] by simp
  qed
qed

section \<open>Instances\<close>

text \<open>
  The leaf argument is the notion at leaf maps. @{text Factor_Positive_Parametricity} renames the leaves
  of terms by formed maps fixing the leaves a program states, acting on terms by @{text map_term_leaves},
  and its @{text positive_meaning_leaf_involution} and @{text positive_meaning_unlisted_leaves} are the
  equivariance of an observation-free program's meaning under those renamings; the admissibility, which
  leaves a program states, is syntactic, which is why the octet audit checks it natively. It is cited as
  that theory states it and restated in this form only where a use consumes it so. Uses are an instance
  of their own, the permutations of the uses of artifact environments acting through
  @{text rename_environment} (@{text Factor_Use_Actions}); re-addressing, @{text push_object} under
  @{text finite_addressing}, is a further instance not stated here.
\<close>

end
