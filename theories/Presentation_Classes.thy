theory Presentation_Classes
  imports Main
begin

section \<open>Admissible presentations recover their complete subjects\<close>

locale presentation_class =
  fixes presents :: "'a \<Rightarrow> 'p \<Rightarrow> bool"
    and subject :: "'a \<Rightarrow> bool"
    and admissible :: "'p \<Rightarrow> bool"
  assumes subject_boundary: "presents a p \<Longrightarrow> subject a"
    and presentation_boundary: "presents a p \<Longrightarrow> admissible p"
    and total: "subject a \<Longrightarrow> \<exists>p. presents a p"
    and admitted: "admissible p \<Longrightarrow> \<exists>a. presents a p"
    and recovery: "presents a p \<Longrightarrow> presents b p \<Longrightarrow> a=b"
begin

lemma subject_iff: "subject a \<longleftrightarrow> (\<exists>p. presents a p)"
  using subject_boundary total by blast

lemma admissible_iff: "admissible p \<longleftrightarrow> (\<exists>a. presents a p)"
  using presentation_boundary admitted by blast

theorem inhabited_iff:
  "(\<exists>p. admissible p) \<longleftrightarrow> (\<exists>a. subject a)"
  using admitted subject_boundary total presentation_boundary by blast

theorem unique_recovery:
  assumes "admissible p"
  shows "\<exists>!a. presents a p"
  using admitted[OF assms] recovery by blast

theorem constrain:
  assumes sound: "\<And>a p. presents a p \<Longrightarrow> compatible p \<Longrightarrow> condition a"
    and complete: "\<And>a. subject a \<Longrightarrow> condition a \<Longrightarrow>
      \<exists>p. presents a p \<and> compatible p"
  shows "presentation_class (\<lambda>a p. presents a p \<and> compatible p)
    (\<lambda>a. subject a \<and> condition a) (\<lambda>p. admissible p \<and> compatible p)"
  by (unfold_locales)
    (use subject_boundary presentation_boundary admitted recovery sound complete in blast)+

corollary invariant_constraint:
  assumes exact: "\<And>a p. presents a p \<Longrightarrow> compatible p \<longleftrightarrow> condition a"
  shows "presentation_class (\<lambda>a p. presents a p \<and> compatible p)
    (\<lambda>a. subject a \<and> condition a) (\<lambda>p. admissible p \<and> compatible p)"
  by (rule constrain)
    (use exact total in blast)+

lemma list_boundaries:
  assumes "list_all2 presents xs ps"
  shows "(\<forall>a\<in>set xs. subject a) \<and> (\<forall>p\<in>set ps. admissible p)"
  using assms
  by (induction xs arbitrary: ps)
    (auto simp: list_all2_Cons1 dest: subject_boundary presentation_boundary)

lemma list_total:
  assumes "\<forall>a\<in>set xs. subject a"
  shows "\<exists>ps. list_all2 presents xs ps"
  using assms
proof (induction xs)
  case Nil
  show ?case by (rule exI[of _ "[]"]) simp
next
  case (Cons a xs)
  have head: "subject a" and tail: "\<forall>x\<in>set xs. subject x"
    using Cons.prems by auto
  obtain p where first: "presents a p" using total[OF head] by blast
  obtain ps where rest: "list_all2 presents xs ps" using Cons.IH[OF tail] by blast
  show ?case by (rule exI[of _ "p#ps"]) (use first rest in simp)
qed

lemma list_admitted:
  assumes "\<forall>p\<in>set ps. admissible p"
  shows "\<exists>xs. list_all2 presents xs ps"
  using assms by (induction ps) (use admitted in \<open>auto simp: list_all2_Cons2\<close>)

lemma list_recovery:
  assumes "list_all2 presents xs ps" "list_all2 presents ys ps"
  shows "xs=ys"
  using assms
  by (induction xs arbitrary: ys ps)
    (auto simp: list_all2_Cons1 list_all2_Cons2 dest: recovery)

theorem lists:
  "presentation_class (list_all2 presents)
    (\<lambda>xs. \<forall>a\<in>set xs. subject a) (\<lambda>ps. \<forall>p\<in>set ps. admissible p)"
  by (unfold_locales)
    (use list_boundaries list_total list_admitted list_recovery in blast)+

end

section \<open>Changes of presentation preserve the whole intermediate value\<close>

definition composed_presentation ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow>
    'a \<Rightarrow> 'q \<Rightarrow> bool" where
  "composed_presentation first second a q \<longleftrightarrow>
    (\<exists>p. first a p \<and> second p q)"

theorem presentation_class_compose_on:
  assumes first: "presentation_class R D A"
    and second: "presentation_class S E B"
    and covered: "\<And>p. A p \<Longrightarrow> E p"
  shows "presentation_class (composed_presentation R S) D
    (\<lambda>q. B q \<and> (\<exists>p. A p \<and> S p q))"
proof -
  interpret first: presentation_class R D A by (rule first)
  interpret second: presentation_class S E B by (rule second)
  show ?thesis
  proof (unfold_locales)
    fix a q assume read: "composed_presentation R S a q"
    obtain p where parts: "R a p" "S p q" using read unfolding composed_presentation_def by blast
    show "D a" by (rule first.subject_boundary[OF parts(1)])
    show "B q \<and> (\<exists>p. A p \<and> S p q)"
      using first.presentation_boundary[OF parts(1)] second.presentation_boundary[OF parts(2)] parts(2) by blast
  next
    fix a assume domain: "D a"
    obtain p where first_read: "R a p" using first.total[OF domain] by blast
    have intermediate: "E p" by (rule covered[OF first.presentation_boundary[OF first_read]])
    obtain q where second_read: "S p q" using second.total[OF intermediate] by blast
    show "\<exists>q. composed_presentation R S a q"
      by (rule exI[of _ q]) (use first_read second_read in \<open>auto simp: composed_presentation_def\<close>)
  next
    fix q assume allowed: "B q \<and> (\<exists>p. A p \<and> S p q)"
    obtain p where parts: "A p" "S p q" using allowed by blast
    obtain a where read: "R a p" using first.admitted[OF parts(1)] by blast
    show "\<exists>a. composed_presentation R S a q"
      by (rule exI[of _ a]) (use read parts(2) in \<open>auto simp: composed_presentation_def\<close>)
  next
    fix a q b assume one: "composed_presentation R S a q" and two: "composed_presentation R S b q"
    obtain p where left: "R a p" "S p q" using one unfolding composed_presentation_def by blast
    obtain r where right: "R b r" "S r q" using two unfolding composed_presentation_def by blast
    have same: "p=r" by (rule second.recovery[OF left(2) right(2)])
    have other: "R b p" using right(1) same by simp
    show "a=b" by (rule first.recovery[OF left(1) other])
  qed
qed

corollary presentation_class_compose:
  assumes first: "presentation_class R D A" and second: "presentation_class S A B"
  shows "presentation_class (composed_presentation R S) D B"
proof -
  interpret second: presentation_class S A B by (rule second)
  have result: "presentation_class (composed_presentation R S) D
    (\<lambda>q. B q \<and> (\<exists>p. A p \<and> S p q))"
    by (rule presentation_class_compose_on[OF first second]) assumption
  have same: "(\<lambda>q. B q \<and> (\<exists>p. A p \<and> S p q))=B"
    by (rule ext) (use second.admitted second.subject_boundary in blast)
  show ?thesis using result by (simp only: same)
qed

lemma composed_presentation_associative:
  "composed_presentation (composed_presentation R S) T =
    composed_presentation R (composed_presentation S T)"
  by (intro ext) (auto simp: composed_presentation_def)

lemma composed_presentation_identity:
  "composed_presentation (=) R=R"
  "composed_presentation R (=)=R"
  by (intro ext; simp add: composed_presentation_def)+

theorem injective_presentation_class:
  assumes injective: "inj_on f {a. D a}"
  shows "presentation_class (\<lambda>a p. D a \<and> p=f a) D
    (\<lambda>p. \<exists>a. D a \<and> p=f a)"
  by (unfold_locales) (use injective in \<open>auto simp: inj_on_def\<close>)

section \<open>Jointly determining observations give a change of subject\<close>

theorem presentation_class_observations:
  assumes records: "presentation_class read E A"
    and boundary: "\<And>a. D a \<Longrightarrow> E (observe a)"
    and determines: "\<And>a b. D a \<Longrightarrow> D b \<Longrightarrow> observe a=observe b \<Longrightarrow> a=b"
  shows "presentation_class (\<lambda>a p. D a \<and> read (observe a) p) D
    (\<lambda>p. \<exists>a. D a \<and> read (observe a) p)"
proof -
  interpret records: presentation_class read E A by (rule records)
  have injective: "inj_on observe {a. D a}"
    using determines by (auto simp: inj_on_def)
  have first: "presentation_class (\<lambda>a v. D a \<and> v=observe a) D
      (\<lambda>v. \<exists>a. D a \<and> v=observe a)"
    by (rule injective_presentation_class[OF injective])
  have composed: "presentation_class
      (composed_presentation (\<lambda>a v. D a \<and> v=observe a) read) D
      (\<lambda>p. A p \<and> (\<exists>v. (\<exists>a. D a \<and> v=observe a) \<and> read v p))"
    by (rule presentation_class_compose_on[OF first records])
      (use boundary in blast)
  have reading: "composed_presentation (\<lambda>a v. D a \<and> v=observe a) read =
      (\<lambda>a p. D a \<and> read (observe a) p)"
    by (intro ext) (auto simp: composed_presentation_def)
  have admission: "(\<lambda>p. A p \<and> (\<exists>v. (\<exists>a. D a \<and> v=observe a) \<and> read v p)) =
      (\<lambda>p. \<exists>a. D a \<and> read (observe a) p)"
    by (rule ext) (use records.presentation_boundary in blast)
  show ?thesis using composed by (simp only: reading admission)
qed

section \<open>Products require every component and retain their roles\<close>

theorem presentation_class_product:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
  shows "presentation_class (\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p))
    (\<lambda>z. D (fst z) \<and> E (snd z)) (\<lambda>p. A (fst p) \<and> B (snd p))"
proof -
  interpret left: presentation_class R D A by (rule left)
  interpret right: presentation_class S E B by (rule right)
  show ?thesis
  proof (unfold_locales)
    fix z p assume read: "R (fst z) (fst p) \<and> S (snd z) (snd p)"
    show "D (fst z) \<and> E (snd z)"
      using read left.subject_boundary right.subject_boundary by blast
    show "A (fst p) \<and> B (snd p)"
      using read left.presentation_boundary right.presentation_boundary by blast
  next
    fix z assume domain: "D (fst z) \<and> E (snd z)"
    obtain p q where parts: "R (fst z) p" "S (snd z) q"
      using domain left.total right.total by blast
    show "\<exists>p. R (fst z) (fst p) \<and> S (snd z) (snd p)"
      by (rule exI[of _ "(p,q)"]) (use parts in simp)
  next
    fix p assume allowed: "A (fst p) \<and> B (snd p)"
    obtain a b where parts: "R a (fst p)" "S b (snd p)"
      using allowed left.admitted right.admitted by blast
    show "\<exists>z. R (fst z) (fst p) \<and> S (snd z) (snd p)"
      by (rule exI[of _ "(a,b)"]) (use parts in simp)
  next
    fix a p b
    assume first: "R (fst a) (fst p) \<and> S (snd a) (snd p)"
      and second: "R (fst b) (fst p) \<and> S (snd b) (snd p)"
    show "a=b" by (rule prod_eqI) (use first second left.recovery right.recovery in blast)+
  qed
qed

theorem presentation_class_joint:
  assumes left: "presentation_class R D A" and right: "presentation_class S E B"
    and sound: "\<And>a b p q. R a p \<Longrightarrow> S b q \<Longrightarrow>
      compatible p q \<Longrightarrow> linked a b"
    and complete: "\<And>a b. D a \<Longrightarrow> E b \<Longrightarrow> linked a b \<Longrightarrow>
      \<exists>p q. R a p \<and> S b q \<and> compatible p q"
  shows "presentation_class
    (\<lambda>z p. (R (fst z) (fst p) \<and> S (snd z) (snd p)) \<and> compatible (fst p) (snd p))
    (\<lambda>z. (D (fst z) \<and> E (snd z)) \<and> linked (fst z) (snd z))
    (\<lambda>p. (A (fst p) \<and> B (snd p)) \<and> compatible (fst p) (snd p))"
proof -
  interpret pair: presentation_class
    "\<lambda>z p. R (fst z) (fst p) \<and> S (snd z) (snd p)"
    "\<lambda>z. D (fst z) \<and> E (snd z)" "\<lambda>p. A (fst p) \<and> B (snd p)"
    by (rule presentation_class_product[OF left right])
  show ?thesis
  proof (rule pair.constrain)
    fix a p assume read: "R (fst a) (fst p) \<and> S (snd a) (snd p)"
      and compatible: "compatible (fst p) (snd p)"
    show "linked (fst a) (snd a)" using sound read compatible by blast
  next
    fix a assume domain: "D (fst a) \<and> E (snd a)" and link: "linked (fst a) (snd a)"
    obtain p q where parts: "R (fst a) p" "S (snd a) q" "compatible p q"
      using complete domain link by blast
    show "\<exists>p. (R (fst a) (fst p) \<and> S (snd a) (snd p)) \<and> compatible (fst p) (snd p)"
      by (rule exI[of _ "(p,q)"]) (use parts in simp)
  qed
qed

section \<open>Intrinsically determined components need no duplicate stored value\<close>

theorem presentation_class_determined:
  assumes source: "presentation_class R D A"
    and determined: "\<And>a b c. link a b \<Longrightarrow> link a c \<Longrightarrow> b=c"
  shows "presentation_class (\<lambda>z p. R (fst z) p \<and> link (fst z) (snd z))
    (\<lambda>z. D (fst z) \<and> link (fst z) (snd z))
    (\<lambda>p. \<exists>a b. R a p \<and> link a b)"
proof -
  interpret source: presentation_class R D A by (rule source)
  show ?thesis
  proof (unfold_locales)
    fix z p assume read: "R (fst z) p \<and> link (fst z) (snd z)"
    show "D (fst z) \<and> link (fst z) (snd z)"
      using read source.subject_boundary by blast
    show "\<exists>a b. R a p \<and> link a b" using read by blast
  next
    fix z assume domain: "D (fst z) \<and> link (fst z) (snd z)"
    show "\<exists>p. R (fst z) p \<and> link (fst z) (snd z)"
      using domain source.total by blast
  next
    fix p assume "\<exists>a b. R a p \<and> link a b"
    then obtain a b where parts: "R a p" "link a b" by blast
    show "\<exists>z. R (fst z) p \<and> link (fst z) (snd z)"
      by (rule exI[of _ "(a,b)"]) (use parts in simp)
  next
    fix z p w
    assume first: "R (fst z) p \<and> link (fst z) (snd z)"
      and second: "R (fst w) p \<and> link (fst w) (snd w)"
    have sources: "fst z=fst w" using first second source.recovery by blast
    have one: "link (fst z) (snd z)" using first by blast
    have other: "link (fst z) (snd w)" using second sources by simp
    have components: "snd z=snd w" by (rule determined[OF one other])
    show "z=w" by (rule prod_eqI[OF sources components])
  qed
qed

section \<open>Alternative forms require agreement where they overlap\<close>

theorem presentation_class_alternatives:
  assumes first: "presentation_class R D A" and second: "presentation_class S D B"
    and overlap: "\<And>a b p. R a p \<Longrightarrow> S b p \<Longrightarrow> a=b"
  shows "presentation_class (\<lambda>a p. R a p \<or> S a p) D (\<lambda>p. A p \<or> B p)"
proof -
  interpret first: presentation_class R D A by (rule first)
  interpret second: presentation_class S D B by (rule second)
  show ?thesis
  proof (unfold_locales)
    fix a p assume read: "R a p \<or> S a p"
    show "D a" using read first.subject_boundary second.subject_boundary by blast
    show "A p \<or> B p" using read first.presentation_boundary second.presentation_boundary by blast
  next
    fix a assume domain: "D a"
    show "\<exists>p. R a p \<or> S a p" using first.total[OF domain] by blast
  next
    fix p assume allowed: "A p \<or> B p"
    show "\<exists>a. R a p \<or> S a p" using allowed first.admitted second.admitted by blast
  next
    fix a p b assume left: "R a p \<or> S a p" and right: "R b p \<or> S b p"
    show "a=b" using left right first.recovery second.recovery overlap by blast
  qed
qed

theorem separate_coverage_has_no_joint_witness:
  "presentation_class (\<lambda>_::unit. \<lambda>p::bool. p) (\<lambda>_. True) id \<and>
    presentation_class (\<lambda>_::unit. \<lambda>p::bool. \<not>p) (\<lambda>_. True) Not \<and>
    \<not>(\<exists>p::bool. p \<and> \<not>p)"
  by (auto simp: presentation_class_def)

text \<open>
  The locale records total coverage, admissibility, and recovery of the entire
  declared subject. It does not by itself establish an account of the physical
  material or of any relation to another subject. Those obligations belong to
  the independent subject and presentation relations in each application.

  A constrained class needs soundness for every retained presentation and a
  compatible witness for every required subject. Two separately total classes
  need not have a common witness. The joint construction therefore includes
  that obligation. Lists retain positions and repeated occurrences; products
  retain both roles. These constructions impose no exchange rule.

  Composition recovers the complete intermediate presentation before recovering
  its subject. An intrinsically determined component is recovered through its
  independently proved functional link, without storing a duplicate value.
  A jointly determining family of observations can replace a literal copy
  when its complete record has a presentation and its observation map is
  injective on the required subject domain. The observation theorem derives
  this class through the same composition rule; it gives no native force to
  an arbitrary mathematical observation. Alternatives need agreement on
  overlapping forms. Neither construction chooses a privileged topology or
  a preferred representative. The parameters
  are ordinary typed relations in the proof language, not a new primitive kind
  or an assertion that arbitrary predicates have native semantic definitions.
\<close>

end
