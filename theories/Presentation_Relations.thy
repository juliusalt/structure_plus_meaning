theory Presentation_Relations
  imports Presentation_Classes
begin

section \<open>Relations retain all of their presented arguments\<close>

definition presented_predicate ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> bool" where
  "presented_predicate presents property p \<longleftrightarrow>
    (\<exists>a. presents a p \<and> property a)"

definition presented_relation ::
  "('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'q \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'q \<Rightarrow> bool" where
  "presented_relation left right relation p q \<longleftrightarrow>
    (\<exists>a b. left a p \<and> right b q \<and> relation a b)"

context presentation_class
begin

theorem predicate_at:
  assumes "presents a p"
  shows "presented_predicate presents property p \<longleftrightarrow> property a"
  using assms recovery by (auto simp: presented_predicate_def; blast)

theorem predicate_invariance:
  assumes "presents a p" "presents a q"
    and exact: "\<And>x. observe x \<longleftrightarrow> presented_predicate presents property x"
  shows "observe p \<longleftrightarrow> observe q"
  by (simp only: exact predicate_at[OF assms(1)] predicate_at[OF assms(2)])

theorem predicate_conjunction:
  "presented_predicate presents (\<lambda>a. P a \<and> Q a) p \<longleftrightarrow>
    presented_predicate presents P p \<and> presented_predicate presents Q p"
  using recovery by (auto simp: presented_predicate_def; blast)

end

lemma presented_predicate_alternatives:
  "presented_predicate R (\<lambda>a. P a \<or> Q a) p \<longleftrightarrow>
    presented_predicate R P p \<or> presented_predicate R Q p"
  by (auto simp: presented_predicate_def)

theorem presented_relation_at:
  assumes left: "presentation_class A D X" and right: "presentation_class B E Y"
    and first: "A a p" and second: "B b q"
  shows "presented_relation A B R p q \<longleftrightarrow> R a b"
proof -
  interpret left: presentation_class A D X by (rule left)
  interpret right: presentation_class B E Y by (rule right)
  show ?thesis using first second left.recovery right.recovery
    by (auto simp: presented_relation_def; blast)
qed

theorem presented_relation_invariance:
  assumes left: "presentation_class A D X" and right: "presentation_class B E Y"
    and first: "A a p" "B b q" and second: "A a u" "B b v"
    and exact: "\<And>x y. observe x y \<longleftrightarrow> presented_relation A B R x y"
  shows "observe p q \<longleftrightarrow> observe u v"
  by (simp only: exact presented_relation_at[OF left right first]
      presented_relation_at[OF left right second])

section \<open>Conjunction shares the same recovered arguments\<close>

theorem presented_relation_conjunction:
  assumes left: "presentation_class A D X" and right: "presentation_class B E Y"
  shows "presented_relation A B (\<lambda>a b. R a b \<and> S a b) p q \<longleftrightarrow>
    presented_relation A B R p q \<and> presented_relation A B S p q"
proof -
  interpret left: presentation_class A D X by (rule left)
  interpret right: presentation_class B E Y by (rule right)
  show ?thesis using left.recovery right.recovery
    by (auto simp: presented_relation_def; blast)
qed

lemma presented_relation_alternatives:
  "presented_relation A B (\<lambda>a b. R a b \<or> S a b) p q \<longleftrightarrow>
    presented_relation A B R p q \<or> presented_relation A B S p q"
  by (auto simp: presented_relation_def)

section \<open>Relational composition needs a shared intermediate presentation\<close>

theorem presented_relation_compose:
  assumes middle: "presentation_class B D X"
  shows "(\<exists>q. presented_relation A B R p q \<and> presented_relation B C S q r) \<longleftrightarrow>
    presented_relation A C (\<lambda>a c. \<exists>b. D b \<and> R a b \<and> S b c) p r"
proof -
  interpret middle: presentation_class B D X by (rule middle)
  show ?thesis
  proof
    assume "\<exists>q. presented_relation A B R p q \<and> presented_relation B C S q r"
    then obtain q a b d c where first: "A a p" "B b q" "R a b"
      and second: "B d q" "C c r" "S d c"
      by (auto simp: presented_relation_def)
    have same: "b=d" by (rule middle.recovery[OF first(2) second(1)])
    have domain: "D b" by (rule middle.subject_boundary[OF first(2)])
    show "presented_relation A C (\<lambda>a c. \<exists>b. D b \<and> R a b \<and> S b c) p r"
      using first second same domain by (auto simp: presented_relation_def)
  next
    assume "presented_relation A C (\<lambda>a c. \<exists>b. D b \<and> R a b \<and> S b c) p r"
    then obtain a c b where parts: "A a p" "C c r" "D b" "R a b" "S b c"
      by (auto simp: presented_relation_def)
    obtain q where presented: "B b q" using middle.total[OF parts(3)] by blast
    show "\<exists>q. presented_relation A B R p q \<and> presented_relation B C S q r"
      by (rule exI[of _ q]) (use parts presented in \<open>auto simp: presented_relation_def\<close>)
  qed
qed

lemma presented_relation_change:
  "presented_relation (composed_presentation A T) (composed_presentation B U) R x y \<longleftrightarrow>
    (\<exists>p q. T p x \<and> U q y \<and> presented_relation A B R p q)"
  by (auto simp: presented_relation_def composed_presentation_def)

lemma presented_predicate_change:
  "presented_predicate (composed_presentation A T) P q \<longleftrightarrow>
    presented_predicate T (presented_predicate A P) q"
  by (auto simp: presented_predicate_def composed_presentation_def)

text \<open>
  These relations specify preservation and reflection of an independently
  stated predicate or relation. A native reader must prove that its actual
  meaning equals the appropriate presented relation. Defining the lift does
  not supply that proof.

  Conjunction uses recovery to identify both subjects. Relational composition
  additionally uses one common intermediate presentation and total coverage of
  its subject domain. Omitting that domain could claim a witness that has no
  presentation. Independently proving the component classes supplies neither
  a shared context nor the exactness of a reader's intrinsic links.

  The relations above admit every representative of their stated classes.
  When physical compatibility restricts which representatives can be joined,
  the joint class construction supplies a separate soundness and coverage
  obligation. Representation-sensitive observations remain observations of the
  actual representation unless an invariance theorem has been established.
\<close>

end
