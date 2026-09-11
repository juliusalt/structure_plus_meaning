theory Factor_Finite_Set_Readings
  imports Factor_List_Set_Presentations Presentation_Contracts
begin

section \<open>Complete displayed finite sets are characterized by member coverage\<close>

lemma list_all2_subject_constraint:
  "list_all2 (\<lambda>a p. D a \<and> R a p) xs ps \<longleftrightarrow>
    (\<forall>a\<in>set xs. D a) \<and> list_all2 R xs ps"
  by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)

lemma data_list_fset_reading_coverage:
  assumes unique: "\<And>a b p. R a p \<Longrightarrow> R b p \<Longrightarrow> a=b"
  shows "data_list_fset_presents R S (data_list_term ps) \<longleftrightarrow>
    rel_set R (fset S) (set ps)"
proof
  assume "data_list_fset_presents R S (data_list_term ps)"
  then obtain xs where readings: "list_all2 R xs ps" "fset_of_list xs=S"
    by (auto simp only: data_list_fset_presents_def data_sequence_presents_def data_list_term_injective)
  have members: "set xs=fset S" using readings(2) by (simp add: fset_of_list.rep_eq[symmetric])
  show "rel_set R (fset S) (set ps)"
    using list_all2_members[OF readings(1)] by (simp only: members rel_set_def)
next
  assume coverage: "rel_set R (fset S) (set ps)"
  have covered: "\<forall>p\<in>set ps. \<exists>a. a\<in>fset S \<and> R a p"
    using coverage by (simp only: rel_set_def) blast
  obtain xs where rows: "\<forall>a\<in>set xs. a\<in>fset S" "list_all2 R xs ps"
    using covered by (simp only: list_all2_exists_left list_all2_subject_constraint) blast
  have members: "set xs=fset S"
  proof (rule equalityI)
    show "set xs\<subseteq>fset S" using rows(1) by blast
    show "fset S\<subseteq>set xs"
    proof
      fix a assume "a\<in>fset S"
      then obtain p where first: "p\<in>set ps" "R a p" using coverage
        by (simp only: rel_set_def) blast
      obtain b where second: "b\<in>set xs" "R b p"
        using list_all2_members[OF rows(2)] first(1) by blast
      have "a=b" by (rule unique[OF first(2) second(2)])
      then show "a\<in>set xs" using second(1) by simp
    qed
  qed
  have same: "fset_of_list xs=S"
    by (rule fset_inject[THEN iffD1]) (simp add: fset_of_list.rep_eq members)
  show "data_list_fset_presents R S (data_list_term ps)"
    using rows(2) same by (auto simp only: data_list_fset_presents_def data_sequence_presents_def)
qed

lemma data_list_fset_reading_data:
  assumes read: "data_list_fset_presents R S p"
    and data: "\<And>a t. R a t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  shows "\<exists>ps. p=data_list_term ps \<and> data_elements ps"
proof -
  obtain xs ps where rows: "list_all2 R xs ps" "p=data_list_term ps"
    using read by (auto simp only: data_list_fset_presents_def data_sequence_presents_def)
  have "data_elements ps" using list_all2_members[OF rows(1)] data by blast
  then show ?thesis using rows(2) by blast
qed

section \<open>The element comparison owns its meaning at the presented source\<close>

lemma related_set_at_source:
  assumes source: "rel_set R A P"
    and compare: "\<And>a p q. R a p \<Longrightarrow> C p q \<longleftrightarrow> R a q"
  shows "rel_set C P Q \<longleftrightarrow> rel_set R A Q"
proof
  assume relation: "rel_set C P Q"
  show "rel_set R A Q"
  proof (rule rel_setI)
    fix a assume "a\<in>A"
    then obtain p where first: "p\<in>P" "R a p" using source by (simp only: rel_set_def) blast
    obtain q where second: "q\<in>Q" "C p q" using relation first(1) by (simp only: rel_set_def) blast
    have "R a q" using second(2) by (simp only: compare[OF first(2)])
    then show "\<exists>q\<in>Q. R a q" using second(1) by blast
  next
    fix q assume "q\<in>Q"
    then obtain p where first: "p\<in>P" "C p q" using relation by (simp only: rel_set_def) blast
    obtain a where second: "a\<in>A" "R a p" using source first(1) by (simp only: rel_set_def) blast
    have "R a q" using first(2) by (simp only: compare[OF second(2)])
    then show "\<exists>a\<in>A. R a q" using second(1) by blast
  qed
next
  assume relation: "rel_set R A Q"
  show "rel_set C P Q"
  proof (rule rel_setI)
    fix p assume "p\<in>P"
    then obtain a where first: "a\<in>A" "R a p" using source by (simp only: rel_set_def) blast
    obtain q where second: "q\<in>Q" "R a q" using relation first(1) by (simp only: rel_set_def) blast
    have "C p q" using second(2) by (simp only: compare[OF first(2)])
    then show "\<exists>q\<in>Q. C p q" using second(1) by blast
  next
    fix q assume "q\<in>Q"
    then obtain a where first: "a\<in>A" "R a q" using relation by (simp only: rel_set_def) blast
    obtain p where second: "p\<in>P" "R a p" using source first(1) by (simp only: rel_set_def) blast
    have "C p q" using first(2) by (simp only: compare[OF second(2)])
    then show "\<exists>p\<in>P. C p q" using second(1) by blast
  qed
qed

theorem data_list_fset_comparison_output:
  assumes elements: "presentation_class R D A"
    and source: "data_list_fset_presents R S p"
    and data: "\<And>a t. R a t \<Longrightarrow> term_formed t \<and> self_contained_term t"
    and compare: "\<And>a x y. R a x \<Longrightarrow> C x y \<longleftrightarrow> R a y"
  shows "(\<exists>ps qs. p=data_list_term ps \<and> q=data_list_term qs \<and>
      data_elements ps \<and> data_elements qs \<and> rel_set C (set ps) (set qs))
    \<longleftrightarrow> data_list_fset_presents R S q"
proof -
  obtain ps where first: "p=data_list_term ps" "data_elements ps"
    using data_list_fset_reading_data[where R=R and S=S and p=p, OF source] data by blast
  have coverage: "rel_set R (fset S) (set ps)"
    using source by (simp only: first(1)
      data_list_fset_reading_coverage[OF presentation_class.recovery[OF elements]])
  have compared: "rel_set C (set ps) (set qs) \<longleftrightarrow>
      data_list_fset_presents R S (data_list_term qs)" for qs
    by (simp only: related_set_at_source[where R=R and C=C and A="fset S" and P="set ps" and Q="set qs", OF coverage compare]
      data_list_fset_reading_coverage[OF presentation_class.recovery[OF elements]])
  show ?thesis
  proof
    assume "\<exists>us qs. p=data_list_term us \<and> q=data_list_term qs \<and>
      data_elements us \<and> data_elements qs \<and> rel_set C (set us) (set qs)"
    then obtain us qs where parts: "p=data_list_term us" "q=data_list_term qs"
      "rel_set C (set us) (set qs)" by blast
    have same: "us=ps" using parts(1) first(1) data_list_term_injective by blast
    have "data_list_fset_presents R S (data_list_term qs)"
      using parts(3) by (simp only: same compared)
    then show "data_list_fset_presents R S q" by (simp only: parts(2))
  next
    assume read: "data_list_fset_presents R S q"
    obtain qs where second: "q=data_list_term qs" "data_elements qs"
      using data_list_fset_reading_data[where R=R and S=S and p=q, OF read] data by blast
    have related: "rel_set C (set ps) (set qs)" using read by (simp only: second(1) compared)
    show "\<exists>us qs. p=data_list_term us \<and> q=data_list_term qs \<and>
      data_elements us \<and> data_elements qs \<and> rel_set C (set us) (set qs)"
      using first second related by blast
  qed
qed

text \<open>
  Every displayed member is read and every subject member is displayed.
  Unique recovery is needed to reconstruct the whole finite set from those
  two coverage conditions. The theorem permits any number and order of
  presentations of one member, including different presentations repeated
  together. Neither displayed occurrence counts nor inner forms become part
  of the recovered finite-set identity.

  The comparison equation is owned at every presented source element and
  accounts for every possible target term. Both coverage directions retain
  that operand order. No global symmetry or unrestricted element-domain
  equivalence is inferred from this local contract.
\<close>

end
