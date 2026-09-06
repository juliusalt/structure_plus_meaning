theory Factor_Generation_Values
  imports Factor_Target_Values RRA_Generation
begin

section \<open>Finite data quotations of exact generation cores\<close>

inductive generation_value_presents :: "generation_core \<Rightarrow> factor_term \<Rightarrow> bool" where
  generation: "target_value_presents l a \<Longrightarrow>
    data_collection_presents generation_value_presents (fset P) b \<Longrightarrow>
    target_value_presents p c \<Longrightarrow> target_value_presents q d \<Longrightarrow>
    generation_value_presents (Generation l P p q) (Pair_Term a (Pair_Term b (Pair_Term c d)))"

lemma generation_value_presents_cases:
  "generation_value_presents (Generation l P p q) t \<longleftrightarrow>
    (\<exists>a b c d. target_value_presents l a \<and>
      data_collection_presents generation_value_presents (fset P) b \<and>
      target_value_presents p c \<and> target_value_presents q d \<and>
      t=Pair_Term a (Pair_Term b (Pair_Term c d)))"
  by (auto elim: generation_value_presents.cases intro: generation_value_presents.generation)

theorem generation_value_presents_formed:
  assumes "generation_value_presents G t"
  shows "generation_formed G \<and> term_formed t \<and> self_contained_term t"
  using assms
proof (induction G arbitrary: t)
  case (Generation l P p q)
  obtain a b c d where fields: "target_value_presents l a"
    "data_collection_presents generation_value_presents (fset P) b"
    "target_value_presents p c" "target_value_presents q d"
    and encoded: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    using Generation.prems by (simp only: generation_value_presents_cases) blast
  have predecessors: "\<forall>H\<in>fset P. generation_formed H"
    using data_collection_presents_sources[OF fields(2)] Generation.IH by blast
  have lf: "target_formed l" and pf: "target_formed p" and qf: "target_formed q"
    using target_value_presents_formed[OF fields(1)]
      target_value_presents_formed[OF fields(3)] target_value_presents_formed[OF fields(4)] by auto
  have core: "generation_formed (Generation l P p q)"
    by (rule generation_formed.formed[OF lf pf qf predecessors])
  have bf: "term_formed b" by (rule data_collection_presents_formed[OF fields(2)])
    (use Generation.IH in blast)
  have bc: "self_contained_term b" by (rule data_collection_presents_self_contained[OF fields(2)])
    (use Generation.IH in blast)
  show ?case using core bf bc target_value_presents_formed[OF fields(1)]
    target_value_presents_formed[OF fields(3)] target_value_presents_formed[OF fields(4)] encoded by simp
qed

theorem generation_value_presents_unique:
  assumes "generation_value_presents G t" "generation_value_presents H t"
  shows "G=H"
  using assms
proof (induction G arbitrary: H t)
  case (Generation l P p q)
  obtain a b c d where first: "target_value_presents l a"
    "data_collection_presents generation_value_presents (fset P) b"
    "target_value_presents p c" "target_value_presents q d"
    and encoded: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    using Generation.prems(1) by (simp only: generation_value_presents_cases) blast
  obtain l' P' p' q' where shape: "H=Generation l' P' p' q'" by (cases H) auto
  obtain a' b' c' d' where second: "target_value_presents l' a'"
    "data_collection_presents generation_value_presents (fset P') b'"
    "target_value_presents p' c'" "target_value_presents q' d'"
    and encoded': "t=Pair_Term a' (Pair_Term b' (Pair_Term c' d'))"
    using Generation.prems(2) by (simp only: shape generation_value_presents_cases) blast
  have same_values: "a'=a" "b'=b" "c'=c" "d'=d" using encoded encoded' by simp_all
  have other: "target_value_presents l' a"
    "data_collection_presents generation_value_presents (fset P') b"
    "target_value_presents p' c" "target_value_presents q' d"
    using second same_values by simp_all
  have targets: "l=l'" "p=p'" "q=q'"
    using target_value_presents_unique[OF first(1) other(1)]
      target_value_presents_unique[OF first(3) other(3)]
      target_value_presents_unique[OF first(4) other(4)] by auto
  have predecessors: "fset P=fset P'"
    by (rule data_collection_presents_unique[OF first(2) other(2)])
      (use Generation.IH in blast)
  have "P=P'" using predecessors by (simp add: fset_inject)
  then show ?case using targets shape by simp
qed

theorem generation_value_presents_total:
  assumes "generation_formed G"
  shows "\<exists>t. generation_value_presents G t"
  using assms
proof (induction rule: generation_formed.induct)
  case (formed l p q P)
  obtain a where locus: "target_value_presents l a"
    using target_value_presents_total[OF formed.hyps(1)] by blast
  obtain c where payload: "target_value_presents p c"
    using target_value_presents_total[OF formed.hyps(2)] by blast
  obtain d where cause: "target_value_presents q d"
    using target_value_presents_total[OF formed.hyps(3)] by blast
  have each: "\<forall>H\<in>fset P. \<exists>t. generation_value_presents H t" using formed.IH by blast
  obtain b where predecessors: "data_collection_presents generation_value_presents (fset P) b"
    using data_collection_presents_total[OF finite_fset each] by blast
  show ?case using generation_value_presents.generation[OF locus predecessors payload cause] by blast
qed

theorem generation_value_quotation_total:
  assumes "generation_formed G"
  shows "\<exists>t C. generation_value_presents G t \<and> complete_data_quoted_at C [] t"
proof -
  obtain t where present: "generation_value_presents G t"
    using generation_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using generation_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  A generation value contains its exact locus, complete predecessor collection,
  payload, and cause. Each target contains its artifact data, and predecessors
  are represented recursively. Every formed core has a finite complete native
  quotation with no external slots. Equal represented values recover equal
  exact cores. Predecessor collections admit every complete order and every
  allowed presentation of their members; no canonical order is selected.

  This is data recovery. It neither validates the recorded cause nor introduces
  a publication, authority, or evidence field into generation identity.
\<close>

end
