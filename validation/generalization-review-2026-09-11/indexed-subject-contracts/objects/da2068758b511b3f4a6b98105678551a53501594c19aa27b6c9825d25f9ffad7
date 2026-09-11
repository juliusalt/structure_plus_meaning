theory Factor_Generation_Values
  imports Factor_Target_Presentations Factor_Finite_Set_Presentations RRA_Generation
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

section \<open>Bounded classes combine to cover every finite core\<close>

abbreviation generation_value_stage :: "nat \<Rightarrow> generation_core \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_value_stage n G t \<equiv> (generation_formed G \<and> size G<n) \<and> generation_value_presents G t"

lemma generation_value_stage_class:
  "presentation_class (generation_value_stage n) (\<lambda>G. generation_formed G \<and> size G<n)
    (\<lambda>t. \<exists>G. generation_value_stage n G t)"
proof (induction n)
  case 0
  show ?case by (simp add: presentation_class_def)
next
  case (Suc n)
  let ?T="\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  let ?P="presented_predicate (data_sequence_presents (generation_value_stage n)) distinct"
  let ?tail="\<lambda>t. \<exists>p q. ?T p \<and> ?T q \<and> t=Pair_Term p q"
  let ?middle="\<lambda>t. \<exists>p q. ?P p \<and> ?tail q \<and> t=Pair_Term p q"
  let ?A="\<lambda>t. \<exists>p q. ?T p \<and> ?middle q \<and> t=Pair_Term p q"
  let ?R="factor_pair_presents target_value_presents
    (factor_pair_presents (data_fset_presents (generation_value_stage n))
      (factor_pair_presents target_value_presents target_value_presents))"
  let ?D="\<lambda>z. target_formed (fst z) \<and>
    ((\<forall>H\<in>fset (fst (snd z)). generation_formed H \<and> size H<n) \<and>
      (target_formed (fst (snd (snd z))) \<and> target_formed (snd (snd (snd z)))))"
  have fields: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF target_value_presentation_class
      factor_pair_class[OF data_fset_presentation_class[OF Suc.IH]
        factor_pair_class[OF target_value_presentation_class target_value_presentation_class]]])
  let ?observe="\<lambda>G. (generation_locus G,(generation_predecessors G,
    (generation_payload G,generation_cause G)))"
  let ?domain="\<lambda>G. generation_formed G \<and> size G<Suc n"
  have smaller: "\<forall>H\<in>fset (generation_predecessors G). generation_formed H \<and> size H<n"
    if parent: "?domain G" for G
  proof (intro ballI)
    fix H assume member: "H\<in>fset (generation_predecessors G)"
    have formed: "generation_formed H"
      using generation_formed_fields[OF conjunct1[OF parent]] member by blast
    have decreased: "size H<size G"
      by (rule predecessor_size_decreases) (use member in \<open>simp add: predecessor_edges_def\<close>)
    have bound: "size H<n" using decreased parent by arith
    show "generation_formed H \<and> size H<n" using formed bound by blast
  qed
  have observed: "presentation_class (\<lambda>G t. ?domain G \<and> ?R (?observe G) t)
      ?domain (\<lambda>t. \<exists>G. ?domain G \<and> ?R (?observe G) t)"
  proof (rule presentation_class_observations[OF fields])
    fix G assume domain: "?domain G"
    show "?D (?observe G)"
      using generation_formed_fields[OF conjunct1[OF domain]] smaller[OF domain] by simp
  next
    fix G H assume "?domain G" "?domain H" "?observe G=?observe H"
    then show "G=H" by (simp add: generation_identity)
  qed
  have reading: "(?domain G \<and> ?R (?observe G) t) \<longleftrightarrow> generation_value_stage (Suc n) G t" for G t
    using smaller[of G]
    by (cases G) (auto simp: factor_pair_presents_def generation_value_presents_cases
      data_collection_presents_constrain; blast)
  show ?case using observed by (simp only: reading)
qed

theorem generation_value_presentation_class:
  "presentation_class generation_value_presents generation_formed
    (\<lambda>t. \<exists>G. generation_value_presents G t)"
proof -
  have united: "presentation_class (\<lambda>G t. \<exists>n\<in>UNIV. generation_value_stage n G t)
      (\<lambda>G. \<exists>n\<in>UNIV. generation_formed G \<and> size G<n)
      (\<lambda>t. \<exists>n\<in>UNIV. \<exists>G. generation_value_stage n G t)"
  proof (rule presentation_class_directed_union)
    fix n :: nat assume "n\<in>UNIV"
    show "presentation_class (generation_value_stage n) (\<lambda>G. generation_formed G \<and> size G<n)
      (\<lambda>t. \<exists>G. generation_value_stage n G t)" by (rule generation_value_stage_class)
  next
    fix i j :: nat assume "i\<in>UNIV" "j\<in>UNIV"
    show "\<exists>k\<in>UNIV. (\<forall>G t. generation_value_stage i G t \<longrightarrow> generation_value_stage k G t) \<and>
      (\<forall>G t. generation_value_stage j G t \<longrightarrow> generation_value_stage k G t)"
      by (rule bexI[of _ "max i j"]) (auto intro: less_le_trans)
  qed
  have domain: "(\<exists>n\<in>UNIV. generation_formed G \<and> size G<n) \<longleftrightarrow> generation_formed G" for G
  proof
    assume "\<exists>n\<in>UNIV. generation_formed G \<and> size G<n"
    then show "generation_formed G" by blast
  next
    assume "generation_formed G"
    then show "\<exists>n\<in>UNIV. generation_formed G \<and> size G<n"
      by (rule_tac x="Suc (size G)" in bexI) simp_all
  qed
  have reading: "(\<exists>n\<in>UNIV. generation_value_stage n G t) \<longleftrightarrow> generation_value_presents G t" for G t
  proof
    assume "\<exists>n\<in>UNIV. generation_value_stage n G t"
    then show "generation_value_presents G t" by blast
  next
    assume read: "generation_value_presents G t"
    have formed: "generation_formed G" using generation_value_presents_formed[OF read] by blast
    show "\<exists>n\<in>UNIV. generation_value_stage n G t"
      by (rule bexI[of _ "Suc (size G)"]) (use read formed in simp_all)
  qed
  have admission: "(\<exists>n\<in>UNIV. \<exists>G. generation_value_stage n G t) \<longleftrightarrow>
      (\<exists>G. generation_value_presents G t)" for t
    using reading by blast
  show ?thesis using united by (simp only: reading domain admission)
qed

interpretation generation_values: presentation_class generation_value_presents generation_formed
  "\<lambda>t. \<exists>G. generation_value_presents G t"
  by (rule generation_value_presentation_class)

theorem generation_value_presents_unique:
  assumes "generation_value_presents G t" "generation_value_presents H t"
  shows "G=H"
  by (rule generation_values.recovery[OF assms])

theorem generation_value_presents_total:
  assumes "generation_formed G"
  shows "\<exists>t. generation_value_presents G t"
  by (rule generation_values.total[OF assms])

theorem generation_quotation_presentation_class:
  "presentation_class
    (composed_presentation generation_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    generation_formed
    (\<lambda>p. \<exists>t. (\<exists>G. generation_value_presents G t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_value_presentation_class])
    (use generation_value_presents_formed in blast)

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

  The class is derived through target products and finite-set classes at each
  size bound, followed by the general directed union rule. Every formed finite
  core lies below a bound, and every existing value presentation lies in the
  union. Totality and recovery follow from that construction. The bound is not
  stored, and complete quotation composes with the full recursive value.

  This is data recovery. It neither validates the recorded cause nor introduces
  a publication, authority, or evidence field into generation identity.
\<close>

end
