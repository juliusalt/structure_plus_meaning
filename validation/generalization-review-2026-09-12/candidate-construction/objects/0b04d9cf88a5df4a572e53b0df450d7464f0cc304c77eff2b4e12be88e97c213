theory Factor_Publication_Values
  imports Factor_Generation_Values RRA_Publication
begin

section \<open>Complete publication selections as inspectable data\<close>

definition publication_value_presents :: "publication_view \<Rightarrow> factor_term \<Rightarrow> bool" where
  "publication_value_presents P t \<longleftrightarrow> publication_formed P \<and>
    (\<exists>s d e. data_collection_presents generation_value_presents (fset (publication_snapshot P)) s \<and>
      data_collection_presents target_value_presents (fset (publication_dependencies P)) d \<and>
      data_collection_presents target_value_presents (fset (publication_evidence P)) e \<and>
      t=Pair_Term s (Pair_Term d e))"

theorem publication_value_presentation_class:
  "presentation_class publication_value_presents publication_formed
    (\<lambda>t. \<exists>P. publication_value_presents P t)"
proof -
  let ?G="presented_predicate (data_sequence_presents generation_value_presents) distinct"
  let ?T="presented_predicate (data_sequence_presents target_value_presents) distinct"
  let ?tail="\<lambda>t. \<exists>p q. ?T p \<and> ?T q \<and> t=Pair_Term p q"
  let ?A="\<lambda>t. \<exists>p q. ?G p \<and> ?tail q \<and> t=Pair_Term p q"
  let ?R="factor_pair_presents (data_fset_presents generation_value_presents)
    (factor_pair_presents (data_fset_presents target_value_presents) (data_fset_presents target_value_presents))"
  let ?D="\<lambda>z. (\<forall>G\<in>fset (fst z). generation_formed G) \<and>
    ((\<forall>x\<in>fset (fst (snd z)). target_formed x) \<and> (\<forall>x\<in>fset (snd (snd z)). target_formed x))"
  have fields: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF data_fset_presentation_class[OF generation_value_presentation_class]
      factor_pair_class[OF data_fset_presentation_class[OF target_value_presentation_class]
        data_fset_presentation_class[OF target_value_presentation_class]]])
  let ?observe="\<lambda>P. (publication_snapshot P,(publication_dependencies P,publication_evidence P))"
  have observed: "presentation_class (\<lambda>P t. publication_formed P \<and> ?R (?observe P) t)
      publication_formed (\<lambda>t. \<exists>P. publication_formed P \<and> ?R (?observe P) t)"
  proof (rule presentation_class_observations[OF fields])
    fix P assume "publication_formed P"
    then show "?D (?observe P)" by (simp add: publication_formed_def snapshot_formed_def selection_formed_def)
  next
    fix P Q assume "publication_formed P" "publication_formed Q" "?observe P=?observe Q"
    then show "P=Q" by (simp add: publication_view_identity)
  qed
  have reading: "(publication_formed P \<and> ?R (?observe P) t) \<longleftrightarrow> publication_value_presents P t" for P t
    by (auto simp: publication_value_presents_def factor_pair_presents_def; blast)
  show ?thesis using observed by (simp only: reading)
qed

interpretation publication_values: presentation_class publication_value_presents publication_formed
  "\<lambda>t. \<exists>P. publication_value_presents P t"
  by (rule publication_value_presentation_class)

theorem publication_value_presents_unique:
  assumes first: "publication_value_presents P t" and second: "publication_value_presents Q t"
  shows "P=Q"
  by (rule publication_values.recovery[OF first second])

lemma publication_value_presents_formed:
  assumes "publication_value_presents P t"
  shows "publication_formed P \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain s d e where formed: "publication_formed P" and fields:
    "data_collection_presents generation_value_presents (fset (publication_snapshot P)) s"
    "data_collection_presents target_value_presents (fset (publication_dependencies P)) d"
    "data_collection_presents target_value_presents (fset (publication_evidence P)) e"
    "t=Pair_Term s (Pair_Term d e)"
    using assms unfolding publication_value_presents_def by blast
  have sf: "term_formed s" by (rule data_collection_presents_formed[OF fields(1)])
    (meson generation_value_presents_formed)
  have df: "term_formed d" by (rule data_collection_presents_formed[OF fields(2)])
    (meson target_value_presents_formed)
  have ef: "term_formed e" by (rule data_collection_presents_formed[OF fields(3)])
    (meson target_value_presents_formed)
  have sc: "self_contained_term s" by (rule data_collection_presents_self_contained[OF fields(1)])
    (meson generation_value_presents_formed)
  have dc: "self_contained_term d" by (rule data_collection_presents_self_contained[OF fields(2)])
    (meson target_value_presents_formed)
  have ec: "self_contained_term e" by (rule data_collection_presents_self_contained[OF fields(3)])
    (meson target_value_presents_formed)
  show ?thesis using formed fields(4) sf df ef sc dc ec by simp
qed

theorem publication_value_presents_total:
  assumes formed: "publication_formed P"
  shows "\<exists>t. publication_value_presents P t"
  by (rule publication_values.total[OF formed])

theorem publication_quotation_presentation_class:
  "presentation_class
    (composed_presentation publication_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    publication_formed
    (\<lambda>p. \<exists>t. (\<exists>P. publication_value_presents P t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF publication_value_presentation_class])
    (use publication_value_presents_formed in blast)

theorem publication_value_quotation_total:
  assumes "publication_formed P"
  shows "\<exists>t C. publication_value_presents P t \<and> complete_data_quoted_at C [] t"
proof -
  obtain t where present: "publication_value_presents P t"
    using publication_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using publication_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  Every selected core, declared dependency, and evidence target is present.
  All three collections retain their finite-set meaning and admit every
  complete order. Complete native quotation determines these recovered fields
  independently of outer bindings. Equal publication views do not identify
  their different presentation sites.

  Finite-set classes and products supply the complete field record. The
  observation construction restricts it to the existing publication-formation
  domain and recovers the whole view. Totality and uniqueness follow from
  that class, and quotation composes with the entire value.

  The representation has no validity or adoption field. An evidence selection
  remains a selection of exact material, and snapshot formation checks only
  its existing at-most-one-generation-per-locus condition.
\<close>

end
