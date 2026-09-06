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

theorem publication_value_presents_unique:
  assumes first: "publication_value_presents P t" and second: "publication_value_presents Q t"
  shows "P=Q"
proof -
  obtain s d e where left:
    "data_collection_presents generation_value_presents (fset (publication_snapshot P)) s"
    "data_collection_presents target_value_presents (fset (publication_dependencies P)) d"
    "data_collection_presents target_value_presents (fset (publication_evidence P)) e"
    "t=Pair_Term s (Pair_Term d e)"
    using first unfolding publication_value_presents_def by blast
  obtain s' d' e' where right:
    "data_collection_presents generation_value_presents (fset (publication_snapshot Q)) s'"
    "data_collection_presents target_value_presents (fset (publication_dependencies Q)) d'"
    "data_collection_presents target_value_presents (fset (publication_evidence Q)) e'"
    "t=Pair_Term s' (Pair_Term d' e')"
    using second unfolding publication_value_presents_def by blast
  have same: "s'=s" "d'=d" "e'=e" using left(4) right(4) by simp_all
  have other:
    "data_collection_presents generation_value_presents (fset (publication_snapshot Q)) s"
    "data_collection_presents target_value_presents (fset (publication_dependencies Q)) d"
    "data_collection_presents target_value_presents (fset (publication_evidence Q)) e"
    using right same by simp_all
  have snapshots: "fset (publication_snapshot P)=fset (publication_snapshot Q)"
    by (rule data_collection_presents_unique[OF left(1) other(1)])
      (rule generation_value_presents_unique; assumption)
  have dependencies: "fset (publication_dependencies P)=fset (publication_dependencies Q)"
    by (rule data_collection_presents_unique[OF left(2) other(2)])
      (rule target_value_presents_unique; assumption)
  have evidence: "fset (publication_evidence P)=fset (publication_evidence Q)"
    by (rule data_collection_presents_unique[OF left(3) other(3)])
      (rule target_value_presents_unique; assumption)
  show ?thesis using snapshots dependencies evidence
    by (simp add: publication_view_identity fset_inject)
qed

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
proof -
  have cores: "\<forall>G\<in>fset (publication_snapshot P). generation_formed G"
    and deps: "\<forall>x\<in>fset (publication_dependencies P). target_formed x"
    and evid: "\<forall>x\<in>fset (publication_evidence P). target_formed x"
    using formed by (auto simp: publication_formed_def snapshot_formed_def selection_formed_def)
  have each_core: "\<forall>G\<in>fset (publication_snapshot P). \<exists>t. generation_value_presents G t"
    using cores generation_value_presents_total by blast
  have each_dep: "\<forall>x\<in>fset (publication_dependencies P). \<exists>t. target_value_presents x t"
    using deps target_value_presents_total by blast
  have each_evid: "\<forall>x\<in>fset (publication_evidence P). \<exists>t. target_value_presents x t"
    using evid target_value_presents_total by blast
  obtain s where snapshot:
    "data_collection_presents generation_value_presents (fset (publication_snapshot P)) s"
    using data_collection_presents_total[OF finite_fset each_core] by blast
  obtain d where dependencies:
    "data_collection_presents target_value_presents (fset (publication_dependencies P)) d"
    using data_collection_presents_total[OF finite_fset each_dep] by blast
  obtain e where evidence:
    "data_collection_presents target_value_presents (fset (publication_evidence P)) e"
    using data_collection_presents_total[OF finite_fset each_evid] by blast
  show ?thesis using formed snapshot dependencies evidence
    unfolding publication_value_presents_def by blast
qed

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

  The representation has no validity or adoption field. An evidence selection
  remains a selection of exact material, and snapshot formation checks only
  its existing at-most-one-generation-per-locus condition.
\<close>

end
