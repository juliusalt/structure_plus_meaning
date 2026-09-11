theory Factor_Fragment_Presentations
  imports RRA_Fragment Factor_Structural_Collections
begin

section \<open>A fragment presents its complete source and exact selection\<close>

definition fragment_value_presents :: "exact_fragment \<Rightarrow> factor_term \<Rightarrow> bool" where
  "fragment_value_presents F p \<longleftrightarrow> fragment_formed F \<and>
    factor_pair_presents artifact_value_presents payload_set_presents
      (fragment_source F,fragment_selection F) p"

lemma fragment_selection_boundary:
  assumes "fragment_formed F"
  shows "finite (fragment_selection F) \<and> (\<forall>a\<in>fragment_selection F. octets_formed a)"
  using assms by (auto simp: fragment_formed_def exact_formed_def)

theorem fragment_value_presentation_class:
  "presentation_class fragment_value_presents fragment_formed (\<lambda>p. \<exists>F. fragment_value_presents F p)"
proof -
  let ?D="\<lambda>z. exact_formed (fst z) \<and> finite (snd z) \<and> (\<forall>a\<in>snd z. octets_formed a)"
  let ?R="factor_pair_presents artifact_value_presents payload_set_presents"
  have pair: "presentation_class ?R ?D
      (\<lambda>t. \<exists>p q. (11,p)\<in>positive_meaning artifact_admission_system \<and>
        (1,q)\<in>positive_meaning distinct_payloads_system \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF artifact_presentations.presentation_class_axioms payload_set_presentation_class])
  have observation: "presentation_class
      (\<lambda>F p. fragment_formed F \<and> ?R (fragment_source F,fragment_selection F) p)
      fragment_formed (\<lambda>p. \<exists>F. fragment_formed F \<and> ?R (fragment_source F,fragment_selection F) p)"
  proof (rule presentation_class_observations[OF pair])
    fix F assume formed: "fragment_formed F"
    show "?D (fragment_source F,fragment_selection F)"
      using formed fragment_selection_boundary[OF formed] by (simp add: fragment_formed_def)
  next
    fix F G assume "fragment_formed F" "fragment_formed G"
      "(fragment_source F,fragment_selection F)=(fragment_source G,fragment_selection G)"
    then show "F=G" by (cases F; cases G) auto
  qed
  show ?thesis using observation by (simp only: presentation_class_def fragment_value_presents_def)
qed

interpretation fragments: presentation_class fragment_value_presents fragment_formed
  "\<lambda>p. \<exists>F. fragment_value_presents F p"
  by (rule fragment_value_presentation_class)

lemma fragment_value_fields:
  "fragment_value_presents F (Pair_Term p q) \<longleftrightarrow>
    fragment_formed F \<and> artifact_value_presents (fragment_source F) p \<and>
    payload_set_presents (fragment_selection F) q"
  by (simp add: fragment_value_presents_def)

lemma fragment_value_enumerations:
  "fragment_value_presents G p \<longleftrightarrow>
    (\<exists>A E B F c. fragment_formed G \<and> artifact_enumeration (fragment_source G) A E B F \<and>
      payload_set_presents (fragment_selection G) c \<and> p=Pair_Term (artifact_data_term A E B F) c)"
  by (auto simp: fragment_value_presents_def factor_pair_presents_def artifact_value_presents_def; blast)

lemma fragment_value_formed:
  assumes "fragment_value_presents F p"
  shows "term_formed p \<and> self_contained_term p"
  using assms artifact_value_presents_formed payload_set_formed
  by (auto simp: fragment_value_presents_def factor_pair_presents_def)

theorem fragment_value_quotation_class:
  "presentation_class
    (composed_presentation fragment_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    fragment_formed
    (\<lambda>p. \<exists>t. (\<exists>F. fragment_value_presents F t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF fragment_value_presentation_class])
    (use fragment_value_formed in blast)

section \<open>The boundary and omission are derived from that same source\<close>

lemma fragment_boundary_coordinates:
  assumes formed: "fragment_formed F"
  shows "finite (fragment_boundary F) \<and> (\<forall>z\<in>fragment_boundary F. incidence_coordinates_formed z)"
proof -
  let ?S="object_structure (fragment_source F)"
  have subset: "fragment_boundary F\<subseteq>rra_incidence ?S"
    by (auto simp: fragment_boundary_def crossing_incidence_def touching_incidence_def)
  have rf: "rra_formed ?S" and addresses: "\<forall>a\<in>rra_carrier ?S. octets_formed a"
    using formed by (auto simp: fragment_formed_def exact_formed_def object_formed_def)
  have finite: "finite (fragment_boundary F)"
    by (rule finite_subset[OF subset]) (use rf in \<open>simp add: rra_formed_def\<close>)
  show ?thesis using finite subset rf addresses
    by (auto simp: rra_formed_def; blast)
qed

lemma fragment_omission_coordinates:
  assumes "fragment_formed F"
  shows "finite (fragment_omission F) \<and> (\<forall>a\<in>fragment_omission F. octets_formed a)"
  using assms by (auto simp: fragment_omission_def fragment_formed_def exact_formed_def object_formed_def rra_formed_def)

abbreviation fragment_views ::
  "exact_fragment \<Rightarrow> exact_artifact\<times>((local_address\<times>local_address\<times>local_address) set\<times>exact_artifact)" where
  "fragment_views F \<equiv> (fragment_material F,(fragment_boundary F,fragment_remainder F))"

abbreviation fragment_views_presents ::
  "(exact_artifact\<times>((local_address\<times>local_address\<times>local_address) set\<times>exact_artifact)) \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "fragment_views_presents \<equiv> factor_pair_presents artifact_value_presents
    (factor_pair_presents incidence_set_presents artifact_value_presents)"

abbreviation fragment_views_formed ::
  "(exact_artifact\<times>((local_address\<times>local_address\<times>local_address) set\<times>exact_artifact)) \<Rightarrow> bool" where
  "fragment_views_formed z \<equiv> exact_formed (fst z) \<and>
    (finite (fst (snd z)) \<and> (\<forall>e\<in>fst (snd z). incidence_coordinates_formed e)) \<and> exact_formed (snd (snd z))"

theorem fragment_views_presentation_class:
  "presentation_class fragment_views_presents fragment_views_formed
    (\<lambda>p. \<exists>z. fragment_views_presents z p)"
proof -
  have nested: "presentation_class (factor_pair_presents incidence_set_presents artifact_value_presents)
      (\<lambda>z. (finite (fst z) \<and> (\<forall>e\<in>fst z. incidence_coordinates_formed e)) \<and> exact_formed (snd z))
      (\<lambda>t. \<exists>p q. presented_predicate (data_sequence_presents incidence_value_presents) distinct p \<and>
        (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF incidence_set_presentation_class artifact_presentations.presentation_class_axioms])
  have pair: "presentation_class fragment_views_presents fragment_views_formed
      (\<lambda>t. \<exists>p q. (11,p)\<in>positive_meaning artifact_admission_system \<and>
        (\<exists>b r. presented_predicate (data_sequence_presents incidence_value_presents) distinct b \<and>
          (11,r)\<in>positive_meaning artifact_admission_system \<and> q=Pair_Term b r) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF artifact_presentations.presentation_class_axioms nested])
  show ?thesis
  proof (rule presentation_class.intro)
    fix z p assume presented: "fragment_views_presents z p"
    show "fragment_views_formed z" by (rule presentation_class.subject_boundary[OF pair presented])
    show "\<exists>z. fragment_views_presents z p" using presented by blast
  next
    fix z assume "fragment_views_formed z"
    then show "\<exists>p. fragment_views_presents z p" by (rule presentation_class.total[OF pair])
  next
    fix p assume "\<exists>z. fragment_views_presents z p"
    then show "\<exists>z. fragment_views_presents z p" .
  next
    fix z p z' assume "fragment_views_presents z p" "fragment_views_presents z' p"
    then show "z=z'" by (rule presentation_class.recovery[OF pair])
  qed
qed

lemma fragment_views_boundary:
  assumes "fragment_formed F"
  shows "fragment_views_formed (fragment_views F)"
  using fragment_material_formed[OF assms] fragment_remainder_formed[OF assms]
    fragment_boundary_coordinates[OF assms] by simp

definition fragment_report_presents :: "exact_fragment \<Rightarrow> factor_term \<Rightarrow> bool" where
  "fragment_report_presents F t \<longleftrightarrow>
    factor_pair_presents fragment_value_presents fragment_views_presents (F,fragment_views F) t"

theorem fragment_report_presentation_class:
  "presentation_class fragment_report_presents fragment_formed (\<lambda>t. \<exists>F. fragment_report_presents F t)"
proof -
  have pair: "presentation_class (factor_pair_presents fragment_value_presents fragment_views_presents)
      (\<lambda>z. fragment_formed (fst z) \<and> fragment_views_formed (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>F. fragment_value_presents F p) \<and>
        (\<exists>z. fragment_views_presents z q) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF fragment_value_presentation_class fragment_views_presentation_class])
  have observed: "presentation_class
      (\<lambda>F t. fragment_formed F \<and>
        factor_pair_presents fragment_value_presents fragment_views_presents (F,fragment_views F) t)
      fragment_formed
      (\<lambda>t. \<exists>F. fragment_formed F \<and>
        factor_pair_presents fragment_value_presents fragment_views_presents (F,fragment_views F) t)"
    by (rule presentation_class_observations[OF pair])
      (use fragment_views_boundary in auto)
  have source: "factor_pair_presents fragment_value_presents fragment_views_presents (F,fragment_views F) t
      \<Longrightarrow> fragment_formed F" for F t
    using fragments.subject_boundary by (auto simp: factor_pair_presents_def)
  have relation: "fragment_report_presents=(\<lambda>F t. fragment_formed F \<and>
      factor_pair_presents fragment_value_presents fragment_views_presents (F,fragment_views F) t)"
    by (intro ext) (use source in \<open>auto simp only: fragment_report_presents_def\<close>)
  show ?thesis using observed by (simp only: relation)
qed

lemma fragment_report_formed:
  assumes "fragment_report_presents F t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p m b r where source: "fragment_value_presents F p"
    and material: "artifact_value_presents (fragment_material F) m"
    and boundary: "incidence_set_presents (fragment_boundary F) b"
    and remainder: "artifact_value_presents (fragment_remainder F) r"
    and shape: "t=Pair_Term p (Pair_Term m (Pair_Term b r))"
    using assms by (auto simp: fragment_report_presents_def factor_pair_presents_def)
  show ?thesis using fragment_value_formed[OF source] artifact_value_presents_formed[OF material]
    incidence_set_formed[OF boundary] artifact_value_presents_formed[OF remainder] by (simp add: shape)
qed

theorem fragment_report_quotation_class:
  "presentation_class
    (composed_presentation fragment_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    fragment_formed
    (\<lambda>p. \<exists>t. (\<exists>F. fragment_report_presents F t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF fragment_report_presentation_class])
    (use fragment_report_formed in blast)

text \<open>
  The independently defined fragment remains one exact source artifact and one
  finite selected carrier. Its class is the general product and observation
  construction restricted by the existing fragment relation. No material,
  omission, crossing incidence, or remainder is added to that primitive basis.

  A complete report keeps the same fragment and presents all three derived
  structural views. Every compatible component presentation is available.
  Quotation preserves each report's complete actual body; it does not privilege
  any order in the source fields, selected carrier, or boundary collection.
\<close>

end
