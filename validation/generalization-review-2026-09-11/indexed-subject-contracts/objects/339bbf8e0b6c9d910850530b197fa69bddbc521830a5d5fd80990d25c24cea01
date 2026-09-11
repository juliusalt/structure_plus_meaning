theory Factor_Quoted_Artifacts
  imports Factor_Presentation_Transport
begin

section \<open>A complete artifact determines its actual data body\<close>

definition quoted_artifact_presents :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "quoted_artifact_presents t c \<longleftrightarrow>
    (\<exists>C r. artifact_value_presents C c \<and> complete_data_quoted_at C r t)"

theorem quoted_artifact_presentation:
  "presentation_class quoted_artifact_presents
    (\<lambda>t. term_formed t \<and> self_contained_term t)
    (\<lambda>c. \<exists>t. quoted_artifact_presents t c)"
proof -
  let ?L="\<lambda>C t. \<exists>r. complete_data_quoted_at C r t"
  have determined: "t=v" if "?L C t" "?L C v" for C t v
    using that complete_data_quotation_whole_unique by blast
  have linked: "presentation_class
      (\<lambda>z c. artifact_value_presents (fst z) c \<and> ?L (fst z) (snd z))
      (\<lambda>z. exact_formed (fst z) \<and> ?L (fst z) (snd z))
      (\<lambda>c. \<exists>C t. artifact_value_presents C c \<and> ?L C t)"
    by (rule presentation_class_determined[OF artifact_presentations.presentation_class_axioms determined])
  have projected: "presentation_class
      (\<lambda>t c. \<exists>z. (artifact_value_presents (fst z) c \<and> ?L (fst z) (snd z)) \<and> snd z=t)
      (\<lambda>t. term_formed t \<and> self_contained_term t)
      (\<lambda>c. \<exists>C t. artifact_value_presents C c \<and> ?L C t)"
  proof (rule presentation_class_image[OF linked])
    fix z assume "exact_formed (fst z) \<and> ?L (fst z) (snd z)"
    then show "term_formed (snd z) \<and> self_contained_term (snd z)"
      by (auto simp: complete_data_quoted_at_def)
  next
    fix t assume formed: "term_formed t \<and> self_contained_term t"
    have quote: "complete_data_quoted_at (term_syntax t) [] t"
      by (rule complete_data_quotation_total) (use formed in auto)
    show "\<exists>z. (exact_formed (fst z) \<and> ?L (fst z) (snd z)) \<and> snd z=t"
      by (rule exI[of _ "(term_syntax t,t)"])
        (use quote complete_data_quotation_formed[OF quote] in auto)
  qed
  have reading: "(\<lambda>t c. \<exists>z. (artifact_value_presents (fst z) c \<and> ?L (fst z) (snd z)) \<and> snd z=t)
      =quoted_artifact_presents"
    by (intro ext) (auto simp: quoted_artifact_presents_def; metis fst_conv snd_conv)
  have admission: "(\<lambda>c. \<exists>C t. artifact_value_presents C c \<and> ?L C t)=
      (\<lambda>c. \<exists>t. quoted_artifact_presents t c)"
    by (intro ext) (auto simp: quoted_artifact_presents_def)
  show ?thesis using projected by (simp only: reading admission)
qed

interpretation quoted_artifacts: presentation_class quoted_artifact_presents
  "\<lambda>t. term_formed t \<and> self_contained_term t"
  "\<lambda>c. \<exists>t. quoted_artifact_presents t c"
  by (rule quoted_artifact_presentation)

lemma quoted_artifact_presents_formed:
  assumes "quoted_artifact_presents t c"
  shows "term_formed c \<and> self_contained_term c"
  using assms artifact_value_presents_formed by (auto simp: quoted_artifact_presents_def)

theorem quoted_artifact_presentation_class:
  assumes source: "presentation_class R D A"
    and boundary: "\<And>t. A t \<Longrightarrow> term_formed t \<and> self_contained_term t"
  shows "presentation_class (composed_presentation R quoted_artifact_presents) D
    (\<lambda>c. \<exists>t. A t \<and> quoted_artifact_presents t c)"
proof -
  have result: "presentation_class (composed_presentation R quoted_artifact_presents) D
      (\<lambda>c. (\<exists>v. quoted_artifact_presents v c) \<and> (\<exists>t. A t \<and> quoted_artifact_presents t c))"
    by (rule presentation_class_compose_on[OF source quoted_artifact_presentation boundary])
  have admission: "(\<lambda>c. (\<exists>v. quoted_artifact_presents v c) \<and>
      (\<exists>t. A t \<and> quoted_artifact_presents t c)) =
      (\<lambda>c. \<exists>t. A t \<and> quoted_artifact_presents t c)"
    by (intro ext) blast
  show ?thesis using result by (simp only: admission)
qed

lemma quoted_artifact_at_source:
  assumes source: "artifact_value_presents C c"
  shows "quoted_artifact_presents t c \<longleftrightarrow> (\<exists>r. complete_data_quoted_at C r t)"
proof -
  have predicate: "quoted_artifact_presents t c \<longleftrightarrow>
      presented_predicate artifact_value_presents (\<lambda>C. \<exists>r. complete_data_quoted_at C r t) c"
    by (simp only: quoted_artifact_presents_def presented_predicate_def) blast
  show ?thesis by (simp only: predicate artifact_presentations.predicate_at[OF source])
qed

lemma quoted_artifact_body_report:
  "quoted_body_presents t (Pair_Term c v) \<longleftrightarrow>
    quoted_artifact_presents t c \<and> v=t"
  by (auto simp: quoted_body_presents_def quoted_artifact_presents_def)

text \<open>
  The complete artifact determines its quotation root and actual body.
  The determined-component and covered-image constructions therefore recover
  that body from artifact data alone. No duplicate body or root is stored.
  Every formed self-contained term has a complete artifact presentation, and
  every presentation of every complete quoted artifact remains available.

  Composition with an independent class recovers its subject through that
  actual body. A later report may present the same subject differently; the
  stored artifact continues to quote its own exact term. This class is a
  further use of the existing complete quotation relation and does not select
  an exclusive topology for presentations of its subjects.
\<close>

end
