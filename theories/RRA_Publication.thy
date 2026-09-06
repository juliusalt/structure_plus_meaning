theory RRA_Publication
  imports RRA_Selection
begin

section \<open>Publication fields and their exact structural site\<close>

record publication_view =
  publication_snapshot :: selection_snapshot
  publication_dependencies :: "exact_target fset"
  publication_evidence :: "exact_target fset"

definition publication_formed :: "publication_view \<Rightarrow> bool" where
  "publication_formed P \<longleftrightarrow>
    snapshot_formed (publication_snapshot P) \<and>
    (\<forall>t\<in>fset (publication_dependencies P). target_formed t) \<and>
    (\<forall>t\<in>fset (publication_evidence P). target_formed t)"

definition publication_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   publication_view \<Rightarrow> bool" where
  "publication_at E u root P \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R ps sr dr er. artifact_at E u R \<and> record_at R root ps [sr,dr,er] \<and>
      snapshot_at E u sr (publication_snapshot P) \<and>
      target_selection_at E u dr (fset (publication_dependencies P)) \<and>
      target_selection_at E u er (fset (publication_evidence P)))"

definition published ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> bool" where
  "published E u root G \<longleftrightarrow>
    (\<exists>P. publication_at E u root P \<and> G \<in> fset (publication_snapshot P))"

lemma publication_view_identity:
  fixes P Q :: publication_view
  shows "P = Q \<longleftrightarrow>
    publication_snapshot P = publication_snapshot Q \<and>
    publication_dependencies P = publication_dependencies Q \<and>
    publication_evidence P = publication_evidence Q"
  by (cases P; cases Q) auto

lemma publication_at_unique:
  assumes first: "publication_at E u root P" and second: "publication_at E u root Q"
  shows "P = Q"
proof -
  obtain R ps sr dr er where a: "environment_formed E" "artifact_at E u R"
    "record_at R root ps [sr,dr,er]" "snapshot_at E u sr (publication_snapshot P)"
    "target_selection_at E u dr (fset (publication_dependencies P))"
    "target_selection_at E u er (fset (publication_evidence P))"
    using first unfolding publication_at_def by blast
  obtain S qs sr' dr' er' where b: "artifact_at E u S"
    "record_at S root qs [sr',dr',er']" "snapshot_at E u sr' (publication_snapshot Q)"
    "target_selection_at E u dr' (fset (publication_dependencies Q))"
    "target_selection_at E u er' (fset (publication_evidence Q))"
    using second unfolding publication_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have endpoints: "sr = sr' \<and> dr = dr' \<and> er = er'"
    using record_at_unique[OF a(3)] b(2) same by auto
  have selected: "publication_snapshot P = publication_snapshot Q"
    using snapshot_at_unique[OF a(4)] b(3) endpoints by blast
  have dependencies: "fset (publication_dependencies P) = fset (publication_dependencies Q)"
    using target_selection_unique[OF a(5)] b(4) endpoints by blast
  have evidence: "fset (publication_evidence P) = fset (publication_evidence Q)"
    using target_selection_unique[OF a(6)] b(5) endpoints by blast
  show ?thesis using selected dependencies evidence
    by (simp add: publication_view_identity fset_inject)
qed

lemma publication_at_formed:
  assumes "publication_at E u root P"
  shows "publication_formed P"
  using assms unfolding publication_at_def publication_formed_def snapshot_at_def
  by (meson target_selection_formed)

lemma published_core_formed:
  assumes "published E u root G"
  shows "generation_formed G"
proof -
  obtain P where pub: "publication_at E u root P" and selected: "G \<in> fset (publication_snapshot P)"
    using assms unfolding published_def by blast
  have formed: "selection_formed (publication_snapshot P)"
    using publication_at_formed[OF pub] by (simp add: publication_formed_def snapshot_formed_def)
  show ?thesis using formed selected by (auto simp: selection_formed_def)
qed

lemma publication_at_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "publication_at E u root P = publication_at F u root P"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  show ?thesis
    by (simp only: publication_at_def ef ff arts snapshot_at_locality[OF assms]
        target_selection_locality[OF assms])
qed

lemma evidence_selection_does_not_change_generations:
  assumes sf: "snapshot_formed S"
    and df: "\<forall>t\<in>fset D. target_formed t"
    and ef: "\<forall>t\<in>fset X. target_formed t"
    and ff: "\<forall>t\<in>fset Y. target_formed t"
  defines "P \<equiv> \<lparr>publication_snapshot=S, publication_dependencies=D, publication_evidence=X\<rparr>"
    and "Q \<equiv> \<lparr>publication_snapshot=S, publication_dependencies=D, publication_evidence=Y\<rparr>"
  shows "publication_formed P \<and> publication_formed Q"
    and "publication_snapshot P = publication_snapshot Q"
    and "\<forall>G. (G \<in> fset (publication_snapshot P)) = (G \<in> fset (publication_snapshot Q))"
  using assms by (simp_all add: publication_formed_def)

text \<open>
  The view is recovered at an exact artifact site under an explicit environment.
  Equality of recovered fields does not identify two presentation sites.
  Evidence selections identify exact material; publication formation does not
  validate that material as proof. Publication supplies no currentness or
  authority judgment. Its evidence fields can vary while every selected
  generation remains the same exact core.
\<close>

end
