theory Finite_Observation_Repairs
  imports Observation_Repairs Finite_Investigation
begin

section \<open>Finite repair reports specialize the same comparison account\<close>

definition finite_sound_observation_facets where
  "finite_sound_observation_facets C relation U table=ffilter (\<lambda>f.
    fBall C (\<lambda>c. fBall C (\<lambda>d. relation c d \<longrightarrow>
      fset (finite_candidate_profile {|f|} table c)\<subseteq>
      fset (finite_candidate_profile {|f|} table d)))) U"

lemma finite_sound_observation_facets_exact:
  "fset (finite_sound_observation_facets C relation U table)=
    sound_observation_facets (fset C) relation (fset U) (finite_table_observations table)"
  by (auto simp: finite_sound_observation_facets_def finite_candidate_profile_exact
    candidate_profile_comparison; blast)

definition finite_observation_conflicts where
  "finite_observation_conflicts C relation F table=ffUnion (fimage (\<lambda>c.
    ffUnion (fimage (\<lambda>d. if relation c d then
      fimage (\<lambda>(f,w). (c,d,f,w)) (finite_candidate_losses F table c d) else {||}) C)) C)"

lemma finite_observation_conflicts_exact:
  "fset (finite_observation_conflicts C relation F table)=
    observation_conflicts (fset C) relation (fset F) (finite_table_observations table)"
  by (auto simp: finite_observation_conflicts_def ffUnion.rep_eq fimage.rep_eq
    finite_candidate_losses_exact observation_conflicts_def image_iff case_prod_beta'
    split: prod.splits if_splits; force)

lemma finite_basis_residual_member:
  "(c,d)\<in>fset (finite_basis_residual C F table relation) \<longleftrightarrow>
    c\<in>fset C \<and> d\<in>fset C \<and>
    (relation c d \<noteq> (candidate_profile (fset F) (finite_table_observations table) c\<subseteq>
      candidate_profile (fset F) (finite_table_observations table) d))"
  by (auto simp: finite_basis_residual_def ffUnion.rep_eq fimage.rep_eq
    finite_candidate_profile_exact image_iff)

definition finite_available_observation_repairs where
  "finite_available_observation_repairs C relation U F table=
    (let A=ffilter (\<lambda>f. f\<notin>fset F) (finite_sound_observation_facets C relation U table)
     in ffUnion (fimage (\<lambda>(c,d). if relation c d then {||} else
       fimage (\<lambda>(f,w). (c,d,f,w)) (finite_candidate_losses A table c d))
       (finite_basis_residual C F table relation)))"

lemma finite_available_observation_repairs_exact:
  "fset (finite_available_observation_repairs C relation U F table)=
    available_observation_repairs (fset C) relation (fset U) (fset F) (finite_table_observations table)"
proof -
  let ?A="ffilter (\<lambda>f. f\<notin>fset F) (finite_sound_observation_facets C relation U table)"
  let ?O="finite_table_observations table"
  have selected: "fset ?A=sound_observation_facets (fset C) relation (fset U) ?O-fset F"
    by (auto simp del: sound_observation_facets_member
      simp add: ffilter.rep_eq finite_sound_observation_facets_exact)
  have union_member: "x\<in>fset (ffUnion (fimage g T)) \<longleftrightarrow>
      (\<exists>t\<in>fset T. x\<in>fset (g t))" for x g T
    by (auto simp: ffUnion.rep_eq fimage.rep_eq)
  have row: "(c,d,f,w)\<in>fset (if relation a b then {||} else
      fimage (\<lambda>(g,v). (a,b,g,v)) (finite_candidate_losses ?A table a b)) \<longleftrightarrow>
      \<not>relation a b \<and> c=a \<and> d=b \<and> (f,w)\<in>candidate_losses (fset ?A) ?O a b"
    for c d f w a b
    by (auto simp: fimage.rep_eq finite_candidate_losses_exact image_iff case_prod_beta'
      split: prod.splits if_splits)
  have member: "(c,d,f,w)\<in>fset (finite_available_observation_repairs C relation U F table) \<longleftrightarrow>
      (c,d)\<in>fset (finite_basis_residual C F table relation) \<and> \<not>relation c d \<and>
      (f,w)\<in>candidate_losses (fset ?A) ?O c d" for c d f w
    by (simp only: finite_available_observation_repairs_def Let_def union_member;
      auto simp only: row split: prod.splits)
  have missing: "(c,d)\<in>fset (finite_basis_residual C F table relation) \<and> \<not>relation c d \<longleftrightarrow>
      (c,d)\<in>comparison_failures (fset C) relation (fset F) ?O" for c d
    by (auto simp only: finite_basis_residual_member comparison_failures_def mem_Collect_eq split_conv)
  have represented: "(c,d,f,w)\<in>fset (finite_available_observation_repairs C relation U F table) \<longleftrightarrow>
      (c,d)\<in>comparison_failures (fset C) relation (fset F) ?O \<and>
      (f,w)\<in>candidate_losses (sound_observation_facets (fset C) relation (fset U) ?O-fset F) ?O c d"
    for c d f w
    using missing[of c d] by (simp only: member selected) blast
  show ?thesis
    by (auto simp only: available_observation_repairs_def mem_Collect_eq split_conv represented)
qed

definition finite_unrepairable_comparisons where
  "finite_unrepairable_comparisons C relation U table=
    finite_basis_residual C (finite_sound_observation_facets C relation U table) table relation"

lemma finite_unrepairable_comparisons_exact:
  "fset (finite_unrepairable_comparisons C relation U table)=
    comparison_failures (fset C) relation
      (sound_observation_facets (fset C) relation (fset U) (finite_table_observations table))
      (finite_table_observations table)"
proof -
  have sound: "comparison_observations_sound (fset C) relation
      (sound_observation_facets (fset C) relation (fset U) (finite_table_observations table))
      (finite_table_observations table)" by (rule sound_observation_facets_sound)
  show ?thesis
    using sound by (auto simp: finite_unrepairable_comparisons_def finite_basis_residual_def
      ffUnion.rep_eq fimage.rep_eq finite_candidate_profile_exact finite_sound_observation_facets_exact
      comparison_failures_def comparison_observations_sound_def split: prod.splits; blast)
qed

export_code finite_sound_observation_facets finite_observation_conflicts
  finite_available_observation_repairs finite_unrepairable_comparisons checking SML

end
