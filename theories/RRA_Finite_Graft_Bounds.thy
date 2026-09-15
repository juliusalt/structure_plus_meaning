theory RRA_Finite_Graft_Bounds
  imports RRA_Lookup_Graft_Readiness RRA_Encoded_Bounded_States
begin

definition finite_environment_head_bound :: "nat\<Rightarrow>local_address option finite_artifact_environment\<Rightarrow>bool" where
  "finite_environment_head_bound n E=fBall (finite_environment_artifacts E) (\<lambda>(u,R). use_word_head u<n)"

lemma finite_environment_head_bound_uses:
  "finite_environment_head_bound n E \<longleftrightarrow> (\<forall>u\<in>fset (finite_environment_uses E). use_word_head u<n)"
  by (auto simp: finite_environment_head_bound_def finite_environment_uses_def fimage.rep_eq Ball_def)

lemma shared_graft_source_use:
  "finite_shared_graft_artifact E u F \<Longrightarrow> u |\<in>| finite_environment_uses E"
  by (auto simp: finite_shared_graft_artifact_def finite_environment_uses_def fimage.rep_eq Bex_def intro: rev_image_eqI)

lemma shared_graft_source_bound:
  "finite_environment_head_bound n E \<Longrightarrow> finite_shared_graft_artifact E u F \<Longrightarrow> use_word_head u<n"
  using shared_graft_source_use by (auto simp: finite_environment_head_bound_uses)

theorem bounded_graft_prefix_embedding:
  assumes bound: "finite_environment_head_bound n E" and shared: "finite_shared_graft_artifact E u F"
  shows "boundary_use_embedding (environment_uses (decode_finite_environment E)) u (prefix_use_map [n] u)"
proof -
  have all: "\<forall>v\<in>insert u (fset (finite_environment_uses E)). use_word_head v<n"
    using bound shared_graft_source_bound[OF bound shared] by (auto simp: finite_environment_head_bound_uses)
  show ?thesis by (simp only: finite_environment_uses_correct[symmetric];
    rule prefix_boundary_embedding; rule use_head_bound_prefix_avoids[OF all])
qed

theorem finite_graft_head_bound:
  assumes bound: "finite_environment_head_bound n E" and source: "use_word_head u<n"
  shows "finite_environment_head_bound (Suc n) (finite_embedded_graft (prefix_use_map [n] u) E F)"
proof -
  have mapped: "use_word_head (prefix_use_map [n] u x)<Suc n" for x
    using source by (cases x) auto
  show ?thesis using bound mapped
    by (auto simp: finite_environment_head_bound_def finite_embedded_graft_def finite_merge_environment_def
      finite_rename_environment_def fimage.rep_eq Ball_def)
qed

lemma encoded_environment_head_bound:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    finite_environment_head_bound n E \<longleftrightarrow>
      (\<forall>u R. R |\<in>| encoded_environment_artifacts use_code I u \<longrightarrow> use_word_head u<n)"
  by (auto simp: finite_environment_head_bound_def encoded_environment_represents_def
    environment_lookup_represents_def Ball_def split_paired_All)

lemma encoded_bounded_subject:
  assumes valid: "encoded_bounded_valid use_code slot_code q"
  shows "\<exists>E. finite_environment_formed E \<and> encoded_environment_represents use_code slot_code (snd q) E \<and>
      finite_environment_head_bound (fst q) E"
proof -
  obtain E where formed: "finite_environment_formed E"
    and represented: "encoded_environment_represents use_code slot_code (snd q) E"
    using valid by (auto simp: encoded_bounded_valid_def)
  have bound: "finite_environment_head_bound (fst q) E"
    using valid by (simp add: encoded_environment_head_bound[OF represented] encoded_bounded_valid_def)
  show ?thesis using formed represented bound by blast
qed

text \<open>
  Any actual strict head bound supplies the fresh one-coordinate prefix once
  the old shared source exists. The bound need not be minimal. Whole grafting
  preserves every old use and gives every present imported use the current
  head, so its successor bounds the complete resulting environment.
\<close>

end
