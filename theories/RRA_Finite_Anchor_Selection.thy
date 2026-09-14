theory RRA_Finite_Anchor_Selection
  imports RRA_Executable_Citations RRA_Finite_Environment_Positions Finite_Singleton_Selection Keyed_Option_Maps
begin

definition finite_anchor_artifact where
  "finite_anchor_artifact E d=finite_singleton_option
    (ffilter (\<lambda>R. snd d |\<in>| finite_carrier (finite_structure R)) (finite_artifacts_at E (fst d)))"

lemma finite_anchor_artifact_member:
  assumes formed: "finite_environment_formed E"
  shows "finite_anchor_artifact E d=Some R \<longleftrightarrow>
    (fst d,R) |\<in>| finite_environment_artifacts E \<and> snd d |\<in>| finite_carrier (finite_structure R)"
proof -
  let ?T="ffilter (\<lambda>R. snd d |\<in>| finite_carrier (finite_structure R)) (finite_artifacts_at E (fst d))"
  have unique: "x=y" if "x |\<in>| ?T" "y |\<in>| ?T" for x y
    using formed that
    by (auto simp: finite_environment_formed_def finite_relation_functional_correct
      single_valued_def finite_artifacts_at_member)
  have selected: "finite_singleton_option ?T=Some R \<longleftrightarrow> R |\<in>| ?T"
    by (rule finite_singleton_option_member[OF unique])
  show ?thesis using selected
    by (auto simp only: finite_anchor_artifact_def ffmember_filter finite_artifacts_at_member)
qed

theorem finite_anchor_artifact_domain:
  assumes formed: "finite_environment_formed E"
  shows "(\<exists>R. finite_anchor_artifact E d=Some R) \<longleftrightarrow>
    d |\<in>| finite_environment_positions E"
  by (simp only: finite_anchor_artifact_member[OF formed] finite_environment_positions_member)

theorem finite_anchor_artifact_properties:
  assumes formed: "finite_environment_formed E" and selected: "finite_anchor_artifact E d=Some R"
  shows "artifact_at (decode_finite_environment E) (fst d) (decode_finite_object R)"
    "anchor_formed (decode_finite_object R,snd d)"
proof -
  have row: "(fst d,R) |\<in>| finite_environment_artifacts E"
    and inside: "snd d |\<in>| finite_carrier (finite_structure R)"
    using selected by (simp only: finite_anchor_artifact_member[OF formed]; blast)+
  show source: "artifact_at (decode_finite_environment E) (fst d) (decode_finite_object R)"
    using row by simp
  have environment: "environment_formed (decode_finite_environment E)"
    using formed by (simp only: finite_environment_formed_correct)
  have exact: "exact_formed (decode_finite_object R)"
    using environment source by (simp only: environment_formed_def; blast)
  show "anchor_formed (decode_finite_object R,snd d)"
    using exact inside by (simp add: anchor_formed_def)
qed

export_code finite_anchor_artifact checking SML

end
