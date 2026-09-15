theory RRA_Finite_Graft_Readiness
  imports RRA_Graft_Readiness RRA_Finite_Embedded_Grafts
begin

definition finite_shared_graft_artifact ::
  "local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>
    local_address option finite_artifact_environment\<Rightarrow>bool" where
  "finite_shared_graft_artifact E u F=fBex (finite_environment_artifacts E)
    (\<lambda>(v,R). v=u \<and> (None,R) |\<in>| finite_environment_artifacts F)"

lemma finite_shared_graft_artifact_exact:
  "finite_shared_graft_artifact E u F \<longleftrightarrow>
    (\<exists>R. artifact_at (decode_finite_environment E) u R \<and> artifact_at (decode_finite_environment F) None R)"
  by (auto simp: finite_shared_graft_artifact_def Bex_def split_paired_Ex)

definition finite_boundary_bindings_compatible where
  "finite_boundary_bindings_compatible h E u F=fBall (finite_environment_bindings F)
    (\<lambda>((v,k),w). v=None \<longrightarrow> fBall (finite_environment_bindings E)
      (\<lambda>((x,j),y). x=u \<and> j=k \<longrightarrow> y=h w))"

lemma finite_boundary_bindings_compatible_exact:
  "finite_boundary_bindings_compatible h E u F=
    boundary_bindings_compatible h (decode_finite_environment E) u (decode_finite_environment F)"
  by (auto simp: finite_boundary_bindings_compatible_def boundary_bindings_compatible_def
    binds_slot_def Ball_def split_paired_All)

definition finite_graft_prerequisites where
  "finite_graft_prerequisites h E u F \<longleftrightarrow> finite_environment_formed E \<and>
    finite_environment_formed F \<and> finite_shared_graft_artifact E u F \<and>
    finite_boundary_bindings_compatible h E u F"

theorem finite_graft_prerequisites_exact:
  "boundary_use_embedding (environment_uses (decode_finite_environment E)) u h \<Longrightarrow>
    finite_graft_prerequisites h E u F=original_graft_ready h
      (decode_finite_environment E) u (decode_finite_environment F)"
  by (simp add: finite_graft_prerequisites_def original_graft_ready_def
    finite_environment_formed_correct finite_shared_graft_artifact_exact finite_boundary_bindings_compatible_exact)

lemma finite_compact_boundary_embedding:
  "boundary_use_embedding (environment_uses (decode_finite_environment E)) u
    (finite_compact_use_map (finite_environment_uses E) u)"
  by (simp only: finite_compact_use_map_exact finite_environment_uses_correct[symmetric];
    rule compact_boundary_embedding; simp)

definition finite_compact_graft_ready where
  "finite_compact_graft_ready E u F=finite_graft_prerequisites
    (finite_compact_use_map (finite_environment_uses E) u) E u F"

theorem finite_compact_graft_ready_exact:
  "finite_compact_graft_ready E u F=original_graft_ready
    (finite_compact_use_map (finite_environment_uses E) u)
      (decode_finite_environment E) u (decode_finite_environment F)"
  by (simp only: finite_compact_graft_ready_def finite_graft_prerequisites_exact[OF finite_compact_boundary_embedding])

export_code finite_compact_graft_ready checking SML

end
