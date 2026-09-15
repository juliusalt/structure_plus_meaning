theory RRA_Lookup_Graft_Readiness
  imports RRA_Finite_Graft_Readiness RRA_Environment_Lookup_Contracts
begin

definition lookup_shared_graft_artifact where
  "lookup_shared_graft_artifact artifacts u F=fBex (finite_environment_artifacts F)
    (\<lambda>(v,R). v=None \<and> R |\<in>| artifacts u)"

definition lookup_boundary_bindings_compatible where
  "lookup_boundary_bindings_compatible bindings h u F=fBall (finite_environment_bindings F)
    (\<lambda>((v,k),w). v=None \<longrightarrow> fBall (bindings u k) (\<lambda>x. x=h w))"

lemma lookup_shared_graft_artifact_exact:
  "environment_lookup_represents artifacts bindings E \<Longrightarrow>
    lookup_shared_graft_artifact artifacts u F=finite_shared_graft_artifact E u F"
  by (auto simp: environment_lookup_represents_def lookup_shared_graft_artifact_def
    finite_shared_graft_artifact_def Bex_def split_paired_Ex)

lemma lookup_boundary_bindings_compatible_exact:
  "environment_lookup_represents artifacts bindings E \<Longrightarrow>
    lookup_boundary_bindings_compatible bindings h u F=finite_boundary_bindings_compatible h E u F"
  by (auto simp: environment_lookup_represents_def lookup_boundary_bindings_compatible_def
    finite_boundary_bindings_compatible_def Ball_def split_paired_All)

definition lookup_graft_ready where
  "lookup_graft_ready artifacts bindings h u F \<longleftrightarrow> finite_environment_formed F \<and>
    lookup_shared_graft_artifact artifacts u F \<and> lookup_boundary_bindings_compatible bindings h u F"

theorem lookup_graft_ready_finite:
  "environment_lookup_represents artifacts bindings E \<Longrightarrow> finite_environment_formed E \<Longrightarrow>
    lookup_graft_ready artifacts bindings h u F=finite_graft_prerequisites h E u F"
  by (simp add: lookup_graft_ready_def finite_graft_prerequisites_def
    lookup_shared_graft_artifact_exact lookup_boundary_bindings_compatible_exact)

theorem lookup_graft_ready_original:
  assumes represented: "environment_lookup_represents artifacts bindings E"
    and formed: "finite_environment_formed E"
    and embedding: "finite_shared_graft_artifact E u F \<Longrightarrow>
      boundary_use_embedding (environment_uses (decode_finite_environment E)) u h"
  shows "lookup_graft_ready artifacts bindings h u F=original_graft_ready h
    (decode_finite_environment E) u (decode_finite_environment F)"
  using embedding
  by (auto simp: lookup_graft_ready_finite[OF represented formed] finite_graft_prerequisites_def
    original_graft_ready_def finite_environment_formed_correct finite_shared_graft_artifact_exact
    finite_boundary_bindings_compatible_exact)

text \<open>
  Shared-artifact and binding compatibility checks query only the actual old
  boundary and traverse the imported rows. A compatible existing binding is
  admitted. The original environment is supplied by its complete lookup
  contract; no whole old view is computed by these checks.
\<close>

end
