theory RRA_Graft_Readiness
  imports RRA_General_Environment_Grafts
begin

definition original_graft_ready ::
  "(local_address option\<Rightarrow>local_address option)\<Rightarrow>
    local_address option artifact_environment\<Rightarrow>local_address option\<Rightarrow>
    local_address option artifact_environment\<Rightarrow>bool" where
  "original_graft_ready h E u F \<longleftrightarrow>
    environment_formed E \<and> environment_formed F \<and>
    (\<exists>R. artifact_at E u R \<and> artifact_at F None R) \<and>
    boundary_use_embedding (environment_uses E) u h \<and> boundary_bindings_compatible h E u F"

theorem original_ready_graft_formed:
  assumes ready: "original_graft_ready h E u F"
  shows "environment_formed (embedded_graft_environment h E F)"
proof -
  obtain R where old: "environment_formed E" and imported: "environment_formed F"
    and source: "artifact_at E u R" and boundary: "artifact_at F None R"
    and embedding: "boundary_use_embedding (environment_uses E) u h"
    and compatible: "boundary_bindings_compatible h E u F"
    using ready by (auto simp: original_graft_ready_def)
  interpret graft: environment_graft E F u R h
    by (unfold_locales) (rule old, rule imported, rule source, rule boundary, rule embedding)
  show ?thesis using compatible by (simp only: graft.formed_exact)
qed

theorem original_graft_ready_by_result:
  assumes embedding: "boundary_use_embedding (environment_uses E) u h"
  shows "original_graft_ready h E u F \<longleftrightarrow> environment_formed E \<and> environment_formed F \<and>
    (\<exists>R. artifact_at E u R \<and> artifact_at F None R) \<and>
    environment_formed (embedded_graft_environment h E F)"
proof
  assume ready: "original_graft_ready h E u F"
  show "environment_formed E \<and> environment_formed F \<and>
    (\<exists>R. artifact_at E u R \<and> artifact_at F None R) \<and> environment_formed (embedded_graft_environment h E F)"
    using ready original_ready_graft_formed[OF ready] by (auto simp: original_graft_ready_def)
next
  assume all: "environment_formed E \<and> environment_formed F \<and>
    (\<exists>R. artifact_at E u R \<and> artifact_at F None R) \<and> environment_formed (embedded_graft_environment h E F)"
  then obtain R where old: "environment_formed E" and imported: "environment_formed F"
    and source: "artifact_at E u R" and boundary: "artifact_at F None R"
    and formed: "environment_formed (embedded_graft_environment h E F)" by blast
  interpret graft: environment_graft E F u R h
    by (unfold_locales) (rule old, rule imported, rule source, rule boundary, rule embedding)
  have compatible: "boundary_bindings_compatible h E u F" using formed by (simp only: graft.formed_exact)
  show "original_graft_ready h E u F" using old imported source boundary embedding compatible
    by (auto simp: original_graft_ready_def)
qed

definition original_graft_result where
  "original_graft_result h E u F result=(case result of
    None \<Rightarrow> \<not>original_graft_ready h E u F
  | Some G \<Rightarrow> original_graft_ready h E u F \<and> G=embedded_graft_environment h E F)"

text \<open>
  Readiness retains original formation of both environments, their identical
  shared artifact, the complete boundary embedding and compatibility of every
  shared binding. Success preserves the whole merge; refusal is an explicit
  result. Formation is derived from these prerequisites, not asserted by a flag.
\<close>

end
