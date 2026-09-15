theory RRA_General_Environment_Grafts
  imports RRA_Boundary_Use_Embeddings
begin

definition embedded_graft_environment where
  "embedded_graft_environment h E F=merge_environment E (rename_environment h F)"

definition boundary_bindings_compatible where
  "boundary_bindings_compatible h E u F \<longleftrightarrow>
    (\<forall>k v w. binds_slot F None k v \<longrightarrow> binds_slot E u k w \<longrightarrow> w=h v)"

locale environment_graft =
  fixes E F :: "local_address option artifact_environment" and u :: "local_address option"
    and R :: exact_artifact and h :: "local_address option\<Rightarrow>local_address option"
  assumes old_formed: "environment_formed E" and imported_formed: "environment_formed F"
    and old_source: "artifact_at E u R" and imported_source: "artifact_at F None R"
    and embedding: "boundary_use_embedding (environment_uses E) u h"
begin

lemma map_injective: "inj h" using embedding by (simp add: boundary_use_embedding_def)
lemma map_boundary [simp]: "h None=u" using embedding by (simp add: boundary_use_embedding_def)
lemma map_outside: "h (Some word)\<notin>insert u (environment_uses E)"
  using embedding by (simp add: boundary_use_embedding_def)

lemma imported_at_existing:
  assumes member: "v\<in>environment_uses E" and at: "artifact_at (rename_environment h F) v S"
  shows "v=u \<and> S=R"
proof -
  obtain x where mapped: "h x=v" and source: "artifact_at F x S"
    using at by (auto simp: artifact_at_renaming)
  have origin: "x=None \<and> v=u" by (rule boundary_embedding_origin[OF embedding member mapped])
  have same: "S=R" by (rule environment_artifact_unique[OF imported_formed _ imported_source])
    (use source origin in simp)
  show ?thesis using origin same by blast
qed

lemma renamed_boundary_binding:
  "binds_slot (rename_environment h F) u k (h v) \<longleftrightarrow> binds_slot F None k v"
  using binds_slot_renamed_use[OF map_injective, of F None k v] by simp

lemma imported_binding_at_existing:
  assumes member: "v\<in>environment_uses E"
  shows "binds_slot (rename_environment h F) v k w \<longleftrightarrow>
    v=u \<and> (\<exists>y. binds_slot F None k y \<and> w=h y)"
proof
  assume at: "binds_slot (rename_environment h F) v k w"
  obtain x y where mapped: "h x=v" and target: "w=h y" and source: "binds_slot F x k y"
    using at by (auto simp: binds_slot_renaming)
  have origin: "x=None \<and> v=u" by (rule boundary_embedding_origin[OF embedding member mapped])
  show "v=u \<and> (\<exists>y. binds_slot F None k y \<and> w=h y)" using source origin target by blast
next
  assume "v=u \<and> (\<exists>y. binds_slot F None k y \<and> w=h y)"
  then obtain y where source: "binds_slot F None k y" and shape: "v=u" "w=h y" by blast
  show "binds_slot (rename_environment h F) v k w"
    using source by (simp only: shape renamed_boundary_binding)
qed

lemma original_binding_source:
  "binds_slot E v k w \<Longrightarrow> v\<in>environment_uses E"
  using old_formed by (auto simp: environment_formed_def environment_uses_def artifact_at_def rel_dom_def; blast)

lemma artifacts_compatible:
  "artifact_at E v S \<Longrightarrow> artifact_at (rename_environment h F) v T \<Longrightarrow> S=T"
proof -
  assume old: "artifact_at E v S" and imported: "artifact_at (rename_environment h F) v T"
  have member: "v\<in>environment_uses E" using old by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have origin: "v=u \<and> T=R" by (rule imported_at_existing[OF member imported])
  have same: "S=R" by (rule environment_artifact_unique[OF old_formed _ old_source]) (use old origin in simp)
  show ?thesis using same origin by blast
qed

theorem compatibility_exact:
  "environments_compatible E (rename_environment h F) \<longleftrightarrow> boundary_bindings_compatible h E u F"
proof
  assume compatible: "environments_compatible E (rename_environment h F)"
  show "boundary_bindings_compatible h E u F"
  proof (unfold boundary_bindings_compatible_def, intro allI impI)
    fix k v w
    assume imported: "binds_slot F None k v" and old: "binds_slot E u k w"
    have renamed: "binds_slot (rename_environment h F) u k (h v)"
      using imported by (simp only: renamed_boundary_binding)
    show "w=h v" using compatible old renamed by (auto simp: environments_compatible_def)
  qed
next
  assume boundary: "boundary_bindings_compatible h E u F"
  have bindings: "binds_slot E v k x \<Longrightarrow> binds_slot (rename_environment h F) v k y \<Longrightarrow> x=y" for v k x y
  proof -
    assume old: "binds_slot E v k x" and imported: "binds_slot (rename_environment h F) v k y"
    have member: "v\<in>environment_uses E" by (rule original_binding_source[OF old])
    have origin: "v=u \<and> (\<exists>z. binds_slot F None k z \<and> y=h z)"
      using imported_binding_at_existing[OF member, of k y] imported by blast
    show "x=y" using boundary old origin by (auto simp: boundary_bindings_compatible_def)
  qed
  show "environments_compatible E (rename_environment h F)"
    using artifacts_compatible bindings by (auto simp: environments_compatible_def)
qed

theorem formed_exact:
  "environment_formed (embedded_graft_environment h E F) \<longleftrightarrow> boundary_bindings_compatible h E u F"
  using environment_merge_formed_iff[OF old_formed environment_renaming_formed[OF imported_formed map_injective]]
  by (simp only: embedded_graft_environment_def compatibility_exact)

lemma includes_original: "environment_included E (embedded_graft_environment h E F)"
  unfolding embedded_graft_environment_def by (rule environment_included_merge_left)

lemma includes_imported: "environment_included (rename_environment h F) (embedded_graft_environment h E F)"
  unfolding embedded_graft_environment_def by (rule environment_included_merge_right)

theorem original_artifacts_unchanged:
  "v\<in>environment_uses E \<Longrightarrow>
    artifact_at (embedded_graft_environment h E F) v S \<longleftrightarrow> artifact_at E v S"
  using imported_at_existing old_source by (auto simp: embedded_graft_environment_def)

theorem imported_artifacts_exact:
  "artifact_at (embedded_graft_environment h E F) (h (Some word)) S \<longleftrightarrow> artifact_at F (Some word) S"
proof -
  have absent: "\<not>artifact_at E (h (Some word)) S"
    using map_outside[of word] by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  show ?thesis using absent artifact_at_renamed_use[OF map_injective, of F "Some word" S]
    by (simp add: embedded_graft_environment_def)
qed

theorem passive_original_bindings_unchanged:
  "(\<And>k v. \<not>binds_slot F None k v) \<Longrightarrow> v\<in>environment_uses E \<Longrightarrow>
    binds_slot (embedded_graft_environment h E F) v k w \<longleftrightarrow> binds_slot E v k w"
  using imported_binding_at_existing by (auto simp: embedded_graft_environment_def)

lemma passive_boundary_compatible:
  "(\<And>k v. \<not>binds_slot F None k v) \<Longrightarrow> boundary_bindings_compatible h E u F"
  by (simp add: boundary_bindings_compatible_def)

lemma unbound_boundary_compatible:
  "(\<And>k v w. binds_slot F None k v \<Longrightarrow> \<not>binds_slot E u k w) \<Longrightarrow>
    boundary_bindings_compatible h E u F"
  by (auto simp: boundary_bindings_compatible_def)

end

text \<open>
  One general composition contract preserves every original and renamed row.
  Its remaining formation condition is exactly compatibility of bindings at
  the shared source. Passive imported boundaries and unbound literal slots
  instantiate that condition. Neither case requires reconstructing the artifact
  uniqueness, occurrence-origin or merge-formation argument.
\<close>

end
