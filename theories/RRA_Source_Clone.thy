theory RRA_Source_Clone
  imports RRA_Fresh_Uses RRA_Read_Transport
begin

section \<open>A fresh reading use for one embedded source artifact\<close>

definition clone_source_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> exact_artifact \<Rightarrow>
    (local_address \<Rightarrow> local_address) \<Rightarrow> 'u \<Rightarrow> 'u artifact_environment" where
  "clone_source_environment E u R f z =
    \<lparr>environment_artifacts = insert (z,R) (environment_artifacts E),
     environment_bindings = environment_bindings E \<union>
       {((z,k),v) |k v. k \<in> rra_carrier (object_structure R) \<and> binds_slot E u (f k) v}\<rparr>"

lemma clone_artifact_iff:
  "artifact_at (clone_source_environment E u R f z) v S \<longleftrightarrow>
    (v=z \<and> S=R) \<or> artifact_at E v S"
  by (auto simp: clone_source_environment_def artifact_at_def)

lemma clone_binding_iff:
  "binds_slot (clone_source_environment E u R f z) v k w \<longleftrightarrow>
    binds_slot E v k w \<or> (v=z \<and> k \<in> rra_carrier (object_structure R) \<and> binds_slot E u (f k) w)"
  by (auto simp: clone_source_environment_def binds_slot_def)

lemma clone_source_artifact:
  assumes fresh: "z \<notin> environment_uses E"
  shows "artifact_at (clone_source_environment E u R f z) z S \<longleftrightarrow> S=R"
  using fresh by (auto simp: clone_source_environment_def environment_uses_def rel_dom_def artifact_at_def)

lemma fresh_use_no_bindings:
  assumes ef: "environment_formed E" and fresh: "z \<notin> environment_uses E"
  shows "\<not> binds_slot E z k v"
proof
  assume binding: "binds_slot E z k v"
  obtain S where source: "artifact_at E z S"
    using ef binding unfolding environment_formed_def by blast
  have member: "z \<in> environment_uses E"
    using source by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  show False using fresh member by blast
qed

lemma clone_source_binding:
  assumes ef: "environment_formed E" and fresh: "z \<notin> environment_uses E"
  shows "binds_slot (clone_source_environment E u R f z) z k v \<longleftrightarrow>
    k \<in> rra_carrier (object_structure R) \<and> binds_slot E u (f k) v"
  using fresh_use_no_bindings[OF ef fresh] by (simp add: clone_binding_iff)

lemma clone_source_targets_are_old:
  assumes ef: "environment_formed E" and fresh: "z \<notin> environment_uses E"
    and binding: "binds_slot (clone_source_environment E u R f z) z k v"
  shows "v \<in> environment_uses E"
proof -
  have old: "binds_slot E u (f k) v" using binding clone_source_binding[OF ef fresh] by blast
  show ?thesis using ef old unfolding environment_formed_def by blast
qed

lemma clone_old_artifact:
  assumes "v \<noteq> z"
  shows "artifact_at (clone_source_environment E u R f z) v S \<longleftrightarrow> artifact_at E v S"
  using assms by (simp add: clone_artifact_iff)

lemma clone_old_binding:
  assumes "v \<noteq> z"
  shows "binds_slot (clone_source_environment E u R f z) v k w \<longleftrightarrow> binds_slot E v k w"
  using assms by (simp add: clone_binding_iff)

lemma clone_environment_includes:
  "environment_included E (clone_source_environment E u R f z)"
  by (auto simp: environment_included_def clone_source_environment_def)

lemma clone_environment_uses:
  "environment_uses (clone_source_environment E u R f z) = insert z (environment_uses E)"
  by (auto simp: environment_uses_def rel_dom_def clone_source_environment_def)

lemma clone_environment_formed:
  assumes ef: "environment_formed E" and rf: "exact_formed R" and fresh: "z \<notin> environment_uses E"
  shows "environment_formed (clone_source_environment E u R f z)"
proof -
  let ?U = "rra_carrier (object_structure R)"
  let ?B = "{((z,k),v) |k v. k \<in> ?U \<and> binds_slot E u (f k) v}"
  have fu: "finite ?U" using rf by (simp add: exact_formed_def object_formed_def rra_formed_def)
  have fv: "finite (environment_uses E)" by (rule environment_uses_finite[OF ef])
  have target_old: "\<And>k v. binds_slot E u (f k) v \<Longrightarrow> v \<in> environment_uses E"
    using ef unfolding environment_formed_def by blast
  have bounded: "?B \<subseteq> ({z} \<times> ?U) \<times> environment_uses E" using target_old by auto
  have fb: "finite ?B" by (rule finite_subset[OF bounded]) (use fu fv in simp)
  have old_artifacts: "finite (environment_artifacts E)" "single_valued (environment_artifacts E)"
    and old_bindings: "finite (environment_bindings E)" "single_valued (environment_bindings E)"
    using ef by (auto simp: environment_formed_def)
  have new_artifacts: "single_valued (insert (z,R) (environment_artifacts E))"
    using old_artifacts(2) fresh by (auto simp: single_valued_def environment_uses_def rel_dom_def)
  have new_bindings: "single_valued ?B"
    using old_bindings(2) by (auto simp: single_valued_def binds_slot_def)
  have compatible: "\<forall>x v w. (x,v) \<in> environment_bindings E \<longrightarrow> (x,w) \<in> ?B \<longrightarrow> v=w"
    using fresh_use_no_bindings[OF ef fresh] by (auto simp: binds_slot_def)
  have all_bindings: "single_valued (environment_bindings E \<union> ?B)"
    using single_valued_union_iff[OF old_bindings(2) new_bindings] compatible by blast
  have artifacts: "\<forall>v S. artifact_at (clone_source_environment E u R f z) v S \<longrightarrow> exact_formed S"
    using ef rf by (auto simp: clone_artifact_iff environment_formed_def)
  have binding_bounds: "\<forall>v k w. binds_slot (clone_source_environment E u R f z) v k w \<longrightarrow>
    (\<exists>S. artifact_at (clone_source_environment E u R f z) v S \<and> k \<in> rra_carrier (object_structure S)) \<and>
    w \<in> environment_uses (clone_source_environment E u R f z)"
    using ef target_old
    by (auto simp: clone_binding_iff clone_artifact_iff clone_environment_uses environment_formed_def; blast)
  show ?thesis using old_artifacts(1) old_bindings(1) new_artifacts fb all_bindings artifacts binding_bounds
    by (simp add: environment_formed_def clone_source_environment_def)
qed

lemma clone_source_literal_values:
  assumes ef: "environment_formed E" and fresh: "z \<notin> environment_uses E"
    and member: "k \<in> rra_carrier (object_structure R)"
  shows "external_slot_values (clone_source_environment E u R f z) z k = external_slot_values E u (f k)"
proof -
  have no_self: "\<And>v. binds_slot E u (f k) v \<Longrightarrow> v \<noteq> z"
    using ef fresh unfolding environment_formed_def by blast
  show ?thesis using no_self member
    by (auto simp: external_slot_values_def clone_source_binding[OF ef fresh] clone_artifact_iff)
qed

definition clone_source_use ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address option" where
  "clone_source_use E u = fresh_use_map (environment_uses E) u (Some [])"

lemma clone_source_use_fresh:
  assumes "environment_formed E"
  shows "clone_source_use E u \<notin> environment_uses E"
  using fresh_use_map_outside[OF environment_uses_finite[OF assms], of u "[]"]
  by (simp add: clone_source_use_def)

lemma fresh_clone_environment_formed:
  assumes "environment_formed E" "exact_formed R"
  shows "environment_formed (clone_source_environment E u R f (clone_source_use E u))"
  by (rule clone_environment_formed[OF assms clone_source_use_fresh[OF assms(1)]])

text \<open>
  A fresh reading use receives exactly the source artifact and the bindings
  obtained by pulling back existing destination slots along the proposed copy.
  Every target use and artifact remains the existing one. The auxiliary use is
  finite and formed, and changes no old artifact or binding. This construction
  lets a child reader be checked against the complete destination environment
  before its syntax is embedded there, including self calls in the destination.
\<close>

end
