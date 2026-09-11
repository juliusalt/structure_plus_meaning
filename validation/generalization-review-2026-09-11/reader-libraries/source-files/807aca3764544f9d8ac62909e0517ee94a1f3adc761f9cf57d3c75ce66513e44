theory RRA_Literal_Extension
  imports RRA_Fresh_Uses RRA_Syntax_Construction RRA_Binding_Extension
begin

section \<open>Allocating fresh uses for a finite literal table\<close>

lemma renamed_literal_bindings:
  "binds_slot (rename_environment h (literal_environment R L)) v k w \<longleftrightarrow>
    v = h None \<and> k \<in> rel_dom L \<and> w = h (Some k)"
  by (auto simp: rename_environment_def literal_environment_def binds_slot_def image_image intro: rev_image_eqI)

locale literal_extension =
  fixes E :: "local_address option artifact_environment" and u :: "local_address option"
    and R :: exact_artifact and L :: "(local_address \<times> exact_artifact) set"
  assumes old_formed: "environment_formed E" and old_source: "artifact_at E u R"
    and table_finite: "finite L" and table_functional: "single_valued L"
    and target_formed: "\<forall>k T. (k,T) \<in> L \<longrightarrow> exact_formed T"
    and slots_inside: "rel_dom L \<subseteq> rra_carrier (object_structure R)"
    and slots_unbound: "\<And>k v. k \<in> rel_dom L \<Longrightarrow> \<not> binds_slot E u k v"
begin

abbreviation fresh_map where "fresh_map \<equiv> fresh_use_map (environment_uses E) u"
abbreviation imported where "imported \<equiv> rename_environment fresh_map (literal_environment R L)"
abbreviation installed where "installed \<equiv> graft_environment E u (literal_environment R L)"

lemma source_formed: "exact_formed R"
  using old_formed old_source unfolding environment_formed_def by blast

lemma literal_formed: "environment_formed (literal_environment R L)"
  by (rule literal_environment_formed[OF source_formed table_finite table_functional target_formed slots_inside])

lemma map_injective: "inj fresh_map"
  by (rule fresh_use_map_injective[OF environment_uses_finite[OF old_formed]])

lemma fresh_literal_use: "fresh_map (Some k) \<notin> environment_uses E"
  using fresh_use_map_outside[OF environment_uses_finite[OF old_formed], of u k] by blast

lemma imported_formed: "environment_formed imported"
  by (rule environment_renaming_formed[OF literal_formed map_injective])

lemma imported_binding:
  "binds_slot imported v k w \<longleftrightarrow> v=u \<and> k \<in> rel_dom L \<and> w=fresh_map (Some k)"
  by (simp add: renamed_literal_bindings)

lemma compatible: "environments_compatible E imported"
proof -
  have artifacts: "\<forall>v S T. artifact_at E v S \<longrightarrow> artifact_at imported v T \<longrightarrow> S=T"
  proof (intro allI impI)
    fix v S T assume old: "artifact_at E v S" and new: "artifact_at imported v T"
    have member: "v \<in> environment_uses E" using old by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
    have boundary: "artifact_at (literal_environment R L) None R" by simp
    have same: "v=u \<and> T=R" by (rule graft_imported_artifact[OF old_formed literal_formed boundary member new])
    have old_at_source: "artifact_at E u S" using old same by simp
    have old_value: "S=R" by (rule environment_artifact_unique[OF old_formed old_at_source old_source])
    show "S=T" using old_value same by blast
  qed
  have bindings: "\<forall>v k x y. binds_slot E v k x \<longrightarrow> binds_slot imported v k y \<longrightarrow> x=y"
  proof (intro allI impI)
    fix v k x y assume old: "binds_slot E v k x" and new: "binds_slot imported v k y"
    have parts: "v=u" "k \<in> rel_dom L" using new by (auto simp: imported_binding)
    have empty: "\<not> binds_slot E u k x" by (rule slots_unbound[OF parts(2)])
    show "x=y" using old parts(1) empty by blast
  qed
  show ?thesis using artifacts bindings by (simp add: environments_compatible_def)
qed

theorem formed: "environment_formed installed"
  using environment_merge_formed_iff[OF old_formed imported_formed] compatible
  by (simp add: graft_environment_def)

lemma included: "environment_included E installed"
  by (rule graft_includes_existing)

lemma source: "artifact_at installed u R"
  by (rule included_artifact[OF included old_source])

lemma old_artifacts:
  assumes "v \<in> environment_uses E"
  shows "artifact_at installed v T \<longleftrightarrow> artifact_at E v T"
  by (rule graft_existing_artifacts_unchanged[OF old_formed literal_formed old_source _ assms]) simp

lemma bindings:
  "binds_slot installed v k w \<longleftrightarrow>
    binds_slot E v k w \<or> (v=u \<and> k \<in> rel_dom L \<and> w=fresh_map (Some k))"
  by (simp add: graft_environment_def imported_binding)

lemma source_binding:
  assumes "k \<in> rel_dom L"
  shows "binds_slot installed u k v \<longleftrightarrow> v=fresh_map (Some k)"
  using slots_unbound[OF assms, of v] assms by (simp add: bindings)

lemma other_bindings:
  assumes "v \<noteq> u \<or> k \<notin> rel_dom L"
  shows "binds_slot installed v k w \<longleftrightarrow> binds_slot E v k w"
  using assms by (auto simp: bindings)

lemma literal_artifact:
  "artifact_at installed (fresh_map (Some k)) T \<longleftrightarrow> (k,T) \<in> L"
proof -
  have absent: "\<not> artifact_at E (fresh_map (Some k)) T"
    using fresh_literal_use[of k] by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have imported: "artifact_at imported (fresh_map (Some k)) T \<longleftrightarrow> (k,T) \<in> L"
    using artifact_at_renamed_use[OF map_injective, of "literal_environment R L" "Some k" T] by simp
  show ?thesis using absent imported by (simp add: graft_environment_def)
qed

lemma literal_values:
  assumes "k \<in> rel_dom L"
  shows "external_slot_values installed u k = {T. (k,T) \<in> L}"
  by (auto simp only: external_slot_values_def source_binding[OF assms] literal_artifact mem_Collect_eq)

lemma literal_singleton:
  assumes entry: "(k,T) \<in> L"
  shows "external_slot_values installed u k = {T}"
proof -
  have key: "k \<in> rel_dom L" by (rule rel_domI[OF entry])
  show ?thesis using literal_values[OF key] single_valued_fibre[OF table_functional entry] by simp
qed

lemma old_literal_values:
  assumes separate: "v \<noteq> u \<or> k \<notin> rel_dom L"
  shows "external_slot_values installed v k = external_slot_values E v k"
proof (rule set_eqI)
  fix T
  have locations: "\<And>w. binds_slot E v k w \<Longrightarrow> w \<in> environment_uses E"
    using old_formed unfolding environment_formed_def by blast
  show "T \<in> external_slot_values installed v k \<longleftrightarrow> T \<in> external_slot_values E v k"
    using old_artifacts locations by (auto simp: external_slot_values_def other_bindings[OF separate])
qed

end

text \<open>
  The original source artifact is shared at its existing use. Each literal slot
  receives a fresh use containing its exact artifact value. Every old artifact
  value is unchanged, old bindings are retained, and all other source-slot
  bindings and literal observations are exact. The construction works with
  arbitrary pre-existing bindings at other slots of the shared source.
\<close>

end
