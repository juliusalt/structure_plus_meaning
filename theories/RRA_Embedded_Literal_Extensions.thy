theory RRA_Embedded_Literal_Extensions
  imports RRA_Literal_Extension RRA_General_Environment_Grafts
begin

locale embedded_literal_extension = literal_extension E u R L
  for E :: "local_address option artifact_environment" and u :: "local_address option"
    and R :: exact_artifact and L :: "(local_address\<times>exact_artifact) set" +
  fixes h :: "local_address option\<Rightarrow>local_address option"
  assumes embedding: "boundary_use_embedding (environment_uses E) u h"
begin

abbreviation result where "result\<equiv>embedded_graft_environment h E (literal_environment R L)"

sublocale graft: environment_graft E "literal_environment R L" u R h
  by (unfold_locales) (rule old_formed, rule literal_formed, rule old_source, simp, rule embedding)

lemma boundary_compatible: "boundary_bindings_compatible h E u (literal_environment R L)"
proof (rule graft.unbound_boundary_compatible)
  fix k v w
  assume imported: "binds_slot (literal_environment R L) None k v"
  have key: "k\<in>rel_dom L" using imported by (auto simp: literal_environment_def binds_slot_def)
  show "\<not>binds_slot E u k w" by (rule slots_unbound[OF key])
qed

theorem result_formed: "environment_formed result"
  using boundary_compatible by (simp only: graft.formed_exact)

lemma result_includes_original: "environment_included E result"
  by (rule graft.includes_original)

lemma result_source: "artifact_at result u R"
  by (rule included_artifact[OF result_includes_original old_source])

lemma result_old_artifacts:
  "v\<in>environment_uses E \<Longrightarrow> artifact_at result v T \<longleftrightarrow> artifact_at E v T"
  by (rule graft.original_artifacts_unchanged)

lemma result_bindings:
  "binds_slot result v k w \<longleftrightarrow>
    binds_slot E v k w \<or> (v=u \<and> k\<in>rel_dom L \<and> w=h (Some k))"
  by (simp add: embedded_graft_environment_def renamed_literal_bindings)

lemma result_source_binding:
  "k\<in>rel_dom L \<Longrightarrow> binds_slot result u k v \<longleftrightarrow> v=h (Some k)"
  using slots_unbound by (auto simp: result_bindings)

lemma result_other_bindings:
  "v\<noteq>u \<or> k\<notin>rel_dom L \<Longrightarrow> binds_slot result v k w \<longleftrightarrow> binds_slot E v k w"
  by (auto simp: result_bindings)

lemma result_literal_artifact:
  "artifact_at result (h (Some k)) T \<longleftrightarrow> (k,T)\<in>L"
  by (simp only: graft.imported_artifacts_exact) simp

lemma result_literal_values:
  "k\<in>rel_dom L \<Longrightarrow> external_slot_values result u k={T. (k,T)\<in>L}"
  by (auto simp only: external_slot_values_def result_source_binding result_literal_artifact mem_Collect_eq)

lemma result_literal_singleton:
  assumes entry: "(k,T)\<in>L"
  shows "external_slot_values result u k={T}"
proof -
  have key: "k\<in>rel_dom L" by (rule rel_domI[OF entry])
  show ?thesis using result_literal_values[OF key] single_valued_fibre[OF table_functional entry] by simp
qed

lemma result_old_literal_values:
  assumes separate: "v\<noteq>u \<or> k\<notin>rel_dom L"
  shows "external_slot_values result v k=external_slot_values E v k"
proof (rule set_eqI)
  fix T
  have locations: "\<And>w. binds_slot E v k w \<Longrightarrow> w\<in>environment_uses E"
    using old_formed unfolding environment_formed_def by blast
  show "T\<in>external_slot_values result v k \<longleftrightarrow> T\<in>external_slot_values E v k"
    using result_old_artifacts locations
    by (auto simp: external_slot_values_def result_other_bindings[OF separate])
qed

end

context literal_extension
begin

lemma original_literal_embedding_contract:
  "embedded_literal_extension E u R L (fresh_use_map (environment_uses E) u)"
  by (unfold_locales)
    (rule original_boundary_embedding[OF environment_uses_finite[OF old_formed]])

end

lemma original_literal_embedding_result:
  "embedded_graft_environment (fresh_use_map (environment_uses E) u) E (literal_environment R L)=
    graft_environment E u (literal_environment R L)"
  by (simp only: embedded_graft_environment_def graft_environment_def)

text \<open>
  Any complete boundary embedding instantiates the existing literal-extension
  prerequisites. The general graft contract owns formation and old-artifact
  preservation; exact binding and literal values retain the supplied mapping.
  The original zero-prefix construction is an explicit complete instance.
  A stored-bound implementation can use the same contract without making
  that original fresh-use choice canonical.
\<close>

end
