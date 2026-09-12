theory Factor_Prescribed_Environments
  imports Factor_Prescribed_Schemas Factor_Reference_Environments
begin

section \<open>Actual environments retain the specified schema coordinates\<close>

theorem schema_environment_at_coordinates:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
    and E :: "local_address option artifact_environment"
  assumes schema: "schema_formed S" and ef: "environment_formed E"
    and callees: "\<forall>d\<in>schema_dependencies S. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    and binders: "binder_addressing (schema_variables S) f"
    and sockets: "finite_addressing (schema_sockets S) h"
    and separate: "f ` schema_variables S \<inter> h ` schema_sockets S={}"
  shows "\<exists>F u R r. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    artifact_at F u R \<and> native_schema_at F u r (rename_schema f h id S) \<and>
    (\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have addresses: "\<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
    using callees by (auto simp: anchor_formed_def exact_formed_def)
  obtain R r L C where compiled:
    "exact_formed R"
    "\<forall>F u. environment_formed F \<longrightarrow> artifact_at F u R \<longrightarrow>
      syntax_references F u L C \<longrightarrow> native_schema_at F u r (rename_schema f h id S)"
    "\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t"
    "reference_table_formed L C" "rel_dom L \<union> rel_dom C\<subseteq>rra_carrier (object_structure R)"
    "rel_ran C=schema_dependencies S"
    using schema_compilation_at_coordinates[OF schema addresses binders sockets separate] by blast
  have targets: "\<forall>d\<in>rel_ran C. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    using callees compiled(6) by simp
  obtain F u where extension:
    "environment_formed F" "environment_included E F" "u\<notin>environment_uses E"
    "artifact_at F u R" "syntax_references F u L C"
    "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using reference_environment_total[OF ef compiled(1,4,5) targets] by metis
  have native: "native_schema_at F u r (rename_schema f h id S)"
    using compiled(2) extension(1,4,5) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ R], rule exI[of _ r])
    (use extension native compiled(3) in blast)
qed

theorem schema_environment_preserving_sockets:
  fixes S :: "('a,local_address,local_address option definition_site) factor_schema"
    and E :: "local_address option artifact_environment"
  assumes schema: "schema_formed S" and ef: "environment_formed E"
    and callees: "\<forall>d\<in>schema_dependencies S. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    and sockets: "\<forall>s\<in>schema_sockets S. octets_formed s"
  shows "\<exists>f F u R r. binder_addressing (schema_variables S) f \<and>
    f ` schema_variables S \<inter> schema_sockets S={} \<and>
    environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    artifact_at F u R \<and> native_schema_at F u r (rename_schema f id id S) \<and>
    (\<forall>X t. schema_rule_instance (rename_schema f id id S) X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have finite: "finite (schema_sockets S)"
    using schema by (simp add: schema_sockets_def schema_formed_def finite_rel_dom)
  obtain f where addressing: "binder_addressing (schema_variables S) f"
    and separate: "f ` schema_variables S \<inter> schema_sockets S={}"
    using binder_addressing_avoiding[OF schema_variables_finite[OF schema] finite] by blast
  have socket_map: "finite_addressing (schema_sockets S) id"
    using sockets by (simp add: finite_addressing_def)
  have apart: "f ` schema_variables S \<inter> id ` schema_sockets S={}" using separate by simp
  show ?thesis using addressing separate
    schema_environment_at_coordinates[OF schema ef callees addressing socket_map apart] by blast
qed

text \<open>
  The destination environment supplies the actual literal and callee bindings.
  All artifacts and outgoing bindings at old uses are preserved. For formed
  existing sockets, the identity socket map is available after choosing binder
  coordinates away from their finite set. This preserves socket identity in
  the projected schema, in addition to preserving its rule-instance relation.
\<close>

end
