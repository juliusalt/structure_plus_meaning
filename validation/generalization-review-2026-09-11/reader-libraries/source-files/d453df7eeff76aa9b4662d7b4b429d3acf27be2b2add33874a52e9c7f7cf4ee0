theory Factor_Schema_Environments
  imports Factor_Schema_Totality Factor_Reference_Environments
begin

section \<open>Actual native schema construction over existing callee anchors\<close>

theorem schema_environment_compilation:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
    and E :: "local_address option artifact_environment"
  assumes schema: "schema_formed S" and ef: "environment_formed E"
    and callees: "\<forall>d\<in>schema_dependencies S. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
  shows "\<exists>F u R r f h. environment_formed F \<and> environment_included E F \<and> u \<notin> environment_uses E \<and>
    artifact_at F u R \<and> native_schema_at F u r (rename_schema f h id S) \<and>
    inj_on f (schema_variables S) \<and> inj_on h (schema_sockets S) \<and>
    (\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have addresses: "\<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
  proof (intro ballI)
    fix d assume dependency: "d \<in> schema_dependencies S"
    obtain T where anchor: "anchor_formed (T,snd d)" using callees dependency by blast
    show "octets_formed (snd d)" using anchor by (auto simp: anchor_formed_def exact_formed_def)
  qed
  obtain R :: exact_artifact and r :: local_address
    and f :: "'a \<Rightarrow> local_address" and h :: "'s \<Rightarrow> local_address"
    and L :: "(local_address \<times> exact_artifact) set"
    and C :: "(local_address \<times> local_address option definition_site) set" where compiled:
    "exact_formed R" "inj_on f (schema_variables S)" "inj_on h (schema_sockets S)"
    "\<forall>F u. environment_formed F \<longrightarrow> artifact_at F u R \<longrightarrow>
      syntax_references F u L C \<longrightarrow> native_schema_at F u r (rename_schema f h id S)"
    "\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t"
    "reference_table_formed L C" "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    "rel_ran C = schema_dependencies S"
    using schema_compilation_total[OF schema addresses] by metis
  have targets: "\<forall>d\<in>rel_ran C. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    using callees compiled(8) by simp
  obtain F u where extension:
    "environment_formed F" "environment_included E F" "u \<notin> environment_uses E"
    "artifact_at F u R" "syntax_references F u L C"
    "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using reference_environment_total[OF ef compiled(1,6,7) targets] by metis
  have quote: "native_schema_at F u r (rename_schema f h id S)"
    using compiled(4) extension(1,4,5) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ R], rule exI[of _ r],
      rule exI[of _ f], rule exI[of _ h]) (use extension quote compiled(2,3,5) in blast)
qed

corollary callee_free_schema_native_total:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes formed: "schema_formed S" and no_callees: "schema_dependencies S = {}"
  shows "\<exists>E u r f h. environment_formed E \<and> native_schema_at E u r (rename_schema f h id S) \<and>
    inj_on f (schema_variables S) \<and> inj_on h (schema_sockets S) \<and>
    (\<forall>X t. schema_rule_instance (rename_schema f h id S) X t \<longleftrightarrow> schema_rule_instance S X t)"
proof -
  let ?E = "\<lparr>environment_artifacts={}, environment_bindings={}\<rparr> :: local_address option artifact_environment"
  have ef: "environment_formed ?E" by (simp add: environment_formed_def artifact_at_def binds_slot_def single_valued_def)
  have targets: "\<forall>d\<in>schema_dependencies S. \<exists>T. artifact_at ?E (fst d) T \<and> anchor_formed (T,snd d)"
    using no_callees by simp
  show ?thesis using schema_environment_compilation[OF formed ef targets] by metis
qed

text \<open>
  A source schema can be compiled into an actual finite native quotation over
  any formed environment supplying its callee anchors. The construction adds
  one fresh code use, fresh literal uses, and the required bindings. Every old
  artifact and every binding at an old use is unchanged. Semantic equivalence
  is proved for all arguments and support relations. Callee-free schemas,
  including arbitrary complete material premises, require no initial package.
\<close>

end
