theory Factor_Definition_Environments
  imports Factor_Definition_Compilation Factor_Reference_Environments
begin

section \<open>Actual native definitions over existing callee anchors\<close>

theorem definition_environment_compilation:
  fixes p :: "'a term_pattern"
    and Cs :: "('c \<times> ('a,'s,local_address option definition_site) factor_schema) set"
    and E :: "local_address option artifact_environment"
  assumes pf: "pattern_formed p" and fin: "finite Cs" and sv: "single_valued Cs"
    and formed: "\<forall>S\<in>rel_ran Cs. schema_formed S" and ef: "environment_formed E"
    and callees: "\<forall>d\<in>(\<Union>S\<in>rel_ran Cs. schema_dependencies S).
      \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
  shows "\<exists>F u R f h D. environment_formed F \<and> environment_included E F \<and> u \<notin> environment_uses E \<and>
    artifact_at F u R \<and> native_definition_at F u [] (rename_pattern f p) D \<and>
    inj_on f (pattern_variables p) \<and> schema_family_variant h Cs D \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have addresses: "\<forall>S\<in>rel_ran Cs. \<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
  proof (intro ballI)
    fix S d assume clause: "S \<in> rel_ran Cs" and dependency: "d \<in> schema_dependencies S"
    obtain T where target: "anchor_formed (T,snd d)" using callees clause dependency by blast
    show "octets_formed (snd d)" using target by (auto simp: anchor_formed_def exact_formed_def)
  qed
  obtain R :: exact_artifact and f :: "'a \<Rightarrow> local_address" and h :: "'c \<Rightarrow> local_address"
    and D :: "(local_address \<times> local_address option native_schema) set"
    and L :: "(local_address \<times> exact_artifact) set"
    and C :: "(local_address \<times> local_address option definition_site) set" where compiled:
    "exact_formed R" "inj_on f (pattern_variables p)" "schema_family_variant h Cs D"
    "reference_table_formed L C" "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    "rel_ran C = (\<Union>S\<in>rel_ran Cs. schema_dependencies S)"
    "\<forall>F u. environment_formed F \<longrightarrow> artifact_at F u R \<longrightarrow> syntax_references F u L C \<longrightarrow>
      native_definition_at F u [] (rename_pattern f p) D"
    using definition_compilation_total[OF pf fin sv formed addresses] by metis
  have targets: "\<forall>d\<in>rel_ran C. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
    using callees compiled(6) by simp
  obtain F u where extension: "environment_formed F" "environment_included E F" "u \<notin> environment_uses E"
    "artifact_at F u R" "syntax_references F u L C"
    "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using reference_environment_total[OF ef compiled(1,4,5) targets] by metis
  have quote: "native_definition_at F u [] (rename_pattern f p) D" using compiled(7) extension(1,4,5) by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ R], rule exI[of _ f],
      rule exI[of _ h], rule exI[of _ D]) (use extension quote compiled(2,3) in blast)
qed

text \<open>
  Arbitrary formed interfaces and complete identified clause families have
  actual finite native definition quotations whenever their callees are
  supplied by a formed environment. The construction preserves every old use,
  artifact value, and binding. The interface and clause correspondence is
  structural, with independent theorems for acceptance and rule instances.
\<close>

end
