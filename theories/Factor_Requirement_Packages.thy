theory Factor_Requirement_Packages
  imports Factor_Requirement_Guards Factor_Single_Clause_Packages Factor_Retained_Clause_Admission
begin

section \<open>Requirements are calls into the actual retained source package\<close>

theorem native_requirement_meaning:
  fixes E :: "local_address option artifact_environment"
    and R :: "('s\<times>local_address option definition_site) set"
  assumes source: "native_package_at E pu pr P" and included: "environment_included E F"
    and target: "native_package_at F qu qr Q" and member: "d\<in>system_definitions Q"
    and read: "native_single_clause_at F (fst d) (snd d) T"
    and schema: "schema_alpha_variant (requirement_guard_schema R) T"
    and finite: "finite R" and functional: "single_valued R"
    and dependencies: "rel_ran R\<subseteq>system_definitions P"
  shows "(d,t)\<in>positive_meaning Q \<longleftrightarrow>
    term_formed t \<and> (\<forall>(s,k)\<in>R. (k,t)\<in>positive_meaning P)"
proof -
  have ff: "environment_formed F"
    using native_package_projection(1)[OF target] by (simp add: native_package_formed_def)
  have copied: "native_package_at F pu pr P" by (rule native_package_included[OF source included ff])
  have target_dependencies: "rel_ran R\<subseteq>system_definitions Q"
    using native_single_clause_dependencies[OF target member read]
    by (simp only: schema_alpha_dependencies[OF schema] requirement_guard_dependencies)
  have old: "(k,z)\<in>positive_meaning Q \<longleftrightarrow> (k,z)\<in>positive_meaning P"
    if required: "(s,k)\<in>R" for s k z
  proof -
    have positions: "k\<in>system_definitions Q" "k\<in>system_definitions P"
      using dependencies target_dependencies required by (auto simp: rel_ran_def)
    show ?thesis by (rule native_packages_shared_meaning[OF target copied positions])
  qed
  have same: "(\<forall>(s,k)\<in>R. (k,t)\<in>positive_meaning Q) \<longleftrightarrow>
    (\<forall>(s,k)\<in>R. (k,t)\<in>positive_meaning P)"
    using old by (auto simp: case_prod_unfold)
  show ?thesis by (simp only: native_single_clause_meaning[OF target member read]
    schema_alpha_rule_instance[OF schema] requirement_guard_rule[OF finite functional] same)
qed

theorem native_requirement_package_total:
  fixes E :: "local_address option artifact_environment"
    and R :: "('s\<times>local_address option definition_site) set"
  assumes package: "native_package_at E pu pr P" and encoded: "environment_value_presents E e"
    and finite: "finite R" and functional: "single_valued R"
    and dependencies: "rel_ran R\<subseteq>system_definitions P"
  shows "\<exists>F u v Q T f z. environment_formed F \<and> environment_included E F \<and>
    u\<notin>environment_uses E \<and> (u,[])\<notin>system_definitions P \<and>
    native_package_at F pu pr P \<and> native_package_at F v [] Q \<and>
    system_definitions Q=insert (u,[]) (system_definitions P) \<and>
    native_single_clause_at F u [] T \<and> schema_alpha_variant (requirement_guard_schema R) T \<and>
    environment_value_presents F f \<and> schema_reference_presents T z \<and>
    (370,package_subject_argument f (use_data_term v) (Payload_Term []) (definition_site_value (u,[])))
      \<in>positive_meaning (retained_clause_system e z) \<and>
    (\<forall>t. schema_call_formed Q (u,[]) t \<longleftrightarrow> term_formed t) \<and>
    (\<forall>t. ((u,[]),t)\<in>positive_meaning Q \<longleftrightarrow>
      term_formed t \<and> (\<forall>(s,d)\<in>R. (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed Q d t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a)"
proof -
  let ?S="requirement_guard_schema R"
  have sf: "schema_formed ?S" by (rule requirement_guard_formed[OF finite functional])
  have dep: "schema_dependencies ?S\<subseteq>system_definitions P" using dependencies by simp
  obtain F u v Q T where built: "environment_formed F" "environment_included E F"
    "u\<notin>environment_uses E" "(u,[])\<notin>system_definitions P"
    "native_package_at F pu pr P" "native_package_at F v [] Q"
    "system_definitions Q=insert (u,[]) (system_definitions P)"
    "native_single_clause_at F u [] T" "schema_alpha_variant ?S T"
    "\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance ?S X t"
    "\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed Q d t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P)"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a"
    using native_single_clause_package_total[OF package sf dep] by blast
  have member: "(u,[])\<in>system_definitions Q" using built(7) by simp
  have read: "native_single_clause_at F (fst (u,[])) (snd (u,[])) T" using built(8) by simp
  obtain f z where presentation: "environment_value_presents F f" "schema_reference_presents T z"
    "(370,package_subject_argument f (use_data_term v) (Payload_Term []) (definition_site_value (u,[])))
      \<in>positive_meaning (retained_clause_system e z)"
    using retained_clause_presentations_total[OF encoded built(2,6) member read] by blast
  have call: "schema_call_formed Q (u,[]) t \<longleftrightarrow> term_formed t" for t
    by (rule native_single_clause_call[OF built(6) member read])
  have meaning: "((u,[]),t)\<in>positive_meaning Q \<longleftrightarrow>
    term_formed t \<and> (\<forall>(s,d)\<in>R. (d,t)\<in>positive_meaning P)" for t
    by (rule native_requirement_meaning[OF package built(2,6) member read built(9) finite functional dependencies])
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ v], rule exI[of _ Q], rule exI[of _ T],
    rule exI[of _ f], rule exI[of _ z])
    (use built(1-9,11-13) presentation call meaning in blast)
qed

section \<open>An independently admitted installation has the original source meaning\<close>

theorem admitted_requirement_package_meaning:
  fixes E :: "local_address option artifact_environment"
    and R :: "('s\<times>local_address option definition_site) set"
  assumes source: "native_package_at E pu pr P" and encoded: "environment_value_presents E e"
    and reference: "schema_reference_presents T v"
    and schema: "schema_alpha_variant (requirement_guard_schema R) T"
    and finite: "finite R" and functional: "single_valued R"
    and dependencies: "rel_ran R\<subseteq>system_definitions P"
    and target: "native_package_at F qu qr Q" and presented: "environment_value_presents F f"
    and admitted: "(370,package_subject_argument f (use_data_term qu) (Payload_Term qr) (definition_site_value d))
      \<in>positive_meaning (retained_clause_system e v)"
  shows "(d,t)\<in>positive_meaning Q \<longleftrightarrow>
    term_formed t \<and> (\<forall>(s,k)\<in>R. (k,t)\<in>positive_meaning P)"
proof -
  interpret reader: retained_clause_reader e v
    by (rule retained_clause_reader.intro)
      (use environment_value_presents_formed[OF encoded] schema_reference_presents_formed[OF reference] in auto)
  obtain U where actual: "native_package_at F qu qr U" "d\<in>system_definitions U"
    "environment_included E F" "native_single_clause_at F (fst d) (snd d) T"
    using admitted by (simp only: reader.on_values[OF encoded reference presented]; blast)
  have same: "U=Q" by (rule native_package_unique[OF actual(1) target])
  have member: "d\<in>system_definitions Q" using actual(2) same by simp
  show ?thesis by (rule native_requirement_meaning[OF source actual(3) target member actual(4)
    schema finite functional dependencies])
qed

text \<open>
  The source is the complete actual native package already present in the
  environment. The new clause cites its existing definition sites. Compilation
  retains the original package, installs the complete extended package, and
  preserves every old artifact, outgoing binding, interface, and meaning.
  Private binder and socket coordinates may change; the actual callee sites
  and the all-term conjunction are preserved.

  This contract supplies the source and installation that a source-domain-only
  blueprint omits. It does not assert that every development requirement has
  already been represented, or that a complete development record has been
  constructed and admitted.
\<close>

end
