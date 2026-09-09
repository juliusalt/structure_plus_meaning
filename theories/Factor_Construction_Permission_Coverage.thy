theory Factor_Construction_Permission_Coverage
  imports Factor_Construction_Query Factor_Program_Tests Factor_Construction_Permission_Admission Factor_Permission_Completion
begin

section \<open>The same observation reduction evaluates agreement with the original test\<close>

theorem construction_completed_truth_agreement:
  assumes completion: "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
    saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
  shows "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      (\<lambda>z. (\<exists>a. construction_account_presents a z) \<and> (d,z)\<in>positive_meaning P) \<longleftrightarrow>
    rel_fun construction_presentation_step (=)
      (\<lambda>z. (d,z)\<in>positive_meaning P) (\<lambda>z. (d,z)\<in>positive_meaning P)"
  by (simp only: completion presentation_class.saturation_fixed_iff[OF construction_account_presentation_class]
    construction_generators.generator_observation_iff)

theorem construction_completion_agreement_residual:
  assumes completion: "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P)"
    and known: "K\<subseteq>{c. observation_condition c}"
  shows "(\<lambda>z. (e,z)\<in>positive_meaning Q)=
      (\<lambda>z. (\<exists>a. construction_account_presents a z) \<and> (d,z)\<in>positive_meaning P) \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (observation_obligations construction_presentation_step (\<lambda>z. (d,z)\<in>positive_meaning P)))
      \<subseteq>{c. observation_condition c}"
proof -
  have residual: "rel_fun construction_presentation_step (=)
      (\<lambda>z. (d,z)\<in>positive_meaning P) (\<lambda>z. (d,z)\<in>positive_meaning P) \<longleftrightarrow>
    rel_ran (remaining_obligations K
      (observation_obligations construction_presentation_step (\<lambda>z. (d,z)\<in>positive_meaning P)))
      \<subseteq>{c. observation_condition c}"
    using exact_obligation_reduction_residual[OF observation_invariance_reduction known,
      unfolded exact_obligation_reduction_def, rule_format,
      where E=construction_presentation_step and a="\<lambda>z. (d,z)\<in>positive_meaning P"] by simp
  show ?thesis by (simp only: construction_completed_truth_agreement[OF completion] residual)
qed

section \<open>The fixed reference supports every actual native test\<close>

locale construction_permission_completion = construction_permission_admission C k c cu cr R
  for C k c cu cr R +
  fixes query :: "local_address option definition_site"
  assumes query_entry: "query\<in>system_definitions R"
    and query_meaning: "\<And>z. (query,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
begin


sublocale completion: presented_permission_completion construction_account_presents
  construction_account_domain "\<lambda>t. \<exists>a. construction_account_presents a t" C k c cu cr R query
  by (rule presented_permission_completion.intro[OF permission.presented_permission_admission_axioms])
    (rule presented_permission_completion_axioms.intro[OF query_entry query_meaning])

theorem program_test_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes formed: "schema_system_formed P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e test. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<noteq>test \<and> {e,test}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert e (insert test (system_definitions R)) \<and>
    native_related_test_package C k F u [] e \<and> construction_permission_invariant Q e \<and>
    (\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R))"
  using completion.program_test_completion[OF formed source_entry]
  by (simp only: construction_permission_observations presented_program_observations)

theorem native_test_completion:
  assumes package: "native_package_at E pu pr P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e test. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<noteq>test \<and> {e,test}\<inter>system_definitions R={} \<and>
    system_definitions Q=insert e (insert test (system_definitions R)) \<and>
    native_related_test_package C k F u [] e \<and> construction_permission_invariant Q e \<and>
    (\<forall>b\<in>{e,test}. \<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (test,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>b\<in>system_definitions R. \<forall>z.
      (schema_call_formed Q b z \<longleftrightarrow> schema_call_formed R b z) \<and>
      ((b,z)\<in>positive_meaning Q \<longleftrightarrow> (b,z)\<in>positive_meaning R))"
  using completion.native_test_completion[OF package source_entry]
  by (simp only: construction_permission_observations presented_program_observations)

theorem program_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes formed: "schema_system_formed P" and source_entry: "d\<in>system_definitions P"
  shows "\<exists>F u Q e. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    e\<in>system_definitions Q \<and> native_related_test_package C k F u [] e \<and>
    construction_permission_invariant Q e \<and>
    (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
    (\<lambda>z. (e,z)\<in>positive_meaning Q)=
      saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k)))"
  using completion.program_completion[OF formed source_entry]
  by (simp only: construction_permission_observations presented_program_observations)

corollary invariant_program_completion:
  fixes P :: "('a,'s,'d,'n) schema_system"
  assumes "schema_system_formed P" "d\<in>system_definitions P" "construction_permission_invariant P d"
  shows "\<exists>F u Q e. closed_native_package_at F u [] Q \<and> construction_permission_invariant Q e \<and>
    (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>a z. construction_account_presents a z \<longrightarrow>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)) \<and>
    (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k)))"
  using completion.invariant_program_completion[OF assms(1,2)] assms(3)
  by (simp only: construction_permission_observations presented_program_observations)

end

section \<open>One native checker precedes every finite source program and every completed policy\<close>

theorem fixed_native_permission_completion_coverage:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu T entry.
    closed_native_package_at B bu [] T \<and>
    (\<forall>P :: ('a,'s,'d,'n) schema_system. \<forall>d. schema_system_formed P \<longrightarrow> d\<in>system_definitions P \<longrightarrow>
      (\<exists>F u Q e. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
        e\<in>system_definitions Q \<and> construction_permission_invariant Q e \<and>
        (\<forall>z. schema_call_formed Q e z \<longleftrightarrow> term_formed z) \<and>
        (\<lambda>z. (e,z)\<in>positive_meaning Q)=
          saturate_observation construction_account_presents (\<lambda>z. (d,z)\<in>positive_meaning P) \<and>
        (\<forall>p. program_entry_value_presents F u [] e p \<longrightarrow>
          (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
            native_package_at G bu [] T \<and> native_application_at G au [] entry p I K \<and>
            native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
            native_positive_holds G bu [] au [] \<and>
            (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
            (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))))"
proof -
  obtain C :: "local_address option artifact_environment" and cu R k query where reference:
    "closed_native_package_at C cu [] R" "{k,query}\<subseteq>system_definitions R"
    "\<forall>z. (k,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)"
    "\<forall>z. (query,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z"
    using native_construction_query_reference by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at C cu [] R" using reference(1) by (simp add: closed_native_package_at_def)
  have cf: "environment_formed C" using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain c where source: "environment_value_presents C c" using environment_value_presents_total[OF cf] by blast
  have comparison: "(k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents p q" for p q
    using reference(3)[rule_format, of "Pair_Term p q"] by simp
  have k: "k\<in>system_definitions R" and query_entry: "query\<in>system_definitions R" using reference(2) by blast+
  interpret completion: construction_permission_completion C k c cu "[]" R query
    by (unfold_locales)
      (rule package, rule source, rule k, rule comparison, rule query_entry, rule reference(4)[rule_format])
  show ?thesis using completion.completion.fixed_checker_completion_coverage
    by (simp only: construction_permission_observations presented_program_observations)
qed

text \<open>
  Every actual native test, and every entry of every formed finite abstract
  positive program, has an admitted native completion. The construction first
  fixes the comparison and query reference, then copies the supplied program
  as literal data in a new test clause and adds one related-witness clause.
  Its meaning is exactly the existing least invariant completion. The original
  program's truth and the reference's old meanings are preserved separately.

  The same exact observation reduction evaluates truth agreement with the
  original test. The full equation includes the whole account boundary;
  completed truth is false outside it. Every invariant original permission has
  identical truth on every complete account. The new variable interface can
  still differ from the original, including on presented accounts. Interface
  agreement remains a separate condition.

  One actual native checker precedes all future finite source programs. Every
  complete presentation of each constructed policy has an actual formed,
  positive checker application with its original scope and bindings retained.
  Empty positive meanings are included. An empty program has no actual entry
  to supply as a test; the quantified entry boundary does not invent one.

  Coverage of invariant truth does not decide invariance of arbitrary
  original code, identify programs with equal truth, replace recorded causes,
  or confer authority on a new policy. Native mathematical-proof checking,
  general recorded-cause admission, higher protocols, reflection, genesis,
  and the final repository audit remain separate obligations.
\<close>

end
