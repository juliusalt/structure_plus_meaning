theory Factor_Continuation_Programs
  imports Factor_Native_Continuation Factor_Pattern_Programs
begin

section \<open>Explicit finite programs with proved presentation invariance\<close>

lemma continuation_recognizer_program:
  assumes pf: "pattern_formed p"
    and recognizes: "\<And>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<Longrightarrow>
      (pattern_accepts p t\<longleftrightarrow>M S T U C cu cr)"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    d\<in>system_definitions Q \<and> continuation_permission_invariant Q d \<and>
    (\<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M S T U C cu cr))"
proof -
  let ?P="recognizer_system a p"
  have formed: "schema_system_formed ?P" by (rule recognizer_system_formed[OF pf])
  have member: "()\<in>system_definitions ?P"
    by (simp add: system_definitions_def recognizer_system_def rel_dom_def)
  have observed: "\<And>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<Longrightarrow>
      (((),t)\<in>positive_meaning ?P\<longleftrightarrow>M S T U C cu cr)"
    using recognizer_positive_meaning[OF pf, where a=a] recognizes by blast
  have boundary: "\<And>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<Longrightarrow>
      schema_call_formed ?P () t"
    using continuation_value_presents_formed recognizer_call_formed[OF pf, where a=a] by blast
  have invariant: "continuation_permission_invariant ?P ()"
    unfolding continuation_permission_invariant_def
  proof (intro allI impI)
    fix S T U C cu cr t v assume first: "continuation_value_presents S T U C cu cr t"
      and second: "continuation_value_presents S T U C cu cr v"
    show "(schema_call_formed ?P () t\<longleftrightarrow>schema_call_formed ?P () v) \<and>
      (((),t)\<in>positive_meaning ?P\<longleftrightarrow>((),v)\<in>positive_meaning ?P)"
      using boundary[OF first] boundary[OF second] observed[OF first] observed[OF second] by blast
  qed
  obtain E :: "local_address option artifact_environment" and pu Q d where compiled:
    "closed_native_package_at E pu [] Q" "native_package_environment E pu []=E"
    "d\<in>system_definitions Q" "continuation_permission_invariant Q d"
    "\<forall>t. (schema_call_formed Q d t\<longleftrightarrow>schema_call_formed ?P () t) \<and>
      ((d,t)\<in>positive_meaning Q\<longleftrightarrow>((),t)\<in>positive_meaning ?P)"
    using native_continuation_program_compilation[OF formed member invariant] by blast
  have every: "\<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M S T U C cu cr)"
  proof (intro allI impI)
    fix S T U C cu cr t assume present: "continuation_value_presents S T U C cu cr t"
    show "schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M S T U C cu cr)"
      using compiled(5)[rule_format, of t] boundary[OF present] observed[OF present] by blast
  qed
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ d])
       (use compiled(1-4) every in blast)
qed

theorem constant_continuation_program:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    d\<in>system_definitions Q \<and> continuation_permission_invariant Q d \<and>
    (\<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>b))"
proof -
  let ?p="if b then Pattern_Variable (0::nat) else Pattern_Payload []"
  have pf: "pattern_formed ?p" by (simp add: octets_formed_def)
  have recognizes: "\<And>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<Longrightarrow>
      (pattern_accepts ?p t\<longleftrightarrow>b)"
  proof -
    fix S T U C cu cr t assume present: "continuation_value_presents S T U C cu cr t"
    have tf: "term_formed t" using continuation_value_presents_formed[OF present] by blast
    have pair: "\<exists>a v. t=Pair_Term a v" by (rule continuation_value_is_pair[OF present])
    show "pattern_accepts ?p t\<longleftrightarrow>b"
    proof (cases b)
      case True then show ?thesis using tf by simp
    next
      case False then show ?thesis using pair by (auto simp: pattern_accepts_def)
    qed
  qed
  show ?thesis by (rule continuation_recognizer_program[OF pf recognizes])
qed

theorem constant_native_continuation_application:
  assumes before: "snapshot_formed S" and proposal: "transaction_formed T" and after: "snapshot_formed U"
    and material: "environment_formed C" and site: "(cu,cr)\<in>environment_positions C"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>pu au Q d t I K.
    environment_formed F \<and> native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
    continuation_permission_invariant Q d \<and> continuation_value_presents S T U C cu cr t \<and>
    native_application_formed F pu [] au [] \<and>
    (native_continuation_at F pu [] au [] S T U C cu cr\<longleftrightarrow>b) \<and>
    (native_advance_at F pu [] au [] S T U C cu cr\<longleftrightarrow>b \<and> transact S T (Applied U))"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d where policy:
    "closed_native_package_at E pu [] Q" "d\<in>system_definitions Q" "continuation_permission_invariant Q d"
    "\<forall>S T U C cu cr t. continuation_value_presents S T U C cu cr t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>b)"
    using constant_continuation_program[of b] by blast
  have package: "native_package_at E pu [] Q" using policy(1) by (simp add: closed_native_package_at_def)
  obtain t where present: "continuation_value_presents S T U C cu cr t"
    using continuation_value_presents_total[OF assms] by blast
  have observed: "schema_call_formed Q d t" "(d,t)\<in>positive_meaning Q\<longleftrightarrow>b"
    using policy(4)[rule_format, OF present] by auto
  have permission: "factor_continues Q d S T U C cu cr\<longleftrightarrow>b"
    using factor_continuation_at_presentation[OF policy(3) present] observed(2) by blast
  obtain F au I K where future: "environment_formed F" "native_package_at F pu [] Q"
    "native_application_at F au [] d t I K"
    "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed Q d t"
    "native_continuation_at F pu [] au [] S T U C cu cr\<longleftrightarrow>factor_continues Q d S T U C cu cr"
    using native_continuation_application_total[OF package policy(2,3) present] by blast
  have advance: "native_advance_at F pu [] au [] S T U C cu cr\<longleftrightarrow>b \<and> transact S T (Applied U)"
    using future(5) permission by (auto simp: native_advance_at_def)
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ pu], rule exI[of _ au], rule exI[of _ Q],
        rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use future policy(3) present observed(1) permission advance in blast)
qed

section \<open>Structural success and ordinary permission can vary independently\<close>

theorem structural_success_can_be_refused:
  assumes sf: "snapshot_formed S" and cf: "environment_formed C" and site: "(cu,cr)\<in>environment_positions C"
  shows "transact S empty_transaction (Applied S) \<and>
    (\<exists>F :: local_address option artifact_environment. \<exists>pu au Q d t I K.
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      continuation_permission_invariant Q d \<and> continuation_value_presents S empty_transaction S C cu cr t \<and>
      native_application_formed F pu [] au [] \<and>
      \<not>native_continuation_at F pu [] au [] S empty_transaction S C cu cr \<and>
      \<not>native_advance_at F pu [] au [] S empty_transaction S C cu cr)"
  using empty_transaction_preserves_snapshot[OF sf]
    constant_native_continuation_application[OF sf empty_transaction_formed sf cf site, where b=False] by blast

theorem conflict_can_have_continuation_permission:
  assumes sf: "snapshot_formed S" and wf: "snapshot_formed W"
    and selected: "G\<in>fset S" and proposed: "generation_locus G\<in>snapshot_loci W"
    and cf: "environment_formed C" and site: "(cu,cr)\<in>environment_positions C"
  shows "transact S (admission_transaction W) (Conflict (observed_comparison S (admission_transaction W))) \<and>
    (\<exists>F :: local_address option artifact_environment. \<exists>pu au Q d t I K.
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      continuation_permission_invariant Q d \<and>
      continuation_value_presents S (admission_transaction W) W C cu cr t \<and>
      native_application_formed F pu [] au [] \<and>
      native_continuation_at F pu [] au [] S (admission_transaction W) W C cu cr \<and>
      \<not>native_advance_at F pu [] au [] S (admission_transaction W) W C cu cr)"
proof -
  have conflict: "transact S (admission_transaction W)
    (Conflict (observed_comparison S (admission_transaction W)))"
    by (rule admitting_a_selected_locus_conflicts[OF sf wf selected proposed])
  obtain F :: "local_address option artifact_environment" and pu au Q d t I K where calls:
    "native_package_at F pu [] Q" "native_application_at F au [] d t I K"
    "continuation_permission_invariant Q d"
    "continuation_value_presents S (admission_transaction W) W C cu cr t"
    "native_application_formed F pu [] au []"
    "native_continuation_at F pu [] au [] S (admission_transaction W) W C cu cr"
    using constant_native_continuation_application[
      OF sf admission_transaction_formed[OF wf] wf cf site, where b=True] by blast
  have rejected: "\<not>native_advance_at F pu [] au [] S (admission_transaction W) W C cu cr"
    by (rule native_advance_conflict_rejected[OF conflict])
  show ?thesis
    by (rule conjI[OF conflict], rule exI[of _ F], rule exI[of _ pu], rule exI[of _ au],
        rule exI[of _ Q], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use calls rejected in blast)
qed

text \<open>
  The constant witnesses are actual finite premise-free pattern programs with
  broad formed interfaces. A variable conclusion permits every continuation
  argument; an empty-payload conclusion refuses every such pair argument.
  Their presentation invariance is proved before compilation. The parameter in
  the existence theorem chooses which explicit program is constructed.

  These formed policies and actual applications exhibit refusal of a successful
  transaction and permission on a conflicting proposal. Advancement requires
  both relations. Neither witness omits the program, weakens call formation,
  or substitutes historical membership for a semantic rule.
\<close>

end
