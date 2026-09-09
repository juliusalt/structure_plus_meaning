theory Factor_Construction_Permission_Completion
  imports Factor_Construction_Comparison Factor_Related_Test_Clauses
    Factor_Recorded_Construction_Obligations
begin

section \<open>A checked clause consumes an independently proved comparison\<close>

theorem construction_permission_from_saturation:
  assumes boundary: "\<And>p. schema_call_formed P d p \<longleftrightarrow> term_formed p"
    and meaning: "(\<lambda>p. (d,p)\<in>positive_meaning P)=saturate_observation construction_account_presents test"
  shows "construction_permission_invariant P d"
proof -
  have formation: "rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (schema_call_formed P d) (schema_call_formed P d)"
    using construction_account_formed by (auto simp: rel_fun_def presentation_transport_def boundary)
  have truth: "rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (\<lambda>p. (d,p)\<in>positive_meaning P) (\<lambda>p. (d,p)\<in>positive_meaning P)"
    by (simp only: meaning; rule presentation_class.saturation_invariant[OF construction_account_presentation_class])
  show ?thesis using formation truth by (simp only: construction_permission_observations; blast)
qed

theorem checked_construction_permission:
  assumes package: "native_package_at H pu pr P" and reference: "native_package_at H cu cr C"
    and member: "d\<in>system_definitions P" and comparison_entry: "k\<in>system_definitions C"
    and comparison: "\<And>u v. (k,Pair_Term u v)\<in>positive_meaning C \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents u v"
    and source: "site_value_presents H (fst d) (snd d) p"
    and template: "schema_reference_presents (related_test_clause x y s t k test) v"
    and checked: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
  shows "construction_permission_invariant P d"
    "(\<lambda>z. (d,z)\<in>positive_meaning P)=saturate_observation construction_account_presents
      (\<lambda>z. (test,z)\<in>positive_meaning P)"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
proof -
  have boundary: "schema_call_formed P d z \<longleftrightarrow> term_formed z" for z
    by (rule admitted_related_test_meaning(1)[OF package member source template checked variables sockets])
  have dependencies: "{k,test}\<subseteq>system_definitions P"
    by (rule admitted_related_test_meaning(2)[OF package member source template checked variables sockets])
  have local_entry: "k\<in>system_definitions P" using dependencies by blast
  have shared: "(k,Pair_Term u v)\<in>positive_meaning P \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents u v" for u v
    by (simp only: native_packages_shared_meaning[OF package reference local_entry comparison_entry] comparison)
  show exact: "(\<lambda>z. (d,z)\<in>positive_meaning P)=saturate_observation construction_account_presents
      (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (intro ext; simp only: admitted_related_test_meaning(3)[OF package member source template checked variables sockets]
      shared saturate_observation_def)
  show "construction_permission_invariant P d" by (rule construction_permission_from_saturation[OF boundary exact])
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z" by (rule boundary)
qed

theorem recorded_construction_from_checked_permission:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d z I K"
    and common: "environment_formed H" "environment_included F H"
    and reference: "native_package_at H cu cr C" and member: "d\<in>system_definitions P"
    and comparison_entry: "k\<in>system_definitions C"
    and comparison: "\<And>u v. (k,Pair_Term u v)\<in>positive_meaning C \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents u v"
    and source: "site_value_presents H (fst d) (snd d) p"
    and template: "schema_reference_presents (related_test_clause x y s t k test) v"
    and checked: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
    and minimal: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact (construction_account_output a)"
    and account: "construction_account_presents a z" and truth: "(d,z)\<in>positive_meaning P"
  shows "recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    "remaining_obligations {c. observation_condition c} (construction_permission_obligations P d)={}"
proof -
  have retained: "native_package_at H pu pr P" by (rule native_package_included[OF package common(2,1)])
  have invariant: "construction_permission_invariant P d"
    by (rule checked_construction_permission(1)[OF retained reference member comparison_entry comparison
      source template checked variables sockets])
  show "recorded_construction_cause_at E gu gr G (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    by (simp only: recorded_construction_residual_exact[OF scope package app])
      (use minimal payload account truth invariant in
        \<open>auto simp: remaining_obligations_def recorded_construction_obligations_def\<close>)
  show "remaining_obligations {c. observation_condition c} (construction_permission_obligations P d)={}"
    using invariant by (simp only: remaining_obligations_empty construction_permission_obligations_exact)
qed

section \<open>An explicit new policy completes a literal test\<close>

definition construction_order_test_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_order_test_system=add_view_definition construction_comparison_system 262 data_x
    {(0,data_rule (exact_term_pattern order_audit_claim) {})}"

interpretation construction_order_test_view: positive_view construction_comparison_system 262 data_x
  "{(0,data_rule (exact_term_pattern order_audit_claim) {})}"
  by (unfold_locales)
    (use construction_comparison_definition_bound
      construction_claim_formed[OF order_audit_construction order_audit_coordinates]
      in \<open>auto simp: schema_formed_def schema_dependencies_def single_valued_def rel_ran_def dest: subsetD\<close>)

lemma construction_order_test_system_formed [simp]: "schema_system_formed construction_order_test_system"
  using construction_order_test_view.formed by (simp only: construction_order_test_system_def)

lemma construction_order_test_definitions [simp]:
  "system_definitions construction_order_test_system=insert 262 (system_definitions construction_comparison_system)"
  by (simp add: construction_order_test_system_def)

lemma construction_order_test_call:
  "schema_call_formed construction_order_test_system d z \<longleftrightarrow>
    d\<in>system_definitions construction_order_test_system \<and> term_formed z"
  using added_variable_calls[OF construction_comparison_system_formed
    construction_order_test_view.formed construction_comparison_call]
  by (simp only: construction_order_test_system_def)

lemma construction_order_test_clause:
  "((262,c),S)\<in>system_clauses construction_order_test_system \<longleftrightarrow>
    (c,S)\<in>{(0,data_rule (exact_term_pattern order_audit_claim) {})}"
  by (simp add: construction_order_test_system_def construction_order_test_view.no_old_clause)

lemma construction_order_test_meaning:
  "(262,z)\<in>positive_meaning construction_order_test_system \<longleftrightarrow> z=order_audit_claim"
  by (subst ordinary_positive_entry_valuation)
    (use construction_claim_formed[OF order_audit_construction order_audit_coordinates]
      in \<open>auto simp: construction_order_test_clause schema_variables_def construction_order_test_call\<close>)

lemma construction_order_test_comparison:
  "(261,Pair_Term p q)\<in>positive_meaning construction_order_test_system \<longleftrightarrow>
    presentation_transport construction_account_presents construction_account_presents p q"
proof -
  have member: "261\<in>system_definitions construction_comparison_system" by simp
  show ?thesis using construction_order_test_view.old_meaning[OF member, of "Pair_Term p q"]
    by (simp only: construction_order_test_system_def construction_comparison_at_pair)
qed

definition construction_completion_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_completion_system=add_view_definition construction_order_test_system 263 data_x
    {(0,related_test_clause 0 1 0 1 261 262)}"

interpretation construction_completion_view: positive_view construction_order_test_system 263 data_x
  "{(0,related_test_clause 0 1 0 1 261 262)}"
  by (rule related_test_view)
    (use construction_comparison_definition_bound in \<open>auto dest: subsetD\<close>)

lemma construction_completion_system_formed [simp]: "schema_system_formed construction_completion_system"
  using construction_completion_view.formed by (simp only: construction_completion_system_def)

lemma construction_completion_definitions [simp]:
  "system_definitions construction_completion_system=insert 263 (system_definitions construction_order_test_system)"
  by (simp add: construction_completion_system_def)

lemma construction_completion_call:
  "schema_call_formed construction_completion_system d z \<longleftrightarrow>
    d\<in>system_definitions construction_completion_system \<and> term_formed z"
  using added_variable_calls[OF construction_order_test_system_formed
    construction_completion_view.formed construction_order_test_call]
  by (simp only: construction_completion_system_def)

lemma construction_completion_meaning:
  "(263,z)\<in>positive_meaning construction_completion_system \<longleftrightarrow>
    presentation_transport construction_account_presents construction_account_presents z order_audit_claim"
  by (simp only: construction_completion_system_def
      related_test_view_meaning[OF construction_completion_view.positive_view_axioms zero_neq_one zero_neq_one]
      construction_order_test_comparison construction_order_test_meaning; simp)

lemma construction_completion_old_test:
  "(262,z)\<in>positive_meaning construction_completion_system \<longleftrightarrow> z=order_audit_claim"
proof -
  have member: "262\<in>system_definitions construction_order_test_system" by simp
  show ?thesis using construction_completion_view.old_meaning[OF member, of z]
    by (simp only: construction_completion_system_def construction_order_test_meaning)
qed

theorem construction_completed_permission_invariant:
  "construction_permission_invariant construction_completion_system 263"
proof (rule construction_permission_from_saturation[where test="\<lambda>p. p=order_audit_claim"])
  show "schema_call_formed construction_completion_system 263 p \<longleftrightarrow> term_formed p" for p
    by (simp add: construction_completion_call)
  show "(\<lambda>p. (263,p)\<in>positive_meaning construction_completion_system)=
      saturate_observation construction_account_presents (\<lambda>p. p=order_audit_claim)"
    by (intro ext) (simp add: construction_completion_meaning saturate_observation_def)
qed

lemma construction_order_account_presentations:
  "construction_account_presents (([],order_audit_bases),empty_source_construction) order_audit_claim"
  "construction_account_presents (([],order_audit_bases),empty_source_construction) reversed_base_claim"
proof -
  show "construction_account_presents (([],order_audit_bases),empty_source_construction) order_audit_claim"
    using order_audit_construction order_audit_coordinates
    by (simp only: construction_account_at_claim[OF construction_claim_term_presents[OF order_audit_construction]]; blast)
  show "construction_account_presents (([],order_audit_bases),empty_source_construction) reversed_base_claim"
    using order_audit_construction order_audit_coordinates
    by (simp only: construction_account_at_claim[OF reversed_base_claim_presents]; blast)
qed

theorem construction_completed_order_tests:
  "(263,order_audit_claim)\<in>positive_meaning construction_completion_system"
  "(263,reversed_base_claim)\<in>positive_meaning construction_completion_system"
  "(262,reversed_base_claim)\<notin>positive_meaning construction_completion_system"
  "\<not>construction_permission_invariant order_sensitive_construction_program ()"
  using construction_order_account_presentations reversed_base_claim_different
    order_sensitive_construction_not_admitted
  by (auto simp: construction_completion_meaning construction_completion_old_test presentation_transport_def)

theorem construction_original_entry_still_noninvariant:
  "\<not>construction_permission_invariant construction_completion_system 262"
proof
  assume invariant: "construction_permission_invariant construction_completion_system 262"
  have same: "(262,order_audit_claim)\<in>positive_meaning construction_completion_system \<longleftrightarrow>
      (262,reversed_base_claim)\<in>positive_meaning construction_completion_system"
    by (rule construction_permission_invariantD(2)[OF invariant order_audit_construction order_audit_coordinates
      construction_claim_term_presents[OF order_audit_construction] reversed_base_claim_presents])
  show False using same reversed_base_claim_different by (simp only: construction_completion_old_test; blast)
qed

theorem construction_completed_permission_conditions:
  "remaining_obligations {c. observation_condition c} (construction_permission_obligations construction_completion_system 263)={}"
  "remaining_obligations {c. observation_condition c} (construction_permission_obligations construction_completion_system 262)\<noteq>{}"
proof -
  show "remaining_obligations {c. observation_condition c} (construction_permission_obligations construction_completion_system 263)={}"
    by (simp only: remaining_obligations_empty construction_permission_obligations_exact)
      (rule construction_completed_permission_invariant)
  show "remaining_obligations {c. observation_condition c} (construction_permission_obligations construction_completion_system 262)\<noteq>{}"
    by (simp only: remaining_obligations_empty construction_permission_obligations_exact)
      (rule construction_original_entry_still_noninvariant)
qed

section \<open>The completed policy has actual native code and checked whole-definition evidence\<close>

theorem native_completed_construction_permission:
  "\<exists>E :: local_address option artifact_environment. \<exists>eu Q d k test T p v.
    closed_native_package_at E eu [] Q \<and> native_package_environment E eu []=E \<and>
    d\<in>system_definitions Q \<and> construction_permission_invariant Q d \<and>
    native_single_clause_at E (fst d) (snd d) T \<and>
    site_value_presents E (fst d) (snd d) p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<exists>x y s t. x\<noteq>y \<and> s\<noteq>t \<and> T=related_test_clause x y s t k test) \<and>
    (\<forall>z. schema_call_formed Q d z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (d,z)\<in>positive_meaning Q \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents z order_audit_claim) \<and>
    (d,reversed_base_claim)\<in>positive_meaning Q \<and> (test,reversed_base_claim)\<notin>positive_meaning Q"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and eu Q where compiled:
    "inj_on g (system_definitions construction_completion_system)"
    "closed_native_package_at E eu [] Q" "native_package_environment E eu []=E"
    "system_alpha_variant (rename_system g construction_completion_system) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning construction_completion_system"
    using program_compilation_total[OF construction_completion_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at E eu [] Q" using compiled(2) by (simp add: closed_native_package_at_def)
  have member: "263\<in>system_definitions construction_completion_system"
    "262\<in>system_definitions construction_completion_system" by simp_all
  have target: "g 263\<in>system_definitions Q"
    using member(1) compiled(4) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have interface: "system_interface construction_completion_system 263=Pattern_Variable 0"
    by (rule system_interface_unique[OF construction_completion_system_formed])
      (simp add: construction_completion_system_def)
  have family: "system_clause_family construction_completion_system 263={(0,related_test_clause 0 1 0 1 261 262)}"
    using construction_completion_view.view_clause_family by (simp only: construction_completion_system_def)
  obtain T p v where read:
    "native_single_clause_at E (fst (g 263)) (snd (g 263)) T"
    "schema_alpha_variant (rename_schema id id g (related_test_clause (0::nat) 1 (0::nat) 1 261 262)) T"
    "site_value_presents E (fst (g 263)) (snd (g 263)) p" "schema_reference_presents T v"
    "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using compiled_single_clause_reading[OF construction_completion_system_formed compiled(1,4)
      package member(1) interface family] by blast
  have alpha: "schema_alpha_variant (related_test_clause (0::nat) 1 (0::nat) 1 (g 261) (g 262)) T"
    using read(2) by simp
  have template: "\<exists>x y s t. x\<noteq>y \<and> s\<noteq>t \<and> T=related_test_clause x y s t (g 261) (g 262)"
    by (rule related_test_alpha_profile[OF alpha zero_neq_one zero_neq_one])
  have call: "schema_call_formed Q (g 263) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF construction_completion_system_formed compiled(1,4) member(1)]
      construction_completion_call; simp)
  have meaning: "(g 263,z)\<in>positive_meaning Q \<longleftrightarrow>
      presentation_transport construction_account_presents construction_account_presents z order_audit_claim" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) member(1) compiled(5)] construction_completion_meaning)
  have invariant: "construction_permission_invariant Q (g 263)"
  proof (rule construction_permission_from_saturation[OF call, where test="\<lambda>p. p=order_audit_claim"])
    show "(\<lambda>p. (g 263,p)\<in>positive_meaning Q)=saturate_observation construction_account_presents (\<lambda>p. p=order_audit_claim)"
      by (intro ext) (simp add: meaning saturate_observation_def)
  qed
  have completed: "(g 263,reversed_base_claim)\<in>positive_meaning Q"
    using construction_completed_order_tests(2)
    by (simp only: compiled_system_meaning_at[OF compiled(1) member(1) compiled(5)])
  have unchanged: "(g 262,reversed_base_claim)\<notin>positive_meaning Q"
    using construction_completed_order_tests(3)
      compiled_system_meaning_at[OF compiled(1) member(2) compiled(5), where t=reversed_base_claim] by blast
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ eu], rule exI[of _ Q], rule exI[of _ "g 263"],
      rule exI[of _ "g 261"], rule exI[of _ "g 262"], rule exI[of _ T], rule exI[of _ p], rule exI[of _ v])
      (use compiled(2,3) target invariant read(1,3-5) template call meaning completed unchanged in blast)
qed

text \<open>
  The sufficient contract reads the actual complete permission definition.
  Its correspondence dependency belongs to an independently proved reference
  package. Shared-definition agreement transfers that fixed meaning to the
  actual candidate package. The two-premise rule then proves global formation
  and truth invariance through the general saturation contract.

  Recorded causes retain their original minimal scope, package, application,
  payload, and account. A larger common environment can retain the reference
  root and the checked definition as evidence while preserving the original
  package exactly. The generic obligation account combines this established
  invariance with the remaining four actual cause conditions.

  The example deliberately constructs a new completed policy. It accepts
  both complete base orders and leaves its literal test, and the earlier
  order-sensitive program, unchanged and noninvariant. Native compilation
  supplies actual code, complete definition reports, and accepted ordinary
  whole-definition evidence. This does not replace an existing cause's policy.

  Factor_Construction_Permission_Admission joins the whole sufficient profile
  through one native checker, including common-environment and fixed-reference
  checks. This profile does not decide every semantically invariant program.
  Native presentation of the mathematical comparison and saturation proofs,
  higher protocols, reflection, and genesis retain their separate obligations.
\<close>

end
