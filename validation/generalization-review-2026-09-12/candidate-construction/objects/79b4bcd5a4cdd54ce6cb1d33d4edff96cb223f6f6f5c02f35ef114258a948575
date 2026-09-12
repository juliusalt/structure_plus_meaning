theory Factor_Package_Retention_Admission
  imports Factor_Package_Coverage
begin

section \<open>Admission of the complete minimal program scope\<close>

abbreviation package_retention_admission_result :: "factor_term \<Rightarrow> bool" where
  "package_retention_admission_result z \<equiv> \<exists>E u r P.
    site_value_presents E u r z \<and> closed_native_package_at E u r P"

definition package_retention_admission_schema :: "(nat,nat,nat) factor_schema" where
  "package_retention_admission_schema=data_rule
    (package_context_pattern (Pattern_Pair data_x data_y) data_z data_w)
    {(0,80,source_root_pattern (Pattern_Pair data_x data_y) data_z data_w),
     (1,51,Pattern_Pair data_x (Pattern_Variable 4)),
     (2,51,Pattern_Pair data_y (Pattern_Variable 5)),
     (3,120,Pattern_Pair (package_context_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 4)),
     (4,121,Pattern_Pair (package_context_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 5))}"

definition package_retention_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "package_retention_admission_system=add_view_definition package_slot_list_system 122 data_x {(0,package_retention_admission_schema)}"

lemma package_retention_admission_system_formed [simp]: "schema_system_formed package_retention_admission_system"
  unfolding package_retention_admission_system_def
  by (rule add_recursive_definition_formed[OF package_slot_list_system_formed])
    (auto simp: package_retention_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_retention_admission_definitions [simp]:
  "system_definitions package_retention_admission_system=insert 122 (system_definitions package_slot_list_system)"
  by (simp add: package_retention_admission_system_def)

lemma package_retention_admission_call:
  "schema_call_formed package_retention_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions package_retention_admission_system \<and> term_formed t"
  using added_variable_calls[OF package_slot_list_system_formed
    package_retention_admission_system_formed[unfolded package_retention_admission_system_def] package_slot_list_call]
  by (simp only: package_retention_admission_system_def[symmetric])

lemma package_retention_admission_old_meaning:
  assumes "d\<in>system_definitions package_slot_list_system"
  shows "(d,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_slot_list_system"
  using added_definition_preserves_old(2)[OF package_slot_list_system_formed
    package_retention_admission_system_formed[unfolded package_retention_admission_system_def], of d t] assms
  by (auto simp: package_retention_admission_system_def)

lemma package_retention_admission_clause [simp]:
  "((122,c),S)\<in>system_clauses package_retention_admission_system \<longleftrightarrow> (c,S)\<in>{(0,package_retention_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_slot_list_system \<Longrightarrow>
    d\<in>system_definitions package_slot_list_system" for d c S
    using package_slot_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((122,c),S)\<notin>system_clauses package_slot_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_retention_admission_system_def)
qed

lemma package_retention_admission_replay_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_slot_reading_system"
  using package_retention_admission_old_meaning[of d t] package_lists_previous_meaning[of d t]
    package_slot_reading_replay_meaning[OF assms, of t] assms by auto

lemma package_retention_admission_components:
  "(80,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (80,t)\<in>positive_meaning package_admission_system"
  "(51,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (51,t)\<in>positive_meaning row_keys_system"
  "(120,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (120,t)\<in>positive_meaning package_source_list_system"
  "(121,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (121,t)\<in>positive_meaning package_slot_list_system"
  using package_retention_admission_replay_meaning[of 80 t] retention_admission_slot_meaning[of 80 t]
    retention_admission_components(1)[of t]
    package_retention_admission_replay_meaning[of 51 t] retention_admission_slot_meaning[of 51 t]
    retention_admission_components(4)[of t]
    package_retention_admission_old_meaning[of 120 t] package_slot_list_old_meaning[of 120 t]
    package_retention_admission_old_meaning[of 121 t] by auto

lemma package_retention_admission_step:
  assumes read:
    "(80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(120,Pair_Term (package_context_term (Pair_Term a b) pu pr) us)\<in>positive_meaning package_source_list_system"
    "(121,Pair_Term (package_context_term (Pair_Term a b) pu pr) ks)\<in>positive_meaning package_slot_list_system"
  shows "(122,package_context_term (Pair_Term a b) pu pr)\<in>positive_meaning package_retention_admission_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then a else if j=1 then b else if j=2 then pu else if j=3 then pr else if j=4 then us else ks"
  have result: "(122,evaluate_pattern ?h (schema_conclusion package_retention_admission_schema))
    \<in>positive_meaning package_retention_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(4)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(5)]] in
        \<open>auto simp: package_retention_admission_schema_def schema_variables_def
          package_retention_admission_call package_retention_admission_components\<close>)
  show ?thesis using result by (simp add: package_retention_admission_schema_def)
qed

lemma package_retention_admission_fields:
  "(122,z)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (\<exists>a b pu pr us ks. z=package_context_term (Pair_Term a b) pu pr \<and>
      (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (120,Pair_Term (package_context_term (Pair_Term a b) pu pr) us)\<in>positive_meaning package_source_list_system \<and>
      (121,Pair_Term (package_context_term (Pair_Term a b) pu pr) ks)\<in>positive_meaning package_slot_list_system)"
proof
  assume holds: "(122,z)\<in>positive_meaning package_retention_admission_system"
  have ordinary: "schema_material_premises S={}"
    if "((122,c),S)\<in>system_clauses package_retention_admission_system" for c S
    using that by (auto simp: package_retention_admission_schema_def)
  have valuation: "(122,z)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (\<exists>c S f. ((122,c),S)\<in>system_clauses package_retention_admission_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed package_retention_admission_system 122 z \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning package_retention_admission_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((122,c),S)\<in>system_clauses package_retention_admission_system"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning package_retention_admission_system"
    using iffD1[OF valuation holds] by blast
  have schema: "S=package_retention_admission_schema" using clause by simp
  have read_0: "(80,source_root_argument (Pair_Term (h 0) (h 1)) (h 2) (h 3))\<in>positive_meaning package_admission_system"
    using support[rule_format, of 0 80 "source_root_pattern (Pattern_Pair data_x data_y) data_z data_w"]
    by (simp add: schema package_retention_admission_schema_def package_retention_admission_components)
  have read_1: "(51,Pair_Term (h 0) (h 4))\<in>positive_meaning row_keys_system"
    using support[rule_format, of 1 51 "Pattern_Pair data_x (Pattern_Variable 4)"]
    by (simp add: schema package_retention_admission_schema_def package_retention_admission_components)
  have read_2: "(51,Pair_Term (h 1) (h 5))\<in>positive_meaning row_keys_system"
    using support[rule_format, of 2 51 "Pattern_Pair data_y (Pattern_Variable 5)"]
    by (simp add: schema package_retention_admission_schema_def package_retention_admission_components)
  have read_3: "(120,Pair_Term (package_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3)) (h 4))\<in>positive_meaning package_source_list_system"
    using support[rule_format, of 3 120 "Pattern_Pair (package_context_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 4)"]
    by (simp add: schema package_retention_admission_schema_def package_retention_admission_components)
  have read_4: "(121,Pair_Term (package_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3)) (h 5))\<in>positive_meaning package_slot_list_system"
    using support[rule_format, of 4 121 "Pattern_Pair (package_context_pattern (Pattern_Pair data_x data_y) data_z data_w) (Pattern_Variable 5)"]
    by (simp add: schema package_retention_admission_schema_def package_retention_admission_components)
  have encoded: "z=package_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3)"
    using shape by (simp add: schema package_retention_admission_schema_def)
  show "\<exists>a b pu pr us ks. z=package_context_term (Pair_Term a b) pu pr \<and>
    (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (120,Pair_Term (package_context_term (Pair_Term a b) pu pr) us)\<in>positive_meaning package_source_list_system \<and>
    (121,Pair_Term (package_context_term (Pair_Term a b) pu pr) ks)\<in>positive_meaning package_slot_list_system"
    by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
      rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"])
      (use encoded read_0 read_1 read_2 read_3 read_4 in blast)
next
  assume "\<exists>a b pu pr us ks. z=package_context_term (Pair_Term a b) pu pr \<and>
    (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (120,Pair_Term (package_context_term (Pair_Term a b) pu pr) us)\<in>positive_meaning package_source_list_system \<and>
    (121,Pair_Term (package_context_term (Pair_Term a b) pu pr) ks)\<in>positive_meaning package_slot_list_system"
  then show "(122,z)\<in>positive_meaning package_retention_admission_system"
    by (blast intro: package_retention_admission_step)
qed

theorem package_retention_admission_sound:
  assumes holds: "(122,z)\<in>positive_meaning package_retention_admission_system"
  shows "package_retention_admission_result z"
proof -
  obtain a b p q us ks where shape: "z=package_context_term (Pair_Term a b) p q"
    and calls: "(80,source_root_argument (Pair_Term a b) p q)\<in>positive_meaning package_admission_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(120,Pair_Term (package_context_term (Pair_Term a b) p q) us)\<in>positive_meaning package_source_list_system"
    "(121,Pair_Term (package_context_term (Pair_Term a b) p q) ks)\<in>positive_meaning package_slot_list_system"
    using holds by (simp only: package_retention_admission_fields) blast
  obtain E pu pr P where source: "environment_value_presents E (Pair_Term a b)"
    and program: "p=use_data_term pu" "q=Payload_Term pr" "native_package_at E pu pr P"
    using calls(1) by (simp only: package_admission_exact factor_term.inject) blast
  have closed: "environment_closed E {pu} (native_package_demands E pu pr)"
    using calls(4,5) by (simp only: program(1,2))
      (simp only: package_stored_coverage[OF source program(3) calls(2,3), symmetric]; blast)
  have presented: "site_value_presents E pu pr z"
    using package_context_presents[OF source program(3)] by (simp only: shape program(1,2))
  show ?thesis using presented program(3) closed by (auto simp: closed_native_package_at_def)
qed

theorem package_retention_admission_complete:
  assumes present: "site_value_presents E pu pr z" and closed: "closed_native_package_at E pu pr P"
  shows "(122,z)\<in>positive_meaning package_retention_admission_system"
proof -
  obtain e where body: "environment_value_presents E e" "z=Pair_Term e (site_data_term pu pr)"
    using present by (auto simp: site_value_presents_def)
  obtain a b where fields: "e=Pair_Term a b"
    using body(1) by (auto simp: environment_value_presents_def)
  have source: "environment_value_presents E (Pair_Term a b)" using body(1) by (simp only: fields)
  have shape: "z=package_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)"
    using body(2) by (simp add: fields site_data_term_def)
  have package: "native_package_at E pu pr P" and boundary: "environment_closed E {pu} (native_package_demands E pu pr)"
    using closed by (auto simp: closed_native_package_at_def)
  have program: "(80,source_root_argument (Pair_Term a b) (use_data_term pu) (Payload_Term pr))
    \<in>positive_meaning package_admission_system" by (rule package_admission_complete[OF source package])
  obtain us ks where keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    using environment_keys_total[OF source] by blast
  have coverage: "(120,Pair_Term (package_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)) us)
      \<in>positive_meaning package_source_list_system \<and>
    (121,Pair_Term (package_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)) ks)
      \<in>positive_meaning package_slot_list_system"
    by (simp only: package_stored_coverage[OF source package keys]) (rule boundary)
  show ?thesis by (simp only: shape)
    (rule package_retention_admission_step[OF program keys conjunct1[OF coverage] conjunct2[OF coverage]])
qed

theorem package_retention_admission_exact:
  "(122,z)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow> package_retention_admission_result z"
  using package_retention_admission_sound package_retention_admission_complete by blast

corollary package_retention_admission_on_values:
  assumes present: "site_value_presents E u r z"
  shows "(122,z)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (\<exists>P. closed_native_package_at E u r P)"
  by (simp only: package_retention_admission_exact)
    (use present site_value_presents_unique[OF _ present] in blast)

corollary package_retention_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(122,package_context_term e pu pr)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (\<exists>u r P. pu=use_data_term u \<and> pr=Payload_Term r \<and> closed_native_package_at E u r P)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  have present: "site_value_presents E u r (package_context_term e (use_data_term u) (Payload_Term r))"
    if "closed_native_package_at E u r P" for u r P
    by (rule package_context_presents[OF source, where P=P])
      (use that in \<open>simp add: closed_native_package_at_def\<close>)
  show ?thesis
    by (simp only: package_retention_admission_exact site_value_presents_def site_data_term_def factor_term.inject)
      (use source unique present[unfolded site_value_presents_def site_data_term_def] in blast)
qed

corollary package_retention_admission_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    environment_closed E {u} (native_package_demands E u r)"
  by (simp only: package_retention_admission_on_values[OF package_context_presents[OF source package]])
    (use package in \<open>auto simp: closed_native_package_at_def\<close>)

corollary package_retention_admission_minimal:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    native_package_environment E u r=E"
  by (simp only: package_retention_admission_at_read[OF source package] native_package_closed_fixed_iff[OF package])

corollary package_retention_admission_canonical:
  assumes package: "native_package_at E u r P"
    and source: "environment_value_presents (native_package_environment E u r) e"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
    \<in>positive_meaning package_retention_admission_system"
  by (rule package_retention_admission_complete[
    OF package_context_presents[OF source native_package_environment_recovers[OF package]]
      native_package_closed_restriction[OF package]])

corollary package_retention_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(122,package_context_term e pu pr)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (122,package_context_term f pu pr)\<in>positive_meaning package_retention_admission_system"
  by (simp only: package_retention_admission_at_source[OF assms(1)] package_retention_admission_at_source[OF assms(2)])

section \<open>Unused material cannot acquire a retention role\<close>

theorem package_retention_rejects_unused_binding:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and stored: "(v,k)\<in>rel_dom (environment_bindings E)"
    and unused: "(v,k)\<notin>native_package_demands E u r"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
    \<notin>positive_meaning package_retention_admission_system"
  by (simp only: package_retention_admission_at_read[OF source package] native_package_closed_coverage[OF package])
    (use stored unused in blast)

theorem package_retention_rejects_unused_artifact:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
    and stored: "v\<in>environment_uses E"
    and unused: "v\<notin>native_package_sources E u r\<union>rel_ran (environment_bindings E)"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
    \<notin>positive_meaning package_retention_admission_system"
  by (simp only: package_retention_admission_at_read[OF source package] native_package_closed_coverage[OF package])
    (use stored unused in blast)

theorem package_retention_at_empty_family:
  assumes source: "environment_value_presents E e" and artifact: "artifact_at E u R"
    and family: "family_at R r {}"
  shows "(122,package_context_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    environment_uses E={u} \<and> environment_bindings E={}"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have checked: "(80,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
    by (rule package_admission_empty[OF source artifact family])
  obtain P where package: "native_package_at E u r P"
    using checked by (simp only: package_admission_on_values[OF source]) blast
  have root_family: "native_root_family_at E u r {}"
    using ef artifact family by (auto simp: native_root_family_at_def single_valued_def rel_dom_def)
  have roots: "native_package_roots E u r={}"
    by (simp only: native_package_roots_from_family[OF root_family]; simp add: rel_ran_def)
  have sites: "native_package_sites E u r={}"
    by (simp add: native_package_sites_def roots native_definition_sites_def)
  have endpoints: "family_endpoints E u r={}"
    by (simp only: family_endpoints_from_read[OF ef artifact family]; simp add: rel_ran_def)
  have demands: "native_package_demands E u r={}"
    by (simp add: native_package_demands_def native_root_requests_def endpoints sites requested_slots_def)
  have member: "u\<in>environment_uses E"
    using artifact by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  have criterion: "(122,package_context_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    rel_dom (environment_bindings E)\<subseteq>{} \<and>
      environment_uses E\<subseteq>{u}\<union>rel_ran (environment_bindings E)"
    by (simp only: package_retention_admission_at_read[OF source package]
      native_package_closed_coverage[OF package])
      (simp add: demands native_package_sources_def sites)
  have only: "environment_uses E\<subseteq>{u} \<longleftrightarrow> environment_uses E={u}"
    using member by auto
  show ?thesis by (cases "environment_bindings E={}") (simp_all add: criterion only)
qed

section \<open>The admitted body of a complete program quotation\<close>

theorem package_retention_at_quotation:
  assumes quote: "complete_data_quoted_at C q t"
  shows "(122,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (\<exists>E u r P. program_scope_quoted_at C q E u r P)"
proof
  assume checked: "(122,t)\<in>positive_meaning package_retention_admission_system"
  obtain E u r P where fields: "site_value_presents E u r t" "closed_native_package_at E u r P"
    using package_retention_admission_sound[OF checked] by blast
  show "\<exists>E u r P. program_scope_quoted_at C q E u r P"
    using fields quote by (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)
next
  assume "\<exists>E u r P. program_scope_quoted_at C q E u r P"
  then obtain E u r P s where fields: "site_value_presents E u r s" "closed_native_package_at E u r P"
    "complete_data_quoted_at C q s" by (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)
  have same: "s=t" by (rule complete_data_quotation_unique[OF fields(3) quote])
  show "(122,t)\<in>positive_meaning package_retention_admission_system"
    by (simp only: same[symmetric]) (rule package_retention_admission_complete[OF fields(1,2)])
qed

section \<open>Five fixed native entries precede all future submitted scopes\<close>

abbreviation package_retention_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "package_retention_operation_result d t \<equiv>
    (d=118 \<and> package_source_reading_result t) \<or>
    (d=119 \<and> package_slot_reading_result t) \<or>
    (d=120 \<and> package_source_list_result t) \<or>
    (d=121 \<and> package_slot_list_result t) \<or>
    (d=122 \<and> package_retention_admission_result t)"

lemma package_retention_operation_components:
  "(118,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (118,t)\<in>positive_meaning package_source_reading_system"
  "(119,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    (119,t)\<in>positive_meaning package_slot_reading_system"
  using package_retention_admission_old_meaning[of 118 t] package_lists_previous_meaning[of 118 t]
    package_slot_reading_old_meaning[of 118 t]
    package_retention_admission_old_meaning[of 119 t] package_lists_previous_meaning[of 119 t] by auto

lemma package_retention_operations_exact:
  assumes "d\<in>{118,119,120,121,122}"
  shows "(d,t)\<in>positive_meaning package_retention_admission_system \<longleftrightarrow>
    package_retention_operation_result d t"
proof -
  consider "d=118" | "d=119" | "d=120" | "d=121" | "d=122" using assms by auto
  then show ?thesis by cases
    (simp_all add: package_retention_operation_components package_retention_admission_components
      package_source_reading_exact package_slot_reading_exact package_source_list_exact
      package_slot_list_exact package_retention_admission_exact)
qed

theorem native_package_retention_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {118::nat,119,120,121,122} \<and>
    (\<forall>d\<in>{118,119,120,121,122}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> package_retention_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions package_retention_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions package_retention_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed package_retention_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning package_retention_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF package_retention_admission_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have sites: "inj_on g {118,119,120,121,122}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {118,119,120,121,122}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{118,119,120,121,122}" and tf: "term_formed t"
    have member: "d\<in>system_definitions package_retention_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed package_retention_admission_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning package_retention_admission_system"
      "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R"
      "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
      using future[rule_format, OF member tf] by (elim exE conjE) (rule that; assumption)
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> package_retention_operation_result d t) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member package_retention_operations_exact[OF selected] in
          \<open>auto simp: package_retention_admission_call\<close>)
  qed
qed

text \<open>
  Five ordinary premises admit the actual package, project both complete
  stored key lists, and check every source and binding. The result is exactly
  the existing site value with a closed native package. Canonical restriction
  always supplies an admitted value; different complete presentations have
  identical admission. An empty root family retains exactly its one whole
  source artifact and no bindings.

  The five entries share one fixed native package before all future inputs.
  Future applications preserve its exact minimal program environment and all
  prior artifacts and outgoing bindings. Package formation and retention do
  not require an application, a proof graph, or the truth of any call.

  For an independently established complete data quotation, body admission
  is exactly the existing program-scope quotation relation. Admission of that
  whole-artifact quotation itself, higher generation and authority readers,
  complete transition-material admission, and genesis remain separate.
\<close>

end
