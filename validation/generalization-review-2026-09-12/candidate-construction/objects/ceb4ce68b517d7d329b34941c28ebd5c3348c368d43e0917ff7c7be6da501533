theory Factor_Package_Source_Reading
  imports Factor_Scope_Admission Factor_Program_Scopes
begin

section \<open>Sources required by one actual package scope\<close>

abbreviation package_context_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "package_context_term e u r \<equiv> Pair_Term e (Pair_Term u r)"

abbreviation package_context_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "package_context_pattern e u r \<equiv> Pattern_Pair e (Pattern_Pair u r)"

lemma package_context_presents:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
  shows "site_value_presents E u r (package_context_term e (use_data_term u) (Payload_Term r))"
  using source native_package_root_position[OF package]
  by (auto simp: site_value_presents_def site_data_term_def)

lemma package_context_formed:
  assumes "environment_value_presents E e" "native_package_at E u r P"
  shows "term_formed (package_context_term e (use_data_term u) (Payload_Term r))"
  using site_value_presents_formed[OF package_context_presents[OF assms]] by blast

abbreviation package_source_candidates where
  "package_source_candidates E pu pr v \<equiv>
    (pu=use_data_term v \<and> (\<exists>R. artifact_at E v R)) \<or>
    (\<exists>u r a P. pu=use_data_term u \<and> pr=Payload_Term r \<and>
      native_package_at E u r P \<and> (v,a)\<in>system_definitions P) \<or>
    v\<in>rel_ran (environment_bindings E)"

abbreviation package_source_reading_result :: "factor_term \<Rightarrow> bool" where
  "package_source_reading_result z \<equiv> \<exists>E e pu pr v.
    z=Pair_Term (package_context_term e pu pr) (use_data_term v) \<and>
    environment_value_presents E e \<and> term_formed (package_context_term e pu pr) \<and>
    package_source_candidates E pu pr v"

abbreviation package_source_observed where
  "package_source_observed e pu pr x \<equiv>
    (x=pu \<and> (\<exists>a. (37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system)) \<or>
    (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term x a))\<in>positive_meaning package_membership_system) \<or>
    (\<exists>u k. (38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system)"

definition package_root_source_schema :: "(nat,nat,nat) factor_schema" where
  "package_root_source_schema=data_rule
    (Pattern_Pair (package_context_pattern data_x data_y data_z) data_y)
    {(0,37,artifact_lookup_pattern data_x data_y data_w)}"

definition package_definition_source_schema :: "(nat,nat,nat) factor_schema" where
  "package_definition_source_schema=data_rule
    (Pattern_Pair (package_context_pattern data_x data_y data_z) data_w)
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4)))}"

definition package_binding_target_schema :: "(nat,nat,nat) factor_schema" where
  "package_binding_target_schema=data_rule
    (Pattern_Pair (package_context_pattern data_x data_y data_z) data_w)
    {(0,38,binding_lookup_pattern data_x (Pattern_Variable 4) (Pattern_Variable 5) data_w)}"

definition package_source_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "package_source_reading_clauses={(0,package_root_source_schema),
    (1,package_definition_source_schema),(2,package_binding_target_schema)}"

definition package_source_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "package_source_reading_system=add_view_definition scope_forwarding_system 118 data_x package_source_reading_clauses"

lemma package_source_reading_system_formed [simp]: "schema_system_formed package_source_reading_system"
  unfolding package_source_reading_system_def
  by (rule add_recursive_definition_formed[OF scope_forwarding_system_formed])
    (auto simp: package_source_reading_clauses_def package_root_source_schema_def
      package_definition_source_schema_def package_binding_target_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_source_reading_definitions [simp]:
  "system_definitions package_source_reading_system=insert 118 (system_definitions scope_forwarding_system)"
  by (simp add: package_source_reading_system_def)

lemma package_source_reading_call:
  "schema_call_formed package_source_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions package_source_reading_system \<and> term_formed t"
  using added_variable_calls[OF scope_forwarding_system_formed
    package_source_reading_system_formed[unfolded package_source_reading_system_def] scope_forwarding_call]
  by (simp only: package_source_reading_system_def[symmetric])

lemma package_source_reading_old_meaning:
  assumes "d\<in>system_definitions scope_forwarding_system"
  shows "(d,t)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning scope_forwarding_system"
  using added_definition_preserves_old(2)[OF scope_forwarding_system_formed
    package_source_reading_system_formed[unfolded package_source_reading_system_def], of d t] assms
  by (auto simp: package_source_reading_system_def)

lemma package_source_reading_clause [simp]:
  "((118,c),S)\<in>system_clauses package_source_reading_system \<longleftrightarrow> (c,S)\<in>package_source_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses scope_forwarding_system \<Longrightarrow>
    d\<in>system_definitions scope_forwarding_system" for d c S
    using scope_forwarding_system_formed unfolding schema_system_formed_def by blast
  have absent: "((118,c),S)\<notin>system_clauses scope_forwarding_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_source_reading_system_def)
qed

lemma package_source_reading_replay_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_slot_reading_system"
  using package_source_reading_old_meaning[of d t] scope_forwarding_old_meaning[of d t]
    native_positive_admission_previous_meaning[of d t] replay_admission_old_meaning[of d t]
    retention_admission_slot_meaning[OF assms, of t] assms by auto

lemma package_source_reading_components:
  "(37,t)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(83,t)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(38,t)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (38,t)\<in>positive_meaning binding_lookup_system"
  using package_source_reading_replay_meaning[of 37 t] replay_slot_reading_components(1)[of t]
    package_source_reading_replay_meaning[of 83 t] replay_slot_reading_components(5)[of t]
    package_source_reading_replay_meaning[of 38 t] replay_slot_reading_old_meaning[of 38 t]
    replay_source_reading_components(4)[of t] by auto

lemma package_root_source_step:
  assumes formed: "term_formed (package_context_term e pu pr)"
    and read: "(37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system"
  shows "(118,Pair_Term (package_context_term e pu pr) pu)\<in>positive_meaning package_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else a"
  have result: "(118,evaluate_pattern ?h (schema_conclusion package_root_source_schema))
    \<in>positive_meaning package_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: package_source_reading_clauses_def package_root_source_schema_def schema_variables_def
          package_source_reading_call package_source_reading_components\<close>)
  show ?thesis using result by (simp add: package_root_source_schema_def)
qed

lemma package_definition_source_step:
  assumes formed: "term_formed (package_context_term e pu pr)"
    and read: "(83,package_subject_argument e pu pr (Pair_Term v a))\<in>positive_meaning package_membership_system"
  shows "(118,Pair_Term (package_context_term e pu pr) v)\<in>positive_meaning package_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then v else a"
  have result: "(118,evaluate_pattern ?h (schema_conclusion package_definition_source_schema))
    \<in>positive_meaning package_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: package_source_reading_clauses_def package_definition_source_schema_def schema_variables_def
          package_source_reading_call package_source_reading_components\<close>)
  show ?thesis using result by (simp add: package_definition_source_schema_def)
qed

lemma package_binding_target_step:
  assumes formed: "term_formed (package_context_term e pu pr)"
    and read: "(38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system"
  shows "(118,Pair_Term (package_context_term e pu pr) v)\<in>positive_meaning package_source_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then v else if j=4 then u else k"
  have result: "(118,evaluate_pattern ?h (schema_conclusion package_binding_target_schema))
    \<in>positive_meaning package_source_reading_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read]] in
        \<open>auto simp: package_source_reading_clauses_def package_binding_target_schema_def schema_variables_def
          package_source_reading_call package_source_reading_components\<close>)
  show ?thesis using result by (simp add: package_binding_target_schema_def)
qed

lemma package_source_reading_fields:
  "(118,z)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (\<exists>e pu pr x. z=Pair_Term (package_context_term e pu pr) x \<and>
      term_formed (package_context_term e pu pr) \<and> package_source_observed e pu pr x)"
proof
  assume holds: "(118,z)\<in>positive_meaning package_source_reading_system"
  have ordinary: "schema_material_premises S={}"
    if "((118,c),S)\<in>system_clauses package_source_reading_system" for c S
    using that by (auto simp: package_source_reading_clauses_def package_root_source_schema_def
      package_definition_source_schema_def package_binding_target_schema_def)
  have valuation: "(118,z)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (\<exists>c S f. ((118,c),S)\<in>system_clauses package_source_reading_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed package_source_reading_system 118 z \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning package_source_reading_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((118,c),S)\<in>system_clauses package_source_reading_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning package_source_reading_system"
    using iffD1[OF valuation holds] by blast
  show "\<exists>e pu pr x. z=Pair_Term (package_context_term e pu pr) x \<and>
    term_formed (package_context_term e pu pr) \<and> package_source_observed e pu pr x"
    using clause assignment shape support by (auto simp: package_source_reading_clauses_def
      package_root_source_schema_def package_definition_source_schema_def package_binding_target_schema_def
      schema_variables_def package_source_reading_components)
next
  assume "\<exists>e pu pr x. z=Pair_Term (package_context_term e pu pr) x \<and>
    term_formed (package_context_term e pu pr) \<and> package_source_observed e pu pr x"
  then show "(118,z)\<in>positive_meaning package_source_reading_system"
    by (auto intro: package_root_source_step package_definition_source_step package_binding_target_step)
qed

lemma package_source_observed_environment:
  assumes "package_source_observed e pu pr x"
  shows "\<exists>E. environment_value_presents E e"
  using assms by (auto simp: artifact_lookup_exact package_membership_exact binding_lookup_exact)

lemma package_source_observed_at_source:
  assumes source: "environment_value_presents E e"
  shows "package_source_observed e pu pr x \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> package_source_candidates E pu pr v)"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have material: "\<exists>a. artifact_value_presents R a" if "artifact_at E u R" for u R
    by (rule artifact_value_presents_total) (use ef that in \<open>auto simp: environment_formed_def\<close>)
  have lookup: "(\<exists>a. (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system) \<longleftrightarrow>
    (\<exists>v R. u=use_data_term v \<and> artifact_at E v R)" for u
    by (simp only: artifact_lookup_at_source[OF source]) (use material in blast)
  show ?thesis
    by (simp only: lookup package_membership_at_source[OF source] binding_lookup_at_source[OF source]
      site_data_term_def factor_term.inject)
      (auto simp: rel_ran_def binds_slot_def)
qed

theorem package_source_reading_exact:
  "(118,z)\<in>positive_meaning package_source_reading_system \<longleftrightarrow> package_source_reading_result z"
proof
  assume holds: "(118,z)\<in>positive_meaning package_source_reading_system"
  obtain e pu pr x where parts: "z=Pair_Term (package_context_term e pu pr) x"
    "term_formed (package_context_term e pu pr)" "package_source_observed e pu pr x"
    using holds by (simp only: package_source_reading_fields) blast
  obtain E where source: "environment_value_presents E e"
    using package_source_observed_environment[OF parts(3)] by blast
  obtain v where selected: "x=use_data_term v" "package_source_candidates E pu pr v"
    using parts(3) by (simp only: package_source_observed_at_source[OF source]) blast
  show "package_source_reading_result z" using parts(1,2) source selected by blast
next
  assume "package_source_reading_result z"
  then obtain E e pu pr v where parts: "z=Pair_Term (package_context_term e pu pr) (use_data_term v)"
    "environment_value_presents E e" "term_formed (package_context_term e pu pr)" "package_source_candidates E pu pr v"
    by blast
  have observed: "package_source_observed e pu pr (use_data_term v)"
    by (simp only: package_source_observed_at_source[OF parts(2)]) (use parts(4) in blast)
  show "(118,z)\<in>positive_meaning package_source_reading_system"
    by (simp only: package_source_reading_fields) (use parts(1,3) observed in blast)
qed

corollary package_source_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(118,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    term_formed (package_context_term e pu pr) \<and>
      (\<exists>v. x=use_data_term v \<and> package_source_candidates E pu pr v)"
proof -
  have fields: "(118,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    term_formed (package_context_term e pu pr) \<and> package_source_observed e pu pr x"
    by (simp only: package_source_reading_fields factor_term.inject; blast)
  show ?thesis by (simp only: fields package_source_observed_at_source[OF source])
qed

lemma package_source_candidates_at_read:
  assumes package: "native_package_at E pu pr P"
  shows "package_source_candidates E (use_data_term pu) (Payload_Term pr) v \<longleftrightarrow>
    v\<in>native_package_sources E pu pr\<union>rel_ran (environment_bindings E)"
proof -
  have root: "\<exists>R. artifact_at E pu R"
    using package by (auto simp: native_package_at_def native_root_family_at_def)
  have definitions: "(\<exists>Q. native_package_at E pu pr Q \<and> (v,a)\<in>system_definitions Q) \<longleftrightarrow>
    (v,a)\<in>system_definitions P" for a
    using package native_package_unique[OF _ package] by blast
  have projection: "v\<in>image fst A \<longleftrightarrow> (\<exists>a. (v,a)\<in>A)" for A by force
  show ?thesis
    using root by (auto simp: inj_eq[OF use_data_term_injective] definitions native_package_sources_def
      native_package_projection(3)[OF package, symmetric] projection)
qed

corollary package_source_reading_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(118,Pair_Term (package_context_term e (use_data_term pu) (Payload_Term pr)) x)
      \<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> v\<in>native_package_sources E pu pr\<union>rel_ran (environment_bindings E))"
  by (simp only: package_source_reading_at_source[OF source] package_context_formed[OF source package]
    package_source_candidates_at_read[OF package]; simp)

corollary package_source_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(118,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_source_reading_system \<longleftrightarrow>
    (118,Pair_Term (package_context_term f pu pr) x)\<in>positive_meaning package_source_reading_system"
  using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)]
  by (simp only: package_source_reading_at_source[OF assms(1)] package_source_reading_at_source[OF assms(2)]) auto

text \<open>
  The context is the existing environment-and-site value. Three ordinary
  clauses identify its root use, a reached definition use, or an actual
  binding target. A whole literal artifact can be needed without its outgoing
  bindings being read. The separate slot check accounts for those bindings.

  Each branch checks its own role. The enclosing retention entry admits the
  complete actual package even when the stored key lists are empty.
  The source-program coordinate 118 is a fresh local coordinate; the separately
  configured interpreter program's entry 117 is not part of this generic base.
\<close>

end
