theory Factor_Package_Slot_Reading
  imports Factor_Package_Source_Reading
begin

section \<open>Slots read by the actual package grammar\<close>

abbreviation package_slot_observed where
  "package_slot_observed e pu pr u k \<equiv>
    (u=pu \<and> replay_root_slot_observed e pu pr k) \<or>
    (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term u a))\<in>positive_meaning package_membership_system \<and>
      (105,citation_observation_argument e u a k)\<in>positive_meaning definition_slot_reading_system)"

abbreviation package_slot_candidates where
  "package_slot_candidates E pu pr u k \<equiv>
    (\<exists>v r. pu=use_data_term v \<and> pr=Payload_Term r \<and> u=v \<and>
      (u,k)\<in>requested_slots E (native_root_requests E v r)) \<or>
    (\<exists>v r a P. pu=use_data_term v \<and> pr=Payload_Term r \<and> native_package_at E v r P \<and>
      (u,a)\<in>system_definitions P \<and> k\<in>native_definition_slots E u a)"

abbreviation package_slot_reading_result :: "factor_term \<Rightarrow> bool" where
  "package_slot_reading_result z \<equiv> \<exists>E e pu pr u k.
    z=Pair_Term (package_context_term e pu pr) (Pair_Term (use_data_term u) (Payload_Term k)) \<and>
    environment_value_presents E e \<and> term_formed (package_context_term e pu pr) \<and>
    package_slot_candidates E pu pr u k"

definition package_root_slot_schema :: "(nat,nat,nat) factor_schema" where
  "package_root_slot_schema=data_rule
    (Pattern_Pair (package_context_pattern data_x data_y data_z) (Pattern_Pair data_y data_w))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (1,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z) (Pattern_Variable 5)),
     (2,5,Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))
       (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8))),
     (3,42,citation_reading_pattern data_x data_y (Pattern_Variable 7)
       (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)) (Pattern_Variable 11)),
     (4,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12)))}"

definition package_definition_slot_schema :: "(nat,nat,nat) factor_schema" where
  "package_definition_slot_schema=data_rule
    (Pattern_Pair (package_context_pattern data_x data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 5))),
     (1,105,citation_observation_pattern data_x data_w (Pattern_Variable 5) (Pattern_Variable 4))}"

definition package_slot_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "package_slot_reading_clauses={(0,package_root_slot_schema),(1,package_definition_slot_schema)}"

definition package_slot_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "package_slot_reading_system=add_view_definition package_source_reading_system 119 data_x package_slot_reading_clauses"

lemma package_slot_reading_system_formed [simp]: "schema_system_formed package_slot_reading_system"
  unfolding package_slot_reading_system_def
  by (rule add_recursive_definition_formed[OF package_source_reading_system_formed])
    (auto simp: package_slot_reading_clauses_def package_root_slot_schema_def package_definition_slot_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_slot_reading_definitions [simp]:
  "system_definitions package_slot_reading_system=insert 119 (system_definitions package_source_reading_system)"
  by (simp add: package_slot_reading_system_def)

lemma package_slot_reading_call:
  "schema_call_formed package_slot_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions package_slot_reading_system \<and> term_formed t"
  using added_variable_calls[OF package_source_reading_system_formed
    package_slot_reading_system_formed[unfolded package_slot_reading_system_def] package_source_reading_call]
  by (simp only: package_slot_reading_system_def[symmetric])

lemma package_slot_reading_old_meaning:
  assumes "d\<in>system_definitions package_source_reading_system"
  shows "(d,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_source_reading_system"
  using added_definition_preserves_old(2)[OF package_source_reading_system_formed
    package_slot_reading_system_formed[unfolded package_slot_reading_system_def], of d t] assms
  by (auto simp: package_slot_reading_system_def)

lemma package_slot_reading_clause [simp]:
  "((119,c),S)\<in>system_clauses package_slot_reading_system \<longleftrightarrow> (c,S)\<in>package_slot_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_source_reading_system \<Longrightarrow>
    d\<in>system_definitions package_source_reading_system" for d c S
    using package_source_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((119,c),S)\<notin>system_clauses package_source_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_slot_reading_system_def)
qed

lemma package_slot_reading_replay_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_slot_reading_system"
  using package_slot_reading_old_meaning[of d t]
    package_source_reading_replay_meaning[OF assms, of t] assms by auto

lemma package_slot_reading_components:
  "(37,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(32,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (32,t)\<in>positive_meaning family_admission_system"
  "(5,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (5,t)\<in>positive_meaning bag_comparison_system"
  "(42,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (42,t)\<in>positive_meaning citation_reading_system"
  "(83,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(105,t)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (105,t)\<in>positive_meaning definition_slot_reading_system"
  using package_slot_reading_replay_meaning[of 37 t] replay_slot_reading_components(1)[of t]
    package_slot_reading_replay_meaning[of 32 t] replay_slot_reading_components(2)[of t]
    package_slot_reading_replay_meaning[of 5 t] replay_slot_reading_components(3)[of t]
    package_slot_reading_replay_meaning[of 42 t] replay_slot_reading_components(4)[of t]
    package_slot_reading_replay_meaning[of 83 t] replay_slot_reading_components(5)[of t]
    package_slot_reading_replay_meaning[of 105 t] replay_slot_reading_components(6)[of t] by auto

lemma package_root_slot_step:
  assumes formed: "term_formed (package_context_term e pu pr)" and read:
    "(37,artifact_lookup_argument e pu a)\<in>positive_meaning artifact_lookup_system"
    "(32,rooted_rows_argument a pr rows)\<in>positive_meaning family_admission_system"
    "(5,Pair_Term (Pair_Term socket endpoint) (Pair_Term rows rest))\<in>positive_meaning bag_comparison_system"
    "(42,citation_reading_argument e pu endpoint (Pair_Term slots address) interior)\<in>positive_meaning citation_reading_system"
    "(5,Pair_Term k (Pair_Term slots remainder))\<in>positive_meaning bag_comparison_system"
  shows "(119,Pair_Term (package_context_term e pu pr) (Pair_Term pu k))\<in>positive_meaning package_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then k
    else if j=4 then a else if j=5 then rows else if j=6 then socket else if j=7 then endpoint
    else if j=8 then rest else if j=9 then slots else if j=10 then address else if j=11 then interior else remainder"
  have result: "(119,evaluate_pattern ?h (schema_conclusion package_root_slot_schema))
    \<in>positive_meaning package_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(4)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(5)]] in
        \<open>auto simp: package_slot_reading_clauses_def package_root_slot_schema_def schema_variables_def
          package_slot_reading_call package_slot_reading_components\<close>)
  show ?thesis using result by (simp add: package_root_slot_schema_def)
qed

lemma package_definition_slot_step:
  assumes formed: "term_formed (package_context_term e pu pr)" and read:
    "(83,package_subject_argument e pu pr (Pair_Term u a))\<in>positive_meaning package_membership_system"
    "(105,citation_observation_argument e u a k)\<in>positive_meaning definition_slot_reading_system"
  shows "(119,Pair_Term (package_context_term e pu pr) (Pair_Term u k))\<in>positive_meaning package_slot_reading_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then u else if j=4 then k else a"
  have result: "(119,evaluate_pattern ?h (schema_conclusion package_definition_slot_schema))
    \<in>positive_meaning package_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]] in
        \<open>auto simp: package_slot_reading_clauses_def package_definition_slot_schema_def schema_variables_def
          package_slot_reading_call package_slot_reading_components\<close>)
  show ?thesis using result by (simp add: package_definition_slot_schema_def)
qed

lemma package_slot_reading_fields:
  "(119,z)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (\<exists>e pu pr u k. z=Pair_Term (package_context_term e pu pr) (Pair_Term u k) \<and>
      term_formed (package_context_term e pu pr) \<and> package_slot_observed e pu pr u k)"
proof
  assume holds: "(119,z)\<in>positive_meaning package_slot_reading_system"
  have ordinary: "schema_material_premises S={}"
    if "((119,c),S)\<in>system_clauses package_slot_reading_system" for c S
    using that by (auto simp: package_slot_reading_clauses_def package_root_slot_schema_def package_definition_slot_schema_def)
  have valuation: "(119,z)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (\<exists>c S f. ((119,c),S)\<in>system_clauses package_slot_reading_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      z=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed package_slot_reading_system 119 z \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning package_slot_reading_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((119,c),S)\<in>system_clauses package_slot_reading_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning package_slot_reading_system"
    using iffD1[OF valuation holds] by blast
  consider (root) "S=package_root_slot_schema" | (defined) "S=package_definition_slot_schema"
    using clause by (auto simp: package_slot_reading_clauses_def)
  then show "\<exists>e pu pr u k. z=Pair_Term (package_context_term e pu pr) (Pair_Term u k) \<and>
    term_formed (package_context_term e pu pr) \<and> package_slot_observed e pu pr u k"
  proof cases
    case root
    have formed: "term_formed (package_context_term (h 0) (h 1) (h 2))"
      using assignment by (auto simp: root package_root_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (package_context_term (h 0) (h 1) (h 2)) (Pair_Term (h 1) (h 3))"
      using shape by (simp add: root package_root_slot_schema_def)
    have read_0: "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
      using support[rule_format, of 0 37 "artifact_lookup_pattern data_x data_y (Pattern_Variable 4)"]
      by (simp add: root package_root_slot_schema_def package_slot_reading_components)
    have read_1: "(32,rooted_rows_argument (h 4) (h 2) (h 5))\<in>positive_meaning family_admission_system"
      using support[rule_format, of 1 32 "Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z) (Pattern_Variable 5)"]
      by (simp add: root package_root_slot_schema_def package_slot_reading_components)
    have read_2: "(5,Pair_Term (Pair_Term (h 6) (h 7)) (Pair_Term (h 5) (h 8)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 2 5 "Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 8))"]
      by (simp add: root package_root_slot_schema_def package_slot_reading_components)
    have read_3: "(42,citation_reading_argument (h 0) (h 1) (h 7) (Pair_Term (h 9) (h 10)) (h 11))\<in>positive_meaning citation_reading_system"
      using support[rule_format, of 3 42 "citation_reading_pattern data_x data_y (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)) (Pattern_Variable 11)"]
      by (simp add: root package_root_slot_schema_def package_slot_reading_components)
    have read_4: "(5,Pair_Term (h 3) (Pair_Term (h 9) (h 12)))\<in>positive_meaning bag_comparison_system"
      using support[rule_format, of 4 5 "Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 12))"]
      by (simp add: root package_root_slot_schema_def package_slot_reading_components)
    have observed: "package_slot_observed (h 0) (h 1) (h 2) (h 1) (h 3)"
      using read_0 read_1 read_2 read_3 read_4 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
        rule exI[of _ "h 1"], rule exI[of _ "h 3"]) (use encoded formed observed in blast)
  next
    case defined
    have formed: "term_formed (package_context_term (h 0) (h 1) (h 2))"
      using assignment by (auto simp: defined package_definition_slot_schema_def schema_variables_def)
    have encoded: "z=Pair_Term (package_context_term (h 0) (h 1) (h 2)) (Pair_Term (h 3) (h 4))"
      using shape by (simp add: defined package_definition_slot_schema_def)
    have read_0: "(83,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 5)))\<in>positive_meaning package_membership_system"
      using support[rule_format, of 0 83 "package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 5))"]
      by (simp add: defined package_definition_slot_schema_def package_slot_reading_components)
    have read_1: "(105,citation_observation_argument (h 0) (h 3) (h 5) (h 4))\<in>positive_meaning definition_slot_reading_system"
      using support[rule_format, of 1 105 "citation_observation_pattern data_x data_w (Pattern_Variable 5) (Pattern_Variable 4)"]
      by (simp add: defined package_definition_slot_schema_def package_slot_reading_components)
    have observed: "package_slot_observed (h 0) (h 1) (h 2) (h 3) (h 4)"
      using read_0 read_1 by blast
    show ?thesis
      by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
        rule exI[of _ "h 3"], rule exI[of _ "h 4"]) (use encoded formed observed in blast)
  qed
next
  assume "\<exists>e pu pr u k. z=Pair_Term (package_context_term e pu pr) (Pair_Term u k) \<and>
    term_formed (package_context_term e pu pr) \<and> package_slot_observed e pu pr u k"
  then show "(119,z)\<in>positive_meaning package_slot_reading_system"
    by (auto intro: package_root_slot_step package_definition_slot_step)
qed

lemma package_slot_observed_environment:
  assumes "package_slot_observed e pu pr u k"
  shows "\<exists>E. environment_value_presents E e"
  using assms by (auto simp: artifact_lookup_exact package_membership_exact)

lemma package_slot_observed_at_source:
  assumes source: "environment_value_presents E e"
  shows "package_slot_observed e pu pr u k \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and> package_slot_candidates E pu pr v a)"
proof -
  have roots: "(u=pu \<and> replay_root_slot_observed e pu pr k) \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>w r. pu=use_data_term w \<and> pr=Payload_Term r \<and> v=w \<and>
        (v,a)\<in>requested_slots E (native_root_requests E w r)))"
    by (simp only: replay_root_slot_at_source[OF source]) blast
  have definitions:
    "(\<exists>b. (83,package_subject_argument e pu pr (Pair_Term u b))\<in>positive_meaning package_membership_system \<and>
      (105,citation_observation_argument e u b k)\<in>positive_meaning definition_slot_reading_system) \<longleftrightarrow>
    (\<exists>v a. u=use_data_term v \<and> k=Payload_Term a \<and>
      (\<exists>w r b P. pu=use_data_term w \<and> pr=Payload_Term r \<and> native_package_at E w r P \<and>
        (v,b)\<in>system_definitions P \<and> a\<in>native_definition_slots E v b))"
    by (simp only: package_membership_at_source[OF source] definition_slot_reading_at_source[OF source]
      site_data_term_def factor_term.inject; auto simp: inj_eq[OF use_data_term_injective]; blast)
  show ?thesis by (simp only: roots definitions conj_disj_distribL ex_disj_distrib)
qed

theorem package_slot_reading_exact:
  "(119,z)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow> package_slot_reading_result z"
proof
  assume holds: "(119,z)\<in>positive_meaning package_slot_reading_system"
  obtain e pu pr u k where parts: "z=Pair_Term (package_context_term e pu pr) (Pair_Term u k)"
    "term_formed (package_context_term e pu pr)" "package_slot_observed e pu pr u k"
    using holds by (simp only: package_slot_reading_fields) blast
  obtain E where source: "environment_value_presents E e"
    using package_slot_observed_environment[OF parts(3)] by blast
  obtain v a where selected: "u=use_data_term v" "k=Payload_Term a" "package_slot_candidates E pu pr v a"
    using parts(3) by (simp only: package_slot_observed_at_source[OF source]) blast
  show "package_slot_reading_result z" using parts(1,2) source selected by blast
next
  assume "package_slot_reading_result z"
  then obtain E e pu pr u k where parts:
    "z=Pair_Term (package_context_term e pu pr) (Pair_Term (use_data_term u) (Payload_Term k))"
    "environment_value_presents E e" "term_formed (package_context_term e pu pr)"
    "package_slot_candidates E pu pr u k" by blast
  have observed: "package_slot_observed e pu pr (use_data_term u) (Payload_Term k)"
    by (simp only: package_slot_observed_at_source[OF parts(2)]) (use parts(4) in blast)
  show "(119,z)\<in>positive_meaning package_slot_reading_system"
    by (simp only: package_slot_reading_fields) (use parts(1,3) observed in blast)
qed

corollary package_slot_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    term_formed (package_context_term e pu pr) \<and>
      (\<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and> package_slot_candidates E pu pr u k)"
proof -
  have fields: "(119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    term_formed (package_context_term e pu pr) \<and>
      (\<exists>u k. x=Pair_Term u k \<and> package_slot_observed e pu pr u k)"
    by (simp only: package_slot_reading_fields factor_term.inject; blast)
  show ?thesis by (simp only: fields package_slot_observed_at_source[OF source]; blast)
qed

lemma package_slot_candidates_at_read:
  assumes package: "native_package_at E pu pr P"
  shows "package_slot_candidates E (use_data_term pu) (Payload_Term pr) u k \<longleftrightarrow>
    (u,k)\<in>native_package_demands E pu pr"
proof -
  have definitions: "(\<exists>Q. native_package_at E pu pr Q \<and> (u,a)\<in>system_definitions Q \<and>
      k\<in>native_definition_slots E u a) \<longleftrightarrow>
    (u,a)\<in>system_definitions P \<and> k\<in>native_definition_slots E u a" for a
    using package native_package_unique[OF _ package] by blast
  have root_owner: "(u,k)\<in>requested_slots E (native_root_requests E pu pr) \<Longrightarrow> u=pu"
    by (auto simp: requested_slots_def native_root_requests_def)
  show ?thesis
    by (simp add: inj_eq[OF use_data_term_injective] definitions native_package_demands_def
      native_package_projection(3)[OF package, symmetric]) (use root_owner in blast)
qed

corollary package_slot_reading_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(119,Pair_Term (package_context_term e (use_data_term pu) (Payload_Term pr)) x)
      \<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (\<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and> (u,k)\<in>native_package_demands E pu pr)"
  by (simp only: package_slot_reading_at_source[OF source] package_context_formed[OF source package]
    package_slot_candidates_at_read[OF package]; simp)

corollary package_slot_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<longleftrightarrow>
    (119,Pair_Term (package_context_term f pu pr) x)\<in>positive_meaning package_slot_reading_system"
  using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)]
  by (simp only: package_slot_reading_at_source[OF assms(1)] package_slot_reading_at_source[OF assms(2)]) auto

text \<open>
  Two ordinary clauses inspect slots in the root citation family and in every
  reached definition. The existing citation and definition observations supply
  the exact demand set. The owning use remains part of each slot key.

  The partial helper does not claim that the selected package is formed merely
  because one root citation is readable. Complete package admission is a
  separate premise of retention, including when there are no stored bindings.
\<close>

end
