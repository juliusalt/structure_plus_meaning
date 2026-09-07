theory Factor_Package_Membership
  imports Factor_Definition_Edge_Reading
begin

section \<open>One package context accompanies every selected subject\<close>

abbreviation package_subject_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "package_subject_argument e u r x \<equiv> Pair_Term (source_root_argument e u r) x"

abbreviation package_subject_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "package_subject_pattern e u r x \<equiv> Pattern_Pair (source_root_pattern e u r) x"

abbreviation package_membership_result :: "factor_term \<Rightarrow> bool" where
  "package_membership_result z \<equiv> \<exists>E e u r d P.
    z=package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d) \<and>
    environment_value_presents E e \<and> native_package_at E u r P \<and> d\<in>system_definitions P"

definition package_membership_root_schema :: "(nat,nat,nat) factor_schema" where
  "package_membership_root_schema=data_rule (package_subject_pattern data_x data_y data_z data_w)
    {(0,80,source_root_pattern data_x data_y data_z),
     (1,79,citation_observation_pattern data_x data_y data_z (Pattern_Variable 4)),
     (2,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)))}"

definition package_membership_step_schema :: "(nat,nat,nat) factor_schema" where
  "package_membership_step_schema=data_rule (package_subject_pattern data_x data_y data_z data_w)
    {(0,83,package_subject_pattern data_x data_y data_z (Pattern_Variable 4)),
     (1,82,Pattern_Pair data_x (Pattern_Pair (Pattern_Variable 4) data_w))}"

definition package_membership_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "package_membership_clauses={(0,package_membership_root_schema),(1,package_membership_step_schema)}"

definition package_membership_system :: "(nat,nat,nat,nat) schema_system" where
  "package_membership_system=add_view_definition definition_edge_reading_system 83 data_x package_membership_clauses"

lemma package_membership_system_formed [simp]: "schema_system_formed package_membership_system"
  unfolding package_membership_system_def
  by (rule add_recursive_definition_formed[OF definition_edge_reading_system_formed])
    (auto simp: package_membership_clauses_def package_membership_root_schema_def package_membership_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_membership_definitions [simp]:
  "system_definitions package_membership_system=insert 83 (system_definitions definition_edge_reading_system)"
  by (simp add: package_membership_system_def)

lemma package_membership_call:
  "schema_call_formed package_membership_system d t \<longleftrightarrow>
    d\<in>system_definitions package_membership_system \<and> term_formed t"
  using added_variable_calls[OF definition_edge_reading_system_formed
    package_membership_system_formed[unfolded package_membership_system_def] definition_edge_reading_call]
  by (simp only: package_membership_system_def[symmetric])

lemma package_membership_old_meaning:
  assumes "d\<in>system_definitions definition_edge_reading_system"
  shows "(d,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_edge_reading_system"
  using added_definition_preserves_old(2)[OF definition_edge_reading_system_formed
    package_membership_system_formed[unfolded package_membership_system_def], of d t] assms
  by (auto simp: package_membership_system_def)

lemma package_membership_clause [simp]:
  "((83,c),S)\<in>system_clauses package_membership_system \<longleftrightarrow> (c,S)\<in>package_membership_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_edge_reading_system \<Longrightarrow>
    d\<in>system_definitions definition_edge_reading_system" for d c S
    using definition_edge_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((83,c),S)\<notin>system_clauses definition_edge_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_membership_system_def)
qed

lemma package_membership_previous_meaning:
  assumes "d\<in>system_definitions package_admission_system"
  shows "(d,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_admission_system"
  using package_membership_old_meaning[of d t] definition_edge_reading_previous_meaning[OF assms, of t] assms by auto

lemma package_membership_components:
  "(80,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(79,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (79,t)\<in>positive_meaning root_family_reading_system"
  "(82,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(5,t)\<in>positive_meaning package_membership_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  using package_membership_previous_meaning[of 80 t] package_membership_previous_meaning[of 79 t]
    package_admission_components(1)[of t] package_membership_old_meaning[of 82 t]
    package_membership_old_meaning[of 5 t] definition_edge_reading_components(5)[of t] by auto

lemma package_membership_root:
  assumes package: "(80,source_root_argument e u r)\<in>positive_meaning package_admission_system"
    and roots: "(79,citation_observation_argument e u r ds)\<in>positive_meaning root_family_reading_system"
    and selected: "(5,Pair_Term d (Pair_Term ds rest))\<in>positive_meaning bag_comparison_system"
  shows "(83,package_subject_argument e u r d)\<in>positive_meaning package_membership_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed d" "term_formed ds" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF package]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then d else if n=4 then ds else rest"
  have result: "(83,evaluate_pattern ?h (schema_conclusion package_membership_root_schema))\<in>positive_meaning package_membership_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: package_membership_clauses_def package_membership_root_schema_def
        schema_variables_def package_membership_call package_membership_components\<close>)
  show ?thesis using result by (simp add: package_membership_root_schema_def)
qed

lemma package_membership_step:
  assumes reached: "(83,package_subject_argument e u r a)\<in>positive_meaning package_membership_system"
    and edge: "(82,Pair_Term e (Pair_Term a b))\<in>positive_meaning definition_edge_reading_system"
  shows "(83,package_subject_argument e u r b)\<in>positive_meaning package_membership_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed a" "term_formed b"
    using schema_call_formed_target[OF positive_meaning_formed[OF reached]]
      schema_call_formed_target[OF positive_meaning_formed[OF edge]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then b else a"
  have result: "(83,evaluate_pattern ?h (schema_conclusion package_membership_step_schema))\<in>positive_meaning package_membership_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use formed assms in \<open>auto simp: package_membership_clauses_def package_membership_step_schema_def
        schema_variables_def package_membership_call package_membership_components\<close>)
  show ?thesis using result by (simp add: package_membership_step_schema_def)
qed

theorem package_membership_sound:
  assumes holds: "(83,z)\<in>positive_meaning package_membership_system"
  shows "package_membership_result z"
proof -
  have invariant: "(83::nat)=83 \<longrightarrow> package_membership_result z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=83 \<longrightarrow> package_membership_result t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses package_membership_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed package_membership_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning package_membership_system \<and>
        (e=83 \<longrightarrow> package_membership_result (evaluate_pattern h p))"
    show "d=83 \<longrightarrow> package_membership_result (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=83"
      then have cases: "S=package_membership_root_schema \<or> S=package_membership_step_schema"
        using clause by (auto simp: package_membership_clauses_def)
      then show "package_membership_result (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=package_membership_root_schema"
        have calls: "(80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system"
          "(79,citation_observation_argument (h 0) (h 1) (h 2) (h 4))\<in>positive_meaning root_family_reading_system"
          "(5,Pair_Term (h 3) (Pair_Term (h 4) (h 5)))\<in>positive_meaning bag_comparison_system"
          using support by (auto simp: schema package_membership_root_schema_def package_membership_components)
        obtain E u r P where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          "native_package_at E u r P"
          using calls(1) by (simp only: package_admission_exact factor_term.inject) blast
        obtain ds where roots_value: "h 4=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
          using calls(2) by (simp only: source(2,3) root_family_reading_at_source[OF source(1)]
            inj_eq[OF use_data_term_injective] factor_term.inject) blast
        have roots: "(79,citation_observation_argument (h 0) (use_data_term u) (Payload_Term r)
            (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
          using calls(2) by (simp only: source(2,3) roots_value)
        obtain Q where raw: "native_root_family_at E u r Q" "rel_ran Q=set ds"
          using root_family_reading_recovers[OF source(1) roots] by blast
        have selected: "selected_data_member (h 3) (h 4)" using calls(3) by blast
        have member: "h 3\<in>set (map (\<lambda>d. definition_site_value d) ds)"
          using selected by (simp only: roots_value selected_data_member_exact data_list_term_injective) auto
        then obtain a where target: "h 3=definition_site_value a" "a\<in>set ds" by auto
        have root: "a\<in>rel_ran Q" using target(2) raw(2) by simp
        have reached: "a\<in>native_definition_sites E (rel_ran Q)" using native_definition_roots[of "rel_ran Q" E] root by blast
        have definitions: "system_definitions P=native_definition_sites E (rel_ran Q)"
          by (rule native_package_complete_roots[OF source(4) raw(1)])
        have inside: "a\<in>system_definitions P" using reached definitions by simp
        show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u],
          rule exI[of _ r], rule exI[of _ a], rule exI[of _ P])
          (use source target inside in \<open>simp add: schema package_membership_root_schema_def\<close>)
      next
        assume schema: "S=package_membership_step_schema"
        have earlier: "package_membership_result (package_subject_argument (h 0) (h 1) (h 2) (h 4))"
          and edge_call: "(82,Pair_Term (h 0) (Pair_Term (h 4) (h 3)))\<in>positive_meaning definition_edge_reading_system"
          using support by (auto simp: schema package_membership_step_schema_def package_membership_components)
        obtain E u r a P where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
          "h 4=definition_site_value a" "native_package_at E u r P" "a\<in>system_definitions P"
          using earlier by (simp only: factor_term.inject) blast
        obtain b where target: "h 3=definition_site_value b" "(a,b)\<in>native_definition_edges E"
          using edge_call by (simp only: source(4) definition_edge_reading_at_source[OF source(1)] definition_site_value_eq) blast
        obtain Q where roots: "native_root_family_at E u r Q" using source(5) by (auto simp: native_package_at_def)
        have definitions: "system_definitions P=native_definition_sites E (rel_ran Q)"
          by (rule native_package_complete_roots[OF source(5) roots])
        have prior: "a\<in>native_definition_sites E (rel_ran Q)" using source(6) definitions by simp
        have reached: "b\<in>native_definition_sites E (rel_ran Q)" by (rule native_definition_step[OF prior target(2)])
        have inside: "b\<in>system_definitions P" using reached definitions by simp
        show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u],
          rule exI[of _ r], rule exI[of _ b], rule exI[of _ P])
          (use source target inside in \<open>simp add: schema package_membership_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem package_membership_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P" and member: "d\<in>system_definitions P"
  shows "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d))
    \<in>positive_meaning package_membership_system"
proof -
  obtain Q where roots: "native_root_family_at E u r Q" using package by (auto simp: native_package_at_def)
  have definitions: "system_definitions P=native_definition_sites E (rel_ran Q)"
    by (rule native_package_complete_roots[OF package roots])
  obtain a where start: "a\<in>rel_ran Q" and path: "(a,d)\<in>(native_definition_edges E)\<^sup>*"
    using member definitions by (auto simp: native_definition_sites_def)
  have admitted: "(80,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source package])
  obtain ds where reading: "(79,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds)))\<in>positive_meaning root_family_reading_system"
    and range: "rel_ran Q=set ds" using root_family_reading_total[OF source roots] by blast
  have data: "data_elements (map (\<lambda>d. definition_site_value d) ds)"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]] by (auto simp: data_list_term_formed)
  have selected: "selected_data_member (definition_site_value a) (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
    by (simp only: selected_data_member_exact data_list_term_injective) (use data start range in auto)
  obtain rest where selection: "(5,Pair_Term (definition_site_value a)
      (Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds)) rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have base: "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value a))
      \<in>positive_meaning package_membership_system"
    by (rule package_membership_root[OF admitted reading selection])
  have advance: "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value y))
      \<in>positive_meaning package_membership_system"
    if prior: "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value x))
      \<in>positive_meaning package_membership_system" and edge: "(x,y)\<in>native_definition_edges E" for x y
    by (rule package_membership_step[OF prior definition_edge_reading_complete[OF source edge]])
  show ?thesis using path by (induction rule: rtrancl_induct) (use base advance in auto)
qed

theorem package_membership_exact:
  "(83,z)\<in>positive_meaning package_membership_system \<longleftrightarrow> package_membership_result z"
  using package_membership_sound package_membership_complete by blast

corollary package_membership_at_source:
  assumes source: "environment_value_presents E e"
  shows "(83,package_subject_argument e u r x)\<in>positive_meaning package_membership_system \<longleftrightarrow>
    (\<exists>v a d P. u=use_data_term v \<and> r=Payload_Term a \<and> x=definition_site_value d \<and>
      native_package_at E v a P \<and> d\<in>system_definitions P)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: package_membership_exact factor_term.inject) (use source unique in blast)
qed

corollary package_membership_on_values:
  assumes source: "environment_value_presents E e"
  shows "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning package_membership_system \<longleftrightarrow> (\<exists>P. native_package_at E u r P \<and> d\<in>system_definitions P)"
  by (simp only: package_membership_at_source[OF source] inj_eq[OF use_data_term_injective]
    factor_term.inject definition_site_value_eq) blast

corollary package_membership_at_package:
  assumes source: "environment_value_presents E e" and package: "native_package_at E u r P"
  shows "(83,package_subject_argument e (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning package_membership_system \<longleftrightarrow> d\<in>system_definitions P"
proof -
  have unique: "Q=P" if "native_package_at E u r Q" for Q
    by (rule native_package_unique[OF that package])
  show ?thesis by (simp only: package_membership_on_values[OF source]) (use package unique in blast)
qed

corollary package_membership_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(83,package_subject_argument e u r x)\<in>positive_meaning package_membership_system \<longleftrightarrow>
    (83,package_subject_argument f u r x)\<in>positive_meaning package_membership_system"
  by (simp only: package_membership_at_source[OF assms(1)] package_membership_at_source[OF assms(2)])

text \<open>
  The base clause admits the actual package and selects an actual root
  destination. The recursive clause follows one actual definition edge.
  Induction over positive meaning and induction over raw finite paths prove
  that these clauses reach precisely the existing package's definitions.

  Package formation is retained by every recursive step, including cycles.
  No hidden closure bound selects members, and an empty package has no
  members. The package context is carried unchanged. Its grouping is shared
  by the following call and list entries and adds no native grammar form.
\<close>

end
