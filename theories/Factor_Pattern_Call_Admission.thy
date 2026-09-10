theory Factor_Pattern_Call_Admission
  imports Factor_Pattern_Call_Readings Factor_System_Composition
begin

section \<open>Existing substitution and package readers share their actual definitions\<close>

lemma pattern_call_package_base_agreement:
  "systems_agree_on definition_call_admission_system program_call_admission_system
    (system_definitions definition_call_admission_system)"
  by (simp add: systems_agree_on_added program_call_admission_system_def package_membership_system_def
    definition_edge_reading_system_def definition_clause_reading_system_def package_admission_system_def
    root_family_reading_system_def located_list_system_def package_closure_admission_system_def
    definition_callee_list_system_def definition_callee_inclusion_system_def schema_callee_list_system_def
    schema_callee_inclusion_system_def)

lemma pattern_call_base_agreement:
  "systems_agree_on substitution_reading_system program_call_admission_system
    (system_definitions substitution_reading_system \<inter> system_definitions program_call_admission_system)"
proof -
  have substitution: "systems_agree_on definition_call_admission_system substitution_reading_system
      (system_definitions definition_call_admission_system)"
    by (simp add: systems_agree_on_added substitution_reading_system_def reference_bindings_system_def)
  have shared: "systems_agree_on substitution_reading_system program_call_admission_system
      (system_definitions definition_call_admission_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF substitution] pattern_call_package_base_agreement])
  have overlap: "system_definitions substitution_reading_system \<inter> system_definitions program_call_admission_system=
      system_definitions definition_call_admission_system" by auto
  show ?thesis using shared by (simp only: overlap)
qed

definition pattern_call_base_system :: "(nat,nat,nat,nat) schema_system" where
  "pattern_call_base_system=system_union substitution_reading_system program_call_admission_system"

lemma pattern_call_base_formed [simp]: "schema_system_formed pattern_call_base_system"
  unfolding pattern_call_base_system_def
  by (rule system_union_agree_formed[OF substitution_reading_system_formed program_call_admission_system_formed
    pattern_call_base_agreement])

lemma pattern_call_base_definitions [simp]:
  "system_definitions pattern_call_base_system=
    system_definitions substitution_reading_system \<union> system_definitions program_call_admission_system"
  by (simp add: pattern_call_base_system_def)

lemma pattern_call_base_call:
  "schema_call_formed pattern_call_base_system d t \<longleftrightarrow>
    d\<in>system_definitions pattern_call_base_system \<and> term_formed t"
  using system_union_agree_call[OF substitution_reading_system_formed program_call_admission_system_formed
    pattern_call_base_agreement, of d t]
  by (simp only: pattern_call_base_system_def system_union_definitions substitution_reading_call
    program_call_admission_call Un_iff; blast)

lemma pattern_call_base_substitution_meaning:
  assumes "d\<in>system_definitions substitution_reading_system"
  shows "(d,t)\<in>positive_meaning pattern_call_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning substitution_reading_system"
  using system_union_agree_left_locality(2)[OF substitution_reading_system_formed program_call_admission_system_formed
    pattern_call_base_agreement assms, of t] by (simp only: pattern_call_base_system_def)

lemma pattern_call_base_package_meaning:
  assumes "d\<in>system_definitions program_call_admission_system"
  shows "(d,t)\<in>positive_meaning pattern_call_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning program_call_admission_system"
  using system_union_agree_right_locality(2)[OF substitution_reading_system_formed program_call_admission_system_formed
    pattern_call_base_agreement assms, of t] by (simp only: pattern_call_base_system_def)

section \<open>One ordinary clause checks the five complete readings\<close>

abbreviation pattern_call_reading_pattern where
  "pattern_call_reading_pattern e u r d f v q \<equiv>
    Pattern_Pair (package_subject_pattern e u r d) (Pattern_Pair f (Pattern_Pair v q))"

definition pattern_call_reading_schema :: "(nat,nat,nat) factor_schema" where
  "pattern_call_reading_schema=data_rule
    (pattern_call_reading_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,125,reference_bindings_pattern (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
     (1,56,scoped_instantiation_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)
       (Pattern_Variable 8) (Pattern_Variable 10) (Pattern_Variable 12) (Pattern_Variable 13)),
     (2,56,scoped_instantiation_pattern (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)
       (Pattern_Variable 9) (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13)),
     (3,84,package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 10))),
     (4,84,package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 11)))}"

definition pattern_call_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "pattern_call_reading_system=add_view_definition pattern_call_base_system 292 data_x {(0,pattern_call_reading_schema)}"

interpretation pattern_call_reading_view: positive_view pattern_call_base_system 292 data_x "{(0,pattern_call_reading_schema)}"
  by (rule positive_view.intro)
    (auto simp: pattern_call_reading_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma pattern_call_reading_system_formed [simp]: "schema_system_formed pattern_call_reading_system"
  using pattern_call_reading_view.formed by (simp only: pattern_call_reading_system_def)

lemma pattern_call_reading_definitions [simp]:
  "system_definitions pattern_call_reading_system=insert 292 (system_definitions pattern_call_base_system)"
  by (simp add: pattern_call_reading_system_def)

lemma pattern_call_reading_call:
  "schema_call_formed pattern_call_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions pattern_call_reading_system \<and> term_formed t"
  using added_variable_calls[OF pattern_call_base_formed
    pattern_call_reading_system_formed[unfolded pattern_call_reading_system_def] pattern_call_base_call]
  by (simp only: pattern_call_reading_system_def[symmetric])

lemma pattern_call_reading_old_meaning:
  assumes "d\<in>system_definitions pattern_call_base_system"
  shows "(d,t)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning pattern_call_base_system"
  using pattern_call_reading_view.old_meaning[OF assms] by (simp only: pattern_call_reading_system_def)

lemma pattern_call_reading_clause [simp]:
  "((292,c),S)\<in>system_clauses pattern_call_reading_system \<longleftrightarrow> c=0 \<and> S=pattern_call_reading_schema"
  using pattern_call_reading_view.no_old_clause by (auto simp: pattern_call_reading_system_def)

lemma pattern_call_reading_components:
  "(125,t)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (125,t)\<in>positive_meaning reference_bindings_system"
  "(56,t)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (56,t)\<in>positive_meaning scoped_instantiation_system"
  "(84,t)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (84,t)\<in>positive_meaning program_call_admission_system"
  using pattern_call_reading_old_meaning[of 125 t] pattern_call_base_substitution_meaning[of 125 t]
    substitution_reading_components(1)[of t]
    pattern_call_reading_old_meaning[of 56 t] pattern_call_base_substitution_meaning[of 56 t]
    substitution_reading_old_meaning[of 56 t] reference_bindings_old_meaning[of 56 t]
    definition_call_admission_scoped_meaning[of t]
    pattern_call_reading_old_meaning[of 84 t] pattern_call_base_package_meaning[of 84 t] by auto

lemma pattern_call_reading_valuation:
  "(292,z)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13}. term_formed (h j)) \<and>
      z=pattern_call_reading_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (125,reference_bindings_value (h 7) (h 8) (h 9))\<in>positive_meaning reference_bindings_system \<and>
      (56,scoped_instantiation_argument (h 4) (h 5) (h 6) (h 8) (h 10) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system \<and>
      (56,scoped_instantiation_argument (h 4) (h 5) (h 6) (h 9) (h 11) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system \<and>
      (84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 10)))
        \<in>positive_meaning program_call_admission_system \<and>
      (84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 11)))
        \<in>positive_meaning program_call_admission_system)"
proof -
  have ordinary: "schema_material_premises pattern_call_reading_schema={}"
    by (simp add: pattern_call_reading_schema_def)
  have accepts: "schema_call_formed pattern_call_reading_system 292 (evaluate_pattern h (schema_conclusion pattern_call_reading_schema))"
    if "\<forall>a\<in>schema_variables pattern_call_reading_schema. term_formed (h a)" for h
    using that by (auto simp: pattern_call_reading_call pattern_call_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF pattern_call_reading_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: pattern_call_reading_schema_def schema_variables_def pattern_call_reading_components
      conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem pattern_call_reading_at_arguments:
  "(292,pattern_call_reading_argument e u r d f v q)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    pattern_call_reading_calls e u r d f v q"
proof
  assume admitted: "(292,pattern_call_reading_argument e u r d f v q)\<in>positive_meaning pattern_call_reading_system"
  obtain h :: "nat\<Rightarrow>factor_term" where boundary:
    "e=h 0" "u=h 1" "r=h 2" "d=h 3" "f=h 4" "v=h 5" "q=h 6"
    and calls:
      "(125,reference_bindings_value (h 7) (h 8) (h 9))\<in>positive_meaning reference_bindings_system"
      "(56,scoped_instantiation_argument (h 4) (h 5) (h 6) (h 8) (h 10) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system"
      "(56,scoped_instantiation_argument (h 4) (h 5) (h 6) (h 9) (h 11) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system"
      "(84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 10)))
        \<in>positive_meaning program_call_admission_system"
      "(84,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 11)))
        \<in>positive_meaning program_call_admission_system"
    using admitted by (simp only: pattern_call_reading_valuation factor_term.inject) blast
  show "pattern_call_reading_calls e u r d f v q" unfolding pattern_call_reading_calls_def
    by (rule exI[of _ "h 7"], rule exI[of _ "h 8"], rule exI[of _ "h 9"], rule exI[of _ "h 10"],
      rule exI[of _ "h 11"], rule exI[of _ "h 12"], rule exI[of _ "h 13"])
      (use boundary calls in simp)
next
  assume reads: "pattern_call_reading_calls e u r d f v q"
  obtain b xb yb x y i k where calls:
    "(125,reference_bindings_value b xb yb)\<in>positive_meaning reference_bindings_system"
    "(56,scoped_instantiation_argument f v q xb x i k)\<in>positive_meaning scoped_instantiation_system"
    "(56,scoped_instantiation_argument f v q yb y i k)\<in>positive_meaning scoped_instantiation_system"
    "(84,package_subject_argument e u r (Pair_Term d x))\<in>positive_meaning program_call_admission_system"
    "(84,package_subject_argument e u r (Pair_Term d y))\<in>positive_meaning program_call_admission_system"
    using reads by (auto simp: pattern_call_reading_calls_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then d
    else if j=4 then f else if j=5 then v else if j=6 then q else if j=7 then b
    else if j=8 then xb else if j=9 then yb else if j=10 then x else if j=11 then y else if j=12 then i else k"
  show "(292,pattern_call_reading_argument e u r d f v q)\<in>positive_meaning pattern_call_reading_system"
    by (simp only: pattern_call_reading_valuation; rule exI[of _ ?h])
      (use calls schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(4)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(5)]] in auto)
qed

theorem pattern_call_reading_exact:
  "(292,z)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow> pattern_call_reading_result z"
proof
  assume admitted: "(292,z)\<in>positive_meaning pattern_call_reading_system"
  obtain e u r d f v q where shape: "z=pattern_call_reading_argument e u r d f v q"
    using admitted by (simp only: pattern_call_reading_valuation) blast
  show "pattern_call_reading_result z" using admitted
    by (simp only: shape pattern_call_reading_at_arguments pattern_call_reading_calls_result)
next
  assume result: "pattern_call_reading_result z"
  obtain e u r d f v q where shape: "z=pattern_call_reading_argument e u r d f v q"
    using result unfolding pattern_call_reading_result_def by blast
  show "(292,z)\<in>positive_meaning pattern_call_reading_system" using result
    by (simp only: shape pattern_call_reading_at_arguments pattern_call_reading_calls_result)
qed

corollary pattern_call_reading_on_sources:
  assumes "environment_value_presents E e" "environment_value_presents F f"
  shows "(292,pattern_call_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      f (use_data_term v) (Payload_Term q))\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    schema_pattern_call_at E u r d F v q"
  by (simp only: pattern_call_reading_at_arguments pattern_call_readings_exact[OF assms])

corollary pattern_call_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E e'"
    "environment_value_presents F f" "environment_value_presents F f'"
  shows "(292,pattern_call_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      f (use_data_term v) (Payload_Term q))\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (292,pattern_call_reading_argument e' (use_data_term u) (Payload_Term r) (definition_site_value d)
      f' (use_data_term v) (Payload_Term q))\<in>positive_meaning pattern_call_reading_system"
  by (simp only: pattern_call_reading_on_sources[OF assms(1,3)] pattern_call_reading_on_sources[OF assms(2,4)])

corollary pattern_call_reading_all_instances:
  assumes source: "environment_value_presents E e" "environment_value_presents F f"
    and package: "native_package_at E u r P" and quote: "scoped_pattern_at F v q p I K"
  shows "(292,pattern_call_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
      f (use_data_term v) (Payload_Term q))\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow>
    (\<forall>t. pattern_accepts p t \<longrightarrow> schema_call_formed P d t)"
  using scoped_pattern_formed[OF quote]
  by (simp only: pattern_call_reading_on_sources[OF source] schema_pattern_call_at_reads[OF package quote]
    schema_pattern_call_all_instances; blast)

corollary pattern_call_reading_retains_substitution:
  "(291,z)\<in>positive_meaning pattern_call_reading_system \<longleftrightarrow> substitution_reading_result z"
  using pattern_call_reading_old_meaning[of 291 z] pattern_call_base_substitution_meaning[of 291 z]
    substitution_reading_exact[of z] by auto

section \<open>The native checker is fixed before every future submitted pattern and package\<close>

theorem fixed_native_pattern_call_checker:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu P entry.
    closed_native_package_at B bu [] P \<and>
    (\<forall>z. term_formed z \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] P \<and> native_application_at G au [] entry z I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> pattern_call_reading_result z) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))"
proof -
  obtain h :: "nat\<Rightarrow>local_address option definition_site"
    and B :: "local_address option artifact_environment" and bu P
    where closed: "closed_native_package_at B bu [] P"
    and future: "\<forall>d\<in>system_definitions pattern_call_reading_system. \<forall>z. term_formed z \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] P \<and> native_application_at G au [] (h d) z I K \<and>
        native_package_environment G bu []=B \<and>
        (native_application_formed G bu [] au [] \<longleftrightarrow> schema_call_formed pattern_call_reading_system d z) \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> (d,z)\<in>positive_meaning pattern_call_reading_system) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x))"
    using compiled_program_future_applications[OF pattern_call_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have entry: "292\<in>system_definitions pattern_call_reading_system" by simp
  have instances: "\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
      native_package_at G bu [] P \<and> native_application_at G au [] (h 292) z I K \<and>
      native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
      (native_positive_holds G bu [] au [] \<longleftrightarrow> pattern_call_reading_result z) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)"
    if "term_formed z" for z
    using future[rule_format, OF entry that] entry that
    by (simp only: pattern_call_reading_call pattern_call_reading_exact) auto
  show ?thesis by (rule exI[of _ B], rule exI[of _ bu], rule exI[of _ P], rule exI[of _ "h 292"])
    (use closed instances in blast)
qed

text \<open>
  The combined program keeps every definition of the existing substitution
  and package readers. Their overlap is the same complete source program,
  and dependency locality preserves both meanings. One further ordinary
  clause checks the five readings against those actual definitions.

  The checker is compiled once before all future arguments. Its exact
  contract recovers both submitted environments and every site; it requires
  no externally assumed decoding. Compatible presentations preserve the
  result. For an actual scoped pattern, acceptance is equivalent to call
  formation for all its instances. This checks one boundary needed by proof
  schemes; the graph, clause origins, and material and assertion conditions
  still require their own checks.
\<close>

end
