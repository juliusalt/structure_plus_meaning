theory Factor_Retained_Clause_Admission
  imports Factor_Related_Test_Admission
begin

section \<open>One actual package entry retains its source and complete clause\<close>

definition retained_clause_schema :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat) factor_schema" where
  "retained_clause_schema e v=data_rule
    (package_subject_pattern data_x data_y data_z data_w)
    {(0,83,package_subject_pattern data_x data_y data_z data_w),
     (1,113,Pattern_Pair (exact_term_pattern e) data_x),
     (2,127,Pattern_Pair (Pattern_Pair data_x data_w) (exact_term_pattern v))}"

definition retained_clause_system :: "factor_term \<Rightarrow> factor_term \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "retained_clause_system e v=add_view_definition related_test_admission_base 370 data_x
    {(0,retained_clause_schema e v)}"

definition retained_clause_result where
  "retained_clause_result E S p \<longleftrightarrow>
    (\<exists>F u r Q d f. environment_value_presents F f \<and>
      p=package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d) \<and>
      native_package_at F u r Q \<and> d\<in>system_definitions Q \<and>
      environment_included E F \<and> native_single_clause_at F (fst d) (snd d) S)"

locale retained_clause_reader =
  fixes e v :: factor_term
  assumes fields: "term_formed e" "term_formed v"
begin

lemma schema_formed: "schema_formed (retained_clause_schema e v)"
  using fields by (auto simp: retained_clause_schema_def schema_formed_def single_valued_def)

lemma dependencies: "schema_dependencies (retained_clause_schema e v)={83,113,127}"
  by (simp add: retained_clause_schema_def schema_dependencies_def rel_ran_image)

sublocale view: positive_view related_test_admission_base 370 data_x "{(0,retained_clause_schema e v)}"
  by (rule positive_view.intro)
    (use related_test_admission_base_bound related_test_admission_base_roots schema_formed dependencies
      in \<open>auto simp: single_valued_def dest: subsetD\<close>)

lemma formed: "schema_system_formed (retained_clause_system e v)"
  using view.formed by (simp only: retained_clause_system_def)

lemma definitions [simp]: "system_definitions (retained_clause_system e v)=
  insert 370 (system_definitions related_test_admission_base)"
  by (simp add: retained_clause_system_def)

lemma calls: "schema_call_formed (retained_clause_system e v) d t \<longleftrightarrow>
    d\<in>system_definitions (retained_clause_system e v) \<and> term_formed t"
  using added_variable_calls[OF related_test_admission_base_formed view.formed related_test_admission_base_call]
  by (simp only: retained_clause_system_def)

lemma old_meaning:
  assumes "d\<in>system_definitions related_test_admission_base"
  shows "(d,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (d,t)\<in>positive_meaning related_test_admission_base"
  using view.old_meaning[OF assms] by (simp only: retained_clause_system_def)

lemma clause [simp]: "((370,c),S)\<in>system_clauses (retained_clause_system e v) \<longleftrightarrow>
  c=0 \<and> S=retained_clause_schema e v"
  using view.no_old_clause by (auto simp: retained_clause_system_def)

lemma components:
  "(83,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system"
  "(113,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  "(127,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system"
proof -
  have retained: "d\<in>system_definitions related_test_admission_base" if "d\<in>{83,113,127}" for d
    by (rule subsetD[OF related_test_admission_base_roots that])
  have same: "(d,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
      (d,t)\<in>positive_meaning related_test_components_system" if "d\<in>{83,113,127}" for d
    by (simp only: old_meaning[OF retained[OF that]] related_test_admission_base_meaning[OF retained[OF that]])
  show "(83,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (83,t)\<in>positive_meaning package_membership_system" using same[of 83]
    by (simp add: related_test_component_meanings)
  show "(113,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system" using same[of 113]
    by (simp add: related_test_component_meanings)
  show "(127,t)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (127,t)\<in>positive_meaning single_clause_reading_system" using same[of 127]
    by (simp add: related_test_component_meanings)
qed

lemma valuation:
  "(370,p)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3}. term_formed (h j)) \<and>
      p=package_subject_argument (h 0) (h 1) (h 2) (h 3) \<and>
      (83,p)\<in>positive_meaning package_membership_system \<and>
      (113,Pair_Term e (h 0))\<in>positive_meaning environment_inclusion_system \<and>
      (127,Pair_Term (Pair_Term (h 0) (h 3)) v)\<in>positive_meaning single_clause_reading_system)"
proof -
  have ordinary: "schema_material_premises (retained_clause_schema e v)={}"
    by (simp add: retained_clause_schema_def)
  have accepts: "schema_call_formed (retained_clause_system e v) 370
      (evaluate_pattern h (schema_conclusion (retained_clause_schema e v)))"
    if "\<forall>a\<in>schema_variables (retained_clause_schema e v). term_formed (h a)" for h
    using that fields by (auto simp: calls retained_clause_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    using fields apply (auto simp: retained_clause_schema_def schema_variables_def components)
    done
qed

lemma on_arguments:
  "(370,package_subject_argument f u r d)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (83,package_subject_argument f u r d)\<in>positive_meaning package_membership_system \<and>
    (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<and>
    (127,Pair_Term (Pair_Term f d) v)\<in>positive_meaning single_clause_reading_system"
proof
  assume holds: "(370,package_subject_argument f u r d)\<in>positive_meaning (retained_clause_system e v)"
  show "(83,package_subject_argument f u r d)\<in>positive_meaning package_membership_system \<and>
    (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<and>
    (127,Pair_Term (Pair_Term f d) v)\<in>positive_meaning single_clause_reading_system"
    using holds by (auto simp: valuation)
next
  assume parts: "(83,package_subject_argument f u r d)\<in>positive_meaning package_membership_system \<and>
    (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<and>
    (127,Pair_Term (Pair_Term f d) v)\<in>positive_meaning single_clause_reading_system"
  have formed: "term_formed f" "term_formed u" "term_formed r" "term_formed d"
    using schema_call_formed_target[OF positive_meaning_formed[OF conjunct1[OF parts]]] by auto
  let ?h="\<lambda>j::nat. if j=0 then f else if j=1 then u else if j=2 then r else d"
  show "(370,package_subject_argument f u r d)\<in>positive_meaning (retained_clause_system e v)"
    by (simp only: valuation; rule exI[of _ ?h]) (use formed parts in auto)
qed

theorem on_values:
  assumes source: "environment_value_presents E e" and reference: "schema_reference_presents S v"
    and target: "environment_value_presents F f"
  shows "(370,package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow>
    (\<exists>Q. native_package_at F u r Q \<and> d\<in>system_definitions Q) \<and>
      environment_included E F \<and> native_single_clause_at F (fst d) (snd d) S"
proof -
  have same: "G=E" if "environment_value_presents G e" for G
    by (rule environment_value_presents_unique[OF that source])
  have other: "G=F" if "environment_value_presents G f" for G
    by (rule environment_value_presents_unique[OF that target])
  have inclusion: "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
      environment_included E F"
    by (simp only: environment_inclusion_exact factor_term.inject) (use source target same other in blast)
  show ?thesis
  proof (cases "\<exists>Q. native_package_at F u r Q \<and> d\<in>system_definitions Q")
    case False
    then show ?thesis by (simp only: on_arguments package_membership_on_values[OF target]; simp)
  next
    case True
    then obtain Q where package: "native_package_at F u r Q" and member: "d\<in>system_definitions Q" by blast
    have position: "d\<in>environment_positions F" by (rule native_package_entry_position[OF package member])
    have site: "site_value_presents F (fst d) (snd d) (Pair_Term f (definition_site_value d))"
      using target position by (simp add: site_value_presents_def site_data_term_def)
    show ?thesis by (simp only: on_arguments package_membership_on_values[OF target] inclusion
      single_clause_reading_at_reference[OF site reference])
  qed
qed

theorem exact:
  assumes source: "environment_value_presents E e" and reference: "schema_reference_presents S v"
  shows "(370,p)\<in>positive_meaning (retained_clause_system e v) \<longleftrightarrow> retained_clause_result E S p"
proof
  assume holds: "(370,p)\<in>positive_meaning (retained_clause_system e v)"
  have member: "(83,p)\<in>positive_meaning package_membership_system" using holds by (simp only: valuation; blast)
  obtain F f u r d Q where parts: "environment_value_presents F f"
    "p=package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d)"
    "native_package_at F u r Q" "d\<in>system_definitions Q"
    using package_membership_sound[OF member] by blast
  have actual: "environment_included E F \<and> native_single_clause_at F (fst d) (snd d) S"
    using holds by (simp only: parts(2) on_values[OF source reference parts(1)]; blast)
  show "retained_clause_result E S p" unfolding retained_clause_result_def
    by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ r], rule exI[of _ Q], rule exI[of _ d], rule exI[of _ f])
      (use parts actual in blast)
next
  assume "retained_clause_result E S p"
  then obtain F u r Q d f where parts: "environment_value_presents F f"
    "p=package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d)"
    "native_package_at F u r Q" "d\<in>system_definitions Q"
    "environment_included E F" "native_single_clause_at F (fst d) (snd d) S"
    unfolding retained_clause_result_def by blast
  show "(370,p)\<in>positive_meaning (retained_clause_system e v)"
    by (simp only: parts(2) on_values[OF source reference parts(1)]) (use parts(3-6) in blast)
qed

theorem native_checker:
  assumes source: "environment_value_presents E e" and reference: "schema_reference_presents S v"
  shows "\<exists>C :: local_address option artifact_environment. \<exists>cu Q d.
    closed_native_package_at C cu [] Q \<and> native_package_environment C cu []=C \<and>
    d\<in>system_definitions Q \<and>
    (\<forall>p. schema_call_formed Q d p \<longleftrightarrow> term_formed p) \<and>
    (\<forall>p. (d,p)\<in>positive_meaning Q \<longleftrightarrow> retained_clause_result E S p)"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q where compiled:
    "inj_on g (system_definitions (retained_clause_system e v))"
    "closed_native_package_at C cu [] Q" "native_package_environment C cu []=C"
    "system_alpha_variant (rename_system g (retained_clause_system e v)) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning (retained_clause_system e v)"
    using program_compilation_total[OF formed] by (elim exE conjE) (rule that; assumption)
  have member: "370\<in>system_definitions (retained_clause_system e v)" by simp
  have entry: "g 370\<in>system_definitions Q"
    using compiled(4) member unfolding system_alpha_variant_def renamed_system_definitions by blast
  have call: "schema_call_formed Q (g 370) p \<longleftrightarrow> term_formed p" for p
    by (simp only: compiled_system_call_boundary[OF formed compiled(1,4) member] calls; simp)
  have meaning: "(g 370,p)\<in>positive_meaning Q \<longleftrightarrow> retained_clause_result E S p" for p
    by (simp only: compiled_system_meaning_at[OF compiled(1) member compiled(5)] exact[OF source reference])
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q], rule exI[of _ "g 370"])
    (use compiled(2,3) entry call meaning in blast)
qed

end


section \<open>Every actual retained installation has an admitted complete presentation\<close>

theorem retained_clause_presentations_total:
  fixes F :: "local_address option artifact_environment"
  assumes source: "environment_value_presents E e" and included: "environment_included E F"
    and package: "native_package_at F u r Q" and member: "d\<in>system_definitions Q"
    and read: "native_single_clause_at F (fst d) (snd d) S"
  shows "\<exists>f v. environment_value_presents F f \<and> schema_reference_presents S v \<and>
    (370,package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning (retained_clause_system e v)"
proof -
  have formed: "environment_formed F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain f where target: "environment_value_presents F f"
    using environment_value_presents_total[OF formed] by blast
  obtain a where schema: "native_schema_at F (fst d) a S"
    using native_single_clause_schema[OF read] by blast
  obtain v where reference: "schema_reference_presents S v"
    using native_schema_reference_total[OF schema] by blast
  interpret reader: retained_clause_reader e v
    by (rule retained_clause_reader.intro)
      (use environment_value_presents_formed[OF source] schema_reference_presents_formed[OF reference] in auto)
  have admitted: "(370,package_subject_argument f (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning (retained_clause_system e v)"
    by (simp only: reader.on_values[OF source reference target]) (use package member included read in blast)
  show ?thesis using target reference admitted by blast
qed

text \<open>
  The source environment and complete expected schema reference are fixed
  before future operands. Three existing operations read the actual proposed
  package entry, retain the entire original environment, and check the whole
  definition. The installed program is recovered from its complete package;
  its domain is not supplied as a substitute for its clauses or meanings.

  This generic checker applies to any schema. Its source-retention condition
  prevents the same callee coordinates from silently referring to changed
  source artifacts. It does not decide whether an independently required
  condition has been adequately expressed by that schema.
\<close>

end
