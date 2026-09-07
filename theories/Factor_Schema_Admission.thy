theory Factor_Schema_Admission
  imports Factor_Schema_Material_Checking
begin

section \<open>Schema formation has a complete instance independently of truth\<close>

abbreviation source_root_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "source_root_argument e u r \<equiv> Pair_Term (Pair_Term e u) r"

abbreviation source_root_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "source_root_pattern e u r \<equiv> Pattern_Pair (Pattern_Pair e u) r"

abbreviation schema_admission_result :: "factor_term \<Rightarrow> bool" where
  "schema_admission_result z \<equiv> \<exists>E e u r S.
    z=source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents E e \<and> native_schema_at E u r S"

definition schema_admission_schema :: "(nat,nat,nat) factor_schema" where
  "schema_admission_schema=data_rule (source_root_pattern data_x data_y data_z)
    {(0,65,schema_instantiation_pattern data_x data_y data_z data_w
      (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))}"

definition schema_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_admission_system=add_view_definition schema_material_checking_system 69 data_x {(0,schema_admission_schema)}"

lemma schema_admission_system_formed [simp]: "schema_system_formed schema_admission_system"
  unfolding schema_admission_system_def
  by (rule add_recursive_definition_formed[OF schema_material_checking_system_formed])
    (auto simp: schema_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_admission_definitions [simp]:
  "system_definitions schema_admission_system=insert 69 (system_definitions schema_material_checking_system)"
  by (simp add: schema_admission_system_def)

lemma schema_admission_call:
  "schema_call_formed schema_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_admission_system \<and> term_formed t"
  using added_variable_calls[OF schema_material_checking_system_formed
    schema_admission_system_formed[unfolded schema_admission_system_def] schema_material_checking_call]
  by (simp only: schema_admission_system_def[symmetric])

lemma schema_admission_old_meaning:
  assumes "d\<in>system_definitions schema_material_checking_system"
  shows "(d,t)\<in>positive_meaning schema_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning schema_material_checking_system"
  using added_definition_preserves_old(2)[OF schema_material_checking_system_formed
    schema_admission_system_formed[unfolded schema_admission_system_def], of d t] assms
  by (auto simp: schema_admission_system_def)

lemma schema_admission_clause [simp]:
  "((69,c),S)\<in>system_clauses schema_admission_system \<longleftrightarrow> (c,S)\<in>{(0,schema_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses schema_material_checking_system \<Longrightarrow>
    d\<in>system_definitions schema_material_checking_system" for d c S
    using schema_material_checking_system_formed unfolding schema_system_formed_def by blast
  have absent: "((69,c),S)\<notin>system_clauses schema_material_checking_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_admission_system_def)
qed

lemma schema_admission_previous_meaning:
  assumes "d\<in>system_definitions schema_instantiation_system"
  shows "(d,t)\<in>positive_meaning schema_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning schema_instantiation_system"
  using schema_admission_old_meaning[of d t] schema_material_checking_old_meaning[of d t]
    material_rows_checking_old_meaning[of d t] material_checking_old_meaning[OF assms, of t] assms by auto

lemma schema_admission_component:
  "(65,t)\<in>positive_meaning schema_admission_system \<longleftrightarrow>
    (65,t)\<in>positive_meaning schema_instantiation_system"
  by (rule schema_admission_previous_meaning) simp

lemma schema_admission_step:
  assumes inst: "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system"
  shows "(69,source_root_argument e u r)\<in>positive_meaning schema_admission_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed b"
    "term_formed t" "term_formed q" "term_formed c"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then b
    else if n=4 then t else if n=5 then q else c"
  have result: "(69,evaluate_pattern ?h (schema_conclusion schema_admission_schema))\<in>positive_meaning schema_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed inst in \<open>auto simp: schema_admission_schema_def schema_variables_def
        schema_admission_call schema_admission_component\<close>)
  show ?thesis using result by (simp add: schema_admission_schema_def)
qed

theorem schema_admission_sound:
  assumes holds: "(69,z)\<in>positive_meaning schema_admission_system"
  shows "schema_admission_result z"
proof -
  have consequence: "(69,z)\<in>schema_consequences schema_admission_system (positive_meaning schema_admission_system)"
    using holds positive_meaning_unfold[of schema_admission_system] by blast
  obtain n S h where clause: "((69,n),S)\<in>system_clauses schema_admission_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning schema_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=schema_admission_schema" using clause by simp
  have inst: "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6))
      \<in>positive_meaning schema_instantiation_system"
    using support by (auto simp: schema schema_admission_schema_def schema_admission_component)
  obtain E u r T where raw: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "h 2=Payload_Term r" "native_schema_at E u r T"
    using inst by (simp only: schema_instantiation_exact factor_term.inject) blast
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ T])
      (use raw conclusion in \<open>simp add: schema schema_admission_schema_def\<close>)
qed

theorem schema_admission_complete:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
  shows "(69,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning schema_admission_system"
proof -
  let ?B="image (\<lambda>a. (a,Payload_Term [])) (schema_variables S)"
  have finite: "finite (schema_variables S)" by (rule schema_variables_finite[OF native_schema_formed[OF raw]])
  have bindings: "term_bindings_formed (schema_variables S) ?B"
    using finite by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  have table_finite: "finite ?B" by (rule finite_imageI[OF finite])
  obtain xs where rows: "set xs=?B" "distinct xs" using finite_distinct_list[OF table_finite] by blast
  have table: "term_bindings_formed (schema_variables S) (set xs)" using bindings rows(1) by simp
  obtain t qs cs where inst: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term xs) t (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw table rows(2)] by blast
  show ?thesis by (rule schema_admission_step[OF inst])
qed

theorem schema_admission_exact:
  "(69,z)\<in>positive_meaning schema_admission_system \<longleftrightarrow> schema_admission_result z"
  using schema_admission_sound schema_admission_complete by blast

corollary schema_admission_at_source:
  assumes source: "environment_value_presents E e"
  shows "(69,source_root_argument e u r)\<in>positive_meaning schema_admission_system \<longleftrightarrow>
    (\<exists>v a S. u=use_data_term v \<and> r=Payload_Term a \<and> native_schema_at E v a S)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: schema_admission_exact factor_term.inject) (use source unique in blast)
qed

corollary schema_admission_on_values:
  assumes source: "environment_value_presents E e"
  shows "(69,source_root_argument e (use_data_term u) (Payload_Term r))\<in>positive_meaning schema_admission_system
    \<longleftrightarrow> (\<exists>S. native_schema_at E u r S)"
  by (simp only: schema_admission_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary schema_admission_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(69,source_root_argument e u r)\<in>positive_meaning schema_admission_system \<longleftrightarrow>
    (69,source_root_argument f u r)\<in>positive_meaning schema_admission_system"
  by (simp only: schema_admission_at_source[OF assms(1)] schema_admission_at_source[OF assms(2)])

text \<open>
  One ordinary clause hides the complete substitution and both complete
  instance projections. Every formed native schema has such an instance.
  The constant empty-payload assignment is only a witness in that proof;
  it is not stored syntax or an added condition on admissible substitutions.

  Grammar admission calls instantiation independently of material checking.
  A schema may contain unsatisfied material equations or prospective calls.
  Their truth does not authorize its reading. The argument contains exactly
  the complete environment presentation, actual use, and actual root.
\<close>

end
