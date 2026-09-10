theory Factor_Schema_Material_Checking
  imports Factor_Material_Checking
begin

section \<open>Schema instantiation and material satisfaction retain distinct entries\<close>

abbreviation schema_material_checking_result :: "factor_term \<Rightarrow> bool" where
  "schema_material_checking_result z \<equiv> \<exists>E e u r xs S t qs cs.
    z=schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs) \<and>
    environment_value_presents E e \<and> distinct xs \<and> distinct qs \<and> distinct cs \<and>
    native_schema_at E u r S \<and> schema_instance S (set xs) t (set qs) \<and>
    set cs=material_instance_relation (set xs) (schema_material_premises S) \<and> schema_material_satisfied S (set xs)"

definition schema_material_checking_schema :: "(nat,nat,nat) factor_schema" where
  "schema_material_checking_schema=data_rule
    (schema_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,65,schema_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)),
     (1,67,Pattern_Variable 6)}"

definition schema_material_checking_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_material_checking_system=add_view_definition material_rows_checking_system 68 data_x {(0,schema_material_checking_schema)}"

lemma schema_material_checking_system_formed [simp]: "schema_system_formed schema_material_checking_system"
  unfolding schema_material_checking_system_def
  by (rule add_recursive_definition_formed[OF material_rows_checking_system_formed])
    (auto simp: schema_material_checking_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_material_checking_definitions [simp]:
  "system_definitions schema_material_checking_system=insert 68 (system_definitions material_rows_checking_system)"
  by (simp add: schema_material_checking_system_def)

lemma schema_material_checking_call:
  "schema_call_formed schema_material_checking_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_material_checking_system \<and> term_formed t"
  using added_variable_calls[OF material_rows_checking_system_formed
    schema_material_checking_system_formed[unfolded schema_material_checking_system_def] material_rows_checking_call]
  by (simp only: schema_material_checking_system_def[symmetric])

lemma schema_material_checking_old_meaning:
  assumes "d\<in>system_definitions material_rows_checking_system"
  shows "(d,t)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> (d,t)\<in>positive_meaning material_rows_checking_system"
  using added_definition_preserves_old(2)[OF material_rows_checking_system_formed
    schema_material_checking_system_formed[unfolded schema_material_checking_system_def], of d t] assms
  by (auto simp: schema_material_checking_system_def)

lemma schema_material_checking_clause [simp]:
  "((68,c),S)\<in>system_clauses schema_material_checking_system \<longleftrightarrow> (c,S)\<in>{(0,schema_material_checking_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses material_rows_checking_system \<Longrightarrow>
    d\<in>system_definitions material_rows_checking_system" for d c S
    using material_rows_checking_system_formed unfolding schema_system_formed_def by blast
  have absent: "((68,c),S)\<notin>system_clauses material_rows_checking_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_material_checking_system_def)
qed

lemma schema_material_checking_components:
  "(65,t)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> (65,t)\<in>positive_meaning schema_instantiation_system"
  "(66,t)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> (66,t)\<in>positive_meaning material_checking_system"
  "(67,t)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> (67,t)\<in>positive_meaning material_rows_checking_system"
  using schema_material_checking_old_meaning[of 65 t] material_rows_checking_old_meaning[of 65 t]
    material_checking_old_meaning[of 65 t] schema_material_checking_old_meaning[of 66 t]
    material_rows_checking_old_meaning[of 66 t] schema_material_checking_old_meaning[of 67 t] by auto

lemma schema_material_checking_step:
  assumes inst: "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system"
    and material: "(67,c)\<in>positive_meaning material_rows_checking_system"
  shows "(68,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_material_checking_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed b" "term_formed t" "term_formed q" "term_formed c"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then b
    else if n=4 then t else if n=5 then q else c"
  have result: "(68,evaluate_pattern ?h (schema_conclusion schema_material_checking_schema))\<in>positive_meaning schema_material_checking_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: schema_material_checking_schema_def schema_variables_def
        schema_material_checking_call schema_material_checking_components\<close>)
  show ?thesis using result by (simp add: schema_material_checking_schema_def)
qed

lemma schema_material_checking_source:
  assumes holds: "(68,z)\<in>positive_meaning schema_material_checking_system"
  shows "\<exists>e u r b t q c. z=schema_instantiation_argument e u r b t q c \<and>
    (65,z)\<in>positive_meaning schema_instantiation_system \<and> (67,c)\<in>positive_meaning material_rows_checking_system"
proof -
  have consequence: "(68,z)\<in>schema_consequences schema_material_checking_system (positive_meaning schema_material_checking_system)"
    using holds positive_meaning_unfold[of schema_material_checking_system] by blast
  obtain n S h where clause: "((68,n),S)\<in>system_clauses schema_material_checking_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning schema_material_checking_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=schema_material_checking_schema" using clause by simp
  show ?thesis
    by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"],
      rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"])
      (use conclusion support in \<open>auto simp: schema schema_material_checking_schema_def schema_material_checking_components\<close>)
qed

theorem schema_material_checking_fields:
  "(68,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow>
    (65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system \<and>
    (67,c)\<in>positive_meaning material_rows_checking_system"
  using schema_material_checking_source[of "schema_instantiation_argument e u r b t q c"]
    schema_material_checking_step[of e u r b t q c] by auto

theorem schema_material_checking_exact:
  "(68,z)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> schema_material_checking_result z"
proof
  assume holds: "(68,z)\<in>positive_meaning schema_material_checking_system"
  obtain e u r b t q c where fields: "z=schema_instantiation_argument e u r b t q c"
    "(65,z)\<in>positive_meaning schema_instantiation_system" "(67,c)\<in>positive_meaning material_rows_checking_system"
    using schema_material_checking_source[OF holds] by blast
  obtain E f a l xs S v qs cs where parts:
    "z=schema_instantiation_argument f (use_data_term a) (Payload_Term l) (binding_rows_term xs) v
      (call_instance_rows_term qs) (binding_rows_term cs)"
    "environment_value_presents E f" "distinct xs" "distinct qs" "distinct cs" "native_schema_at E a l S"
    "schema_instance S (set xs) v (set qs)" "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using fields(2) by (simp only: schema_instantiation_exact) blast
  have checked: "(67,binding_rows_term cs)\<in>positive_meaning material_rows_checking_system"
    using parts(1) fields(1,3) by auto
  have satisfied: "schema_material_satisfied S (set xs)"
    using checked by (simp only: schema_material_rows_checking[OF parts(6-8)])
  show "schema_material_checking_result z"
    by (rule exI[of _ E], rule exI[of _ f], rule exI[of _ a], rule exI[of _ l], rule exI[of _ xs],
      rule exI[of _ S], rule exI[of _ v], rule exI[of _ qs], rule exI[of _ cs])
      (use parts satisfied in blast)
next
  assume "schema_material_checking_result z"
  then obtain E e u r xs S t qs cs where parts:
    "z=schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs)"
    "environment_value_presents E e" "distinct xs" "distinct qs" "distinct cs" "native_schema_at E u r S"
    "schema_instance S (set xs) t (set qs)" "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    "schema_material_satisfied S (set xs)" by blast
  have inst: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    by (rule schema_instantiation_complete[OF parts(6,2,7,3-5,8)])
  have material: "(67,binding_rows_term cs)\<in>positive_meaning material_rows_checking_system"
    using parts(9) by (simp only: schema_material_rows_checking[OF parts(6-8)])
  show "(68,z)\<in>positive_meaning schema_material_checking_system"
    using schema_material_checking_step[OF inst material] parts(1) by simp
qed

corollary schema_material_checking_on_values:
  assumes source: "environment_value_presents E e"
  shows "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> distinct cs \<and>
    (\<exists>S. native_schema_at E u r S \<and> schema_instance S (set xs) t (set qs) \<and>
      set cs=material_instance_relation (set xs) (schema_material_premises S) \<and> schema_material_satisfied S (set xs))"
proof -
  have bridge: "(67,binding_rows_term cs)\<in>positive_meaning material_rows_checking_system \<longleftrightarrow>
      schema_material_satisfied S (set xs)"
    if "native_schema_at E u r S" "schema_instance S (set xs) t (set qs)"
      "set cs=material_instance_relation (set xs) (schema_material_premises S)" for S
    by (rule schema_material_rows_checking[OF that])
  show ?thesis
    by (simp only: schema_material_checking_fields schema_instantiation_on_values[OF source]) (use bridge in blast)
qed

corollary schema_material_checking_at_schema:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
  shows "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system \<longleftrightarrow>
    distinct xs \<and> distinct qs \<and> distinct cs \<and> schema_instance S (set xs) t (set qs) \<and>
    set cs=material_instance_relation (set xs) (schema_material_premises S) \<and> schema_material_satisfied S (set xs)"
proof -
  have unique: "T=S" if "native_schema_at E u r T" for T
    by (rule native_schema_unique[OF that raw])
  show ?thesis
    by (simp only: schema_material_checking_on_values[OF source]) (use raw unique in blast)
qed

corollary schema_material_checking_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(68,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow>
    (68,schema_instantiation_argument f u r b t q c)\<in>positive_meaning schema_material_checking_system"
  by (simp only: schema_material_checking_fields schema_instantiation_presentation_invariance[OF assms])

corollary schema_material_checking_orders:
  assumes source: "environment_value_presents E e" and same: "mset xs=mset ys" "mset qs=mset qs'" "mset cs=mset cs'"
  shows "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system \<longleftrightarrow>
    (68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) t
      (call_instance_rows_term qs') (binding_rows_term cs'))\<in>positive_meaning schema_material_checking_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)] mset_eq_imp_distinct_iff[OF same(3)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)] mset_eq_setD[OF same(3)]
  by (simp only: schema_material_checking_on_values[OF source])

corollary schema_material_checking_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system"
    and second: "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) v
      (call_instance_rows_term qs') (binding_rows_term cs'))\<in>positive_meaning schema_material_checking_system"
  shows "t=v \<and> mset qs=mset qs' \<and> mset cs=mset cs'"
  using first second schema_instantiation_result_unique[OF source]
  by (simp only: schema_material_checking_fields) blast

theorem schema_material_checking_exists:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and bindings: "term_bindings_formed (schema_variables S) (set xs)" and order: "distinct xs"
  shows "(\<exists>t qs cs. (68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system)
    \<longleftrightarrow> schema_material_satisfied S (set xs)"
proof
  assume "\<exists>t qs cs. (68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system"
  then show "schema_material_satisfied S (set xs)"
    by (simp only: schema_material_checking_at_schema[OF source raw]) blast
next
  assume satisfied: "schema_material_satisfied S (set xs)"
  obtain t qs cs where inst: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_total[OF source raw bindings order] by blast
  have checked: "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system"
    using inst satisfied by (simp only: schema_instantiation_at_schema[OF source raw] schema_material_checking_at_schema[OF source raw])
  show "\<exists>t qs cs. (68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_material_checking_system"
    using checked by blast
qed

corollary schema_material_checking_missing_or_extra_socket:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and changed: "rel_dom (set qs)\<noteq>rel_dom (schema_premises S) \<or> rel_dom (set cs)\<noteq>rel_dom (schema_material_premises S)"
  shows "(68,schema_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (call_instance_rows_term qs) (binding_rows_term cs))\<notin>positive_meaning schema_material_checking_system"
  using schema_instantiation_missing_or_extra_socket[OF source raw changed]
  by (simp only: schema_material_checking_fields) blast

section \<open>Four distinct native sites precede every future operand\<close>

abbreviation schema_checking_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "schema_checking_operation_result d t \<equiv>
    (d=65 \<and> schema_instantiation_result t) \<or> (d=66 \<and> material_checking_result t) \<or>
    (d=67 \<and> material_rows_checking_result t) \<or> (d=68 \<and> schema_material_checking_result t)"

lemma schema_checking_operations_exact:
  assumes "d\<in>{65,66,67,68}"
  shows "(d,t)\<in>positive_meaning schema_material_checking_system \<longleftrightarrow> schema_checking_operation_result d t"
proof -
  consider "d=65" | "d=66" | "d=67" | "d=68" using assms by auto
  then show ?thesis
    by cases (simp_all add: schema_material_checking_components schema_instantiation_exact material_checking_exact
      material_rows_checking_exact schema_material_checking_exact)
qed

theorem native_schema_checking_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {65::nat,66,67,68} \<and>
    (\<forall>d\<in>{65,66,67,68}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> schema_checking_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions schema_material_checking_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions schema_material_checking_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed schema_material_checking_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning schema_material_checking_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF schema_material_checking_system_formed] by blast
  have sites: "inj_on g {65,66,67,68}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {65,66,67,68}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{65,66,67,68}" and tf: "term_formed t"
    have member: "d\<in>system_definitions schema_material_checking_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed schema_material_checking_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning schema_material_checking_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> schema_checking_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member schema_checking_operations_exact[OF selected] in \<open>auto simp: schema_material_checking_call\<close>)
  qed
qed

text \<open>
  The final entry composes schema instantiation with complete checking of
  its material projection. The raw schema and all instantiated operands
  remain uniquely recoverable. Satisfaction neither supplies a schema
  reading nor erases a premise socket. An empty supplied material list
  passes only when it is the schema's complete material projection.

  All four entries have exact contracts over every term and preserve all
  earlier meanings. The two schema entries accept every complete source
  presentation and independent substitution, call-row, and material-row
  order. Their outputs are unique up to enumeration. The instantiation entry
  is total for every valid schema and complete formed binding table; the
  combined entry has an output exactly when its material equations hold.

  One fixed closed native program supplies four distinct sites before every
  future formed operand and retains its canonical environment. It has
  sixty-nine definitions and one hundred and fifteen clauses. The result
  does not assert that prospective calls meet a program's interfaces or
  that those calls hold. Definition and package admission, finite evidence
  checking, the complete amendment protocol, reflection, and genesis
  remain separate work.
\<close>

end
