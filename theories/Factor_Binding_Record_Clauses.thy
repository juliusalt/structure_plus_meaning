theory Factor_Binding_Record_Clauses
  imports Factor_Binding_Observation_Recovery Factor_Substitution_Admission Factor_Recursive_Groups
begin

section \<open>The existing record and row programs retain their complete meanings\<close>

definition binding_record_base_system :: "(nat,nat,nat,nat) schema_system" where
  "binding_record_base_system=system_union reference_bindings_system binding_observation_program"

interpretation binding_record_components:
  positive_definition_group reference_bindings_system binding_observation_program
proof
  show "schema_system_formed reference_bindings_system" by simp
  show "schema_system_formed_over (system_definitions reference_bindings_system) binding_observation_program"
    using binding_observation_program_formed
    unfolding schema_system_formed_over_def schema_system_formed_def by blast
  show "system_definitions reference_bindings_system\<inter>system_definitions binding_observation_program={}"
    by auto
qed

lemma binding_record_base_formed [simp]: "schema_system_formed binding_record_base_system"
  using binding_record_components.formed by (simp only: binding_record_base_system_def)

lemma binding_record_base_definitions [simp]:
  "system_definitions binding_record_base_system=
    system_definitions reference_bindings_system\<union>{343,344,345,346,347}"
  by (simp add: binding_record_base_system_def)

lemma binding_record_base_call:
  "schema_call_formed binding_record_base_system d t \<longleftrightarrow>
    d\<in>system_definitions binding_record_base_system \<and> term_formed t"
  using binding_record_components.variable_calls[OF reference_bindings_call binding_observation_interfaces]
  by (simp only: binding_record_base_system_def)

lemma binding_record_base_reference:
  assumes "d\<in>system_definitions reference_bindings_system"
  shows "(d,t)\<in>positive_meaning binding_record_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning reference_bindings_system"
  using binding_record_components.old_meaning[OF assms]
  by (simp only: binding_record_base_system_def)

lemma binding_record_base_observation:
  assumes "d\<in>{343,344,345,346,347}"
  shows "(d,t)\<in>positive_meaning binding_record_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning binding_observation_program"
  using system_union_left_locality(2)[OF binding_observation_program_formed reference_bindings_system_formed,
    of d t] assms
  by (auto simp: binding_record_base_system_def system_union_commute)

section \<open>One actual replacement record supplies both observations\<close>

abbreviation binding_record_argument where
  "binding_record_argument e u r b owner bs i k \<equiv>
    Pair_Term (Pair_Term e (Pair_Term u r))
      (Pair_Term b (Pair_Term owner (Pair_Term bs (Pair_Term i k))))"

abbreviation binding_record_pattern where
  "binding_record_pattern e u r b owner bs i k \<equiv>
    Pattern_Pair (Pattern_Pair e (Pattern_Pair u r))
      (Pattern_Pair b (Pattern_Pair owner (Pattern_Pair bs (Pattern_Pair i k))))"

definition binding_record_schema :: "(nat,nat,nat) factor_schema" where
  "binding_record_schema=data_rule
    (binding_record_pattern data_x data_y data_z data_w
      (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7))
    {(0,125,reference_bindings_pattern data_w (Pattern_Variable 8) (Pattern_Variable 9)),
     (1,61,pattern_instantiation_pattern data_x data_y data_w (Pattern_Variable 8) data_z
       (Pattern_Variable 10) data_w (Pattern_Variable 6) (Pattern_Variable 7)),
     (2,61,pattern_instantiation_pattern data_x data_y data_w (Pattern_Variable 9) data_z
       (Pattern_Variable 11) data_w (Pattern_Variable 6) (Pattern_Variable 7)),
     (3,347,binding_observation_pattern (Pattern_Variable 4) (Pattern_Variable 5)
       (Pattern_Variable 10) (Pattern_Variable 11))}"

definition binding_record_system :: "(nat,nat,nat,nat) schema_system" where
  "binding_record_system=add_view_definition binding_record_base_system 348 data_x {(0,binding_record_schema)}"

interpretation binding_record_view: positive_view binding_record_base_system 348 data_x "{(0,binding_record_schema)}"
  by (rule positive_view.intro)
    (auto simp: binding_record_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma binding_record_formed [simp]: "schema_system_formed binding_record_system"
  using binding_record_view.formed by (simp only: binding_record_system_def)

lemma binding_record_definitions [simp]:
  "system_definitions binding_record_system=insert 348 (system_definitions binding_record_base_system)"
  by (simp add: binding_record_system_def)

lemma binding_record_call:
  "schema_call_formed binding_record_system d t \<longleftrightarrow>
    d\<in>system_definitions binding_record_system \<and> term_formed t"
  using added_variable_calls[OF binding_record_base_formed
    binding_record_formed[unfolded binding_record_system_def] binding_record_base_call]
  by (simp only: binding_record_system_def[symmetric])

lemma binding_record_old_meaning:
  assumes "d\<in>system_definitions binding_record_base_system"
  shows "(d,t)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning binding_record_base_system"
  using binding_record_view.old_meaning[OF assms] by (simp only: binding_record_system_def)

lemma binding_record_clause [simp]:
  "((348,c),S)\<in>system_clauses binding_record_system \<longleftrightarrow> c=0 \<and> S=binding_record_schema"
  using binding_record_view.no_old_clause by (auto simp: binding_record_system_def)

lemma binding_record_readers:
  "(125,t)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    (125,t)\<in>positive_meaning reference_bindings_system"
  "(61,t)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    (61,t)\<in>positive_meaning record_instantiation_system"
  "(347,t)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    (347,t)\<in>positive_meaning binding_observation_program"
  using binding_record_old_meaning[of 125 t] binding_record_base_reference[of 125 t]
    binding_record_old_meaning[of 61 t] binding_record_base_reference[of 61 t]
    substitution_reading_old_meaning[of 61 t] substitution_reading_components(2)[of t]
    binding_record_old_meaning[of 347 t] binding_record_base_observation[of 347 t] by auto

lemma binding_record_valuation:
  "(348,z)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11}. term_formed (h j)) \<and>
      z=binding_record_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) \<and>
      (125,reference_bindings_value (h 3) (h 8) (h 9))\<in>positive_meaning reference_bindings_system \<and>
      (61,pattern_instantiation_argument (h 0) (h 1) (h 3) (h 8) (h 2) (h 10) (h 3) (h 6) (h 7))
        \<in>positive_meaning record_instantiation_system \<and>
      (61,pattern_instantiation_argument (h 0) (h 1) (h 3) (h 9) (h 2) (h 11) (h 3) (h 6) (h 7))
        \<in>positive_meaning record_instantiation_system \<and>
      (347,binding_observation_argument (h 4) (h 5) (h 10) (h 11))\<in>positive_meaning binding_observation_program)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: binding_record_clause binding_record_schema_def schema_variables_def
      binding_record_call binding_record_readers)

definition binding_record_calls where
  "binding_record_calls e u r b owner bs i k \<longleftrightarrow>
    (\<exists>xb yb xs ys.
      (125,reference_bindings_value b xb yb)\<in>positive_meaning reference_bindings_system \<and>
      (61,pattern_instantiation_argument e u b xb r xs b i k)\<in>positive_meaning record_instantiation_system \<and>
      (61,pattern_instantiation_argument e u b yb r ys b i k)\<in>positive_meaning record_instantiation_system \<and>
      (347,binding_observation_argument owner bs xs ys)\<in>positive_meaning binding_observation_program)"

theorem binding_record_at_arguments:
  "(348,binding_record_argument e u r b owner bs i k)\<in>positive_meaning binding_record_system \<longleftrightarrow>
    binding_record_calls e u r b owner bs i k"
proof
  assume "(348,binding_record_argument e u r b owner bs i k)\<in>positive_meaning binding_record_system"
  then show "binding_record_calls e u r b owner bs i k"
    by (simp only: binding_record_valuation factor_term.inject binding_record_calls_def) blast
next
  assume "binding_record_calls e u r b owner bs i k"
  then obtain xb yb xs ys where calls:
    "(125,reference_bindings_value b xb yb)\<in>positive_meaning reference_bindings_system"
    "(61,pattern_instantiation_argument e u b xb r xs b i k)\<in>positive_meaning record_instantiation_system"
    "(61,pattern_instantiation_argument e u b yb r ys b i k)\<in>positive_meaning record_instantiation_system"
    "(347,binding_observation_argument owner bs xs ys)\<in>positive_meaning binding_observation_program"
    by (auto simp: binding_record_calls_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then b
    else if j=4 then owner else if j=5 then bs else if j=6 then i else if j=7 then k
    else if j=8 then xb else if j=9 then yb else if j=10 then xs else ys"
  show "(348,binding_record_argument e u r b owner bs i k)\<in>positive_meaning binding_record_system"
    by (simp only: binding_record_valuation; rule exI[of _ ?h])
      (use calls schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF calls(4)]] in auto)
qed

definition binding_record_result :: "factor_term\<Rightarrow>bool" where
  "binding_record_result z \<longleftrightarrow>
    (\<exists>e u r b owner bs i k. z=binding_record_argument e u r b owner bs i k \<and>
      binding_record_calls e u r b owner bs i k)"

theorem binding_record_exact:
  "(348,z)\<in>positive_meaning binding_record_system \<longleftrightarrow> binding_record_result z"
  using binding_record_valuation[of z] binding_record_at_arguments
  by (auto simp only: binding_record_result_def; blast)

text \<open>
  The same source, binder list, and support occur in both record readings.
  Their complete outputs become the two observations of the supplied rows.
  The disjoint program union preserves every original definition; all four
  premises and the new conclusion use the ordinary positive semantics.
\<close>

end
