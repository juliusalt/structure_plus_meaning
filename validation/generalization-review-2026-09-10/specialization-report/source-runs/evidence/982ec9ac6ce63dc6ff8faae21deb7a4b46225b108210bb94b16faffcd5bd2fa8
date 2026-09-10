theory Factor_Specialization_Reports
  imports Factor_Clause_Specialization_Contracts
begin

section \<open>A checked specialization exposes its complete target report\<close>

abbreviation specialization_report_value where
  "specialization_report_value a d c b q v \<equiv>
    Pair_Term (Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q)) v"

abbreviation specialization_report_pattern where
  "specialization_report_pattern a d c b q v \<equiv>
    Pattern_Pair (Pattern_Pair (Pattern_Pair a (Pattern_Pair d c)) (Pattern_Pair b q)) v"

definition specialization_report_schema :: "(nat,nat,nat) factor_schema" where
  "specialization_report_schema=data_rule
    (specialization_report_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5))
    {(0,294,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
       (Pattern_Pair data_w (Pattern_Variable 4))),
     (1,126,Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))}"

definition specialization_report_system :: "(nat,nat,nat,nat) schema_system" where
  "specialization_report_system=add_view_definition clause_specialization_reading_system
    342 data_x {(0,specialization_report_schema)}"

interpretation specialization_report_view:
  positive_view clause_specialization_reading_system 342 data_x "{(0,specialization_report_schema)}"
  by (rule positive_view.intro)
    (auto simp: specialization_report_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma specialization_report_formed [simp]: "schema_system_formed specialization_report_system"
  using specialization_report_view.formed by (simp only: specialization_report_system_def)

lemma specialization_report_definitions [simp]:
  "system_definitions specialization_report_system=insert 342 (system_definitions clause_specialization_reading_system)"
  by (simp add: specialization_report_system_def)

lemma specialization_report_call:
  "schema_call_formed specialization_report_system d t \<longleftrightarrow>
    d\<in>system_definitions specialization_report_system \<and> term_formed t"
  using added_variable_calls[OF clause_specialization_reading_system_formed
    specialization_report_formed[unfolded specialization_report_system_def] clause_specialization_reading_call]
  by (simp only: specialization_report_system_def[symmetric])

lemma specialization_report_old_meaning:
  assumes "d\<in>system_definitions clause_specialization_reading_system"
  shows "(d,t)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning clause_specialization_reading_system"
  using specialization_report_view.old_meaning[OF assms]
  by (simp only: specialization_report_system_def)

lemma specialization_report_clause [simp]:
  "((342,c),S)\<in>system_clauses specialization_report_system \<longleftrightarrow>
    c=0 \<and> S=specialization_report_schema"
  using specialization_report_view.no_old_clause
  by (auto simp: specialization_report_system_def)

lemma specialization_report_components:
  "(294,t)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (294,t)\<in>positive_meaning clause_specialization_reading_system"
  "(126,t)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (126,t)\<in>positive_meaning clause_specialization_reading_system"
  by (rule specialization_report_old_meaning; simp)+

lemma specialization_report_valuation:
  "(342,z)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5}. term_formed (h j)) \<and>
      z=specialization_report_value (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) \<and>
      (294,Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (Pair_Term (h 3) (h 4)))
        \<in>positive_meaning clause_specialization_reading_system \<and>
      (126,Pair_Term (h 4) (h 5))\<in>positive_meaning clause_specialization_reading_system)"
proof -
  have ordinary: "schema_material_premises specialization_report_schema={}"
    by (simp add: specialization_report_schema_def)
  have accepts: "schema_call_formed specialization_report_system 342
      (evaluate_pattern h (schema_conclusion specialization_report_schema))"
    if "\<forall>a\<in>schema_variables specialization_report_schema. term_formed (h a)" for h
    using that by (auto simp: specialization_report_call specialization_report_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF specialization_report_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: specialization_report_schema_def schema_variables_def specialization_report_components
      conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem specialization_report_at_arguments:
  "(342,specialization_report_value a d c b q v)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (294,Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q))
      \<in>positive_meaning clause_specialization_reading_system \<and>
    (126,Pair_Term q v)\<in>positive_meaning clause_specialization_reading_system"
proof
  assume admitted: "(342,specialization_report_value a d c b q v)\<in>positive_meaning specialization_report_system"
  show "(294,Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q))
      \<in>positive_meaning clause_specialization_reading_system \<and>
    (126,Pair_Term q v)\<in>positive_meaning clause_specialization_reading_system"
    using admitted by (simp only: specialization_report_valuation factor_term.inject) blast
next
  assume reads: "(294,Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q))
      \<in>positive_meaning clause_specialization_reading_system \<and>
    (126,Pair_Term q v)\<in>positive_meaning clause_specialization_reading_system"
  let ?h="\<lambda>j::nat. if j=0 then a else if j=1 then d else if j=2 then c else if j=3 then b else if j=4 then q else v"
  have formed: "term_formed a" "term_formed d" "term_formed c" "term_formed b" "term_formed q" "term_formed v"
    using reads positive_meaning_formed[of 294 "Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q)"
      clause_specialization_reading_system]
      positive_meaning_formed[of 126 "Pair_Term q v" clause_specialization_reading_system]
    by (auto dest: schema_call_formed_target)
  show "(342,specialization_report_value a d c b q v)\<in>positive_meaning specialization_report_system"
    by (simp only: specialization_report_valuation; rule exI[of _ ?h]) (use reads formed in auto)
qed

definition specialization_report_result :: "factor_term\<Rightarrow>bool" where
  "specialization_report_result z \<longleftrightarrow>
    (\<exists>a d c b q v. z=specialization_report_value a d c b q v \<and>
      (294,Pair_Term (Pair_Term a (Pair_Term d c)) (Pair_Term b q))
        \<in>positive_meaning clause_specialization_reading_system \<and>
      (126,Pair_Term q v)\<in>positive_meaning clause_specialization_reading_system)"

theorem specialization_report_exact:
  "(342,z)\<in>positive_meaning specialization_report_system \<longleftrightarrow> specialization_report_result z"
  using specialization_report_valuation[of z] specialization_report_at_arguments
  by (auto simp only: specialization_report_result_def; blast)

lemma specialization_report_reference_meaning:
  "(126,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (126,z)\<in>positive_meaning schema_reading_system"
  using clause_specialization_reading_old_meaning[of 126 z]
    schema_pattern_reading_components(1)[of z] by auto

theorem specialization_report_on_sources:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
  shows "(342,Pair_Term
      (clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) f (use_data_term v) (Payload_Term q)
        g (use_data_term w) (Payload_Term t)) z)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    schema_clause_specialization_at E u r d c F v q G w t \<and>
      (\<exists>T. native_schema_at G w t T \<and> schema_reference_presents T z)"
  by (simp only: specialization_report_at_arguments
    clause_specialization_reading_on_sources[OF sources] specialization_report_reference_meaning
    schema_reading_on_values[OF sources(3)])

corollary specialization_report_at_target:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
    and target: "native_schema_at G w t T"
  shows "(342,Pair_Term
      (clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) f (use_data_term v) (Payload_Term q)
        g (use_data_term w) (Payload_Term t)) z)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    schema_clause_specialization_at E u r d c F v q G w t \<and> schema_reference_presents T z"
  by (simp only: specialization_report_on_sources[OF sources])
    (use target native_schema_unique[OF _ target] in blast)

corollary specialization_report_presentation_invariance:
  assumes sources: "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
    and first: "schema_reference_presents T x" and second: "schema_reference_presents T y"
    and target: "native_schema_at G w t T"
  shows "(342,Pair_Term
      (clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) f (use_data_term v) (Payload_Term q)
        g (use_data_term w) (Payload_Term t)) x)\<in>positive_meaning specialization_report_system \<longleftrightarrow>
    (342,Pair_Term
      (clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
        (definition_site_value d) (Payload_Term c) f (use_data_term v) (Payload_Term q)
        g (use_data_term w) (Payload_Term t)) y)\<in>positive_meaning specialization_report_system"
  by (simp only: specialization_report_at_target[OF sources target] first second)

text \<open>
  The report belongs to exactly the target site checked by the complete clause
  specialization reader. A report from a different schema cannot be substituted
  by selecting it independently. Both readers are ordinary clauses in the same
  program. The report contains all variable, premise, and material fields; the
  operation does not decide whether any remaining material condition is true.
\<close>

end
