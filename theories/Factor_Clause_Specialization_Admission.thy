theory Factor_Clause_Specialization_Admission
  imports Factor_Clause_Specialization_Readings
begin

section \<open>Three existing checks establish the actual symbolic clause instance\<close>

abbreviation clause_specialization_reading_pattern where
  "clause_specialization_reading_pattern e u r d c f v q g w t \<equiv>
    Pattern_Pair (package_subject_pattern e u r (Pattern_Pair d c))
      (Pattern_Pair (Pattern_Pair f (Pattern_Pair v q)) (Pattern_Pair g (Pattern_Pair w t)))"

definition clause_specialization_reading_schema :: "(nat,nat,nat) factor_schema" where
  "clause_specialization_reading_schema=data_rule
    (clause_specialization_reading_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
      (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11))
    {(0,81,citation_observation_pattern data_x data_w (Pattern_Variable 4)
       (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 12))),
     (1,291,substitution_reading_pattern data_x data_w (Pattern_Variable 12)
       (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
       (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)),
     (2,293,pattern_call_reading_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4))
       (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11))}"

definition clause_specialization_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "clause_specialization_reading_system=add_view_definition schema_pattern_reading_system 294 data_x
    {(0,clause_specialization_reading_schema)}"

interpretation clause_specialization_reading_view:
  positive_view schema_pattern_reading_system 294 data_x "{(0,clause_specialization_reading_schema)}"
  by (rule positive_view.intro)
    (auto simp: clause_specialization_reading_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma clause_specialization_reading_system_formed [simp]: "schema_system_formed clause_specialization_reading_system"
  using clause_specialization_reading_view.formed by (simp only: clause_specialization_reading_system_def)

lemma clause_specialization_reading_definitions [simp]:
  "system_definitions clause_specialization_reading_system=insert 294 (system_definitions schema_pattern_reading_system)"
  by (simp add: clause_specialization_reading_system_def)

lemma clause_specialization_reading_call:
  "schema_call_formed clause_specialization_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions clause_specialization_reading_system \<and> term_formed t"
  using added_variable_calls[OF schema_pattern_reading_system_formed
    clause_specialization_reading_system_formed[unfolded clause_specialization_reading_system_def] schema_pattern_reading_call]
  by (simp only: clause_specialization_reading_system_def[symmetric])

lemma clause_specialization_reading_old_meaning:
  assumes "d\<in>system_definitions schema_pattern_reading_system"
  shows "(d,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning schema_pattern_reading_system"
  using clause_specialization_reading_view.old_meaning[OF assms] by (simp only: clause_specialization_reading_system_def)

lemma clause_specialization_reading_clause [simp]:
  "((294,c),S)\<in>system_clauses clause_specialization_reading_system \<longleftrightarrow>
    c=0 \<and> S=clause_specialization_reading_schema"
  using clause_specialization_reading_view.no_old_clause by (auto simp: clause_specialization_reading_system_def)

lemma clause_specialization_reading_components:
  "(81,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (81,t)\<in>positive_meaning definition_clause_reading_system"
  "(291,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (291,t)\<in>positive_meaning substitution_reading_system"
  "(293,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (293,t)\<in>positive_meaning schema_pattern_reading_system"
  using clause_specialization_reading_old_meaning[of 81 t] schema_pattern_reading_list_meaning[of 81 t]
    program_call_list_old_meaning[of 81 t] application_admission_old_meaning[of 81 t]
    program_call_admission_old_meaning[of 81 t] package_membership_old_meaning[of 81 t]
    definition_edge_reading_old_meaning[of 81 t]
    clause_specialization_reading_old_meaning[of 291 t] schema_pattern_reading_pattern_meaning[of 291 t]
    pattern_call_reading_old_meaning[of 291 t] pattern_call_base_substitution_meaning[of 291 t]
    clause_specialization_reading_old_meaning[of 293 t] by auto

lemma clause_specialization_reading_valuation:
  "(294,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}. term_formed (h j)) \<and>
      z=clause_specialization_reading_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) \<and>
      (81,citation_observation_argument (h 0) (h 3) (h 4) (Pair_Term (h 5) (h 12)))\<in>positive_meaning definition_clause_reading_system \<and>
      (291,substitution_reading_argument (h 0) (h 3) (h 12) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11))\<in>positive_meaning substitution_reading_system \<and>
      (293,pattern_call_reading_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)) (h 9) (h 10) (h 11))\<in>positive_meaning schema_pattern_reading_system)"
proof -
  have ordinary: "schema_material_premises clause_specialization_reading_schema={}"
    by (simp add: clause_specialization_reading_schema_def)
  have accepts: "schema_call_formed clause_specialization_reading_system 294
      (evaluate_pattern h (schema_conclusion clause_specialization_reading_schema))"
    if "\<forall>a\<in>schema_variables clause_specialization_reading_schema. term_formed (h a)" for h
    using that by (auto simp: clause_specialization_reading_call clause_specialization_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF clause_specialization_reading_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: clause_specialization_reading_schema_def schema_variables_def clause_specialization_reading_components
      conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem clause_specialization_reading_at_arguments:
  "(294,clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    clause_specialization_reading_calls e u r du dr c f v q g w t"
proof
  assume admitted: "(294,clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)\<in>positive_meaning clause_specialization_reading_system"
  obtain h :: "nat\<Rightarrow>factor_term" where boundary:
    "e=h 0"
    "u=h 1"
    "r=h 2"
    "du=h 3"
    "dr=h 4"
    "c=h 5"
    "f=h 6"
    "v=h 7"
    "q=h 8"
    "g=h 9"
    "w=h 10"
    "t=h 11"
    and calls:
    "(81,citation_observation_argument (h 0) (h 3) (h 4) (Pair_Term (h 5) (h 12)))\<in>positive_meaning definition_clause_reading_system"
    "(291,substitution_reading_argument (h 0) (h 3) (h 12) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11))\<in>positive_meaning substitution_reading_system"
    "(293,pattern_call_reading_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)) (h 9) (h 10) (h 11))\<in>positive_meaning schema_pattern_reading_system"
    using admitted by (simp only: clause_specialization_reading_valuation factor_term.inject) blast
  show "clause_specialization_reading_calls e u r du dr c f v q g w t" unfolding clause_specialization_reading_calls_def
    by (rule exI[of _ "h 12"])
      (use boundary calls in simp)
next
  assume reads: "clause_specialization_reading_calls e u r du dr c f v q g w t"
  obtain a where calls:
    "(81,citation_observation_argument e du dr (Pair_Term c a))\<in>positive_meaning definition_clause_reading_system"
    "(291,substitution_reading_argument e du a f v q g w t)\<in>positive_meaning substitution_reading_system"
    "(293,pattern_call_reading_argument e u r (Pair_Term du dr) g w t)\<in>positive_meaning schema_pattern_reading_system"
    using reads by (auto simp: clause_specialization_reading_calls_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then r else if j=3 then du else if j=4 then dr else if j=5 then c else if j=6 then f else if j=7 then v else if j=8 then q else if j=9 then g else if j=10 then w else if j=11 then t else a"
  show "(294,clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t)\<in>positive_meaning clause_specialization_reading_system"
    by (simp only: clause_specialization_reading_valuation; rule exI[of _ ?h])
      (use calls schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]] schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]] schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] in auto)
qed

theorem clause_specialization_reading_exact:
  "(294,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow> clause_specialization_reading_result z"
proof
  assume admitted: "(294,z)\<in>positive_meaning clause_specialization_reading_system"
  obtain e u r du dr c f v q g w t where shape: "z=clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t"
    using admitted by (simp only: clause_specialization_reading_valuation) blast
  show "clause_specialization_reading_result z" using admitted
    by (simp only: shape clause_specialization_reading_at_arguments clause_specialization_reading_calls_result)
next
  assume result: "clause_specialization_reading_result z"
  obtain e u r du dr c f v q g w t where shape: "z=clause_specialization_reading_argument e u r (Pair_Term du dr) c f v q g w t"
    using result unfolding clause_specialization_reading_result_def site_data_term_def by blast
  show "(294,z)\<in>positive_meaning clause_specialization_reading_system" using result
    by (simp only: shape clause_specialization_reading_at_arguments clause_specialization_reading_calls_result)
qed

corollary clause_specialization_reading_on_sources:
  assumes "environment_value_presents E e" "environment_value_presents F f" "environment_value_presents G g"
  shows "(294,clause_specialization_reading_argument e (use_data_term u) (Payload_Term r)
      (definition_site_value d) (Payload_Term c) f (use_data_term v) (Payload_Term q)
      g (use_data_term w) (Payload_Term t))\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    schema_clause_specialization_at E u r d c F v q G w t"
  by (cases d) (simp only: site_data_term_def fst_conv snd_conv clause_specialization_reading_at_arguments
    clause_specialization_readings_exact[OF assms])

corollary clause_specialization_retains_readers:
  "(291,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow> substitution_reading_result z"
  "(292,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow> pattern_call_reading_result z"
  "(293,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow> schema_pattern_reading_result z"
  using clause_specialization_reading_components(2)[of z] substitution_reading_exact[of z]
    clause_specialization_reading_old_meaning[of 292 z] schema_pattern_reading_pattern_meaning[of 292 z]
    pattern_call_reading_exact[of z] clause_specialization_reading_components(3)[of z]
    schema_pattern_reading_exact[of z] by auto

section \<open>One compiled program checks both boundaries before all future inputs\<close>

theorem fixed_native_schema_specialization_checker:
  "\<exists>B :: local_address option artifact_environment. \<exists>bu P entries.
    closed_native_package_at B bu [] P \<and>
    (\<forall>d\<in>{293::nat,294}. \<forall>z. term_formed z \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] P \<and> native_application_at G au [] (entries d) z I K \<and>
        native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow>
          (if d=293 then schema_pattern_reading_result z else clause_specialization_reading_result z)) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)))"
proof -
  obtain h :: "nat\<Rightarrow>local_address option definition_site"
    and B :: "local_address option artifact_environment" and bu P
    where closed: "closed_native_package_at B bu [] P"
    and future: "\<forall>d\<in>system_definitions clause_specialization_reading_system. \<forall>z. term_formed z \<longrightarrow>
      (\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
        native_package_at G bu [] P \<and> native_application_at G au [] (h d) z I K \<and>
        native_package_environment G bu []=B \<and>
        (native_application_formed G bu [] au [] \<longleftrightarrow> schema_call_formed clause_specialization_reading_system d z) \<and>
        (native_positive_holds G bu [] au [] \<longleftrightarrow> (d,z)\<in>positive_meaning clause_specialization_reading_system) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
        (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x))"
    using compiled_program_future_applications[OF clause_specialization_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have cases: "d=293 \<or> d=294" if "d\<in>{293,294}" for d :: nat using that by auto
  have meaning: "(d,z)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
      (if d=293 then schema_pattern_reading_result z else clause_specialization_reading_result z)"
    if "d\<in>{293,294}" for d z
    using cases[OF that] clause_specialization_retains_readers(3)[of z] clause_specialization_reading_exact[of z] by auto
  have instances: "\<exists>G au I K. environment_formed G \<and> environment_included B G \<and> au\<notin>environment_uses B \<and>
      native_package_at G bu [] P \<and> native_application_at G au [] (h d) z I K \<and>
      native_package_environment G bu []=B \<and> native_application_formed G bu [] au [] \<and>
      (native_positive_holds G bu [] au [] \<longleftrightarrow>
        (if d=293 then schema_pattern_reading_result z else clause_specialization_reading_result z)) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>A. artifact_at G v A \<longleftrightarrow> artifact_at B v A) \<and>
      (\<forall>v\<in>environment_uses B. \<forall>s x. binds_slot G v s x \<longleftrightarrow> binds_slot B v s x)"
    if member: "d\<in>{293,294}" and formed: "term_formed z" for d z
  proof -
    have entry: "d\<in>system_definitions clause_specialization_reading_system" using cases[OF member] by auto
    show ?thesis using future[rule_format, OF entry formed] entry formed
      by (simp only: clause_specialization_reading_call meaning[OF member]) auto
  qed
  show ?thesis by (rule exI[of _ B], rule exI[of _ bu], rule exI[of _ P], rule exI[of _ h])
    (use closed instances in blast)
qed

text \<open>
  The new clause invokes the existing clause-root and substitution readers
  and the complete schema boundary check. Exactness recovers the actual
  package, clause occurrence, replacement record, and target schema from
  every admitted input. The original substitution and symbolic-call
  operations keep their meanings.

  One closed native program supplies both new entries before all future
  arguments. Complete graph admission still requires every node, its exact
  discharges, shared target-variable identities, and assertion boundary.
\<close>

end
