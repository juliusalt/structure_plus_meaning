theory Factor_Reference_Bindings
  imports Factor_Definition_Call_Admission
begin

section \<open>One binder list supplies both reference substitutions\<close>

abbreviation reference_bindings_value ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "reference_bindings_value v x y \<equiv> Pair_Term v (Pair_Term x y)"

abbreviation reference_bindings_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "reference_bindings_pattern v x y \<equiv> Pattern_Pair v (Pattern_Pair x y)"

definition reference_bindings_nil_schema :: "(nat,nat,nat) factor_schema" where
  "reference_bindings_nil_schema=data_rule
    (reference_bindings_pattern (Pattern_Payload []) (Pattern_Payload []) (Pattern_Payload [])) {}"

definition reference_bindings_cons_schema :: "(nat,nat,nat) factor_schema" where
  "reference_bindings_cons_schema=data_rule
    (reference_bindings_pattern (Pattern_Pair data_x data_y)
      (Pattern_Pair (Pattern_Pair data_x data_x) data_z)
      (Pattern_Pair (Pattern_Pair data_x (Pattern_Target (Whole_Artifact empty_artifact))) data_w))
    {(0,1,data_list_pattern [data_x]),(1,125,reference_bindings_pattern data_y data_z data_w)}"

definition reference_bindings_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "reference_bindings_clauses={(0,reference_bindings_nil_schema),(1,reference_bindings_cons_schema)}"

definition reference_bindings_system :: "(nat,nat,nat,nat) schema_system" where
  "reference_bindings_system=add_view_definition definition_call_admission_system 125 data_x reference_bindings_clauses"

lemma reference_bindings_system_formed [simp]: "schema_system_formed reference_bindings_system"
  unfolding reference_bindings_system_def
  by (rule add_recursive_definition_formed[OF definition_call_admission_system_formed])
    (auto simp: reference_bindings_clauses_def reference_bindings_nil_schema_def reference_bindings_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma reference_bindings_definitions [simp]:
  "system_definitions reference_bindings_system=insert 125 (system_definitions definition_call_admission_system)"
  by (simp add: reference_bindings_system_def)

lemma reference_bindings_call:
  "schema_call_formed reference_bindings_system d t \<longleftrightarrow>
    d\<in>system_definitions reference_bindings_system \<and> term_formed t"
  using added_variable_calls[OF definition_call_admission_system_formed
    reference_bindings_system_formed[unfolded reference_bindings_system_def] definition_call_admission_call]
  by (simp only: reference_bindings_system_def[symmetric])

lemma reference_bindings_old_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning reference_bindings_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning definition_call_admission_system"
  using added_definition_preserves_old(2)[OF definition_call_admission_system_formed
    reference_bindings_system_formed[unfolded reference_bindings_system_def], of d t] assms
  by (auto simp: reference_bindings_system_def)

lemma reference_bindings_clause [simp]:
  "((125,c),S)\<in>system_clauses reference_bindings_system \<longleftrightarrow>
    (c,S)\<in>reference_bindings_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_call_admission_system \<Longrightarrow>
    d\<in>system_definitions definition_call_admission_system" for d c S
    using definition_call_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((125,c),S)\<notin>system_clauses definition_call_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: reference_bindings_system_def)
qed

lemma reference_bindings_payload:
  "(1,t)\<in>positive_meaning reference_bindings_system \<longleftrightarrow>
    (1,t)\<in>positive_meaning distinct_payloads_system"
  using reference_bindings_old_meaning[of 1 t] definition_call_admission_instantiation_meaning[of 1 t]
    schema_instantiation_pattern_meaning[of 1 t] pattern_instantiation_components(11)[of t] by auto

abbreviation reference_bindings_result :: "factor_term \<Rightarrow> bool" where
  "reference_bindings_result z \<equiv> \<exists>Vs. (\<forall>a\<in>set Vs. octets_formed a) \<and>
    z=reference_bindings_value (data_list_term (map Payload_Term Vs))
      (binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs))
      (binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs))"

lemma reference_bindings_rule:
  assumes clause: "(c,S)\<in>reference_bindings_clauses"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning reference_bindings_system"
  shows "(125,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning reference_bindings_system"
proof -
  have member: "((125,c),S)\<in>system_clauses reference_bindings_system" using clause by simp
  have sf: "schema_formed S"
    using member reference_bindings_system_formed unfolding schema_system_formed_def by blast
  have ordinary: "schema_material_premises S={}" using clause
    by (auto simp: reference_bindings_clauses_def reference_bindings_nil_schema_def reference_bindings_cons_schema_def)
  have target: "schema_call_formed reference_bindings_system 125 (evaluate_pattern f (schema_conclusion S))"
    using evaluate_pattern_formed[of "schema_conclusion S" f] sf assignment
    by (auto simp: reference_bindings_call schema_formed_def schema_variables_def)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment target support])
qed

theorem reference_bindings_sound:
  assumes holds: "(125,z)\<in>positive_meaning reference_bindings_system"
  shows "reference_bindings_result z"
proof -
  have invariant: "(125::nat)=125 \<longrightarrow> reference_bindings_result z"
  proof (rule positive_valuation_induct[OF holds,
      where property="\<lambda>d t. d=125 \<longrightarrow> reference_bindings_result t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses reference_bindings_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed reference_bindings_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning reference_bindings_system \<and>
        (e=125 \<longrightarrow> reference_bindings_result (evaluate_pattern f p))"
    show "d=125 \<longrightarrow> reference_bindings_result (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=125"
      then have alternatives: "S=reference_bindings_nil_schema \<or> S=reference_bindings_cons_schema"
        using clause by (auto simp: reference_bindings_clauses_def)
      then show "reference_bindings_result (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=reference_bindings_nil_schema"
        show ?thesis by (rule exI[of _ "[]"]) (simp add: schema reference_bindings_nil_schema_def)
      next
        assume schema: "S=reference_bindings_cons_schema"
        have head_call: "(1,data_list_term [f 0])\<in>positive_meaning reference_bindings_system"
          using support[rule_format, of 0 1 "data_list_pattern [data_x]"] schema
          by (simp add: reference_bindings_cons_schema_def)
        have payload: "(1,data_list_term [f 0])\<in>positive_meaning distinct_payloads_system"
          using head_call by (simp only: reference_bindings_payload)
        obtain a where head: "f 0=Payload_Term a" "octets_formed a"
          using distinct_payload_term_list_sound[OF payload] by auto
        obtain Vs where tail: "\<forall>a\<in>set Vs. octets_formed a"
          "f 1=data_list_term (map Payload_Term Vs)"
          "f 2=binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs)"
          "f 3=binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)"
          using support[rule_format, of 1 125 "reference_bindings_pattern data_y data_z data_w"] schema
          by (auto simp: reference_bindings_cons_schema_def)
        show ?thesis by (rule exI[of _ "a#Vs"])
          (use head tail in \<open>simp add: schema reference_bindings_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem reference_bindings_complete:
  assumes "\<forall>a\<in>set Vs. octets_formed a"
  shows "(125,reference_bindings_value (data_list_term (map Payload_Term Vs))
      (binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs))
      (binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)))
    \<in>positive_meaning reference_bindings_system"
  using assms
proof (induction Vs)
  case Nil
  have result: "(125,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion reference_bindings_nil_schema))
      \<in>positive_meaning reference_bindings_system"
    by (rule reference_bindings_rule[where c=0])
      (auto simp: reference_bindings_clauses_def reference_bindings_nil_schema_def schema_variables_def)
  show ?case using result by (simp add: reference_bindings_nil_schema_def)
next
  case (Cons a Vs)
  have address: "octets_formed a" and tail_formed: "\<forall>b\<in>set Vs. octets_formed b" using Cons.prems by auto
  have tail: "(125,reference_bindings_value (data_list_term (map Payload_Term Vs))
      (binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs))
      (binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)))
      \<in>positive_meaning reference_bindings_system"
    by (rule Cons.IH[OF tail_formed])
  have payload: "(1,data_list_term [Payload_Term a])\<in>positive_meaning reference_bindings_system"
    using address by (simp only: reference_bindings_payload payload_recognition_exact) auto
  let ?f="\<lambda>j::nat. if j=0 then Payload_Term a else if j=1 then data_list_term (map Payload_Term Vs)
    else if j=2 then binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs)
    else binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)"
  have result: "(125,evaluate_pattern ?f (schema_conclusion reference_bindings_cons_schema))
      \<in>positive_meaning reference_bindings_system"
    by (rule reference_bindings_rule[where c=1])
      (use payload tail address tail_formed in \<open>auto simp: reference_bindings_clauses_def
        reference_bindings_cons_schema_def schema_variables_def binding_rows_term_formed data_list_term_formed\<close>)
  show ?case using result by (simp add: reference_bindings_cons_schema_def)
qed

theorem reference_bindings_exact:
  "(125,z)\<in>positive_meaning reference_bindings_system \<longleftrightarrow> reference_bindings_result z"
  using reference_bindings_sound reference_bindings_complete by blast

corollary reference_bindings_at_list:
  "(125,reference_bindings_value (data_list_term (map Payload_Term Vs)) x y)
      \<in>positive_meaning reference_bindings_system \<longleftrightarrow>
    (\<forall>a\<in>set Vs. octets_formed a) \<and>
    x=binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs) \<and>
    y=binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)"
  by (simp only: reference_bindings_exact factor_term.inject data_list_term_injective
    injective_mapped_lists[OF payload_term_inj]) blast

text \<open>
  The two ordinary clauses traverse one complete binder list and both
  substitution tables together. The first table pairs each address with its
  own payload. The second uses that identical address and one formed target.
  Termination is checked in all three fields.

  These clauses retain list occurrences, including repeated addresses.
  Schema instantiation separately requires a distinct complete binding table;
  that requirement supplies binder distinctness in the schema reader.
  The two private tables use the public binder enumeration and add no
  independent ordering or value to the reported schema.
\<close>

end
