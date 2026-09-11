theory Factor_Schema_Reading
  imports Factor_Schema_Observations Factor_Reference_Bindings
begin

section \<open>The source site and the complete reference report are separate operands\<close>

abbreviation schema_reference_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "schema_reference_argument e u r v \<equiv> Pair_Term (Pair_Term e (Pair_Term u r)) v"

definition schema_reading_schema :: "(nat,nat,nat) factor_schema" where
  "schema_reading_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z))
      (schema_reference_pattern data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)
        (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)))
    {(0,125,reference_bindings_pattern data_w (Pattern_Variable 10) (Pattern_Variable 11)),
     (1,65,schema_instantiation_pattern data_x data_y data_z (Pattern_Variable 10)
       (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)),
     (2,65,schema_instantiation_pattern data_x data_y data_z (Pattern_Variable 11)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9))}"

definition schema_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_reading_system=add_view_definition reference_bindings_system 126 data_x {(0,schema_reading_schema)}"

interpretation schema_reading_view: positive_view reference_bindings_system 126 data_x "{(0,schema_reading_schema)}"
  by (rule positive_view.intro)
    (auto simp: schema_reading_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_reading_system_formed [simp]: "schema_system_formed schema_reading_system"
  using schema_reading_view.formed by (simp only: schema_reading_system_def)

lemma schema_reading_definitions [simp]:
  "system_definitions schema_reading_system=insert 126 (system_definitions reference_bindings_system)"
  by (simp add: schema_reading_system_def)

lemma schema_reading_call:
  "schema_call_formed schema_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_reading_system \<and> term_formed t"
  using added_variable_calls[OF reference_bindings_system_formed
    schema_reading_system_formed[unfolded schema_reading_system_def] reference_bindings_call]
  by (simp only: schema_reading_system_def[symmetric])

lemma schema_reading_old_meaning:
  assumes "d\<in>system_definitions reference_bindings_system"
  shows "(d,t)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning reference_bindings_system"
  using schema_reading_view.old_meaning[OF assms]
  by (simp only: schema_reading_system_def)

lemma schema_reading_clause [simp]:
  "((126,c),S)\<in>system_clauses schema_reading_system \<longleftrightarrow> c=0 \<and> S=schema_reading_schema"
  using schema_reading_view.no_old_clause
  by (auto simp: schema_reading_system_def)

lemma schema_reading_components:
  "(125,t)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (125,t)\<in>positive_meaning reference_bindings_system"
  "(65,t)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (65,t)\<in>positive_meaning schema_instantiation_system"
  using schema_reading_old_meaning[of 125 t] schema_reading_old_meaning[of 65 t]
    reference_bindings_old_meaning[of 65 t] definition_call_admission_instantiation_meaning[of 65 t] by auto

lemma schema_reading_valuation:
  "(126,z)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11}. term_formed (h j)) \<and>
      z=schema_reference_argument (h 0) (h 1) (h 2)
        (schema_reference_value (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)) \<and>
      (125,reference_bindings_value (h 3) (h 10) (h 11))\<in>positive_meaning reference_bindings_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 10) (h 4) (h 5) (h 6))
        \<in>positive_meaning schema_instantiation_system \<and>
      (65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 11) (h 7) (h 8) (h 9))
        \<in>positive_meaning schema_instantiation_system)"
proof -
  have ordinary: "schema_material_premises schema_reading_schema={}"
    by (simp add: schema_reading_schema_def)
  have accepts: "schema_call_formed schema_reading_system 126
      (evaluate_pattern h (schema_conclusion schema_reading_schema))"
    if "\<forall>a\<in>schema_variables schema_reading_schema. term_formed (h a)" for h
    using that by (auto simp: schema_reading_call schema_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF schema_reading_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: schema_reading_schema_def schema_variables_def schema_reading_components
      conj_ac all_conj_distrib imp_conjL)
    done
qed

abbreviation schema_reading_result :: "factor_term \<Rightarrow> bool" where
  "schema_reading_result z \<equiv> \<exists>E u r S p v.
    z=Pair_Term p v \<and> site_value_presents E u r p \<and>
    native_schema_at E u r S \<and> schema_reference_presents S v"

lemma native_schema_position:
  assumes "native_schema_at E u r S"
  shows "(u,r)\<in>environment_positions E"
  using assms by (auto simp: native_schema_at_def record_at_def)

theorem schema_reading_sound:
  assumes holds: "(126,z)\<in>positive_meaning schema_reading_system"
  shows "schema_reading_result z"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where shape:
    "z=schema_reference_argument (h 0) (h 1) (h 2)
      (schema_reference_value (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9))"
    and reads:
      "(125,reference_bindings_value (h 3) (h 10) (h 11))\<in>positive_meaning reference_bindings_system"
      "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 10) (h 4) (h 5) (h 6))
        \<in>positive_meaning schema_instantiation_system"
      "(65,schema_instantiation_argument (h 0) (h 1) (h 2) (h 11) (h 7) (h 8) (h 9))
        \<in>positive_meaning schema_instantiation_system"
    using holds by (simp only: schema_reading_valuation) blast
  obtain Vs where variables: "\<forall>a\<in>set Vs. octets_formed a"
    and tables: "h 3=data_list_term (map Payload_Term Vs)"
      "h 10=binding_rows_term (map (\<lambda>a. (a,Payload_Term a)) Vs)"
      "h 11=binding_rows_term (map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs)"
    using reads(1) by (simp only: reference_bindings_exact factor_term.inject) blast
  obtain E u r xs S qs cs where source: "environment_value_presents E (h 0)"
    and coordinates: "h 1=use_data_term u" "h 2=Payload_Term r"
    and first: "h 10=binding_rows_term xs" "h 5=call_instance_rows_term qs" "h 6=binding_rows_term cs"
      "distinct xs" "distinct qs" "distinct cs"
      "native_schema_at E u r S" "schema_instance S (set xs) (h 4) (set qs)"
      "set cs=material_instance_relation (set xs) (schema_material_premises S)"
    using reads(2) by (simp only: schema_instantiation_exact factor_term.inject) blast
  have xs: "xs=map (\<lambda>a. (a,Payload_Term a)) Vs"
    using first(1) tables(2) by (simp only: binding_rows_term_injective)
  have order: "distinct Vs" using first(4) xs by (simp add: distinct_map)
  have first_instance: "schema_instance S (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) (h 4) (set qs)"
    using first(8) by (simp only: xs set_map)
  have graph_domain: "rel_dom (image (\<lambda>a. (a,Payload_Term a)) (set Vs))=set Vs"
    by (auto simp: rel_dom_def)
  have domain: "set Vs=schema_variables S"
    using first_instance by (simp only: schema_instance_def term_bindings_formed_def graph_domain)
  obtain ws ds where second: "h 8=call_instance_rows_term ws" "h 9=binding_rows_term ds"
    "distinct ws" "distinct ds"
    "schema_instance S (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) (h 7) (set ws)"
    "set ds=material_instance_relation
      (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) (schema_material_premises S)"
    using reads(3)
    by (simp only: coordinates tables(3) schema_instantiation_outputs_at[OF source first(7)] set_map) blast
  let ?p="Pair_Term (h 0) (site_data_term u r)"
  let ?v="schema_reference_value (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9)"
  have site: "site_value_presents E u r ?p"
    using source native_schema_position[OF first(7)] by (auto simp: site_value_presents_def)
  have reference: "schema_reference_presents S ?v"
    apply (simp only: schema_reference_presents_fields)
    apply (rule conjI[OF native_schema_data_formed[OF first(7)]])
    apply (rule exI[of _ Vs], rule exI[of _ "h 4"], rule exI[of _ qs], rule exI[of _ cs],
      rule exI[of _ "h 7"], rule exI[of _ ws], rule exI[of _ ds])
    using order domain first(2,3,5,6,9) first_instance second tables(1) xs
    apply (auto simp: set_map)
    done
  show ?thesis by (rule exI[of _ E], rule exI[of _ u], rule exI[of _ r], rule exI[of _ S],
      rule exI[of _ ?p], rule exI[of _ ?v])
    (use shape coordinates site first(7) reference in \<open>simp add: site_data_term_def\<close>)
qed

theorem schema_reading_complete:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and reference: "schema_reference_presents S z"
  shows "(126,schema_reference_argument e (use_data_term u) (Payload_Term r) z)
    \<in>positive_meaning schema_reading_system"
proof -
  obtain Vs t qs cs v ws ds where data:
    "schema_data_formed S" "distinct Vs" "set Vs=schema_variables S"
    "distinct qs" "distinct cs" "distinct ws" "distinct ds"
    "schema_instance S (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) t (set qs)"
    "set cs=material_instance_relation (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) (schema_material_premises S)"
    "schema_instance S (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) v (set ws)"
    "set ds=material_instance_relation
      (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) (schema_material_premises S)"
    "z=schema_reference_value (data_list_term (map Payload_Term Vs)) t
      (call_instance_rows_term qs) (binding_rows_term cs) v (call_instance_rows_term ws) (binding_rows_term ds)"
    using schema_reference_presents_fields[THEN iffD1, OF reference]
    by (elim conjE exE) (rule that; assumption)
  let ?xs="map (\<lambda>a. (a,Payload_Term a)) Vs"
  let ?ys="map (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) Vs"
  have orders: "distinct ?xs" "distinct ?ys"
    using data(2) by (auto simp: distinct_map inj_on_def)
  have variables: "\<forall>a\<in>set Vs. octets_formed a"
    using data(1,3) by (auto simp: schema_data_formed_def)
  have tables: "(125,reference_bindings_value (data_list_term (map Payload_Term Vs))
      (binding_rows_term ?xs) (binding_rows_term ?ys))\<in>positive_meaning reference_bindings_system"
    by (rule reference_bindings_complete[OF variables])
  have first: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term ?xs) t (call_instance_rows_term qs) (binding_rows_term cs))
      \<in>positive_meaning schema_instantiation_system"
    by (rule schema_instantiation_complete[OF raw source _ orders(1) data(4,5)])
      (use data(8,9) in \<open>simp_all only: set_map\<close>)
  have second: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term ?ys) v (call_instance_rows_term ws) (binding_rows_term ds))
      \<in>positive_meaning schema_instantiation_system"
    by (rule schema_instantiation_complete[OF raw source _ orders(2) data(6,7)])
      (use data(10,11) in \<open>simp_all only: set_map\<close>)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term u else if j=2 then Payload_Term r
    else if j=3 then data_list_term (map Payload_Term Vs) else if j=4 then t
    else if j=5 then call_instance_rows_term qs else if j=6 then binding_rows_term cs else if j=7 then v
    else if j=8 then call_instance_rows_term ws else if j=9 then binding_rows_term ds
    else if j=10 then binding_rows_term ?xs else binding_rows_term ?ys"
  show ?thesis by (simp only: schema_reading_valuation; rule exI[of _ ?h])
    (use tables first second data(12)
      schema_call_formed_target[OF positive_meaning_formed[OF tables]]
      schema_call_formed_target[OF positive_meaning_formed[OF first]]
      schema_call_formed_target[OF positive_meaning_formed[OF second]] in auto)
qed

theorem schema_reading_exact:
  "(126,z)\<in>positive_meaning schema_reading_system \<longleftrightarrow> schema_reading_result z"
proof
  show "(126,z)\<in>positive_meaning schema_reading_system \<Longrightarrow> schema_reading_result z"
    by (rule schema_reading_sound)
next
  assume "schema_reading_result z"
  then obtain E u r S p v where parts: "z=Pair_Term p v" "site_value_presents E u r p"
    "native_schema_at E u r S" "schema_reference_presents S v" by blast
  obtain e where source: "environment_value_presents E e" "p=Pair_Term e (site_data_term u r)"
    using parts(2) by (auto simp: site_value_presents_def)
  show "(126,z)\<in>positive_meaning schema_reading_system"
    using schema_reading_complete[OF source(1) parts(3,4)] parts(1) source(2)
    by (simp only: site_data_term_def)
qed

corollary schema_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(126,schema_reference_argument e (use_data_term u) (Payload_Term r) v)
      \<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (\<exists>S. native_schema_at E u r S \<and> schema_reference_presents S v)"
proof
  assume holds: "(126,schema_reference_argument e (use_data_term u) (Payload_Term r) v)
    \<in>positive_meaning schema_reading_system"
  obtain F w a S p q where parts:
    "schema_reference_argument e (use_data_term u) (Payload_Term r) v=Pair_Term p q"
    "site_value_presents F w a p" "native_schema_at F w a S" "schema_reference_presents S q"
    using schema_reading_sound[OF holds] by blast
  obtain f where fields: "environment_value_presents F f" "p=Pair_Term f (site_data_term w a)"
    using parts(2) by (auto simp: site_value_presents_def)
  have same: "f=e" "w=u" "a=r" "q=v"
    using parts(1) fields(2)
    by (auto simp: site_data_term_def inj_eq[OF use_data_term_injective])
  have presented: "environment_value_presents F e" using fields(1) same(1) by simp
  have environment: "F=E" by (rule environment_value_presents_unique[OF presented source])
  show "\<exists>S. native_schema_at E u r S \<and> schema_reference_presents S v"
    by (rule exI[of _ S]) (use parts(3,4) same environment in simp)
next
  assume "\<exists>S. native_schema_at E u r S \<and> schema_reference_presents S v"
  then obtain S where parts: "native_schema_at E u r S" "schema_reference_presents S v" by blast
  show "(126,schema_reference_argument e (use_data_term u) (Payload_Term r) v)
    \<in>positive_meaning schema_reading_system"
    by (rule schema_reading_complete[OF source parts])
qed

section \<open>Admission preserves and reflects the actual schema relation\<close>

theorem schema_reading_presented_relation:
  "(126,Pair_Term p v)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    presented_relation (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      schema_reference_presents
      (\<lambda>z S. native_schema_at (fst z) (fst (snd z)) (snd (snd z)) S) p v"
  by (auto simp: schema_reading_exact presented_relation_def; metis fst_conv snd_conv)

theorem schema_reading_joint_class:
  "presentation_class
    (\<lambda>z t. factor_pair_presents
      (\<lambda>a p. site_value_presents (fst a) (fst (snd a)) (snd (snd a)) p)
      schema_reference_presents z t \<and> (126,t)\<in>positive_meaning schema_reading_system)
    (\<lambda>z. native_schema_at (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z))
    (\<lambda>t. (126,t)\<in>positive_meaning schema_reading_system)"
proof -
  let ?R="\<lambda>a p. site_value_presents (fst a) (fst (snd a)) (snd (snd a)) p"
  let ?D="\<lambda>a::local_address option artifact_environment \<times> (local_address option\<times>local_address).
    environment_formed (fst a) \<and> snd a\<in>environment_positions (fst a)"
  let ?link="\<lambda>a::local_address option artifact_environment \<times> (local_address option\<times>local_address).
    \<lambda>S::local_address option native_schema. native_schema_at (fst a) (fst (snd a)) (snd (snd a)) S"
  let ?observe="\<lambda>t. (126,t)\<in>positive_meaning schema_reading_system"
  have generic: "presentation_class (\<lambda>z t. factor_pair_presents ?R schema_reference_presents z t \<and> ?observe t)
      (\<lambda>z. (?D (fst z) \<and> schema_data_formed (snd z)) \<and> ?link (fst z) (snd z)) ?observe"
    by (rule factor_relation_presentation_class[OF site_presentations.presentation_class_axioms
      schema_reference_presentations.presentation_class_axioms schema_reading_presented_relation])
      (auto simp: schema_reading_exact)
  have bounded: "?D a \<and> schema_data_formed S" if read: "?link a S" for a S
    using read native_schema_data_formed[OF read] native_schema_position[OF read]
    by (auto simp: native_schema_at_def)
  have domain: "(\<lambda>z. (?D (fst z) \<and> schema_data_formed (snd z)) \<and> ?link (fst z) (snd z)) =
      (\<lambda>z. ?link (fst z) (snd z))"
    by (rule ext) (use bounded in blast)
  show ?thesis using generic by (simp only: domain)
qed

theorem schema_reading_at_reference:
  assumes source: "site_value_presents E u r p" and reference: "schema_reference_presents S v"
  shows "(126,Pair_Term p v)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    native_schema_at E u r S"
proof -
  have site: "site_value_presents (fst (E,u,r)) (fst (snd (E,u,r))) (snd (snd (E,u,r))) p"
    using source by simp
  have result: "presented_relation
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t) schema_reference_presents
      (\<lambda>z S. native_schema_at (fst z) (fst (snd z)) (snd (snd z)) S) p v \<longleftrightarrow>
      native_schema_at (fst (E,u,r)) (fst (snd (E,u,r))) (snd (snd (E,u,r))) S"
    by (rule presented_relation_at[OF site_presentations.presentation_class_axioms
      schema_reference_presentations.presentation_class_axioms site reference])
  show ?thesis using result by (simp only: schema_reading_presented_relation fst_conv snd_conv)
qed

corollary schema_reading_presentation_invariance:
  assumes first: "site_value_presents E u r p" "schema_reference_presents S v"
    and second: "site_value_presents E u r q" "schema_reference_presents S w"
  shows "(126,Pair_Term p v)\<in>positive_meaning schema_reading_system \<longleftrightarrow>
    (126,Pair_Term q w)\<in>positive_meaning schema_reading_system"
  by (simp only: schema_reading_at_reference[OF first] schema_reading_at_reference[OF second])

theorem schema_reading_total:
  assumes raw: "native_schema_at E u r S"
  shows "\<exists>p v. site_value_presents E u r p \<and> schema_reference_presents S v \<and>
    (126,Pair_Term p v)\<in>positive_meaning schema_reading_system"
proof -
  have formed: "environment_formed E" using raw by (simp add: native_schema_at_def)
  obtain p where site: "site_value_presents E u r p"
    using site_value_presents_total[OF formed native_schema_position[OF raw]] by blast
  obtain v where reference: "schema_reference_presents S v"
    using native_schema_reference_total[OF raw] by blast
  have admitted: "(126,Pair_Term p v)\<in>positive_meaning schema_reading_system"
    using raw by (simp only: schema_reading_at_reference[OF site reference])
  show ?thesis using site reference admitted by blast
qed

section \<open>One compiled reader checks its own clauses and all future source reports\<close>

lemma native_package_schema_origin:
  assumes package: "native_package_at E pu pr P" and clause: "((d,c),S)\<in>system_clauses P"
  shows "\<exists>r. native_schema_at E (fst d) r S"
proof -
  obtain roots where program: "P=native_program E roots"
    using package by (auto simp: native_package_at_def)
  obtain p C where definition_read: "native_definition_at E (fst d) (snd d) p C" and member: "(c,S)\<in>C"
    using clause by (auto simp: program native_definition_graph_def)
  show ?thesis by (rule native_definition_clause_origin[OF definition_read member])
qed

theorem native_schema_reading_checker:
  "\<exists>g :: nat\<Rightarrow>local_address option definition_site. \<exists>C cu Q.
    inj_on g (system_definitions schema_reading_system) \<and> closed_native_package_at C cu [] Q \<and>
    system_alpha_variant (rename_system g schema_reading_system) Q \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and>
        au\<notin>environment_uses C \<and> native_package_at F cu [] Q \<and>
        native_application_at F au [] (g 126) t I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> schema_reading_result t) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x))) \<and>
    (\<exists>d c S. ((d,c),S)\<in>system_clauses Q) \<and>
    (\<forall>d c S. ((d,c),S)\<in>system_clauses Q \<longrightarrow>
      (\<exists>r. native_schema_at C (fst d) r S \<and>
        (\<exists>p v. site_value_presents C (fst d) r p \<and> schema_reference_presents S v) \<and>
        (\<forall>p v. site_value_presents C (fst d) r p \<longrightarrow> schema_reference_presents S v \<longrightarrow>
          (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and>
        au\<notin>environment_uses C \<and> native_package_at F cu [] Q \<and>
        native_application_at F au [] (g 126) (Pair_Term p v) I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        native_positive_holds F cu [] au [] \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)))))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q
    where compiled: "inj_on g (system_definitions schema_reading_system)" "closed_native_package_at C cu [] Q"
      "native_package_environment C cu []=C" "system_alpha_variant (rename_system g schema_reading_system) Q"
      "positive_meaning Q=image (map_prod g id) (positive_meaning schema_reading_system)"
    and applications: "\<forall>d\<in>system_definitions schema_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F cu []=C \<and>
        (native_application_formed F cu [] au [] \<longleftrightarrow> schema_call_formed schema_reading_system d t) \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning schema_reading_system) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x))"
    using compiled_program_with_future_applications[OF schema_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have entry: "126\<in>system_definitions schema_reading_system" by simp
  have future: "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and>
        au\<notin>environment_uses C \<and> native_package_at F cu [] Q \<and>
        native_application_at F au [] (g 126) t I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> schema_reading_result t) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)" if formed: "term_formed t" for t
    using applications[rule_format, OF entry formed] formed
    by (simp only: schema_reading_call schema_reading_exact) auto
  have package: "native_package_at C cu [] Q" using compiled(2) by (simp add: closed_native_package_at_def)
  let ?nil="reference_bindings_value (Payload_Term []) (Payload_Term []) (Payload_Term [])"
  have base: "(125,?nil)\<in>positive_meaning reference_bindings_system"
    using reference_bindings_complete[of "[]"] by simp
  have source: "(125,?nil)\<in>positive_meaning schema_reading_system"
    using base by (simp only: schema_reading_components(1))
  have mapped: "(g 125,?nil)\<in>positive_meaning Q"
    using imageI[OF source, of "map_prod g id"] compiled(5) by simp
  have consequence: "(g 125,?nil)\<in>schema_consequences Q (positive_meaning Q)"
    using mapped positive_meaning_unfold[of Q] by blast
  obtain c S where own: "((g 125,c),S)\<in>system_clauses Q"
    using schema_consequences_valuationD[OF consequence] by blast
  have self: "\<exists>r. native_schema_at C (fst d) r S \<and>
      (\<exists>p v. site_value_presents C (fst d) r p \<and> schema_reference_presents S v) \<and>
      (\<forall>p v. site_value_presents C (fst d) r p \<longrightarrow> schema_reference_presents S v \<longrightarrow>
        (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and>
        au\<notin>environment_uses C \<and> native_package_at F cu [] Q \<and>
        native_application_at F au [] (g 126) (Pair_Term p v) I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        native_positive_holds F cu [] au [] \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)))"
    if clause: "((d,c),S)\<in>system_clauses Q" for d c S
  proof -
    obtain r where raw: "native_schema_at C (fst d) r S"
      using native_package_schema_origin[OF package clause] by blast
    have witnesses: "\<exists>p v. site_value_presents C (fst d) r p \<and> schema_reference_presents S v"
      using schema_reading_total[OF raw] by blast
    have calls: "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and>
        au\<notin>environment_uses C \<and> native_package_at F cu [] Q \<and>
        native_application_at F au [] (g 126) (Pair_Term p v) I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        native_positive_holds F cu [] au [] \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)"
      if site: "site_value_presents C (fst d) r p" and reference: "schema_reference_presents S v"
      for p v
    proof -
      have formed: "term_formed (Pair_Term p v)"
        using site_value_presents_formed[OF site] schema_reference_presents_formed[OF reference] by simp
      have result: "schema_reading_result (Pair_Term p v)"
        using site raw reference by blast
      show ?thesis using future[OF formed] result by blast
    qed
    show ?thesis by (rule exI[of _ r]) (use raw witnesses calls in blast)
  qed
  show ?thesis by (rule exI[of _ g], rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q])
    (use compiled(1,2,4) future own self in blast)
qed

text \<open>
  Three ordinary premises relate one actual source site to its complete
  reference report. The binder traversal supplies both private tables, and
  the existing schema reader checks both outputs against the same actual
  schema. Complete material outputs remain present even though their truth
  is not tested. Missing or additional syntax cannot be hidden by choosing
  two unrelated schemas or by varying the binder between readings.

  The all-term contract is the presented native-schema relation. Its source
  is the complete environment and actual site; its other operand belongs to
  the observation class derived from products, collections, and determining
  observations. Admission preserves and reflects that intrinsic link for
  every member of both classes. Reference formation never asserts the truth
  of an arbitrary mathematical contract.

  One finite native compilation is fixed before every future report. It
  contains an actual clause, and every one of its own clauses has source and
  reference presentations. All compatible presentations of each such clause
  are admitted by calls to that same compiled reader. The original program
  environment, artifacts, and outgoing bindings remain intact.
\<close>

end
