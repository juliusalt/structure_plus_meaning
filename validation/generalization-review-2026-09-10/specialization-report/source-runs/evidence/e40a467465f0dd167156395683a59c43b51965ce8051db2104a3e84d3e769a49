theory Factor_Definition_Edge_Reading
  imports Factor_Definition_Clause_Reading
begin

section \<open>Every edge follows an actual clause and prospective citation\<close>

abbreviation definition_edge_reading_result :: "factor_term \<Rightarrow> bool" where
  "definition_edge_reading_result z \<equiv> \<exists>E e d f.
    z=Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f)) \<and>
    environment_value_presents E e \<and> (d,f)\<in>native_definition_edges E"

definition definition_edge_reading_schema :: "(nat,nat,nat) factor_schema" where
  "definition_edge_reading_schema=data_rule (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w))
    {(0,81,citation_observation_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))),
     (1,65,schema_instantiation_pattern data_x data_y (Pattern_Variable 5) (Pattern_Variable 6)
       (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9)),
     (2,59,Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10)),
     (3,51,Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)),
     (4,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 12)))}"

definition definition_edge_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "definition_edge_reading_system=add_view_definition definition_clause_reading_system 82 data_x {(0,definition_edge_reading_schema)}"

lemma definition_edge_reading_system_formed [simp]: "schema_system_formed definition_edge_reading_system"
  unfolding definition_edge_reading_system_def
  by (rule add_recursive_definition_formed[OF definition_clause_reading_system_formed])
    (auto simp: definition_edge_reading_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma definition_edge_reading_definitions [simp]:
  "system_definitions definition_edge_reading_system=insert 82 (system_definitions definition_clause_reading_system)"
  by (simp add: definition_edge_reading_system_def)

lemma definition_edge_reading_call:
  "schema_call_formed definition_edge_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions definition_edge_reading_system \<and> term_formed t"
  using added_variable_calls[OF definition_clause_reading_system_formed
    definition_edge_reading_system_formed[unfolded definition_edge_reading_system_def] definition_clause_reading_call]
  by (simp only: definition_edge_reading_system_def[symmetric])

lemma definition_edge_reading_old_meaning:
  assumes "d\<in>system_definitions definition_clause_reading_system"
  shows "(d,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_clause_reading_system"
  using added_definition_preserves_old(2)[OF definition_clause_reading_system_formed
    definition_edge_reading_system_formed[unfolded definition_edge_reading_system_def], of d t] assms
  by (auto simp: definition_edge_reading_system_def)

lemma definition_edge_reading_clause [simp]:
  "((82,c),S)\<in>system_clauses definition_edge_reading_system \<longleftrightarrow> (c,S)\<in>{(0,definition_edge_reading_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_clause_reading_system \<Longrightarrow>
    d\<in>system_definitions definition_clause_reading_system" for d c S
    using definition_clause_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((82,c),S)\<notin>system_clauses definition_clause_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: definition_edge_reading_system_def)
qed

lemma definition_edge_reading_previous_meaning:
  assumes "d\<in>system_definitions package_admission_system"
  shows "(d,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_admission_system"
  using definition_edge_reading_old_meaning[of d t] definition_clause_reading_old_meaning[OF assms, of t] assms by auto

lemma definition_edge_reading_components:
  "(81,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (81,t)\<in>positive_meaning definition_clause_reading_system"
  "(65,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (65,t)\<in>positive_meaning schema_instantiation_system"
  "(59,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (59,t)\<in>positive_meaning row_values_system"
  "(51,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (51,t)\<in>positive_meaning row_keys_system"
  "(5,t)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (5,t)\<in>positive_meaning bag_comparison_system"
  using definition_edge_reading_old_meaning[of 81 t]
    definition_edge_reading_previous_meaning[of 65 t] package_admission_previous_meaning[of 65 t]
    package_closure_previous_meaning[of 65 t] definition_call_admission_instantiation_meaning[of 65 t]
    definition_edge_reading_previous_meaning[of 59 t] package_admission_old_meaning[of 59 t]
    root_family_reading_components(3)[of t]
    definition_edge_reading_previous_meaning[of 51 t] package_admission_old_meaning[of 51 t]
    root_family_reading_components(5)[of t]
    definition_edge_reading_old_meaning[of 5 t] definition_clause_reading_components(5)[of t] by auto

lemma definition_edge_reading_step:
  assumes clause: "(81,citation_observation_argument e u r (Pair_Term c a))\<in>positive_meaning definition_clause_reading_system"
    and inst: "(65,schema_instantiation_argument e u a b t q m)\<in>positive_meaning schema_instantiation_system"
    and projection: "(59,Pair_Term q v)\<in>positive_meaning row_values_system"
    and keys: "(51,Pair_Term v fs)\<in>positive_meaning row_keys_system"
    and selected: "(5,Pair_Term f (Pair_Term fs rest))\<in>positive_meaning bag_comparison_system"
  shows "(82,Pair_Term e (Pair_Term (Pair_Term u r) f))\<in>positive_meaning definition_edge_reading_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed f" "term_formed c"
    "term_formed a" "term_formed b" "term_formed t" "term_formed q" "term_formed m"
    "term_formed v" "term_formed fs" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF clause]]
      schema_call_formed_target[OF positive_meaning_formed[OF inst]]
      schema_call_formed_target[OF positive_meaning_formed[OF keys]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then f
    else if n=4 then c else if n=5 then a else if n=6 then b else if n=7 then t
    else if n=8 then q else if n=9 then m else if n=10 then v else if n=11 then fs else rest"
  have result: "(82,evaluate_pattern ?h (schema_conclusion definition_edge_reading_schema))
      \<in>positive_meaning definition_edge_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: definition_edge_reading_schema_def schema_variables_def
        definition_edge_reading_call definition_edge_reading_components\<close>)
  show ?thesis using result by (simp add: definition_edge_reading_schema_def)
qed

theorem definition_edge_reading_sound:
  assumes holds: "(82,z)\<in>positive_meaning definition_edge_reading_system"
  shows "definition_edge_reading_result z"
proof -
  have consequence: "(82,z)\<in>schema_consequences definition_edge_reading_system (positive_meaning definition_edge_reading_system)"
    using holds positive_meaning_unfold[of definition_edge_reading_system] by blast
  obtain n S h where clause: "((82,n),S)\<in>system_clauses definition_edge_reading_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning definition_edge_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=definition_edge_reading_schema" using clause by simp
  have calls: "(81,citation_observation_argument (h 0) (h 1) (h 2) (Pair_Term (h 4) (h 5)))
      \<in>positive_meaning definition_clause_reading_system"
    "(65,schema_instantiation_argument (h 0) (h 1) (h 5) (h 6) (h 7) (h 8) (h 9))
      \<in>positive_meaning schema_instantiation_system"
    "(59,Pair_Term (h 8) (h 10))\<in>positive_meaning row_values_system"
    "(51,Pair_Term (h 10) (h 11))\<in>positive_meaning row_keys_system"
    "(5,Pair_Term (h 3) (Pair_Term (h 11) (h 12)))\<in>positive_meaning bag_comparison_system"
    using support by (auto simp: schema definition_edge_reading_schema_def definition_edge_reading_components)
  obtain E u r c a where source: "environment_value_presents E (h 0)" "h 1=use_data_term u" "h 2=Payload_Term r"
    "h 4=Payload_Term c" "h 5=Payload_Term a"
    using calls(1) by (simp only: definition_clause_reading_exact factor_term.inject) blast
  obtain xs T qs cs where instantiated: "h 6=binding_rows_term xs" "h 8=call_instance_rows_term qs" "h 9=binding_rows_term cs"
    "native_schema_at E u a T" "schema_instance T (set xs) (h 7) (set qs)"
    using calls(2) by (simp only: source(2,5) schema_instantiation_at_source[OF source(1)]
      inj_eq[OF use_data_term_injective] factor_term.inject) blast
  have actual: "(81,citation_observation_argument (h 0) (use_data_term u) (Payload_Term r)
      (Pair_Term (Payload_Term c) (Payload_Term a)))\<in>positive_meaning definition_clause_reading_system"
    using calls(1) by (simp only: source)
  obtain pat C where defn: "native_definition_at E u r pat C" "(c,T)\<in>C"
    using definition_clause_reading_recovers[OF source(1) actual instantiated(4)] by blast
  have rows: "h 10=pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
    using calls(3) by (simp only: instantiated(2) call_instance_row_values)
  have keys: "h 11=data_list_term (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    using calls(4) by (simp only: rows call_instance_callee_keys)
  have selected: "selected_data_member (h 3) (h 11)" using calls(5) by blast
  have member: "h 3\<in>set (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    using selected by (simp only: keys selected_data_member_exact data_list_term_injective) auto
  obtain f where target: "h 3=definition_site_value f" "f\<in>schema_dependencies T"
    using member by (simp only: call_instance_callee_values[OF instantiated(5)]) auto
  have edge: "((u,r),f)\<in>native_definition_edges E"
    using defn target(2) by (auto simp: native_definition_edges_def)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ "(u,r)"], rule exI[of _ f])
      (use source target edge conclusion in \<open>simp add: schema definition_edge_reading_schema_def site_data_term_def\<close>)
qed

theorem definition_edge_reading_complete:
  assumes source: "environment_value_presents E e" and edge: "(d,f)\<in>native_definition_edges E"
  shows "(82,Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f)))\<in>positive_meaning definition_edge_reading_system"
proof -
  obtain u r where site: "d=(u,r)" by (cases d)
  obtain pat C c S where raw: "native_definition_at E u r pat C" "(c,S)\<in>C" "f\<in>schema_dependencies S"
    using edge by (auto simp: native_definition_edges_def site)
  obtain a where clause: "(81,citation_observation_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (Payload_Term c) (Payload_Term a)))\<in>positive_meaning definition_clause_reading_system"
    and schema: "native_schema_at E u a S"
    using definition_clause_reading_total[OF source raw(1,2)] by blast
  obtain xs t qs cs where inst: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term a)
      (binding_rows_term xs) t (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_inhabited[OF source schema] by blast
  have instantiated: "schema_instance S (set xs) t (set qs)"
    using iffD1[OF schema_instantiation_at_schema[OF source schema] inst] by blast
  let ?v="pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
  let ?fs="data_list_term (map (\<lambda>(s,d,t). definition_site_value d) qs)"
  have qf: "term_formed (call_instance_rows_term qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]] by auto
  have projection: "(59,Pair_Term (call_instance_rows_term qs) ?v)\<in>positive_meaning row_values_system"
    by (simp only: call_instance_row_values) (use qf in blast)
  have vf: "term_formed ?v" using schema_call_formed_target[OF positive_meaning_formed[OF projection]] by auto
  have keys: "(51,Pair_Term ?v ?fs)\<in>positive_meaning row_keys_system"
    by (simp only: call_instance_callee_keys) (use vf in blast)
  have data: "data_elements (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF keys]] by (auto simp: data_list_term_formed)
  have member: "definition_site_value f\<in>set (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    by (simp only: call_instance_callee_values[OF instantiated]) (rule imageI[OF raw(3)])
  have selected: "selected_data_member (definition_site_value f) ?fs"
    by (simp only: selected_data_member_exact data_list_term_injective) (use data member in auto)
  obtain rest where selection: "(5,Pair_Term (definition_site_value f) (Pair_Term ?fs rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  show ?thesis using definition_edge_reading_step[OF clause inst projection keys selection]
    by (simp add: site site_data_term_def)
qed

theorem definition_edge_reading_exact:
  "(82,z)\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow> definition_edge_reading_result z"
  using definition_edge_reading_sound definition_edge_reading_complete by blast

corollary definition_edge_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(82,Pair_Term e (Pair_Term a b))\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (\<exists>d f. a=definition_site_value d \<and> b=definition_site_value f \<and> (d,f)\<in>native_definition_edges E)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: definition_edge_reading_exact factor_term.inject) (use source unique in blast)
qed

corollary definition_edge_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(82,Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f)))
    \<in>positive_meaning definition_edge_reading_system \<longleftrightarrow> (d,f)\<in>native_definition_edges E"
  by (simp only: definition_edge_reading_at_source[OF source] definition_site_value_eq) blast

corollary definition_edge_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(82,Pair_Term e (Pair_Term a b))\<in>positive_meaning definition_edge_reading_system \<longleftrightarrow>
    (82,Pair_Term f (Pair_Term a b))\<in>positive_meaning definition_edge_reading_system"
  by (simp only: definition_edge_reading_at_source[OF assms(1)] definition_edge_reading_at_source[OF assms(2)])

text \<open>
  An edge begins at an admitted actual definition. Its selected clause socket
  exposes the actual schema root, and complete instantiation projects exactly
  that schema's prospective callees. One selection from this complete callee
  list exposes the requested destination.

  The relation is exactly the existing definition-edge relation. It does not
  require material satisfaction, prospective-call truth, or a definition at
  the destination. Package admission separately requires every reached site
  to be a definition. No scan of unrelated environment positions selects
  an edge, and every complete source presentation has the same answer.
\<close>

end
