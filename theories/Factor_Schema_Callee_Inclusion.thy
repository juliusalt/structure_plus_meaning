theory Factor_Schema_Callee_Inclusion
  imports Factor_Definition_Call_Admission
begin

section \<open>Complete instance rows preserve exactly the prospective callees\<close>

abbreviation definition_site_value :: "local_address option definition_site \<Rightarrow> factor_term" where
  "definition_site_value d \<equiv> site_data_term (fst d) (snd d)"

lemma definition_site_value_eq [simp]:
  "definition_site_value d=definition_site_value e \<longleftrightarrow> d=e"
  by (cases d; cases e) simp

lemma definition_site_value_injective: "inj (\<lambda>d. definition_site_value d)"
  by (rule injI) (simp only: definition_site_value_eq)

lemma definition_site_value_subset [simp]:
  "(\<lambda>d. definition_site_value d) ` A \<subseteq> (\<lambda>d. definition_site_value d) ` B \<longleftrightarrow> A\<subseteq>B"
  by auto

lemma schema_premise_instance_dependencies:
  assumes inst: "schema_premise_instance S B Q"
  shows "fst ` rel_ran Q=schema_dependencies S"
proof
  show "fst ` rel_ran Q\<subseteq>schema_dependencies S"
  proof
    fix d assume "d\<in>fst ` rel_ran Q"
    then obtain s t where member: "(s,d,t)\<in>Q" by (auto simp: rel_ran_def)
    obtain p where premise: "(s,d,p)\<in>schema_premises S"
      using schema_premise_instance_origin[OF inst member] by blast
    have "(d,p)\<in>rel_ran (schema_premises S)" by (rule rel_ranI[OF premise])
    then have "fst (d,p)\<in>fst ` rel_ran (schema_premises S)" by (rule imageI)
    then show "d\<in>schema_dependencies S" by (simp only: fst_conv schema_dependencies_def)
  qed
  show "schema_dependencies S\<subseteq>fst ` rel_ran Q"
  proof
    fix d assume "d\<in>schema_dependencies S"
    then obtain s p where premise: "(s,d,p)\<in>schema_premises S"
      by (auto simp: schema_dependencies_def rel_ran_def)
    obtain t where member: "(s,d,t)\<in>Q"
      using inst premise unfolding schema_premise_instance_def by blast
    have "(d,t)\<in>rel_ran Q" by (rule rel_ranI[OF member])
    then have "fst (d,t)\<in>fst ` rel_ran Q" by (rule imageI)
    then show "d\<in>fst ` rel_ran Q" by (simp only: fst_conv)
  qed
qed

lemma call_instance_callee_values:
  assumes inst: "schema_instance S B t (set qs)"
  shows "set (map (\<lambda>(s,d,t). definition_site_value d) qs)=
    (\<lambda>d. definition_site_value d) ` schema_dependencies S"
proof -
  have instantiated: "schema_premise_instance S B (set qs)" using inst by (simp add: schema_instance_def)
  have "set (map (\<lambda>(s,d,t). definition_site_value d) qs)=
    (\<lambda>d. definition_site_value d) ` (fst ` rel_ran (set qs))"
    by (simp add: rel_ran_image image_image comp_def split_def)
  then show ?thesis by (simp only: schema_premise_instance_dependencies[OF instantiated])
qed

lemma call_instance_row_values:
  "(59,Pair_Term (call_instance_rows_term qs) v)\<in>positive_meaning row_values_system \<longleftrightarrow>
    term_formed (call_instance_rows_term qs) \<and>
    v=pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
  by (simp only: row_values_at_rows)
    (simp add: call_instance_value_def comp_def split_def)

lemma call_instance_callee_keys:
  "(51,Pair_Term (pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)) v)
      \<in>positive_meaning row_keys_system \<longleftrightarrow>
    term_formed (pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)) \<and>
    v=data_list_term (map (\<lambda>(s,d,t). definition_site_value d) qs)"
  by (simp only: row_keys_at_rows) (simp add: comp_def split_def)

section \<open>One ordinary clause checks the complete callee projection\<close>

abbreviation schema_callee_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "schema_callee_argument e v u r \<equiv> source_root_argument e (Pair_Term v u) r"

abbreviation schema_callee_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "schema_callee_pattern e v u r \<equiv> source_root_pattern e (Pattern_Pair v u) r"

abbreviation schema_callee_inclusion_result :: "factor_term \<Rightarrow> bool" where
  "schema_callee_inclusion_result z \<equiv> \<exists>E e ys u r S.
    z=schema_callee_argument e (data_list_term ys) (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents E e \<and> data_elements ys \<and> native_schema_at E u r S \<and>
    (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"

definition schema_callee_inclusion_schema :: "(nat,nat,nat) factor_schema" where
  "schema_callee_inclusion_schema=data_rule (schema_callee_pattern data_x data_y data_z data_w)
    {(0,65,schema_instantiation_pattern data_x data_z data_w
       (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)),
     (1,59,Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 8)),
     (2,51,Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)),
     (3,47,Pattern_Pair (Pattern_Variable 9) data_y)}"

definition schema_callee_inclusion_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_callee_inclusion_system=add_view_definition definition_call_admission_system 73 data_x {(0,schema_callee_inclusion_schema)}"

lemma schema_callee_inclusion_system_formed [simp]: "schema_system_formed schema_callee_inclusion_system"
  unfolding schema_callee_inclusion_system_def
  by (rule add_recursive_definition_formed[OF definition_call_admission_system_formed])
    (auto simp: schema_callee_inclusion_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_callee_inclusion_definitions [simp]:
  "system_definitions schema_callee_inclusion_system=insert 73 (system_definitions definition_call_admission_system)"
  by (simp add: schema_callee_inclusion_system_def)

lemma schema_callee_inclusion_call:
  "schema_call_formed schema_callee_inclusion_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_callee_inclusion_system \<and> term_formed t"
  using added_variable_calls[OF definition_call_admission_system_formed
    schema_callee_inclusion_system_formed[unfolded schema_callee_inclusion_system_def] definition_call_admission_call]
  by (simp only: schema_callee_inclusion_system_def[symmetric])

lemma schema_callee_inclusion_old_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> (d,t)\<in>positive_meaning definition_call_admission_system"
  using added_definition_preserves_old(2)[OF definition_call_admission_system_formed
    schema_callee_inclusion_system_formed[unfolded schema_callee_inclusion_system_def], of d t] assms
  by (auto simp: schema_callee_inclusion_system_def)

lemma schema_callee_inclusion_clause [simp]:
  "((73,c),S)\<in>system_clauses schema_callee_inclusion_system \<longleftrightarrow> (c,S)\<in>{(0,schema_callee_inclusion_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses definition_call_admission_system \<Longrightarrow>
    d\<in>system_definitions definition_call_admission_system" for d c S
    using definition_call_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((73,c),S)\<notin>system_clauses definition_call_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_callee_inclusion_system_def)
qed

lemma schema_callee_instantiation_meaning:
  assumes "d\<in>system_definitions schema_instantiation_system"
  shows "(d,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning schema_instantiation_system"
  using schema_callee_inclusion_old_meaning[of d t]
    definition_call_admission_instantiation_meaning[OF assms, of t] assms by auto

lemma schema_callee_inclusion_components:
  "(65,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> (65,t)\<in>positive_meaning schema_instantiation_system"
  "(59,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(51,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(47,t)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  using schema_callee_instantiation_meaning[of 65 t]
    schema_callee_instantiation_meaning[of 59 t] schema_instantiation_old_meaning[of 59 t]
    premise_family_instantiation_old_meaning[of 59 t] premise_rows_vector_meaning[of 59 t]
    vector_instantiation_old_meaning[of 59 t]
    schema_callee_instantiation_meaning[of 51 t] schema_instantiation_pattern_meaning[of 51 t]
    pattern_instantiation_old_meaning[of 51 t] binder_admission_prior_entries(1)[of t]
    schema_callee_instantiation_meaning[of 47 t] schema_instantiation_pattern_meaning[of 47 t]
    pattern_instantiation_quotation_meaning[of 47 t] quotation_admission_old_meaning[of 47 t]
    payload_disjoint_prior_entries(3)[of t] by auto

lemma schema_callee_inclusion_step:
  assumes inst: "(65,schema_instantiation_argument e u r b t q c)\<in>positive_meaning schema_instantiation_system"
    and rows: "(59,Pair_Term q v)\<in>positive_meaning row_values_system"
    and keys: "(51,Pair_Term v k)\<in>positive_meaning row_keys_system"
    and included: "(47,Pair_Term k w)\<in>positive_meaning data_subset_system"
  shows "(73,schema_callee_argument e w u r)\<in>positive_meaning schema_callee_inclusion_system"
proof -
  have formed: "term_formed e" "term_formed w" "term_formed u" "term_formed r" "term_formed b"
    "term_formed t" "term_formed q" "term_formed c" "term_formed v" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]]
      schema_call_formed_target[OF positive_meaning_formed[OF rows]]
      schema_call_formed_target[OF positive_meaning_formed[OF included]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then w else if n=2 then u else if n=3 then r
    else if n=4 then b else if n=5 then t else if n=6 then q else if n=7 then c else if n=8 then v else k"
  have result: "(73,evaluate_pattern ?h (schema_conclusion schema_callee_inclusion_schema))
      \<in>positive_meaning schema_callee_inclusion_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: schema_callee_inclusion_schema_def schema_variables_def
        schema_callee_inclusion_call schema_callee_inclusion_components\<close>)
  show ?thesis using result by (simp add: schema_callee_inclusion_schema_def)
qed

theorem schema_callee_inclusion_sound:
  assumes holds: "(73,z)\<in>positive_meaning schema_callee_inclusion_system"
  shows "schema_callee_inclusion_result z"
proof -
  have consequence: "(73,z)\<in>schema_consequences schema_callee_inclusion_system (positive_meaning schema_callee_inclusion_system)"
    using holds positive_meaning_unfold[of schema_callee_inclusion_system] by blast
  obtain n S h where clause: "((73,n),S)\<in>system_clauses schema_callee_inclusion_system"
    and conclusion: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning schema_callee_inclusion_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=schema_callee_inclusion_schema" using clause by simp
  have calls: "(65,schema_instantiation_argument (h 0) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      \<in>positive_meaning schema_instantiation_system"
    "(59,Pair_Term (h 6) (h 8))\<in>positive_meaning row_values_system"
    "(51,Pair_Term (h 8) (h 9))\<in>positive_meaning row_keys_system"
    "(47,Pair_Term (h 9) (h 1))\<in>positive_meaning data_subset_system"
    using support by (auto simp: schema schema_callee_inclusion_schema_def schema_callee_inclusion_components)
  obtain E u r xs T qs where raw: "environment_value_presents E (h 0)" "h 2=use_data_term u"
    "h 3=Payload_Term r" "h 6=call_instance_rows_term qs" "native_schema_at E u r T"
    "schema_instance T (set xs) (h 5) (set qs)"
    using calls(1) by (simp only: schema_instantiation_exact factor_term.inject) blast
  have rows: "h 8=pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
    using calls(2) by (simp only: raw(4) call_instance_row_values)
  have keys: "h 9=data_list_term (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    using calls(3) by (simp only: rows call_instance_callee_keys)
  obtain ys where bound: "h 1=data_list_term ys" "data_elements ys"
    "set (map (\<lambda>(s,d,t). definition_site_value d) qs)\<subseteq>set ys"
    using calls(4) by (simp only: keys data_subset_exact factor_term.inject data_list_term_injective) blast
  have included: "(\<lambda>d. definition_site_value d) ` schema_dependencies T\<subseteq>set ys"
    using bound(3) by (simp only: call_instance_callee_values[OF raw(6)])
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ ys], rule exI[of _ u],
        rule exI[of _ r], rule exI[of _ T])
      (use raw bound included conclusion in \<open>simp add: schema schema_callee_inclusion_schema_def\<close>)
qed

theorem schema_callee_inclusion_complete:
  assumes source: "environment_value_presents E e" and raw: "native_schema_at E u r S"
    and data: "data_elements ys" and included: "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
  shows "(73,schema_callee_argument e (data_list_term ys) (use_data_term u) (Payload_Term r))
    \<in>positive_meaning schema_callee_inclusion_system"
proof -
  obtain xs t qs cs where inst: "(65,schema_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term xs) t (call_instance_rows_term qs) (binding_rows_term cs))\<in>positive_meaning schema_instantiation_system"
    using schema_instantiation_inhabited[OF source raw] by blast
  have instantiated: "schema_instance S (set xs) t (set qs)"
    using iffD1[OF schema_instantiation_at_schema[OF source raw] inst] by blast
  let ?v="pair_list_term (map (\<lambda>(s,d,t). (definition_site_value d,t)) qs)"
  let ?k="data_list_term (map (\<lambda>(s,d,t). definition_site_value d) qs)"
  have qf: "term_formed (call_instance_rows_term qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF inst]] by auto
  have rows: "(59,Pair_Term (call_instance_rows_term qs) ?v)\<in>positive_meaning row_values_system"
    by (simp only: call_instance_row_values) (use qf in blast)
  have vf: "term_formed ?v" using schema_call_formed_target[OF positive_meaning_formed[OF rows]] by auto
  have keys: "(51,Pair_Term ?v ?k)\<in>positive_meaning row_keys_system"
    by (simp only: call_instance_callee_keys) (use vf in blast)
  have elements: "data_elements (map (\<lambda>(s,d,t). definition_site_value d) qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF keys]]
    by (auto simp: data_list_term_formed)
  have subset: "(47,Pair_Term ?k (data_list_term ys))\<in>positive_meaning data_subset_system"
    by (simp only: data_subset_lists call_instance_callee_values[OF instantiated])
      (use elements data included in blast)
  show ?thesis by (rule schema_callee_inclusion_step[OF inst rows keys subset])
qed

theorem schema_callee_inclusion_exact:
  "(73,z)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow> schema_callee_inclusion_result z"
proof
  assume "(73,z)\<in>positive_meaning schema_callee_inclusion_system"
  then show "schema_callee_inclusion_result z" by (rule schema_callee_inclusion_sound)
next
  assume "schema_callee_inclusion_result z"
  then obtain E e ys u r S where parts:
    "z=schema_callee_argument e (data_list_term ys) (use_data_term u) (Payload_Term r)"
    "environment_value_presents E e" "data_elements ys" "native_schema_at E u r S"
    "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by auto
  show "(73,z)\<in>positive_meaning schema_callee_inclusion_system"
    by (simp only: parts(1); rule schema_callee_inclusion_complete[OF parts(2,4,3,5)])
qed

corollary schema_callee_inclusion_at_source:
  assumes source: "environment_value_presents E e"
  shows "(73,schema_callee_argument e w u r)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow>
    (\<exists>ys v a S. w=data_list_term ys \<and> u=use_data_term v \<and> r=Payload_Term a \<and>
      data_elements ys \<and> native_schema_at E v a S \<and>
      (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
proof
  assume holds: "(73,schema_callee_argument e w u r)\<in>positive_meaning schema_callee_inclusion_system"
  obtain F f ys v a S where parts:
    "schema_callee_argument e w u r=schema_callee_argument f (data_list_term ys) (use_data_term v) (Payload_Term a)"
    "environment_value_presents F f" "data_elements ys" "native_schema_at F v a S"
    "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
    using schema_callee_inclusion_sound[OF holds] by blast
  have input: "f=e" "w=data_list_term ys" "u=use_data_term v" "r=Payload_Term a" using parts(1) by auto
  have same: "F=E"
    by (rule environment_value_presents_unique[OF _ source]) (use parts(2) input(1) in simp)
  show "\<exists>ys v a S. w=data_list_term ys \<and> u=use_data_term v \<and> r=Payload_Term a \<and>
    data_elements ys \<and> native_schema_at E v a S \<and>
    (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
    by (rule exI[of _ ys], rule exI[of _ v], rule exI[of _ a], rule exI[of _ S])
      (use parts input same in simp)
next
  assume "\<exists>ys v a S. w=data_list_term ys \<and> u=use_data_term v \<and> r=Payload_Term a \<and>
    data_elements ys \<and> native_schema_at E v a S \<and>
    (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
  then obtain ys v a S where parts: "w=data_list_term ys" "u=use_data_term v" "r=Payload_Term a"
    "data_elements ys" "native_schema_at E v a S"
    "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys" by blast
  show "(73,schema_callee_argument e w u r)\<in>positive_meaning schema_callee_inclusion_system"
    by (simp only: parts(1-3); rule schema_callee_inclusion_complete[OF source parts(5,4,6)])
qed

corollary schema_callee_inclusion_on_values:
  assumes source: "environment_value_presents E e"
  shows "(73,schema_callee_argument e (data_list_term ys) (use_data_term u) (Payload_Term r))
      \<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow>
    data_elements ys \<and> (\<exists>S. native_schema_at E u r S \<and>
      (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  by (simp only: schema_callee_inclusion_at_source[OF source] data_list_term_injective
    inj_eq[OF use_data_term_injective] factor_term.inject) blast

corollary schema_callee_inclusion_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(73,schema_callee_argument e w u r)\<in>positive_meaning schema_callee_inclusion_system \<longleftrightarrow>
    (73,schema_callee_argument f w u r)\<in>positive_meaning schema_callee_inclusion_system"
  by (simp only: schema_callee_inclusion_at_source[OF assms(1)] schema_callee_inclusion_at_source[OF assms(2)])

section \<open>Every actual clause root is checked under the same bound\<close>

abbreviation schema_callee_list_result :: "factor_term \<Rightarrow> bool" where
  "schema_callee_list_result z \<equiv> \<exists>a xs. z=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. schema_callee_inclusion_result (Pair_Term a x))"

definition schema_callee_list_system :: "(nat,nat,nat,nat) schema_system" where
  "schema_callee_list_system=add_view_definition schema_callee_inclusion_system 74 data_x (context_list_clauses 73 74)"

lemma schema_callee_list_system_formed [simp]: "schema_system_formed schema_callee_list_system"
  unfolding schema_callee_list_system_def
  by (rule add_recursive_definition_formed[OF schema_callee_inclusion_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma schema_callee_list_definitions [simp]:
  "system_definitions schema_callee_list_system=insert 74 (system_definitions schema_callee_inclusion_system)"
  by (simp add: schema_callee_list_system_def)

lemma schema_callee_list_call:
  "schema_call_formed schema_callee_list_system d t \<longleftrightarrow>
    d\<in>system_definitions schema_callee_list_system \<and> term_formed t"
  using added_variable_calls[OF schema_callee_inclusion_system_formed
    schema_callee_list_system_formed[unfolded schema_callee_list_system_def] schema_callee_inclusion_call]
  by (simp only: schema_callee_list_system_def[symmetric])

lemma schema_callee_list_old_meaning:
  assumes "d\<in>system_definitions schema_callee_inclusion_system"
  shows "(d,t)\<in>positive_meaning schema_callee_list_system \<longleftrightarrow> (d,t)\<in>positive_meaning schema_callee_inclusion_system"
  using added_definition_preserves_old(2)[OF schema_callee_inclusion_system_formed
    schema_callee_list_system_formed[unfolded schema_callee_list_system_def], of d t] assms
  by (auto simp: schema_callee_list_system_def)

lemma schema_callee_list_clause [simp]:
  "((74,c),S)\<in>system_clauses schema_callee_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 73 74)"
proof -
  have owned: "((d,c),S)\<in>system_clauses schema_callee_inclusion_system \<Longrightarrow>
    d\<in>system_definitions schema_callee_inclusion_system" for d c S
    using schema_callee_inclusion_system_formed unfolding schema_system_formed_def by blast
  have absent: "((74,c),S)\<notin>system_clauses schema_callee_inclusion_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: schema_callee_list_system_def)
qed

lemma schema_callee_list_element:
  "(73,t)\<in>positive_meaning schema_callee_list_system \<longleftrightarrow> (73,t)\<in>positive_meaning schema_callee_inclusion_system"
  by (rule schema_callee_list_old_meaning) simp

interpretation schema_callee_list_profile: context_list_profile schema_callee_list_system 73 74
  by (rule context_list_profile.intro) (auto simp: schema_callee_list_call)

theorem schema_callee_list_exact:
  "(74,z)\<in>positive_meaning schema_callee_list_system \<longleftrightarrow> schema_callee_list_result z"
  by (simp only: schema_callee_list_profile.exact schema_callee_list_element schema_callee_inclusion_exact)

corollary schema_callee_list_on_values:
  assumes source: "environment_value_presents E e" and data: "data_elements ys"
  shows "(74,Pair_Term (Pair_Term e (Pair_Term (data_list_term ys) (use_data_term u)))
      (data_list_term (map Payload_Term rs)))\<in>positive_meaning schema_callee_list_system \<longleftrightarrow>
    (\<forall>r\<in>set rs. \<exists>S. native_schema_at E u r S \<and>
      (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  by (simp only: schema_callee_list_profile.lists schema_callee_list_element)
    (use environment_value_presents_formed[OF source] data in
      \<open>auto simp: schema_callee_inclusion_on_values[OF source] data_list_term_formed\<close>)

text \<open>
  Complete schema instantiation retains every prospective socket and its
  actual callee. Projecting row values and then row keys therefore obtains
  exactly the schema dependencies, independently of the chosen substitution,
  row order, and material truth. The two projection operations already exist.

  The bound is a complete self-contained data list. It may contain repeated
  values and additional data. This entry checks inclusion alone; it does not
  claim that every bound element is a definition. The list entry checks every
  supplied schema root through the same fixed callee definition and carries
  the same source and bound into each call. Its empty case accepts a formed
  context without independently reading an environment or bound.
\<close>

end
