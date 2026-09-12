theory Factor_Premise_Slot_Reading
  imports Factor_Derivation_Admission Factor_Slot_Observations
begin

section \<open>One actual slot of a premise under its declared scope\<close>

abbreviation scope_slot_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "scope_slot_argument e u v r k \<equiv> citation_observation_argument e u r (Pair_Term v k)"

abbreviation scope_slot_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "scope_slot_pattern e u v r k \<equiv> citation_observation_pattern e u r (Pattern_Pair v k)"

abbreviation premise_slot_reading_result :: "factor_term \<Rightarrow> bool" where
  "premise_slot_reading_result z \<equiv> \<exists>E e u Vs r k.
    z=scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Vs)) (Payload_Term r) (Payload_Term k) \<and>
    environment_value_presents E e \<and> distinct Vs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and>
    k\<in>native_premise_slots E u (set Vs) r"

definition premise_call_slot_schema :: "(nat,nat,nat) factor_schema" where
  "premise_call_slot_schema=data_rule
    (scope_slot_pattern data_x data_y data_z data_w (Pattern_Variable 4))
    {(0,57,prospective_instantiation_pattern data_x data_y data_z (Pattern_Variable 5) data_w
       (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10)),
     (1,5,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 11)))}"

definition premise_material_slot_schema :: "(nat,nat,nat) factor_schema" where
  "premise_material_slot_schema=data_rule
    (scope_slot_pattern data_x data_y data_z data_w (Pattern_Variable 4))
    {(0,62,material_instantiation_pattern data_x data_y data_z (Pattern_Variable 5) data_w
       (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10)
       (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13)),
     (1,5,Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 14)))}"

definition premise_slot_reading_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "premise_slot_reading_clauses={(0,premise_call_slot_schema),(1,premise_material_slot_schema)}"

definition premise_slot_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "premise_slot_reading_system=add_view_definition derivation_admission_system 103 data_x premise_slot_reading_clauses"

lemma premise_slot_reading_system_formed [simp]: "schema_system_formed premise_slot_reading_system"
  unfolding premise_slot_reading_system_def
  by (rule add_recursive_definition_formed[OF derivation_admission_system_formed])
    (auto simp: premise_slot_reading_clauses_def premise_call_slot_schema_def premise_material_slot_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma premise_slot_reading_definitions [simp]:
  "system_definitions premise_slot_reading_system=insert 103 (system_definitions derivation_admission_system)"
  by (simp add: premise_slot_reading_system_def)

lemma premise_slot_reading_call:
  "schema_call_formed premise_slot_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions premise_slot_reading_system \<and> term_formed t"
  using added_variable_calls[OF derivation_admission_system_formed
    premise_slot_reading_system_formed[unfolded premise_slot_reading_system_def] derivation_admission_call]
  by (simp only: premise_slot_reading_system_def[symmetric])

lemma premise_slot_reading_old_meaning:
  assumes "d\<in>system_definitions derivation_admission_system"
  shows "(d,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning derivation_admission_system"
  using added_definition_preserves_old(2)[OF derivation_admission_system_formed
    premise_slot_reading_system_formed[unfolded premise_slot_reading_system_def], of d t] assms
  by (auto simp: premise_slot_reading_system_def)

lemma premise_slot_reading_clause [simp]:
  "((103,c),S)\<in>system_clauses premise_slot_reading_system \<longleftrightarrow> (c,S)\<in>premise_slot_reading_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses derivation_admission_system \<Longrightarrow>
    d\<in>system_definitions derivation_admission_system" for d c S
    using derivation_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((103,c),S)\<notin>system_clauses derivation_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: premise_slot_reading_system_def)
qed

lemma premise_slot_reading_material_meaning:
  assumes "d\<in>system_definitions material_instantiation_system"
  shows "(d,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning material_instantiation_system"
  using premise_slot_reading_old_meaning[of d t] derivation_admission_old_meaning[of d t]
    proof_claim_checking_graph_meaning[of d t] proof_graph_membership_node_meaning[of d t]
    proof_node_reading_base_meaning[of d t] admitted_instantiation_previous_meaning[of d t]
    package_admission_previous_meaning[of d t] package_closure_previous_meaning[of d t]
    definition_call_admission_instantiation_meaning[of d t] schema_instantiation_old_meaning[of d t]
    premise_family_instantiation_old_meaning[of d t] premise_rows_old_meaning[OF assms, of t] assms by auto

lemma premise_slot_reading_components:
  "(57,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow> (57,t)\<in>positive_meaning prospective_instantiation_system"
  "(62,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow> (62,t)\<in>positive_meaning material_instantiation_system"
  "(5,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  using premise_slot_reading_material_meaning[of 57 t] material_instantiation_old_meaning[of 57 t]
    record_instantiation_old_meaning[of 57 t] vector_instantiation_old_meaning[of 57 t]
    row_values_old_meaning[of 57 t] application_reading_old_meaning[of 57 t]
    premise_slot_reading_material_meaning[of 62 t] premise_slot_reading_material_meaning[of 5 t]
    material_instantiation_old_meaning[of 5 t] record_instantiation_old_meaning[of 5 t]
    vector_instantiation_environment_meaning[of 5 t] environment_identity_old_meaning[of 5 t]
    environment_comparison_old_meaning[of 5 t] environment_bag_base_meaning[of 5 t] by auto

lemma premise_slot_reading_pattern_meaning:
  assumes "d\<in>system_definitions pattern_instantiation_system"
  shows "(d,t)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning pattern_instantiation_system"
  using premise_slot_reading_material_meaning[of d t] material_instantiation_old_meaning[of d t]
    record_instantiation_old_meaning[of d t] vector_instantiation_pattern_meaning[OF assms, of t] assms by auto

lemma premise_call_slot_step:
  assumes reading: "(57,prospective_instantiation_argument e u v b r d t w i ks)\<in>positive_meaning prospective_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term k (Pair_Term ks rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed v" "term_formed r" "term_formed k" "term_formed b"
    "term_formed d" "term_formed t" "term_formed w" "term_formed i" "term_formed ks" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then v else if j=3 then r else if j=4 then k
    else if j=5 then b else if j=6 then d else if j=7 then t else if j=8 then w else if j=9 then i else if j=10 then ks else rest"
  have result: "(103,evaluate_pattern ?h (schema_conclusion premise_call_slot_schema))\<in>positive_meaning premise_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use reading member formed in \<open>auto simp: premise_slot_reading_clauses_def premise_call_slot_schema_def
        schema_variables_def premise_slot_reading_call premise_slot_reading_components\<close>)
  show ?thesis using result by (simp add: premise_call_slot_schema_def)
qed

lemma premise_material_slot_step:
  assumes reading: "(62,material_instantiation_argument e u v b r s a d c f w i ks)\<in>positive_meaning material_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system"
proof -
  obtain rest where member: "(5,Pair_Term k (Pair_Term ks rest))\<in>positive_meaning bag_comparison_system"
    using selected by blast
  have formed: "term_formed e" "term_formed u" "term_formed v" "term_formed r" "term_formed k" "term_formed b"
    "term_formed s" "term_formed a" "term_formed d" "term_formed c" "term_formed f" "term_formed w"
    "term_formed i" "term_formed ks" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]]
      schema_call_formed_target[OF positive_meaning_formed[OF member]] by (auto simp: material_tuple_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then u else if j=2 then v else if j=3 then r else if j=4 then k
    else if j=5 then b else if j=6 then s else if j=7 then a else if j=8 then d else if j=9 then c
    else if j=10 then f else if j=11 then w else if j=12 then i else if j=13 then ks else rest"
  have result: "(103,evaluate_pattern ?h (schema_conclusion premise_material_slot_schema))\<in>positive_meaning premise_slot_reading_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use reading member formed in \<open>auto simp: premise_slot_reading_clauses_def premise_material_slot_schema_def
        schema_variables_def premise_slot_reading_call premise_slot_reading_components material_tuple_def\<close>)
  show ?thesis using result by (simp add: premise_material_slot_schema_def)
qed

lemma premise_slot_from_call:
  assumes reading: "(57,prospective_instantiation_argument e u v b r d t w i ks)\<in>positive_meaning prospective_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "premise_slot_reading_result (scope_slot_argument e u v r k)"
proof -
  obtain E q Vs a p site Is Ks where fields: "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)"
    "r=Payload_Term a" "ks=data_list_term (map Payload_Term Ks)"
    and source: "environment_value_presents E e" and scope: "distinct Vs" "\<forall>x\<in>set Vs. octets_formed x"
    and call: "prospective_call_at E q (set Vs) a site p (set Is) (set Ks)"
    using reading by (auto simp: prospective_instantiation_exact)
  obtain j where slot: "k=Payload_Term j" "j\<in>set Ks"
    using selected by (auto simp: fields(4) selected_data_member_exact data_list_term_injective)
  have needed: "j\<in>native_premise_slots E q (set Vs) a"
    using call slot(2) unfolding native_premise_slots_def by (blast intro: native_premise_at.call)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ q], rule exI[of _ Vs], rule exI[of _ a], rule exI[of _ j])
      (use fields source scope slot needed in auto)
qed

lemma premise_slot_from_material:
  assumes reading: "(62,material_instantiation_argument e u v b r s a d c f w i ks)\<in>positive_meaning material_instantiation_system"
    and selected: "selected_data_member k ks"
  shows "premise_slot_reading_result (scope_slot_argument e u v r k)"
proof -
  obtain E q Vs root M Is Ks where fields: "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)"
    "r=Payload_Term root" "ks=data_list_term (map Payload_Term Ks)"
    and source: "environment_value_presents E e" and scope: "distinct Vs" "\<forall>x\<in>set Vs. octets_formed x"
    and material: "native_material_at E q (set Vs) root M (set Is) (set Ks)"
    using reading by (auto simp: material_instantiation_exact)
  obtain j where slot: "k=Payload_Term j" "j\<in>set Ks"
    using selected by (auto simp: fields(4) selected_data_member_exact data_list_term_injective)
  have needed: "j\<in>native_premise_slots E q (set Vs) root"
    using material slot(2) unfolding native_premise_slots_def by (blast intro: native_premise_at.material)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ q], rule exI[of _ Vs], rule exI[of _ root], rule exI[of _ j])
      (use fields source scope slot needed in auto)
qed

theorem premise_slot_reading_sound:
  assumes holds: "(103,z)\<in>positive_meaning premise_slot_reading_system"
  shows "premise_slot_reading_result z"
proof -
  have consequence: "(103,z)\<in>schema_consequences premise_slot_reading_system (positive_meaning premise_slot_reading_system)"
    using holds positive_meaning_unfold[of premise_slot_reading_system] by blast
  obtain c S h where clause: "((103,c),S)\<in>system_clauses premise_slot_reading_system"
    and head: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning premise_slot_reading_system"
    using schema_consequences_valuationD[OF consequence] by blast
  consider (call) "S=premise_call_slot_schema" | (material) "S=premise_material_slot_schema"
    using clause by (auto simp: premise_slot_reading_clauses_def)
  then show ?thesis
  proof cases
    case call
    have reading: "(57,prospective_instantiation_argument (h 0) (h 1) (h 2) (h 5) (h 3)
        (h 6) (h 7) (h 8) (h 9) (h 10))\<in>positive_meaning prospective_instantiation_system"
      and selected: "selected_data_member (h 4) (h 10)"
      using support by (auto simp: call premise_call_slot_schema_def premise_slot_reading_components)
    show ?thesis using premise_slot_from_call[OF reading selected] head by (simp add: call premise_call_slot_schema_def)
  next
    case material
    have reading: "(62,material_instantiation_argument (h 0) (h 1) (h 2) (h 5) (h 3)
        (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 13))\<in>positive_meaning material_instantiation_system"
      and selected: "selected_data_member (h 4) (h 13)"
      using support by (auto simp: material premise_material_slot_schema_def premise_slot_reading_components material_tuple_def)
    show ?thesis using premise_slot_from_material[OF reading selected] head by (simp add: material premise_material_slot_schema_def)
  qed
qed

theorem premise_slot_reading_complete:
  assumes source: "environment_value_presents E e"
    and scope: "distinct Vs" "\<forall>a\<in>set Vs. octets_formed a"
    and slot: "k\<in>native_premise_slots E u (set Vs) r"
  shows "(103,scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
    (Payload_Term r) (Payload_Term k))\<in>positive_meaning premise_slot_reading_system"
proof -
  obtain p I K where reading: "native_premise_at E u (set Vs) r p I K" and member: "k\<in>K"
    using slot by (auto simp: native_premise_slots_def)
  show ?thesis
  proof (cases rule: native_premise_at.cases[OF reading, case_names call material])
    case (call d q)
    have actual: "prospective_call_at E u (set Vs) r d q I K" using call by auto
    obtain b d' t w i ks where child:
      "(57,prospective_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
        b (Payload_Term r) d' t w i ks)\<in>positive_meaning prospective_instantiation_system"
      "selected_data_member (Payload_Term k) ks"
      by (rule prospective_slot_observation[OF actual source scope member]) blast
    show ?thesis by (rule premise_call_slot_step[OF child])
  next
    case (material M)
    have actual: "native_material_at E u (set Vs) r M I K" using material by auto
    obtain b s a d c f w i ks where child:
      "(62,material_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
        b (Payload_Term r) s a d c f w i ks)\<in>positive_meaning material_instantiation_system"
      "selected_data_member (Payload_Term k) ks"
      by (rule material_slot_observation[OF actual source scope member]) blast
    show ?thesis by (rule premise_material_slot_step[OF child])
  qed
qed

theorem premise_slot_reading_exact:
  "(103,z)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow> premise_slot_reading_result z"
  using premise_slot_reading_sound premise_slot_reading_complete by blast

corollary premise_slot_reading_at_source:
  assumes source: "environment_value_presents E e"
  shows "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    (\<exists>q Vs a j. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and> r=Payload_Term a \<and>
      k=Payload_Term j \<and> distinct Vs \<and> (\<forall>x\<in>set Vs. octets_formed x) \<and>
      j\<in>native_premise_slots E q (set Vs) a)"
proof
  assume holds: "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system"
  obtain F q Vs a j where fields: "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)"
    "r=Payload_Term a" "k=Payload_Term j"
    and other_source: "environment_value_presents F e" and scope: "distinct Vs" "\<forall>x\<in>set Vs. octets_formed x"
    and slot: "j\<in>native_premise_slots F q (set Vs) a"
    using holds by (simp only: premise_slot_reading_exact factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF other_source source])
  show "\<exists>q Vs a j. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and> r=Payload_Term a \<and>
    k=Payload_Term j \<and> distinct Vs \<and> (\<forall>x\<in>set Vs. octets_formed x) \<and> j\<in>native_premise_slots E q (set Vs) a"
    by (rule exI[of _ q], rule exI[of _ Vs], rule exI[of _ a], rule exI[of _ j]) (use fields scope slot same in auto)
next
  assume "\<exists>q Vs a j. u=use_data_term q \<and> v=data_list_term (map Payload_Term Vs) \<and> r=Payload_Term a \<and>
    k=Payload_Term j \<and> distinct Vs \<and> (\<forall>x\<in>set Vs. octets_formed x) \<and> j\<in>native_premise_slots E q (set Vs) a"
  then obtain q Vs a j where fields: "u=use_data_term q" "v=data_list_term (map Payload_Term Vs)"
    "r=Payload_Term a" "k=Payload_Term j"
    and scope: "distinct Vs" "\<forall>x\<in>set Vs. octets_formed x" and slot: "j\<in>native_premise_slots E q (set Vs) a" by blast
  show "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system"
    using premise_slot_reading_complete[OF source scope slot] by (simp only: fields)
qed

corollary premise_slot_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(103,scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (Payload_Term r) (Payload_Term k))\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    distinct Vs \<and> (\<forall>a\<in>set Vs. octets_formed a) \<and> k\<in>native_premise_slots E u (set Vs) r"
  by (simp add: premise_slot_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
    data_list_term_injective injective_mapped_lists[OF payload_term_inj])

corollary premise_slot_reading_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(103,scope_slot_argument e u v r k)\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    (103,scope_slot_argument f u v r k)\<in>positive_meaning premise_slot_reading_system"
  by (simp only: premise_slot_reading_at_source[OF assms(1)] premise_slot_reading_at_source[OF assms(2)])

corollary premise_slot_reading_scope_order:
  assumes source: "environment_value_presents E e" and order: "distinct Vs" "distinct Ws" "set Vs=set Ws"
  shows "(103,scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (Payload_Term r) (Payload_Term k))\<in>positive_meaning premise_slot_reading_system \<longleftrightarrow>
    (103,scope_slot_argument e (use_data_term u) (data_list_term (map Payload_Term Ws))
      (Payload_Term r) (Payload_Term k))\<in>positive_meaning premise_slot_reading_system"
  using order by (simp only: premise_slot_reading_on_values[OF source])

corollary premise_slot_reading_bound:
  assumes source: "environment_value_presents E e"
    and reading: "(103,scope_slot_argument e (use_data_term u) v (Payload_Term r) (Payload_Term k))
      \<in>positive_meaning premise_slot_reading_system"
  shows "(u,k)\<in>rel_dom (environment_bindings E)"
  using reading by (auto simp: premise_slot_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
    dest: native_premise_slots_bound)

text \<open>
  The two clauses reuse complete prospective and material instantiation. They
  select an actual slot from the reader's output and hide all substitution and
  instance fields. Material truth and callee truth are not premises. The scope
  remains explicit, complete as supplied, and independent of its enumeration.
\<close>

end
