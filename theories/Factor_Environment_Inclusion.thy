theory Factor_Environment_Inclusion
  imports Factor_Replay_Admission
begin

section \<open>Every complete artifact row is retained at its actual use\<close>

abbreviation artifact_inclusion_result :: "factor_term \<Rightarrow> bool" where
  "artifact_inclusion_result z \<equiv> \<exists>f xs. z=Pair_Term f (data_list_term xs) \<and> term_formed f \<and>
    (\<forall>x\<in>set xs. \<exists>F row. environment_value_presents F f \<and>
      row\<in>environment_artifacts F \<and> environment_artifact_entry_presents row x)"

definition artifact_inclusion_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_inclusion_system=add_view_definition replay_admission_system 112 data_x (context_list_clauses 37 112)"

lemma artifact_inclusion_system_formed [simp]: "schema_system_formed artifact_inclusion_system"
  unfolding artifact_inclusion_system_def
  by (rule add_recursive_definition_formed[OF replay_admission_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma artifact_inclusion_definitions [simp]:
  "system_definitions artifact_inclusion_system=insert 112 (system_definitions replay_admission_system)"
  by (simp add: artifact_inclusion_system_def)

lemma artifact_inclusion_call:
  "schema_call_formed artifact_inclusion_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_inclusion_system \<and> term_formed t"
  using added_variable_calls[OF replay_admission_system_formed
    artifact_inclusion_system_formed[unfolded artifact_inclusion_system_def] replay_admission_call]
  by (simp only: artifact_inclusion_system_def[symmetric])

lemma artifact_inclusion_old_meaning:
  assumes "d\<in>system_definitions replay_admission_system"
  shows "(d,t)\<in>positive_meaning artifact_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_admission_system"
  using added_definition_preserves_old(2)[OF replay_admission_system_formed
    artifact_inclusion_system_formed[unfolded artifact_inclusion_system_def], of d t] assms
  by (auto simp: artifact_inclusion_system_def)

lemma artifact_inclusion_clause [simp]:
  "((112,c),S)\<in>system_clauses artifact_inclusion_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 37 112)"
proof -
  have owned: "((d,c),S)\<in>system_clauses replay_admission_system \<Longrightarrow>
    d\<in>system_definitions replay_admission_system" for d c S
    using replay_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((112,c),S)\<notin>system_clauses replay_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: artifact_inclusion_system_def)
qed

lemma artifact_inclusion_element:
  "(37,t)\<in>positive_meaning artifact_inclusion_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  using artifact_inclusion_old_meaning[of 37 t] replay_admission_old_meaning[of 37 t]
    retention_admission_slot_meaning[of 37 t] replay_slot_reading_components(1)[of t] by auto

interpretation artifact_inclusion_profile: context_list_profile artifact_inclusion_system 37 112
  by (rule context_list_profile.intro) (auto simp: artifact_inclusion_call)

lemma artifact_lookup_entry:
  "(37,Pair_Term f x)\<in>positive_meaning artifact_lookup_system \<longleftrightarrow>
    (\<exists>F row. environment_value_presents F f \<and>
      row\<in>environment_artifacts F \<and> environment_artifact_entry_presents row x)"
  by (auto simp: artifact_lookup_exact environment_artifact_entry_presents_def artifact_at_def)

theorem artifact_inclusion_exact:
  "(112,z)\<in>positive_meaning artifact_inclusion_system \<longleftrightarrow> artifact_inclusion_result z"
  by (simp only: artifact_inclusion_profile.exact artifact_inclusion_element artifact_lookup_entry)

lemma artifact_inclusion_at_entry:
  assumes source: "environment_value_presents F f"
    and entry: "environment_artifact_entry_presents row x"
  shows "(37,Pair_Term f x)\<in>positive_meaning artifact_lookup_system \<longleftrightarrow>
    row\<in>environment_artifacts F"
proof -
  have unique: "G=F" if "environment_value_presents G f" for G
    by (rule environment_value_presents_unique[OF that source])
  have same: "other=row" if "environment_artifact_entry_presents other x" for other
    by (rule environment_artifact_entry_unique[OF that entry])
  show ?thesis by (simp only: artifact_lookup_entry) (use source entry unique same in blast)
qed

theorem artifact_inclusion_on_collection:
  assumes source: "data_collection_presents environment_artifact_entry_presents A a"
    and target: "environment_value_presents F f"
  shows "(112,Pair_Term f a)\<in>positive_meaning artifact_inclusion_system \<longleftrightarrow>
    A\<subseteq>environment_artifacts F"
proof -
  obtain xs ts where rows: "set xs=A" "list_all2 environment_artifact_entry_presents xs ts"
    "a=data_list_term ts" using source unfolding data_collection_presents_def by blast
  have members: "(\<forall>row\<in>A. \<exists>x\<in>set ts. environment_artifact_entry_presents row x) \<and>
    (\<forall>x\<in>set ts. \<exists>row\<in>A. environment_artifact_entry_presents row x)"
    using list_all2_members[OF rows(2)] rows(1) by simp
  have all: "(\<forall>x\<in>set ts. (37,Pair_Term f x)\<in>positive_meaning artifact_lookup_system) \<longleftrightarrow>
    A\<subseteq>environment_artifacts F"
    using members artifact_inclusion_at_entry[OF target] by blast
  show ?thesis by (simp only: rows(3) artifact_inclusion_profile.lists artifact_inclusion_element all)
    (use environment_value_presents_formed[OF target] in blast)
qed

section \<open>Formation and both complete tables admit environment inclusion\<close>

lemma binding_collection_inclusion:
  assumes source: "environment_value_presents E (Pair_Term a b)"
    and target: "environment_value_presents F (Pair_Term c d)"
  shows "(47,Pair_Term b d)\<in>positive_meaning data_subset_system \<longleftrightarrow>
    environment_bindings E\<subseteq>environment_bindings F"
proof -
  have ef: "environment_formed E" and ff: "environment_formed F"
    using source target by (auto simp: environment_value_presents_def)
  obtain xs ys where rows: "set xs=environment_bindings E" "set ys=environment_bindings F"
    "b=data_list_term (map binding_data xs)" "d=data_list_term (map binding_data ys)"
    using source target by (auto simp: environment_value_presents_def data_collection_presents_function)
  have data: "data_elements (map binding_data xs)" "data_elements (map binding_data ys)"
    using binding_data_formed[OF ef] binding_data_formed[OF ff] rows(1,2) by auto
  have subset: "set (map binding_data xs)\<subseteq>set (map binding_data ys) \<longleftrightarrow>
    environment_bindings E\<subseteq>environment_bindings F"
    using rows(1,2) by (auto dest: injD[OF binding_data_injective])
  show ?thesis using data by (simp only: rows(3,4) data_subset_lists subset; blast)
qed

abbreviation environment_inclusion_result :: "factor_term \<Rightarrow> bool" where
  "environment_inclusion_result z \<equiv> \<exists>E F e f. z=Pair_Term e f \<and>
    environment_value_presents E e \<and> environment_value_presents F f \<and> environment_included E F"

definition environment_inclusion_schema :: "(nat,nat,nat) factor_schema" where
  "environment_inclusion_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,26,Pattern_Pair data_x data_y),(1,26,Pattern_Pair data_z data_w),
     (2,112,Pattern_Pair (Pattern_Pair data_z data_w) data_x),
     (3,47,Pattern_Pair data_y data_w)}"

definition environment_inclusion_system :: "(nat,nat,nat,nat) schema_system" where
  "environment_inclusion_system=add_view_definition artifact_inclusion_system 113 data_x {(0,environment_inclusion_schema)}"

lemma environment_inclusion_system_formed [simp]: "schema_system_formed environment_inclusion_system"
  unfolding environment_inclusion_system_def
  by (rule add_recursive_definition_formed[OF artifact_inclusion_system_formed])
    (auto simp: environment_inclusion_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma environment_inclusion_definitions [simp]:
  "system_definitions environment_inclusion_system=insert 113 (system_definitions artifact_inclusion_system)"
  by (simp add: environment_inclusion_system_def)

lemma environment_inclusion_call:
  "schema_call_formed environment_inclusion_system d t \<longleftrightarrow>
    d\<in>system_definitions environment_inclusion_system \<and> term_formed t"
  using added_variable_calls[OF artifact_inclusion_system_formed
    environment_inclusion_system_formed[unfolded environment_inclusion_system_def] artifact_inclusion_call]
  by (simp only: environment_inclusion_system_def[symmetric])

lemma environment_inclusion_old_meaning:
  assumes "d\<in>system_definitions artifact_inclusion_system"
  shows "(d,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_inclusion_system"
  using added_definition_preserves_old(2)[OF artifact_inclusion_system_formed
    environment_inclusion_system_formed[unfolded environment_inclusion_system_def], of d t] assms
  by (auto simp: environment_inclusion_system_def)

lemma environment_inclusion_clause [simp]:
  "((113,c),S)\<in>system_clauses environment_inclusion_system \<longleftrightarrow> (c,S)\<in>{(0,environment_inclusion_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses artifact_inclusion_system \<Longrightarrow>
    d\<in>system_definitions artifact_inclusion_system" for d c S
    using artifact_inclusion_system_formed unfolding schema_system_formed_def by blast
  have absent: "((113,c),S)\<notin>system_clauses artifact_inclusion_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: environment_inclusion_system_def)
qed

lemma environment_inclusion_quotation_meaning:
  assumes "d\<in>system_definitions quotation_admission_system"
  shows "(d,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning quotation_admission_system"
  using environment_inclusion_old_meaning[of d t] artifact_inclusion_old_meaning[of d t]
    replay_admission_old_meaning[of d t] retention_admission_slot_meaning[of d t]
    replay_slot_reading_pattern_meaning[of d t] pattern_instantiation_old_meaning[of d t]
    binder_admission_quotation_meaning[OF assms, of t] assms by auto

lemma environment_inclusion_components:
  "(26,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
  "(112,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (112,t)\<in>positive_meaning artifact_inclusion_system"
  "(47,t)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (47,t)\<in>positive_meaning data_subset_system"
  using environment_inclusion_quotation_meaning[of 26 t] quotation_admission_reading_meaning[of 26 t]
    citation_reading_old_meaning[of 26 t] citation_location_old_meaning[of 26 t]
    citation_interpretation_old_meaning[of 26 t] citation_resolution_old_meaning[of 26 t]
    binding_lookup_old_meaning[of 26 t] artifact_lookup_components(1)[of t]
    environment_inclusion_old_meaning[of 112 t]
    environment_inclusion_quotation_meaning[of 47 t] quotation_admission_old_meaning[of 47 t]
    payload_disjoint_prior_entries(3)[of t] by auto

lemma environment_inclusion_valuation:
  "(113,z)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3}. term_formed (h j)) \<and>
      z=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)) \<and>
      (\<exists>E. environment_value_presents E (Pair_Term (h 0) (h 1))) \<and>
      (\<exists>F. environment_value_presents F (Pair_Term (h 2) (h 3))) \<and>
      (112,Pair_Term (Pair_Term (h 2) (h 3)) (h 0))\<in>positive_meaning artifact_inclusion_system \<and>
      (47,Pair_Term (h 1) (h 3))\<in>positive_meaning data_subset_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: environment_inclusion_schema_def schema_variables_def
      environment_inclusion_call environment_inclusion_components)

theorem environment_inclusion_sound:
  assumes holds: "(113,z)\<in>positive_meaning environment_inclusion_system"
  shows "environment_inclusion_result z"
proof -
  obtain h :: "nat \<Rightarrow> factor_term" and E F where shape: "z=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3))"
    and source: "environment_value_presents E (Pair_Term (h 0) (h 1))"
    and target: "environment_value_presents F (Pair_Term (h 2) (h 3))"
    and calls: "(112,Pair_Term (Pair_Term (h 2) (h 3)) (h 0))\<in>positive_meaning artifact_inclusion_system"
      "(47,Pair_Term (h 1) (h 3))\<in>positive_meaning data_subset_system"
    using holds by (auto simp: environment_inclusion_valuation)
  have rows: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) (h 0)"
    using source by (auto simp: environment_value_presents_def)
  have artifacts: "environment_artifacts E\<subseteq>environment_artifacts F"
    using calls(1) by (simp only: artifact_inclusion_on_collection[OF rows target])
  have bindings: "environment_bindings E\<subseteq>environment_bindings F"
    using calls(2) by (simp only: binding_collection_inclusion[OF source target])
  have included: "environment_included E F" using artifacts bindings by (simp add: environment_included_def)
  show ?thesis using shape source target included by blast
qed

theorem environment_inclusion_complete:
  assumes source: "environment_value_presents E e" and target: "environment_value_presents F f"
    and included: "environment_included E F"
  shows "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
proof -
  obtain a b c d where shapes: "e=Pair_Term a b" "f=Pair_Term c d"
    and rows: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    using source target by (auto simp: environment_value_presents_def)
  have first: "environment_value_presents E (Pair_Term a b)" and second: "environment_value_presents F (Pair_Term c d)"
    using source target by (simp_all only: shapes)
  have artifact_subset: "environment_artifacts E\<subseteq>environment_artifacts F"
    and binding_subset: "environment_bindings E\<subseteq>environment_bindings F"
    using included by (auto simp: environment_included_def)
  have artifact_call: "(112,Pair_Term (Pair_Term c d) a)\<in>positive_meaning artifact_inclusion_system"
    by (rule iffD2[OF artifact_inclusion_on_collection[OF rows second] artifact_subset])
  have binding_call: "(47,Pair_Term b d)\<in>positive_meaning data_subset_system"
    by (rule iffD2[OF binding_collection_inclusion[OF first second] binding_subset])
  let ?h="\<lambda>j::nat. if j=0 then a else if j=1 then b else if j=2 then c else d"
  show ?thesis by (simp only: environment_inclusion_valuation, rule exI[of _ ?h])
    (use artifact_call binding_call first second environment_value_presents_formed[OF first]
      environment_value_presents_formed[OF second] in \<open>auto simp: shapes\<close>)
qed

theorem environment_inclusion_exact:
  "(113,z)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow> environment_inclusion_result z"
  using environment_inclusion_sound environment_inclusion_complete by blast

corollary environment_inclusion_at_source:
  assumes source: "environment_value_presents E e"
  shows "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (\<exists>F. environment_value_presents F f \<and> environment_included E F)"
proof -
  have unique: "G=E" if "environment_value_presents G e" for G
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: environment_inclusion_exact factor_term.inject) (use source unique in blast)
qed

corollary environment_inclusion_on_values:
  assumes source: "environment_value_presents E e" and target: "environment_value_presents F f"
  shows "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    environment_included E F"
  by (simp only: environment_inclusion_at_source[OF source])
    (use target environment_value_presents_unique[OF _ target] in blast)

corollary environment_inclusion_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E a"
    "environment_value_presents F f" "environment_value_presents F b"
  shows "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system \<longleftrightarrow>
    (113,Pair_Term a b)\<in>positive_meaning environment_inclusion_system"
  by (simp only: environment_inclusion_on_values[OF assms(1,3)] environment_inclusion_on_values[OF assms(2,4)])

corollary admitted_environment_antisymmetry:
  assumes "environment_value_presents E e" "environment_value_presents F f"
    "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
    "(113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
  shows "E=F"
  using assms(3,4) by (simp only: environment_inclusion_on_values[OF assms(1,2)]
    environment_inclusion_on_values[OF assms(2,1)]; blast intro: environment_included_antisym)

text \<open>
  Artifact inclusion uses the existing admitted artifact lookup at every row,
  so it compares represented contents at exact uses and permits every complete
  child-artifact presentation. Binding rows have an injective data encoding;
  the existing ordinary subset operation therefore compares their exact
  relation. Both complete environments are admitted, including empty ones.

  The list helper has its existing partial empty-list contract. The enclosing
  inclusion entry establishes both environment roles and checks both complete
  tables. It adds no choice of a smaller source and no new stored field.
\<close>

end
