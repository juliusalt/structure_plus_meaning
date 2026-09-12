theory Finite_Keyed_Table_Comparison
  imports Factor_Keyed_Table_Comparison Factor_Executable_Data_Values
    Factor_Data_Set_Comparison Factor_Library_Compilation Factor_Clause_Rule_Application Factor_Guided_Investigation
begin

abbreviation decoded_keyed_rows where
  "decoded_keyed_rows xs \<equiv> map (map_prod decode_finite_term decode_finite_term) xs"

definition finite_keyed_rows_formed :: "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow> bool" where
  "finite_keyed_rows_formed xs \<longleftrightarrow>
    (\<forall>(k,v)\<in>set xs. finite_term_formed k \<and> finite_data_projection k=Some k \<and> finite_term_formed v)"

definition finite_keyed_table_comparison ::
  "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
    (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> bool" where
  "finite_keyed_table_comparison xs ys \<longleftrightarrow>
    finite_keyed_rows_formed xs \<and> finite_keyed_rows_formed ys \<and>
    distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"

definition finite_keyed_data_comparison ::
  "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
    (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> bool" where
  "finite_keyed_data_comparison xs ys \<longleftrightarrow>
    finite_keyed_rows_formed xs \<and> finite_keyed_rows_formed ys \<and>
    (\<forall>(k,v)\<in>set xs. finite_data_projection v=Some v) \<and>
    (\<forall>(k,v)\<in>set ys. finite_data_projection v=Some v) \<and> set xs=set ys"

definition finite_key_fibre_holds :: "finite_factor_term \<Rightarrow>
    (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> finite_factor_term list \<Rightarrow> bool" where
  "finite_key_fibre_holds k xs vs \<longleftrightarrow>
    finite_term_formed k \<and> finite_data_projection k=Some k \<and>
    finite_keyed_rows_formed xs \<and> vs=key_values k xs"

lemma finite_data_projection_self_contained [simp]:
  "finite_data_projection x=Some x \<longleftrightarrow> self_contained_term (decode_finite_term x)"
  by (simp only: finite_data_projection_exact; simp)

lemma finite_keyed_rows_formed_correct:
  "finite_keyed_rows_formed xs \<longleftrightarrow> formed_key_rows (decoded_keyed_rows xs)"
  by (auto simp: finite_keyed_rows_formed_def finite_term_formed_correct)

lemma decoded_keyed_rows_set:
  "set (decoded_keyed_rows xs)=set (decoded_keyed_rows ys) \<longleftrightarrow> set xs=set ys"
proof -
  have injective: "inj (map_prod decode_finite_term decode_finite_term)"
    by (auto simp: inj_def map_prod_def)
  show ?thesis by (simp only: set_map inj_image_eq_iff[OF injective])
qed

lemma decoded_keyed_rows_keys:
  "distinct (map fst (decoded_keyed_rows xs)) \<longleftrightarrow> distinct (map fst xs)"
proof -
  have projection: "map fst (decoded_keyed_rows xs)=map decode_finite_term (map fst xs)"
    by (simp add: comp_def case_prod_unfold)
  show ?thesis by (simp add: projection distinct_map inj_on_def)
qed

theorem finite_keyed_table_comparison_correct:
  "finite_keyed_table_comparison xs ys \<longleftrightarrow>
    (353,Pair_Term (pair_list_term (decoded_keyed_rows xs)) (pair_list_term (decoded_keyed_rows ys)))
      \<in>positive_meaning keyed_table_comparison_system"
  by (simp only: keyed_table_comparison_lists finite_keyed_table_comparison_def
    finite_keyed_rows_formed_correct decoded_keyed_rows_keys decoded_keyed_rows_set)

theorem finite_keyed_table_admission_correct:
  "finite_keyed_table_comparison xs xs \<longleftrightarrow>
    (21,pair_list_term (decoded_keyed_rows xs))\<in>positive_meaning keyed_list_system"
  by (simp only: finite_keyed_table_comparison_correct keyed_table_self_admission)

theorem finite_keyed_data_comparison_correct:
  "finite_keyed_data_comparison xs ys \<longleftrightarrow>
    (219,Pair_Term (pair_list_term (decoded_keyed_rows xs)) (pair_list_term (decoded_keyed_rows ys)))
      \<in>positive_meaning data_set_comparison_system"
proof -
  have identity: "inj (\<lambda>(k,v). Pair_Term k v)" by (auto simp: inj_def)
  have paired_sets: "set (map (\<lambda>(k,v). Pair_Term k v) (decoded_keyed_rows xs))=
      set (map (\<lambda>(k,v). Pair_Term k v) (decoded_keyed_rows ys)) \<longleftrightarrow>
      set (decoded_keyed_rows xs)=set (decoded_keyed_rows ys)"
    by (simp only: set_map inj_image_eq_iff[OF identity])
  have row_sets: "set (map (\<lambda>(k,v). Pair_Term k v) (decoded_keyed_rows xs))=
      set (map (\<lambda>(k,v). Pair_Term k v) (decoded_keyed_rows ys)) \<longleftrightarrow> set xs=set ys"
    by (simp only: paired_sets decoded_keyed_rows_set)
  show ?thesis by (simp only: data_set_comparison_lists row_sets)
    (auto simp: finite_keyed_data_comparison_def finite_keyed_rows_formed_def finite_term_formed_correct)
qed

theorem finite_key_fibre_holds_correct:
  "finite_key_fibre_holds k xs vs \<longleftrightarrow>
    (28,key_fibre_argument (decode_finite_term k) (pair_list_term (decoded_keyed_rows xs))
      (data_list_term (map decode_finite_term vs)))\<in>positive_meaning key_fibre_system"
proof -
  have injective: "inj decode_finite_term" by (auto simp: inj_def)
  have fibres: "key_values (decode_finite_term k) (decoded_keyed_rows xs)=map decode_finite_term (key_values k xs)"
    using key_values_map[OF injective, where k=k and g=decode_finite_term and xs=xs]
    by (simp only: map_prod_def)
  show ?thesis by (simp only: key_fibre_lists fibres data_list_term_injective
    injective_mapped_lists[OF injective] finite_key_fibre_holds_def finite_keyed_rows_formed_correct
    finite_term_formed_correct finite_data_projection_self_contained)
qed

section \<open>Generated applications consume the actual ordinary clauses\<close>

definition finite_keyed_table_row_schema where
  "finite_keyed_table_row_schema=finite_schema_of (keyed_table_row_schema 28)"

definition finite_keyed_table_nil_schema where
  "finite_keyed_table_nil_schema=finite_schema_of context_list_nil_schema"

definition finite_keyed_table_step_schema where
  "finite_keyed_table_step_schema=finite_schema_of (context_list_step_schema 351 352)"

definition finite_keyed_table_whole_schema where
  "finite_keyed_table_whole_schema=finite_schema_of (related_set_schema 352 352)"

lemmas finite_keyed_table_row_code [code]=finite_keyed_table_row_schema_def
  [unfolded keyed_table_row_schema_def finite_schema_of_def map_relation_values_def, simplified]
lemmas finite_keyed_table_nil_code [code]=finite_keyed_table_nil_schema_def
  [unfolded context_list_nil_schema_def finite_schema_of_def map_relation_values_def, simplified]
lemmas finite_keyed_table_step_code [code]=finite_keyed_table_step_schema_def
  [unfolded context_list_step_schema_def finite_schema_of_def map_relation_values_def, simplified]
lemmas finite_keyed_table_whole_code [code]=finite_keyed_table_whole_schema_def
  [unfolded related_set_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma finite_keyed_table_schemas:
  "decode_finite_schema finite_keyed_table_row_schema=keyed_table_row_schema 28"
  "decode_finite_schema finite_keyed_table_nil_schema=context_list_nil_schema"
  "decode_finite_schema finite_keyed_table_step_schema=context_list_step_schema 351 352"
  "decode_finite_schema finite_keyed_table_whole_schema=related_set_schema 352 352"
  unfolding finite_keyed_table_row_schema_def finite_keyed_table_nil_schema_def
    finite_keyed_table_step_schema_def finite_keyed_table_whole_schema_def
  by (rule decode_finite_schema_of; auto simp: keyed_table_schema_defs
    schema_formed_def single_valued_def octets_formed_def)+

definition keyed_table_construction_library ::
  "(nat\<times>(nat,nat,nat) finite_factor_schema\<times>(nat\<times>nat\<times>nat finite_term_pattern) list) list" where
  "keyed_table_construction_library=finite_compiled_library
    [(351,finite_keyed_table_row_schema),(352,finite_keyed_table_nil_schema),
     (352,finite_keyed_table_step_schema),(353,finite_keyed_table_whole_schema)]"

lemma keyed_table_compiled_clause:
  assumes member: "(d,S,ps)\<in>set keyed_table_construction_library"
  shows "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses keyed_table_comparison_system \<and>
    (d,Pattern_Variable 0)\<in>system_interfaces keyed_table_comparison_system"
proof -
  have clause: "\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses keyed_table_comparison_system"
    and entry: "d\<in>{351,352,353}"
    using member by (auto simp: keyed_table_construction_library_def finite_compiled_library_member
      finite_keyed_table_schemas keyed_table_comparison_clause keyed_table_clause_family_def context_list_clauses_def)
  have interface: "(d,Pattern_Variable 0)\<in>system_interfaces keyed_table_comparison_system"
    using entry by (auto simp: keyed_table_comparison_system_def system_union_interfaces)
  show ?thesis using clause interface by blast
qed

theorem keyed_table_construction_member_sound:
  assumes member: "(d,S,ps)\<in>set keyed_table_construction_library"
    and rule_instance: "schema_rule_instance (decode_finite_schema S) (positive_meaning keyed_table_comparison_system) t"
  shows "(d,t)\<in>positive_meaning keyed_table_comparison_system"
proof -
  obtain c where actual: "((d,c),decode_finite_schema S)\<in>system_clauses keyed_table_comparison_system"
    and interface: "(d,Pattern_Variable 0)\<in>system_interfaces keyed_table_comparison_system"
    using keyed_table_compiled_clause[OF member] by blast
  show ?thesis by (rule positive_variable_clause_rule[OF keyed_table_comparison_formed actual interface rule_instance])
qed

theorem keyed_table_selected_guided_sound:
  assumes selected: "set L\<subseteq>set keyed_table_construction_library"
    and known: "image decode_finite_call_term (fset K)\<subseteq>positive_meaning keyed_table_comparison_system"
  shows "image decode_finite_call_term (finite_inference_result (finite_guided_rules n L C Q) K)
    \<subseteq>positive_meaning keyed_table_comparison_system"
  by (rule finite_guided_closure_sound)
    (use selected known keyed_table_construction_member_sound in blast)+

theorem finite_key_fibre_known_sound:
  assumes "finite_key_fibre_holds k xs vs"
  shows "(28,key_fibre_argument (decode_finite_term k) (pair_list_term (decoded_keyed_rows xs))
    (data_list_term (map decode_finite_term vs)))\<in>positive_meaning keyed_table_comparison_system"
  using assms by (simp only: keyed_table_fibre_meaning finite_key_fibre_holds_correct)

text \<open>
  The finite operations have exact native-call contracts on their complete
  decoded operands. They keep the target-containing values required by symbolic
  pattern observations. The older data-set comparator is exported separately
  as a diagnostic control with its original narrower value boundary.

  The construction library comes from the same actual native clauses and the
  common complete premise compiler. Its soundness remains conditional on its
  actual instantiated premises. Successful construction does not establish
  those premises or admit a whole symbolic proof graph.
\<close>

export_code finite_keyed_table_comparison finite_keyed_data_comparison finite_key_fibre_holds
  keyed_table_construction_library checking SML

end
