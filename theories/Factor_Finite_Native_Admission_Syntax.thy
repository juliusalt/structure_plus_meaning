theory Factor_Finite_Native_Admission_Syntax
  imports Factor_Finite_Requirement_Installation Factor_Finite_Source_Construction Factor_Finite_Checked_Requirements
begin

section \<open>The original admission clauses use native private coordinates\<close>

definition finite_native_admission_schema :: "(nat,nat,'d) finite_factor_schema \<Rightarrow>
    (local_address,local_address,'d) finite_factor_schema" where
  "finite_native_admission_schema S=finite_rename_schema unary_address unary_address id S"

lemma finite_native_admission_schema_correct:
  "decode_finite_schema (finite_native_admission_schema S)=
    rename_schema unary_address unary_address id (decode_finite_schema S)"
  by (simp only: finite_native_admission_schema_def finite_rename_schema_correct)

lemma finite_native_admission_rule:
  "schema_rule_instance (decode_finite_schema (finite_native_admission_schema S)) M t \<longleftrightarrow>
    schema_rule_instance (decode_finite_schema S) M t"
  by (simp only: finite_native_admission_schema_correct;
    rule schema_rule_instance_alpha; rule inj_on_subset[OF unary_address_inj]) simp_all

lemma finite_native_admission_schema_formed:
  assumes "schema_formed (decode_finite_schema S)"
  shows "schema_formed (decode_finite_schema (finite_native_admission_schema S))"
  by (simp only: finite_native_admission_schema_correct;
    rule renamed_schema_formed[OF assms]; rule inj_on_subset[OF unary_address_inj]) simp

lemma finite_native_admission_schema_dependencies:
  "schema_dependencies (decode_finite_schema (finite_native_admission_schema S))=
    schema_dependencies (decode_finite_schema S)"
  by (simp add: finite_native_admission_schema_correct renamed_schema_dependencies)

definition finite_native_pair_clauses where
  "finite_native_pair_clauses a b={|([],finite_native_admission_schema (finite_admitted_pair_schema a b))|}"

definition finite_native_list_clauses where
  "finite_native_list_clauses a d={|
    (unary_address 0,finite_native_admission_schema finite_data_list_nil_schema),
    (unary_address 1,finite_native_admission_schema (finite_admitted_pair_schema a d))|}"

lemma finite_native_pair_clauses_rules:
  "(\<exists>c S. (c,S)\<in>map_relation_values decode_finite_schema (fset (finite_native_pair_clauses a b)) \<and>
      schema_rule_instance S M t) \<longleftrightarrow> schema_rule_instance (admitted_pair_schema a b) M t"
  by (simp add: finite_native_pair_clauses_def map_relation_values_def finite_native_admission_rule)

lemma finite_native_list_clauses_rules:
  "(\<exists>c S. (c,S)\<in>map_relation_values decode_finite_schema (fset (finite_native_list_clauses a d)) \<and>
      schema_rule_instance S M t) \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>list_profile_clauses a d \<and> schema_rule_instance S M t)"
proof -
  have family: "map_relation_values decode_finite_schema (fset (finite_native_list_clauses a d))=
      {(unary_address 0,decode_finite_schema (finite_native_admission_schema finite_data_list_nil_schema)),
       (unary_address 1,decode_finite_schema (finite_native_admission_schema (finite_admitted_pair_schema a d)))}"
    by (simp add: finite_native_list_clauses_def map_relation_values_def)
  show ?thesis by (simp only: family list_profile_clauses_def schema_two_clause_rules
    finite_native_admission_rule finite_data_list_nil_schema_correct finite_admitted_pair_schema_correct
    admitted_pair_schema_list_step)
qed

section \<open>Fresh provisional definitions are constructed in the recovered program\<close>

definition finite_native_admission_fresh :: "local_address option finite_native_system \<Rightarrow>
    local_address option definition_site" where
  "finite_native_admission_fresh P=(finite_fresh_use_map
    (fimage fst (finite_system_definitions P)) None (Some []),[])"

lemma finite_native_admission_fresh_absent:
  "finite_native_admission_fresh P \<notin> fset (finite_system_definitions P)"
proof -
  have outside: "finite_fresh_use_map (fimage fst (finite_system_definitions P)) None (Some [])
      \<notin> insert None (fset (fimage fst (finite_system_definitions P)))"
    by (simp only: finite_fresh_use_map_exact; rule fresh_use_map_outside) simp

  show ?thesis
  proof
    assume member: "finite_native_admission_fresh P\<in>fset (finite_system_definitions P)"
    have mapped: "fst (finite_native_admission_fresh P)\<in>fset (fimage fst (finite_system_definitions P))"
      by (simp only: fimage.rep_eq; rule imageI[OF member])
    show False using outside mapped
      by (simp only: finite_native_admission_fresh_def fst_conv; blast)
  qed
qed

definition finite_native_admission_leaf where
  "finite_native_admission_leaf d P=(if d |\<in>| finite_system_definitions P then Some (d,P) else None)"

definition finite_native_admission_pair where
  "finite_native_admission_pair a b P=(let d=finite_native_admission_fresh P in
    Some (d,finite_add_view_definition P d (Finite_Variable []) (finite_native_pair_clauses a b)))"

definition finite_native_admission_list where
  "finite_native_admission_list a P=(let d=finite_native_admission_fresh P in
    Some (d,finite_add_view_definition P d (Finite_Variable []) (finite_native_list_clauses a d)))"

definition finite_construct_native_admission where
  "finite_construct_native_admission g P=construct_admission_goal finite_native_admission_leaf
    finite_native_admission_pair finite_native_admission_list g P"

definition finite_native_admission_target where
  "finite_native_admission_target E pu pr g=finite_native_source_target
    (\<lambda>P. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)
    (finite_construct_native_admission g) E pu pr"

definition finite_construct_source_admission where
  "finite_construct_source_admission E pu pr g=finite_construct_source
    (\<lambda>P. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)
    (finite_construct_native_admission g) E pu pr"

text \<open>
  The source reader supplies the complete program. Every requested leaf must
  already be a definition of that source. The shared goal constructor adds the
  original pair and list clause families with injectively renamed private
  coordinates. The list step calls its own new definition at the tail.

  The final source extension checks the complete constructed program and
  allocates native positions. The returned entry uses that same placement.
  Factor_Finite_Native_Admission_Construction establishes the complete goal
  meaning and source preservation for this same operation.
\<close>

end
