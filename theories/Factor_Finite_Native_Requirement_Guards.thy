theory Factor_Finite_Native_Requirement_Guards
  imports Factor_Finite_Native_Admission_Installation
begin

section \<open>Reuse the original conjunction on actual native definition sites\<close>

definition finite_native_requirement_schema where
  "finite_native_requirement_schema ds=finite_native_admission_schema
    (finite_requirement_guard_schema (fset_of_list (zip [0..<length ds] ds)))"

lemma finite_native_requirement_schema_occurrences:
  "finite_schema_premises (finite_native_requirement_schema ds)=
    fimage (\<lambda>(i,d). (unary_address i,d,Finite_Variable (unary_address 0)))
      (fset_of_list (zip [0..<length ds] ds))"
  by (simp add: finite_native_requirement_schema_def finite_native_admission_schema_def
    finite_rename_schema_def finite_requirement_guard_schema_def fset_eq_iff fimage.rep_eq image_image split_def)

lemma finite_native_requirement_schema_formed [simp]:
  "schema_formed (decode_finite_schema (finite_native_requirement_schema ds))"
  unfolding finite_native_requirement_schema_def
  by (rule finite_native_admission_schema_formed;
    simp only: finite_requirement_guard_schema_correct fset_of_list.rep_eq
      requirement_sockets_def[symmetric]; rule requirement_guard_formed) simp_all

lemma finite_native_requirement_schema_dependencies [simp]:
  "schema_dependencies (decode_finite_schema (finite_native_requirement_schema ds))=set ds"
  by (simp only: finite_native_requirement_schema_def finite_native_admission_schema_dependencies
    finite_requirement_guard_schema_correct fset_of_list.rep_eq requirement_sockets_def[symmetric]
    requirement_guard_dependencies requirement_sockets_range)

lemma finite_native_requirement_schema_rule:
  "schema_rule_instance (decode_finite_schema (finite_native_requirement_schema ds)) M t \<longleftrightarrow>
    term_formed t \<and> (\<forall>d\<in>set ds. (d,t)\<in>M)"
  by (simp only: finite_native_requirement_schema_def finite_native_admission_rule
    finite_requirement_guard_schema_correct fset_of_list.rep_eq requirement_sockets_def[symmetric]
    requirement_guard_rule[OF requirement_sockets_finite requirement_sockets_functional] requirement_sockets_all)

definition finite_native_requirement_clauses where
  "finite_native_requirement_clauses ds={|([],finite_native_requirement_schema ds)|}"

definition finite_native_requirement_guard where
  "finite_native_requirement_guard ds P=(let d=finite_native_admission_fresh P in
    Some (d,finite_add_view_definition P d (Finite_Variable []) (finite_native_requirement_clauses ds)))"

locale finite_native_requirement_guard_installation =
  fixes P :: "local_address option finite_native_system"
    and ds :: "local_address option definition_site list"
  assumes source: "finite_system_formed P"
    and supported: "set ds\<subseteq>fset (finite_system_definitions P)"
begin

sublocale install: finite_native_admission_installation P "finite_native_requirement_clauses ds"
  by (unfold_locales; (rule source)?)
    (use supported in \<open>auto simp: finite_native_requirement_clauses_def single_valued_def\<close>)

theorem exact:
  "(install.entry,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
    term_formed t \<and> (\<forall>d\<in>set ds. (d,t)\<in>positive_meaning (decode_finite_system P))"
proof -
  have current: "(install.entry,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
      term_formed t \<and> (\<forall>d\<in>set ds. (d,t)\<in>positive_meaning (decode_finite_system install.target))"
    by (simp only: positive_variable_rule_family[OF install.call] install.complete_family;
      simp add: finite_native_requirement_clauses_def map_relation_values_def finite_native_requirement_schema_rule)
  have old: "(d,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
      (d,t)\<in>positive_meaning (decode_finite_system P)" if member: "d\<in>set ds" for d
    by (rule install.old_meaning)
      (use supported member in \<open>simp only: finite_system_definitions_correct; blast\<close>)
  show ?thesis by (simp only: current; use old in blast)
qed

lemma result:
  "finite_native_requirement_guard ds P=Some (install.entry,install.target)"
  by (simp only: finite_native_requirement_guard_def Let_def)

end

end
