theory Factor_Finite_Native_Admission_Installation
  imports Factor_Finite_Native_Admission_Syntax
begin

section \<open>One fresh native definition retains the complete source boundary\<close>

locale finite_native_admission_installation =
  fixes P :: "local_address option finite_native_system"
    and C :: "(local_address\<times>local_address option finite_native_schema) fset"
  assumes source: "finite_system_formed P"
    and functional: "single_valued (fset C)"
    and clauses: "\<And>c S. (c,S)\<in>fset C \<Longrightarrow> schema_formed (decode_finite_schema S)"
    and dependencies: "\<And>c S. (c,S)\<in>fset C \<Longrightarrow>
      schema_dependencies (decode_finite_schema S)\<subseteq>
        insert (finite_native_admission_fresh P) (fset (finite_system_definitions P))"
begin

abbreviation entry where "entry \<equiv> finite_native_admission_fresh P"
abbreviation target where "target \<equiv> finite_add_view_definition P entry (Finite_Variable []) C"
abbreviation family where "family \<equiv> map_relation_values decode_finite_schema (fset C)"

lemma old_formed: "schema_system_formed (decode_finite_system P)"
  using source by (simp only: finite_system_formed_correct)

lemma fresh: "entry\<notin>system_definitions (decode_finite_system P)"
  by (subst finite_system_definitions_correct[symmetric]; rule finite_native_admission_fresh_absent)

lemma formed: "schema_system_formed (decode_finite_system target)"
proof -
  have functional_family: "single_valued family"
    using functional by (auto simp: single_valued_def)
  have formed_family: "\<forall>c S. (c,S)\<in>family \<longrightarrow> schema_formed S"
    using clauses by auto
  have callees: "schema_dependencies S\<subseteq>insert entry (system_definitions (decode_finite_system P))"
    if member: "(c,S)\<in>family" for c S
  proof -
    obtain V where original: "(c,V)\<in>fset C" and decoded: "S=decode_finite_schema V"
      using member by auto
    show ?thesis using dependencies[OF original]
      by (simp only: decoded finite_system_definitions_correct)
  qed
  show ?thesis
    by (simp only: finite_add_view_definition_correct decode_finite_pattern.simps;
      rule add_recursive_definition_formed[OF old_formed fresh])
      (use functional_family formed_family callees in auto)
qed

lemma extension: "admission_extension (decode_finite_system P) (decode_finite_system target)"
  using old_formed formed fresh
  by (auto simp: admission_extension_def systems_agree_on_def)

lemma member: "entry\<in>system_definitions (decode_finite_system target)"
  by simp

lemma call: "schema_call_formed (decode_finite_system target) entry t \<longleftrightarrow> term_formed t"
  by (simp only: finite_add_view_definition_correct decode_finite_pattern.simps;
    rule added_fresh_variable_call[OF fresh])
    (use formed in \<open>simp only: finite_add_view_definition_correct decode_finite_pattern.simps\<close>)

lemma complete_family: "system_clause_family (decode_finite_system target) entry=family"
  by (simp only: finite_add_view_definition_correct decode_finite_pattern.simps;
    rule added_fresh_clause_family[OF old_formed fresh])

lemma old_meaning:
  assumes "d\<in>system_definitions (decode_finite_system P)"
  shows "(d,t)\<in>positive_meaning (decode_finite_system target) \<longleftrightarrow>
    (d,t)\<in>positive_meaning (decode_finite_system P)"
  by (rule admission_extension_meaning[OF extension assms])

end

section \<open>The constructed pair and list have their original component meanings\<close>

locale finite_native_pair_installation =
  fixes P :: "local_address option finite_native_system"
    and a b :: "local_address option definition_site"
  assumes source: "finite_system_formed P"
    and first: "a\<in>fset (finite_system_definitions P)"
    and second: "b\<in>fset (finite_system_definitions P)"
begin

sublocale install: finite_native_admission_installation P "finite_native_pair_clauses a b"
  by (unfold_locales; (rule source)?)
    (use first second in \<open>auto simp: finite_native_pair_clauses_def single_valued_def
      finite_native_admission_schema_dependencies intro: finite_native_admission_schema_formed\<close>)

lemma exact:
  "(install.entry,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning (decode_finite_system P) \<and>
      (b,y)\<in>positive_meaning (decode_finite_system P))"
proof -
  have constructed: "(install.entry,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
      (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning (decode_finite_system install.target) \<and>
        (b,y)\<in>positive_meaning (decode_finite_system install.target))"
    by (rule admitted_pair_rule_family[OF install.call])
      (simp only: install.complete_family finite_native_pair_clauses_rules)
  show ?thesis by (simp only: constructed
    install.old_meaning[OF first[unfolded finite_system_definitions_correct]]
    install.old_meaning[OF second[unfolded finite_system_definitions_correct]])
qed

lemma result:
  "finite_native_admission_pair a b P=Some (install.entry,install.target)"
  by (simp only: finite_native_admission_pair_def Let_def)

end

locale finite_native_list_installation =
  fixes P :: "local_address option finite_native_system"
    and a :: "local_address option definition_site"
  assumes source: "finite_system_formed P"
    and element: "a\<in>fset (finite_system_definitions P)"
begin

sublocale install: finite_native_admission_installation P
    "finite_native_list_clauses a (finite_native_admission_fresh P)"
  by (unfold_locales; (rule source)?)
    (use element in \<open>auto simp: finite_native_list_clauses_def single_valued_def
      finite_native_admission_schema_dependencies intro: finite_native_admission_schema_formed\<close>)

sublocale semantics: list_rule_relation "positive_meaning (decode_finite_system install.target)" a install.entry
  by (rule list_profile_rule_family[OF install.call])
    (simp only: install.complete_family finite_native_list_clauses_rules)

lemma exact:
  "(install.entry,t)\<in>positive_meaning (decode_finite_system install.target) \<longleftrightarrow>
    (\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (a,x)\<in>positive_meaning (decode_finite_system P)))"
  by (simp only: semantics.exact install.old_meaning[OF element[unfolded finite_system_definitions_correct]])

lemma result:
  "finite_native_admission_list a P=Some (install.entry,install.target)"
  by (simp only: finite_native_admission_list_def Let_def)

end

end
