theory Factor_Recursive_Groups
  imports Factor_System_Composition Factor_System_Restriction
begin

section \<open>A finite group may call its own definitions and a formed base\<close>

definition schema_system_formed_over ::
  "'d set \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> bool" where
  "schema_system_formed_over D Q \<longleftrightarrow>
    finite (system_interfaces Q) \<and> single_valued (system_interfaces Q) \<and>
    (\<forall>d p. (d,p)\<in>system_interfaces Q \<longrightarrow> pattern_formed p) \<and>
    finite (system_clauses Q) \<and> single_valued (system_clauses Q) \<and>
    (\<forall>d c S. ((d,c),S)\<in>system_clauses Q \<longrightarrow>
      d\<in>system_definitions Q \<and> schema_formed S \<and>
      schema_dependencies S\<subseteq>D\<union>system_definitions Q)"

lemma schema_system_formed_over_empty [simp]:
  "schema_system_formed_over {} Q \<longleftrightarrow> schema_system_formed Q"
  by (simp add: schema_system_formed_over_def schema_system_formed_def)

lemma schema_system_formed_over_mono:
  assumes "schema_system_formed_over D Q" "D\<subseteq>E"
  shows "schema_system_formed_over E Q"
  using assms by (auto simp: schema_system_formed_over_def; blast)

theorem schema_system_formed_over_families:
  assumes interfaces: "system_interfaces Q={(d,p d) |d. d\<in>D}"
    and clauses: "system_clauses Q={((d,c),S). d\<in>D \<and> (c,S)\<in>C d}"
    and finite: "finite D"
    and patterns: "\<And>d. d\<in>D \<Longrightarrow> pattern_formed (p d)"
    and families: "\<And>d. d\<in>D \<Longrightarrow> finite (C d)"
    and functional: "\<And>d. d\<in>D \<Longrightarrow> single_valued (C d)"
    and schemas: "\<And>d c S. d\<in>D \<Longrightarrow> (c,S)\<in>C d \<Longrightarrow>
      schema_formed S \<and> schema_dependencies S\<subseteq>E\<union>D"
  shows "schema_system_formed_over E Q"
proof -
  have domain: "system_definitions Q=D"
    by (auto simp: system_definitions_def rel_dom_def interfaces)
  have interface_image: "system_interfaces Q=(\<lambda>d. (d,p d)) ` D"
    by (auto simp: interfaces)
  have clause_union: "system_clauses Q=(\<Union>d\<in>D. (\<lambda>(c,S). ((d,c),S)) ` C d)"
    by (auto simp: clauses)
  have finite_material: "finite (system_interfaces Q)" "finite (system_clauses Q)"
    using finite families by (simp_all add: interface_image clause_union)
  have interface_functional: "single_valued (system_interfaces Q)"
    by (auto simp: interfaces single_valued_def)
  have clause_functional: "single_valued (system_clauses Q)"
    using functional by (auto simp: clauses single_valued_def; blast)
  show ?thesis using finite_material interface_functional clause_functional patterns schemas
    by (auto simp: schema_system_formed_over_def interfaces clauses domain; blast)
qed

definition system_external_dependencies :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set" where
  "system_external_dependencies Q=rel_ran (system_dependency_edges Q)-system_definitions Q"

lemma system_external_dependencies_clauses:
  "system_external_dependencies Q=
    (\<Union>row\<in>system_clauses Q. schema_dependencies (snd row))-system_definitions Q"
  by (auto simp: system_external_dependencies_def system_dependency_edges_def rel_ran_def; blast)

lemma system_external_dependencies_boundary:
  assumes "schema_system_formed_over D Q"
  shows "system_external_dependencies Q\<subseteq>D"
  using assms by (auto simp: schema_system_formed_over_def system_external_dependencies_def
    system_dependency_edges_def rel_ran_def; blast)

lemma schema_system_formed_over_actual_dependencies:
  assumes formed: "schema_system_formed_over D Q"
  shows "schema_system_formed_over (system_external_dependencies Q) Q"
proof -
  have dependencies: "schema_dependencies S\<subseteq>system_external_dependencies Q\<union>system_definitions Q"
    if "((d,c),S)\<in>system_clauses Q" for d c S
    using that by (auto simp: system_external_dependencies_def system_dependency_edges_def rel_ran_def)
  show ?thesis using formed dependencies unfolding schema_system_formed_over_def by blast
qed

locale positive_definition_group =
  fixes P Q :: "('a,'s,'d,'c) schema_system"
  assumes source_formed: "schema_system_formed P"
    and group_formed: "schema_system_formed_over (system_definitions P) Q"
    and separate: "system_definitions P\<inter>system_definitions Q={}"
begin

abbreviation extended where "extended \<equiv> system_union P Q"

lemma no_old_interface:
  assumes "d\<in>system_definitions Q"
  shows "(d,p)\<notin>system_interfaces P"
  using assms separate by (auto simp: system_definitions_def rel_dom_def)

lemma no_group_interface:
  assumes "d\<in>system_definitions P"
  shows "(d,p)\<notin>system_interfaces Q"
  using assms separate by (auto simp: system_definitions_def rel_dom_def)

lemma no_old_clause:
  assumes "d\<in>system_definitions Q"
  shows "((d,c),S)\<notin>system_clauses P"
  using source_formed separate assms unfolding schema_system_formed_def by blast

lemma no_group_clause:
  assumes "d\<in>system_definitions P"
  shows "((d,c),S)\<notin>system_clauses Q"
  using group_formed separate assms unfolding schema_system_formed_over_def by blast

theorem formed: "schema_system_formed extended"
proof -
  have finite: "finite (system_interfaces extended)" "finite (system_clauses extended)"
    using source_formed group_formed
    by (auto simp: system_union_def schema_system_formed_def schema_system_formed_over_def)
  have old_interfaces: "single_valued (system_interfaces P)"
    and old_clauses: "single_valued (system_clauses P)"
    using source_formed unfolding schema_system_formed_def by blast+
  have new_interfaces: "single_valued (system_interfaces Q)"
    and new_clauses: "single_valued (system_clauses Q)"
    using group_formed unfolding schema_system_formed_over_def by blast+
  have interfaces_disjoint: "\<And>d p q. (d,p)\<in>system_interfaces P \<Longrightarrow>
      (d,q)\<in>system_interfaces Q \<Longrightarrow> False"
    using separate by (auto simp: system_definitions_def rel_dom_def)
  have clauses_disjoint: "\<And>d c S T. ((d,c),S)\<in>system_clauses P \<Longrightarrow>
      ((d,c),T)\<in>system_clauses Q \<Longrightarrow> False"
  proof -
    fix d c S T assume old: "((d,c),S)\<in>system_clauses P" and new: "((d,c),T)\<in>system_clauses Q"
    have inside: "d\<in>system_definitions P" "d\<in>system_definitions Q"
      using source_formed old group_formed new
      unfolding schema_system_formed_def schema_system_formed_over_def by blast+
    show False using inside separate by blast
  qed
  have interfaces: "single_valued (system_interfaces extended)"
    using old_interfaces new_interfaces interfaces_disjoint
    by (auto simp: single_valued_def; blast)
  have clauses: "single_valued (system_clauses extended)"
    using old_clauses new_clauses clauses_disjoint
    by (auto simp: single_valued_def; blast)
  have patterns: "\<forall>d p. (d,p)\<in>system_interfaces extended \<longrightarrow> pattern_formed p"
    using source_formed group_formed
    by (auto simp: schema_system_formed_def schema_system_formed_over_def)
  have schemas: "\<forall>d c S. ((d,c),S)\<in>system_clauses extended \<longrightarrow>
    d\<in>system_definitions extended \<and> schema_formed S \<and>
    schema_dependencies S\<subseteq>system_definitions extended"
    using source_formed group_formed
    by (auto simp: schema_system_formed_def schema_system_formed_over_def; blast)
  show ?thesis using finite interfaces clauses patterns schemas by (simp only: schema_system_formed_def)
qed

theorem old_agreement: "systems_agree_on P extended (system_definitions P)"
  using no_group_interface no_group_clause by (auto simp: systems_agree_on_def)

theorem group_agreement: "systems_agree_on Q extended (system_definitions Q)"
  using no_old_interface no_old_clause by (auto simp: systems_agree_on_def)

lemma group_clauses:
  assumes "d\<in>system_definitions Q"
  shows "((d,c),S)\<in>system_clauses extended \<longleftrightarrow> ((d,c),S)\<in>system_clauses Q"
  using no_old_clause[OF assms] by simp

theorem old_calls:
  assumes "d\<in>system_definitions P"
  shows "schema_call_formed extended d t \<longleftrightarrow> schema_call_formed P d t"
  using schema_call_agreement[OF source_formed formed old_agreement assms] by blast

theorem old_meaning:
  assumes "d\<in>system_definitions P"
  shows "(d,t)\<in>positive_meaning extended \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have closed: "system_dependency_closed P (system_definitions P)"
    using system_dependency_boundary(1)[OF source_formed] by (auto simp: system_dependency_closed_def)
  show ?thesis using positive_meaning_dependency_locality[OF source_formed formed old_agreement closed assms] by blast
qed

theorem group_calls:
  assumes "d\<in>system_definitions Q"
  shows "schema_call_formed extended d t \<longleftrightarrow>
    (\<exists>p. (d,p)\<in>system_interfaces Q \<and> pattern_accepts p t)"
  using no_old_interface[OF assms] by (simp only: schema_call_formed_def formed system_union_interfaces) blast

theorem variable_calls:
  assumes prior: "schema_call_formed P d t \<longleftrightarrow> d\<in>system_definitions P \<and> term_formed t"
    and interfaces: "\<And>e p. (e,p)\<in>system_interfaces Q \<longleftrightarrow> e\<in>D \<and> p=Pattern_Variable a"
  shows "schema_call_formed extended d t \<longleftrightarrow> d\<in>system_definitions extended \<and> term_formed t"
proof -
  have domain: "system_definitions Q=D" using interfaces
    by (auto simp: system_definitions_def rel_dom_def)
  have calls: "schema_call_formed extended d t \<longleftrightarrow>
      schema_call_formed P d t \<or> (d\<in>D \<and> term_formed t)"
    by (simp only: schema_call_formed_def formed source_formed system_union_interfaces interfaces) auto
  show ?thesis by (simp only: calls prior system_union_definitions domain) blast
qed

theorem rebased_agreement:
  assumes target: "schema_system_formed R"
    and agreement: "systems_agree_on P R (system_definitions P)"
    and fresh: "system_definitions R\<inter>system_definitions Q={}"
  shows "systems_agree_on extended (system_union R Q) (system_definitions extended)"
proof -
  have absent_interface: "(d,p)\<notin>system_interfaces R" if "d\<in>system_definitions Q" for d p
    using fresh that by (auto simp: system_definitions_def rel_dom_def)
  have absent_clause: "((d,c),S)\<notin>system_clauses R" if "d\<in>system_definitions Q" for d c S
    using target fresh that unfolding schema_system_formed_def by blast
  show ?thesis using agreement no_old_interface no_old_clause absent_interface absent_clause
    by (auto simp: systems_agree_on_def)
qed

theorem native_total:
  "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E u T.
    inj_on g (system_definitions P\<union>system_definitions Q) \<and> closed_native_package_at E u [] T \<and>
    native_package_environment E u []=E \<and> system_alpha_variant (rename_system g extended) T \<and>
    positive_meaning T=map_prod g id ` positive_meaning extended"
  using program_compilation_total[OF formed] by simp

end

text \<open>
  A recursive group is a finite ordinary system whose actual dependencies may
  reach its own definitions and a supplied formed base. Relative formation
  changes only that dependency boundary. Every interface, clause, and premise
  remains present, with the existing functionality and formation conditions.

  The existing ordinary union closes the group. The base has no new callees,
  so its whole meaning and all its call boundaries are preserved. Definitions
  in the group acquire meaning in this combined program. The unclosed group
  is not assigned a separate native meaning and supplies no external truth
  parameter. Positive dependency cycles use the existing least fixed point.

  This construction stores no group label, ordering, or certificate field.
  Its relative domain is a proof boundary. Native compilation uses the actual
  combined definitions before any future operand is supplied.
\<close>

end
