theory Factor_View_Definitions
  imports Factor_Compiled_Applications Factor_Positive_Locality
begin

section \<open>Rule support is observed only at explicit callees\<close>

lemma schema_instance_dependency:
  assumes inst: "schema_instance S V t Q" and member: "(s,d,x) \<in> Q"
  shows "d \<in> schema_dependencies S"
proof -
  have target: "d \<in> fst ` rel_ran Q"
    using member by (auto simp: rel_ran_def intro: rev_image_eqI)
  show ?thesis using target schema_instance_target_boundary[OF inst] by simp
qed

lemma schema_rule_support_agreement:
  assumes agree: "\<forall>d\<in>schema_dependencies S. \<forall>x. (d,x) \<in> X \<longleftrightarrow> (d,x) \<in> Y"
  shows "schema_rule_instance S X t \<longleftrightarrow> schema_rule_instance S Y t"
proof -
  have support: "\<And>V Q. schema_instance S V t Q \<Longrightarrow>
    ((\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> (d,x) \<in> X) \<longleftrightarrow>
     (\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> (d,x) \<in> Y))"
  proof -
    fix V Q assume inst: "schema_instance S V t Q"
    have inside: "\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> d \<in> schema_dependencies S"
      by (intro allI impI; rule schema_instance_dependency[OF inst]; assumption)
    show "(\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> (d,x) \<in> X) \<longleftrightarrow>
      (\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> (d,x) \<in> Y)"
      using inside agree by blast
  qed
  show ?thesis using support unfolding schema_rule_instance_def by blast
qed

section \<open>A fresh definition over already formed dependencies\<close>

definition add_view_definition ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> 'a term_pattern \<Rightarrow>
    ('c \<times> ('a,'s,'d) factor_schema) set \<Rightarrow> ('a,'s,'d,'c) schema_system" where
  "add_view_definition P d p C =
    \<lparr>system_interfaces = insert (d,p) (system_interfaces P),
     system_clauses = system_clauses P \<union> (\<lambda>(c,S). ((d,c),S)) ` C\<rparr>"

lemma added_view_interfaces [simp]:
  "(e,q) \<in> system_interfaces (add_view_definition P d p C) \<longleftrightarrow>
    (e=d \<and> q=p) \<or> (e,q) \<in> system_interfaces P"
  by (simp add: add_view_definition_def)

lemma added_view_clauses [simp]:
  "((e,c),S) \<in> system_clauses (add_view_definition P d p C) \<longleftrightarrow>
    ((e,c),S) \<in> system_clauses P \<or> (e=d \<and> (c,S) \<in> C)"
  by (auto simp: add_view_definition_def)

lemma added_view_definitions [simp]:
  "system_definitions (add_view_definition P d p C) = insert d (system_definitions P)"
  by (auto simp: system_definitions_def rel_dom_def)

lemma add_recursive_definition_formed:
  assumes source_formed: "schema_system_formed P" and fresh: "d\<notin>system_definitions P"
    and interface_formed: "pattern_formed p" and finite_clauses: "finite C"
    and functional_clauses: "single_valued C"
    and clauses_formed: "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_formed S"
    and callees: "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S \<subseteq> insert d (system_definitions P)"
  shows "schema_system_formed (add_view_definition P d p C)"
proof -
  let ?T="add_view_definition P d p C"
  have no_interface: "(d,q)\<notin>system_interfaces P" for q
    using fresh by (auto simp: system_definitions_def rel_dom_def)
  have no_clause: "((d,c),S)\<notin>system_clauses P" for c S
    using source_formed fresh by (auto simp: schema_system_formed_def)
  have finite: "finite (system_interfaces ?T)" "finite (system_clauses ?T)"
    using source_formed finite_clauses by (simp_all add: add_view_definition_def schema_system_formed_def)
  have old_isv: "single_valued (system_interfaces P)" and old_csv: "single_valued (system_clauses P)"
    using source_formed by (auto simp: schema_system_formed_def)
  have isv: "single_valued (system_interfaces ?T)"
    using old_isv no_interface by (auto simp: single_valued_def)
  have csv: "single_valued (system_clauses ?T)"
    using old_csv functional_clauses no_clause by (auto simp: single_valued_def; blast)
  have interfaces: "\<forall>e q. (e,q)\<in>system_interfaces ?T \<longrightarrow> pattern_formed q"
    using source_formed interface_formed by (auto simp: schema_system_formed_def)
  have clauses: "\<forall>e c S. ((e,c),S)\<in>system_clauses ?T \<longrightarrow>
    e\<in>system_definitions ?T \<and> schema_formed S \<and> schema_dependencies S \<subseteq> system_definitions ?T"
    using source_formed clauses_formed callees by (auto simp: schema_system_formed_def; blast)
  show ?thesis using finite isv csv interfaces clauses by (simp only: schema_system_formed_def)
qed

theorem added_definition_preserves_old:
  assumes source: "schema_system_formed P" and target: "schema_system_formed (add_view_definition P d p C)"
    and fresh: "d\<notin>system_definitions P" and member: "e\<in>system_definitions P"
  shows "schema_call_formed (add_view_definition P d p C) e t \<longleftrightarrow> schema_call_formed P e t"
    and "(e,t)\<in>positive_meaning (add_view_definition P d p C) \<longleftrightarrow> (e,t)\<in>positive_meaning P"
proof -
  have agree: "systems_agree_on P (add_view_definition P d p C) (system_definitions P)"
    using fresh by (auto simp: systems_agree_on_def)
  have closed: "system_dependency_closed P (system_definitions P)"
    using system_dependency_boundary(1)[OF source] by (auto simp: system_dependency_closed_def)
  show "schema_call_formed (add_view_definition P d p C) e t \<longleftrightarrow> schema_call_formed P e t"
    using schema_call_agreement[OF source target agree member] by blast
  show "(e,t)\<in>positive_meaning (add_view_definition P d p C) \<longleftrightarrow> (e,t)\<in>positive_meaning P"
    using positive_meaning_dependency_locality[OF source target agree closed member] by blast
qed

locale positive_view =
  fixes P :: "('a,'s,'d,'c) schema_system" and d :: 'd and p :: "'a term_pattern"
    and C :: "('c \<times> ('a,'s,'d) factor_schema) set"
  assumes source_formed: "schema_system_formed P"
    and fresh: "d \<notin> system_definitions P"
    and interface_formed: "pattern_formed p"
    and finite_clauses: "finite C" and functional_clauses: "single_valued C"
    and clauses_formed: "\<forall>c S. (c,S) \<in> C \<longrightarrow> schema_formed S"
    and callees: "\<forall>c S. (c,S) \<in> C \<longrightarrow> schema_dependencies S \<subseteq> system_definitions P"
begin

abbreviation extended where "extended \<equiv> add_view_definition P d p C"

lemma no_old_interface: "(d,q) \<notin> system_interfaces P"
  using fresh by (auto simp: system_definitions_def rel_dom_def)

lemma no_old_clause: "((d,c),S) \<notin> system_clauses P"
  using source_formed fresh by (auto simp: schema_system_formed_def)

lemma formed: "schema_system_formed extended"
  by (rule add_recursive_definition_formed[OF source_formed fresh interface_formed
    finite_clauses functional_clauses clauses_formed]) (use callees in blast)

lemma old_agreement: "systems_agree_on P extended (system_definitions P)"
  using fresh by (auto simp: systems_agree_on_def)

lemma old_closed: "system_dependency_closed P (system_definitions P)"
  using system_dependency_boundary(1)[OF source_formed] by (auto simp: system_dependency_closed_def)

theorem old_meaning:
  assumes member: "e \<in> system_definitions P"
  shows "(e,t) \<in> positive_meaning extended \<longleftrightarrow> (e,t) \<in> positive_meaning P"
  using positive_meaning_dependency_locality[OF source_formed formed old_agreement old_closed member] by blast

theorem old_calls:
  assumes member: "e \<in> system_definitions P"
  shows "schema_call_formed extended e t \<longleftrightarrow> schema_call_formed P e t"
  using schema_call_agreement[OF source_formed formed old_agreement member] by blast

lemma view_call: "schema_call_formed extended d t \<longleftrightarrow> pattern_accepts p t"
  by (simp only: schema_call_formed_def formed added_view_interfaces)
     (use no_old_interface in auto)

lemma view_clause_family: "system_clause_family extended d = C"
  by (rule set_eqI; rename_tac entry; case_tac entry; simp add: no_old_clause)

lemma view_rule:
  assumes clause: "(c,S) \<in> C"
  shows "schema_rule_instance S
      {q\<in>positive_meaning extended. schema_call_formed extended (fst q) (snd q)} t \<longleftrightarrow>
    schema_rule_instance S (positive_meaning P) t"
proof -
  have agree: "\<forall>e\<in>schema_dependencies S. \<forall>x.
    (e,x) \<in> {q\<in>positive_meaning extended. schema_call_formed extended (fst q) (snd q)}
      \<longleftrightarrow> (e,x) \<in> positive_meaning P"
  proof (intro ballI allI)
    fix e x assume dependency: "e \<in> schema_dependencies S"
    have inside: "e \<in> system_definitions P" using callees clause dependency by blast
    have meaning: "(e,x) \<in> positive_meaning extended \<longleftrightarrow> (e,x) \<in> positive_meaning P"
      by (rule old_meaning[OF inside])
    have accepts: "(e,x) \<in> positive_meaning extended \<Longrightarrow> schema_call_formed extended e x"
      by (rule positive_meaning_formed)
    show "(e,x) \<in> {q\<in>positive_meaning extended. schema_call_formed extended (fst q) (snd q)}
      \<longleftrightarrow> (e,x) \<in> positive_meaning P"
      using meaning accepts by auto
  qed
  show ?thesis by (rule schema_rule_support_agreement[OF agree])
qed

theorem view_meaning:
  "(d,t) \<in> positive_meaning extended \<longleftrightarrow>
    pattern_accepts p t \<and> (\<exists>c S. (c,S) \<in> C \<and> schema_rule_instance S (positive_meaning P) t)"
  by (subst positive_meaning_unfold)
     (simp only: schema_consequence_rule view_call view_clause_family; use view_rule in blast)

theorem native_total:
  "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E u Q.
    inj_on g (insert d (system_definitions P)) \<and> closed_native_package_at E u [] Q \<and>
    native_package_environment E u [] = E \<and>
    system_alpha_variant (rename_system g extended) Q \<and>
    positive_meaning Q = map_prod g id ` positive_meaning extended"
  using program_compilation_total[OF formed] by (simp only: added_view_definitions)

end

theorem positive_view_exists:
  fixes P :: "('a,'s,nat,'c) schema_system"
  assumes pf: "schema_system_formed P" and iface: "pattern_formed p"
    and finite: "finite C" and functional: "single_valued C"
    and schemas: "\<forall>c S. (c,S) \<in> C \<longrightarrow> schema_formed S"
    and dependencies: "\<forall>c S. (c,S) \<in> C \<longrightarrow> schema_dependencies S \<subseteq> system_definitions P"
  shows "\<exists>d. positive_view P d p C"
proof -
  have bound: "finite (system_definitions P)" by (rule system_definitions_finite[OF pf])
  have room: "\<exists>d. d \<notin> system_definitions P"
  proof (rule ccontr)
    assume "\<not> (\<exists>d. d \<notin> system_definitions P)"
    then have "system_definitions P = UNIV" by auto
    with bound show False by simp
  qed
  obtain d where fresh: "d \<notin> system_definitions P" using room by blast
  have "positive_view P d p C"
    by (rule positive_view.intro[OF pf fresh iface finite functional schemas dependencies])
  then show ?thesis by blast
qed

text \<open>
  A fresh view uses the existing interface and complete clause-family grammar.
  Its clauses may share bound variables across their identified premises and
  may contain complete material equations. Every callee is already present in
  the source system. The old calls and old meaning are unchanged.

  The new meaning is exactly interface acceptance and one applicable clause
  whose whole premise family holds in the old meaning. Singleton premise
  families give fixed projections; larger families give conjunctions. No
  view-specific truth dispatcher, wrapper code, or dependency registry is added.
  The extension exists on an unbounded coordinate carrier and has native
  compilation through the general theorem.
\<close>

end
