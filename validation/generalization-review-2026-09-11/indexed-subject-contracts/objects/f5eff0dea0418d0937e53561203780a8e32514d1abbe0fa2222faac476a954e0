theory Factor_Program_Changes
  imports Factor_Definition_Closure
begin

section \<open>Changed definitions come from complete interface and clause rows\<close>

definition system_changed_definitions ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> 'd set" where
  "system_changed_definitions P Q =
    {d. (\<exists>p. ((d,p)\<in>system_interfaces P)\<noteq>((d,p)\<in>system_interfaces Q)) \<or>
      (\<exists>c S. (((d,c),S)\<in>system_clauses P)\<noteq>(((d,c),S)\<in>system_clauses Q))}"

lemma system_changed_definitions_sym:
  "system_changed_definitions P Q=system_changed_definitions Q P"
  by (auto simp: system_changed_definitions_def)

lemma system_changed_definitions_self [simp]: "system_changed_definitions P P={}"
  by (simp add: system_changed_definitions_def)

lemma system_changed_definitions_boundary:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
  shows "system_changed_definitions P Q\<subseteq>system_definitions P\<union>system_definitions Q"
    and "finite (system_changed_definitions P Q)"
proof -
  show inside: "system_changed_definitions P Q\<subseteq>system_definitions P\<union>system_definitions Q"
    using formed by (auto simp: system_changed_definitions_def schema_system_formed_def
      system_definitions_def rel_dom_def; blast)
  show "finite (system_changed_definitions P Q)"
    by (rule finite_subset[OF inside]) (simp add: system_definitions_finite[OF formed(1)]
      system_definitions_finite[OF formed(2)])
qed

theorem systems_agree_on_unchanged:
  "systems_agree_on P Q U\<longleftrightarrow>U\<inter>system_changed_definitions P Q={}"
  by (auto simp: systems_agree_on_def system_changed_definitions_def; blast)

section \<open>Every caller of a changed definition belongs to the affected boundary\<close>

definition system_affected_definitions :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "system_affected_definitions P U =
    {d\<in>system_definitions P. \<exists>e\<in>U. (d,e)\<in>(system_dependency_edges P)\<^sup>*}"

lemma system_affected_definitions_inside:
  "system_affected_definitions P U\<subseteq>system_definitions P"
  by (auto simp: system_affected_definitions_def)

lemma system_affected_definitions_finite:
  assumes "schema_system_formed P"
  shows "finite (system_affected_definitions P U)"
  by (rule finite_subset[OF system_affected_definitions_inside system_definitions_finite[OF assms]])

lemma system_affected_seeds:
  "U\<inter>system_definitions P\<subseteq>system_affected_definitions P U"
  by (auto simp: system_affected_definitions_def)

lemma system_affected_closure:
  "d\<in>system_affected_definitions P U\<longleftrightarrow>
    d\<in>system_definitions P \<and> system_definition_closure P {d}\<inter>U\<noteq>{}"
  by (auto simp: system_affected_definitions_def system_definition_closure_def)

lemma system_affected_step:
  assumes formed: "schema_system_formed P" and edge: "(d,e)\<in>system_dependency_edges P"
    and affected: "e\<in>system_affected_definitions P U"
  shows "d\<in>system_affected_definitions P U"
proof -
  obtain x where last: "x\<in>U" and path: "(e,x)\<in>(system_dependency_edges P)\<^sup>*"
    using affected unfolding system_affected_definitions_def by blast
  have inside: "d\<in>system_definitions P" using system_dependency_boundary(1)[OF formed] edge by blast
  have first: "(d,e)\<in>(system_dependency_edges P)\<^sup>*" using edge by auto
  have full: "(d,x)\<in>(system_dependency_edges P)\<^sup>*" by (rule rtrancl_trans[OF first path])
  show ?thesis using inside last full unfolding system_affected_definitions_def by blast
qed

theorem system_affected_least:
  assumes formed: "schema_system_formed P" and seeds: "U\<inter>system_definitions P\<subseteq>B"
    and backward: "\<And>d e. (d,e)\<in>system_dependency_edges P \<Longrightarrow> e\<in>B \<Longrightarrow> d\<in>B"
  shows "system_affected_definitions P U\<subseteq>B"
proof
  fix d assume member: "d\<in>system_affected_definitions P U"
  obtain e where inside: "d\<in>system_definitions P" and last: "e\<in>U"
    and path: "(d,e)\<in>(system_dependency_edges P)\<^sup>*"
    using member unfolding system_affected_definitions_def by blast
  have roots: "{d}\<subseteq>system_definitions P" using inside by simp
  have closure: "system_definition_closure P {d}\<subseteq>system_definitions P"
    by (rule system_definition_closure_boundary(1)[OF formed roots])
  have reached: "e\<in>system_definition_closure P {d}" using path
    by (auto simp: system_definition_closure_def)
  have terminal: "e\<in>B" using seeds last closure reached by blast
  have reverse: "e\<in>B \<longrightarrow> d\<in>B" using path
  proof (induction rule: rtrancl_induct)
    case base then show ?case by simp
  next
    case (step x y)
    show ?case
    proof
      assume member: "y\<in>B"
      have previous: "x\<in>B" by (rule backward[OF step.hyps(2) member])
      show "d\<in>B" using step.IH previous by blast
    qed
  qed
  show "d\<in>B" using terminal reverse by blast
qed

theorem system_affected_empty:
  assumes formed: "schema_system_formed P"
  shows "system_affected_definitions P U={}\<longleftrightarrow>U\<inter>system_definitions P={}"
proof
  assume empty: "system_affected_definitions P U={}"
  show "U\<inter>system_definitions P={}" using system_affected_seeds[where P=P and U=U] empty by blast
next
  assume empty: "U\<inter>system_definitions P={}"
  have included: "system_affected_definitions P U\<subseteq>{}"
    by (rule system_affected_least[OF formed]) (use empty in auto)
  show "system_affected_definitions P U={}" using included by blast
qed

lemma system_unaffected_closed:
  assumes formed: "schema_system_formed P"
  shows "system_dependency_closed P (system_definitions P-system_affected_definitions P U)"
proof (unfold system_dependency_closed_def, intro ballI allI impI)
  fix d e assume member: "d\<in>system_definitions P-system_affected_definitions P U"
    and edge: "(d,e)\<in>system_dependency_edges P"
  have inside: "e\<in>system_definitions P" using system_dependency_boundary(1)[OF formed] edge by blast
  have outside: "e\<notin>system_affected_definitions P U"
    using system_affected_step[OF formed edge] member by blast
  show "e\<in>system_definitions P-system_affected_definitions P U" using inside outside by blast
qed

theorem system_unaffected_meaning:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
    and member: "d\<in>system_definitions P"
    and unaffected: "d\<notin>system_affected_definitions P (system_changed_definitions P Q)"
  shows "schema_call_formed P d t\<longleftrightarrow>schema_call_formed Q d t"
    and "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,t)\<in>positive_meaning Q"
proof -
  let ?D="system_changed_definitions P Q"
  let ?U="system_definitions P-system_affected_definitions P ?D"
  have empty: "?U\<inter>?D={}" using system_affected_seeds[where P=P and U="?D"] by blast
  have agree: "systems_agree_on P Q ?U" using empty by (simp add: systems_agree_on_unchanged)
  have closed: "system_dependency_closed P ?U" by (rule system_unaffected_closed[OF formed(1)])
  have inside: "d\<in>?U" using member unaffected by blast
  show "schema_call_formed P d t\<longleftrightarrow>schema_call_formed Q d t"
    by (rule schema_call_agreement[OF formed agree inside])
  show "(d,t)\<in>positive_meaning P\<longleftrightarrow>(d,t)\<in>positive_meaning Q"
    by (rule positive_meaning_dependency_locality[OF formed agree closed inside])
qed

section \<open>The public interfaces and affected definitions fix the comparison domain\<close>

definition system_comparison_definitions ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow> 'd set" where
  "system_comparison_definitions P Q roots =
    roots\<union>system_affected_definitions P (system_changed_definitions P Q)"

definition system_comparison_calls ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow> 'd set \<Rightarrow>
    ('d\<times>factor_term) set" where
  "system_comparison_calls P Q roots =
    {(d,t). d\<in>system_comparison_definitions P Q roots \<and> schema_call_formed P d t}"

lemma system_comparison_definitions_boundary:
  assumes formed: "schema_system_formed P" and roots: "roots\<subseteq>system_definitions P"
  shows "system_comparison_definitions P Q roots\<subseteq>system_definitions P"
    and "finite (system_comparison_definitions P Q roots)"
proof -
  show inside: "system_comparison_definitions P Q roots\<subseteq>system_definitions P"
    using roots system_affected_definitions_inside[where P=P and U="system_changed_definitions P Q"]
    by (auto simp: system_comparison_definitions_def)
  show "finite (system_comparison_definitions P Q roots)"
    by (rule finite_subset[OF inside system_definitions_finite[OF formed]])
qed

theorem system_comparison_calls_projection:
  assumes formed: "schema_system_formed P" and roots: "roots\<subseteq>system_definitions P"
  shows "rel_dom (system_comparison_calls P Q roots)=system_comparison_definitions P Q roots"
proof (rule set_eqI)
  fix d show "d\<in>rel_dom (system_comparison_calls P Q roots)\<longleftrightarrow>
      d\<in>system_comparison_definitions P Q roots"
  proof
    assume "d\<in>rel_dom (system_comparison_calls P Q roots)"
    then show "d\<in>system_comparison_definitions P Q roots"
      by (auto simp: system_comparison_calls_def rel_dom_def)
  next
    assume member: "d\<in>system_comparison_definitions P Q roots"
    have inside: "d\<in>system_definitions P"
      using system_comparison_definitions_boundary(1)[OF formed roots] member by blast
    obtain t where call: "schema_call_formed P d t" using schema_call_inhabited[OF formed inside] by blast
    show "d\<in>rel_dom (system_comparison_calls P Q roots)"
      using member call by (auto simp: system_comparison_calls_def rel_dom_def)
  qed
qed

theorem system_comparison_domains_empty:
  assumes formed: "schema_system_formed P" "schema_system_formed Q"
  shows "system_comparison_definitions P Q R={} \<and> system_comparison_definitions Q P S={}
    \<longleftrightarrow> R={} \<and> S={} \<and> system_changed_definitions P Q={}"
proof -
  have same: "system_changed_definitions Q P=system_changed_definitions P Q"
    by (rule system_changed_definitions_sym)
  show ?thesis using system_changed_definitions_boundary(1)[OF formed]
    by (auto simp: system_comparison_definitions_def system_affected_empty[OF formed(1)]
      system_affected_empty[OF formed(2)] same)
qed

text \<open>
  The changed boundary compares the complete recovered interface and clause
  rows at fixed definition coordinates. Introduction, removal, and alteration
  are all included. This is a structural comparison of those projections,
  not a test for semantic inequivalence or a quotient by private renaming.

  Affected definitions are exactly the backward closure of that boundary in
  each program's prospective-callee graph. The leastness theorem accounts for
  every such caller, including recursive cycles. Definitions outside it keep
  their formation and positive meaning for every future argument.

  The comparison domain includes every supplied public root and every affected
  definition. Its call domain includes every argument admitted by those actual
  interfaces; it is not restricted to a finite sample of calls. Every formed
  interface has an argument, so no required definition disappears through an
  empty call domain. Native use must recover the roots from the actual package.
  The domain does not itself assert migration, interpretation, preservation,
  incompatibility, authority, or successor legitimacy.
\<close>

end
