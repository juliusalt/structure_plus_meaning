theory Factor_Component_Agreement
  imports Factor_Recursive_Groups
begin

section \<open>Whole component agreements compose through their own boundaries\<close>

lemma whole_agreement_definitions:
  assumes "systems_agree_on P Q (system_definitions P)"
  shows "system_definitions P\<subseteq>system_definitions Q"
  using assms by (auto simp: systems_agree_on_def system_definitions_def rel_dom_def; blast)

lemma whole_agreement_clause_interface:
  assumes agreement: "systems_agree_on P Q (system_definitions P)"
    and clause: "((d,c),S)\<in>system_clauses P"
    and interface: "(d,p)\<in>system_interfaces P"
  shows "((d,c),S)\<in>system_clauses Q \<and> (d,p)\<in>system_interfaces Q"
  using assms by (auto simp: systems_agree_on_def system_definitions_def rel_dom_def; blast)

theorem whole_agreement_positive_subset:
  assumes source: "schema_system_formed P" and target: "schema_system_formed Q"
    and agreement: "systems_agree_on P Q (system_definitions P)"
  shows "positive_meaning P\<subseteq>positive_meaning Q"
proof
  fix q assume known: "q\<in>positive_meaning P"
  obtain d t where shape: "q=(d,t)" by (cases q)
  have inside: "d\<in>system_definitions P"
    using positive_meaning_formed[OF known[unfolded shape]]
    by (auto simp: schema_call_formed_def system_definitions_def rel_dom_def)
  show "q\<in>positive_meaning Q"
    using known whole_system_agreement_meaning[OF source target agreement inside, of t]
    by (simp only: shape)
qed

theorem whole_agreement_transitive:
  assumes "systems_agree_on P Q (system_definitions P)"
    "systems_agree_on Q T (system_definitions Q)"
  shows "systems_agree_on P T (system_definitions P)"
  by (rule systems_agree_on_transitive[OF assms(1)],
      rule systems_agree_on_subdomain[OF assms(2) whole_agreement_definitions[OF assms(1)]])

theorem whole_agreement_union:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and first: "systems_agree_on P T (system_definitions P)"
    and second: "systems_agree_on Q T (system_definitions Q)"
  shows "systems_agree_on (system_union P Q) T (system_definitions (system_union P Q))"
proof (rule systems_agree_on_sym)
  show "systems_agree_on T (system_union P Q) (system_definitions (system_union P Q))"
    by (rule systems_agree_on_union_domain[OF left right])
      (use systems_agree_on_sym[OF first] systems_agree_on_sym[OF second] in auto)
qed

theorem common_component_overlap_agreement:
  assumes first: "systems_agree_on B P (system_definitions B\<inter>system_definitions P)"
    and second: "systems_agree_on B Q (system_definitions B\<inter>system_definitions Q)"
    and covered: "system_definitions P\<inter>system_definitions Q\<subseteq>system_definitions B"
  shows "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
proof -
  let ?U="system_definitions P\<inter>system_definitions Q"
  have left: "?U\<subseteq>system_definitions B\<inter>system_definitions P"
    and right: "?U\<subseteq>system_definitions B\<inter>system_definitions Q"
    using covered by blast+
  show ?thesis by (rule systems_agree_on_transitive[
    OF systems_agree_on_sym[OF systems_agree_on_subdomain[OF first left]]
      systems_agree_on_subdomain[OF second right]])
qed

theorem overlap_agreement_union:
  assumes left: "schema_system_formed P" and right: "schema_system_formed Q"
    and first: "systems_agree_on P T (system_definitions P\<inter>system_definitions T)"
    and second: "systems_agree_on Q T (system_definitions Q\<inter>system_definitions T)"
  shows "systems_agree_on (system_union P Q) T
    (system_definitions (system_union P Q)\<inter>system_definitions T)"
proof -
  let ?U="system_definitions (system_union P Q)\<inter>system_definitions T"
  have one: "systems_agree_on T P (?U\<inter>system_definitions P)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF first]]) auto
  have two: "systems_agree_on T Q (?U\<inter>system_definitions Q)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF second]]) auto
  have covered: "?U\<subseteq>system_definitions P\<union>system_definitions Q" by auto
  show ?thesis by (rule systems_agree_on_sym[OF systems_agree_on_union_domain[
    OF left right one two covered]])
qed

theorem rooted_agreement_transfer:
  assumes "systems_agree_on P Q (system_definitions P)"
  shows "systems_agree_on (rooted_system P roots) Q (system_definitions (rooted_system P roots))"
  by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF rooted_system_agreement]],
      rule systems_agree_on_subdomain[OF assms rooted_system_subdomain])

theorem rooted_overlap_agreement:
  assumes agreement: "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
  shows "systems_agree_on (rooted_system P roots) Q
    (system_definitions (rooted_system P roots)\<inter>system_definitions Q)"
proof -
  let ?U="system_definitions (rooted_system P roots)\<inter>system_definitions Q"
  have first: "systems_agree_on (rooted_system P roots) P ?U"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF rooted_system_agreement]]) blast
  have boundary: "?U\<subseteq>system_definitions P\<inter>system_definitions Q"
    using rooted_system_subdomain[of P roots] by blast
  show ?thesis by (rule systems_agree_on_transitive[OF first
    systems_agree_on_subdomain[OF agreement boundary]])
qed

context positive_definition_group
begin

theorem rebased_group:
  assumes target: "schema_system_formed R"
    and agreement: "systems_agree_on P R (system_definitions P)"
    and fresh: "system_definitions R\<inter>system_definitions Q={}"
  shows "positive_definition_group R Q"
  by (rule positive_definition_group.intro[OF target _ fresh],
      rule schema_system_formed_over_mono[OF group_formed whole_agreement_definitions[OF agreement]])

theorem extended_overlap_agreement:
  assumes agreement: "systems_agree_on P R (system_definitions P\<inter>system_definitions R)"
    and fresh: "system_definitions Q\<inter>system_definitions R={}"
  shows "systems_agree_on extended R (system_definitions extended\<inter>system_definitions R)"
proof -
  have domain: "system_definitions extended\<inter>system_definitions R=
      system_definitions P\<inter>system_definitions R"
    using fresh by (auto simp: system_union_definitions)
  have first: "systems_agree_on extended P (system_definitions P\<inter>system_definitions R)"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF old_agreement]]) blast
  show ?thesis unfolding domain by (rule systems_agree_on_transitive[OF first agreement])
qed

end

text \<open>
  Whole agreement already includes every source interface, so it supplies the
  required domain inclusion. Transitivity and union can therefore consume
  whole component contracts directly. Rooted restriction retains the same
  agreement on its least dependency boundary. A recursive group can be
  rebased using that contract and freshness; its earlier rebasing theorem
  then preserves the complete original program. These rules do not identify
  different implementations merely because their meanings happen to agree.

  A common component transfers agreement only when its actual definition
  boundary covers every overlap of the two targets. It need not be retained
  in its entirety by either target. Agreement with a union follows from
  agreement with each formed component on its own overlap; formation of
  the union itself remains a separate condition. Pairwise compatibility
  cannot silently supply a common boundary or transitivity.
\<close>

end
