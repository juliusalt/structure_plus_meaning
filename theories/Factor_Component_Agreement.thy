theory Factor_Component_Agreement
  imports Factor_Recursive_Groups
begin

section \<open>Whole component agreements compose through their own boundaries\<close>

lemma whole_agreement_definitions:
  assumes "systems_agree_on P Q (system_definitions P)"
  shows "system_definitions P\<subseteq>system_definitions Q"
  using assms by (auto simp: systems_agree_on_def system_definitions_def rel_dom_def; blast)

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

theorem rooted_agreement_transfer:
  assumes "systems_agree_on P Q (system_definitions P)"
  shows "systems_agree_on (rooted_system P roots) Q (system_definitions (rooted_system P roots))"
  by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF rooted_system_agreement]],
      rule systems_agree_on_subdomain[OF assms rooted_system_subdomain])

context positive_definition_group
begin

theorem rebased_group:
  assumes target: "schema_system_formed R"
    and agreement: "systems_agree_on P R (system_definitions P)"
    and fresh: "system_definitions R\<inter>system_definitions Q={}"
  shows "positive_definition_group R Q"
  by (rule positive_definition_group.intro[OF target _ fresh],
      rule schema_system_formed_over_mono[OF group_formed whole_agreement_definitions[OF agreement]])

end

text \<open>
  Whole agreement already includes every source interface, so it supplies the
  required domain inclusion. Transitivity and union can therefore consume
  whole component contracts directly. Rooted restriction retains the same
  agreement on its least dependency boundary. A recursive group can be
  rebased using that contract and freshness; its earlier rebasing theorem
  then preserves the complete original program. These rules do not identify
  different implementations merely because their meanings happen to agree.
\<close>

end
