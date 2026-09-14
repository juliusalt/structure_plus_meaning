theory RRA_External_Occurrence_Syntax
  imports RRA_Bound_Syntax_Construction
begin

section \<open>A callee address is data; its artifact comes from the environment\<close>

definition external_occurrence_syntax :: "local_address \<Rightarrow> exact_artifact" where
  "external_occurrence_syntax a =
    \<lparr>object_structure = \<lparr>rra_carrier = {[],[4],[5]}, rra_incidence = {([],[],[4]),([],[4],[5])}\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {([5],a)}\<rparr>\<rparr>"

lemma external_occurrence_syntax_literal:
  "external_occurrence_syntax a = literal_syntax (Occurrence_Anchor (R,a))"
  by (simp add: external_occurrence_syntax_def)

lemma external_occurrence_syntax_formed:
  assumes "octets_formed a"
  shows "exact_formed (external_occurrence_syntax a)"
  using assms by (auto simp: external_occurrence_syntax_def exact_formed_def object_formed_def
      rra_formed_def basis_formed_def basis_values_def bag_support_def single_valued_def octets_formed_def)

lemma external_occurrence_syntax_properties:
  "[] \<in> rra_carrier (object_structure (external_occurrence_syntax a))"
  "bag_count (object_data (external_occurrence_syntax a)) = (\<lambda>_. 0)"
  "binder_silent (external_occurrence_syntax a)"
  by (auto simp: external_occurrence_syntax_def binder_silent_def headed_incidence_def
      restrict_basis_def empty_basis_def basis_identity fun_eq_iff)

lemma external_occurrence_syntax_recovers:
  assumes formed: "octets_formed a"
  shows "citation_at (external_occurrence_syntax a) [] (External [4] a) {[],[5]}"
proof -
  have payload: "payload_at (external_occurrence_syntax a) [5] a"
    by (auto simp: external_occurrence_syntax_def payload_at_def restrict_basis_def basis_identity fun_eq_iff)
  have raw: "raw_citation_at (external_occurrence_syntax a) [] (External [4] a) {[],[5]}"
    by (rule raw_citation_at.external[OF _ _ _ payload])
       (auto simp: external_occurrence_syntax_def headed_incidence_def)
  show ?thesis using raw external_occurrence_syntax_formed[OF formed]
    by (auto simp: citation_at_def external_occurrence_syntax_def restrict_basis_def empty_basis_def basis_identity fun_eq_iff)
qed

end
