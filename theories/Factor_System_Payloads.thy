theory Factor_System_Payloads
  imports Factor_Positive_Parametricity Factor_System_Composition Factor_System_Restriction
begin

section \<open>The payloads of composed programs\<close>

text \<open>
  The payloads a program states (@{const system_payloads}) through the three ways programs are composed:
  a fresh view states its predecessor's payloads with those of its interface and its clauses, a union what its
  two parts state, and a rooted restriction no more than its source. A program built by these steps has its
  payloads composed down its lineage, each step computed on its own patterns alone.
\<close>

lemma add_view_definition_payloads:
  "system_payloads (add_view_definition P d p C)=system_payloads P\<union>{v. Payload_Term v\<in>pattern_leaves p}\<union>
    (\<Union>(c,S)\<in>C. {v. Payload_Term v\<in>schema_leaves S})"
  by (auto simp: system_payloads_def system_leaves_def add_view_definition_def)

lemma system_union_payloads: "system_payloads (system_union P Q)=system_payloads P\<union>system_payloads Q"
  by (auto simp: system_payloads_def system_leaves_def system_union_def)

lemma rooted_system_payloads: "system_payloads (rooted_system P R)\<subseteq>system_payloads P"
  by (auto simp: system_payloads_def system_leaves_def rooted_system_def system_restriction_def)

end
