theory Factor_Scheme_Claim_Joins
  imports Factor_Scheme_Observations Functional_Relation_Joins Factor_Clause_Specialization_Graphs
begin

section \<open>The complete symbolic premise relation is the actual child-claim join\<close>

theorem schema_scheme_local_reading_join:
  assumes graph: "schema_graph_formed G root" and claims: "single_valued J"
    and domain: "rel_dom J=schema_graph_nodes G"
  shows "schema_scheme_local_reading P G J n (Schema_Inference c V) \<longleftrightarrow>
    (\<exists>T. schema_clause_specialization P (fst (rel_value J n)) c (fset V) T \<and>
      schema_conclusion T=snd (rel_value J n) \<and>
      schema_premises T=schema_graph_premises G n O J)"
proof -
  have covered: "rel_ran (schema_graph_premises G n)\<subseteq>rel_dom J"
    using schema_graph_premises_targets[OF graph, of n] domain by simp
  have join: "(rel_dom (schema_graph_premises G n)=rel_dom (schema_premises T) \<and>
      (\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow> (s,rel_value J m)\<in>schema_premises T))
      \<longleftrightarrow> schema_premises T=schema_graph_premises G n O J"
    if specialized: "schema_clause_specialization P (fst (rel_value J n)) c (fset V) T" for T
  proof -
    have functional: "single_valued (schema_premises T)"
      using specialized by (auto simp: schema_clause_specialization_def schema_pattern_boundary_def schema_formed_def)
    show ?thesis using functional_relation_join_characterization[OF claims functional covered]
      by (simp only: eq_commute)
  qed
  show ?thesis by (simp only: schema_scheme_local_reading.simps) (use join in blast)
qed


lemma schema_scheme_local_reading_fixed_target:
  assumes graph: "schema_graph_formed G root" and claims: "single_valued J"
    and domain: "rel_dom J=schema_graph_nodes G" and claim: "(n,d,p)\<in>J"
    and target: "schema_clause_specialization P d c (fset V) T"
  shows "schema_scheme_local_reading P G J n (Schema_Inference c V) \<longleftrightarrow>
    schema_conclusion T=p \<and> schema_premises T=schema_graph_premises G n O J"
proof -
  have selected_value: "rel_value J n=(d,p)" by (rule rel_value_eq[OF claims claim])
  have unique: "S=T" if "schema_clause_specialization P d c (fset V) S" for S
    by (rule schema_clause_specialization_unique[OF that target])
  show ?thesis by (simp only: schema_scheme_local_reading_join[OF graph claims domain] selected_value fst_conv snd_conv)
    (use target unique in blast)
qed

lemma observed_schema_premises_values:
  "observed_schema_premises T=map_relation_values (map_prod id pattern_claim_observation) (schema_premises T)"
  by (auto simp: observed_schema_premises_def map_socket_graph_def map_relation_values_def map_prod_def)

lemma observed_schema_premises_join:
  "observed_schema_premises T=R O map_relation_values (map_prod id pattern_claim_observation) J
    \<longleftrightarrow> schema_premises T=R O J"
proof -
  have injective: "inj (map_prod id pattern_claim_observation)"
    by (auto simp: inj_def map_prod_def)
  show ?thesis by (simp only: observed_schema_premises_values map_relation_values_join[symmetric]
    map_relation_values_injective[OF injective])
qed

theorem schema_scheme_local_reading_observed_join:
  assumes "schema_graph_formed G root" "single_valued J" "rel_dom J=schema_graph_nodes G"
  shows "schema_scheme_local_reading P G J n (Schema_Inference c V) \<longleftrightarrow>
    (\<exists>T. schema_clause_specialization P (fst (rel_value J n)) c (fset V) T \<and>
      pattern_claim_observation (schema_conclusion T)=pattern_claim_observation (snd (rel_value J n)) \<and>
      observed_schema_premises T=schema_graph_premises G n O
        map_relation_values (map_prod id pattern_claim_observation) J)"
  by (simp only: schema_scheme_local_reading_join[OF assms] pattern_claim_observation_injective
    observed_schema_premises_join)

text \<open>
  This uses the independently defined symbolic local judgment. The complete
  graph and claim domains supply coverage of every actual discharge target.
  Injective paired observations preserve each full claim, including its
  callee, and commute with the existing relation join. The resulting equality
  retains all premise sockets; it is not a one-sided check of selected rows.

  These are mathematical contracts for the native child reader. They do not
  admit arbitrary pairs as pattern observations, establish the surrounding
  whole-graph conditions, or check their own mathematical proofs natively.
\<close>

end
