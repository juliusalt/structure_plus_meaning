theory Factor_Scheme_Local_Readings
  imports Factor_Clause_Specialization_Instances Factor_Learned_Schemas
begin

section \<open>A complete local specialization determines each symbolic inference\<close>

fun schema_scheme_local_reading ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow> 'n \<Rightarrow>
    ('a,'c,'b term_pattern) inference_node \<Rightarrow> bool" where
  "schema_scheme_local_reading P G J n Schema_Assertion \<longleftrightarrow>
    schema_graph_premises G n={}"
| "schema_scheme_local_reading P G J n (Schema_Inference c V) \<longleftrightarrow>
    (\<exists>T. schema_clause_specialization P (fst (rel_value J n)) c (fset V) T \<and>
      schema_conclusion T=snd (rel_value J n) \<and>
      rel_dom (schema_graph_premises G n)=rel_dom (schema_premises T) \<and>
      (\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
        (s,rel_value J m)\<in>schema_premises T))"

lemma schema_scheme_local_reading_checks:
  assumes system: "schema_system_formed P"
    and claims: "single_valued J"
    and complete: "rel_dom J=schema_graph_nodes G"
    and graph: "schema_graph_formed G root"
    and local: "schema_scheme_local_reading P G J n A"
  shows "checks_schema_scheme_node P G J n A"
proof (cases A)
  case Schema_Assertion
  then show ?thesis using local by simp
next
  case (Schema_Inference c V)
  obtain T where specialized: "schema_clause_specialization P (fst (rel_value J n)) c (fset V) T"
    and head: "schema_conclusion T=snd (rel_value J n)"
    and domain: "rel_dom (schema_graph_premises G n)=rel_dom (schema_premises T)"
    and children: "\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
      (s,rel_value J m)\<in>schema_premises T"
    using local by (simp only: Schema_Inference schema_scheme_local_reading.simps) blast
  obtain S where clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
    and bindings: "pattern_bindings_formed (schema_variables S) (fset V)"
    and target: "T=schema_substitute (rel_value (fset V)) S"
    using specialized by (auto simp: schema_clause_specialization_def)
  have formed: "schema_formed S" using system clause by (auto simp: schema_system_formed_def)
  have sv: "single_valued (schema_premises S)" using formed by (simp add: schema_formed_def)
  have child: "(m,fst (rel_value (schema_premises S) s),
      pattern_substitute (rel_value (fset V)) (snd (rel_value (schema_premises S) s)))\<in>J"
    if edge: "(s,m)\<in>schema_graph_premises G n" for s m
  proof -
    have row: "(s,rel_value J m)\<in>schema_premises T" using children edge by blast
    obtain e q where source: "(s,e,q)\<in>schema_premises S"
      and child_value: "rel_value J m=(e,pattern_substitute (rel_value (fset V)) q)"
      using row by (auto simp: target schema_substitute_def map_socket_graph_def map_prod_def)
    have lookup: "rel_value (schema_premises S) s=(e,q)" by (rule rel_value_eq[OF sv source])
    have member: "m\<in>schema_graph_nodes G"
      using graph edge by (auto simp: schema_graph_formed_def schema_graph_premises_def schema_graph_edges_def)
    have key: "m\<in>rel_dom J" using complete member by simp
    obtain a where claim: "(m,a)\<in>J" using key unfolding rel_dom_def by blast
    have actual: "(m,rel_value J m)\<in>J" using claim rel_value_eq[OF claims claim] by simp
    show ?thesis using actual by (simp only: lookup fst_conv snd_conv child_value)
  qed
  have source_domain: "rel_dom (schema_graph_premises G n)=rel_dom (schema_premises S)"
    using domain by (simp add: target schema_substitute_def map_socket_graph_domain)
  show ?thesis unfolding Schema_Inference checks_schema_scheme_node.simps
    by (rule exI[of _ S]) (use clause bindings head target source_domain child in auto)
qed

lemma schema_scheme_reading_local:
  assumes read: "schema_scheme_reading P G root d p J"
    and node: "(n,A)\<in>fset (graph_inferences G)"
  shows "schema_scheme_local_reading P G J n A"
proof (cases A)
  case Schema_Assertion
  have "checks_schema_scheme_node P G J n A" using read node by (simp only: schema_scheme_reading_def; blast)
  then show ?thesis by (simp add: Schema_Assertion)
next
  case (Schema_Inference c V)
  have occurrence: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)" using node by (simp add: Schema_Inference)
  obtain S where clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
    and specialization: "schema_clause_specialization P (fst (rel_value J n)) c (fset V)
      (schema_substitute (rel_value (fset V)) S)"
    and head: "schema_conclusion (schema_substitute (rel_value (fset V)) S)=snd (rel_value J n)"
    using schema_scheme_node_specialization[OF read occurrence] by blast
  let ?T="schema_substitute (rel_value (fset V)) S"
  have checked: "checks_schema_scheme_node P G J n (Schema_Inference c V)"
    using read occurrence by (simp only: schema_scheme_reading_def; blast)
  have system: "single_valued (system_clauses P)" and claims: "single_valued J"
    using read by (auto simp: schema_scheme_reading_def schema_system_formed_def)
  obtain R where other: "((fst (rel_value J n),c),R)\<in>system_clauses P"
    and domain: "rel_dom (schema_graph_premises G n)=rel_dom (schema_premises R)"
    and children: "\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
      (m,fst (rel_value (schema_premises R) s),
        pattern_substitute (rel_value (fset V)) (snd (rel_value (schema_premises R) s)))\<in>J"
    using checked by auto
  have same: "R=S" by (rule single_valued_outputs[OF system other clause])
  have formed: "schema_formed S" using read clause by (auto simp: schema_scheme_reading_def schema_system_formed_def)
  have sv: "single_valued (schema_premises S)" using formed by (simp add: schema_formed_def)
  have child: "(s,rel_value J m)\<in>schema_premises ?T"
    if edge: "(s,m)\<in>schema_graph_premises G n" for s m
  proof -
    obtain e q where source: "(s,e,q)\<in>schema_premises S"
      using edge domain same by (auto simp: rel_dom_def; blast)
    have lookup: "rel_value (schema_premises S) s=(e,q)" by (rule rel_value_eq[OF sv source])
    have actual_child: "(m,fst (rel_value (schema_premises R) s),
        pattern_substitute (rel_value (fset V)) (snd (rel_value (schema_premises R) s)))\<in>J"
      by (rule children[rule_format, OF edge])
    have claim: "(m,e,pattern_substitute (rel_value (fset V)) q)\<in>J"
      using actual_child by (simp only: same lookup fst_conv snd_conv)
    have child_value: "rel_value J m=(e,pattern_substitute (rel_value (fset V)) q)"
      by (rule rel_value_eq[OF claims claim])
    show ?thesis using source by (simp only: child_value schema_substitute_premise; blast)
  qed
  have target_domain: "rel_dom (schema_graph_premises G n)=rel_dom (schema_premises ?T)"
    using domain same by (simp add: schema_substitute_def map_socket_graph_domain)
  show ?thesis unfolding Schema_Inference schema_scheme_local_reading.simps
    by (rule exI[of _ ?T]) (use specialization head target_domain child in blast)
qed

theorem schema_scheme_reading_by_local_specializations:
  "schema_scheme_reading P G root d p J \<longleftrightarrow>
    schema_system_formed P \<and> schema_graph_formed G root \<and>
    single_valued J \<and> rel_dom J=schema_graph_nodes G \<and> (root,d,p)\<in>J \<and>
    (\<forall>n e q. (n,e,q)\<in>J \<longrightarrow> schema_pattern_call P e q) \<and>
    (\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> schema_scheme_local_reading P G J n A)"
proof
  assume read: "schema_scheme_reading P G root d p J"
  have local: "\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> schema_scheme_local_reading P G J n A"
    by (intro allI impI, rule schema_scheme_reading_local[OF read]) assumption
  show "schema_system_formed P \<and> schema_graph_formed G root \<and>
    single_valued J \<and> rel_dom J=schema_graph_nodes G \<and> (root,d,p)\<in>J \<and>
    (\<forall>n e q. (n,e,q)\<in>J \<longrightarrow> schema_pattern_call P e q) \<and>
    (\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> schema_scheme_local_reading P G J n A)"
    using read local by (simp only: schema_scheme_reading_def; blast)
next
  assume fields: "schema_system_formed P \<and> schema_graph_formed G root \<and>
    single_valued J \<and> rel_dom J=schema_graph_nodes G \<and> (root,d,p)\<in>J \<and>
    (\<forall>n e q. (n,e,q)\<in>J \<longrightarrow> schema_pattern_call P e q) \<and>
    (\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> schema_scheme_local_reading P G J n A)"
  have system: "schema_system_formed P" and graph: "schema_graph_formed G root"
    and claims: "single_valued J" and complete: "rel_dom J=schema_graph_nodes G"
    using fields by blast+
  have checked: "\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> checks_schema_scheme_node P G J n A"
  proof (intro allI impI)
    fix n A assume node: "(n,A)\<in>fset (graph_inferences G)"
    have local: "schema_scheme_local_reading P G J n A" using fields node by blast
    show "checks_schema_scheme_node P G J n A"
      by (rule schema_scheme_local_reading_checks[OF system claims complete graph local])
  qed
  show "schema_scheme_reading P G root d p J"
    using fields checked by (simp only: schema_scheme_reading_def; blast)
qed

text \<open>
  The local relation consumes an entire specialized schema. Matching only its
  head would discard premise sockets and the private variables used in material
  conditions. Complete claim and discharge domains are checked independently
  of local specialization. The specialization relation supplies every material
  operand used by the existing learned-rule extraction.

  This equivalence connects the native complete-clause reader's mathematical
  result to the symbolic proof judgment. It does not identify ground bindings
  with pattern bindings or assert that graph geometry alone checks an argument.
\<close>

end
