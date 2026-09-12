theory Factor_Positioned_Instances
  imports Factor_Program_Positions
begin

section \<open>Complete instances retain the owning use of every private coordinate\<close>

lemma positioned_admitted_instanceI:
  assumes formed: "schema_system_formed P" and admitted: "admitted_schema_instance P d c V t Q"
  shows "admitted_schema_instance (positioned_program P) d (fst d,c)
    (rename_term_bindings (Pair (fst d)) V) t (map_socket_graph (Pair (fst d)) id id Q)"
proof -
  obtain S where source: "((d,c),S)\<in>system_clauses P" and inst: "schema_instance S V t Q"
    and material: "schema_material_satisfied S V"
    using admitted by (auto simp: admitted_schema_instance_def)
  have binders: "inj_on (Pair (fst d)) (schema_variables S)"
    and sockets: "inj_on (Pair (fst d)) (schema_sockets S)"
    by (auto simp: inj_on_def)
  have clause: "((d,(fst d,c)),rename_schema (Pair (fst d)) (Pair (fst d)) id S)
      \<in>system_clauses (positioned_program P)"
    using source by (auto simp: positioned_clause_entry)
  have copied: "schema_instance (rename_schema (Pair (fst d)) (Pair (fst d)) id S)
      (rename_term_bindings (Pair (fst d)) V) t (map_socket_graph (Pair (fst d)) id id Q)"
    by (rule schema_instance_renaming[OF inst binders sockets])
  have bindings: "term_bindings_formed (schema_variables S) V"
    using inst by (simp add: schema_instance_def)
  have checked: "schema_material_satisfied (rename_schema (Pair (fst d)) (Pair (fst d)) id S)
      (rename_term_bindings (Pair (fst d)) V)"
    using material by (simp only: schema_material_satisfied_renaming[OF bindings binders])
  have head: "schema_call_formed (positioned_program P) d t"
    using admitted by (simp only: positioned_program_calls[OF formed]) (simp add: admitted_schema_instance_def)
  have calls: "\<forall>s e x. (s,e,x)\<in>map_socket_graph (Pair (fst d)) id id Q \<longrightarrow>
      schema_call_formed (positioned_program P) e x"
    using admitted by (auto simp: map_socket_graph_member positioned_program_calls[OF formed] admitted_schema_instance_def)
  show ?thesis using head clause copied checked calls unfolding admitted_schema_instance_def by blast
qed

lemma positioned_admitted_instanceE:
  assumes formed: "schema_system_formed P"
    and admitted: "admitted_schema_instance (positioned_program P) d k W t R"
  obtains c V Q where "k=(fst d,c)" "W=rename_term_bindings (Pair (fst d)) V"
    "R=map_socket_graph (Pair (fst d)) id id Q" "admitted_schema_instance P d c V t Q"
proof -
  obtain T where clause: "((d,k),T)\<in>system_clauses (positioned_program P)"
    and inst: "schema_instance T W t R" and material: "schema_material_satisfied T W"
    using admitted by (auto simp: admitted_schema_instance_def)
  obtain c S where source: "((d,c),S)\<in>system_clauses P" and site: "k=(fst d,c)"
    and renamed: "T=rename_schema (Pair (fst d)) (Pair (fst d)) id S"
    using clause by (auto simp: positioned_clause_entry)
  have binders: "inj_on snd (schema_variables T)" and sockets: "inj_on snd (schema_sockets T)"
    by (auto simp: renamed renamed_schema_variables renamed_schema_sockets inj_on_def)
  have cancellation: "rename_schema snd snd id T=S"
    unfolding renamed by (rule rename_schema_cancels) simp_all
  let ?V="rename_term_bindings snd W"
  let ?Q="map_socket_graph snd id id R"
  have recovered: "schema_instance S ?V t ?Q"
    using schema_instance_renaming[OF inst binders sockets, where g=id] by (simp only: cancellation)
  have bindings: "term_bindings_formed (schema_variables T) W"
    using inst by (simp add: schema_instance_def)
  have checked: "schema_material_satisfied S ?V"
    using schema_material_satisfied_renaming[OF bindings binders, where h=snd and g=id] material
    by (simp only: cancellation)
  have wdomain: "rel_dom W=Pair (fst d) ` schema_variables S"
    using bindings by (simp add: term_bindings_formed_def renamed renamed_schema_variables)
  have rdomain: "rel_dom R=Pair (fst d) ` rel_dom (schema_premises S)"
    using schema_instance_socket_boundary[OF inst]
    by (simp add: renamed rename_schema_def map_socket_graph_domain)
  have wowner: "fst a=fst d" if member: "(a,x)\<in>W" for a x
  proof -
    have key: "a\<in>rel_dom W" by (rule rel_domI[OF member])
    have owned_scope: "a\<in>Pair (fst d) ` schema_variables S" using key by (simp only: wdomain)
    show ?thesis using owned_scope by auto
  qed
  have rowner: "fst s=fst d" if member: "(s,q)\<in>R" for s q
  proof -
    have key: "s\<in>rel_dom R" by (rule rel_domI[OF member])
    have owned_scope: "s\<in>Pair (fst d) ` rel_dom (schema_premises S)" using key by (simp only: rdomain)
    show ?thesis using owned_scope by auto
  qed
  have restore_bindings: "rename_term_bindings (Pair (fst d)) ?V=W"
    using wowner by (auto simp: rename_term_bindings_def image_iff; force)
  have restore_premises: "map_socket_graph (Pair (fst d)) id id ?Q=R"
    using rowner by (auto simp: map_socket_graph_def map_prod_def image_iff; force)
  have head: "schema_call_formed P d t"
    using admitted by (simp add: admitted_schema_instance_def positioned_program_calls[OF formed])
  have calls: "\<forall>s e x. (s,e,x)\<in>?Q \<longrightarrow> schema_call_formed P e x"
    using admitted by (auto simp: admitted_schema_instance_def map_socket_graph_member positioned_program_calls[OF formed])
  have original: "admitted_schema_instance P d c ?V t ?Q"
    using head source recovered checked calls unfolding admitted_schema_instance_def by blast
  show thesis by (rule that[OF site restore_bindings[symmetric] restore_premises[symmetric] original])
qed

theorem positioned_admitted_instance_exact:
  assumes formed: "schema_system_formed P"
  shows "admitted_schema_instance (positioned_program P) d k W t R \<longleftrightarrow>
    (\<exists>c V Q. k=(fst d,c) \<and> W=rename_term_bindings (Pair (fst d)) V \<and>
      R=map_socket_graph (Pair (fst d)) id id Q \<and> admitted_schema_instance P d c V t Q)"
  using positioned_admitted_instanceE[OF formed] positioned_admitted_instanceI[OF formed] by blast

text \<open>
  Positioning is exact for the supplied bindings and complete premise relation.
  The inverse follows from their actual domains, so a binding or socket owned
  by another use cannot be substituted. Clause ownership uses the definition's
  semantic use; its local definition address is not part of a binder or socket
  site. Callee sites, all argument terms, and material satisfaction are retained.
\<close>

end
