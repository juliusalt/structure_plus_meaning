theory Factor_System_Payloads
  imports Factor_Positive_Parametricity Factor_System_Composition Factor_System_Restriction Factor_System_Renaming
begin

section \<open>The payloads of composed programs\<close>

text \<open>
  The payloads a program states (@{const system_payloads}) through the three ways programs are composed:
  a view, fresh or not, states its predecessor's payloads with those of its interface and its clauses, a union
  what its two parts state, and a rooted restriction no more than its source. A program built by these steps has
  its payloads composed down its lineage, each step computed on its own patterns alone.
\<close>

text \<open>
  The payloads a schema states and the payloads a definition states, its interface's with its clauses';
  a formed program states exactly those of its definitions, as the payload audit reads it.
\<close>

definition schema_payloads :: "('a,'s,'d) factor_schema \<Rightarrow> octets set" where
  "schema_payloads S={v. Payload_Term v\<in>schema_leaves S}"

definition definition_payloads :: "'a term_pattern \<Rightarrow> ('c\<times>('a,'s,'d) factor_schema) set \<Rightarrow> octets set" where
  "definition_payloads p C={v. Payload_Term v\<in>pattern_leaves p} \<union> (\<Union>(c,S)\<in>C. schema_payloads S)"

theorem system_payloads_definitions:
  assumes formed: "schema_system_formed P"
  shows "system_payloads P=
    (\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
proof (rule set_eqI)
  fix v
  have owned: "\<And>d c S. ((d,c),S)\<in>system_clauses P \<Longrightarrow> d\<in>system_definitions P"
    using formed unfolding schema_system_formed_def by blast
  show "v\<in>system_payloads P \<longleftrightarrow>
    v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
  proof
    assume "v\<in>system_payloads P"
    then have "Payload_Term v\<in>system_leaves P" by (simp add: system_payloads_def)
    then consider (interface) d p where "(d,p)\<in>system_interfaces P" "Payload_Term v\<in>pattern_leaves p"
      | (clause) d c S where "((d,c),S)\<in>system_clauses P" "Payload_Term v\<in>schema_leaves S"
      by (auto simp: system_leaves_def)
    then show "v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
    proof cases
      case interface
      have "d\<in>system_definitions P" using interface(1) by (auto simp: system_definitions_def rel_dom_def)
      moreover have "system_interface P d=p" by (rule system_interface_unique[OF formed interface(1)])
      ultimately show ?thesis using interface(2) by (auto simp: definition_payloads_def)
    next
      case clause
      then show ?thesis using owned[OF clause(1)] by (fastforce simp: definition_payloads_def schema_payloads_def)
    qed
  next
    assume "v\<in>(\<Union>d\<in>system_definitions P. definition_payloads (system_interface P d) (system_clause_family P d))"
    then obtain d where d: "d\<in>system_definitions P"
      and v: "v\<in>definition_payloads (system_interface P d) (system_clause_family P d)" by blast
    have member: "(d,system_interface P d)\<in>system_interfaces P" by (rule system_interface_member[OF formed d])
    show "v\<in>system_payloads P"
      using v member by (fastforce simp: definition_payloads_def schema_payloads_def system_payloads_def system_leaves_def)
  qed
qed

lemma add_view_definition_payloads:
  "system_payloads (add_view_definition P d p C)=system_payloads P\<union>{v. Payload_Term v\<in>pattern_leaves p}\<union>
    (\<Union>(c,S)\<in>C. {v. Payload_Term v\<in>schema_leaves S})"
  by (auto simp: system_payloads_def system_leaves_def add_view_definition_def)

lemma system_union_payloads: "system_payloads (system_union P Q)=system_payloads P\<union>system_payloads Q"
  by (auto simp: system_payloads_def system_leaves_def system_union_def)

lemma rooted_system_payloads: "system_payloads (rooted_system P R)\<subseteq>system_payloads P"
  by (auto simp: system_payloads_def system_leaves_def rooted_system_def system_restriction_def)

text \<open>
  The three steps bound a lineage: a program built from programs that state the empty payload alone, by
  steps whose own patterns state none, states none either. Each program's fact is collected in
  @{text lineage_payloads}, so a step's fact is derived from its own definition by the step rules and the
  facts of the programs it is built from, whichever they are: a program inserted into a lineage needs its own
  fact and nothing of the steps above it.
\<close>

named_theorems lineage_payloads "programs that state the empty payload alone"

lemma view_payloads_bound:
  assumes "system_payloads P\<subseteq>{[]}" "{v. Payload_Term v\<in>pattern_leaves p}\<subseteq>{[]}"
    "(\<Union>(c,S)\<in>C. {v. Payload_Term v\<in>schema_leaves S})\<subseteq>{[]}"
  shows "system_payloads (add_view_definition P d p C)\<subseteq>{[]}"
  unfolding add_view_definition_payloads using assms by blast

lemma union_payloads_bound:
  "system_payloads P\<subseteq>{[]} \<Longrightarrow> system_payloads Q\<subseteq>{[]} \<Longrightarrow> system_payloads (system_union P Q)\<subseteq>{[]}"
  unfolding system_union_payloads by blast

lemma rooted_payloads_bound: "system_payloads P\<subseteq>{[]} \<Longrightarrow> system_payloads (rooted_system P R)\<subseteq>{[]}"
  using rooted_system_payloads by blast

lemmas lineage_payload_steps = view_payloads_bound union_payloads_bound rooted_payloads_bound

lemmas lineage_payload_simps = system_payloads_def system_leaves_def schema_leaves_def material_leaves_def
  material_fields_def

text \<open>
  The payloads a program states are the payload leaves of its patterns, which neither a change of its
  definition coordinates nor an alpha variant of its clauses and interfaces moves.
\<close>

lemma pattern_leaves_rename: "pattern_leaves (rename_pattern f p)=pattern_leaves p"
  by (induction p) simp_all

lemma material_leaves_rename: "material_leaves (rename_material_pattern f M)=material_leaves M"
  by (simp add: material_leaves_def material_fields_def rename_material_pattern_def pattern_leaves_rename)

lemma schema_leaves_rename: "schema_leaves (rename_schema f h g S)=schema_leaves S"
proof -
  have calls: "(\<Union>(s,d,p)\<in>map_socket_graph h g (rename_pattern f) (schema_premises S). pattern_leaves p)=
      (\<Union>(s,d,p)\<in>schema_premises S. pattern_leaves p)"
    by (simp add: map_socket_graph_def case_prod_beta pattern_leaves_rename)
  have material: "(\<Union>(s,M)\<in>(\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises S. material_leaves M)=
      (\<Union>(s,M)\<in>schema_material_premises S. material_leaves M)"
    by (simp add: case_prod_beta material_leaves_rename)
  show ?thesis unfolding schema_leaves_def rename_schema_def using calls material by (simp add: pattern_leaves_rename)
qed

lemma system_payloads_rename: "system_payloads (rename_system g P)=system_payloads P"
proof -
  have "system_leaves (rename_system g P)=system_leaves P"
    by (simp add: system_leaves_def rename_system_def case_prod_beta schema_leaves_rename)
  then show ?thesis by (simp add: system_payloads_def)
qed

lemma schema_alpha_variant_payloads:
  assumes "schema_alpha_variant S T"
  shows "schema_payloads T=schema_payloads S"
proof -
  obtain f h where "T=rename_schema f h id S" using assms unfolding schema_alpha_variant_def by blast
  then show ?thesis by (simp add: schema_payloads_def schema_leaves_rename)
qed

lemma system_alpha_variant_payloads:
  assumes variant: "system_alpha_variant P Q"
  shows "system_payloads Q=system_payloads P"
proof -
  have pf: "schema_system_formed P" and qf: "schema_system_formed Q"
    and defs: "system_definitions P=system_definitions Q" using variant by (simp_all add: system_alpha_variant_def)
  have each: "definition_payloads (system_interface Q d) (system_clause_family Q d)=
      definition_payloads (system_interface P d) (system_clause_family P d)"
    if member: "d\<in>system_definitions P" for d
  proof -
    obtain f h where interface: "system_interface Q d=rename_pattern f (system_interface P d)"
      and family: "schema_family_variant h (system_clause_family P d) (system_clause_family Q d)"
      using variant member unfolding system_alpha_variant_def by blast
    have clauses: "(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)=
        (\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
    proof (rule set_eqI, rule iffI)
      fix v assume "v\<in>(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)"
      then have "\<exists>x\<in>system_clause_family Q d. v\<in>schema_payloads (snd x)" by (simp only: UN_iff case_prod_beta)
      then obtain x where x: "x\<in>system_clause_family Q d" and v: "v\<in>schema_payloads (snd x)" by (rule bexE)
      have t: "(fst x,snd x)\<in>system_clause_family Q d" using x by simp
      have "fst x\<in>rel_dom (system_clause_family Q d)" using t by (rule rel_domI)
      then obtain c where c: "c\<in>rel_dom (system_clause_family P d)" and e: "fst x=h c"
        using family unfolding schema_family_variant_def by blast
      obtain S where s: "(c,S)\<in>system_clause_family P d" using c by (auto simp: rel_dom_def)
      obtain T' where t': "(h c,T')\<in>system_clause_family Q d" and alpha: "schema_alpha_variant S T'"
        using family s unfolding schema_family_variant_def by blast
      have sv: "single_valued (system_clause_family Q d)" using family unfolding schema_family_variant_def by blast
      have t2: "(h c,snd x)\<in>system_clause_family Q d" using t e by simp
      have same: "T'=snd x" by (rule single_valued_outputs[OF sv t' t2])
      have payload: "v\<in>schema_payloads S" using v schema_alpha_variant_payloads[OF alpha] same by simp
      show "v\<in>(\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
        unfolding UN_iff case_prod_beta using s payload by (intro bexI[where x="(c,S)"]) simp_all
    next
      fix v assume "v\<in>(\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
      then have "\<exists>x\<in>system_clause_family P d. v\<in>schema_payloads (snd x)" by (simp only: UN_iff case_prod_beta)
      then obtain x where x: "x\<in>system_clause_family P d" and v: "v\<in>schema_payloads (snd x)" by (rule bexE)
      have s: "(fst x,snd x)\<in>system_clause_family P d" using x by simp
      obtain T where t: "(h (fst x),T)\<in>system_clause_family Q d" and alpha: "schema_alpha_variant (snd x) T"
        using family s unfolding schema_family_variant_def by blast
      have payload: "v\<in>schema_payloads T" using v schema_alpha_variant_payloads[OF alpha] by simp
      show "v\<in>(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)"
        unfolding UN_iff case_prod_beta using t payload by (intro bexI[where x="(h (fst x),T)"]) simp_all
    qed
    show ?thesis unfolding definition_payloads_def interface pattern_leaves_rename clauses ..
  qed
  show ?thesis unfolding system_payloads_definitions[OF qf] system_payloads_definitions[OF pf] defs[symmetric]
    by (rule SUP_cong[OF refl each])
qed

section \<open>The leaf map and rooting\<close>

text \<open>
  A leaf map of a program (@{const map_system_leaves}) keeps every definition, clause key and callee, so it
  keeps the dependency edges, and restriction and rooting commute with it, the roots kept; it keeps every socket
  and changes no material premise into none, so the mapped program is observation-free exactly when the source is.
\<close>

lemma system_restriction_leaf_map:
  "system_restriction (map_system_leaves h P) U=map_system_leaves h (system_restriction P U)"
  by (rule schema_system.equality) (auto simp: system_restriction_def)

lemma rooted_system_leaf_map:
  "rooted_system (map_system_leaves h P) R=map_system_leaves h (rooted_system P R)"
  by (simp add: rooted_system_def system_definition_closure_def system_restriction_leaf_map)

lemma system_observation_free_leaf_map:
  "system_observation_free (map_system_leaves h P) \<longleftrightarrow> system_observation_free P"
proof
  assume free: "system_observation_free (map_system_leaves h P)"
  show "system_observation_free P" unfolding system_observation_free_def
  proof (intro allI impI)
    fix d c S assume clause: "((d,c),S)\<in>system_clauses P"
    have "((d,c),map_schema_leaves h S)\<in>system_clauses (map_system_leaves h P)"
      unfolding map_system_clauses_member using clause by blast
    then have "schema_material_premises (map_schema_leaves h S)={}"
      using free unfolding system_observation_free_def by blast
    then show "schema_material_premises S={}" by simp
  qed
next
  assume free: "system_observation_free P"
  show "system_observation_free (map_system_leaves h P)" unfolding system_observation_free_def
  proof (intro allI impI)
    fix d c T assume "((d,c),T)\<in>system_clauses (map_system_leaves h P)"
    then obtain S where clause: "((d,c),S)\<in>system_clauses P" and T: "T=map_schema_leaves h S"
      unfolding map_system_clauses_member by blast
    have "schema_material_premises S={}" using free clause unfolding system_observation_free_def by blast
    then show "schema_material_premises T={}" using T by simp
  qed
qed

end
