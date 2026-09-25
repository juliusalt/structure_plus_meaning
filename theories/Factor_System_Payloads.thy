theory Factor_System_Payloads
  imports Factor_Positive_Parametricity Factor_System_Composition Factor_System_Restriction Factor_System_Renaming
    Factor_Payload_Audit
begin

section \<open>The payloads of composed programs\<close>

text \<open>
  The payloads a program states (@{const system_payloads}) through the three ways programs are composed:
  a view, fresh or not, states its predecessor's payloads with those of its interface and its clauses, a union
  what its two parts state, and a rooted restriction no more than its source. A program built by these steps has
  its payloads composed down its lineage, each step computed on its own patterns alone.
\<close>

lemma add_view_definition_payloads:
  "system_payloads (add_view_definition P d p C)=system_payloads P\<union>{v. Payload_Term v\<in>pattern_leaves p}\<union>
    (\<Union>(c,S)\<in>C. {v. Payload_Term v\<in>schema_leaves S})"
  by (auto simp: system_payloads_def system_leaves_def add_view_definition_def)

lemma system_union_payloads: "system_payloads (system_union P Q)=system_payloads P\<union>system_payloads Q"
  by (auto simp: system_payloads_def system_leaves_def system_union_def)

lemma rooted_system_payloads: "system_payloads (rooted_system P R)\<subseteq>system_payloads P"
  by (auto simp: system_payloads_def system_leaves_def rooted_system_def system_restriction_def)

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

end
