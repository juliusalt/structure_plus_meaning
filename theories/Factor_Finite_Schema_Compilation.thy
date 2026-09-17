theory Factor_Finite_Schema_Compilation
  imports Factor_Finite_Schema_Syntax Factor_Finite_Schema_Renaming Finite_Functional_Enumeration Factor_Schema_Code
begin

section \<open>Enumeration is derived from both complete original premise fields\<close>

definition finite_schema_template_rows :: "('a,'s::linorder,'u definition_site) finite_factor_schema \<Rightarrow>
    ('s\<times>('a,'u) finite_premise_template) list" where
  "finite_schema_template_rows S=finite_functional_rows
    (finite_socket_sum (finite_schema_premises S) (finite_schema_materials S))"

lemma finite_schema_template_table_functional:
  assumes "finite_schema_formed S"
  shows "finite_relation_functional (finite_socket_sum (finite_schema_premises S) (finite_schema_materials S))"
  using assms by (auto simp: finite_socket_sum_functional finite_schema_formed_def)

lemma finite_schema_template_rows_keys:
  assumes formed: "finite_schema_formed S"
  shows "distinct (map fst (finite_schema_template_rows S))"
  unfolding finite_schema_template_rows_def
  by (rule finite_functional_rows_distinct_keys[OF finite_schema_template_table_functional[OF formed]])

lemma finite_schema_template_rows_exact:
  assumes formed: "finite_schema_formed S"
  shows "map_relation_values decode_finite_native_premise (set (finite_schema_template_rows S))=
    socket_sum (schema_premises (decode_finite_schema S)) (schema_material_premises (decode_finite_schema S))"
  by (simp only: finite_schema_template_rows_def
    finite_functional_rows_exact[OF finite_schema_template_table_functional[OF formed]]
    decode_finite_premise_socket_sum decode_finite_schema_fields)

type_synonym finite_compiled_schema = "finite_exact_artifact\<times>local_address\<times>
  (local_address,local_address,local_address option definition_site) finite_factor_schema\<times>
  (local_address\<times>finite_exact_artifact) fset\<times>(local_address\<times>local_address option definition_site) fset"

definition finite_compile_schema :: "('a::linorder,'s::linorder,local_address option definition_site) finite_factor_schema \<Rightarrow>
    finite_compiled_schema option" where
  "finite_compile_schema S=(if finite_schema_formed S \<and> fBall (finite_schema_dependencies S) (\<lambda>d. octets_formed (snd d)) then
    (let rows=finite_schema_template_rows S; ts=map snd rows;
      f=finite_binder_coordinates (finite_schema_variables S) in
      case finite_schema_code f (finite_schema_conclusion S) ts of (R,r,ss) \<Rightarrow>
        Some (R,r,finite_rename_schema f (listed_rekey (map fst rows) ss []) id S,
          finite_schema_body_literals (finite_schema_conclusion S) ts,finite_schema_body_callees ts))
    else None)"

lemma finite_compile_schema_domain:
  "finite_compile_schema S=None \<longleftrightarrow>
    \<not>(finite_schema_formed S \<and> fBall (finite_schema_dependencies S) (\<lambda>d. octets_formed (snd d)))"
  by (auto simp: finite_compile_schema_def Let_def split: prod.splits)

theorem finite_compile_schema_correct:
  assumes result: "finite_compile_schema S=Some (R,r,T,L,C)"
  shows "finite_schema_formed S" "finite_exact_formed R"
    "schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
    "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    "reference_table_formed (map_relation_values decode_finite_object (fset L)) (fset C)"
    "rel_dom (fset L)\<union>rel_dom (fset C)\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "rel_ran (fset C)=schema_dependencies (decode_finite_schema S)"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
      syntax_references E u (map_relation_values decode_finite_object (fset L)) (fset C) \<longrightarrow>
      native_schema_at E u r (decode_finite_schema T)"
    "\<forall>X t. schema_rule_instance (decode_finite_schema T) X t \<longleftrightarrow> schema_rule_instance (decode_finite_schema S) X t"
proof -
  have guard: "finite_schema_formed S \<and> fBall (finite_schema_dependencies S) (\<lambda>d. octets_formed (snd d))"
    using result finite_compile_schema_domain[of S] by auto
  show formed: "finite_schema_formed S" using guard by blast
  let ?S="decode_finite_schema S"
  let ?rows="finite_schema_template_rows S"
  let ?os="map fst ?rows"
  let ?ts="map snd ?rows"
  let ?ts'="map decode_finite_native_premise ?ts"
  let ?p="finite_schema_conclusion S"
  let ?f="finite_binder_coordinates (finite_schema_variables S)"
  have sf: "schema_formed ?S" using formed by (simp only: finite_schema_formed_correct)
  have addresses: "\<forall>d\<in>schema_dependencies ?S. octets_formed (snd d)"
    using guard by (simp add: finite_schema_dependencies_correct[symmetric])
  have len: "length ?os=length ?ts'" by simp
  have enum: "set (zip ?os ?ts')=socket_sum (schema_premises ?S) (schema_material_premises ?S)"
    by (simp only: listed_relation_values finite_schema_template_rows_exact[OF formed])
  have variables: "schema_body_variables (schema_conclusion ?S) ?ts'=schema_variables ?S"
    by (rule schema_enumerated_variables[OF len enum])
  have sockets: "schema_sockets ?S=set ?os" by (rule schema_enumerated_sockets[OF len enum])
  have pf: "finite_pattern_formed ?p" using formed by (simp add: finite_schema_formed_def)
  have tf: "\<forall>t\<in>set ?ts. finite_template_formed t"
    using schema_enumerated_templates_formed[OF sf addresses len enum] by auto
  have source_binders: "binder_addressing (schema_variables ?S) ?f"
    using finite_binder_coordinates_properties[of "finite_schema_variables S"]
    by (simp only: finite_schema_variables_correct)
  have binders: "binder_addressing (fset (finite_schema_body_variables ?p ?ts)) ?f"
    using source_binders by (simp only: finite_schema_body_variables_exact decode_finite_schema_fields[symmetric] variables)
  obtain A a ss where code: "finite_schema_code ?f ?p ?ts=(A,a,ss)" by (metis surjective_pairing)
  have built: "finite_exact_formed A"
    "bag_count (object_data (decode_finite_object A))=(\<lambda>_. 0)"
    "a\<in>rra_carrier (object_structure (decode_finite_object A))"
    "length ss=length ?ts" "distinct ss"
    "reference_table_formed (map_relation_values decode_finite_object (fset (finite_schema_body_literals ?p ?ts)))
      (fset (finite_schema_body_callees ?ts))"
    "rel_dom (map_relation_values decode_finite_object (fset (finite_schema_body_literals ?p ?ts)))\<union>
      rel_dom (fset (finite_schema_body_callees ?ts))\<subseteq>rra_carrier (object_structure (decode_finite_object A))"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object A) \<longrightarrow>
      syntax_references E u (map_relation_values decode_finite_object (fset (finite_schema_body_literals ?p ?ts)))
        (fset (finite_schema_body_callees ?ts)) \<longrightarrow>
      native_schema_at E u a (schema_list_projection ?f (decode_finite_pattern ?p) ss ?ts')"
    using finite_schema_code_properties[OF pf tf binders code] by blast+
  let ?h="listed_rekey ?os ss []"
  have lengths: "length ?os=length ss" using built(4) by simp
  have rekey: "inj_on ?h (set ?os)" "map ?h ?os=ss"
    by (rule listed_rekey_properties[OF lengths finite_schema_template_rows_keys[OF formed] built(5)])+
  let ?T="finite_rename_schema ?f ?h id S"
  have projection: "schema_list_projection ?f (decode_finite_pattern ?p) ss ?ts'=decode_finite_schema ?T"
    using schema_list_recovers_source[OF enum, where f="?f" and h="?h"]
    by (simp only: rekey(2) finite_rename_schema_correct decode_finite_schema_fields)
  have fields: "R=A" "r=a" "T=?T" "L=finite_schema_body_literals ?p ?ts" "C=finite_schema_body_callees ?ts"
    using result by (auto simp: finite_compile_schema_def Let_def guard code)
  show "finite_exact_formed R" "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    using built(1-3) by (simp_all only: fields)
  have fi: "inj_on ?f (schema_variables ?S)"
    using source_binders by (simp add: binder_addressing_def finite_addressing_def)
  have hi: "inj_on ?h (schema_sockets ?S)" using rekey(1) by (simp only: sockets)
  show variant: "schema_alpha_variant ?S (decode_finite_schema T)"
    by (simp only: fields(3) finite_rename_schema_correct schema_alpha_variant_def;
      rule exI[of _ "?f"], rule exI[of _ "?h"])
      (use fi hi in blast)
  show "reference_table_formed (map_relation_values decode_finite_object (fset L)) (fset C)"
    "rel_dom (fset L)\<union>rel_dom (fset C)\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    using built(6,7) by (simp_all only: fields map_relation_values_domain)
  show "rel_ran (fset C)=schema_dependencies ?S"
    by (simp only: fields(5) finite_schema_body_callees_exact; rule schema_enumerated_callees[OF len enum])
  show "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
    syntax_references E u (map_relation_values decode_finite_object (fset L)) (fset C) \<longrightarrow>
    native_schema_at E u r (decode_finite_schema T)"
    using built(8) by (simp only: fields projection)
  show "\<forall>X t. schema_rule_instance (decode_finite_schema T) X t \<longleftrightarrow> schema_rule_instance ?S X t"
    using schema_alpha_rule_instance[OF variant] by blast
qed

corollary finite_compiled_schema_code:
  assumes result: "finite_compile_schema S=Some (R,r,T,L,C)"
  shows "schema_code (decode_finite_object R) r (decode_finite_schema T)
    (map_relation_values decode_finite_object (fset L)) (fset C)"
proof -
  have dependencies: "schema_dependencies (decode_finite_schema T)=schema_dependencies (decode_finite_schema S)"
    by (rule schema_alpha_dependencies[OF finite_compile_schema_correct(3)[OF result]])
  show ?thesis using finite_compile_schema_correct[OF result] dependencies
    by (auto simp: schema_code_def finite_exact_formed_correct)
qed

text \<open>
  The constructor checks the actual complete source schema and callee addresses,
  enumerates every original socket, computes its binder and socket coordinates,
  and emits finite code plus its complete reference tables. Its recovered
  schema preserves every rule instance on every support relation and argument.
  The returned schema is a proved projection of that code, not an extra field
  of native syntax or a supplied meaning table.
\<close>

end
