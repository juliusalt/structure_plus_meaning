theory Factor_Schema_Compilation
  imports Factor_Schema_Encoding Factor_Alpha_Semantics
begin

section \<open>Construction preserves the source schema independently of its enumeration\<close>

lemma template_projection_left:
  "template_projection f (Inl dp) = Inl (fst dp,rename_pattern f (snd dp))"
  by (cases dp) simp

lemma mapped_schema_template_sum:
  "socket_sum (schema_premises (rename_schema f h id S))
    (schema_material_premises (rename_schema f h id S)) =
    (\<lambda>(s,t). (h s,template_projection f t)) `
      socket_sum (schema_premises S) (schema_material_premises S)"
  by (simp add: socket_sum_def rename_schema_def map_socket_graph_def map_prod_def
      image_Un image_image split_def template_projection_left)

lemma schema_list_recovers_source:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes enumeration: "set (zip os ts) = socket_sum (schema_premises S) (schema_material_premises S)"
  shows "schema_list_projection f (schema_conclusion S) (map h os) ts = rename_schema f h id S"
proof -
  let ?L = "schema_list_projection f (schema_conclusion S) (map h os) ts"
  let ?R = "rename_schema f h id S"
  have heads: "schema_conclusion ?L = schema_conclusion ?R"
    by (simp add: schema_list_projection_def rename_schema_def)
  have sum: "socket_sum (schema_premises ?L) (schema_material_premises ?L) =
    socket_sum (schema_premises ?R) (schema_material_premises ?R)"
    by (simp only: schema_list_socket_sum set_zip_map_both enumeration mapped_schema_template_sum)
  have bodies: "schema_premises ?L = schema_premises ?R \<and> schema_material_premises ?L = schema_material_premises ?R"
    using sum by (simp only: socket_sum_unique)
  show ?thesis using heads bodies by (cases ?L; cases ?R) simp
qed

theorem schema_list_rule_equivalence:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes enumeration: "set (zip os ts) = socket_sum (schema_premises S) (schema_material_premises S)"
    and binders: "inj_on f (schema_variables S)" and sockets: "inj_on h (schema_sockets S)"
  shows "schema_rule_instance (schema_list_projection f (schema_conclusion S) (map h os) ts) X t
    \<longleftrightarrow> schema_rule_instance S X t"
  by (simp only: schema_list_recovers_source[OF enumeration] schema_rule_instance_alpha[OF binders sockets])

text \<open>
  The list used during construction is an enumeration of the complete original
  socket graph. Its native projection is precisely an injective change of the
  source binder and socket coordinates. The independently defined complete
  rule-instance relation is preserved and reflected for every support relation
  and argument, including all material observations and repeated premises.
\<close>

end
