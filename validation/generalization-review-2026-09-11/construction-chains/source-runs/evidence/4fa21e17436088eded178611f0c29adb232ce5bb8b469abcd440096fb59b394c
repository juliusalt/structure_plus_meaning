theory Factor_Schema_Reference_Binders
  imports Factor_Schema_Observations
begin

section \<open>The report's first field enumerates every schema variable\<close>

theorem schema_reference_binder_boundary:
  assumes report: "schema_reference_presents S (Pair_Term b v)"
  shows "\<exists>Bs. b=data_list_term (map Payload_Term Bs) \<and> distinct Bs \<and>
    set Bs=schema_variables S \<and> (\<forall>a\<in>set Bs. octets_formed a)"
proof -
  obtain Bs where fields: "b=data_list_term (map Payload_Term Bs)" "distinct Bs"
    "set Bs=schema_variables S" "schema_data_formed S"
    using report by (simp only: schema_reference_presents_fields factor_term.inject) blast
  show ?thesis using fields by (auto simp: schema_data_formed_def)
qed

text \<open>
  The scope includes variables appearing only in premises or material
  operands. The remaining complete report is retained by the caller.
\<close>

end
