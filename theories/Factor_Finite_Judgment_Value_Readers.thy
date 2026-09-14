theory Factor_Finite_Judgment_Value_Readers
  imports Factor_Finite_Environment_Value_Readers Factor_Judgment_Values RRA_Finite_Environment_Positions
begin

fun finite_judgment_fields_read where
  "finite_judgment_fields_read (Finite_Pair e (Finite_Pair p a))=
    option_product_map finite_environment_value_read
      (option_product_map finite_site_value_read finite_site_value_read) (e,p,a)"
| "finite_judgment_fields_read t=None"

definition finite_judgment_value_read ::
  "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>
    local_address option\<times>local_address\<times>local_address option\<times>local_address) option" where
  "finite_judgment_value_read t=(case finite_judgment_fields_read t of None \<Rightarrow> None
    | Some (E,(pu,pr),(au,ar)) \<Rightarrow>
      if (pu,pr) |\<in>| finite_environment_positions E \<and> (au,ar) |\<in>| finite_environment_positions E
      then Some (E,pu,pr,au,ar) else None)"

lemma finite_judgment_value_read_result:
  "finite_judgment_value_read t=Some (E,pu,pr,au,ar) \<longleftrightarrow>
    finite_judgment_fields_read t=Some (E,(pu,pr),(au,ar)) \<and>
    (pu,pr) |\<in>| finite_environment_positions E \<and> (au,ar) |\<in>| finite_environment_positions E"
  by (auto simp: finite_judgment_value_read_def split: option.splits prod.splits if_splits)

theorem finite_judgment_value_read_exact:
  "finite_judgment_value_read t=Some (E,pu,pr,au,ar) \<longleftrightarrow>
    judgment_value_presents (decode_finite_environment E) pu pr au ar (decode_finite_term t)"
  by (cases t rule: finite_judgment_fields_read.cases)
    (auto simp: finite_judgment_value_read_result option_product_map_result
      finite_environment_positions_correct finite_environment_value_read_exact
      finite_site_value_read_exact judgment_value_presents_def)

export_code finite_judgment_value_read checking SML

text \<open>
  The complete environment and both actual sites are recovered from the value.
  Environment formation and occurrence membership are required by the original
  judgment-value relation. Native program/application admission, least scope
  and proof truth remain separate conditions on the recovered subject.
\<close>

end
