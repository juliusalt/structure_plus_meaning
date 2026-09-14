theory Factor_Finite_Coordinate_Value_Readers
  imports Factor_Finite_Data_Value_Readers Factor_Coordinate_Values
begin

fun finite_natural_value_read :: "finite_factor_term \<Rightarrow> nat option" where
  "finite_natural_value_read (Finite_Payload p)=(if p=[] then Some 0 else None)"
| "finite_natural_value_read (Finite_Pair x y)=(if x=Finite_Payload [] then
    map_option Suc (finite_natural_value_read y) else None)"
| "finite_natural_value_read (Finite_Target a)=None"

lemma decode_empty_payload_iff:
  "decode_finite_term t=Payload_Term [] \<longleftrightarrow> t=Finite_Payload []"
  by (cases t) simp_all

theorem finite_natural_value_read_exact:
  "finite_natural_value_read t=Some n \<longleftrightarrow> decode_finite_term t=natural_data_term n"
  by (induction t arbitrary: n) (case_tac n; auto simp: decode_empty_payload_iff split: if_splits)+

lemma finite_natural_list_read_exact:
  "finite_data_list_values finite_natural_value_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map natural_data_term xs)"
  by (rule finite_data_list_values_encoded) (rule finite_natural_value_read_exact)

fun finite_use_value_read :: "finite_factor_term \<Rightarrow> local_address option option" where
  "finite_use_value_read (Finite_Payload p)=(if p=[] then Some None else None)"
| "finite_use_value_read (Finite_Pair x y)=(if y=Finite_Payload [] then
    map_option Some (finite_data_list_values finite_natural_value_read x) else None)"
| "finite_use_value_read (Finite_Target a)=None"

theorem finite_use_value_read_exact:
  "finite_use_value_read t=Some u \<longleftrightarrow> decode_finite_term t=use_data_term u"
  by (cases t; cases u) (auto simp: finite_natural_list_read_exact decode_empty_payload_iff split: if_splits)

fun finite_site_value_read :: "finite_factor_term \<Rightarrow> (local_address option\<times>local_address) option" where
  "finite_site_value_read (Finite_Pair x y)=option_product_map finite_use_value_read finite_payload_value_read (x,y)"
| "finite_site_value_read (Finite_Payload p)=None"
| "finite_site_value_read (Finite_Target a)=None"

theorem finite_site_value_read_exact:
  "finite_site_value_read t=Some (u,r) \<longleftrightarrow> decode_finite_term t=site_data_term u r"
  by (cases t) (simp_all add: site_data_term_def option_product_map_result
    finite_use_value_read_exact finite_payload_value_read_exact)

export_code finite_natural_value_read finite_use_value_read finite_site_value_read checking SML

text \<open>
  Use words preserve arbitrary natural components. Site addresses retain their
  exact payload; occurrence and formation conditions belong to the consuming
  environment or judgment relation. No coordinate is chosen by the reader.
\<close>

end
