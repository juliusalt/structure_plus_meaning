theory Factor_Finite_Artifact_Value_Readers
  imports Factor_Finite_Data_Value_Readers Factor_Executable_Artifact_Values
begin

fun finite_address_pair_value_read :: "finite_factor_term \<Rightarrow> (local_address\<times>octets) option" where
  "finite_address_pair_value_read (Finite_Pair x y)=option_product_map finite_payload_value_read finite_payload_value_read (x,y)"
| "finite_address_pair_value_read (Finite_Payload p)=None"
| "finite_address_pair_value_read (Finite_Target a)=None"

lemma finite_address_pair_value_read_exact:
  "finite_address_pair_value_read t=Some z \<longleftrightarrow> decode_finite_term t=address_pair_data z"
  by (cases t; cases z) (simp_all add: address_pair_data_def option_product_map_result finite_payload_value_read_exact)

fun finite_incidence_value_read ::
  "finite_factor_term \<Rightarrow> (local_address\<times>local_address\<times>local_address) option" where
  "finite_incidence_value_read (Finite_Pair x y)=option_product_map finite_payload_value_read finite_address_pair_value_read (x,y)"
| "finite_incidence_value_read (Finite_Payload p)=None"
| "finite_incidence_value_read (Finite_Target a)=None"

lemma finite_incidence_value_read_exact:
  "finite_incidence_value_read t=Some z \<longleftrightarrow> decode_finite_term t=incidence_data z"
  by (cases t; cases z) (simp_all add: incidence_data_def option_product_map_result finite_payload_value_read_exact
    finite_address_pair_value_read_exact)

lemma finite_address_list_read_exact:
  "finite_data_list_values finite_payload_value_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map Payload_Term xs)"
  by (rule finite_data_list_values_encoded) (rule finite_payload_value_read_exact)

lemma finite_incidence_list_read_exact:
  "finite_data_list_values finite_incidence_value_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map incidence_data xs)"
  by (rule finite_data_list_values_encoded) (rule finite_incidence_value_read_exact)

lemma finite_address_pair_list_read_exact:
  "finite_data_list_values finite_address_pair_value_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map address_pair_data xs)"
  by (rule finite_data_list_values_encoded) (rule finite_address_pair_value_read_exact)

fun finite_artifact_rows_read :: "finite_factor_term \<Rightarrow> artifact_value_rows option" where
  "finite_artifact_rows_read (Finite_Pair a (Finite_Pair e (Finite_Pair b f)))=
    option_product_map (finite_data_list_values finite_payload_value_read)
      (option_product_map (finite_data_list_values finite_incidence_value_read)
        (option_product_map (finite_data_list_values finite_address_pair_value_read)
          (finite_data_list_values finite_address_pair_value_read))) (a,e,b,f)"
| "finite_artifact_rows_read t=None"

theorem finite_artifact_rows_read_exact:
  "finite_artifact_rows_read t=Some (A,E,B,F) \<longleftrightarrow>
    decode_finite_term t=artifact_data_term A E B F"
  by (cases t rule: finite_artifact_rows_read.cases)
    (simp_all add: artifact_data_term_def option_product_map_result finite_address_list_read_exact
      finite_incidence_list_read_exact finite_address_pair_list_read_exact)

definition finite_artifact_value_read where
  "finite_artifact_value_read t=(case finite_artifact_rows_read t of None \<Rightarrow> None
    | Some (A,E,B,F) \<Rightarrow> let C=finite_enumerated_artifact A E B F in
      if finite_artifact_enumeration C A E B F then Some C else None)"

lemma finite_artifact_value_read_result:
  "finite_artifact_value_read t=Some C \<longleftrightarrow>
    (\<exists>A E B F. finite_artifact_rows_read t=Some (A,E,B,F) \<and> finite_artifact_enumeration C A E B F)"
  by (auto simp: finite_artifact_value_read_def finite_artifact_enumeration_def Let_def
    split: option.splits prod.splits if_splits)

theorem finite_artifact_value_read_exact:
  "finite_artifact_value_read t=Some C \<longleftrightarrow>
    artifact_value_presents (decode_finite_object C) (decode_finite_term t)"
  by (simp only: finite_artifact_value_read_result finite_artifact_rows_read_exact
    finite_artifact_enumeration_correct artifact_value_presents_def; blast)

text \<open>
  The actual four lists determine the reconstructed artifact. Every admitted
  enumeration order remains available. Counted attachments retain repetitions;
  the original enumeration contract checks distinctness of the set fields and
  formation of the complete reconstructed artifact.
\<close>

end
