theory Factor_Finite_Artifact_Value_Readers
  imports Factor_Finite_Data_Value_Readers Factor_Executable_Artifact_Values
begin

text \<open>
  An incidence and an attachment row are read by the material observation's own readers
  (@{const finite_incidence_read}, @{const finite_attachment_read}): one reader of each row notion.
\<close>

lemma finite_address_list_read_exact:
  "finite_data_list_values finite_payload_value_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map Payload_Term xs)"
  by (rule finite_data_list_values_encoded) (rule finite_payload_value_read_exact)

lemma finite_incidence_list_read_exact:
  "finite_data_list_values finite_incidence_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map incidence_data xs)"
  by (rule finite_data_list_values_encoded) (rule finite_incidence_read_correct)

lemma finite_address_pair_list_read_exact:
  "finite_data_list_values finite_attachment_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map address_pair_data xs)"
  by (rule finite_data_list_values_encoded) (rule finite_attachment_read_correct)

fun finite_artifact_rows_read :: "finite_factor_term \<Rightarrow> artifact_value_rows option" where
  "finite_artifact_rows_read (Finite_Pair a (Finite_Pair e (Finite_Pair b f)))=
    option_product_map (finite_data_list_values finite_payload_value_read)
      (option_product_map (finite_data_list_values finite_incidence_read)
        (option_product_map (finite_data_list_values finite_attachment_read)
          (finite_data_list_values finite_attachment_read))) (a,e,b,f)"
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
