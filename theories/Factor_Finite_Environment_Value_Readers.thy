theory Factor_Finite_Environment_Value_Readers
  imports Factor_Finite_Artifact_Value_Readers Factor_Finite_Coordinate_Value_Readers
    Factor_Finite_Collection_Value_Readers Factor_Data_Collection_Transport Factor_Environment_Values
begin

fun finite_environment_artifact_entry_read ::
  "finite_factor_term \<Rightarrow> (local_address option\<times>finite_exact_artifact) option" where
  "finite_environment_artifact_entry_read (Finite_Pair x y)=
    option_product_map finite_use_value_read finite_artifact_value_read (x,y)"
| "finite_environment_artifact_entry_read (Finite_Payload p)=None"
| "finite_environment_artifact_entry_read (Finite_Target a)=None"

lemma finite_environment_artifact_entry_read_exact:
  "finite_environment_artifact_entry_read t=Some z \<longleftrightarrow>
    environment_artifact_entry_presents (map_prod id decode_finite_object z) (decode_finite_term t)"
  by (cases t; cases z) (auto simp: option_product_map_result finite_use_value_read_exact
    finite_artifact_value_read_exact environment_artifact_entry_presents_def)

fun finite_binding_value_read ::
  "finite_factor_term \<Rightarrow> ((local_address option\<times>local_address)\<times>local_address option) option" where
  "finite_binding_value_read (Finite_Pair x y)=option_product_map finite_site_value_read finite_use_value_read (x,y)"
| "finite_binding_value_read (Finite_Payload p)=None"
| "finite_binding_value_read (Finite_Target a)=None"

lemma finite_binding_value_read_exact:
  "finite_binding_value_read t=Some z \<longleftrightarrow> decode_finite_term t=binding_data z"
proof -
  obtain u k v where row: "z=((u,k),v)" by (cases z) auto
  show ?thesis by (cases t) (simp_all add: row option_product_map_result finite_site_value_read_exact
    finite_use_value_read_exact binding_data_def site_data_term_def)
qed

lemma finite_environment_artifact_collection_read_exact:
  "finite_data_collection_read finite_environment_artifact_entry_read t=Some A \<longleftrightarrow>
    data_collection_presents environment_artifact_entry_presents
      (map_relation_values decode_finite_object (fset A)) (decode_finite_term t)"
proof -
  have injective: "inj (map_prod id decode_finite_object)" by (auto simp: inj_def)
  have actual: "finite_data_collection_read finite_environment_artifact_entry_read t=Some A \<longleftrightarrow>
    data_collection_presents (\<lambda>z v. environment_artifact_entry_presents
      (map_prod id decode_finite_object z) v) (fset A) (decode_finite_term t)"
    by (rule finite_data_collection_read_exact) (rule finite_environment_artifact_entry_read_exact)
  have image: "data_collection_presents (\<lambda>z v. environment_artifact_entry_presents
      (map_prod id decode_finite_object z) v) (fset A) (decode_finite_term t)=
    data_collection_presents environment_artifact_entry_presents
      (map_prod id decode_finite_object ` fset A) (decode_finite_term t)"
    by (rule sym) (rule data_collection_presents_image[OF injective])
  show ?thesis by (simp only: actual; subst image;
    simp only: map_relation_values_def map_prod_def id_apply case_prod_unfold)
qed

lemma finite_binding_collection_read_exact:
  "finite_data_collection_read finite_binding_value_read t=Some B \<longleftrightarrow>
    data_collection_presents (\<lambda>z v. v=binding_data z) (fset B) (decode_finite_term t)"
  by (rule finite_data_collection_read_exact) (rule finite_binding_value_read_exact)

fun finite_environment_fields_read where
  "finite_environment_fields_read (Finite_Pair a b)=
    option_product_map (finite_data_collection_read finite_environment_artifact_entry_read)
      (finite_data_collection_read finite_binding_value_read) (a,b)"
| "finite_environment_fields_read (Finite_Payload p)=None"
| "finite_environment_fields_read (Finite_Target a)=None"

definition finite_environment_value_read ::
  "finite_factor_term \<Rightarrow> local_address option finite_artifact_environment option" where
  "finite_environment_value_read t=(case finite_environment_fields_read t of None \<Rightarrow> None
    | Some (A,B) \<Rightarrow> let E=\<lparr>finite_environment_artifacts=A,finite_environment_bindings=B\<rparr> in
      if finite_environment_formed E then Some E else None)"

lemma finite_environment_value_read_result:
  "finite_environment_value_read t=Some E \<longleftrightarrow> finite_environment_formed E \<and>
    finite_environment_fields_read t=Some (finite_environment_artifacts E,finite_environment_bindings E)"
  by (cases E) (auto simp: finite_environment_value_read_def Let_def split: option.splits prod.splits if_splits)

theorem finite_environment_value_read_exact:
  "finite_environment_value_read t=Some E \<longleftrightarrow>
    environment_value_presents (decode_finite_environment E) (decode_finite_term t)"
  by (cases t) (auto simp: finite_environment_value_read_result option_product_map_result
    finite_environment_formed_correct finite_environment_artifact_collection_read_exact
    finite_binding_collection_read_exact environment_value_presents_def)

text \<open>
  Both complete collections are recovered before the original environment
  formation condition is checked. Equal artifacts at different uses remain
  separate entries, counted multiplicity is retained, and every binding source,
  slot and target is recovered from its actual value. No enumeration order is
  privileged by the reader.
\<close>

end
