theory Finite_Keyed_Fibre_Values
  imports Finite_Keyed_Table_Comparison
begin

section \<open>The public finite operation returns the complete existing fibre\<close>

definition finite_key_fibre_values ::
  "finite_factor_term\<Rightarrow>(finite_factor_term\<times>finite_factor_term) list\<Rightarrow>finite_factor_term list" where
  "finite_key_fibre_values k xs=key_values k xs"

theorem finite_key_fibre_values_native:
  "(28,key_fibre_argument (decode_finite_term k) (pair_list_term (decoded_keyed_rows xs))
      (data_list_term (map decode_finite_term (finite_key_fibre_values k xs))))\<in>positive_meaning key_fibre_system
    \<longleftrightarrow> finite_term_formed k \<and> finite_data_projection k=Some k \<and> finite_keyed_rows_formed xs"
  by (simp only: finite_key_fibre_holds_correct[symmetric] finite_key_fibre_holds_def finite_key_fibre_values_def) simp

text \<open>
  This is the existing key-values operation at the finite term type. The fixed
  type makes the value-producing operation available through the generated
  module interface without requiring an abstract equality dictionary from a
  host caller. It introduces no new fibre semantics. Missing keys return an
  empty list and repeated rows remain repeated values. Admission still requires
  the complete key and table formation conditions in the equation above.
\<close>

export_code finite_key_fibre_values checking SML

end
