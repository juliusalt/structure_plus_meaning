theory Factor_Keyed_Row_Admission
  imports Factor_Keyed_Lists
begin

lemma keyed_list_row_admission:
  "(21,pair_list_term xs)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    formed_key_rows xs \<and> distinct (map fst xs)"
  by (simp only: keyed_list_exact pair_list_term_injective) auto

end
