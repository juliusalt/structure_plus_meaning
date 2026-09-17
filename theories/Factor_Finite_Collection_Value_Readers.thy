theory Factor_Finite_Collection_Value_Readers
  imports Factor_Finite_Data_Value_Readers
begin

definition finite_data_collection_read where
  "finite_data_collection_read read t=(case finite_data_list_values read t of None \<Rightarrow> None
    | Some xs \<Rightarrow> if distinct xs then Some (fset_of_list xs) else None)"

lemma finite_data_collection_read_result:
  "finite_data_collection_read read t=Some A \<longleftrightarrow>
    (\<exists>xs. finite_data_list_values read t=Some xs \<and> distinct xs \<and> fset_of_list xs=A)"
  by (auto simp: finite_data_collection_read_def split: option.splits if_splits)

theorem finite_data_collection_read_exact:
  assumes element: "\<And>v a. read v=Some a \<longleftrightarrow> P a (decode_finite_term v)"
  shows "finite_data_collection_read read t=Some A \<longleftrightarrow>
    data_collection_presents P (fset A) (decode_finite_term t)"
  by (simp only: finite_data_collection_read_result finite_data_list_values_present[where read=read and P=P, OF element]
    fset_inject[symmetric] fset_of_list.rep_eq data_collection_presents_def; blast)

text \<open>
  Collection recovery instantiates the complete list traversal and requires
  distinct recovered members. Every original member presentation and every
  complete enumeration order remain available under the element contract.
\<close>

end
