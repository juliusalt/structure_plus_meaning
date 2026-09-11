theory Factor_Observation_Table_Execution
  imports Factor_Observation_Table_Native Factor_Observation_Scope_Execution Factor_Keyed_Set_Execution
begin

section \<open>The computed row witnesses retain complete comparison\<close>

lemma observation_profile_table_lists:
  "(330,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) q)\<in>positive_meaning observation_table_system
    \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      (317,Pair_Term (observation_profile_table_term cs fs rows) q)\<in>positive_meaning keyed_set_system"
proof -
  have computation: "(329,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) w)\<in>positive_meaning observation_table_system
      \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      w=observation_profile_table_term cs fs rows" for w by (rule observation_profile_table_ordered)
  show ?thesis using observation_table_profile_comparison.at_computed_result[
    where p="observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))" and q=q
      and admitted="observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows)"
      and result="observation_profile_table_term cs fs rows", OF computation]
    by (simp only: observation_table_components)
qed

lemma observation_loss_table_lists:
  "(335,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) q)\<in>positive_meaning observation_table_system
    \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      (317,Pair_Term (observation_loss_table_term cs fs rows) q)\<in>positive_meaning keyed_set_system"
proof -
  have computation: "(334,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) w)\<in>positive_meaning observation_table_system
      \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      w=observation_loss_table_term cs fs rows" for w by (rule observation_loss_table_ordered)
  show ?thesis using observation_table_loss_comparison.at_computed_result[
    where p="observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))" and q=q
      and admitted="observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows)"
      and result="observation_loss_table_term cs fs rows", OF computation]
    by (simp only: observation_table_components)
qed

section \<open>Finite encodings commute with the existing row computations\<close>

abbreviation observation_profile_table_list where
  "observation_profile_table_list C F rows \<equiv> map (\<lambda>c. (c,observation_profile_list F rows c)) C"

abbreviation observation_loss_table_list where
  "observation_loss_table_list C F rows \<equiv>
    map (\<lambda>(c,d). ((c,d),observation_losses_list F rows c d)) (List.product C C)"

lemma list_product_map_fields:
  "List.product (map f xs) (map g ys)=map (map_prod f g) (List.product xs ys)"
  by (simp add: product_concat_map map_concat map_map comp_def)

lemma observation_profile_table_octet_encoding:
  "observation_profile_table_term (map observation_octet C) (map observation_octet F) (map observation_octet_row rows)=
    data_list_term (map keyed_set_row_term
      (map (map_prod keyed_octet (map keyed_octet_pair)) (observation_profile_table_list C F rows)))"
  by (simp only: map_map comp_def observation_profile_list_map[OF observation_octet_injective observation_octet_injective])
    (simp add: map_map comp_def case_prod_unfold)

lemma observation_loss_table_octet_encoding:
  "observation_loss_table_term (map observation_octet C) (map observation_octet F) (map observation_octet_row rows)=
    data_list_term (map keyed_set_row_term
      (map (map_prod keyed_octet_pair (map keyed_octet_pair)) (observation_loss_table_list C F rows)))"
  by (simp only: list_product_map_fields map_map comp_def fst_map_prod snd_map_prod
      observation_losses_list_map[OF observation_octet_injective observation_octet_injective observation_octet_injective])
    (simp add: map_map comp_def case_prod_unfold)

section \<open>Executed equations call the actual complete native operations\<close>

abbreviation observation_table_octet_argument where
  "observation_table_octet_argument C U F rows \<equiv>
    observation_scope_argument (data_list_term (map observation_octet C)) (data_list_term (map observation_octet U))
      (data_list_term (map observation_octet F)) (data_list_term (map observation_row_term (map observation_octet_row rows)))"

abbreviation observation_table_octet_profiles where
  "observation_table_octet_profiles displayed \<equiv>
    data_list_term (map keyed_set_row_term (map (map_prod keyed_octet (map keyed_octet_pair)) displayed))"

abbreviation observation_table_octet_losses where
  "observation_table_octet_losses displayed \<equiv>
    data_list_term (map keyed_set_row_term (map (map_prod keyed_octet_pair (map keyed_octet_pair)) displayed))"

definition observation_octet_profile_table :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    (nat\<times>nat\<times>nat) list \<Rightarrow> (nat\<times>(nat\<times>nat) list) list \<Rightarrow> bool" where
  "observation_octet_profile_table C U F rows displayed \<longleftrightarrow>
    (330,Pair_Term (observation_table_octet_argument C U F rows) (observation_table_octet_profiles displayed))
      \<in>positive_meaning observation_table_system"

definition observation_octet_loss_table :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    (nat\<times>nat\<times>nat) list \<Rightarrow> ((nat\<times>nat)\<times>(nat\<times>nat) list) list \<Rightarrow> bool" where
  "observation_octet_loss_table C U F rows displayed \<longleftrightarrow>
    (335,Pair_Term (observation_table_octet_argument C U F rows) (observation_table_octet_losses displayed))
      \<in>positive_meaning observation_table_system"

lemma observation_octet_profile_table_code [code]:
  "observation_octet_profile_table C U F rows displayed \<longleftrightarrow>
    observation_octet_scope C U F rows \<and> keyed_octet_profiles (observation_profile_table_list C F rows) displayed"
  by (simp only: observation_octet_profile_table_def observation_profile_table_lists
    observation_octet_scope_def observation_scope_encoded observation_profile_table_octet_encoding keyed_octet_profiles_def)

lemma observation_octet_loss_table_code [code]:
  "observation_octet_loss_table C U F rows displayed \<longleftrightarrow>
    observation_octet_scope C U F rows \<and> keyed_octet_losses (observation_loss_table_list C F rows) displayed"
  by (simp only: observation_octet_loss_table_def observation_loss_table_lists
    observation_octet_scope_def observation_scope_encoded observation_loss_table_octet_encoding keyed_octet_losses_def)

export_code observation_octet_profile_table observation_octet_loss_table nat_of_integer integer_of_nat
  in SML module_name Native_Observation_Tables file_prefix native_observation_tables

text \<open>
  Both exported decisions are actual calls of the complete native table
  operations. Their checked equations compose whole-scope admission,
  the existing profile and loss computations, and complete nested-set
  comparison. The computed witnesses enumerate every declared key.
  The supplied result retains both levels of presentation freedom.
  Octet encodings provide a finite execution interface; the complete
  contracts apply to arbitrary admitted data terms.
\<close>

end
