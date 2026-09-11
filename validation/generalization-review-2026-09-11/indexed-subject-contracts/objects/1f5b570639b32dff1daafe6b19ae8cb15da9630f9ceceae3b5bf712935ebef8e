theory Factor_Observation_Table_Witnesses
  imports Factor_Observation_Table_Equations Factor_Scope_Computation_Contracts
begin

section \<open>The original complete scope controls both table computations\<close>

lemma observation_table_admission:
  "(311,p)\<in>positive_meaning observation_table_system \<longleftrightarrow> (\<exists>z. observation_scope_presents z p)"
  by (simp only: observation_table_components observation_scope_presented presented_predicate_def; blast)

lemma observation_profile_table_ordered:
  "(329,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) q)\<in>positive_meaning observation_table_system
    \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      q=observation_profile_table_term cs fs rows"
proof (cases "observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows)")
  case True
  note fields=observation_scope_subject_list_data[OF True]
  have formed_us: "term_formed (data_list_term us)" using fields(2) by (auto simp: data_list_term_formed)
  have mapped: "(327,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows))) (data_list_term cs) q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow> q=observation_profile_table_term cs fs rows"
    using observation_table_profile_map_lists[OF fields(3,4), of cs q] fields(1) by blast
  show ?thesis by (simp only: observation_table_profile_admitted.at_input observation_table_components
      observation_scope_encoded True observation_profile_table_raw formed_us mapped simp_thms)
next
  case False
  show ?thesis by (simp only: observation_table_profile_admitted.at_input observation_table_components
    observation_scope_encoded False simp_thms)
qed

lemma observation_loss_table_ordered:
  "(334,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) q)\<in>positive_meaning observation_table_system
    \<longleftrightarrow> observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows) \<and>
      q=observation_loss_table_term cs fs rows"
proof (cases "observation_scope_subject_formed (fset_of_list cs) (fset_of_list us) (fset_of_list fs) (fset_of_list rows)")
  case True
  note fields=observation_scope_subject_list_data[OF True]
  have formed_us: "term_formed (data_list_term us)" using fields(2) by (auto simp: data_list_term_formed)
  have product: "(324,context_relation_argument (data_list_term cs) (data_list_term cs) keys)
      \<in>positive_meaning observation_table_system \<longleftrightarrow>
      keys=data_list_term (map observation_value_term (List.product cs cs))" for keys
    using fields(1) by (simp only: observation_table_components data_product_ordered_lists observation_table_candidate_product; blast)
  have pair_data: "\<forall>(c,d)\<in>set (List.product cs cs). data_elements [c,d]"
    using fields(1) by (auto simp: set_product)
  have mapped: "(332,context_relation_argument
      (Pair_Term (data_list_term fs) (data_list_term (map observation_row_term rows)))
      (data_list_term (map observation_value_term (List.product cs cs))) q)
      \<in>positive_meaning observation_table_system \<longleftrightarrow> q=observation_loss_table_term cs fs rows"
    by (rule observation_table_loss_map_lists[OF fields(3,4) pair_data])
  have raw: "(333,Pair_Term (observation_scope_argument (data_list_term cs) (data_list_term us)
      (data_list_term fs) (data_list_term (map observation_row_term rows))) q)\<in>positive_meaning observation_table_system
      \<longleftrightarrow> q=observation_loss_table_term cs fs rows"
    by (simp only: observation_loss_table_raw product formed_us simp_thms; simp only: mapped)
  show ?thesis by (simp only: observation_table_loss_admitted.at_input observation_table_components
      observation_scope_encoded True raw simp_thms)
next
  case False
  show ?thesis by (simp only: observation_table_loss_admitted.at_input observation_table_components
    observation_scope_encoded False simp_thms)
qed

section \<open>Each ordered witness presents the complete finite graph\<close>

lemma observation_profile_table_computed_presents:
  assumes keys: "data_elements cs" and rows: "observation_rows_data rows"
  shows "observation_profile_rows_presents
    (finite_profile_table (fset_of_list cs) (fset_of_list fs) (fset_of_list rows)) (observation_profile_table_term cs fs rows)"
proof -
  have key_reads: "observation_datum_presents c (id c)" if "c\<in>set cs" for c
    using keys that by simp
  have value_reads: "observation_values_presents
      (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c)
      (data_list_term (map observation_value_term (observation_profile_list fs rows c)))" for c
    by (rule observation_profile_computed_presents[OF rows])
  show ?thesis unfolding finite_profile_table_enumeration
    using factor_keyed_fset_enumeration[where K=observation_datum_presents and R=observation_values_presents
      and xs=cs and h=id and f="finite_candidate_profile (fset_of_list fs) (fset_of_list rows)"
      and g="\<lambda>c. data_list_term (map observation_value_term (observation_profile_list fs rows c))",
      OF key_reads value_reads] by (simp only: id_apply)
qed

lemma observation_loss_table_computed_presents:
  assumes keys: "data_elements cs" and rows: "observation_rows_data rows"
  shows "observation_loss_rows_presents
    (finite_loss_table (fset_of_list cs) (fset_of_list fs) (fset_of_list rows)) (observation_loss_table_term cs fs rows)"
proof -
  have key_reads: "observation_value_presents z (observation_value_term z)" if "z\<in>set (List.product cs cs)" for z
    using keys that by (cases z) (auto simp: observation_value_graph set_product)
  have value_reads: "observation_values_presents
      (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) (fst z) (snd z))
      (data_list_term (map observation_value_term (observation_losses_list fs rows (fst z) (snd z))))" for z
    by (rule observation_losses_computed_presents[OF rows])
  show ?thesis unfolding finite_loss_table_enumeration
    using factor_keyed_fset_enumeration[where K=observation_value_presents and R=observation_values_presents
      and xs="List.product cs cs" and h=observation_value_term
      and f="\<lambda>z. finite_candidate_losses (fset_of_list fs) (fset_of_list rows) (fst z) (snd z)"
      and g="\<lambda>z. data_list_term (map observation_value_term (observation_losses_list fs rows (fst z) (snd z)))",
      OF key_reads value_reads] by (simp add: case_prod_unfold)
qed

section \<open>Both computations instantiate the shared scope-witness contract\<close>

abbreviation observation_profile_table_subject where
  "observation_profile_table_subject z \<equiv>
    finite_profile_table (fst (fst z)) (snd (snd (fst z))) (snd z)"

abbreviation observation_loss_table_subject where
  "observation_loss_table_subject z \<equiv>
    finite_loss_table (fst (fst z)) (snd (snd (fst z))) (snd z)"

theorem observation_profile_table_witness:
  "presented_function_witness observation_scope_presents observation_scope_domain
    (\<lambda>p. \<exists>z. observation_scope_presents z p)
    observation_profile_rows_presents (observation_keyed_rows_domain observation_datum)
    (\<lambda>q. \<exists>S. observation_profile_rows_presents S q) observation_profile_table_subject
    (\<lambda>p q. (329,Pair_Term p q)\<in>positive_meaning observation_table_system)"
proof -
  have boundary: "(311,p)\<in>positive_meaning observation_scope_system"
    if "(329,Pair_Term p q)\<in>positive_meaning observation_table_system" for p q
    using that by (simp only: observation_table_profile_admitted.at_input observation_table_components; blast)
  have returned: "observation_profile_rows_presents
      (observation_profile_table_subject ((fset_of_list cs,(fset_of_list us,fset_of_list fs)),fset_of_list rows))
      (observation_profile_table_term cs fs rows)"
    if "data_elements cs" "data_elements us" "data_elements fs" "observation_rows_data rows" for cs us fs rows
    by (simp only: fst_conv snd_conv; rule observation_profile_table_computed_presents[OF that(1,4)])
  show ?thesis by (rule observation_scope_computed_witness[
    where S=observation_profile_rows_presents and E="observation_keyed_rows_domain observation_datum"
      and B="\<lambda>q. \<exists>S. observation_profile_rows_presents S q" and f=observation_profile_table_subject
      and operation="\<lambda>p q. (329,Pair_Term p q)\<in>positive_meaning observation_table_system"
      and h="\<lambda>cs us fs rows. observation_profile_table_term cs fs rows",
    OF observation_profile_rows_class boundary observation_profile_table_ordered returned])
qed

theorem observation_loss_table_witness:
  "presented_function_witness observation_scope_presents observation_scope_domain
    (\<lambda>p. \<exists>z. observation_scope_presents z p)
    observation_loss_rows_presents (observation_keyed_rows_domain (\<lambda>(c,d). data_elements [c,d]))
    (\<lambda>q. \<exists>S. observation_loss_rows_presents S q) observation_loss_table_subject
    (\<lambda>p q. (334,Pair_Term p q)\<in>positive_meaning observation_table_system)"
proof -
  have boundary: "(311,p)\<in>positive_meaning observation_scope_system"
    if "(334,Pair_Term p q)\<in>positive_meaning observation_table_system" for p q
    using that by (simp only: observation_table_loss_admitted.at_input observation_table_components; blast)
  have returned: "observation_loss_rows_presents
      (observation_loss_table_subject ((fset_of_list cs,(fset_of_list us,fset_of_list fs)),fset_of_list rows))
      (observation_loss_table_term cs fs rows)"
    if "data_elements cs" "data_elements us" "data_elements fs" "observation_rows_data rows" for cs us fs rows
    by (simp only: fst_conv snd_conv; rule observation_loss_table_computed_presents[OF that(1,4)])
  show ?thesis by (rule observation_scope_computed_witness[
    where S=observation_loss_rows_presents and E="observation_keyed_rows_domain (\<lambda>(c,d). data_elements [c,d])"
      and B="\<lambda>q. \<exists>S. observation_loss_rows_presents S q" and f=observation_loss_table_subject
      and operation="\<lambda>p q. (334,Pair_Term p q)\<in>positive_meaning observation_table_system"
      and h="\<lambda>cs us fs rows. observation_loss_table_term cs fs rows",
    OF observation_loss_rows_class boundary observation_loss_table_ordered returned])
qed

end
