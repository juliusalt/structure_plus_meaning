theory Factor_Observation_Table_Controls
  imports Factor_Observation_Table_Execution
begin

section \<open>Formed references test every field and empty result admission\<close>

abbreviation observation_table_reference_profile_rows where
  "observation_table_reference_profile_rows n \<equiv> if n=10 then [] else
    [(if n=8 then observation_reference else Payload_Term [],
      if n=9 then [Pair_Term (Payload_Term []) observation_reference] else [])]"

abbreviation observation_table_reference_loss_rows where
  "observation_table_reference_loss_rows n \<equiv> if n=10 then [] else
    [(Pair_Term (Payload_Term []) (if n=8 then observation_reference else Payload_Term []),
      if n=9 then [Pair_Term (Payload_Term []) observation_reference] else [])]"

abbreviation observation_table_reference_profile_argument where
  "observation_table_reference_profile_argument n \<equiv>
    Pair_Term (observation_scope_reference_argument n)
      (data_list_term (map keyed_set_row_term (observation_table_reference_profile_rows n)))"

abbreviation observation_table_reference_loss_argument where
  "observation_table_reference_loss_argument n \<equiv>
    Pair_Term (observation_scope_reference_argument n)
      (data_list_term (map keyed_set_row_term (observation_table_reference_loss_rows n)))"

definition observation_table_reference_formed :: "nat \<Rightarrow> bool" where
  "observation_table_reference_formed n \<longleftrightarrow>
    schema_call_formed observation_table_system 330 (observation_table_reference_profile_argument n) \<and>
    schema_call_formed observation_table_system 335 (observation_table_reference_loss_argument n)"

lemma observation_table_reference_formed_code [code]: "observation_table_reference_formed n=True"
  by (simp add: observation_table_reference_formed_def observation_table_call data_list_term_formed
    octets_formed_def split: if_splits)

definition observation_table_reference_profiles :: "nat \<Rightarrow> bool" where
  "observation_table_reference_profiles n \<longleftrightarrow>
    (330,observation_table_reference_profile_argument n)\<in>positive_meaning observation_table_system"

definition observation_table_reference_losses :: "nat \<Rightarrow> bool" where
  "observation_table_reference_losses n \<longleftrightarrow>
    (335,observation_table_reference_loss_argument n)\<in>positive_meaning observation_table_system"

lemma observation_table_reference_profiles_code [code]:
  "observation_table_reference_profiles n \<longleftrightarrow> 6\<le>n \<and> n\<noteq>8 \<and> n\<noteq>9 \<and> n\<noteq>10"
proof -
  have computed: "(329,Pair_Term (observation_scope_reference_argument n) w)\<in>positive_meaning observation_table_system
      \<longleftrightarrow> 6\<le>n \<and> w=data_list_term (map keyed_set_row_term [(Payload_Term [],[])])" for w
    by (simp only: observation_profile_table_ordered observation_scope_subject_lists)
      (auto simp: observation_profile_list_def octets_formed_def split: if_splits)
  have compared: "(317,Pair_Term (data_list_term (map keyed_set_row_term [(Payload_Term [],[])]))
      (data_list_term (map keyed_set_row_term (observation_table_reference_profile_rows n))))
      \<in>positive_meaning observation_table_system \<longleftrightarrow> n\<noteq>8 \<and> n\<noteq>9 \<and> n\<noteq>10"
    by (simp only: observation_table_components keyed_sets_row_lists)
      (auto simp: octets_formed_def split: if_splits)
  show ?thesis unfolding observation_table_reference_profiles_def
    using observation_table_profile_comparison.at_computed_result[
      where p="observation_scope_reference_argument n"
        and q="data_list_term (map keyed_set_row_term (observation_table_reference_profile_rows n))"
        and admitted="6\<le>n" and result="data_list_term (map keyed_set_row_term [(Payload_Term [],[])])", OF computed]
    by (simp only: compared)
qed

lemma observation_table_reference_losses_code [code]:
  "observation_table_reference_losses n \<longleftrightarrow> 6\<le>n \<and> n\<noteq>8 \<and> n\<noteq>9 \<and> n\<noteq>10"
proof -
  have computed: "(334,Pair_Term (observation_scope_reference_argument n) w)\<in>positive_meaning observation_table_system
      \<longleftrightarrow> 6\<le>n \<and>
      w=data_list_term (map keyed_set_row_term [(Pair_Term (Payload_Term []) (Payload_Term []),[])])" for w
    by (simp only: observation_loss_table_ordered observation_scope_subject_lists)
      (auto simp: observation_losses_list_def observation_profile_list_def octets_formed_def split: if_splits)
  have compared: "(317,Pair_Term
      (data_list_term (map keyed_set_row_term [(Pair_Term (Payload_Term []) (Payload_Term []),[])]))
      (data_list_term (map keyed_set_row_term (observation_table_reference_loss_rows n))))
      \<in>positive_meaning observation_table_system \<longleftrightarrow> n\<noteq>8 \<and> n\<noteq>9 \<and> n\<noteq>10"
    by (simp only: observation_table_components keyed_sets_row_lists)
      (auto simp: octets_formed_def split: if_splits)
  show ?thesis unfolding observation_table_reference_losses_def
    using observation_table_loss_comparison.at_computed_result[
      where p="observation_scope_reference_argument n"
        and q="data_list_term (map keyed_set_row_term (observation_table_reference_loss_rows n))"
        and admitted="6\<le>n" and result="data_list_term (map keyed_set_row_term [(Pair_Term (Payload_Term []) (Payload_Term []),[])])", OF computed]
    by (simp only: compared)
qed

section \<open>Structured data keys and empty data keys remain distinct\<close>

abbreviation observation_table_structured_candidates where
  "observation_table_structured_candidates \<equiv> [Payload_Term [],Pair_Term (Payload_Term []) (Payload_Term [])]"

abbreviation observation_table_structured_query where
  "observation_table_structured_query \<equiv> observation_scope_argument
    (data_list_term observation_table_structured_candidates) (data_list_term []) (data_list_term [])
      (data_list_term (map observation_row_term []))"

abbreviation observation_table_structured_profile_rows where
  "observation_table_structured_profile_rows missing \<equiv> map (\<lambda>c. (c,[]))
    (if missing then [Pair_Term (Payload_Term []) (Payload_Term [])] else rev observation_table_structured_candidates)"

abbreviation observation_table_structured_loss_rows where
  "observation_table_structured_loss_rows missing \<equiv> map (\<lambda>z. (observation_value_term z,[]))
    (filter (\<lambda>(c,d). \<not>missing \<or> c\<noteq>Payload_Term [] \<or> d\<noteq>Payload_Term [])
      (List.product observation_table_structured_candidates observation_table_structured_candidates))"

definition observation_table_structured_profiles :: "bool \<Rightarrow> bool" where
  "observation_table_structured_profiles missing \<longleftrightarrow>
    (330,Pair_Term observation_table_structured_query
      (data_list_term (map keyed_set_row_term (observation_table_structured_profile_rows missing))))
      \<in>positive_meaning observation_table_system"

definition observation_table_structured_losses :: "bool \<Rightarrow> bool" where
  "observation_table_structured_losses missing \<longleftrightarrow>
    (335,Pair_Term observation_table_structured_query
      (data_list_term (map keyed_set_row_term (observation_table_structured_loss_rows missing))))
      \<in>positive_meaning observation_table_system"

lemma observation_table_structured_profiles_code [code]: "observation_table_structured_profiles missing \<longleftrightarrow> \<not>missing"
proof -
  have witness: "observation_profile_table_term cs [] []=
      data_list_term (map keyed_set_row_term (map (\<lambda>c. (c,[])) cs))" for cs
    by (simp add: observation_profile_list_def map_map comp_def)
  show ?thesis unfolding observation_table_structured_profiles_def
    apply (simp only: observation_profile_table_lists witness keyed_sets_row_lists observation_scope_subject_lists)
    by (cases missing; auto simp: octets_formed_def fset_eq_iff)
qed

lemma observation_table_structured_losses_code [code]: "observation_table_structured_losses missing \<longleftrightarrow> \<not>missing"
proof -
  let ?keys="List.product observation_table_structured_candidates observation_table_structured_candidates"
  let ?rows="map (\<lambda>z. (observation_value_term z,[]::factor_term list)) ?keys"
  have witness: "observation_loss_table_term cs [] []=
      data_list_term (map keyed_set_row_term (map (\<lambda>z. (observation_value_term z,[])) (List.product cs cs)))" for cs
    by (simp add: observation_losses_list_def observation_profile_list_def map_map comp_def)
  have present: "(Pair_Term (Payload_Term []) (Payload_Term []),{||})\<in>fset (keyed_list_subject ?rows)" by simp
  have absent: "(Pair_Term (Payload_Term []) (Payload_Term []),{||})\<notin>
      fset (keyed_list_subject (observation_table_structured_loss_rows True))" by simp
  have different: "keyed_list_subject ?rows\<noteq>keyed_list_subject (observation_table_structured_loss_rows True)"
    using present absent by blast
  have compared: "keyed_list_subject ?rows=keyed_list_subject (observation_table_structured_loss_rows missing) \<longleftrightarrow> \<not>missing"
    using different by (cases missing) simp_all
  show ?thesis unfolding observation_table_structured_losses_def
    by (simp only: observation_loss_table_lists witness keyed_sets_row_lists observation_scope_subject_lists compared)
      (simp add: octets_formed_def)
qed

export_code observation_octet_profile_table observation_octet_loss_table
  observation_table_reference_formed observation_table_reference_profiles observation_table_reference_losses
  observation_table_structured_profiles observation_table_structured_losses nat_of_integer integer_of_nat
  in SML module_name Native_Observation_Tables file_prefix native_observation_tables

end
