theory Factor_Keyed_Set_Execution
  imports Factor_Keyed_Set_Encodings
begin

section \<open>Finite interfaces call the actual compiled collection comparison\<close>

abbreviation keyed_octet :: "nat \<Rightarrow> factor_term" where
  "keyed_octet n \<equiv> Payload_Term [n]"

abbreviation keyed_octet_pair :: "(nat\<times>nat) \<Rightarrow> factor_term" where
  "keyed_octet_pair z \<equiv> Pair_Term (keyed_octet (fst z)) (keyed_octet (snd z))"

lemma keyed_octet_injective: "inj keyed_octet"
  by (auto simp: inj_on_def)

lemma keyed_octet_pair_injective: "inj keyed_octet_pair"
  by (auto simp: inj_on_def prod_eq_iff)

definition keyed_octet_sets :: "(nat\<times>nat list) list \<Rightarrow> (nat\<times>nat list) list \<Rightarrow> bool" where
  "keyed_octet_sets xs ys \<longleftrightarrow> (317,Pair_Term
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet (map keyed_octet)) xs)))
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet (map keyed_octet)) ys))))
      \<in>positive_meaning keyed_set_system"

lemma keyed_octet_sets_code [code]:
  "keyed_octet_sets xs ys \<longleftrightarrow>
    list_all (\<lambda>(k,vs). k<256 \<and> list_all (\<lambda>v. v<256) vs) xs \<and>
    list_all (\<lambda>(k,vs). k<256 \<and> list_all (\<lambda>v. v<256) vs) ys \<and>
    keyed_list_subject xs=keyed_list_subject ys"
  unfolding keyed_octet_sets_def
  by (subst keyed_sets_encoded_rows[OF keyed_octet_injective keyed_octet_injective])
    (simp add: list_all_iff case_prod_unfold octets_formed_def)

definition keyed_octet_profiles :: "(nat\<times>(nat\<times>nat) list) list \<Rightarrow>
    (nat\<times>(nat\<times>nat) list) list \<Rightarrow> bool" where
  "keyed_octet_profiles xs ys \<longleftrightarrow> (317,Pair_Term
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet (map keyed_octet_pair)) xs)))
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet (map keyed_octet_pair)) ys))))
      \<in>positive_meaning keyed_set_system"

lemma keyed_octet_profiles_code [code]:
  "keyed_octet_profiles xs ys \<longleftrightarrow>
    list_all (\<lambda>(k,vs). k<256 \<and> list_all (\<lambda>(f,w). f<256 \<and> w<256) vs) xs \<and>
    list_all (\<lambda>(k,vs). k<256 \<and> list_all (\<lambda>(f,w). f<256 \<and> w<256) vs) ys \<and>
    keyed_list_subject xs=keyed_list_subject ys"
  unfolding keyed_octet_profiles_def
  by (subst keyed_sets_encoded_rows[OF keyed_octet_injective keyed_octet_pair_injective])
    (simp add: list_all_iff case_prod_unfold octets_formed_def)

definition keyed_octet_losses :: "((nat\<times>nat)\<times>(nat\<times>nat) list) list \<Rightarrow>
    ((nat\<times>nat)\<times>(nat\<times>nat) list) list \<Rightarrow> bool" where
  "keyed_octet_losses xs ys \<longleftrightarrow> (317,Pair_Term
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet_pair (map keyed_octet_pair)) xs)))
    (data_list_term (map keyed_set_row_term (map (map_prod keyed_octet_pair (map keyed_octet_pair)) ys))))
      \<in>positive_meaning keyed_set_system"

lemma keyed_octet_losses_code [code]:
  "keyed_octet_losses xs ys \<longleftrightarrow>
    list_all (\<lambda>((c,d),vs). c<256 \<and> d<256 \<and> list_all (\<lambda>(f,w). f<256 \<and> w<256) vs) xs \<and>
    list_all (\<lambda>((c,d),vs). c<256 \<and> d<256 \<and> list_all (\<lambda>(f,w). f<256 \<and> w<256) vs) ys \<and>
    keyed_list_subject xs=keyed_list_subject ys"
  unfolding keyed_octet_losses_def
  by (subst keyed_sets_encoded_rows[OF keyed_octet_pair_injective keyed_octet_pair_injective])
    (simp add: list_all_iff case_prod_unfold octets_formed_def)

section \<open>Formed references remain different from self-contained data\<close>

abbreviation keyed_reference where
  "keyed_reference \<equiv> Target_Term (Whole_Artifact empty_artifact)"

abbreviation keyed_reference_source where
  "keyed_reference_source n \<equiv> if n=7 then [] else
    [(if n=0 then keyed_reference else keyed_octet 0,
      if n=1 then [keyed_reference] else [keyed_octet 0,keyed_octet 1])]"

abbreviation keyed_reference_target where
  "keyed_reference_target n \<equiv> if n=7 then [] else
    (if n=9 then [(keyed_octet 0,[keyed_octet 1,keyed_octet 0]),
        (keyed_octet 0,[keyed_octet 0,keyed_octet 1,keyed_octet 0])]
      else [(if n=2 then keyed_reference else keyed_octet 0,
        if n=3 then [keyed_reference] else if n=8 then [keyed_octet 0] else [keyed_octet 0,keyed_octet 1])]) @
      (if n=4 then [(keyed_reference,[])] else if n=5 then [(keyed_octet 0,[keyed_reference])] else [])"

abbreviation keyed_reference_argument where
  "keyed_reference_argument n \<equiv> Pair_Term
    (data_list_term (map keyed_set_row_term (keyed_reference_source n)))
    (data_list_term (map keyed_set_row_term (keyed_reference_target n)))"

definition keyed_reference_call_formed :: "nat \<Rightarrow> bool" where
  "keyed_reference_call_formed n \<longleftrightarrow> schema_call_formed keyed_set_system 317 (keyed_reference_argument n)"

lemma keyed_reference_call_formed_code [code]: "keyed_reference_call_formed n=True"
  by (simp add: keyed_reference_call_formed_def keyed_set_call data_list_term_formed octets_formed_def split: if_splits)

definition keyed_reference_decision :: "nat \<Rightarrow> bool" where
  "keyed_reference_decision n \<longleftrightarrow> (317,keyed_reference_argument n)\<in>positive_meaning keyed_set_system"

lemma keyed_reference_decision_code [code]:
  "keyed_reference_decision n \<longleftrightarrow> 6\<le>n \<and> n\<noteq>8"
  unfolding keyed_reference_decision_def
  by (subst keyed_sets_row_lists)
    (simp add: octets_formed_def finsert_commute split: if_splits; auto simp: fset_eq_iff)

export_code keyed_octet_sets keyed_octet_profiles keyed_octet_losses keyed_reference_decision keyed_reference_call_formed
  nat_of_integer integer_of_nat in SML module_name Native_Keyed_Sets file_prefix native_keyed_sets

end
