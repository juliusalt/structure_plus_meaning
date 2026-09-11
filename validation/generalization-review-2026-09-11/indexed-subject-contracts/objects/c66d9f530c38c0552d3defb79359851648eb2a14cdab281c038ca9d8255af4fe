theory Factor_Keyed_Set_Encodings
  imports Factor_Keyed_Set_Contracts
begin

section \<open>Complete encoded rows expose both finite-set levels\<close>

abbreviation keyed_set_row_term :: "(factor_term\<times>factor_term list) \<Rightarrow> factor_term" where
  "keyed_set_row_term z \<equiv> Pair_Term (fst z) (data_list_term (snd z))"

abbreviation keyed_set_rows_data :: "(factor_term\<times>factor_term list) list \<Rightarrow> bool" where
  "keyed_set_rows_data xs \<equiv> \<forall>z\<in>set xs. data_term_boundary (fst z) \<and> data_elements (snd z)"

abbreviation keyed_list_subject where
  "keyed_list_subject xs \<equiv> fset_of_list (map (map_prod id fset_of_list) xs)"

lemma keyed_set_encoded_data:
  "data_elements (map keyed_set_row_term xs) \<longleftrightarrow> keyed_set_rows_data xs"
  by (auto simp: data_list_term_formed data_list_term_self_contained octets_formed_def)

lemma keyed_set_row_presentation:
  "keyed_set_row_presents (fst z,fset_of_list (snd z)) (keyed_set_row_term z) \<longleftrightarrow>
    data_term_boundary (fst z) \<and> data_elements (snd z)"
  by (simp only: factor_pair_presents_at data_finite_set_at_list simp_thms)

lemma keyed_set_encoded_presentation:
  assumes "keyed_set_rows_data xs"
  shows "keyed_sets_presents (keyed_list_subject xs) (data_list_term (map keyed_set_row_term xs))"
proof -
  have shape: "map_prod id fset_of_list z=(fst z,fset_of_list (snd z))" for z by (cases z) simp
  have rows: "list_all2 keyed_set_row_presents (map (map_prod id fset_of_list) xs) (map keyed_set_row_term xs)"
    using assms by (simp only: list_all2_map1 list_all2_map2 list_all2_same shape keyed_set_row_presentation)
  have sequence: "data_sequence_presents keyed_set_row_presents (map (map_prod id fset_of_list) xs)
      (data_list_term (map keyed_set_row_term xs))"
    using rows by (auto simp only: data_sequence_presents_def)
  show ?thesis by (rule data_list_fset_presents_finite_image[OF sequence])
qed

theorem keyed_sets_row_lists:
  "(317,Pair_Term (data_list_term (map keyed_set_row_term xs)) (data_list_term (map keyed_set_row_term ys)))
      \<in>positive_meaning keyed_set_system \<longleftrightarrow>
    keyed_set_rows_data xs \<and> keyed_set_rows_data ys \<and> keyed_list_subject xs=keyed_list_subject ys"
proof -
  have compared: "(317,Pair_Term (data_list_term (map keyed_set_row_term xs)) (data_list_term (map keyed_set_row_term ys)))
      \<in>positive_meaning keyed_set_system \<longleftrightarrow> keyed_list_subject xs=keyed_list_subject ys"
    if "keyed_set_rows_data xs" "keyed_set_rows_data ys"
    by (rule keyed_sets_contract.at[OF
      keyed_set_encoded_presentation[OF that(1)] keyed_set_encoded_presentation[OF that(2)]])
  have boundary: "keyed_set_rows_data xs \<and> keyed_set_rows_data ys"
    if "(317,Pair_Term (data_list_term (map keyed_set_row_term xs)) (data_list_term (map keyed_set_row_term ys)))
      \<in>positive_meaning keyed_set_system"
    using that by (simp only: keyed_sets.lists keyed_set_encoded_data) blast
  show ?thesis using compared boundary by blast
qed

section \<open>Injective field encodings preserve both finite-set identities\<close>

lemma fset_image_equality:
  assumes "inj f"
  shows "fimage f S=fimage f T \<longleftrightarrow> S=T"
  by (simp only: fset_inject[symmetric] fimage.rep_eq inj_image_eq_iff[OF assms])

lemma keyed_fset_encoding_injective:
  assumes keys: "inj f" and members: "inj g"
  shows "inj (map_prod f (fimage g))"
proof (rule injI)
  fix x y assume same: "map_prod f (fimage g) x=map_prod f (fimage g) y"
  have first: "f (fst x)=f (fst y)" and second: "fimage g (snd x)=fimage g (snd y)"
    using same by (cases x; cases y; auto)+
  have left_equal: "fst x=fst y" by (rule injD[OF keys first])
  have right_equal: "snd x=snd y" using second by (simp only: fset_image_equality[OF members])
  show "x=y" using left_equal right_equal by (simp only: prod_eq_iff)
qed

lemma keyed_list_subject_encoding:
  "keyed_list_subject (map (map_prod f (map g)) xs)=
    fimage (map_prod f (fimage g)) (keyed_list_subject xs)"
proof -
  have rows: "map (map_prod id fset_of_list) (map (map_prod f (map g)) xs)=
      map (map_prod f (fimage g)) (map (map_prod id fset_of_list) xs)"
    by (induction xs) (auto simp: map_prod_def split: prod.splits)
  show ?thesis by (simp only: rows fset_of_list_map)
qed

theorem keyed_sets_encoded_rows:
  assumes keys: "inj f" and members: "inj g"
  shows "(317,Pair_Term
      (data_list_term (map keyed_set_row_term (map (map_prod f (map g)) xs)))
      (data_list_term (map keyed_set_row_term (map (map_prod f (map g)) ys))))
      \<in>positive_meaning keyed_set_system \<longleftrightarrow>
    (\<forall>z\<in>set xs. data_term_boundary (f (fst z)) \<and> (\<forall>v\<in>set (snd z). data_term_boundary (g v))) \<and>
    (\<forall>z\<in>set ys. data_term_boundary (f (fst z)) \<and> (\<forall>v\<in>set (snd z). data_term_boundary (g v))) \<and>
    keyed_list_subject xs=keyed_list_subject ys"
  by (simp only: keyed_sets_row_lists keyed_list_subject_encoding
    fset_image_equality[OF keyed_fset_encoding_injective[OF keys members]])
    (auto simp: map_prod_def split: prod.splits)

text \<open>
  The finite execution interface supplies actual complete encoded rows.
  Their whole data boundary is recovered from the native comparison before
  the two semantic finite-set levels are compared. Injective field maps may
  change coordinates without changing either level of identity. They do
  not choose an order, remove displayed occurrences, or equate two keys.
\<close>

end
