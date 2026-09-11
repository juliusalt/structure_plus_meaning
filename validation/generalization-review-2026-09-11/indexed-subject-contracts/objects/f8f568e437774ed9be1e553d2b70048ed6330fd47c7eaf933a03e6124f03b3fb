theory Factor_Assembly_Folds
  imports Factor_Assembly_Transport
begin

section \<open>Appending the four fields specializes the existing list fold\<close>

abbreviation artifact_list_fields ::
  "factor_term list \<Rightarrow> factor_term list \<Rightarrow> factor_term list \<Rightarrow> factor_term list \<Rightarrow> factor_term" where
  "artifact_list_fields A E B F \<equiv>
    artifact_fields_term (data_list_term A) (data_list_term E) (data_list_term B) (data_list_term F)"

theorem assembly_fields_append_at:
  "(228,collection_join_argument (artifact_list_fields A E B F) (artifact_list_fields A' E' B' F') t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    data_elements A \<and> data_elements E \<and> data_elements B \<and> data_elements F \<and>
    data_elements A' \<and> data_elements E' \<and> data_elements B' \<and> data_elements F' \<and>
    t=artifact_list_fields (A@A') (E@E') (B@B') (F@F')"
  by (auto simp: assembly_fields_append_calls assembly_append_meaning data_append_at_lists)

lemma assembly_fields_append_from_state:
  assumes "data_elements A'" "data_elements E'" "data_elements B'" "data_elements F'"
  shows "(228,collection_join_argument p (artifact_list_fields A' E' B' F') t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>A E B F. data_elements A \<and> data_elements E \<and> data_elements B \<and> data_elements F \<and>
      p=artifact_list_fields A E B F \<and> t=artifact_list_fields (A@A') (E@E') (B@B') (F@F'))"
  using assms by (auto simp: assembly_fields_append_calls assembly_append_meaning
    data_append_exact data_list_term_injective)

theorem assembly_fields_fold_lists:
  assumes data: "\<forall>i\<in>set is. data_elements (A i) \<and> data_elements (E i) \<and> data_elements (B i) \<and> data_elements (F i)"
  shows "(229,collection_join_argument (artifact_list_fields [] [] [] [])
      (data_list_term (map (\<lambda>i. artifact_list_fields (A i) (E i) (B i) (F i)) is)) t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    t=artifact_list_fields (concat (map A is)) (concat (map E is)) (concat (map B is)) (concat (map F is))"
proof -
  let ?D="\<lambda>(a,e,b,f). data_elements a \<and> data_elements e \<and> data_elements b \<and> data_elements f"
  let ?encode="\<lambda>(a,e,b,f). artifact_list_fields a e b f"
  let ?append="\<lambda>(a,e,b,f) (a',e',b',f'). (a@a',e@e',b@b',f@f')"
  let ?seed="([],[],[],[])"
  let ?xs="map (\<lambda>i. (A i,E i,B i,F i)) is"
  have element: "(228,collection_join_argument p (?encode a) q)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      (\<exists>x. ?D x \<and> p=?encode x \<and> q=?encode (?append x a))"
    if "?D a" for a p q
    using that by (cases a) (auto simp: assembly_fields_append_from_state split: prod.splits)
  have folded: "(229,collection_join_argument (?encode ?seed) p q)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      (\<exists>xs. (\<forall>x\<in>set xs. ?D x) \<and> p=data_list_term (map ?encode xs) \<and> q=?encode (foldr ?append xs ?seed))"
    for p q
    by (rule assembly_fields_fold.encoded[where E="?D" and D="?D" and f="?append" and h="?encode" and g="?encode" and z="?seed"])
      (use element in \<open>auto simp: data_list_term_formed octets_formed_def split: prod.splits\<close>)
  have injective: "inj ?encode"
    by (rule injI) (auto simp: case_prod_unfold data_list_term_injective intro!: prod_eqI)
  have domain: "\<forall>x\<in>set ?xs. ?D x" using data by auto
  have whole: "foldr ?append ?xs ?seed=
      (concat (map A is),concat (map E is),concat (map B is),concat (map F is))"
    by (induction "is") auto
  have actual: "map ?encode ?xs=map (\<lambda>i. artifact_list_fields (A i) (E i) (B i) (F i)) is"
    by (simp add: map_map comp_def)
  have fixed_input: "(229,collection_join_argument (?encode ?seed)
      (data_list_term (map ?encode ?xs)) t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      t=?encode (foldr ?append ?xs ?seed)"
    using data by (simp only: folded data_list_term_injective inj_map_eq_map[OF injective]; auto)
  show ?thesis using fixed_input by (simp add: whole actual map_map comp_def)
qed

theorem assembly_piece_list_fold:
  assumes source: "origin_table_presents payload_value_presents q p"
    and enumeration: "piece_family_enumeration P ss A E B F"
    and slots: "\<forall>s\<in>set ss. octets_formed s"
    and mapped: "(227,context_relation_argument p
      (pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)) parts)
      \<in>positive_meaning assembly_checking_system"
  shows "(229,collection_join_argument (artifact_list_fields [] [] [] []) parts t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    t=artifact_list_fields
      (map address_pair_data (tagged_atom_list ss A))
      (map incidence_data (map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x)) (tagged_incidence_list ss E)))
      (map address_pair_data (pushed_attachment_list (rel_value q) (tagged_attachment_list ss B)))
      (map address_pair_data (pushed_attachment_list (rel_value q) (tagged_attachment_list ss F)))"
proof -
  let ?a="\<lambda>s. map (\<lambda>a. address_pair_data (s,a)) (A s)"
  let ?e="\<lambda>s. map (\<lambda>z. incidence_data
      (rel_value q (s,fst z),rel_value q (s,fst (snd z)),rel_value q (s,snd (snd z)))) (E s)"
  let ?b="\<lambda>s. map (\<lambda>z. address_pair_data (rel_value q (s,fst z),snd z)) (B s)"
  let ?f="\<lambda>s. map (\<lambda>z. address_pair_data (rel_value q (s,fst z),snd z)) (F s)"
  have actual: "parts=data_list_term (map (\<lambda>s. artifact_list_fields (?a s) (?e s) (?b s) (?f s)) ss)"
    using mapped by (simp only: assembly_piece_list_at[OF source enumeration slots]; blast)
  have formed: "term_formed parts"
    using positive_meaning_formed[OF mapped] schema_call_formed_target by fastforce
  have data: "\<forall>s\<in>set ss. data_elements (?a s) \<and> data_elements (?e s) \<and>
      data_elements (?b s) \<and> data_elements (?f s)"
    using formed by (auto simp: actual data_list_term_formed address_pair_data_def incidence_data_def)
  have folded: "(229,collection_join_argument (artifact_list_fields [] [] [] []) parts t)
      \<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      t=artifact_list_fields (concat (map ?a ss)) (concat (map ?e ss)) (concat (map ?b ss)) (concat (map ?f ss))"
    using assembly_fields_fold_lists[OF data, of t] by (simp only: actual)
  show ?thesis by (simp only: folded map_concat map_map comp_def case_prod_unfold fst_conv snd_conv)
qed

text \<open>
  The four-field operation is a fixed product of the existing append calls.
  The general relational fold accounts for every recursive step; its encoded
  specialization leaves only componentwise append closure and the ordinary
  list equation. No native recursion is re-proved here.

  The fold retains the supplied outer order and every inner occurrence.
  Its seed fixes all four empty fields. The fields at this stage are lists;
  their later set or bag comparisons determine how assembly observes them.
\<close>

end
