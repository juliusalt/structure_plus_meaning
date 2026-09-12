theory Factor_Table_Maps
  imports Factor_Related_List_Maps Factor_Table_Admission_Profiles
    Factor_Product_Contracts Presentation_Function_Witnesses
begin

section \<open>Value maps retain keys without requiring injective values\<close>

lemma single_valued_value_image:
  assumes "single_valued Q"
  shows "single_valued (map_prod id f ` Q)"
  using assms by (auto simp: single_valued_def; blast)

lemma value_map_injective_on_functional_relation:
  assumes "single_valued Q"
  shows "inj_on (map_prod id f) Q"
  using assms by (auto simp: inj_on_def single_valued_def; blast)

lemma value_image_domain:
  "rel_dom (map_prod id f ` Q)=rel_dom Q"
proof (rule set_eqI)
  fix k
  show "k\<in>rel_dom (map_prod id f ` Q) \<longleftrightarrow> k\<in>rel_dom Q"
  proof
    assume "k\<in>rel_dom (map_prod id f ` Q)"
    then show "k\<in>rel_dom Q" by (auto simp: rel_dom_def)
  next
    assume "k\<in>rel_dom Q"
    then obtain v where member: "(k,v)\<in>Q" by (auto simp: rel_dom_def)
    have "(k,f v)\<in>map_prod id f ` Q" using imageI[OF member, of "map_prod id f"] by simp
    then show "k\<in>rel_dom (map_prod id f ` Q)" by (auto simp: rel_dom_def)
  qed
qed

lemma functional_rows_map:
  assumes "distinct xs" "single_valued (set xs)"
  shows "distinct (map (map_prod id f) xs)"
    "single_valued (set (map (map_prod id f) xs))"
  using value_map_injective_on_functional_relation[OF assms(2), of f]
    single_valued_value_image[OF assms(2), of f] assms(1)
  by (simp_all add: distinct_map)

abbreviation table_sequence_domain ::
  "('k\<Rightarrow>bool) \<Rightarrow> ('v\<Rightarrow>bool) \<Rightarrow> ('k\<times>'v) list \<Rightarrow> bool" where
  "table_sequence_domain D E xs \<equiv>
    distinct xs \<and> single_valued (set xs) \<and> (\<forall>z\<in>set xs. D (fst z) \<and> E (snd z))"

lemma table_sequence_coverage:
  "finite_table_domain D E Q \<longleftrightarrow>
    (\<exists>xs. table_sequence_domain D E xs \<and> set xs=Q)"
  using finite_distinct_list by auto

lemma data_table_sequence_image:
  assumes keys: "presentation_class K D A" and "values": "presentation_class V E B"
  shows "(\<exists>xs. table_sequence_domain D E xs \<and>
      data_sequence_presents (factor_pair_presents K V) xs p \<and> set xs=Q)
    \<longleftrightarrow> data_table_presents K V Q p"
proof -
  have rows: "presentation_class (data_sequence_presents (factor_pair_presents K V))
      (\<lambda>xs. \<forall>z\<in>set xs. D (fst z) \<and> E (snd z))
      (\<lambda>p. \<exists>ps. (\<forall>t\<in>set ps. \<exists>a b. A a \<and> B b \<and> t=Pair_Term a b) \<and>
        p=data_list_term ps)"
    by (rule data_sequence_presentation_class[OF factor_pair_class[OF keys "values"]])
  show ?thesis using presentation_class.subject_boundary[OF rows]
    by (auto simp: data_table_presents_def data_collection_presents_def data_sequence_presents_def; blast)
qed

section \<open>The existing key reader checks the complete supplied sequence\<close>

lemma encoded_table_sequence_keys:
  assumes read: "data_sequence_presents R xs p" and injective: "inj encode"
    and shape: "\<And>z t. R z t \<Longrightarrow> \<exists>v. t=Pair_Term (encode (fst z)) v"
    and formed: "\<And>z t. R z t \<Longrightarrow> term_formed t \<and> self_contained_term (encode (fst z))"
  shows "(21,p)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    distinct xs \<and> single_valued (set xs)"
proof -
  obtain ts where listed: "list_all2 R xs ts" and encoded: "p=data_list_term ts"
    using read by (auto simp: data_sequence_presents_def)
  have terms: "\<forall>t\<in>set ts. term_formed t"
    and keys: "\<forall>z\<in>set xs. self_contained_term (encode (fst z))"
    using listed by (induction xs arbitrary: ts) (auto simp: list_all2_Cons1 dest: formed)+
  show ?thesis using keyed_list_encoded_keys_formed[OF listed terms keys injective shape]
    by (simp only: encoded)
qed

section \<open>Table mapping is a commuting image of sequence mapping\<close>

theorem table_value_mapping_witness:
  assumes keys: "presentation_class K D AK"
    and inputs: "presentation_class V E AV" and outputs: "presentation_class W F AW"
    and sequence: "presented_function_contract (data_sequence_presents (factor_pair_presents K V))
      (\<lambda>xs. \<forall>z\<in>set xs. D (fst z) \<and> E (snd z)) A
      (data_sequence_presents (factor_pair_presents K W))
      (\<lambda>ys. \<forall>z\<in>set ys. D (fst z) \<and> F (snd z)) B
      (map (map_prod id f)) run"
    and guard: "\<And>xs p. data_sequence_presents (factor_pair_presents K V) xs p \<Longrightarrow>
      (check_keys p \<longleftrightarrow> distinct xs \<and> single_valued (set xs))"
  shows "presented_function_witness (data_table_presents K V) (finite_table_domain D E)
    (\<lambda>p. \<exists>Q. data_table_presents K V Q p)
    (data_table_presents K W) (finite_table_domain D F)
    (\<lambda>q. \<exists>Q. data_table_presents K W Q q)
    (\<lambda>Q. map_prod id f ` Q) (\<lambda>p q. check_keys p \<and> run p q)"
proof -
  interpret sequence: presented_function_contract "data_sequence_presents (factor_pair_presents K V)"
    "\<lambda>xs. \<forall>z\<in>set xs. D (fst z) \<and> E (snd z)" A
    "data_sequence_presents (factor_pair_presents K W)"
    "\<lambda>ys. \<forall>z\<in>set ys. D (fst z) \<and> F (snd z)" B
    "map (map_prod id f)" run by (rule sequence)
  interpret sequence_witness: presented_function_witness
    "data_sequence_presents (factor_pair_presents K V)"
    "\<lambda>xs. \<forall>z\<in>set xs. D (fst z) \<and> E (snd z)" A
    "data_sequence_presents (factor_pair_presents K W)"
    "\<lambda>ys. \<forall>z\<in>set ys. D (fst z) \<and> F (snd z)" B
    "map (map_prod id f)" run by (rule sequence.witness)
  let ?R="data_sequence_presents (factor_pair_presents K V)"
  let ?S="data_sequence_presents (factor_pair_presents K W)"
  let ?I="table_sequence_domain D E"
  let ?J="table_sequence_domain D F"
  let ?admit="presented_predicate ?R ?I"
  let ?result="presented_predicate ?S ?J"
  let ?run="\<lambda>p q. ?admit p \<and> run p q"
  interpret restricted: presented_function_witness "\<lambda>xs p. ?I xs \<and> ?R xs p" ?I ?admit
    ?S "\<lambda>ys. \<forall>z\<in>set ys. D (fst z) \<and> F (snd z)" B "map (map_prod id f)" ?run
    by (rule sequence_witness.specialization) simp
  have image: "?J (map (map_prod id f) xs)" if "?I xs" for xs
    using functional_rows_map[of xs f] sequence.image_boundary[of xs] that by blast
  interpret tables: presented_function_witness "\<lambda>xs p. ?I xs \<and> ?R xs p" ?I ?admit
    "\<lambda>ys q. ?J ys \<and> ?S ys q" ?J ?result "map (map_prod id f)" ?run
    by (rule restricted.output_restriction) (use image in auto)
  have projected: "presented_function_witness
      (\<lambda>Q p. \<exists>xs. (?I xs \<and> ?R xs p) \<and> set xs=Q) (finite_table_domain D E) ?admit
      (\<lambda>Q q. \<exists>ys. (?J ys \<and> ?S ys q) \<and> set ys=Q) (finite_table_domain D F) ?result
      (\<lambda>Q. map_prod id f ` Q) ?run"
    by (rule tables.images[where h=set and k=set])
      (auto simp only: table_sequence_coverage set_map)
  have left_read: "(\<lambda>Q p. \<exists>xs. (?I xs \<and> ?R xs p) \<and> set xs=Q)=data_table_presents K V"
    by (intro ext) (use data_table_sequence_image[OF keys inputs] in blast)
  have right_read: "(\<lambda>Q q. \<exists>ys. (?J ys \<and> ?S ys q) \<and> set ys=Q)=data_table_presents K W"
    by (intro ext) (use data_table_sequence_image[OF keys outputs] in blast)
  have left_admission: "?admit=(\<lambda>p. \<exists>Q. data_table_presents K V Q p)"
    by (intro ext) (simp only: left_read[symmetric] presented_predicate_def; blast)
  have right_admission: "?result=(\<lambda>q. \<exists>Q. data_table_presents K W Q q)"
    by (intro ext) (simp only: right_read[symmetric] presented_predicate_def; blast)
  have admitted_guard: "?admit p \<longleftrightarrow> check_keys p \<and> A p" for p
  proof
    assume "?admit p"
    then obtain xs where read: "?R xs p" and domain: "?I xs" by (auto simp only: presented_predicate_def)
    have checked: "check_keys p" using guard[OF read] domain by blast
    have allowed: "A p" by (rule sequence.left.presentation_boundary[OF read])
    show "check_keys p \<and> A p" using checked allowed by blast
  next
    assume accepted: "check_keys p \<and> A p"
    obtain xs where read: "?R xs p" using sequence.left.admitted accepted by blast
    have formed: "\<forall>z\<in>set xs. D (fst z) \<and> E (snd z)"
      by (rule sequence.left.subject_boundary[OF read])
    have domain: "?I xs" using accepted guard[OF read] formed by blast
    show "?admit p" using domain read by (auto simp only: presented_predicate_def)
  qed
  have operation: "?run=(\<lambda>p q. check_keys p \<and> run p q)"
    by (intro ext) (use sequence.boundaries in \<open>auto simp only: admitted_guard\<close>)
  show ?thesis using projected[unfolded operation]
    by (simp only: left_read right_read left_admission right_admission)
qed

text \<open>
  A value map keeps each actual key. Functionality makes the row map injective
  on that relation even when different values have the same image. Hence
  distinct keyed occurrences survive and the mapped relation stays functional.

  The operation first restricts the complete sequence contract by key
  uniqueness. Its output already satisfies the same condition. Taking the set
  image on both sides commutes with mapping values, so the general witness
  theorem supplies the table contract. No consumer repeats the traversal's
  recursive proof or imposes injectivity on artifact material.

  Both table classes contain every permitted row order and component form.
  The particular traversal still preserves its supplied row order. A complete
  downstream test can consume any returned table through the general witness
  contract; claiming every possible raw output from this traversal would be
  stronger and is not a consequence of these theorems.
\<close>

end
