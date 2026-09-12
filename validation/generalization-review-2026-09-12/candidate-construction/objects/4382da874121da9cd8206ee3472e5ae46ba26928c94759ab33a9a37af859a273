theory Factor_Data_Product_Execution
  imports Factor_Data_Product_Contracts
begin

section \<open>Independent injective encodings retain ordered pairs\<close>

abbreviation data_pair_encoding where
  "data_pair_encoding f g z \<equiv> Pair_Term (f (fst z)) (g (snd z))"

lemma data_pair_encoding_injective:
  assumes "inj f" "inj g"
  shows "inj (data_pair_encoding f g)"
  using assms by (auto simp: inj_on_def prod_eq_iff)

lemma data_product_encoded_lists:
  assumes first: "inj f" and second: "inj g"
  shows "(325,context_relation_argument (data_list_term (map g ys)) (data_list_term (map f xs))
      (data_list_term (map (data_pair_encoding f g) zs)))\<in>positive_meaning data_product_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. data_term_boundary (f x)) \<and> (\<forall>y\<in>set ys. data_term_boundary (g y)) \<and>
    (\<forall>z\<in>set zs. data_term_boundary (f (fst z)) \<and> data_term_boundary (g (snd z))) \<and>
    set zs=set xs\<times>set ys"
proof -
  have product: "{Pair_Term x y | x y. x\<in>set (map f xs) \<and> y\<in>set (map g ys)}=
      data_pair_encoding f g ` (set xs\<times>set ys)"
  proof (rule equalityI)
    show "{Pair_Term x y | x y. x\<in>set (map f xs) \<and> y\<in>set (map g ys)}\<subseteq>
        data_pair_encoding f g ` (set xs\<times>set ys)"
    proof
      fix t assume "t\<in>{Pair_Term x y | x y. x\<in>set (map f xs) \<and> y\<in>set (map g ys)}"
      then obtain x y where parts: "t=Pair_Term (f x) (g y)" "x\<in>set xs" "y\<in>set ys" by auto
      show "t\<in>data_pair_encoding f g ` (set xs\<times>set ys)"
        by (rule image_eqI[where x="(x,y)"]) (use parts in auto)
    qed
    show "data_pair_encoding f g ` (set xs\<times>set ys)\<subseteq>
        {Pair_Term x y | x y. x\<in>set (map f xs) \<and> y\<in>set (map g ys)}" by auto
  qed
  have compared: "set (map (data_pair_encoding f g) zs)=
      {Pair_Term x y | x y. x\<in>set (map f xs) \<and> y\<in>set (map g ys)} \<longleftrightarrow>
      set zs=set xs\<times>set ys"
    by (simp only: product; simp only: set_map inj_image_eq_iff[OF data_pair_encoding_injective[OF first second]])
  show ?thesis by (simp only: data_product_lists compared) auto
qed

definition data_product_octets :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat) list \<Rightarrow> bool" where
  "data_product_octets xs ys zs \<longleftrightarrow>
    (325,context_relation_argument (data_list_term (map (\<lambda>n. Payload_Term [n]) ys))
      (data_list_term (map (\<lambda>n. Payload_Term [n]) xs))
      (data_list_term (map (data_pair_encoding (\<lambda>n. Payload_Term [n]) (\<lambda>n. Payload_Term [n])) zs)))
      \<in>positive_meaning data_product_system"

lemma data_product_octets_code [code]:
  "data_product_octets xs ys zs \<longleftrightarrow> list_all (\<lambda>x. x<256) xs \<and> list_all (\<lambda>y. y<256) ys \<and>
    list_all (\<lambda>(x,y). x<256 \<and> y<256) zs \<and> set zs=set xs\<times>set ys"
proof -
  have injective: "inj (\<lambda>n. Payload_Term [n])" by (auto simp: inj_on_def)
  show ?thesis unfolding data_product_octets_def
    by (subst data_product_encoded_lists[OF injective injective])
      (simp add: list_all_iff case_prod_unfold octets_formed_def)
qed

section \<open>Empty inputs retain both complete data boundaries\<close>

abbreviation product_reference where
  "product_reference \<equiv> Target_Term (Whole_Artifact empty_artifact)"

abbreviation product_reference_first where
  "product_reference_first n \<equiv> if n=0 then [product_reference]
    else if n=1 \<or> n=4 then [] else [Payload_Term []]"

abbreviation product_reference_second where
  "product_reference_second n \<equiv> if n=1 then [product_reference]
    else if n=0 \<or> n=4 then [] else [Payload_Term []]"

abbreviation product_reference_output where
  "product_reference_output n \<equiv> if n=2 then [product_reference]
    else if n=3 \<or> n=5 then [Pair_Term (Payload_Term []) (Payload_Term [])] else []"

abbreviation product_reference_argument where
  "product_reference_argument n \<equiv> context_relation_argument
    (data_list_term (product_reference_second n)) (data_list_term (product_reference_first n))
    (data_list_term (product_reference_output n))"

definition data_product_reference_formed :: "nat \<Rightarrow> bool" where
  "data_product_reference_formed n \<longleftrightarrow> schema_call_formed data_product_system 325 (product_reference_argument n)"

lemma data_product_reference_formed_code [code]: "data_product_reference_formed n=True"
  by (simp add: data_product_reference_formed_def data_product_call data_list_term_formed octets_formed_def split: if_splits)

definition data_product_reference_decision :: "nat \<Rightarrow> bool" where
  "data_product_reference_decision n \<longleftrightarrow> (325,product_reference_argument n)\<in>positive_meaning data_product_system"

lemma data_product_reference_decision_code [code]:
  "data_product_reference_decision n \<longleftrightarrow> n=3 \<or> n=4 \<or> n=5"
  unfolding data_product_reference_decision_def
  by (subst data_product_lists) (auto simp: octets_formed_def split: if_splits)

export_code data_product_octets data_product_reference_formed data_product_reference_decision
  nat_of_integer integer_of_nat in SML module_name Native_Data_Product file_prefix native_data_product

end
