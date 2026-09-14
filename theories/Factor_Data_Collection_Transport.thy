theory Factor_Data_Collection_Transport
  imports Factor_Self_Contained_Terms
begin

theorem data_collection_presents_image:
  assumes injective: "inj f"
  shows "data_collection_presents P (f ` A) t \<longleftrightarrow>
    data_collection_presents (\<lambda>a v. P (f a) v) A t"
proof
  assume source: "data_collection_presents P (f ` A) t"
  obtain xs ts where original: "distinct xs" "set xs=f ` A" "list_all2 P xs ts" "t=data_list_term ts"
    using source by (simp only: data_collection_presents_def; blast)
  have range: "\<forall>x\<in>set xs. \<exists>a. x=f a \<and> a\<in>A" using original(2) by blast
  obtain ys where displayed: "xs=map f ys" "\<forall>y\<in>set ys. y\<in>A"
    using range by (simp only: list_range_restricted_witnesses; blast)
  have same: "set ys=A" using original(2) displayed(1)
    by (simp only: set_map inj_image_eq_iff[OF injective])
  have distinct: "distinct ys" using original(1) displayed(1) by (simp add: distinct_map)
  have rows: "list_all2 (\<lambda>a v. P (f a) v) ys ts"
    using original(3) by (simp only: displayed(1) list_all2_map1)
  show "data_collection_presents (\<lambda>a v. P (f a) v) A t"
    using same distinct rows original(4) by (simp only: data_collection_presents_def; blast)
next
  assume source: "data_collection_presents (\<lambda>a v. P (f a) v) A t"
  obtain xs ts where original: "distinct xs" "set xs=A"
    "list_all2 (\<lambda>a v. P (f a) v) xs ts" "t=data_list_term ts"
    using source by (simp only: data_collection_presents_def; blast)
  have distinct: "distinct (map f xs)" using original(1) injective
    by (auto simp: distinct_map inj_on_def inj_def)
  have domain: "set (map f xs)=f ` A" by (simp only: set_map original(2))
  have rows: "list_all2 P (map f xs) ts" using original(3) by (simp only: list_all2_map1)
  show "data_collection_presents P (f ` A) t"
    using distinct domain rows original(4) by (simp only: data_collection_presents_def; blast)
qed

end
