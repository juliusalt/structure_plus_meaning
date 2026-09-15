theory Finite_Query_Value_Rows
  imports Finite_Set_Composition
begin

lemma finite_union_value_image:
  "fimage encode (ffUnion rows)=ffUnion (fimage (fimage encode) rows)"
  by (rule fset_inject[THEN iffD1]) (auto simp: ffUnion.rep_eq fimage.rep_eq)

definition finite_query_value_rows where
  "finite_query_value_rows select_rows rows=ffUnion (fimage (\<lambda>(value,query).
    fimage (\<lambda>(slot,other). (slot,value)) (select_rows query)) rows)"

lemma finite_query_value_rows_image:
  "finite_query_value_rows select_rows (fimage (map_prod encode id) rows)=
    fimage (map_prod id encode) (finite_query_value_rows select_rows rows)"
  by (simp add: finite_query_value_rows_def finite_union_value_image fimage_fimage
    map_prod_def case_prod_unfold comp_def)

lemma finite_query_value_rows_mapped_queries:
  "finite_query_value_rows select_rows (fimage (\<lambda>x. (encode x,query x)) X)=
    fimage (map_prod id encode) (finite_query_value_rows select_rows (fimage (\<lambda>x. (x,query x)) X))"
proof -
  have mapped: "fimage (\<lambda>x. (encode x,query x)) X=
    fimage (map_prod encode id) (fimage (\<lambda>x. (x,query x)) X)"
    by (simp only: fimage_fimage comp_def map_prod_def case_prod_conv id_apply)
  show ?thesis by (simp only: mapped finite_query_value_rows_image)
qed

text \<open>
  Each query selects a complete slot family, whose values come from the source
  row. Mapping those values before combining rows is exactly the image of the
  complete original result. The law needs no injectivity assumption and does
  not replace any query or selected slot.
\<close>

end
