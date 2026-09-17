theory RRA_Generation_Child_Row_Images
  imports RRA_Structural_Generation_Checking Finite_Query_Value_Rows
begin

lemma lookup_generation_child_rows_queries:
  "lookup_generation_child_rows locations u M checks=finite_query_value_rows
    (\<lambda>check. ffilter (\<lambda>(s,d). fBex (locations u d) (\<lambda>(v,a). check v a)) M) checks"
  by (simp only: lookup_generation_child_rows_def finite_query_value_rows_def)

lemma lookup_generation_child_rows_value_image:
  "lookup_generation_child_rows locations u M (fimage (\<lambda>H. (encode H,check H)) P)=
    fimage (map_prod id encode) (lookup_generation_child_rows locations u M (fimage (\<lambda>H. (H,check H)) P))"
  unfolding lookup_generation_child_rows_queries
  by (rule finite_query_value_rows_mapped_queries)

lemma finite_generation_child_rows_queries:
  "finite_generation_child_rows E u M checks=finite_query_value_rows
    (\<lambda>check. ffilter (\<lambda>(s,d). fBex (finite_located_values E u d) (\<lambda>(v,a). check E v a)) M) checks"
  by (simp only: finite_generation_child_rows_def finite_query_value_rows_def)

lemma finite_generation_child_rows_value_image:
  "finite_generation_child_rows E u M (fimage (\<lambda>H. (encode H,check H)) P)=
    fimage (map_prod id encode) (finite_generation_child_rows E u M (fimage (\<lambda>H. (H,check H)) P))"
  unfolding finite_generation_child_rows_queries
  by (rule finite_query_value_rows_mapped_queries)

declare lookup_check_generation_structural_code[code del]

lemma lookup_check_generation_word_rows_code [code]:
  "lookup_check_generation (Generation l P p c) artifacts bindings u r=
    fBex (lookup_generation_field_readings artifacts bindings u r) (\<lambda>(l',M,p',c').
      structural_target_code l=structural_target_code l' \<and>
      structural_target_code p=structural_target_code p' \<and>
      structural_target_code c=structural_target_code c' \<and>
      finite_bijective_relation (fimage fst M) (fimage structural_generation_code P)
        (lookup_generation_child_rows (lookup_located_values artifacts bindings) u M
          (fimage (\<lambda>H. (structural_generation_code H,lookup_check_generation H artifacts bindings)) P)))"
  by (simp only: lookup_generation_child_rows_value_image[where encode=structural_generation_code] lookup_check_generation_structural_code)

declare finite_check_generation_structural_code[code del]

lemma finite_check_generation_word_rows_code [code]:
  "finite_check_generation (Generation l P p c) E u r=
    fBex (finite_generation_field_readings E u r) (\<lambda>(l',M,p',c').
      structural_target_code l=structural_target_code l' \<and>
      structural_target_code p=structural_target_code p' \<and>
      structural_target_code c=structural_target_code c' \<and>
      finite_bijective_relation (fimage fst M) (fimage structural_generation_code P)
        (finite_generation_child_rows E u M
          (fimage (\<lambda>H. (structural_generation_code H,finite_check_generation H)) P)))"
  by (simp only: finite_generation_child_rows_value_image[where encode=structural_generation_code] finite_check_generation_structural_code)

text \<open>
  Both original child readers instantiate the same complete value-image law.
  Their recursive checks still use the original supplied generation at each
  resolved location. Only returned child values are mapped before combination,
  so complete generation-word equality replaces recursive generation equality
  in that combination. The original checker equations and meaning are retained.
  This equation does not establish a physical cost theorem.
\<close>

end
