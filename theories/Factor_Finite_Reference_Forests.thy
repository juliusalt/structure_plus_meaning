theory Factor_Finite_Reference_Forests
  imports Factor_Finite_Reference_Tables Factor_Reference_Forests
begin

section \<open>One finite traversal combines every complete block reference table\<close>

definition finite_syntax_forest_table :: "(local_address\<times>'a) fset list \<Rightarrow> (local_address\<times>'a) fset" where
  "finite_syntax_forest_table Ms=ffUnion (fset_of_list
    (map (\<lambda>i. finite_slot_keys (syntax_branch i) (Ms!i)) [0..<length Ms]))"

lemma finite_syntax_forest_table_exact [simp]:
  "fset (finite_syntax_forest_table Ms)=syntax_forest_table (map fset Ms)"
  by (simp add: finite_syntax_forest_table_def syntax_forest_table_def ffUnion.rep_eq fset_of_list.rep_eq
    image_image atLeast0LessThan cong: SUP_cong_simp)

lemma syntax_forest_value_map:
  "map_relation_values f (syntax_forest_table Ms)=syntax_forest_table (map (map_relation_values f) Ms)"
proof -
  have commute: "map_relation_values f (map_slot_keys g M)=map_slot_keys g (map_relation_values f M)" for g M
    by (simp add: map_relation_values_def map_slot_keys_def image_image split_def)
  have "map_relation_values f (syntax_forest_table Ms)=
      (\<Union>i<length Ms. map_relation_values f (map_slot_keys (syntax_branch i) (Ms!i)))"
    by (simp add: syntax_forest_table_def map_relation_values_def image_UN)
  also have "\<dots>=syntax_forest_table (map (map_relation_values f) Ms)"
    by (simp add: syntax_forest_table_def commute cong: SUP_cong_simp)
  finally show ?thesis .
qed


lemma finite_syntax_forest_table_values:
  "map_relation_values f (fset (finite_syntax_forest_table Ms))=
    syntax_forest_table (map (\<lambda>M. map_relation_values f (fset M)) Ms)"
  by (simp add: syntax_forest_value_map map_map comp_def)

text \<open>
  The pattern forest places its bodies at the forest's branches, so its literal bindings are the
  forest's table of the bodies' tables.
\<close>

lemma pattern_forest_reference_table:
  "syntax_forest_table (map pattern_literal_bindings ps)=pattern_forest_bindings ps"
  by (simp add: syntax_forest_table_def pattern_forest_bindings_def map_slot_keys_def cong: SUP_cong_simp)

end
