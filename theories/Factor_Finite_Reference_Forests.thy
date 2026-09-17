theory Factor_Finite_Reference_Forests
  imports Factor_Finite_Reference_Tables Factor_Reference_Forests
begin

section \<open>One finite traversal combines every complete block reference table\<close>

fun finite_syntax_forest_table :: "(local_address\<times>'a) fset list \<Rightarrow> (local_address\<times>'a) fset" where
  "finite_syntax_forest_table []={||}"
| "finite_syntax_forest_table (M#Ms)=finite_slot_keys (Cons 2) M |\<union>|
    finite_slot_keys (Cons 3) (finite_syntax_forest_table Ms)"

lemma finite_syntax_forest_table_exact [simp]:
  "fset (finite_syntax_forest_table Ms)=syntax_forest_table (map fset Ms)"
  by (induction Ms) simp_all

lemma syntax_forest_value_map:
  "map_relation_values f (syntax_forest_table Ms)=syntax_forest_table (map (map_relation_values f) Ms)"
proof (induction Ms)
  case Nil
  then show ?case by (simp add: map_relation_values_def)
next
  case (Cons M Ms)
  then show ?case by simp
qed

lemma finite_syntax_forest_table_values:
  "map_relation_values f (fset (finite_syntax_forest_table Ms))=
    syntax_forest_table (map (\<lambda>M. map_relation_values f (fset M)) Ms)"
  by (simp add: syntax_forest_value_map map_map comp_def)

lemma pattern_forest_reference_table:
  "syntax_forest_table (map pattern_literal_bindings ps)=pattern_forest_bindings ps"
  by (induction ps) (simp_all add: map_slot_keys_def)

end
