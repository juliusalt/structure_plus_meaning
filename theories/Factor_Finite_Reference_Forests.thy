theory Factor_Finite_Reference_Forests
  imports Factor_Finite_Reference_Tables Factor_Reference_Forests
begin

section \<open>One finite traversal combines every complete block reference table\<close>

text \<open>
  The executable table is the executable placed table at the syntax branches: it reads each child
  table with its index through the placed table's code equation, and a change of its values is the
  placed table's own (@{thm [source] placed_table_values}).
\<close>

definition finite_syntax_forest_table :: "(local_address\<times>'a) fset list \<Rightarrow> (local_address\<times>'a) fset" where
  "finite_syntax_forest_table Ms=finite_placed_table syntax_branch Ms"

lemma finite_syntax_forest_table_exact [simp]:
  "fset (finite_syntax_forest_table Ms)=syntax_forest_table (map fset Ms)"
  by (simp add: finite_syntax_forest_table_def syntax_forest_table_def)

lemma syntax_forest_value_map:
  "map_relation_values f (syntax_forest_table Ms)=syntax_forest_table (map (map_relation_values f) Ms)"
  by (simp add: syntax_forest_table_def placed_table_values)

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
  by (simp add: syntax_forest_table_def pattern_forest_bindings_def)

end
