theory Factor_Source_Shape_Requirements
  imports Factor_Environment_Values Factor_Executable_Terms
begin

section \<open>A necessary source condition does not assert source admission\<close>

definition environment_outer_shape :: "factor_term \<Rightarrow> bool" where
  "environment_outer_shape t \<longleftrightarrow> (\<exists>a b. t=Pair_Term a b)"

lemma environment_presentation_outer_shape:
  assumes "environment_value_presents E t"
  shows "environment_outer_shape t"
  using assms by (auto simp: environment_value_presents_def environment_outer_shape_def)

lemma environment_outer_shape_obstruction:
  assumes "\<not>environment_outer_shape t"
  shows "\<not>environment_value_presents E t"
  using assms environment_presentation_outer_shape by blast

fun finite_environment_outer_shape :: "finite_factor_term \<Rightarrow> bool" where
  "finite_environment_outer_shape (Finite_Pair a b)=True"
| "finite_environment_outer_shape (Finite_Payload v)=False"
| "finite_environment_outer_shape (Finite_Target v)=False"

lemma finite_environment_outer_shape_exact:
  "finite_environment_outer_shape t \<longleftrightarrow> environment_outer_shape (decode_finite_term t)"
  by (cases t) (auto simp: environment_outer_shape_def)

theorem finite_environment_source_obstruction:
  assumes "\<not>finite_environment_outer_shape t"
  shows "\<not>environment_value_presents E (decode_finite_term t)"
  using assms by (simp only: finite_environment_outer_shape_exact)
    (use environment_outer_shape_obstruction in blast)

text \<open>
  The complete environment presentation separates its artifact and binding
  tables. This shape is necessary for every admitted environment, including
  the empty environment. A successful shape test establishes neither table
  formation nor any native reading. Failure rules out every presentation
  witness for that exact source term.
\<close>

export_code finite_environment_outer_shape checking SML

end
