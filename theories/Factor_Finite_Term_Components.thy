theory Factor_Finite_Term_Components
  imports Factor_Executable_Terms
begin

fun finite_term_components :: "finite_factor_term\<Rightarrow>finite_factor_term fset" where
  "finite_term_components (Finite_Target a)={|Finite_Target a|}"
| "finite_term_components (Finite_Payload b)={|Finite_Payload b|}"
| "finite_term_components (Finite_Pair x y)=finsert (Finite_Pair x y)
    (finite_term_components x |\<union>| finite_term_components y)"

lemma finite_term_components_self [simp]: "t |\<in>| finite_term_components t"
  by (cases t) simp_all

end
