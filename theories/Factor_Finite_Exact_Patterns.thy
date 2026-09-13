theory Factor_Finite_Exact_Patterns
  imports Factor_Executable_Terms Factor_Pattern_Programs
begin

fun finite_exact_term_pattern :: "finite_factor_term\<Rightarrow>'a finite_term_pattern" where
  "finite_exact_term_pattern (Finite_Target t)=Finite_Pattern_Target t"
| "finite_exact_term_pattern (Finite_Payload p)=Finite_Pattern_Payload p"
| "finite_exact_term_pattern (Finite_Pair t u)=
    Finite_Pattern_Pair (finite_exact_term_pattern t) (finite_exact_term_pattern u)"

lemma finite_exact_term_pattern_correct [simp]:
  "decode_finite_pattern (finite_exact_term_pattern t)=exact_term_pattern (decode_finite_term t)"
  by (induction t) simp_all

end
