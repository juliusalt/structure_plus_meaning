theory Finite_Pattern_Tuples
  imports Factor_Rule_Instances Factor_Executable_Terms
begin

section \<open>A tuple of terms and its pattern\<close>

text \<open>
  The n-ary tuple of terms nests pairs to the right, a single term being its own tuple and the empty tuple
  the empty payload; its pattern is the same nesting of patterns, and evaluating the pattern of a tuple is
  the tuple of the evaluations. A rule whose conclusion binds a list of variables states it as the tuple
  of those variables.
\<close>

fun term_tuple :: "factor_term list \<Rightarrow> factor_term" where
  "term_tuple []=Payload_Term []"
| "term_tuple [t]=t"
| "term_tuple (t#u#ts)=Pair_Term t (term_tuple (u#ts))"

fun finite_pattern_tuple :: "'a finite_term_pattern list \<Rightarrow> 'a finite_term_pattern" where
  "finite_pattern_tuple []=Finite_Pattern_Payload []"
| "finite_pattern_tuple [p]=p"
| "finite_pattern_tuple (p#q#ps)=Finite_Pattern_Pair p (finite_pattern_tuple (q#ps))"

lemma evaluate_pattern_tuple:
  "evaluate_pattern f (decode_finite_pattern (finite_pattern_tuple ps))=
    term_tuple (map (\<lambda>p. evaluate_pattern f (decode_finite_pattern p)) ps)"
  by (induction ps rule: finite_pattern_tuple.induct) simp_all

lemma finite_pattern_tuple_variables:
  "fset (finite_pattern_variables (finite_pattern_tuple hs)) = (\<Union>h\<in>set hs. fset (finite_pattern_variables h))"
  by (induction hs rule: finite_pattern_tuple.induct) auto

end
