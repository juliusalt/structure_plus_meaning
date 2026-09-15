theory Finite_Prepared_Results
  imports Finite_Set_Composition
begin

fun finite_prepared_results :: "('a\<Rightarrow>'b)\<Rightarrow>'a option\<Rightarrow>'b fset" where
  "finite_prepared_results f None={||}"
| "finite_prepared_results f (Some q)={|f q|}"

lemma finite_prepared_results_exact:
  "r |\<in>| finite_prepared_results f input \<longleftrightarrow> (\<exists>q. input=Some q \<and> r=f q)"
  by (cases input) auto

lemma finite_prepared_results_map:
  "finite_prepared_results f (map_option g input)=finite_prepared_results (f \<circ> g) input"
  by (cases input) simp_all

text \<open>
  Preparation availability and the prepared operation's result occupy separate
  positions. An unavailable input has no row. Every available input has one
  complete result row, including when that result is itself absent.
\<close>

end
