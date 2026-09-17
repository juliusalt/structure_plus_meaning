theory Parallel_Computed_Preparation
 imports Prepared_Computed_Functions "HOL-Library.Parallel" "HOL-Library.FSet"
begin

definition parallel_computed_function :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "parallel_computed_function evaluate keys=(let cache=Parallel.map (\<lambda>x. (x,evaluate x)) (remdups keys)
    in exact_cache_read evaluate (map_of cache))"

theorem parallel_computed_function_exact:
  "parallel_computed_function evaluate keys=evaluate"
proof (rule ext)
  fix x
  have exact: "computation_cache_exact evaluate (Parallel.map (\<lambda>x. (x,evaluate x)) (remdups keys))"
    by (auto simp: computation_cache_exact_def Parallel.map_def)
  show "parallel_computed_function evaluate keys x=evaluate x"
    unfolding parallel_computed_function_def Let_def
    by (rule exact_cache_read_correct; rule computation_cache_lookup[OF exact]; assumption)
qed

definition finite_set_computed_function :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "finite_set_computed_function evaluate keys=evaluate"

declare finite_set_computed_function_def[code del]

lemma finite_set_computed_function_lists_code [code]:
  "finite_set_computed_function evaluate (set xs)=parallel_computed_function evaluate xs"
  by (simp only: finite_set_computed_function_def parallel_computed_function_exact)

lemma finite_set_computed_function_cosets_code [code]:
  "finite_set_computed_function evaluate (List.coset xs)=evaluate"
  by (simp only: finite_set_computed_function_def)

definition finite_computed_function :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'a \<Rightarrow> 'b" where
  "finite_computed_function evaluate keys=finite_set_computed_function evaluate (fset keys)"

theorem finite_computed_function_exact:
  "finite_computed_function evaluate keys=evaluate"
  by (simp only: finite_computed_function_def finite_set_computed_function_def)

text \<open>
  Each distinct complete preparation input is actually evaluated through the
  existing parallel map, and the exact-cache operation retains its full value.
  Missing keys execute the original function. Finite collection enumeration and
  preparation order cannot change the resulting function on any argument.
  Returned functions can themselves be prepared computations; only input keys
  require equality, so no comparison of function values is introduced.
\<close>
end
